#!/usr/bin/env python3
#
# Prototype for narrowing with strategies
#

import itertools
import os
import sys

import maude
from umaudemc import pyslang

# Fix for MAUDE_VERSION constant
if not hasattr(maude, 'MAUDE_VERSION'):
	maude.MAUDE_VERSION = '3'

# Text to print solutions to the snarrow command
SOLUTION_TEXT = '''Solution {index}
result {sort}: {term}
accumulated substitution:
{subs}
'''

# Name of the history file for the interpreter
HISTORY_PATH = '.snarrow.history'


def subterms(term: maude.Term):
	"""Iterator over the subterms of a term"""

	stack = [term]

	while stack:
		yield (term := stack.pop())
		stack += list(term.arguments())


def get_vars(term: maude.Term, varset: set[maude.Term]):
	"""Add all variables in the term to the given set"""

	for subterm in subterms(term):
		if subterm.isVariable():
			varset.add(subterm)


def prefix_variables(term: maude.Term, prefix: str) -> maude.Term:
	"""Prefix the variables of a term"""

	module = term.symbol().getModule()
	subs = {}

	for subt in subterms(term):
		if subt.isVariable():
			subs[subt] = module.parseTerm(f'{prefix}{subt.getVarName()}:{subt.getSort()}')

	return maude.Substitution(subs).instantiate(term)


class CompiledRule:
	"""Rule prepared for narrowing"""

	def __init__(self, rl, prefix):
		self.eq_conds = []
		self.rw_conds = []
		self.mb_conds = []

		# Compile the rule for narrowing
		self.lhs = prefix_variables(rl.getLhs(), prefix)
		self.rhs = prefix_variables(rl.getRhs(), prefix)

		module = rl.getLhs().symbol().getModule()

		# Prepare the condition
		for k, cf in enumerate(rl.getCondition()):
			lhs = prefix_variables(cf.getLhs(), prefix)

			# Sort membership tests
			if isinstance(cf, maude.SortTestCondition):
				# t : s is translated to t = <SMk where <SMk is a fresh variable of sort s
				fake_var = module.parseTerm(f'{prefix}<SM{k}:{cf.getSort()}')
				self.mb_conds.append((lhs, fake_var))
				continue

			rhs = prefix_variables(cf.getRhs(), prefix)

			# Rewriting conditions
			if isinstance(cf, maude.RewriteCondition):
				self.rw_conds.append((lhs, rhs))

			# Equality conditions
			else:
				self.eq_conds.append((lhs, rhs))

		# Calculate the free variables of the rule
		# (there may be free variables in the condition with matching
		# conditions, but we treat them as typical equality conditions)
		lhs_vars, rhs_vars = set(), set()

		get_vars(self.lhs, lhs_vars)
		get_vars(self.rhs, rhs_vars)

		for lhs, rhs in itertools.chain(self.eq_conds, self.rw_conds):
			get_vars(lhs, lhs_vars)
			get_vars(rhs, lhs_vars)

		for lhs, _ in self.mb_conds:
			get_vars(lhs, lhs_vars)

		self.free_vars = sorted(rhs_vars - lhs_vars, key=maude.Term.__str__)

	def problem(self, term):
		"""Unification problem for this rule"""

		return (self.lhs, term), *self.eq_conds, *self.mb_conds


class NarrowStratRunner(pyslang.StratRunner):
	"""Strategy runner for narrowing with strategies"""

	# Prefix for rule variables
	RLVAR_PREFIX = '//s'

	class State(pyslang.StratRunner.State):
		"""Execution state with an accumulated substitution"""

		def __init__(self, term, pc, stack, subs=None, index=0, conditional=False):
			super().__init__(term, pc, stack, conditional)
			# Accumulated substitution
			self.subs = subs if subs else {}
			# Fresh variable index
			self.index = index

		def copy(self, term=None, pc=None, stack=None, subs=None, index=None, conditional=False):
			"""Clone state with possibly some changes"""

			return NarrowStratRunner.State(
				self.term if term is None else term,
				self.pc + 1 if pc is None else pc,
				self.stack if stack is None else stack,
				self.subs if subs is None else subs,
				self.index if index is None else index,
				conditional
			)

		def __repr__(self):
			return f'NarrowingState({self.pc}, {self.term}, {self.stack}, {self.subs}, {self.index})'

	def __init__(self, program, term, filtered=True, conditional=True, unify_test=True, unify_matchrew=True, **kwargs):
		super().__init__(program, term, state_class=self.State, **kwargs)

		# Module
		self.module = term.symbol().getModule()

		# Index and compile the rules in the module by label
		self.rule_map = {None: []}

		for rl in self.module.getRules():
			# Compile the rule for narrowing
			compiled_rule = CompiledRule(rl, self.RLVAR_PREFIX)

			# Discard conditional rules if conditional=False
			# (rule with only rewriting conditions are not discarded
			# since they cannot be used without explicit syntax)
			if not conditional and (compiled_rule.eq_conds or compiled_rule.mb_conds):
				continue

			# Index them by label
			if label := rl.getLabel():
				self.rule_map.setdefault(label, []).append(compiled_rule)

			# Collect all non-conditional rules for all
			if not rl.hasCondition():
				self.rule_map[None].append(compiled_rule)

		# Whether to filter variants
		self.filtered = filtered
		# Whether to do unification with the match strategy
		if unify_test:
			self.handlers[pyslang.Instruction.TEST] = self.test_unify
		# Whether to do unification with the matchrew strategy
		if unify_matchrew:
			self.handlers[pyslang.Instruction.MATCHREW] = self.matchrew_unify

		# Attribute to hold the solution
		self.solution = None

	def replace_variables(self, subs: maude.Substitution, index: int, free=()) -> tuple[dict, maude.Substitution, int]:
		"""Replace the variables in a variant unification substitution"""

		# New temporary substitution to remove % variables
		new_subs = {}

		for _, value in subs:
			for subt in subterms(value):
				if subt.isVariable() and subt.getVarName()[0] in '%#@':
					if subt not in new_subs:
						new_subs[subt] = self.module.parseTerm(f'?{index}:{subt.getSort()}')
						index += 1

		new_subs = maude.Substitution(new_subs)

		# Apply that new substitution to the input substitution, separating
		# the mapping of original variables from the mapping of rule variables

		accum, matching = {}, {}

		for key, value in subs:
			target = matching if key.getVarName().startswith(self.RLVAR_PREFIX) else accum
			target[key] = new_subs.instantiate(value)

		# Add free variables to the matching substitution
		matching |= {var: self.module.parseTerm(f'?{index + k}:{var.getSort()}') for k, var in enumerate(free)}

		return accum, maude.Substitution(matching), index + len(free)

	@staticmethod
	def instantiate(term: maude.Term, subs):
		"""Instantiate and reduce a term"""

		term = subs.instantiate(term)
		term.reduce()
		return term

	def update_accum(self, step: dict[maude.Term, maude.Term]):
		"""Update the accumulated substitution"""

		accum = self.current_state.subs

		# New variables to be inserted into the accumulated substitution
		result = {k: v for k, v in step.items()
		          if k not in accum}

		step = maude.Substitution(step)

		# Update with the old values
		for k, v in accum.items():
			result[k] = self.instantiate(v, step)

		return result

	def rlapp(self, args, stack):
		"""Do narrowing with a rule"""

		self.pending += [self.current_state.copy(term=t, subs=self.update_accum(accum), index=index)
		                 for t, accum, index in self.get_rewrites(args, stack)]

		self.next_pending()

	def get_rewrites(self, args, stack):
		"""Apply a rule and get the narrowing steps"""
		# Regardless of the value of top, we do narrowing on top
		label, initial_subs, top = args

		# The initial substitution should be instantiated and reduced first
		if initial_subs:
			if stack.venv:
				initial_subs = {var: stack.venv.instantiate(value)
				                for var, value in initial_subs.items()}

			for value in initial_subs.values():
				value.reduce()

			initial_subs = maude.Substitution(initial_subs)

		# Get all rules with label "label"
		solutions = []

		for rule in self.rule_map.get(label, ()):
			# Skip rules with rewriting conditions (they are handled elsewhere)
			if rule.rw_conds:
				continue

			# Unification problem
			problem = rule.problem(self.current_state.term)
			rhs = rule.rhs

			# Instantiate the problem (with the given substitution)
			if initial_subs:
				problem = tuple((initial_subs.instantiate(lhs), initial_subs.instantiate(rhs))
				                for lhs, rhs in problem)
				rhs = initial_subs.instantiate(rhs)

			for subs in self.module.variant_unify(problem, filtered=self.filtered):
				accum, matching, index = self.replace_variables(subs, self.current_state.index, free=rule.free_vars)
				solutions.append((self.instantiate(rhs, matching), accum, index))

		return solutions

	def test_unify(self, args, stack):
		"""Test (with narrowing)"""

		# Only match is handled with unification
		if args[0] != -1:
			return self.test(args, stack)

		# This is the same as umaudemc.pyslang.StratRunner.test
		# but with unification

		mtype, pattern, condition = args

		# Instantiate pattern and condition with the environment substitution
		if stack.venv is not None:
			pattern = stack.venv.instantiate(pattern)
			condition = pyslang.instantiate_condition(condition, stack.venv)

		# Prepare the test for matching (this should be cached for efficiency)
		TEST_PREFIX = '//t'
		problem = [(self.current_state.term, prefix_variables(pattern, TEST_PREFIX))]

		for k, cf in enumerate(condition):
			if isinstance(cf, maude.SortTestCondition):
				# t : s is translated to t = <SMk where <SMk is a fresh variable of sort s
				fake_var = self.module.parseTerm(f'{TEST_PREFIX}<SMT{k}:{cf.getSort()}')
				problem.append((prefix_variables(cf.getLhs(), TEST_PREFIX), fake_var))
			else:
				problem.append((prefix_variables(cf.getLhs(), TEST_PREFIX),
				                prefix_variables(cf.getRhs(), TEST_PREFIX)))

		# A single unifier is enough to pass the test
		matched = next(self.module.variant_unify(problem, filtered=self.filtered), None)

		if matched is None:
			self.next_pending()
		else:
			self.current_state.pc += 1

	def matchrew_unify(self, args, stack):
		"""Matchrew (with unification instead of matching)"""

		# Only matchrew is handled with unification
		if args[0] != -1:
			return self.matchrew(args, stack)

		# This is the same as umaudemc.pyslang.StratRunner.matchrew
		# but with unification

		mtype, pattern, condition, variables = args

		# Instead of making the variables of the pattern fresh,
		# we rename the variables of the term to avoid name clashes
		strat_vars, term_vars = set(), set()
		get_vars(pattern, strat_vars)
		for cf in condition:
			if isinstance(cf, maude.AssignmentCondition):
				get_vars(cf.getLhs(), strat_vars)

		get_vars(self.current_state.term, term_vars)

		# Make a substitution to remove the conflicting variables
		new_index, new_term, term_subs = self.current_state.index, self.current_state.term, {}

		for var in strat_vars.intersection(term_vars):
			term_subs[var] = self.module.parseTerm(f'?{new_index}:{var.getSort()}')
			new_index += 1

		if term_subs:
			new_term = maude.Substitution(term_subs).instantiate(self.current_state.term)

		# Original pattern without instantiation
		original_pattern = pattern

		# Instantiate pattern and condition with the environment substitution
		if stack.venv is not None:
			pattern = stack.venv.instantiate(pattern)
			condition = pyslang.instantiate_condition(condition, stack.venv)

		# Prepare the test for matching (this should be cached for efficiency)
		problem = [(new_term, pattern)]

		for k, cf in enumerate(condition):
			if isinstance(cf, maude.SortTestCondition):
				# t : s is translated to t = <SMk where <SMk is a fresh variable of sort s
				fake_var = self.module.parseTerm(f'<SMM{k}:{cf.getSort()}')
				problem.append((cf.getLhs(), fake_var))
			else:
				problem.append((cf.getLhs(), cf.getRhs()))

		for unifier in self.module.variant_unify(problem, filtered=self.filtered):
			accum, _, index = self.replace_variables(unifier, new_index)
			merged_subs, context = self.process_match(stack.venv, maude.Substitution(accum),
			                                          (lambda v: v), original_pattern, variables)

			# The accumulated substitution is extended with this unifier and
			# with the renaming of the main term variables
			accum = (self.current_state.subs | term_subs |
			         {k: v for k, v in accum.items() if k not in strat_vars})

			# Stack node that holds the information required for the matchrew
			new_stack = pyslang.SubtermNode(parent=stack,
			                                venv=merged_subs,
			                                context=context,
			                                pending=[merged_subs.instantiate(var) for var in variables[1:]])

			# Start evaluating the first subterm
			self.pending.append(self.current_state.copy(term=merged_subs.instantiate(variables[0]),
			                                            subs=self.update_accum(accum),
			                                            stack=new_stack,
			                                            index=index))

		self.next_pending()

	def nextsubterm(self, args, stack):
		"""Finish or continue a matchrew (narrowing fixes)"""

		# The parent does the actual work
		super().nextsubterm(args, stack)

		# Instantiate the subterm with the accumulated substitution
		# (since all occurrences of the variables should be in sync)
		subs = maude.Substitution(self.current_state.subs)
		self.current_state.term = subs.instantiate(self.current_state.term)

	@staticmethod
	def prepare_candidates(candidates, prefix, pre_subs=None, post_subs=None):
		"""Prepare the candidates of a rewriting condition instruction"""

		def prepare(term):
			if pre_subs:
				term = pre_subs.instantiate(term)
				term.reduce()
			term = prefix_variables(term, prefix)
			if post_subs:
				term = post_subs.instantiate(term)
				term.reduce()
			return term

		return tuple((prepare(lhs),
		              tuple((prepare(lhs), prepare(rhs)) for lhs, rhs in eq_conds),
		              prepare(rhs))
		             for lhs, eq_conds, rhs in candidates)

	def rwcstart(self, args, stack):
		"""Start a rewriting condition search"""

		# Adapted from umaudemc.pyslang.StratRunner.rwcstart

		top, initial_subs, candidates = args
		stack = self.current_state.stack
		initial_subs_obj = None

		# The initial substitution should be instantiated and reduced first
		if initial_subs:
			if stack.venv:
				initial_subs = {var: stack.venv.instantiate(value)
				                for var, value in initial_subs.items()}

			for value in initial_subs.values():
				value.reduce()

			initial_subs_obj = maude.Substitution(initial_subs)

		# Rename the variables in the rule (this should be done dynamically because
		# applications can be nested, not only syntactically but between calls).
		VAR_PREFIX = f'^rwc/{self.current_state.index}/'

		candidates = self.prepare_candidates(candidates, VAR_PREFIX, pre_subs=initial_subs_obj)

		for k, (lhs, eq_conds, rwc_lhs) in enumerate(candidates):
			# Unification problem
			problem = ((lhs, self.current_state.term), *eq_conds)

			for unifier in self.module.variant_unify(problem, filtered=self.filtered):
				# Replace matching variables
				accum, _, index = self.replace_variables(unifier, self.current_state.index + 1)
				accum = {**self.current_state.subs, **accum}

				# Stack node holding the context and accumulated substitution of the rewriting condition
				new_stack = pyslang.RwcNode(parent=stack, index=k, subs=initial_subs_obj, context=VAR_PREFIX)

				# Start rewriting the left-hand side of the first condition fragment
				subs = maude.Substitution(accum)
				new_term = self.instantiate(rwc_lhs, subs)
				self.pending.append(self.current_state.copy(term=new_term, stack=new_stack, subs=accum, index=index))

		self.next_pending()

	def rwcnext(self, args, stack):
		"""Continue a rewriting condition search"""

		# Adapted from umaudemc.pyslang.StratRunner.rwcstart

		is_final, candidates = args

		# The accumulated substitution
		# (we intentionally leave the initial substitution of the rule out
		# of the accumulated one -in stack.subs- to avoid prefixing those
		# variables, although it is not really needed)
		state_subs = maude.Substitution(self.current_state.subs)

		# rwc_lhs is the LHS of the next condition fragment
		# or the RHS of the rule if is_final
		# -> we should do unification with it
		(rwc_rhs, eq_conds, rwc_lhs), = self.prepare_candidates((candidates[stack.index],), stack.context,
		                                                        pre_subs=stack.subs, post_subs=state_subs)

		problem = ((rwc_rhs, self.current_state.term), *eq_conds)

		for unifier in self.module.variant_unify(problem, filtered=self.filtered):
			# Accumulated substitution
			accum, _, index = self.replace_variables(unifier, self.current_state.index)
			accum = {**self.current_state.subs, **accum}
			subs = maude.Substitution(accum)

			# Instantiate the other variables of the substitution
			for i in range(2):  # once for the unifier, and once for the previous (improve this)
				accum = {k: self.instantiate(v, subs) for k, v in accum.items()}

			if is_final:
				new_term = self .instantiate(rwc_lhs, subs)
				accum = {k: v for k, v in accum.items() if not k.getVarName().startswith(stack.context)}
				self.pending.append(self.current_state.copy(term=new_term, stack=stack.parent, subs=accum, index=index))
			else:
				new_stack = pyslang.RwcNode(parent=stack.parent, index=stack.index, subs=stack.subs, context=stack.context)
				new_term = self.instantiate(rwc_lhs, subs)
				self.pending.append(self.current_state.copy(term=new_term, stack=new_stack, subs=accum, index=index))

		self.next_pending()

	def run(self):
		"""Run the strategy and get the next result"""

		self.solution = None

		# Exactly the same as umaudemc.pyslang.StratRunner.run,
		# except for the call to already_seen

		# Keep running until the strategy is exhausted (or a solution is found)
		while self.current_state:
			# If the state is already visited, continue with other pending work
			while (self.current_state.stack.already_seen(self.current_state.pc,
			                                             (self.current_state.term,
			                                              tuple(self.current_state.subs.items())))):
				if not self.next_pending():
					return None

			# Current state
			state = self.current_state

			# The instruction to be executed
			inst = self.code[state.pc]

			self.handlers[inst.type](inst.extra, state.stack)

			if self.solution:
				# Discard ? variables since they are not needed
				state.subs = {k: v for k, v in state.subs.items()
				              if not k.getVarName().startswith('?')}

				return self.solution, state.subs

		return None


def adapt_condition(conds):
	"""Adapt conditions of the compiled program"""

	# It translates from the maude library types pairs of maude.Term
	tuple_conds = []

	for k, cf in enumerate(conds):
		lhs = cf.getLhs()
		module = lhs.symbol().getModule()

		if isinstance(cf, maude.SortTestCondition):
			# t : s is translated to t = <SMk where <SMk is a fresh variable of sort s
			fake_var = module.parseTerm(f'<SMC{k}:{cf.getSort()}')
			tuple_conds.append((lhs, fake_var))
		else:
			tuple_conds.append((lhs, cf.getRhs()))

	return tuple(tuple_conds)


def adapt_program(p):
	"""Adapt the program for narrowing"""

	for inst in p.inst:
		if inst.type == pyslang.Instruction.RLAPP:
			label, subs, top = inst.extra

			# Prefix the substitution variables
			# (since they are also prefixed in the rule)
			subs = {prefix_variables(k, NarrowStratRunner.RLVAR_PREFIX): v
			        for k, v in subs.items()} if subs else None

			inst.extra = (label, subs, top)

		elif inst.type == pyslang.Instruction.RWCSTART:
			top, initial_subs, candidates = inst.extra

			candidates = tuple((lhs, adapt_condition(conds), rf_lhs)
			                   for lhs, conds, rf_lhs in candidates)

			inst.extra = top, initial_subs, candidates

		elif inst.type == pyslang.Instruction.RWCNEXT:
			is_final, candidates = inst.extra

			candidates = tuple((rf_rhs, adapt_condition(conds), rhs)
			                   for rf_rhs, conds, rhs in candidates)

			inst.extra = (is_final, candidates)


def snarrow(term, strategy, module=None, filtered=True, conditional=True,
            unify_tests=False, unify_matchrew=False, max_sols=-1):
	"""snarrow command, like srewrite but narrowing"""

	# Module
	mod = maude.getModule(module) if module else maude.getCurrentModule()

	if not mod: return 1

	# Parse initial term
	if not (initial := mod.parseTerm(term)): return 1

	# Parse strategy
	# (dirty replacement fix, should be fixed with an extensible parser)
	renamed_strategy = strategy.replace('unifynarrow ', 'matchrew ').replace('unify ', 'match ')
	if not (strategy := mod.parseStrategy(renamed_strategy)): return 1

	# Compile the strategy
	ml = maude.getModule('META-LEVEL')
	sc = pyslang.StratCompiler(mod, ml, use_notify=False)

	p = sc.compile(ml.upStrategy(strategy))
	# p.dump()
	adapt_program(p)

	# Print the given command (like in Maude)
	print(f'snarrow {f"[{max_sols}] " if max_sols != -1 else ""}'
	      f'in {mod} : {initial} using {strategy} .\n')

	# Run the strategy
	runner = NarrowStratRunner(p, initial, filtered=filtered,
	                           conditional=conditional,
	                           unify_test=unify_tests,
	                           unify_matchrew=unify_matchrew)

	index = 0

	# For the given number of solutions (-1 means unbounded)
	while max_sols == -1 or index < max_sols:
		result = runner.run()
		index += 1

		if result:
			term, subs = result
			# Accumulated substitution mappings
			subs_txt = '\n'.join(f'{k} --> {v}' for k, v in subs.items()) or 'none'
			print(SOLUTION_TEXT.format(index=index, sort=term.getSort(), term=term, subs=subs_txt))
		else:
			print('No solutions.' if index == 1 else 'No more solutions.')
			break

	return 0


class MaudeREPL:
	"""Extended Maude REPL"""

	# Standard Maude files
	STANDARD_FILES = (
		'file.maude', 'metaInterpreter.maude', 'process.maude',
		'term-order.maude', 'linear.maude', 'model-checker.maude',
		'smt.maude', 'time.maude', 'machine-int.maude',
		'prelude.maude', 'socket.maude'
	)

	def __init__(self, args):
		self.args = args

	def extended_load(self, filename: str):
		"""Extended load command"""

		# Look for the file
		if not os.path.isfile(filename) and not filename.endswith('.maude'):
			filename += '.maude'

		found = None

		# First try with the current working directory
		if os.path.exists(filename):
			found = os.path.abspath(filename)
			if dirname := os.path.dirname(filename):
				os.chdir(dirname)
		else:
			# Standard files are loaded as usual
			if filename in self.STANDARD_FILES:
				return maude.load(filename)

			# Then try in MAUDE_LIB
			for path in os.getenv('MAUDE_LIB', '').split(os.pathsep):
				if os.path.exists(os.path.join(path, filename)):
					found = filename
					break

		if not found:
			print('\x1b[31mWarning:\x1b[0m' if os.isatty(sys.stdout.fileno()) else 'Warning:',
			      '<standard input>: unable to locate file:', filename)
			return False

		with open(found) as input_file:
			accum = []

			for line in input_file:
				line = line.lstrip()

				# Intercept snarrow commands
				if line.startswith('snarrow'):
					maude.input(''.join(accum))
					accum = []

					print('==========================================')
					self.parse_snarrow(line.rstrip())

				# Intercept load commands (but not sload)
				elif line.startswith('load'):
					maude.input(''.join(accum))
					accum = []

					self.extended_load(line[5:].strip().strip('"'))

				else:
					accum.append(line)

			return maude.input(''.join(accum))

	def parse_snarrow(self, line: str):
		"""Parse the snarrow command"""

		# Currently, the command should be in a single line

		# Parse the command almost heuristically
		try:
			# Check the dot at the end of the command
			index = line.rindex('.')
			line = line[7:index].strip()

			# Bound on the number of solutions
			max_sols = -1
			if line.startswith('['):
				index = line.index(']')
				max_sols = int(line[1:index])
				line = line[index + 1:].lstrip()

			# Module
			if line.startswith('in'):
				index = line.index(':')
				module = line[3:index].strip()
				maude.input(f'select {module} .\n')
				line = line[index + 1:].lstrip()

			# Term (skip parentheses)
			index, parlevel = 0, 0

			while index < len(line):
				if line[index] == '(':
					parlevel += 1
				elif line[index] == ')':
					if parlevel > 0:
						parlevel -= 1
				elif parlevel == 0 and line[index:].startswith('using'):
					break

				index += 1

			term = line[:index].rstrip()

			# Strategy
			strategy = line[index + 5:].rstrip()

			snarrow(term,
			        strategy,
			        filtered=self.args.filtered,
			        unify_tests=self.args.with_unify_tests,
			        max_sols=max_sols)

		except ValueError:
			print('Warning: cannot parse snarrow command.')

	def print_banner(self):
		"""Print the initial banner"""

		print(f'\n          *** Maude {maude.MAUDE_VERSION.replace("+smc", "")} with snarrow command ***\n')

	def run(self):
		"""Maude REPL for direct input"""

		# Select the given module (if any)
		if self.args.module:
			maude.input(f'select {self.args.module} .\n')

		try:
			line = input('Maude> ').strip()

			while line and not line.startswith('quit'):
				# Intercept snarrow commands
				if line.startswith('snarrow'):
					print('==========================================')
					self.parse_snarrow(line)

				# Intercept load commands (but not sload)
				elif line.startswith('load'):
					self.extended_load(line[5:].lstrip().strip('"'))

				else:
					maude.input(line + '\n')
				line = input('Maude> ').strip()

		except EOFError:
			pass

		except KeyboardInterrupt:
			print('Interrupted by the user.')

		print('Bye.')
		return 0


def main():
	import argparse

	parser = argparse.ArgumentParser(description='Narrowing with strategies')
	parser.add_argument('file', help='Maude file', nargs='?')
	parser.add_argument('term', help='Initial term', nargs='?')
	parser.add_argument('strategy', help='Narrowing strategy', nargs='?')
	parser.add_argument('--module', '-m', help='Maude module')
	parser.add_argument('--max-sols', help='Stop when the given number of solutions has been obtained',
	                    type=int, default=-1)
	parser.add_argument('--no-unify-tests', help='Disable unification in the match strategy',
		            dest='with_unify_tests', action='store_false')
	parser.add_argument('--no-unify-matchrew', help='Disable unification in the matchrew strategy',
		            dest='with_unify_matchrew', action='store_false')
	parser.add_argument('--no-filtered', help='Disable variant filtering', dest='filtered', action='store_false')
	parser.add_argument('--no-conditional', help='Disable conditional rules',
		            dest='with_conditional', action='store_false')
	parser.add_argument('--version', help='Show version info and exit', action='store_true')

	args = parser.parse_args()

	# Show version and exit
	if args.version:
		import umaudemc
		print(f'snarrow 2024.01.19 (with Maude={maude.MAUDE_VERSION}, '
		      f'maude library={maude.__version__}, umaudemc={umaudemc.__version__})')
		return 0

	maude.init()

	# Extended Maude interpreter
	repl = MaudeREPL(args)

	if not args.strategy:
		repl.print_banner()

	if args.file:
		repl.extended_load(args.file)

	# Run as a command
	if args.strategy:
		return snarrow(args.term,
		               args.strategy,
		               module=args.module,
		               filtered=args.filtered,
		               conditional=args.with_conditional,
		               unify_tests=args.with_unify_tests,
		               unify_matchrew=args.with_unify_matchrew,
		               max_sols=args.max_sols)

	# Run as an interpreter
	else:
		# Use line history
		import readline
		if os.path.exists(HISTORY_PATH):
			readline.read_history_file(HISTORY_PATH)
		ret = repl.run()
		readline.write_history_file(HISTORY_PATH)
		return ret


if __name__ == '__main__':
	sys.exit(main())
