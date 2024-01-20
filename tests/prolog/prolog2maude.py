#!/usr/bin/env python3
#
# Transform Prolog programs
#

import os
import re
import sys
from collections import Counter

import lark

prolog_grammar = r'''
	?start: stmt *

	stmt: expr "."
	    | expr ":-" horn_clause "."

	expr: ATOM
	    | VAR
	    | CUT
	    | ATOM "(" [ expr ("," expr) * ] ")"

	horn_clause: [ expr ("," expr ) * ]

	ATOM: /([a-z0-9][a-zA-Z0-9]*)|(\\.)/
	VAR: /[A-Z][a-zA-Z0-9]*/
	CUT: "!"

	%import common.WS
	%ignore WS
'''

parser = lark.Lark(prolog_grammar)


class Prolog2Maude(lark.Visitor):
	"""Convert Prolog programs to be used with the narrowing-based Maude prototype"""

	INVALID_CHAR = re.compile(r'[^a-zA-Z0-9\-]')

	def __init__(self):
		self.rules = []
		self.vars = set()
		self.tags_count = Counter()
		self.has_cut = False

	def dump(self, program, name='example', out=sys.stdout):
		self.visit(parser.parse(program))

		# Remove invalid characters for a Maude identifier
		if not (name := self.INVALID_CHAR.sub('', name)):
			name = 'example'

		print(f'''smod {name.upper()} is
	extending LP-EXTRA+NEG .
	extending LP-EXTRA+CUT .
''', file=out)

		# All variables in the rules
		print('\tvars', *sorted(self.vars), ': Term .\n', file=out)

		# Rules
		for _, _, rl in self.rules:
			print(f'\t{rl}', file=out)

		# Number of rules
		print(f'\n\top {name}-count : -> Nat .', file=out)
		print(f'\teq {name}-count = {len(self.rules)} .', file=out)

		# Strategies
		print(f'\n\tstrat {name} : Nat @ Term .\n')
		for k, (tag, _, _) in enumerate(self.rules):
			print(f'\tsd {name}({k}) := {tag} .', file=out)

		# Cut predicate
		if self.has_cut:
			print(f'\n\top {name}-hasCut : Nat -> Bool .\n')
			for k, (_, has_cut, _) in enumerate(self.rules):
				if has_cut:
					print(f'\teq {name}-hasCut({k}) = true .')
			print(f'\teq {name}-hasCut(N:Nat) = false [owise] .')

		print('endsm', file=out)

		# View
		cut_stmt = f'op hasCut to {name}-hasCut .' if self.has_cut else 'var N : Nat .\n\top hasCut(N) to term false .'

		print(f'''
view {name.title()} from PROGRAM to {name.upper()} is
	strat program to {name} .
	op programCount to {name}-count .
	{cut_stmt}
endv''')

		# Module instance
		print(f'''
smod PROLOG-{name.upper()} is
	including PROLOG+CUT{{{name.title()}}} .
	vars X Y Z : Term .
endsm''')

	def stmt(self, tree):
		"""Horn clause"""

		head = tree.children[0]

		# Rule identifier
		self.tags_count[head.tag] += 1
		tag = f'{head.tag}{self.tags_count[head.tag]}'

		# Add variables
		self.vars.update(head.vars)

		if len(tree.children) == 1:
			self.rules.append((tag, False, f'rl [{tag}] : {head.result} => nil .'))

		else:
			# Check whether it is executable by rewriting
			conds = tree.children[1]
			nonexec = '' if conds.vars <= head.vars else ' [nonexec]'

			self.rules.append((tag, conds.has_cut, f'rl [{tag}] : {head.result} => {conds.result}{nonexec} .'))
			self.vars.update(conds.vars)

			if conds.has_cut:
				self.has_cut = True

	def horn_clause(self, tree):
		"""Horn clause list"""

		tree.result = ', '.join(child.result for child in tree.children)
		tree.vars = set().union(*(child.vars for child in tree.children))
		tree.has_cut = any(child.has_cut for child in tree.children)

	def expr(self, tree):
		"""Prolog expression"""

		etype = tree.children[0].type
		value = tree.children[0].value

		# Variable
		if etype == 'VAR':
			tree.result = value
			tree.term = value
			tree.vars = {value}
			tree.tag = 'var'
			tree.has_cut = False

		elif etype == 'CUT':
			tree.result = '!'
			tree.term = '!'
			tree.vars = set()
			tree.tag = 'cut'
			tree.has_cut = True

		# Atom
		elif etype == 'ATOM':
			if len(tree.children) == 1:
				tree.result = "'" + value
				tree.term = tree.result
				tree.vars = set()
			else:
				args = ', '.join(child.term for child in tree.children[1:])
				tree.result = f"'{value}({args})"
				tree.term = f"'{value}[{args}]"
				tree.vars = set().union(*(child.vars for child in tree.children[1:]))

			tree.tag = value
			tree.has_cut = False


def main():
	"""Entry point to the program"""

	import argparse
	parser = argparse.ArgumentParser(description='Convert Prolog programs to Maude')
	parser.add_argument('prolog', help='Name of the Prolog program to convert', type=argparse.FileType('r'))
	parser.add_argument('--name', help='Name of the module')

	args = parser.parse_args()
	program = args.prolog.read()

	try:
		visitor = Prolog2Maude()
		visitor.dump(program, name=os.path.splitext(args.prolog.name)[0])

	except lark.exceptions.UnexpectedCharacters as e:
		print(e)


if __name__ == '__main__':
	sys.exit(main())
