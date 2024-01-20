# Narrowing with strategies in Maude

This is an extension of the [Maude strategy language](https://doi.org/10.1016/j.jlamp.2023.100887) for [narrowing](https://maude.lcc.uma.es/maude-manual/maude-manualch15.html) (instead of rewriting).

The prototype can be used in two ways, as an extended Maude interpreter or as a command-line tool. For the first option, execute
```bash
$ ./snarrow.py [<Maude file>]
```
and the typical Maude prompt will appear. In addition to the standard Maude commands, it understands `snarrow [[<number>]] [in <module name> :] <initial term> using <strategy> .`.

Its syntax as a command-line tool is
```bash
$ ./snarrow.py <Maude file> [-m <module name>] <initial term> <strategy> [--max-sols <number>]
```
The output will coincide with that of the equivalent `snarrow` command.

The command relies on the Python implementation of the strategy language contained in the [umaudemc](https://github.com/fadoss/umaudemc) package, which can be installed with `pip install umaudemc`.


## Options

* `--no-unify-test` does not change matching by unification in the `match` test (matching is always applied with `xmatch` and `amatch`). `unify` is syntactic sugar for `match` even if this option is enabled.
* `--no-unify-matchrew` does not change matching by unification in the `matchrew` combinator (matching is always applied for `xmatchrew` and `amatchrew`). `unifynarrow` is syntactic sugar for `matchrew` even if this option is enabled.
* `--no-conditional` disables narrowing with conditional rules, which is enabled by default. Conditional rules are applied by adding the equational conditions to the narrowing problem of the main pattern, and doing strategy-controlled narrowing search for the rewriting conditions. Rules with rewriting conditions only are never disabled, since the user cannot apply them inadvertently because of their explicit syntax.
* `--no-filtered` disables variant filtering.

Any (perhaps unconditional) rule in the module can be applied, even those not including the `narrowing` attribute. The strategy `all` does a narrowing step using any unconditional rule.


## Tests

Several test cases on the Maude files of the `test` directory can be executed with `./test.sh`. The output of this script should coincide with the `test.expected` file. Namely, there is a Prolog-like logic programming interpreter implementing cut and negation by means of strategies.
