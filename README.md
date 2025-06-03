# Formalization of a linear, oportunistic lambda calculus

What you’ll find right now, is:

`Syntax.v`

- a definition of the syntax for the core calculus
- a definition of “well scoping” ws_ that checks whether a de Bruijn term is well scoped
- a definition of a “structural equivalence” seq_* that lets us permute processes
- a definition of permutation equivalence peq_* that lets us rename de Bruijn variables by a bijection
- a definition of well-formed syntax, wf_*, which checks the scoping and linearity constraints
- a bunch of proofs that show how the relations above are related (for instance, well-formedness respects structural equivalence and permutation equivalence


`Contexts.v`

Defines contexts and renaming for de Bruijn representations.  These definitions and proofs capture the structure of contexts and their isomorphisms, as well as how they interact with renamings.

# Compiles with Rocq 9.0
