# lean-matroids

A formalization of [matroids](https://en.wikipedia.org/wiki/Matroid) in [Lean](https://leanprover.github.io), so far following the (beginning of the) first chapter of *Matroid Theory*, by James Oxley. These files depend on and are inspired by the Lean [mathlib](https://github.com/leanprover/mathlib), and maybe someday some of this will make it in there as well.

Currently [`matroid.lean`](src/matroid.lean) contains:
* structures implementing the following formulations of matroids:
  * independent sets
  * circuits
  * bases
  * rank functions (only partially done)
* proofs that the circuit / basis formulations are equivalent to the independent set formulation, via explicit conversion functions
* proofs that the conversion functions are mutually inverse

Another file [`matroidexamples.lean`](src/matroidexamples.lean) contains:
* the independent set definitions of:
  * the loopy matroid (all subsets dependent)
  * the free matroid (all subsets independent)
  * the uniform matroid
* various explicit example computations involving the basis and circuit lemmas and functions defined in [`matroid.lean`](src/matroid.lean).

### Acknowledgements

Thanks to the denizens of the [Lean Zulip chat](https://leanprover.zulipchat.com) for patiently answering questions and providing proofs, several of which have been copied into this repository.
