# DON Calculus

You can build the proof by running `./build.sh`, which will build the docker
container and check the proof (it will take a few minutes). The proof is
verified when the command finishes without an error code.

Building can also be done by running `make`, assuming a recent version of Coq
is installed locally.

# Paper-to-artifact correspondence

The paper is represented through a series of Coq files.

- SyntaxRuntime.v - Section 3
- OperationalSemantics.v - Section 4
- Typing.v - Section 5
- MetaTheoryBase.v - Section 6
- MetaTheoryLocalConfluence.v - Section 6
- MetaTheoryTyping.v - Section 6
- MetaTheory.v - Section 6

The most important theorems and corollaries are in MetaTheory.v.

There are inline comments throughout the files with direct references to the paper. They
are repeated here for convenience (file followed by line number):

- SyntaxRuntime.v:19:         (* Fig 6: Abstract Syntax and Fig 8: Runtime Definitions *)
- OperationalSemantics.v:209: (* Fig 11: Operational Semantics *)
- OperationalSemantics.v:262: (* Fig 12: Temporal Locality Optimization *)
- Typing.v:21:                (* Fig 13: Type system *)
- MetaTheoryTyping.v:2027:    (* Lemma 6.1 *)
- MetaTheoryTyping.v:1198:    (* Lemma 6.2 *)
- MetaTheoryTyping.v:2750:    (* Theorem 6.3 *)
- MetaTheory.v:249:           (* Theorem 6.5 and Corollary 6.7 *)
- MetaTheory.v:267:           (* Theorem 6.6 *)

# Assumptions

We have no `admit` statements in the proof, and the only axioms we use are for
generating fresh labels and keys, functional extension, and principal of
noetherian (well-founded) induction.
