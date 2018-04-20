# Formalization of Typed Assembly Language (TAL) in Coq

This repository contains an implementation of [Typed Assembly Language](https://www.cs.cornell.edu/talc/), more specifically the simplified version TAL-0, in Coq.

The implementation was developed as part of a masters seminar. It is based on the chapter *Typed Assembly Language* from the book [*Advanced Topics in Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/attapl/) and an already existing (but different) [implementation](https://github.com/ankitku/TAL0/) by Ankit Kumar.

## Usage

In order to compile the Coq files provided by this repository, the [`_CoqProject`](_CoqProject) file can be used.

```shell
coq_makefile -f _CoqProject -o Makefile
```

This generates a `Makefile` that can be executed with `make`. The generated `Makefile` resolves dependencies and calls the Coq compiler `coqc`. Subsequently, the files can be opened and imported.