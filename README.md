# Formalization of Typed Assembly Language (TAL) in Coq

![Build project](https://github.com/matthesjh/coq-tal/workflows/Build%20project/badge.svg)
[![Coq](https://img.shields.io/badge/coq-8.7.2%20%E2%80%93%208.18.0-brightgreen)](https://coq.inria.fr/)

This repository contains an implementation of [Typed Assembly Language](https://www.cs.cornell.edu/talc/), more specifically the simplified version TAL-0, in Coq.

The implementation was developed as part of a master's seminar. It is based on the chapter *Typed Assembly Language* from the book [*Advanced Topics in Types and Programming Languages*](https://www.cis.upenn.edu/~bcpierce/attapl/) and an already existing (but different) [implementation](https://github.com/ankitku/TAL0/) by Ankit Kumar.

## Usage

Please make sure that you have installed the Coq Proof Assistant on your operating system. The latest version of Coq can be found [here](https://coq.inria.fr/download).

**Note:** The files have been fully tested with Coq versions 8.7.2 to 8.18.0.

In order to compile the Coq files provided by this repository, the [`_CoqProject`](_CoqProject) file can be used.

```shell
coq_makefile -f _CoqProject -o Makefile
```

This generates a `Makefile` that can be executed with `make`. The generated `Makefile` resolves dependencies and calls the Coq compiler `coqc`. Subsequently, the files can be opened and imported.

## Documentation

The documentation for the Coq files provided by this repository can be found [here](https://matthesjh.github.io/coq-tal/).