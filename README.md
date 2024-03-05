<!--
SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>

SPDX-License-Identifier: MIT
-->

# Formalization of the theory of the Kami language

[Kami](https://nlnet.nl/project/Kami/) aims to become a programming language for building distributed systems integrated with the rust ecosystem.
The language will be built on solid theoretical foundations. This repository contains a first formalization of the
core type theory behind the language.

## Description
Kami is based on [Modal Type Theory](http://www.danielgratzer.com/papers/phd-thesis.pdf) (MTT), with a system of modalities that encodes the location of computation. Its
nearest relative in the space of languages for distributed systems are "choreographic programming languages", in
particular [Chor-Lambda](https://arxiv.org/abs/2111.03701). The difference is that, being an instance of MTT, we support full dependent types. Nevertheless,
early implementation will keep dependent types out of scope.

A full description of the language will follow in a forthcoming document.

## About this repository

This repository contains an Agda implementation of the MTT type theory, in particular:
 - A "mode solver" for deciding equality of 2-cells in a 2-category specified by generators and two-dimensional rewrite rules,
   as required for MTT.
 - A specification of the typing rules of MTT, based on a previous Agda formalization of dependent type theory by
   Joakim Öhman et al. (See [their repo](https://github.com/mr-ohman/logrel-mltt/) for more info).
 - A series of examples which reproduce the derivation of crisp induction for booleans and natural numbers, following
   chapter 6 of the MTT thesis. This induction principle is required for our motivating use-case:
   To specify a program where the communication behaviour depends arbitrarily on previously communicated values, thus
   showcasing the power of dependent types for choreographic programs. We show that it is possible to describe a program
   which communicates a vector of arbitrary length between two participants - by first sending the length $n$, and consequently
   sending $n$ elements of the vector. Such a choreography cannot be formulated in Chor-Lambda, simply on the grounds that
   dependent types are required. And to tame the interactions of dependent types with annotations of locality, the sound
   foundations of MTT are indispensable.

### Structure

All relevant implementation details are located under the `src/KamiTheory/Main` path. The most important files pertaining
to the type theory are:
  - `../Main/Dependent/Untyped/Definition.agda` contains the raw terms of dependent Kami.
  - `../Main/Dependent/Typed/Definition.agda` contains all typing judgements.
  - `../Main/Dependent/Typed/Instances.agda` contains a partial type checking algorithm useful for the examples.
  - `../Main/Dependent/Typed/Examples` contains various examples culminating in the vector-sending choreography.

The type theory is built on top of a generic mode theory parametrized by a 2-category given by generators and rewrite rules.
For Kami, we implemented the type theory generically, but afterwards specialize to our particular mode theory of local and
global computations.

The generic formalization of mode theories is under the path `../Main/Generic/ModeSystem`. Especially the interactions
between 2-cells required quite some implementation work, to be found in the various subfolders of `ModeSystem/2Cell`.
The instantiation of the particular mode theory of Kami happens in `../ModeSystem/2Graph/Example.agda`, `../ModeSystem/2Cell/Example.agda`
and `../ModeSystem/ModeSystem/Example.agda`.

### Dependencies

In order to re-check or edit the Agda files, the following dependencies are required:
 - A recent version of [Agda](https://github.com/agda/agda)
 - The [agda standard library](https://github.com/agda/agda-stdlib)
 - The [agda-prelude](https://github.com/UlfNorell/agda-prelude)
 - The [agora](https://github.com/determi-io/agora) library, which was developed previously by the author,
   but required some changes to facilitate the current project.

The libraries have to be installed as described in the [agda manual](https://agda.readthedocs.io/en/v2.6.4.2/tools/package-system.html).

After having added all dependencies, in the folder `src/KamiTheory/Main/Dependent/Typed/Examples/`, run

```
agda SendingVector2.agda
```

to typecheck the main example and all its dependencies. Note that, while the example may look deceptively simple, it depends on the previous examples,
and in particular on the normalization algorithms for 2-cells.

## Funding

This project is funded through [NGI Zero Core](https://nlnet.nl/core), a fund established by [NLnet](https://nlnet.nl) with financial support from the European Commission's [Next Generation Internet](https://ngi.eu) program. Learn more at the [NLnet project page](https://nlnet.nl/Kami).

[<img src="https://nlnet.nl/logo/banner.png" alt="NLnet foundation logo" width="20%" />](https://nlnet.nl)
[<img src="https://nlnet.nl/image/logos/NGI0_tag.svg" alt="NGI Zero Logo" width="20%" />](https://nlnet.nl/core)

