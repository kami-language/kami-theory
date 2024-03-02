
# Formalization of the theory of the Kami language

[Kami]() aims to become a programming language for building distributed systems integrated with the rust ecosystem.
The language will be built on solid theoretical foundations. This repository contains a first formalization of the
core type theory behind the language.

## Description
Kami is based on [Modal Type Theory]() (MTT), with a system of modalities that encodes the location of computation. Its
nearest relative in the space of languages for distributed systems are "choreographic programming languages", in
particular [Chor-Lambda](). The difference is that, being an instance of MTT, we support full dependent types. Nevertheless,
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




### Dependencies




