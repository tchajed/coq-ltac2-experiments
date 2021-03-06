# Experiments with Ltac2

[![Build Status](https://travis-ci.com/tchajed/coq-ltac2-experiments.svg?branch=master)](https://travis-ci.com/tchajed/coq-ltac2-experiments)

You might also want to look at an [Ltac2
Tutorial](https://github.com/tchajed/ltac2-tutorial) that I wrote.

## [string.v](src/string.v)

Implements conversion from Gallina strings to Gallina identifiers, and exports
this functionality to Ltac1.

## [matching.v](src/matching.v)

An example of matching over the goal and manipulating hypotheses.

## [deex.v](src/deex.v)

A tactic that destructs exists in the hypotheses and preserves existing names.
Illustrates getting identifiers from binders, passing ident variables to
primitive tactics, and generating fresh names.

## [Ltac2Lib.v](src/Ltac2Lib.v)

A library that gives enough Ltac1 functionality to make Software Foundations
work. Includes a comment explaining how to handle some other incompatibilities
which can't be fixed with code (or at least I don't know how to).

Demonstrates how to wrap Ltac1 with Ltac2 tactics. This is more complicated than
using Ltac1 from an Ltac2 proof _script_, where `ltac1:(...)` around the
original code usually works, because the wrapper has to be a closed value.

## [playground.v](src/playground.v)

Assorted experiments from trying to do anything with Ltac2.
