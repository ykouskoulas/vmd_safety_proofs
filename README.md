# Controller synthesis for guaranteed-safe collision avoidance maneuvers

## What is this?

This repository contains a peer-reviewed publication describing an
adaptive controller for collision-avoidance that is synthesized using
plug-in safety guarantees for each available maneuver. The controller
derives guarantees of safety and correctness partly from the
properties of the associated with maneuvers that are plugged into it.

## Documentation

The paper is titled

*"Provably Safe Controller Synthesis Using Safety Proofs as Building
Blocks"*

and was presented at the 7th international conference in Software
Engineering Research and Innovation in 2019. It describes a controller
that can safely, adaptively switch between collision-avoidance
maneuvers and is guaranteed to be safe if the maneuvers themselves
have certain safety guarantees. The paper provides pseudocode and an
informal proof of correctness for the controller, and provides example
safety guarantees with machine-checked proofs of safety and
correctness for vertical aircraft collision avoidance maneuvers from
prior work.

Abstract:

We describe an approach to developing a veriﬁed
controller using hybrid system safety predicates. It selects from
a dictionary of sequences of control actions, interleaving them
and under model assumptions guaranteeing their continuing
safety in unbounded time. The controller can adapt to changing
priorities and objectives during operation. It can confer safety
guarantees on a primary controller, identifying, intervening,
and remediating actions that might lead to unsafe conditions
in the future. Remediation is delayed until the latest time at
which a safety-preserving intervention is available. When the
assumptions of the safety proofs are violated, the controller
provides altered but quantiﬁable safety guarantees. We apply
this approach to synthesize a controller for aircraft collision
avoidance, and report on the performance of this controller
as a stand-alone collision avoidance system, and as a safety
controller for the FAA’s next-generation aircraft collision
avoidance system ACAS X.

## To build and check the proofs

```
$ coqtop --version
The Coq Proof Assistant, version 8.10.2 (December 2019)
compiled on Dec 8 2019 9:00:07 with OCaml 4.07.1
$ make
coqc seot_util.v
coqc analysis.v
coqc vmd.v
$
```

## About me

Work/projects: https://www.linkedin.com/in/ykouskoulas

Publications:  https://orcid.org/0000-0001-7347-7473

This repo:     https://github.com/ykouskoulas/vmd_safety_proofs
