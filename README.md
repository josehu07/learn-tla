# TLA+/PlusCal Tutorial Solutions

![languages](https://img.shields.io/github/languages/count/josehu07/learn-tla?color=green)
![top-lang](https://img.shields.io/github/languages/top/josehu07/learn-tla?color=purple)
![code-size](https://img.shields.io/github/languages/code-size/josehu07/learn-tla?color=lightgrey)
![license](https://img.shields.io/github/license/josehu07/learn-tla)

This repo contains:

* TLA+ video course solutions adapted from [Lamport's TLA+ video course](https://lamport.azurewebsites.net/video/videos.html)
* PlusCal tutorial solutions adapted from [Lamport's PlusCal tutorial](https://lamport.azurewebsites.net/tla/tutorial/contents.html)
* Dr. TLA+ lecture series material directly linked from [here](https://github.com/tlaplus/DrTLAPlus/tree/master)
* Dr. TLA+ series specifications cleansed and extended with PlusCal by me (WIP)

All PlusCal code in this repo uses the [P-syntax](https://lamport.azurewebsites.net/tla/p-manual.pdf) (instead of the [C-syntax](https://lamport.azurewebsites.net/tla/c-manual.pdf)). All sessions are made runnable with the [VSCode TLA+ extension](https://github.com/tlaplus/vscode-tlaplus) (instead of the canonical [TLA+ Toolbox IDE](https://lamport.azurewebsites.net/tla/toolbox.html)).

## Checking Finite-State Models

To generate a TLA+ specification from PlusCal:

1. Change into a session folder `SessionX/`
2. Open a chosen example module `SessionX*.tla`
3. Run the **TLA+: Parse module** command on this file
    * TLA+ specification code will be generated from the PlusCal comment
    * This step is already done for all PlusCal sessions in this repo

To let TLC check a TLA+ model with parameters:

1. Open the corresponding configuration file `*_MC.cfg`
    * Tweak model checking configurations as desired
2. Open the corresponding model-checkable module `*_MC.tla`
    * Tweak model parameters as desired
3. Run the **TLA+: Check model with TLC** command on this `*_MC.tla` file

If everything goes well, a model-checking result panel should appear at side.

## General Proofs w/ TLAPS

TLAPS is a new addition to TLA+ using SMT solvers to support general, possibly unbounded-state theorem proving. The VSCode extension currently does not offer TLAPS integration (see progress [here](https://github.com/tlaplus/vscode-tlaplus/issues/153)). Also, there is no official tutorial about TLAPS that is complete and publicly available right now. New things might be added to this repo as TLAPS becomes increasingly mature.

## Other Useful Links

* [Learn TLA+ wiki](https://learntla.com/index.html)
* [TLA+ examples gallery](https://github.com/tlaplus/Examples)
* [PlusCal P-syntax manual](https://lamport.azurewebsites.net/tla/p-manual.pdf)
* [PlusCal cheatsheet](https://d3s.mff.cuni.cz/f/teaching/nswi101/old/pluscal.pdf)
* [TLA+ language summary](https://lamport.azurewebsites.net/tla/summary.pdf)
* [Beyond the Toolbox doc](https://learntla.com/topics/cli.html)

## TODO List

* [x] PlusCal tutorial
* [x] TLA+ video course
* [ ] Dr. TLA+ series
* [ ] TLAPS proofs?
