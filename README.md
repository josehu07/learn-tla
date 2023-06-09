# TLA+/PlusCal Tutorial Solutions

![languages](https://img.shields.io/github/languages/count/josehu07/learn-tla?color=green)
![top-lang](https://img.shields.io/github/languages/top/josehu07/learn-tla?color=purple)
![code-size](https://img.shields.io/github/languages/code-size/josehu07/learn-tla?color=lightgrey)
![license](https://img.shields.io/github/license/josehu07/learn-tla)

This repo contains TLA+ video course solutions adapted from [Lamport's TLA+ video course](https://lamport.azurewebsites.net/video/videos.html) and PlusCal tutorial solutions adapted from [Lamport's PlusCal tutorial](https://lamport.azurewebsites.net/tla/tutorial/contents.html).

* All PlusCal code in this repo uses the [P-syntax](https://lamport.azurewebsites.net/tla/p-manual.pdf) (instead of the [C-syntax](https://lamport.azurewebsites.net/tla/c-manual.pdf)).
* All sessions are made runnable with the [VSCode TLA+ extension](https://github.com/tlaplus/vscode-tlaplus) (instead of the heavy-weight [TLA+ Toolbox IDE](https://lamport.azurewebsites.net/tla/toolbox.html)).

## Checking Models

To generate a TLA+ specification from PlusCal:

1. Change into a session folder `SessionX/`.
2. Open a chosen example module `SessionX*.tla`.
3. Run the **TLA+: Parse module** command on this file.
    * TLA+ specification code will be generated from the PlusCal comment.
    * This step is already done for all PlusCal sessions in this repo.

To let TLC check a TLA+ model with parameters:

1. Open the corresponding configuration file `*_MC.cfg`.
    * Tweak model checking configurations as desired.
2. Open the corresponding model-checkable module `*_MC.tla`.
    * Tweak model parameters as desired.
3. Run the **TLA+: Check model with TLC** command on this `*_MC.tla` file.

If everything goes well, a model-checking result panel should appear at side.

## TODO List

* [x] PlusCal tutorial
* [x] TLA+ video course
* [ ] Dr. TLA+ series?
