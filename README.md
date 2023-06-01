# TLA+/PlusCal Tutorial Material

PlusCal tutorial material adapted from [Lamport's tutorial](https://lamport.azurewebsites.net/tla/tutorial/contents.html).

All PlusCal code in this repo use the [P-syntax](https://lamport.azurewebsites.net/tla/p-manual.pdf) (instead of the [C-syntax](https://lamport.azurewebsites.net/tla/c-manual.pdf)). All sessions are made runnable with the [VSCode TLA+ extension](https://github.com/tlaplus/vscode-tlaplus) (instead of the heavy-weight [TLA+ Toolbox IDE](https://lamport.azurewebsites.net/tla/toolbox.html)).

**TODO**: finish sessions 9-11...

## Checking Models

To generate a TLA+ specification from PlusCal and check a model with parameters:

1. Change into a session folder `SessionX/`
2. Open a chosen example module `SessionX*.tla`
3. Run the **TLA+: Parse module** command on this file
    - TLA+ specification code will be generated from the PlusCal comment
    - This step is already done for all modules in this repo
4. Open the corresponding configuration file `SessionX*_MC.cfg`
    - Tweak model checking configurations as desired
5. Open the corresponding model-checkable module `SessionX*_MC.tla`
    - Tweak model parameters as desired
6. Run the **TLA+: Check model with TLC** command on this `_MC.tla` file

A model-checking result panel should appear at side.
