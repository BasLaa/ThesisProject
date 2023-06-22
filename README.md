# Bachelor thesis code

## Compilation Instructions
An existing installation of Coq is required to compile the files. Find more information at: [Install Coq](https://coq.inria.fr/download)

The code comes with a Makefile, so that the code can simply be compiled with `make`:
```
$ git clone https://github.com/BasLaa/ThesisProject.git
$ cd ThesisProject
$ make
```
All Coq files, contained in the folder `theories`, are now compiled and can be run through.

Note that if you are using CoqIDE or Proof General to run through the theories,
you might find that the IDE complains that the files were compiled with a different version of Coq.
If this happens, you can either fix the Coq version of the IDE to match your coqc compiler or compile inside CoqIDE as follows:

- run `make clean` in the terminal to remove the previous compilation if necessary
- Open the first file `BoolSet.v` in CoqIDE and run `make` from within CoqIDE: `Compile` -> `make`
- If this doesn't work, it's because CoqIDE is running `make` inside the `theories` folder instead of the parent directory; there are two options to fix this:

1. Fix this by going to `Edit` -> `Preferences` -> `Externals`. Change the `make` command to something like `cd ..; make` or anything that sequences `cd ..` with the command `make` on your OS. Try running `make` inside CoqIDE once again.
2. Fix this by instead opening a file located in the parent directory in CoqIDE: Open File -> Change the setting in bottom right from 'Coq source code' to 'all'. Then open README.md. Now go to `Compile` -> `make` to run the command from the current directoey.

## Files
- `BoolSet.v` defines sets on boolean functions
- `Definitions.v` defines traces and external behaviours
- `Composition.v` defines composition for external behaviours
- `Prefix.v` defines prefixes and the related properties
- `IO.v` defines input-output behaviours and conversion functions
- `IOComposition.v` defines composition of input-output behaviours
- `InputEnabling.v` defines input-enabling and start a proof of closure under composition (note: proof not complete)
- `Example.v` shows that input-enabling is preserved by composition for a simple example of input-output behaviours
