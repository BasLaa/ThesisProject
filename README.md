# Bachelor thesis code

## Compilation Instructions
An existing installation of Coq is required to compile the files. Find more information at: [Install Coq](https://coq.inria.fr/download)

The code comes with a Makefile, so that the code can simply be compiled with `make`:
```
$ git clone https://github.com/BasLaa/ThesisProject.git
$ cd ThesisProject
$ make
```
All files are now compiled and can be run through.

## Files
- `BoolSet.v` defines sets on boolean functions
- `Definitions.v` defines traces and external behaviours
- `Composition.v` defines composition for external behaviours
- `Prefix.v` defines prefixes and the related properties
- `IO.v` defines input-output behaviours and conversion functions
- `IOComposition.v` defines composition of input-output behaviours
- `InputEnabling.v` defines input-enabling and start a proof of closure under composition (note: proof not complete)
- `Example.v` shows that input-enabling is preserved by composition for a simple example of input-output behaviours
