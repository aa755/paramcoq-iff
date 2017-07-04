# reflective-paramcoq

This work is described in the following paper:
https://arxiv.org/abs/1705.01163

ICFP2017 reviews and rebuttal : http://www.cs.cornell.edu/~aa755/ICFP2017.pdf

slides from an invited talk at the Coq Implementors Workshop 2017: https://coq.inria.fr/cocorico/CoqImplementorsWorkshop/CoqIW2017?action=AttachFile&do=get&target=CoqImplWorkshop2017Fixed.pdf

## opam installation:
This requires several dependencies, which can be install via opam:

```sh
opam pin -k git add coq-template-coq https://github.com/aa755/template-coq#cast
opam pin -k git add coq-squiggleeq https://github.com/aa755/SquiggleEq#dev
```

Then, install this package via: `opam pin -k git add coq-reflective-paramcoq https://github.com/aa755/paramcoq-iff`

## Manual installation:

Dependencies:

The cast branch of template-coq https://github.com/aa755/template-coq

The dev branch of SquiggleEq https://github.com/aa755/SquiggleEq

For each of the above, it should suffice to `git clone ...; git checkout [branch]; cd ...; make; sudo make install`.

After the dependencies are installed, run `make` at `reflective-paramcoq/`.

The core translation is implemented in paramDirect.v#translate. It has a boolean argument (`piff`): `true` means IsoRel, `false` means AnyRel.
The (deductive-style) AnyRel and IsoRel translations for inductive types is in indType.v
The (inductive-style) AnyRel and IsoRel translations for inductive props is in indProp.v

templateCoqMisc.v has functions to convert to/from between the de Bruijn style representation of template-coq and an asbstract named representation (SquiggleEq library). The Squiggle library has abstract proofs of many properties about substimitution, alpha equality, de-bruijn to/from named conversions. It is described at:
www.math.ias.edu/vladimir/files/Anand_ICMS2016.pdf
