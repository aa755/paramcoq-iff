# paramcoq-iff


This work is described in the following paper: https://arxiv.org/abs/1705.01163

ICFP2017 reviews : http://www.cs.cornell.edu/~aa755/icfp2017Reviews.html

POPL2018 reviews : http://www.cs.cornell.edu/~aa755/popl2018Reviews.html

slides from an invited talk at the Coq Implementors Workshop 2017: https://coq.inria.fr/cocorico/CoqImplementorsWorkshop/CoqIW2017?action=AttachFile&do=get&target=CoqImplWorkshop2017Fixed.pdf



# Installation

Dependencies:

- Coq 8.6

- The `v8.6` branch of coq-ext-lib: https://github.com/coq-ext-lib/coq-ext-lib/ , which compiles with Coq trunk as well.

- The `cast86` branch of template-coq https://github.com/aa755/template-coq

- The `vcoq86` branch of SquiggleEq https://github.com/aa755/SquiggleEq

- The `coq86` branch of ReduceAway https://github.com/aa755/ReduceAwayVar

For each of the above, it should suffice to `git clone ...; git checkout [branch]; cd ...; make; sudo make install`.

After the dependencies are installed, run `make` at `reflective-paramcoq/`.

# Organization of this repo

- The core translation is implemented in [paramDirect.v](paramDirect.v) (search for for "Fixpoint translate"). It has a boolean argument (`piff`): `true` means IsoRel, `false` means AnyRel.
- The (deductive-style) AnyRel and IsoRel translations for inductive types is in [indType.v](indType.v)
- The (inductive-style) AnyRel and IsoRel translations for inductive props is in [indProp.v](indProp.v)

The example in Sec.6 of the paper can be found in:
- [/test-suite/iso/squiggle5.v](/test-suite/iso/squiggle5.v) (definitions and weak isorel translation)
- [/test-suite/iso/squiggle5StrongIso.v](/test-suite/iso/squiggle5StrongIso.v) (strong isorel translation)
- [test-suite/iso/squiggle5Impl2.v](test-suite/iso/squiggle5Impl2.v) (instantiation of above to get the free theorem)

[templateCoqMisc.v](templateCoqMisc.v) has functions to convert the de-Bruijn style representation of template-coq to an asbstract named representation (SquiggleEq library). The latter representation is described at:
www.math.ias.edu/vladimir/files/Anand_ICMS2016.pdf

(We found it error-prone to implement the translation in de-Bruijn style. The conversion from abstract de-Bruijn to abstract named representation has been generically proved correct in the SquiggleEq library (see termsDB.v))
