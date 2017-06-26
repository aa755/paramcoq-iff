# paramcoq-iff

Dependencies:

commit `f4cec75fe74ff3f66f401efab357cae79124d984` in the `trunk` branch of Coq https://github.com/coq/coq. Later versions cause compilation errors in template-coq, likely due to changes in the representation of universes caused by cumulative universes in inductives.

The `v8.6` branch of coq-ext-lib: https://github.com/coq-ext-lib/coq-ext-lib/ , which compiles with Coq trunk as well.

The `castTrunkPreUnivPoly` branch of template-coq https://github.com/aa755/template-coq

The `vcoq87` branch of SquiggleEq https://github.com/aa755/SquiggleEq

The `master` branch of ReduceAway https://github.com/aa755/example-plugin


For each of the above, it should suffice to `git clone ...; git checkout [branch]; cd ...; make; sudo make install`.

After the dependencies are installed, run `make` at `reflective-paramcoq/`.

The core translation is implemented in paramDirect.v#translate. It has a boolean argument (`piff`): `true` means IsoRel, `false` means AnyRel.
The (deductive-style) AnyRel and IsoRel translations for inductive types is in indType.v
The (inductive-style) AnyRel and IsoRel translations for inductive props is in indProp.v

templateCoqMisc.v has functions to convert the de Bruijn style representation of template-coq to an asbstract named representation (SquiggleEq library). The latter representation is described at:
www.math.ias.edu/vladimir/files/Anand_ICMS2016.pdf
