# reflective-paramcoq


https://arxiv.org/abs/1705.01163

Dependencies:


The cast branch of template-coq https://github.com/aa755/template-coq

The dev branch of SquiggleEq https://github.com/aa755/SquiggleEq

For each of the above, it should suffice to `git clone ...; git checkout [branch]; cd ...; make; sudo make install`.

After the dependencies are installed, run `make` at `reflective-paramcoq/`.

The core translation is implemented in paramDirect.v#translate. It has a boolean argument (`piff`): `true` means IsoRel, `false` means AnyRel.
The (deductive-style) AnyRel and IsoRel translations for inductive types is in indType.v
The (inductive-style) AnyRel and IsoRel translations for inductive props is in indProp.v

templateCoqMisc.v has functions to convert the de Bruijn style representation of template-coq to an asbstract named representation (SquiggleEq library). The latter representation is described at:
www.math.ias.edu/vladimir/files/Anand_ICMS2016.pdf
