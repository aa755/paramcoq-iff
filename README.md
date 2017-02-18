# reflective-paramcoq

Dependencies:


The v85origin  branch of coq : https://github.com/aa755/coq/commits/v85origin

The v85-patched branch of paramcoq: https://github.com/aa755/paramcoq/

The cast branch of template-coq https://github.com/aa755/template-coq

The dev branch of SquiggleEq https://github.com/aa755/SquiggleEq

The first 2 should not be needed, but they are currently needed to invoke the old parametricity plugin for comparison purposes. For each of the above, it should suffice to `git clone ...; cd ...; make; sudo make install`.

After the dependencies are installed, run `make` at `reflective-paramcoq/`. The translation is implemented in `paramDirect.v`. There are several example invokations in `test-suite/` and `test-suite/iso`
