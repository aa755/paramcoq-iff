1. In the one example included (Section 5), what is the free theorem being used?

We will try to include the full statement of the free theorem in the Appendix. Note that the full statement depends on translations of other objects mentioned in item being translated. It also depends
on some combinators that our translation uses.

2. What's the point of R in IffProps?

IffProps only depends on the type of R, not on R itself. In our notation, Coq can infer the two types (propositions) by the type of R. But, we can indeed remove the R argument of IffProps.

3. Requiring relationships that are both total and one-to-one (i.e. isomorphisms) is a very strong requirement. For example, one-to-one-ness doesn't seem to be satisfied in the Bessel-Descartes fable, right?

Right. ...



