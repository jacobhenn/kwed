# kwed

kwed `/kwɛd/` is a minimalist proof assistant with \[planned\] support for higher inductive types.

when it is in a workable state, the type theory will generally be the same as book HoTT.

the end goal is to have a very minimalistic type theory with the ability to formalize all of modern mathematics in either a classical or constructive setting, depending on the selective use of axioms.

a possible future goal is to rewrite the foundations of the system to be based on a cubical type theory in order to remove the need to depend on function extensionality and univalence as axioms. however, the current state of cubical type theory is not as simple and certainly not as intuitive as book HoTT, so this may not fit with the overall goal of the project.

# roadmap

- [x] basic induction
- [ ] inductive type families
- [ ] path induction
- [ ] higher inductive types
- [ ] enforce strict positivity
- [ ] universe levels
- [ ] write standard library
- [ ] higher inductive-inductive types
- [ ] rigorously examine and justify all features within a model of UF
- [ ] cubical foundations??
