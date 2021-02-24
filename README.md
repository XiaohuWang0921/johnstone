Monic endomorphisms on the subobject classifier
===============================================

This is a formalization of a [proof](https://ncatlab.org/toddtrimble/published/Monic+endomorphisms+on+the+subobject+classifier) of the so called [_Johnstone's exercise_](https://ncatlab.org/nlab/show/subobject+classifier#johnstones_exercise), which states that every monic endomorphism on the subobject classifier of a topos is an involution, i.e. a self-inverse isomorphism.

The proof is formalized in both [Lean](https://leanprover.github.io/) and [Coq](https://coq.inria.fr/), interpreting the type of all propositions `Prop` in both languages as the subobject classifier, assuming the axiom of propositional extensionality (`propext` in Lean and `PropExtensionality.propositional_extensionality` in Coq).

I have made the somewhat unusual choice of writing the proof completely in functional style, i.e. without using tactics, even in Coq, since this seems to be one of the rare cases where Coq's poor support for dependent pattern-matching does not give me a headache. Also I have spared myself the effort of writing any comments. If you are confused and would like to know what my code is doing, please email me and I will arrange a meeting to explain what I did, since I, an unfortunate extrovert with social anxiety, am in grave need for human interactions within my comfort zone.