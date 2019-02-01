Group theory in Agda
====================

**Authors:** Paul Seip, Boas Kluiving, Martin Karlsson, Sebastian Melzer\
**Supervised by:** Andrew Swan

The goal of this project is to formalize groups in homotopy type theory and prove a few basic results about them. In particular, we will show that in this formalization isomorphic groups are equal. Additionally, we prove that definable subgroups are normal, i.e. any map that uniformly transforms a group into a subgroup will return only normal subgroups.

The project is structured in the following files:
* `Group-basics.agda`\
   This file contains the basic definitions of a group, subgroup, homomorphism and isomorphism, as well as a few basic lemma's about them.
* `Magma-basics.agda`\
   The groups in this project are defined in terms of a more basic algebraic structure called Magma. This file contains the definition of a Magma plus some results about the equivalences between Magma's. This file was provided to us by Andrew Swan for the project.
* `Goal1_isom_groups_are_equal.agda`\
   In this file, we prove the goal that isomorphic groups are equal.
* `Goal2_definable_subgr_normal.agda`\
   In this file, we prove the goal that definable subgroups are normal.

### Goal 1: isomorphic groups are equal 

### Goal 2: definable subgroups are normal
One definition of normal subgroups is in terms of inner automorphisms (conjugation maps), namely that every inner automorphism maps the subgroup onto itself. We prove a more general result: that every definable subgroup is closed under any automorphism. 

For this, we make use of the result proven in Goal 1 that there exists an equivalence between isomorphisms and equality of groups. Because of this, we only need to show that definable subgroups are closed under the automorphism generated from the identity path.

To prove this, we need a few supporting results. First of all, we characterize the equality of subgroups. We show propositional extensionality: two subgroups are equal iff their propositions are equal. Secondly, we need to show that the map idtoiso (which transforms an equality into an isomorphism) from Goal 1 actually does this in the trivial way, i.e. with an identity map. Combining these results, we can show that every definable subgroup is indeed closed under any automorphism.

Subsequently, we define inner automorphisms, so we can apply the previous result to inner automorphisms and derive normality of definable subgroups in the above sense. Moreover, we prove that this definition of normality implies the common definition of normality, which then completes the proof.

Finally, we apply the main result to the example of the center of a group, showing that the center of a group is always a normal subgroup. This main result also allows us to prove the normality of other definable subgroups, such as the centralizer.
