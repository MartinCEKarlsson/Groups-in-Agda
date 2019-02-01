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
