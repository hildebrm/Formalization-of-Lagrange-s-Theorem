Require Import Coq.Setoids.Setoid.

Section Group.

(*
Definition of our group class, which takes four parameters, G, op, e, and inv. 
G is the type of the group, op is the binary operation, e is the identity element, 
and inv is the inverse function. The group operation is associative, the group contains
an element, e, such that for all a in G, a * e = a = e * a, and for all a in G, there exists
an element, inv a, such that a * inv a = e = inv a * a. The inverse of the identity element is
the identity element, and the identity element is the identity element of the group operation.
*)

Class Group (G : Type) (op : G -> G -> G) (e : G) (inv : G -> G) : Prop :=
{
  group_associativity : forall a b c : G, op (op a b) c = op a (op b c);
  group_identity_r : forall a : G, (op (a) e) = a;
  group_identity_l : forall a : G, (op e (a)) = a;
  group_inverse_r : forall a : G, op a (inv a) = e;
  group_inverse_l : forall a : G, op (inv a) a = e;
  group_inverse_identity : inv e = e;
  group_identity_middle : forall a b : G, op (op a e) b = op a b;
}.

Variable G : Type.
Variable op : G -> G -> G.
Variable e : G.
Variable inv : G -> G.

Notation "a * b" := (op a b).

Hypothesis group_axioms : Group G op e inv.


(*
A subgroup of a group, G, is a subset of G that is itself a group under the same operation.
The subgroup is closed under the operation, contains the identity element of G, and contains
the inverse of each of its elements. The subgroup is also associative under the operation.
One important detail of our structure is the existence of a subgroup carrier, which is a function
that maps elements of the subgroup to elements of the group. This is necessary for the definition
of left cosets, which are defined in terms of the subgroup carrier.
*)

Class subgroup (H : Type) (e' : H) := makeSubgroup{
  subgroup_carrier : H -> G;
  subgroup_op : H -> H -> H;
  subgroup_inv : H -> H;
  subgroup_associativity : forall h1 h2 h3 : H, subgroup_op h1 (subgroup_op h2 h3) = subgroup_op (subgroup_op h1 h2) h3;
  subgroup_identity_is_identity : subgroup_carrier e' = e;
  subgroup_closure : forall h1 h2 : H, subgroup_carrier (subgroup_op h1 h2) = ((subgroup_carrier h1) * (subgroup_carrier h2));
  subgroup_inverse_r : forall h : H, subgroup_op h (subgroup_inv h) = e';
  subgroup_inverse_l : forall h : H, subgroup_op (subgroup_inv h) h = e';
  subgroup_op_assoc_carry : forall h1 h2 h3 : H, subgroup_carrier (h1) * subgroup_carrier((subgroup_op h2 h3)) = subgroup_carrier (subgroup_op (subgroup_op h1 h2) h3);
  subgroup_inverse_carry : forall h : H, subgroup_carrier (subgroup_inv h) = inv (subgroup_carrier h);
  subgroup_carrier_injective: forall h1 h2 : H, subgroup_carrier(h1) = subgroup_carrier(h2) -> h1 = h2;
}.

Variable H : Type.
Variable subgroup_op : H -> H -> H.
Variable subgroup_e : H.
Variable subgroup_inv : H -> H.

Hypothesis subgroup_axioms : subgroup H subgroup_e.

Notation "[ a ]" := (subgroup_carrier a) (at level 40).
Notation "a <*> b" := (Group.subgroup_op a b) (at level 40).

Lemma subgroup_identity_l : forall h : H, h <*> subgroup_e = h.
Proof.
  intros.  apply subgroup_axioms. rewrite subgroup_closure, subgroup_identity_is_identity. 
  apply group_identity_r.
Qed.

Lemma subgroup_identity_r : forall h : H, subgroup_e <*> h = h.
Proof.
  intros. apply subgroup_axioms. rewrite subgroup_closure, subgroup_identity_is_identity. 
  apply group_identity_l.
Qed.

Lemma identity_retract : forall h : H, [h] = e -> h = subgroup_e.
Proof.
  intros h Heq. 
  apply subgroup_carrier_injective. rewrite subgroup_identity_is_identity. apply Heq.
Qed.


(*
A left coset of a subgroup, H, of a group, G, is a set of the form {g * h | h in H} for some g in G.
The left coset is a subset of G, and the elements of the left coset are the result of the group operation
applied to g and each element of H.
*)

Inductive sameLeftCoset (g1 g2 : G) : Prop :=
  | same_left_coset : forall (h : H),
                      op (inv g1) g2 = [h] -> 
                      sameLeftCoset g1 g2.

Definition leftCoset (g : G) : Type := {x : G | sameLeftCoset g x}.

(*
Here, we prove some properties about the group inverse, and then generalize them to also apply
to the subgroup inverse. We prove that the inverse of the inverse of an element is the element itself,
that the inverse of the product of two elements is the product of the inverses of the elements in reverse
and that the inverse of an element is unique.
*)

Lemma group_inverse_unique : forall g h : G,
    g * h = e -> h = inv g.
Proof.
  intros g h Heq.
  rewrite<-group_identity_r. rewrite <-Heq.
    rewrite <-group_associativity. rewrite group_inverse_l,
    group_identity_l.
  reflexivity.
Qed.

Lemma inverse_involution : forall g : G,
    inv (inv g) = g.
Proof using group_axioms.
  intros. symmetry. apply group_inverse_unique.
  apply group_inverse_l.
Qed.


Lemma inverse_anti_involution : forall g1 g2 : G,
    inv(g1 * g2) = (inv g2) * (inv g1).
Proof using group_axioms.
  intros. symmetry. apply group_inverse_unique.
  rewrite<-group_associativity.
  replace (g1*g2*inv g2) with g1.
  - rewrite group_inverse_r. reflexivity.
  - rewrite group_associativity, group_inverse_r, group_identity_r.
    reflexivity.
Qed.

Lemma subgroup_inverse_unique : forall h1 h2 : H,
  [Group.subgroup_op h1 h2] = e -> [h2] = [Group.subgroup_inv h1].
Proof.
  intros h1 h2 Heq.
  rewrite <- group_identity_r. rewrite <- Heq.
  rewrite subgroup_op_assoc_carry with (h1 := Group.subgroup_inv h1) (h2 := h1) (h3 := h2).
  rewrite subgroup_inverse_l with (h := h1).
  rewrite subgroup_closure, subgroup_identity_is_identity, group_identity_l.
  reflexivity.
Qed.

Lemma subgroup_inverse_involution : forall h : H,
  [Group.subgroup_inv (Group.subgroup_inv h)] = [h].
Proof.
  intros. symmetry. apply subgroup_inverse_unique. 
  rewrite subgroup_inverse_l. apply subgroup_identity_is_identity.
Qed.


Lemma subgroup_inverse_anti_involution : forall h1 h2 : H,
  [Group.subgroup_inv (Group.subgroup_op h1 h2)] = [Group.subgroup_op (Group.subgroup_inv h2) (Group.subgroup_inv h1)].
Proof.
  intros. symmetry. apply subgroup_inverse_unique.
  repeat rewrite <- subgroup_associativity. rewrite subgroup_closure. assert (HP: h2 <*> (Group.subgroup_inv h2 <*> Group.subgroup_inv h1) = Group.subgroup_inv h1).
  { rewrite subgroup_associativity. rewrite subgroup_inverse_r. rewrite subgroup_identity_r. reflexivity. } 
  rewrite HP. rewrite <- subgroup_closure. rewrite subgroup_inverse_r. rewrite subgroup_identity_is_identity. reflexivity.
Qed.


(*
Now, we prove some properties about left cosets. We prove that sameLeftCoset is reflexive, symmetric, and transitive.
We also prove that the left coset bijection is a bijection, and that the left coset bijection maps left cosets to left cosets.
This gives us an intuitive idea that left cosets are equivalent to each other, and form a partition of the group.
*)

Lemma sameLeftCoset_refl : forall g : G, sameLeftCoset g g.
Proof.
  intros. apply same_left_coset with (h := subgroup_e). 
  rewrite group_inverse_l. rewrite subgroup_identity_is_identity. reflexivity.
Qed.

Lemma sameLeftCoset_symm : forall g1 g2 : G, sameLeftCoset g1 g2 -> sameLeftCoset g2 g1.
Proof.
  intros g1 g2 HP.
  inversion HP; subst.
  apply same_left_coset with (h := Group.subgroup_inv h). rewrite subgroup_inverse_carry. rewrite <- H0. rewrite inverse_anti_involution. rewrite inverse_involution. reflexivity.
Qed.

Lemma sameLeftCoset_trans : forall g1 g2 g3 : G, sameLeftCoset g1 g2 -> sameLeftCoset g2 g3 -> sameLeftCoset g1 g3.
Proof using group_axioms.
  intros g1 g2 g3 HP1 HP2. 
  inversion HP1; subst.
  inversion HP2; subst.
  apply same_left_coset with (h := Group.subgroup_op h h0). 
  rewrite subgroup_closure. rewrite <-H0, <-H1, group_associativity. 
  rewrite <- group_associativity with (a := g2) (b := inv g2) (c := g3). 
  rewrite group_inverse_r. rewrite <- group_associativity. rewrite group_identity_middle. reflexivity.
Qed.


Definition leftCosetBijection (g1 g2 x:G) : G :=
  g2 * (inv g1) * x.

Lemma leftCosetBijectionIsBijection (g1 g2 x:G) :
  (leftCosetBijection g1 g2 (leftCosetBijection g2 g1 x)) = x.
Proof using group_axioms.
  unfold leftCosetBijection.
  repeat rewrite<-group_associativity.
  replace (g2*inv g1*g1) with g2.
  - rewrite group_inverse_r, group_identity_l.
    reflexivity.
  - rewrite group_associativity, group_inverse_l,
      group_identity_r.
    reflexivity.
Qed.

Lemma leftCosetBijectionCosets : forall (g1 g2 x : G),
    sameLeftCoset g1 x ->
    sameLeftCoset g2 (leftCosetBijection g1 g2 x).
Proof using group_axioms.
  intros g1 g2 x H1.
  inversion H1. unfold leftCosetBijection.
  rewrite group_associativity, H0.
  econstructor.
  rewrite<-group_associativity, group_inverse_l.
  apply group_identity_l.
Qed.

Definition leftCosetBijection' (g1 g2:G):
  leftCoset g1 -> leftCoset g2 :=
  fun xP => match xP with
            | exist _ x P =>
                exist _ (leftCosetBijection g1 g2 x)
                  (leftCosetBijectionCosets g1 g2 x P)
            end.

(*Need to define G mod sameLeftCoset x H -> G that essentially takes the correst representative from each coset
and maps to to an element in H*)


Add Parametric Relation : G sameLeftCoset
  reflexivity proved by sameLeftCoset_refl
  symmetry proved by sameLeftCoset_symm
  transitivity proved by sameLeftCoset_trans
as sameLeftCoset_rel.

Notation "g1 ~ g2" := (sameLeftCoset_rel g1 g2) (at level 40).

Axiom CanonicalRepresentative : G -> G.

Axiom CanonicalRepProp1 : forall g : G, sameLeftCoset g (CanonicalRepresentative g).
Axiom CanonicalRepProp2: forall g1 g2 : G, sameLeftCoset g1 g2 -> CanonicalRepresentative g1 = CanonicalRepresentative g2.

Axiom retract : leftCoset e -> H.



End Group.