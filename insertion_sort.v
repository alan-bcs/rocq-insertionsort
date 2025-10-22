Require Import Arith Lia.
Require Import List.
Import ListNotations.

(** * Ordenação por Inserção *)

Fixpoint insert (x:nat) l :=
  match l with
  | [] => [x]
  | h::tl => if (x <=? h)
             then x::l
             else h::(insert x tl)
  end.

Fixpoint insertion_sort (l: list nat) :=
  match l with
  | []  => []
  | h::tl => insert h (insertion_sort tl)
  end.

Require Import Sorted.
Require Import Permutation.

Theorem insertion_sort_correct: forall l, Sorted le (insertion_sort l) /\ Permutation (insertion_sort l) l.
Proof.
  Admitted.
