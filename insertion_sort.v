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
Require Import PeanoNat.

Lemma insertPreservesSorted :
  forall x l, Sorted le l -> Sorted le (insert x l).
Proof.
  (* Introduções das implicações*)
  intros.
  (* Indução em H*)
  induction H.
  (* O insert de um elemento em uma lista vazia mantém ela ordenada -> Trivial*)
  constructor.
  (* Lista vazia é ordenado*)
  constructor.
  (*Definição do HdRel_nil*)
  apply HdRel_nil.
  (*Expande a definição do insert*)
  simpl.
  (*Dois casos diferentes: x<=a ou x>a*)
  destruct (x <=? a) eqn:E.
  (*CASO ONDE x<=a*)
  (*Reescreve x<=a da maneira usual*)
  apply Nat.leb_le in E.
  (*Aplicação da definição*)
  constructor.
  (*Quebra a prova pelo construtor do Sorted_cons*)
  apply Sorted_cons.
  (*Exatamente a hipótese H*)
  - exact H.
  (*Exatamente a hipótese H0*)
  - exact H0.
  (*Provar que HdRel le x (a::l), ou seja, provar que x <= a tendo x<=a como hipótese (Hipótese E)*)
  - auto. 
  (*Provar que se x>a -> Sorted le (a :: insert x l)*)
  (*Utiliza o constructor para abrir a prova*)
  - constructor. 
  (*Exatamente a hipótese IHSorted*)
  exact IHSorted. 
  (*Reescreve da maneira usual*)
  apply Nat.leb_gt in E. 
  (*Dois casos possíveis -> l pode ser vazia ou não*)
  destruct l as [| h t]. 
  (*Se l é vazia -> só aplicar o construtor para expandir*)
  constructor. 
  (*Finaliza essa parte da prova*)
  auto with arith. 
  (*No caso onde l não é vazio: x>=h ou x<h, onde h é a cabeça da lista*)
  destruct (x <=? h) eqn:E1. 
  (*Se x<=h. Abre a definição de insert*)
  unfold insert. 
  (*Reescreve a prova usando H1, já que ela aparece na conclusão*)
  rewrite E1. 
  (*Queremos provar HdRel le a (x :: h :: t) tendo a < x*)
  (*Só escreve da forma habitual*)
  apply Nat.leb_le in E1. 
  (*Aplica o construtor de HdRel*)
  constructor. 
  (*Finaliza a prova já que se a < x então a <= x*)
  lia.
  (*Expande só o insert*)
  cbn [insert]. 
  (*Reescreve a prova usando H1*)
  rewrite E1. 
  (*Definições do HdRel*)
  apply HdRel_cons. 
  (*Forma habitual de se escrever*)
  apply Nat.leb_gt in E1. 
  (*Quer se provar a <= h e se tem HdRel le a (h :: t), que diz exatamente em sua definição*)
  inversion H0. 
  (*A partir do inversion se consegue algumas hipóteses implicitas, sendo uma delas a <= h que é o que se quer provar*)
  exact H2.
 Qed.
 
  
  
  
Theorem insertion_sort_correct: forall l, Sorted le (insertion_sort l) /\ Permutation (insertion_sort l) l.
Proof.
  induction l as [|h tl IH].
  simpl. split. apply Sorted_nil.
  apply perm_nil.
  simpl.
  split.
  apply insertPreservesSorted.