(*begin hide*)
Require Import Arith Lia.
Require Import List.
Import ListNotations.
Require Import Sorted.
Require Import Permutation.
Require Import PeanoNat.
(*end hide*)

(** * Introdução  *)

(** 
Este trabalho apresenta uma prova formal da correção do algoritmo de ordenação por inserção (*insertion sort*). 
A formalização foi desenvolvida no assistente de provas Coq. O assistente de provas Coq utiliza o sistema de 
Dedução Natural, o que o torna adequado para o desenvolvimento de atividades computacionais na disciplina de 
Lógica Computacional 1. Conforme discutido em aula, provas matemáticas realizadas apenas em papel estão suscetíveis 
a erros humanos, ambiguidades e saltos lógicos. O uso de uma ferramenta formal como o Coq é fundamental 
para mitigar esses riscos, garantindo o rigor e a correção mecânica de cada passo da demonstração.
*)

(** Observação sobre o ambiente de prova: A formalização deste projeto foi realizada utilizando 
a plataforma online jsCoq (disponível em https://jscoq.github.io/scratchpad.html). 
As versões específicas utilizadas foram o jsCoq 0.12.3, executando sobre o núcleo do Coq versão 8.12.2 (build 81200).*)



(** * Definição dos Algoritmos *)

(** O algoritmo de ordenação por inserção é composto por duas funções principais. A primeira é a função 
auxiliar [insert], que insere um número natural em uma lista que já está ordenada, mantendo a ordenação. *)

Fixpoint insert (x:nat) l :=
  match l with
  | [] => [x]
  | h::tl => if (x <=? h)
             then x::l
             else h::(insert x tl)
  end.

(** A função principal [insertion_sort] percorre a lista de entrada recursivamente, 
inserindo cada elemento na cauda já ordenada. *)

Fixpoint insertion_sort (l: list nat) :=
  match l with
  | []  => []
  | h::tl => insert h (insertion_sort tl)
  end.

(** * Propriedades Auxiliares *)

(** Para provar a correção total do algoritmo, precisamos estabelecer duas propriedades fundamentais sobre a função de inserção:
*)
(** 1. Ela preserva a ordenação dos elementos.
*)
(** 2. Ela preserva o conjunto de elementos (é uma permutação).*)


(** ** Preservação da Ordenação *)

(** O lema a seguir garante que, se inserirmos um elemento [x] em uma lista [l] que já está ordenada 
([Sorted]), a lista resultante também estará ordenada. A prova é feita por indução estrutural 
na lista [l] e análise de casos sobre a comparação entre [x] e a cabeça da lista. *)

Lemma insertPreservesSorted :
  forall x l, Sorted le l -> Sorted le (insert x l).
(*begin hide*)
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
(*end hide*)

(** A prova é realizada por indução na evidência de que a lista [l] já está ordenada ([H : Sorted le l]).
    - Caso Base (Lista Vazia): A inserção de [x] em uma lista vazia resulta na lista unitária [[x]], que é trivialmente ordenada.
    - Passo Indutivo: Supondo uma lista da forma [a :: tl] onde a cauda [tl] também é ordenada, temos dois cenários baseados na comparação entre [x] e a cabeça [a]:
        - Se [x <= a]: O elemento [x] torna-se a nova cabeça da lista ([x :: a :: tl]). Como [x <= a] e o restante da lista já estava ordenado, a propriedade é preservada.
        - Se [x > a]: O algoritmo insere [x] recursivamente na cauda [tl]. Pela hipótese de indução, sabemos que essa inserção 
        recursiva gera uma lista ordenada. Resta apenas provar que a cabeça original [a] preserva a ordem em relação à nova lista gerada, o que é garantido pois [a < x] e [a] já era menor ou igual a todos os elementos de [tl].
*)
 
(** ** Preservação da Permutação *)

(** Além da ordenação, é necessário garantir que a operação de inserção não duplica nem remove elementos indevidamente. 
O lema abaixo estabelece que a lista resultante de [insert x l] é uma permutação da lista [x :: l]. *)

Lemma insertPreservesPerm : forall x l, Permutation (x :: l) (insert x l).
(*begin hide*)
Proof.
  (*indução estrutural em l*)
  induction l.
    (*Caso base*)
    - auto.
    (*(Passo indutivo) dois casos diferentes: x<=a ou x>a*)
    - destruct (x <=? a) eqn:E.
      (*Caso x <= a*)
      (*Simplifica insert e reescreve E. Como os termos ficam idênticos, usamos reflexividade*)
      * simpl. rewrite E. reflexivity.
      (*Caso x > a*)
      (*simplifica insert (x vai para a cauda) e reescreve E*)
      * simpl. rewrite E.
      (*Usamos transitividade para forçar a troca (swap) entre a cabeça 'a' e 'x'*)
      apply perm_trans with (l' := a :: x :: l). 
      (*resolve a troca*)
      apply perm_swap.
      (*ignora a cabeça "a" presente nos dois lados*)
      apply perm_skip. 
      (*usamos nossa hipotese*)
      apply IHl.
Qed.
(*end hide*)

(** * Teorema Principal *)
  
Theorem insertion_sort_correct: forall l, Sorted le (insertion_sort l) /\ Permutation (insertion_sort l) l.
(*begin hide*)
Proof.
  (*inducao estrutural na lista l*)
  induction l as [|h tl IH].
  (*Caso base: lista vazia*) 
  simpl. split. apply Sorted_nil. apply perm_nil.
  
  (*Passo indutivo*)
  (*Expande a definicao de insert*)
  simpl.
  (*divide o "goal" em dois "subgoals" devido a conjução*)
  split.
  
  (*usamos o lema auxiliar: inserir num lista ordenada mantém a ordenação*)
  apply insertPreservesSorted.
  (*quebrar IH em duas hipoteses*)
  destruct IH as [H_sorted H_perm].
  (*usamos nossa hipotese*)
  apply H_sorted.
  (*usamos transitividade com um passo intermediário onde 'h' está na cabeça*)
  apply perm_trans with (l' := h :: insertion_sort tl).
  (*para a primeira parte, invertemos para usarmos o lema auxiliar*)
  symmetry. apply insertPreservesPerm.
  (*ignoramos a cabeça pois são iguais e focamos na calda*)
  apply perm_skip.
  (*quebramos a hipotese*)
  destruct IH as [H_sorted H_perm].
  (*aplicamos a hipotese*)
  apply H_perm.
Qed.
(*end hide*)
