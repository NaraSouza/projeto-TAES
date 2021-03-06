(** * Projeto de Topicos Avancados em Engenharia de Software *)

(* Equipe:

          - Nara Souza de Andrade (nsa2@cin.ufpe.br)
          - Sergio Machado de Arruda Filho (smaf2@cin.ufpe.br)
          - Tiago Sousa Carvalho (tsc2@cin.ufpe.br)

*)

(* ################################################################# *)
(** * Introduction *)

(** Esse projeto tem como objetivo apresentar uma implementacao funcional de arvores AVL,
    alem da analise de algumas de suas propriedades, juntamente com suas provas.
    Utilizaremos como base a implementacao de Binary Search Trees disponibilizada no
    Volume 3 - Verified Functional Algorithms. *)

From VFA Require Import SearchTree.
From VFA Require Import Perm.
Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.

(* ################################################################# *)
(** * Implementation *)

(** Tendo como base as funcoes sobre arvore ja definidas no capitulo de
    Binary Search Trees (Volume 3 - Verified Functional Algorithms), iremos
    definir a funcao de balanceamento de uma arvore AVL. Mas antes, para
    facilitar a implementacao da funcao de balanceamento, vamos definir uma
    funcao que calcula a altura de uma arvore. Tambem iremos definir as funcoes
    rotateLeft, rotateRight e calcBalance, responsaveis por executar as rotacoes
    necessarias para o balanceamento e calcular o fator de balanceamento de uma arvore,
    respectivamente.*)

Module AVL (Import I:Int).

Local Notation int := I.t.

Notation  "a <? b" := (I.ltb a b)
                          (at level 70) : Int_scope.

Fixpoint height {V : Type} (t : tree V) : int :=
  match t with
  | E => 0
  | T l k v r => 1 + (max (height l) (height r))
  end.

Definition rotate_left {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => match r with 
                 |E => E 
                 | T l' x' v' r' => T (T E x v E) x' v' r'
                 end
  end.

Definition rotate_right {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => match l with 
                 |E => E 
                 | T l' x' v' r' => T l' x' v' (T E x v E)
                 end
  end.

Definition calc_balance {V : Type} (t : tree V) : int :=
  match t with
  | E => 0
  | T l x v r => I.sub (height r) (height l)
  end.

Definition balance {V : Type} (t : tree V) : tree V :=
  match t with
  | E => t
  | T l x v r => if 1 <? calc_balance t then 
                                       if calc_balance r <? 0 then rotate_left (T l x v (rotate_right r)) 
                                                             else rotate_left t
                 else if calc_balance t <? -(1) then 
                                               if 0 <? calc_balance l then rotate_right ( T (rotate_left l) x v r) 
                                                                     else rotate_right t
                 else t
  end.

(** * Agora, definiremos a funcao de insert, que utilizara a funcao de balance sempre
      que uma insercao for realizada. *)

Fixpoint insert' {V : Type} (x : key) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if y >? x then balance (T (insert' x v l) y v' r)
                 else if x >? y then balance (T l y v' (insert' x v r))
                      else T l x v r
  end.

(** * Terminada a implementacao, vamos partir para as provas de propriedades. *)

(** * Para que uma arvore seja considerada AVL, todos os seus nos precisam 
      respeitar a seguinte propriedade:

      |hd(u) - he(u)| <= 1, onde hd(u) e a altura da subarvore direita do no u 
      e he(u) e a altura da subarvore esquerda do no u. 
      
      Definiremos a funcao AVL para que possamos checar quando uma arvore 
      satisfaz essa propriedade ou no. *)

(** * Checa se o modulo de um numero e maior que 1. *)

Definition le1 (i : int) : Prop :=
  if 1 <? (max i (-i)) then False else True.

Fixpoint AVL {V : Type} (t: tree V) : Prop :=
  match t with
  | E => True
  | T l x v r => BST t /\ le1 (calc_balance t) /\ AVL l /\ AVL r
  end.

(** * Agora podemos utiliza-la para provar as propriedades abaixo: *)

(** * Propriedade 1: uma arvore vazia e uma AVL. *)

Theorem empty_tree_AVL : forall (V : Type),
    AVL (@empty_tree V).
Proof.
  unfold empty_tree. constructor. Qed.

(** * Propriedade 2: uma insercao em uma arvore AVL produz uma arvore AVL. *)

(** * Obs.: ForallT_insert e insert_BST foram provados no capitulo de SearchTree *)

Theorem insert_AVL : forall (V : Type) (k : key) (v : V) (t : tree V),
    AVL t -> AVL (insert k v t).
Proof.
  intros. induction t0.
  - simpl. split.
    + auto.
    + split. unfold le1. destruct (1 <? max (0 - 0) (- (0 - 0))) eqn:H'. 
      exact_no_check I. apply I. split. apply I. apply I.
  - simpl in H. destruct H. destruct H0. destruct H1. simpl. destruct (k0 >? k) eqn:H'.
    + simpl. split. destruct insert.
      * constructor. apply IHt0_1. apply H1. admit.
        constructor. unfold AVL in H2. Admitted.

(** * Funcoes auxiliares *)

Definition left_tree {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => l
  end.

Definition right_tree {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => r
  end.

(** * Propriedade 3: todos os nos de uma AVL tambem sao AVL. *)

Theorem nodes_AVL : forall (V : Type) (t : tree V), AVL t -> AVL (left_tree t) /\ AVL (right_tree t).
Proof.
  intros. split.
  - simpl. induction t0.
    + simpl. apply I.
    + simpl. simpl in H. destruct H. destruct H0. destruct H1. apply H1.
  - simpl. induction t0.
    + simpl. apply I.
    + simpl. simpl in H. destruct H. destruct H0. apply H1. Qed.

Fixpoint height' {V : Type} (t : tree V) : nat :=
  match t with
  | E => 0
  | T l k v r => 1 + (Nat.max (height' l) (height' r))
  end.

Definition abs_diff_height_subtrees {V : Type} (t : tree V) : nat :=
  match t with
    | E => 0
    | T l x v r => (Nat.max (height' r) (height' l)) - (Nat.min (height' r) (height' l))
  end.

(** * Propriedade 4: a altura das duas subarvores de todo no de uma AVL nunca difere em mais de 1. *)

Theorem subtree_height : forall (V : Type) (t : tree V), AVL t -> abs_diff_height_subtrees t <= 1.
Proof.
  intros. induction t0.
  - simpl. lia.
  - destruct H. destruct H0. destruct H1. apply IHt0_1 in H1. apply IHt0_2 in H2. Admitted.

End AVL.

(* 2021-08-08 *)