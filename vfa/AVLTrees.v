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

Module AVL.

Fixpoint height {V : Type} (t : tree V) : nat :=
  match t with
  | E => 0
  | T l k v r => 1 + (Nat.max (height l) (height r))
  end.

Definition rotateLeft {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => match r with 
                 |E => E 
                 | T l' x' v' r' => T (T E x v E) x' v' r'
                 end
  end.

Definition rotateRight {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => match l with 
                 |E => E 
                 | T l' x' v' r' => T l' x' v' (T E x v E)
                 end
  end.

Definition calcBalance {V : Type} (t : tree V) : nat :=
  match t with
  | E => 0
  | T l x v r => 2 + (height r) - (height l)
  end.

Definition balance {V : Type} (t : tree V) : tree V :=
  match t with
  | E => t
  | T l x v r => if 3 <? calcBalance t then 
                                       if calcBalance r <? 2 then rotateLeft (T l x v (rotateRight r)) 
                                                             else rotateLeft t
                 else if calcBalance t <? 1 then 
                                               if 2 <? calcBalance l then rotateRight ( T (rotateLeft l) x v r) 
                                                                     else rotateRight t
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

Fixpoint AVL {V : Type} (t: tree V) : Prop :=
  match t with
  | E => True
  | T l x v r => 1 <= (calcBalance t) /\ (calcBalance t) <= 3 /\ AVL l /\ AVL r
  end.

(** * Agora podemos utiliza-la para provar as propriedades abaixo: *)

(** * Propriedade 1: uma arvore vazia e uma AVL. *)

Theorem empty_tree_AVL : forall (V : Type),
    AVL (@empty_tree V).
Proof.
  unfold empty_tree. constructor. Qed.

(** * Propriedade 2: uma insercao em uma arvore AVL produz uma arvore AVL. *)
Theorem insert_AVL : forall (V : Type) (k : key) (v : V) (t : tree V),
    AVL t -> AVL (insert k v t).
Proof.
  intros. induction t.
  - simpl;lia.
  - simpl. destruct (T (insert k v t1) k0 v0 t2) eqn:H'.
    + destruct (k0 >? k) eqn:H''.
      * simpl. apply I.
      * destruct (k >? k0) eqn:H'''. unfold AVL in H. 
        

(** * Funcoes auxiliares *)
Definition leftTree {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => l
  end.

Definition rightTree {V : Type} (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => r
  end.

(** * Propriedade 3: todos os nos de uma AVL tambem sao AVL. *)
Theorem nodes_AVL : forall (V : Type) (t : tree V), AVL t -> AVL (leftTree t) /\ AVL (rightTree t).
Proof.
  intros. split.
  - simpl. induction t0.
    + simpl. apply I.
    + simpl. simpl in H. destruct H. destruct H0. apply H0.
  - simpl. induction t0.
    + simpl. apply I.
    + simpl. simpl in H. destruct H. destruct H0. apply H1. Qed.
  

(** * Propriedade 4: a altura das duas subarvores de todo no de uma AVL nunca difere em mais de 1. *)
Theorem subtree_height : forall (V : Type) (t : tree V), AVL t -> 1 <=?
                         I.sub (height (rightTree t)) (height (leftTree t)) /\
                         I.sub (height (leftTree t)) (height (rightTree t)) <=? 1.

End AVL.

(* 2021-08-08 *)