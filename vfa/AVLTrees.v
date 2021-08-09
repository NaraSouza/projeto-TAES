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
Require Import Coq.Init.Nat.
From VFA Require Import Perm.


(* ################################################################# *)
(** * Implementation *)

(** Tendo como base as funcoes sobre arvore ja definidas no capitulo de
    Binary Search Trees (Volume 3 - Verified Functional Algorithms), iremos
    definir a funcao de balanceamento de uma arvore AVL. Mas antes, para
    facilitar a implementacao da funcao de balanceamento, vamos definir uma
    funcao que calcula a altura de uma arvore. Tambem iremos definir as funcoes
    rotateLeft e rotateRight, alem de outras funcoes auxiliares.*)

Fixpoint height {V : Type} (t : tree V) : nat :=
  match t with
  | E => 0
  | T l x v r => 1 + (max (height l) (height r))
  end.

Definition rootKey {V : Type} (t : tree V) : key :=
  match t with
  | E => 0
  | T l x v r => x
  end.

Definition rootValue {V : Type} (d : V) (t : tree V) : V :=
  match t with
  | E => d
  | T l x v r => v
  end.

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

Definition rotateLeft {V : Type} (d : V) (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => T (T E x v E) (rootKey r) (rootValue d r) (rightTree r)
  end.

Definition rotateRight {V : Type} (d : V) (t : tree V) : tree V :=
  match t with
  | E => E
  | T l x v r => T (leftTree l) (rootKey l) (rootValue d l) (T E x v E)
  end.

Definition balance {V : Type} (d : V) (t : tree V) : tree V :=
  match t with
  | E => t
  | T l x v r => if (height l - height r) >? 1 then rotateLeft d t
                else if (height r - height l) >? 1 then rotateRight d t
                     else t
  end.

(** * Agora, definiremos a funcao de insert, que utilizara a funcao de balance sempre
      que uma insercao e realizada. *)

Fixpoint insert' {V : Type} (x : key) (v : V) (d : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if x <? y then balance d (T (insert' x v d l) y v' r)
                 else if x >? y then balance d (T l y v' (insert' x v d r))
                      else T l x v r
  end.

(* 2021-08-08 *)