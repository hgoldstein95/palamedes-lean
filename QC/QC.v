(* Inductive Definitions and QuickChick generators for Palamedes RQ2. Tested with Coq 8.20 *)


From QuickChick Require Import QuickChick.

Inductive X1 : nat -> Prop :=
| C1_a : forall v, v = 2 -> X1 v.

Derive Generator for (fun v => X1 v).
(* Sample (genST (fun v => X1 v)). *)

Inductive X2 : nat -> Prop :=
| C2_a : forall v, 2 = v -> X2 v.

Derive Generator for (fun v => X2 v).
(* Sample (genST (fun v => X2 v)). *)

Inductive X3 : nat -> Prop :=
| C3_a : forall v, v = 2 -> X3 v
| C3_b : forall v, v = 5 -> X3 v.

Derive Generator for (fun v => X3 v).
(* Sample (genST (fun v => X3 v)). *)

Inductive X4 : nat -> Prop :=
| C4_a : forall v, v = 2 -> X4 v
| C4_b : forall v, v = 5 /\ True -> X4 v.

(* Instance should be in the base library, but nobody uses `True` really... *)
Instance decTrue : Dec True.
Proof. constructor; left; exact I. Defined.

Derive Generator for (fun v => X4 v).
(* Sample (genST (fun v => X4 v)). *)

(* X5 out of scope *)

Inductive less : nat -> nat -> Prop :=
| less_n : forall n, less n n
| less_S : forall m n, less n m -> less n (S m).
Derive Generator for (fun x => less n x).
Derive Checker for (less x y).
Merge (fun y => less x y) With (fun y => less y z) As between.
Derive Generator for (fun x => between a b x).

Inductive X6 : nat -> Prop :=
| C6_a : forall n, between 5 10 n -> X6 n.

Derive Generator for (fun v => X6 v).
(* Sample (genST (fun v => X6 v)). *)

Inductive X7 : nat -> Prop :=
| C7_a : forall n, less (S 5) n -> X7 n.

Derive Generator for (fun v => X7 v).
(* Sample (genST (fun v => X7 v)). *)

Inductive X8 : nat -> Prop :=
| C8_a : forall n, n = 0 -> X8 n
| C8_b : forall n, between 5 10 n -> X8 n.

Derive Generator for (fun v => X8 v).
(* Sample (genST (fun v => X8 v)). *)

Inductive AllTwos : list nat -> Prop :=
| AllTwoNil  : AllTwos nil
| AllTwoCons : forall l, AllTwos l -> AllTwos (cons 2 l).

Derive Generator for (fun l => AllTwos l).
(* Sample (genST (fun l => AllTwos l)). *)

Inductive EvenLen : list nat -> Prop :=
| EvenNil : EvenLen nil
| EvenCC  : forall x y l, EvenLen l -> EvenLen (cons x (cons y l)).

Derive Generator for (fun l => EvenLen l).
(* Sample (genST (fun l => EvenLen l)). *)

Merge (fun l => AllTwos l) With (fun l => EvenLen l) As X10.
Derive Generator for (fun l => X10 l).
(* Sample (genST (fun l => X10 l)). *)

Inductive IncrByOneAux : nat -> list nat -> Prop :=
| IncrNil : forall x, IncrByOneAux x nil
| IncrCons: forall x l, IncrByOneAux (S x) l -> IncrByOneAux x (cons x l).

Derive Generator for (fun l => IncrByOneAux n l).
(* Sample (genST (fun l => IncrByOneAux 0 l)). *)

Inductive Len : nat -> list nat -> Prop :=
| LenNil : Len 0 nil
| LenCons: forall n l x, Len n l -> Len (S n) (cons x l).

Derive Generator for (fun l => Len n l).
(* Sample (genST (fun l => Len 5 l)). *)

Merge (fun l => AllTwos l) With (fun l => Len n l) As X14.
Derive Generator for (fun l => X14 n l).
(* Sample (genST (fun l => X14 4 l)). *)

Inductive IsSortedBetween : nat -> nat -> list nat -> Prop :=
| ISB_nil  : forall lo hi, IsSortedBetween lo hi nil
| ISB_cons : forall lo hi x l,
  between lo hi x -> IsSortedBetween x hi l ->
  IsSortedBetween lo hi (cons x l).

Derive Generator for (fun l => IsSortedBetween lo hi l).
(* Sample (genST (fun l => IsSortedBetween 0 10 l)). *)

Inductive Even : nat -> Prop :=
| Even_0  : Even 0
| Even_SS : forall n, Even n -> Even (S (S n)).
Derive Generator for (fun n => Even n).

Inductive AllEven : list nat -> Prop :=
| AE_Nil  : AllEven nil
| AE_Cons : forall x l, Even x -> AllEven l -> AllEven (cons x l).

Derive Generator for (fun l => AllEven l).
(* Sample (genST (fun l => AllEven l)). *)

Inductive IsTrue : bool -> Prop :=
| IsTrue_ : IsTrue true.

Derive Generator for (fun b => IsTrue b).
(* Sample (genST (fun b => IsTrue b)). *)

Inductive NotIn : nat -> list nat -> Prop :=
| NInil : forall x, NotIn x nil
| NIcons: forall x y l, x <> y -> NotIn x l -> NotIn x (cons y l).
Derive Checker for (NotIn n l).

Inductive UniqueAux : list nat -> list nat -> Prop :=
| Unil  : forall l, UniqueAux l nil
| Ucons : forall x xs sofar,
    NotIn x sofar ->
    UniqueAux (cons x sofar) xs ->
    UniqueAux sofar (cons x xs).
Derive Generator for (fun l => UniqueAux L l).
(* Sample (genST (fun l => UniqueAux nil l)). *)

Inductive Elem : nat -> list nat -> Prop :=
| ElNow : forall x l, Elem x (cons x l)
| ElLat : forall x y l, Elem x l -> Elem x (cons y l).
Derive Generator for (fun x => Elem x l).

Inductive DupAux : list nat -> list nat -> Prop :=
| DupNow   : forall x sofar l, Elem x sofar -> DupAux sofar (cons x l)
| DupLater : forall x sofar l, DupAux (cons x sofar) l -> DupAux sofar (cons x l).

Derive Generator for (fun l => DupAux L l).
(* Sample (genST (fun l => DupAux nil l)). *)

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.
Derive Show for Tree.
Derive Arbitrary for Tree.

From Coq Require Import Nat. (* Possible compatibility issue with newer Rocq *)

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    between (succ lo) (pred hi) x ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive Generator for (fun t => bst lo hi t).
(* Sample (genST (fun t => bst 0 17 t)). *)

Inductive complete : nat -> Tree -> Prop :=
| Comp_leaf : complete 0 Leaf
| Comp_node : forall n x l r, complete n l -> complete n r -> complete (S n) (Node x l r).

Derive Generator for (fun t => complete n t).
(* Sample (genST (fun t => complete 3 t)). *)

Inductive maxDepth : nat -> Tree -> Prop :=
| MD_leaf : forall n, maxDepth n Leaf
| MD_node : forall n x l r, maxDepth n l -> maxDepth n r -> maxDepth (S n) (Node x l r).

Derive Generator for (fun t => maxDepth n t).
(* Sample (genST (fun t => maxDepth 2 t)).*)

Inductive NonEmpty : Tree -> Prop :=
| NENode : forall x l r, NonEmpty (Node x l r).
Derive Generator for (fun t => NonEmpty t).
(* Sample (genST (fun t => NonEmpty t)). *)

(* Transcribed from Palamedes' example, not the one from QuickChick's own repo *)
Inductive Label := Pub | Sec.
Derive (Arbitrary, Show) for Label.

Inductive Atom : Type := Atm (x:nat) (l:Label).
Derive (Arbitrary, Show) for Atom.

Inductive Stack :=
| Mty                         
| Cons (a:Atom) (s:Stack)     
| RetCons (pc:Atom) (s:Stack).
Derive Show for Stack.

Inductive good_atom : Atom -> Prop :=
| g0 : forall l, good_atom (Atm 0 l)
| g1 : forall l, good_atom (Atm 1 l).
Derive Generator for (fun a => good_atom a).

Inductive good_stack : nat -> Stack -> Prop :=
| GoodStackMty  : good_stack 0 Mty
| GoodStackCons : forall n a s , good_atom a  -> good_stack n s -> good_stack (S n) (Cons a s)
| GoodStackRet  : forall n pc s, good_atom pc -> good_stack n s -> good_stack (S n) (RetCons pc s).

Derive ArbitrarySizedSuchThat for (fun s => good_stack n s).
(* Sample (genST (fun s => good_stack 3 s)). *)

(* STLC in separate file due to setup *)

(* between already exists *)

Inductive bal : nat -> Tree -> Prop :=
| bal_leaf0 : bal 0 Leaf
| bal_leaf1 : bal 1 Leaf
| bal_node : forall n t1 t2 m,
    bal n t1 -> bal n t2 -> bal (S n) (Node m t1 t2).

Merge (fun t => bst lo hi t) With (fun t => bal n t)
      As AVL.
Derive Generator for (fun t => AVL lo hi n t).
(* Sample (genST (fun t => AVL 0 17 2 t)). *)

Inductive color :=
| red : color
| black : color.

Inductive tree :=
| leaf : tree
| node : color -> nat -> tree -> tree -> tree.

Inductive RBT_aux : color -> nat -> tree -> Prop :=
| rbt_leaf :
  forall c, RBT_aux c 1 leaf
| rbt_black_node :
  forall x c1 c2 h t1 t2,
    RBT_aux c1 h t1 -> RBT_aux c2 h t2 ->
    RBT_aux black (S h) (node black x t1 t2)
| rbt_red_node :
  forall x h t1 t2, 
    RBT_aux black h t1 -> RBT_aux black h t2 ->
    RBT_aux red h (node red x t1 t2).

Derive (Arbitrary, Show) for color.
Derive (Arbitrary, Show) for tree.
Derive Generator for (fun t => RBT_aux c n t).
(* Sample (genST (fun t => RBT_aux black 2 t)). *)

(* bst rewritten for colors *)
Inductive bst' : nat -> nat -> tree -> Prop :=
| bst_leaf' : forall lo hi, bst' lo hi leaf
| bst_node' : forall c lo hi x l r,
    between (succ lo) (pred hi) x ->
    bst' lo x l -> bst' x hi r ->
    bst' lo hi (node c x l r).

Derive Generator for (fun t => bst' lo hi t).

Merge (fun t => RBT_aux c n t) With (fun t => bst' lo hi t) As RBT.
Derive Generator for (fun t => RBT c n lo hi t).
(* Sample (genST (fun t => RBT black 2 0 17 t)). *)
