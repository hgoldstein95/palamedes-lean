Inductive Label := Pub | Sec.

Inductive pub_label : Label -> Prop :=
    | PubLabel : pub_label Pub.

Inductive sec_label : Label -> Prop :=
    | SecLabel : sec_label Sec.

Inductive Atom : Type := Atm (x:nat) (l:Label).

Inductive atom_elements : nat -> Label -> Atom -> Prop :=
    | Elts x l : atom_elements x l (Atm x l).

Inductive Stack :=
| Mty                         
| Cons (a:Atom) (s:Stack)     
| RetCons (pc:Atom) (s:Stack).

Inductive mty : Stack -> Prop :=
    | Empty : mty Mty.

Inductive stack_hd : Stack -> Atom -> Prop :=
    | HdCons : forall a s, stack_hd (Cons a s) a
    | HdRetCons : forall a s, stack_hd (RetCons a s) a.

Inductive stack_cons_tl : Stack -> Stack -> Prop :=
    | TlCons : forall a s, stack_cons_tl (Cons a s) s.

Inductive stack_retcons_tl : Stack -> Stack -> Prop :=
    | TlRetCons : forall a s, stack_retcons_tl (RetCons a s) s.

Inductive stack_len : Stack -> nat -> Prop :=
    | LenMty : stack_len Mty 0
    | LenCons : forall n a s, stack_len s n -> stack_len (Cons a s) (S n)
    | LenRetCons : forall n a s, stack_len s n -> stack_len (RetCons a s) (S n).

Inductive good_atom : Atom -> Prop :=
| g0 : forall l, good_atom (Atm 0 l)
| g1 : forall l, good_atom (Atm 1 l).

Inductive good_stack : nat -> Stack -> Prop :=
| GoodStackMty  : good_stack 0 Mty
| GoodStackCons : forall n a s , good_atom a  -> good_stack n s -> good_stack (S n) (Cons a s)
| GoodStackRet  : forall n pc s, good_atom pc -> good_stack n s -> good_stack (S n) (RetCons pc s).
