Require Import Coq.Program.Basics.
	Module Recover.


	Inductive Rec (E : Type) (V : Type) : Type :=
	| Success (v : V)
	| Recover (e : E) (v : V)
	| Failure (e : E).

	Definition bimap {A B C D: Type} (f: A -> C) (g: B -> D) (r: Rec A B) : Rec C D :=
		match r with
		| Success _ _ v => Success _ _ (g v)
		| Recover _ _ e v => Recover _ _ (f e) (g v)
		| Failure _ _ e => Failure _ _ (f e)
	end.

	Definition fst {A B C: Type} (f: A -> C) (r: Rec A B) : Rec C B :=
		match r with
		| Success _ _ v => Success _ _ v
		| Recover _ _ e v => Recover _ _ (f e) v
		| Failure _ _ e => Failure _ _ (f e)
	end.

	Definition snd {A B C: Type} (f: B -> C) (r: Rec A B) : Rec A C :=
		match r with
		| Success _ _ v => Success _ _ (f v)
		| Recover _ _ e v => Recover _ _ e (f v)
		| Failure _ _ e => Failure _ _ e
	end.

	Theorem bimap_prop : forall (A B : Type) (r: Rec A B) (f:A -> A) (g:B->B),
		(forall x, f(x) = x) -> (forall x, g(x) = x) -> bimap f g r = r.
	Proof.
		intros A B r f g.
		intros fID gID.
		destruct r as [v | e v | e] eqn:E.
		- simpl. rewrite -> gID. reflexivity.
		- simpl. rewrite -> gID,fID. reflexivity.
		- simpl. rewrite -> fID. reflexivity.
	Qed.

	Theorem fst_prop : forall (A B : Type) (r: Rec A B) (f:A -> A),
		(forall x, f(x) = x) -> fst f r = r.
	Proof.
		intros A B r f.
		intros fID.
		destruct r as [v | e v | e] eqn:E.
		- simpl. reflexivity.
		- simpl. rewrite -> fID. reflexivity.
		- simpl. rewrite -> fID. reflexivity.
	Qed.

	Theorem snd_prop : forall (A B : Type) (r: Rec A B) (g:B->B),
		(forall x, g(x) = x) -> snd g r = r.
	Proof.
		intros A B r g.
		intros gID.
		destruct r as [v | e v | e] eqn:E.
		- simpl. rewrite -> gID. reflexivity.
		- simpl. rewrite -> gID. reflexivity.
		- simpl. reflexivity.
	Qed.

	Theorem both_prop : forall (A B : Type) (r: Rec A B) (f:A -> A) (g:B->B),
		bimap f g r = compose (fst f) (snd g) r.
	Proof.
		intros A B r f g.
		destruct r as [v | e v | e] eqn:E.
		- simpl. unfold compose. simpl. reflexivity.
		- simpl. unfold compose. simpl. reflexivity.
		- simpl. unfold compose. simpl. reflexivity.
	Qed.

	Class Semigroup (A : Type) (op: A -> A -> A) : Prop :=
		{ op_assoc : forall a b c, op a (op b c) = op (op a b) c }.

	Class Monoid (A : Type) (op: A -> A -> A) (unit : A) `(SI: Semigroup A op) : Prop :=
		{ unip_prop : forall a, op a unit = a /\ op unit a = a }.

	Definition rec_op {E A: Type} {e_op: E -> E -> E} {SE: Semigroup E e_op}
		{a_op : A -> A -> A} {SA: Semigroup A a_op}
		(a b: Rec E A) :=
		match a, b with
			| Success _ _ a , Success _ _ aa => Success _ _ (a_op a aa)
			| Success _ _ a , Recover _ _ ee aa => Recover _ _ ee (a_op a aa)
			| Success _ _ a , Failure _ _ ee => Recover _ _ ee a
			| Recover _ _ e a , Success _ _ aa => Recover _ _ e (a_op a aa)
			| Recover _ _ e a , Recover _ _ ee aa => Recover _ _ (e_op e ee) (a_op a aa)
			| Recover _ _ e a , Failure  _ _ ee => Recover _ _ (e_op e ee) a
			| Failure _ _ e , Success _ _ aa => Recover _ _ e aa
			| Failure _ _ e , Recover _ _ ee aa => Recover _ _ (e_op e ee) aa
			| Failure _ _ e , Failure _ _ ee => Failure _ _ (e_op e ee)
		end.

	Instance rec_semigroup_instance :
		forall	(A : Type) (a_op: A -> A -> A) (SA: Semigroup A a_op)
				(E : Type) (e_op: E -> E -> E) (SE: Semigroup E e_op),
				Semigroup (Rec E A) rec_op.
	Proof.
		intros A a_op [a_op_assoc] E e_op [e_op_assoc].
		split.
		destruct a as [av | av ae | ae] eqn:Eqa.
		- destruct b as [bv | bv be | be] eqn:Eqb.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. rewrite a_op_assoc. reflexivity.
				* simpl. rewrite a_op_assoc. reflexivity.
				* simpl. reflexivity.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. rewrite a_op_assoc. reflexivity.
				* simpl. rewrite a_op_assoc. reflexivity.
				* simpl. reflexivity.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. reflexivity.
				* simpl. reflexivity.
				* simpl. reflexivity.
		- destruct b as [bv | bv be | be] eqn:Eqb.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. rewrite a_op_assoc. reflexivity.
				* simpl. rewrite a_op_assoc. reflexivity.
				* simpl. reflexivity.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. rewrite a_op_assoc. reflexivity.
				* simpl. rewrite a_op_assoc. rewrite e_op_assoc. reflexivity.
				* simpl. rewrite e_op_assoc. reflexivity.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. reflexivity.
				* simpl. rewrite e_op_assoc. reflexivity.
				* simpl. rewrite e_op_assoc. reflexivity.
		- destruct b as [bv | bv be | be] eqn:Eqb.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. reflexivity.
				* simpl. reflexivity.
				* simpl. reflexivity.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. reflexivity.
				* simpl. rewrite e_op_assoc. reflexivity.
				* simpl. rewrite e_op_assoc. reflexivity.
			+ destruct c as [cv | cv ce | ce] eqn:Eqc.
				* simpl. reflexivity.
				* simpl. rewrite e_op_assoc. reflexivity.
				* simpl. rewrite e_op_assoc. reflexivity.
	Qed.

	Definition pure
		{E A: Type} {op: E->E->E} {S:Semigroup E op}
		(a : A) : Rec E A := Success _ _ a.

	Definition ap {E A B: Type} {op: E->E->E} {S:Semigroup E op}
		(r:Rec E (A -> B)) (q:Rec E A) : (Rec E B) :=
		match r, q with
		| Success _ _ f , Success _ _ v => Success _ _ (f v)
		| Success _ _ f , Recover _ _ e v => Recover _ _ e (f v)
		| Success _ _ _ , Failure _ _ e => Failure _ _ e
		| Recover _ _ e f , Success _ _ v => Recover _ _ e (f v)
		| Recover _ _ e f , Recover _ _ ee v => Recover _ _ (op e ee) (f v)
		| Recover _ _ e _ , Failure _ _ ee => Failure _ _ (op e ee)
		| Failure _ _ e , Success _ _ _ => Failure _ _ e
		| Failure _ _ e , Recover _ _ ee _ => Failure _ _ (op e ee)
		| Failure _ _ e , Failure _ _ ee  => Failure _ _ (op e ee)
	end.

	Theorem identity : forall (E A : Type) (op:E->E->E) (S:Semigroup E op)
		(id: A -> A),
		(forall x, id x = x) -> forall (r:Rec E A), ap (pure id) r = r.
	Proof.
		intros E A op S id idf r.
		destruct r as [v | e v | e].
			- simpl. rewrite -> idf. reflexivity.
			- simpl. rewrite -> idf. reflexivity.
			- simpl. reflexivity.
	Qed.

	Theorem composition : forall (E A B C : Type) (op:E->E->E) (S:Semigroup E op)
		(u :Rec E (B -> C)) (v :Rec E (A -> B)) (w:Rec E A),
		ap (ap (ap (pure compose) u) v) w = ap u (ap v w).
	Proof.
		intros E A B C op S u v w.
		destruct S as [op_assoc].
		destruct u as [uv | ue uv | ue] eqn:Equ.
		- destruct v as [vv | ve vv | ve] eqn:Eqv.
			+ destruct w as [wv | we wv | we] eqn:Eqw.
				* simpl. unfold compose. reflexivity.
				* simpl. unfold compose. reflexivity.
				* simpl. unfold compose. reflexivity.
			+ destruct w as [wv | we wv | we] eqn:Eqw.
				* simpl. unfold compose. reflexivity.
				* simpl. unfold compose. reflexivity.
				* simpl. unfold compose. reflexivity.
			+ destruct w as [wv | we wv | we] eqn:Eqw.
				* simpl. unfold compose. reflexivity.
				* simpl. unfold compose. reflexivity.
				* simpl. unfold compose. reflexivity.
	- destruct v as [vv | ve vv | ve] eqn:Eqv.
		+ destruct w as [wv | we wv | we] eqn:Eqw.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. reflexivity.
		+ destruct w as [wv | we wv | we] eqn:Eqw.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
		+ destruct w as [wv | we wv | we] eqn:Eqw.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
	- destruct v as [vv | ve vv | ve] eqn:Eqv.
		+ destruct w as [wv | we wv | we] eqn:Eqw.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. reflexivity.
		+ destruct w as [wv | we wv | we] eqn:Eqw.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
		+ destruct w as [wv | we wv | we] eqn:Eqw.
			* simpl. unfold compose. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
			* simpl. unfold compose. rewrite -> op_assoc. reflexivity.
	Qed.

	Theorem homomorphism : forall (E A B : Type) (op:E->E->E) (S:Semigroup E op)
		(f: A -> B) (x: A),
		ap (pure f) (pure x) = pure (f x).
	Proof.
		intros E A B op [op_assoc] f x.
		simpl. unfold pure. reflexivity.
	Qed.

	Theorem interchange : forall (E A B : Type) (op:E->E->E) (S:Semigroup E op)
		(u: Rec E (A -> B)) (y: A),
		ap u (pure y) = ap (pure (fun f => apply f y)) u.
	Proof.
	intros E A B op [op_assoc] u y.
	destruct u as [v | e v | e ] eqn:Eq.
	- simpl. unfold apply. reflexivity.
	- simpl. unfold apply. reflexivity.
	- simpl. unfold apply. reflexivity.
	Qed.

End Recover.
