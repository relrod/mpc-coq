Require Import Ascii String FunctionalExtensionality.

Open Scope string.

Definition parser a := string -> option (a * string).

Definition fail {t} : parser t := fun _ => None.

Definition ret {t} (a : t) : parser t :=
  fun inp => Some (a, inp).

(* Parse one character from the string successfully, and return it. Leave the
   rest of the unparsed input to be later parsed. *)
Definition item : parser ascii :=
  fun inp => match inp with
             | EmptyString => None
             | String h t => Some (h, t)
             end.

Definition tail s :=
  match s with
  | EmptyString => ""
  | String _ t => t
  end.

Definition ascii_or_empty s :=
  match s with
  | Some s => s
  | None => "000"%char
  end.

(* If we attempt to parse an empty string using [item], we always get None
   back. *)
Lemma item_parses_one_char_nonempty : item "" = None.
Proof. reflexivity. Qed.

(* If we attempt to parse a nonempty string using [item], we get the first
character of the string as parsed and the rest of the string as unparsed. *)
Lemma item_parses_one_char :
  forall s a b,
    s = String a b ->
    item s = Some (ascii_or_empty (get 0 s), tail s).
Proof.
  intros.
  rewrite H.
  simpl.
  trivial.
Qed.

Example item_nonempty_str : item "foo" = Some ("f"%char, "oo").
Proof. reflexivity. Qed.

Definition flatmap {t u} (p : parser t) (f : t -> parser u) : parser u :=
  fun i => match p i with
           | None => None
           | Some(x, i') => f x i'
           end.

Notation "f >>= g" := (flatmap f g) (at level 60, right associativity).

Lemma monad_left_id :
  forall {t u} (p : parser t) (f : t -> parser u) (a : t),
    ret a >>= f = f a.
Proof. reflexivity. Qed.

Lemma monad_right_id :
  forall {t} (p : parser t),
    p >>= ret = p.
Proof.
  intros.
  unfold ret.
  unfold flatmap.
  extensionality x.
  destruct (p x).
  destruct p0.
  reflexivity.
  reflexivity.
Qed.

Lemma monad_assoc :
  forall {t u v} (p : parser t) (f : t -> parser u) (g : u -> parser v),
    (p >>= f) >>= g = p >>= (fun x => f x >>= g).
Proof.
  intros.
  unfold flatmap.
  extensionality x.
  destruct (p x).
  destruct p0.
  reflexivity.
  reflexivity.
Qed.

Definition sat (f : ascii -> bool) : parser ascii :=
  item >>= fun x => if f x then ret x else fail.

Definition eq_char c := sat (fun x => if ascii_dec c x then true else false).

Notation "a <= b" := (Compare_dec.leb (nat_of_ascii a) (nat_of_ascii b)).

Definition range_inclusive (a b : ascii) : parser ascii :=
  sat (fun c => andb (a <= c) (c <= b)).

Definition choice {t} (p q : parser t) : parser t :=
  fun i =>
    match p i with
      | None => q i
      | s => s
    end.

Notation "x <|> y" := (choice x y) (at level 60).

Lemma choice_left :
  forall s (p q : parser string) a b,
    p s = Some (a, b) ->
    choice p q s = Some (a, b).
Proof.
  intros.
  rewrite <- H.
  unfold choice.
  rewrite H.
  trivial.
Qed.

Lemma choice_right :
  forall s (p q : parser string) a b,
    p s = None ->
    q s = Some (a, b) ->
    choice p q s = Some (a, b).
Proof.
  intros.
  rewrite <- H0.
  unfold choice.
  rewrite H.
  trivial.
Qed.


Definition digit := range_inclusive "0" "9".
Definition lc_char := range_inclusive "a" "z".
Definition uc_char := range_inclusive "A" "Z".
Definition is_char := lc_char <|> uc_char.

(*
Require Import ExtrOcamlString.
Extraction Language Ocaml.
Extraction "parsercombinator.ml" parser fail ret item tail ascii_or_empty flatmap sat choice range_inclusive eq_char.*).