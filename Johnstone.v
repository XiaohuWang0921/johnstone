Require Import PropExtensionality.

Definition monic {A B} (f : A -> B) :=
  forall x y, f x = f y -> x = y.

Section Johnstone.

Variables
  (p : Prop)
  (f : Prop -> Prop)
  (m : monic f).

Definition UT := {q | f q}.
Definition VT := {q | f q /\ q}.
Definition UP := exists q, f q.
Definition VP := exists q, f q /\ q.

Definition H0 (w : f True) : VP :=
  ex_intro _ True (conj w I).

Definition H1 (w : VP) : f True :=
  match w with
  | ex_intro _ q (conj w0 w1) =>
    eq_ind _ _ w0 _
      (propositional_extensionality
        _ _
        (conj
          (fun _ => I)
          (fun _ => w1)))
  end.

Definition H2 : f True = VP :=
  propositional_extensionality
    _ _ (conj H0 H1).

Definition H3 (t : UT) :
  proj1_sig t -> VP :=
  match t with
  | exist _ q w0 =>
    fun (w1 : q) =>
      ex_intro _ q (conj w0 w1)
  end.

Definition H4 (t : UT) (w : VP) :
  proj1_sig t :=
  match t, w with
  | exist _ q0 w0, ex_intro _ q1 (conj w1 w2) =>
    eq_ind _ _ w2 _
      (m q1 q0
        (propositional_extensionality
          _ _
          (conj
            (fun _ => w0)
            (fun _ => w1))))
  end.

Definition H5 (t : UT) :
  proj1_sig t = VP :=
  propositional_extensionality _ _
    (conj (H3 t) (H4 t)).

Definition H6 (w : f VP) : UP :=
  ex_intro _ VP w.

Definition H7 (w : UP) : f VP :=
  match w with
  | ex_intro _ q w0 =>
    eq_ind _ _ w0 _ (H5 (exist _ q w0))
  end.

Definition H8 : f VP = UP :=
  propositional_extensionality _ _
    (conj H6 H7).

Definition H9 (t : UT) (v : proj1_sig t) :
  proj1_sig t = UP :=
  match t with
  | exist _ q w0 =>
    propositional_extensionality _ _
      (conj
        (fun _ => ex_intro _ q w0)
        (fun _ => v))
  end.

Definition H10 (w : f True) : f UP :=
  eq_ind _ _ w _
    (H9 (exist _ True w) I).

Definition H11 (w : f UP) : f True :=
  H1
    (ex_intro _ UP 
      (conj w (ex_intro _ UP w))).

Definition H12 : f UP = f True :=
  propositional_extensionality _ _
    (conj H11 H10).

Definition H13 : UP = True :=
  m UP True H12.

Definition H14 : f (f True) = True :=
  eq_trans
    (f_equal f H2)
    (eq_trans H8 H13).

Definition H15 (w : f (f p)) : p :=
  eq_ind _ _ I _
    (m True p
      (m (f True) (f p)
        (eq_trans H14
          (propositional_extensionality
            _ _
            (conj
              (fun _ => w)
              (fun _ => I)))))).

Definition H16 (w : p) : f (f p) :=
  eq_ind _ id I _
    (eq_trans (eq_sym H14)
      (f_equal f
        (f_equal f
          (propositional_extensionality
            _ _
            (conj
              (fun _ => w)
              (fun _ => I)))))).

Definition Johnstone : f (f p) = p :=
  propositional_extensionality
    _ _
    (conj H15 H16).

End Johnstone.