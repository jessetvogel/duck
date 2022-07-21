import Aesop

axiom Scheme : Type
axiom P : Scheme → Prop
axiom Q : Scheme → Prop
axiom R : Scheme → Prop
axiom S : Scheme → Prop

@[aesop 99%] axiom Q_of_P (X : Scheme) (h : P X) : Q X
@[aesop 99%] axiom R_of_Q (X : Scheme) (h : Q X) : R X

@[aesop 99%] axiom S_of__R_of_P (X : Scheme) (h : P X → R X) : S X

theorem thm : S X := by {
  aesop;
}

#print thm
