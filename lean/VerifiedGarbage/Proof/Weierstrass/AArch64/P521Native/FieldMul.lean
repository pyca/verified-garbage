module

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.FieldEnv
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationFin

import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass

theorem field_mul_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a b : Nat}
    (hs : Scr s base W) (hW : 4016≤W)
    (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (readB : b∈V) (capA : caps a=1) (capB : caps b=1)
    (outFits : loc o+72≤W) (inputFits : ∀x∈V,loc x+72≤W)
    (scratch : ∀x∈V,loc x+72≤3952 ∨ 4016≤loc x)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (normalizeMulStep (loc o) (loc a) (loc b)) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a*E b)) (Function.update caps o 1) t ∧
      Scr t base W ∧ (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.sp=s.sp ∧ t.v .v31=s.v .v31 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ FieldFrame base (loc o) s.mem t.mem := by
  have ba := inv.bound a readA
  have bb := inv.bound b readB
  rw [capA,Nat.one_mul] at ba
  rw [capB,Nat.one_mul] at bb
  refine WP.mono (normalize_mul_step_ok hs hW outFits (inputFits a readA) (inputFits b readB)
    (scratch a readA) ba bb) fun t ⟨bound,value,frame,zero,rd,wr,sp,gp,v31⟩ => ?_
  have ni : OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a*E b)) (Function.update caps o 1) t := by
    apply update_ordinary_kept inv
    · intro x hx hne
      apply wordsVal_frame_two (o:=loc o) (len:=72) (scratch:=3952) (temp:=64) frame
      · simpa only [Nat.reduceMul] using apart x hx hne
      · simpa only [Nat.reduceMul,Nat.reduceAdd] using scratch x hx
      · have h:=inputFits x hx; have e:=hs.enc; omega_arith
    · simpa only [Nat.one_mul] using bound
    · rw [value,ordinary_mul,inv.value a readA,inv.value b readB]
  refine ⟨ni,⟨zero,wr ▸ hs.wr,hs.nowrap,hs.enc⟩,gp,sp,v31,rd,wr,?_⟩
  intro x ho ht
  apply frame x ho
  omega_arith

end VG.Proof.Weierstrass.AArch64.P521Native
