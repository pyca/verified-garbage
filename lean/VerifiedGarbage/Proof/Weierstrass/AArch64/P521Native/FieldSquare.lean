module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.RepresentationFin
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryEnv
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeCallSetup

/-! ### `Weierstrass.AArch64.P521Native.FieldEnv`, which this module and modules that import it used -/

section

/-! Ordinary field environments across calls that also use temporary workspace. -/

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass

/-- A field operation may write its output and the reserved arithmetic scratch. -/
def FieldFrame (base : Addr) (o : Nat) (m m' : Mem) : Prop :=
  ∀x,(ofs base x<o ∨ o+72≤ofs base x) →
    (ofs base x<3952 ∨ 4024≤ofs base x) → m' x=m x

theorem update_ordinary_kept {base : Addr} {p : Nat} [NeZero p] {loc : Nat → Nat}
    {V : List Nat} {E : Nat → Fin p} {caps : Nat → Nat} {s t : State}
    (h : OrdinaryInv base p loc V E caps s) {o cap : Nat} {v : Fin p}
    (kept : ∀x∈V,x≠o → wordsVal t.mem base (loc x) 9=wordsVal s.mem base (loc x) 9)
    (bound : wordsVal t.mem base (loc o) 9<cap*p)
    (value : Fin.ofNat p (wordsVal t.mem base (loc o) 9)=v) :
    OrdinaryInv base p loc (o::V) (Function.update E o v) (Function.update caps o cap) t := by
  constructor
  · intro x hx
    by_cases he : x=o
    · subst x; simpa only [Function.update_self] using bound
    · have hv := List.mem_of_ne_of_mem he hx
      rw [Function.update_of_ne he,kept x hv he]
      exact h.bound x hv
  · intro x hx
    by_cases he : x=o
    · subst x; simpa only [Function.update_self] using value
    · have hv := List.mem_of_ne_of_mem he hx
      rw [Function.update_of_ne he,kept x hv he]
      exact h.value x hv

theorem wordsVal_frame_two {base : Addr} {o len scratch temp : Nat} {m m' : Mem}
    (frame : ∀x,(ofs base x<o ∨ o+len≤ofs base x) →
      (ofs base x<scratch ∨ scratch+temp≤ofs base x) → m' x=m x)
    {d k : Nat} (sepO : d+8*k≤o ∨ o+len≤d) (sepT : d+8*k≤scratch ∨ scratch+temp≤d)
    (fits : d+8*k≤2^64) : wordsVal m' base d k=wordsVal m base d k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [wordsVal]
    have hw : word m' base d=word m base d := Mem.readW_congr fun i hi => by
      apply frame
      · rw [ofs_off base (by omega_arith)]; omega_arith
      · rw [ofs_off base (by omega_arith)]; omega_arith
    rw [hw,ih (by omega_arith) (by omega_arith) (by omega_arith)]

end VG.Proof.Weierstrass.AArch64.P521Native

end

end

/-! ### `Weierstrass.AArch64.P521Native.FieldMul`, which the modules that import this one used -/

section

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

end

end

@[expose] public section
namespace VG.Proof.Weierstrass.AArch64.P521Native
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Mont.AArch64.P521Field
open VG.Proof.Mont.AArch64.P521Square (fieldPrime)
open VG.Proof.Weierstrass

theorem field_square_ok {base : Addr} {W : Nat} {s : State} {loc : Nat → Nat} {V : List Nat}
    {E : Nat → Fin fieldPrime} {caps : Nat → Nat} {o a : Nat}
    (hs : Scr s base W) (hW : 4024≤W) (hMax : W≤8192)
    (inv : OrdinaryInv base fieldPrime loc V E caps s)
    (readA : a∈V) (capA : caps a=1)
    (outFits : loc o+72≤3520) (aFits : loc a+72≤3520) (inputFits : ∀x∈V,loc x+72≤W)
    (scratch : ∀x∈V,loc x+72≤VG.Impl.Weierstrass.AArch64.Mont.moAt 9 ∨ VG.Impl.Weierstrass.AArch64.Mont.moAt 9+72≤loc x)
    (apart : ∀x∈V,x≠o → loc x+72≤loc o ∨ loc o+72≤loc x) :
    WP isa (normalizeSquareStep (loc o) (loc a)) s fun t =>
      OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a*E a)) (Function.update caps o 1) t ∧
      Scr t base W ∧ (∀r∈preserved,t.gpr r=s.gpr r) ∧ t.sp=s.sp ∧ t.v .v31=s.v .v31 ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ FieldFrame base (loc o) s.mem t.mem := by
  have ba := inv.bound a readA
  rw [capA,Nat.one_mul] at ba
  refine WP.mono (normalize_square_step_ok hs hW hMax outFits aFits ba) fun t ⟨bound,value,frame,zero,rd,wr,sp,gp,v31⟩ => ?_
  have ni : OrdinaryInv base fieldPrime loc (o::V) (Function.update E o (E a*E a)) (Function.update caps o 1) t := by
    apply update_ordinary_kept inv
    · intro x hx hne
      apply wordsVal_frame_two (o:=loc o) (len:=72) (scratch:=VG.Impl.Weierstrass.AArch64.Mont.moAt 9) (temp:=72) frame
      · simpa only [Nat.reduceMul] using apart x hx hne
      · simpa only [Nat.reduceMul] using scratch x hx
      · have h:=inputFits x hx; have e:=hs.enc; omega_arith
    · simpa only [Nat.one_mul] using bound
    · rw [value,ordinary_mul,inv.value a readA]
  refine ⟨ni,⟨zero,wr ▸ hs.wr,hs.nowrap,hs.enc⟩,gp,sp,v31,rd,wr,?_⟩
  intro x ho ht
  apply frame x ho
  exact ht

end VG.Proof.Weierstrass.AArch64.P521Native
