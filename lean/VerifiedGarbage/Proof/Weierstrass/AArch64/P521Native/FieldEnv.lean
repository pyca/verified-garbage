module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.OrdinaryEnv
public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Native.NormalizeCallSetup
import VerifiedGarbage.Proof.Framework.Omega

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
