module

public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The arrays recovery's Montgomery products write -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

/-- The result and the callee's range. -/
abbrev montWrites (o : Nat) : List Nat := [o, mAcc, mAcc + 1, mAcc + 2, mAcc + 3]

theorem MR.of_eq {g : Geo} {m : Nat} {s t : State} (h : MR g m s)
    (hm : num t.mem g.B g.w mBase = num s.mem g.B g.w mBase) (hi : w32 t.mem g.B sInv = w32 s.mem g.B sInv) :
    MR g m t :=
  ⟨h.positive, hm.trans h.modulus, h.bound, by rw [hi]; exact h.inverse⟩

theorem MR.keep {g : Geo} {m : Nat} {s t : State} (h : MR g m s) (ws : Ws s g.B g.Z g.w nArr)
    {js : List Nat} (k : Keep g.B g.w js [] s.mem t.mem) (hj : ∀ j ∈ js, j ≠ mBase) : MR g m t :=
  h.of_eq (k.num hj (by simp) (ws.fit64 (by decide))) (k.slot (e := sInv) (by decide) (by simp))

end VG.Proof.Rsa.X86.Recover
