module
public import VerifiedGarbage.Proof.Ed25519.AArch64.Ops
public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMemory
public import VerifiedGarbage.Proof.X25519.AArch64.Top
import VerifiedGarbage.Proof.Framework.Lit


/-! The contract the X25519 function is proven against, and the saved registers. -/

@[expose] public section

namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

/-- The shared signature also supplies the non-wrapping scratch range. -/
def localContract : Contract isa :=
  { Proof.X25519.x25519AArch64 with
    pre := fun s => Proof.X25519.x25519AArch64.pre s ∧ (s.gpr .x3).toNat + 4096 ≤ 2^64 }

theorem savedIndices : ∀ rd ∈ saved, ∃ i < 6,
    rd.1 = VG.Impl.X25519.AArch64.saved.getD i .x19 ∧ rd.2 = 8*i := by decide

theorem saved_of_words {base : Addr} {m : Mem} {g : Reg → BitVec 64}
    (h : ∀ i < 6, word m base (8*i) = g (VG.Impl.X25519.AArch64.saved.getD i .x19)) :
    Saved base g m := by
  intro rd hr
  obtain ⟨i,hi,h1,h2⟩ := savedIndices rd hr
  rw [h1,h2]; exact h i hi

theorem preservedCases : ∀ r ∈ preserved,
    (∃ rd ∈ saved, rd.1 = r) ∨ r ∉ clob ++ ([.x0,.x1,.x19] : List Reg) := by decide

end VG.Proof.X25519.AArch64.Word
