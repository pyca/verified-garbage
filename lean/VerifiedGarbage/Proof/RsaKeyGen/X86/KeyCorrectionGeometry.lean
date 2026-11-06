module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyWorkspace
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
import VerifiedGarbage.Proof.Rsa.WordRanges

/-! # The fixed 128-bit correction bank fits every native RSA workspace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem correction_workspace {s : State} {B : Addr} {Z n : Nat} (h : Ws s B Z n 32) : Ws s B Z 4 4 := by
  refine ⟨h.workspace, ?_, by decide, by decide⟩
  change 256 ≤ Z
  have lower : 256 ≤ 160 + 32 * (4 * (n + 2)) :=
    Nat.le_trans (by decide : 256 ≤ 160 + 32 * (4 * 2))
      (Nat.add_le_add_left (Nat.mul_le_mul_left 32
        (Nat.mul_le_mul_left 4 (Nat.le_add_left 2 n))) 160)
  exact Nat.le_trans lower h.fits

end VG.Proof.RsaKeyGen.X86.Key
