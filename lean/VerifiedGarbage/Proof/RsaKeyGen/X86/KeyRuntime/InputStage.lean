module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInput
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyStageFrame
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.InverseKeeps

/-! # A stage that calls `vg_rsa_keygen_inverse` keeps the key's inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.RsaKeyGen.X86.Key (Environment Input)

/-- `Input.afterStage`, through a stage that calls `vg_rsa_keygen_inverse`. -/
theorem input_afterStage {E : Environment} {s t : State} {regs : List Reg} {js : List Nat}
    (h : Input E s) (Hs : Ws s E.base E.size E.n 32) (ws : VG.Proof.Rsa.X86.Keys.Ws t E.base E.size E.n 32)
    (K : Keeps regs s t)
    (O : OutsS E.base (s.gpr .esp) (VG.Proof.RsaKeyGen.X86.Key.stageRanges E.n js) s.mem t.mem) : Input E t := by
  apply h.keep ws K
  intro d hd
  apply BitVec.eq_of_toNat_eq
  have H := Hs.read_val32 (d := d) (k := 1) (by unfold VG.Impl.Rsa.X86.Keys.hdr; omega) O
    (VG.Proof.RsaKeyGen.X86.Key.stage_preserves_header (n := E.n) (d := d) (count := 1)
      (by change d + 4 ≤ VG.Impl.RsaKeyGen.X86.Key.kOk; unfold VG.Impl.RsaKeyGen.X86.Key.kOk; omega))
  simpa only [val32, Nat.mul_zero, Nat.add_zero] using H

end VG.Proof.RsaKeyGen.X86.KeyRuntime
