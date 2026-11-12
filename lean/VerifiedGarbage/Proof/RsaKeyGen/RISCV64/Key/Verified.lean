module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Key
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.RISCV64.InvLaw
public import VerifiedGarbage.Spec.RsaKeyGen.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Correct
import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.KeyCT

/-! # `vg_rsa_keygen_key` on RISC-V: verified against the shared contract

Correct (`key_verified_of`, `Correct.lean`) and constant time (`key_ct`, `KeyCT.lean`). -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64

/-- The cuts of the constant-time proof after the inverses, by correctness. -/
private theorem front1_ok [VG.Proof.Rsa.RISCV64.InvLaw] : ∀ d s, S2 d s → WP isa front1 s (S5 d) := by
  rintro d s ⟨s0, c0, c, a7⟩
  obtain ⟨tr, t, e, V, F, k⟩ := dFront_ok (preC_of c0.1) c a7
  exact ⟨tr, t, exec_front1 e, s0, c0, V, F, k⟩

private theorem front'_ok [VG.Proof.Rsa.RISCV64.InvLaw] : ∀ d s, S2 d s → WP isa front' s (S5 d) := by
  rintro d s ⟨s0, c0, c, a7⟩
  obtain ⟨tr, t, e, V, F, k⟩ := crtFront_ok (preC_of c0.1) c a7
  exact ⟨tr, t, exec_front e, s0, c0, V, F, k⟩

/-- Constant time, with the cuts proven. -/
theorem key_ct_full [VG.Proof.Rsa.RISCV64.InvLaw] : ConstantTime isa (Proof.RsaKeyGen.keyContract RISCV64.abi).pre
    (Proof.RsaKeyGen.keyContract RISCV64.abi).pub VG.Impl.RsaKeyGen.RISCV64.Key.code :=
  key_ct front1_ok front'_ok

/-- `vg_rsa_keygen_key`. -/
theorem key_verified [VG.Proof.Rsa.RISCV64.InvLaw] :
    Verified RISCV64.target VG.Impl.RsaKeyGen.RISCV64.Key.code (Proof.RsaKeyGen.keyContract RISCV64.abi) :=
  key_verified_of key_ct_full

end VG.Proof.RsaKeyGen.RISCV64.Key
