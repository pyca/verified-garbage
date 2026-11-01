module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.PublicKey
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.PublicKey
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.P256
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# P-256's public keys on RISC-V: `Verified`

`pk_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a2`, public).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.P256

theorem pk_ct : ConstantTime isa pkRV.pre pkRV.pub publicKeyP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def pkSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩]
  wr := [⟨0x1000, 65⟩, ⟨0x8000, 8192⟩]

theorem pk_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target publicKeyP256 (Spec.EcKey.P256.inst.publicKeyContract RISCV64.abi) :=
  Verified.of_correct (pk_rv hL) pk_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
        have h' : match pk s.mem (s.gpr .a1) with
            | some (.affine x y) => s'.gpr .a0 = 1 ∧
                Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 65 = Spec.EcKey.encodePoint (.affine x y)
            | _ => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 65 = List.replicate 65 0 := h
        generalize hq : Spec.EcKey.publicKey _ _ = q
        have hq' : pk s.mem (s.gpr .a1) = q := hq
        rw [hq'] at h'
        rcases q with _ | _ | ⟨x, y⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
        · exact ⟨by rw [h'.1]; rfl, h'.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P256.inst, Spec.EcKey.Instance.publicKeyContract,
          Spec.EcKey.Instance.publicKeySig, Spec.P256.curve, Spec.EcKey.scratchWords, pkRV, pk, RISCV64.abi,
          RISCV64.argRegs] [pkSat] using pkSat }

end VG.Proof.Ecdh.RISCV64.P256
