module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Exchange
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.P256
public import VerifiedGarbage.Spec.Ecdh.Generic
import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.Exchange
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.P256
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P256.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDH over P-256 on RISC-V: `Verified`

`ecdh_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, public: every address is a pointer plus a constant,
and the only branches are the callees' loops, on their counters).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P256

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.P256

theorem ecdh_ct : ConstantTime isa ecdhRV.pre ecdhRV.pub ecdhP256 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, h3⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def ecdhSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 65⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x8000, 8192⟩]

theorem ecdh_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target ecdhP256 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst RISCV64.abi) :=
  Verified.of_correct (ecdh_rv hL) ecdh_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
        show match ex s.mem (s.gpr .a1) (s.gpr .a2) with
          | some z => BitVec.setWidth 32 (s'.gpr .a0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 32 = z
          | none => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 32 = List.replicate 32 0
        have h' : match ex s.mem (s.gpr .a1) (s.gpr .a2) with
            | some z => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 32 = z
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 32 = List.replicate 32 0 := h
        revert h'
        generalize ex s.mem (s.gpr .a1) (s.gpr .a2) = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P256.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P256.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs] [ecdhSat] using ecdhSat }

end VG.Proof.Ecdh.RISCV64.P256
