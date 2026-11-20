module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.P224
public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Ecdh.P224
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.Exchange
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.P224
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P224.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
meta import VerifiedGarbage.Impl.Ecdh.P224.RISCV64
meta import VerifiedGarbage.Spec.Ecdh.P224

/-!
# ECDH over P-224 on RISC-V: `Verified`

`ecdh_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, public: every address is a pointer plus a constant,
and the only branches are the callees' loops, on their counters).
-/

@[expose] public section

namespace VG.Proof.Ecdh.RISCV64.P224

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.P224

theorem ecdh_ct : ConstantTime isa ecdhRV.pre ecdhRV.pub ecdhP224 :=
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
  rd := [⟨0x2000, 28⟩, ⟨0x3000, 57⟩]
  wr := [⟨0x1000, 28⟩, ⟨0x8000, 8192⟩]

theorem ecdh_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target ecdhP224 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst RISCV64.abi) :=
  Verified.of_correct (ecdh_rv hL) ecdh_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
        show match ex s.mem (s.gpr .a1) (s.gpr .a2) with
          | some z => BitVec.setWidth 32 (s'.gpr .a0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 28 = z
          | none => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 28 = List.replicate 28 0
        have h' : match ex s.mem (s.gpr .a1) (s.gpr .a2) with
            | some z => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 28 = z
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 28 = List.replicate 28 0 := h
        revert h'
        generalize ex s.mem (s.gpr .a1) (s.gpr .a2) = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P224.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P224.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs] [ecdhSat] using ecdhSat }

/-- `vg_ecdh_p224` as emitted, cleanup included (`Impl.Ecdh.RISCV64.Fn.exchangeP224`),
meets its contract in constant time and returns without secret residue. -/
theorem exchange_scrubbed (hL : VG.Proof.Weierstrass.Law W) :
    VerifiedScrubbed RISCV64.target Impl.Ecdh.RISCV64.Fn.exchangeP224
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst RISCV64.abi) 32 :=
  RISCV64.Scrub.verifiedScrubbed (api := Spec.Ecdh.P224.exchangeApi) (W := 0)
    { code := ecdhP224, verified := ecdh_verified hL }
    (EcKey.RISCV64.Scrub.exchangeOut _ _ []) (by dsimp only; lit_decide)

end VG.Proof.Ecdh.RISCV64.P224
