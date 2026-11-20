module

public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Exchange
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.EcKey.P384
public import VerifiedGarbage.Spec.Ecdh.Generic
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
public import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64Window
import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Exchange
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.EcKey.P384
meta import VerifiedGarbage.Spec.Ecdh.Generic
meta import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.EcdhLit
meta import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
meta import VerifiedGarbage.Proof.Framework.RISCV64.TaintMono
import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Verified
import VerifiedGarbage.Spec.Ecdh.P384
meta import VerifiedGarbage.Proof.Weierstrass.RISCV64.P384Field.Verified
meta import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
meta import VerifiedGarbage.Proof.EcKey.RISCV64.Scrub
meta import VerifiedGarbage.Impl.Ecdsa.P384.RISCV64Window
meta import VerifiedGarbage.Spec.Ecdh.P384

/-!
# ECDH over P-384 on RISC-V: `Verified`

`ecdh_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a3`, public: every address is a pointer plus a constant,
and the only branches are the callees' loops, on their counters).
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.Ecdh.RISCV64.P384

open VG VG.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Proof.Ecdsa.RISCV64.P384

theorem ecdh_ct : ConstantTime isa ecdhRV.pre ecdhRV.pub ecdhP384 :=
  VG.Taint.constantTime_of_exists (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, h3⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩)
    (by taint_decide_sum [VG.Proof.Weierstrass.RISCV64.P384Field.mulASum,
      VG.Proof.Weierstrass.RISCV64.P384Field.addASum, VG.Proof.Weierstrass.RISCV64.P384Field.subASum])

/-- A state satisfying the precondition. -/
def ecdhSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 97⟩]
  wr := [⟨0x1000, 48⟩, ⟨0x8000, 8192⟩]

theorem ecdh_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target ecdhP384 (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst RISCV64.abi) :=
  Verified.of_correct (ecdh_rv hL) ecdh_ct
    { pre := by
        sig_implies_pre [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
        show match ex s.mem (s.gpr .a1) (s.gpr .a2) with
          | some z => BitVec.setWidth 32 (s'.gpr .a0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 48 = z
          | none => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 48 = List.replicate 48 0
        have h' : match ex s.mem (s.gpr .a1) (s.gpr .a2) with
            | some z => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 48 = z
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 48 = List.replicate 48 0 := h
        revert h'
        generalize ex s.mem (s.gpr .a1) (s.gpr .a2) = q
        rcases q with _ | z <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.EcKey.P384.inst, Spec.Ecdh.Instance.exchangeContract,
          Spec.Ecdh.Instance.exchangeSig, Spec.P384.curve, Spec.EcKey.scratchWords, ecdhRV, ex, RISCV64.abi,
          RISCV64.argRegs] [ecdhSat] using ecdhSat }

/-- `vg_ecdh_p384` as emitted, cleanup included (`Impl.Ecdh.RISCV64.Fn.exchangeP384`),
meets its contract in constant time and returns without secret residue. -/
theorem exchange_scrubbed (hL : VG.Proof.Weierstrass.Law W) :
    VerifiedScrubbed RISCV64.target Impl.Ecdh.RISCV64.Fn.exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst RISCV64.abi) 32 :=
  RISCV64.Scrub.verifiedScrubbed (api := Spec.Ecdh.P384.exchangeApi) (W := 0)
    { code := ecdhP384, verified := ecdh_verified hL }
    (EcKey.RISCV64.Scrub.exchangeOut _ _ []) (by dsimp only; lit_decide)

end VG.Proof.Ecdh.RISCV64.P384
