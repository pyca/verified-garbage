module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Ecdsa.P384
import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Ecdsa.P384
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.P384.SignLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over P-384 on RISC-V: `Verified`

`sign_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a4`, public: every address is a pointer plus a constant,
and the only branches are the callees' loops, on their counters).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.P384

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign

theorem sign_ct : ConstantTime isa signRV.pre signRV.pub signP384 :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4])
    (fun _ _ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3
      · exact h4⟩) (by taint_decide)

/-- A state satisfying the precondition. -/
def signSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x4000 | .a4 => 0x8000 | _ => 0
  sp := 0x20000
  mem _ := 0
  rd := [⟨0x2000, 48⟩, ⟨0x3000, 48⟩, ⟨0x4000, 48⟩]
  wr := [⟨0x1000, 96⟩, ⟨0x8000, 8192⟩]

theorem signRV_implies : signRV.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P384.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P384.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
        show match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
          | some rs => BitVec.setWidth 32 (s'.gpr .a0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 96 =
              Spec.Ecdsa.encode W rs
          | none => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 96 = List.replicate 96 0
        have h' : match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
            | some rs => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 96 = Spec.Ecdsa.encode W rs
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 96 = List.replicate 96 0 := h
        revert h'
        generalize sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P384.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.P384.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.P384.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs] [signSat] using signSat }

theorem sign_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target signP384 (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.P384.inst RISCV64.abi) :=
  Verified.of_correct (sign_rv hL) sign_ct signRV_implies

end VG.Proof.Ecdsa.RISCV64.P384
