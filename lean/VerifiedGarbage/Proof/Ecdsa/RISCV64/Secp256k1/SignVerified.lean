module

public import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Sign
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Spec.Ecdsa.Secp256k1
import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignLit
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Ecdsa.Contract
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.Sign
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Spec.Ecdsa.Secp256k1
meta import VerifiedGarbage.Proof.Ecdsa.RISCV64.Secp256k1.SignLit
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ECDSA signatures over secp256k1 on RISC-V: `Verified`

`sign_rv` with the function's constant time, by taint tracking (only the
pointers, in `a0`–`a4`, public: every address is a pointer plus a constant,
and the only branches are the callees' loops, on their counters).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1

open VG VG.RISCV64 VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdsa.RISCV64.Sign

theorem sign_ct : ConstantTime isa signRV.pre signRV.pub signSecp256k1 :=
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
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

theorem signRV_implies : signRV.Implies (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.Secp256k1.inst RISCV64.abi) :=
    { pre := by
        sig_implies_pre [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
        show match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
          | some rs => BitVec.setWidth 32 (s'.gpr .a0) = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 =
              Spec.Ecdsa.encode W rs
          | none => BitVec.setWidth 32 (s'.gpr .a0) = 0 ∧
            Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 = List.replicate 64 0
        have h' : match sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) with
            | some rs => s'.gpr .a0 = 1 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 = Spec.Ecdsa.encode W rs
            | none => s'.gpr .a0 = 0 ∧ Spec.Ecdsa.bytesAt s'.mem (s.gpr .a0) 64 = List.replicate 64 0 := h
        revert h'
        generalize sg s.mem (s.gpr .a1) (s.gpr .a2) (s.gpr .a3) = q
        rcases q with _ | rs <;> exact fun h => ⟨by rw [h.1]; rfl, h.2⟩
      pub := by
        sig_implies_pub [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs]
      sat := by
        sig_implies_sat [Spec.Ecdsa.Secp256k1.inst, Proof.Ecdsa.Instance.signContract,
          Proof.Ecdsa.Instance.signSig, Spec.Secp256k1.curve, Spec.Ecdsa.scratchWords, signRV, sg, RISCV64.abi,
          RISCV64.argRegs] [signSat] using signSat }

theorem sign_verified (hL : VG.Proof.Weierstrass.Law W) :
    Verified RISCV64.target signSecp256k1 (Proof.Ecdsa.Instance.signContract Spec.Ecdsa.Secp256k1.inst RISCV64.abi) :=
  Verified.of_correct (sign_rv hL) sign_ct signRV_implies

end VG.Proof.Ecdsa.RISCV64.Secp256k1
