module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombMain
import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Framework.Arm.TaintSym
import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.TaintSym
meta import VerifiedGarbage.Proof.Framework.Arm.TaintUmaal
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-! ### `Ecdsa.Verify.Arm.Secp256k1.Contract`, which only this module used -/

section

/-!
# ECDSA verification over secp256k1 on 32-bit ARM: the contract the proof is written against

The facts of `Proof.Ecdsa.verifyContract Spec.Ecdsa.Secp256k1.inst` for 32-bit ARM, by name:
`vg_ecdsa_secp256k1_verify(public, digest, sig, scratch)`, with the arguments in
`r0`–`r3` (AAPCS), the result in `r0` (the low word of `r1:r0`). Only the
pointers are public here: the proof shows that nothing else affects timing,
although the contract would let the contents of the three buffers.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm.Secp256k1

open VG VG.Arm Spec.Weierstrass Spec.Ecdsa

/-- Whether the signature at `sig` of the hash at `digest` is valid for the
public key at `pk`, as the specification says. -/
abbrev vf (m : Mem) (pk digest sig : Addr) : Bool :=
  verify Spec.Secp256k1.curve (bytesAt m pk 65) (hashToInt Spec.Secp256k1.curve (bytesAt m digest 32)) (bytesAt m sig 64)

def verifyArm : Contract Arm.isa where
  pre s :=
    let pk : Region := ⟨State.addr (s.gpr .r0), 65⟩
    let digest : Region := ⟨State.addr (s.gpr .r1), 32⟩
    let sig : Region := ⟨State.addr (s.gpr .r2), 64⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 8192⟩
    s.rd = [pk, digest, sig] ∧ s.wr = [scratch] ∧ pk.Disjoint scratch ∧ digest.Disjoint scratch ∧
      sig.Disjoint scratch ∧ (s.gpr .r0).toNat + 65 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32
  post s s' := BitVec.setWidth 32 (s'.gpr .r1 ++ s'.gpr .r0) =
    if vf s.mem (State.addr (s.gpr .r0)) (State.addr (s.gpr .r1)) (State.addr (s.gpr .r2)) then 1 else 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1

end

end


/-! Verification's generator comb is constant time for secret input contents too. -/

@[expose] public section
namespace VG
materialize_code Impl.Ecdsa.Arm.verifySecp256k1Comb
materialize_code Impl.Ecdsa.Arm.verifySecp256k1CombU
end VG

namespace VG.Proof.Ecdsa.Verify.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm

def combVerifyPub (s t : State) : Prop := verifyArm.pub s t ∧ s.syms secp256k1Comb.tsym=t.syms secp256k1Comb.tsym

theorem combVerify_ct : ConstantTime isa (combVerifyPre false) combVerifyPub verifySecp256k1Comb := by
  refine VG.Taint.constantTime (A := taintSym [secp256k1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2,.r3]) ?_
    (by native_taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2,h3⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    exacts [h0,h1,h2,h3]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

theorem combVerifyU_ct : ConstantTime isa (combVerifyPre true) combVerifyPub verifySecp256k1CombU := by
  refine VG.Taint.constantTime (A := taintSymU [secp256k1Comb.tsym]) (Taint.ofRegs [.r0,.r1,.r2,.r3]) ?_
    (by taint_decide)
  intro s t _ _ ⟨⟨_,h0,h1,h2,h3⟩,sy⟩
  refine ⟨Taint.agree_ofRegs (fun r hr => ?_),fun n hn => ?_⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl
    exacts [h0,h1,h2,h3]
  · obtain rfl := List.mem_singleton.mp hn
    exact sy

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1
