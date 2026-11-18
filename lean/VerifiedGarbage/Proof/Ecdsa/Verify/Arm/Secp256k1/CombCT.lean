module

public import VerifiedGarbage.Spec.Ecdsa.Generic
public import VerifiedGarbage.Spec.Ecdsa.Verify
public import VerifiedGarbage.Spec.Secp256k1
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.CT
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.CT
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.Verified
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
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdsa.Arm.Secp256k1 VG.Proof.Weierstrass

/-- What timing may depend on: the pointers and the table's address, and
the key and the signature (`VPub`), which the contract lets it depend on. -/
def combVerifyPub (um : Bool) (s t : State) : Prop :=
  (verifyArm.pub s t ∧ s.syms secp256k1Comb.tsym = t.syms secp256k1Comb.tsym) ∧ VPub (secp256k1With um) s t

/-- `vg_secp256k1_mul_public`'s pieces and the two parts of verification around
its call, in sequence: what the taint analysis checks. -/
def ctPiecesWith (um : Bool) : Prog isa :=
  pieces (pubPieces (secp256k1With um) ++
    [verifyHead (secp256k1With um) (verifyGeneratorSecp256k1With um), verifyTail (secp256k1With um)])

def ctPieces : Prog isa := ctPiecesWith false

def ctPiecesU : Prog isa := ctPiecesWith true

materialize_code ctPieces
materialize_code ctPiecesU

theorem pubLeaves : PubLeaves (secp256k1With false) := by
  apply PubLeaves.of_checks (A := VG.Arm.taint) (τ := VG.Arm.Taint.ofRegs)
    (fun _ _ _ h => VG.Arm.Taint.agree_ofRegs h) (L := ctPieces) (extra := [_, _]) rfl <;>
    native_taint_decide

theorem pubLeavesU : PubLeaves (secp256k1With true) := by
  apply PubLeaves.of_checks (A := VG.Arm.taintU) (τ := VG.Arm.Taint.ofRegs)
    (fun _ _ _ h => VG.Arm.Taint.agree_ofRegs h) (L := ctPiecesU) (extra := [_, _]) rfl <;>
    taint_decide

/-- Verification is constant time but in the key and the signature, given the
taint analysis's checks of its parts. -/
theorem combVerifyWith_ct (hC : Law Spec.Secp256k1.curve) (um : Bool) (L : PubLeaves (secp256k1With um))
    (hhead : RelCT isa (fun x y => combVerifyPre um x ∧ combVerifyPre um y ∧ combVerifyPub um x y)
      (verifyHead (secp256k1With um) (verifyGeneratorSecp256k1With um)) fun _ _ => True)
    (htail : LeafCT [.r12] (verifyTail (secp256k1With um))) :
    ConstantTime isa (combVerifyPre um) (combVerifyPub um) (verifySecp256k1CombWith um) :=
  verifyWith_ct (secp256k1With_ok um) hC rfl (fun _ _ _ _ h => h.2)
    (fun _ hp => verifyHead_ok (secp256k1With_ok um) hC hp.1 (a0₁ := false) nofun (comb_generatorWP hC hp))
    hhead htail L

theorem combVerify_ct (hC : Law Spec.Secp256k1.curve) :
    ConstantTime isa (combVerifyPre false) (combVerifyPub false) verifySecp256k1Comb :=
  combVerifyWith_ct hC false pubLeaves
    (RelCT.taint (A := taintSym [secp256k1Comb.tsym]) (c := piece ctPieces 26) (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun _ _ h => ⟨Taint.agree_ofRegs (by
        obtain ⟨⟨⟨_, h0, h1, h2, h3⟩, _⟩, _⟩ := h.2.2
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [h0, h1, h2, h3]), fun n hn => by
        obtain rfl := List.mem_singleton.mp hn
        exact h.2.2.1.2⟩) (by native_taint_decide))
    (LeafCT.check (p := piece ctPieces 27) (by native_taint_decide))

theorem combVerifyU_ct (hC : Law Spec.Secp256k1.curve) :
    ConstantTime isa (combVerifyPre true) (combVerifyPub true) verifySecp256k1CombU :=
  combVerifyWith_ct hC true pubLeavesU
    (RelCT.taint (A := taintSymU [secp256k1Comb.tsym]) (c := piece ctPiecesU 26) (Taint.ofRegs [.r0, .r1, .r2, .r3])
      (fun _ _ h => ⟨Taint.agree_ofRegs (by
        obtain ⟨⟨⟨_, h0, h1, h2, h3⟩, _⟩, _⟩ := h.2.2
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [h0, h1, h2, h3]), fun n hn => by
        obtain rfl := List.mem_singleton.mp hn
        exact h.2.2.1.2⟩) (by taint_decide))
    (LeafCT.checkU (p := piece ctPiecesU 27) (by taint_decide))

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1
