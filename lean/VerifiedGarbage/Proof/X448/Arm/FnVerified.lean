module

public import VerifiedGarbage.Proof.X448.Field16Contract
public import VerifiedGarbage.Proof.X448.Arm.FnContract
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.NativeTaintCore
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.X448.Arm.FnLit
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.X448.Arm.FnContract
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.NativeTaintCore
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.X448.Arm.FnLit
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Arm.NativeHintData

/-!
# X448 on ARMv7: the field functions, verified

Each function meets the contract of its `Api` (`Proof/X448/Field16Contract.lean`):
the proof against `mulArm`, `addArm`, `subArm` or `mulA24Arm`, which it
implies; constant time by taint tracking (only the pointer and the offsets,
in `r0`–`r3`, are public, and every address is `ws` plus a constant or an
offset, plus a constant or a counter); and a state satisfying it (`sat`).
-/

@[expose] public section

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem armPub_agree {s₁ s₂ : State} (h : armPub s₁ s₂) : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], s₁.gpr r = s₂.gpr r := by
  obtain ⟨_, h0, h1, h2, h3⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem armPub1_agree {s₁ s₂ : State} (h : armPub1 s₁ s₂) : ∀ r ∈ [Reg.r0, .r1, .r2], s₁.gpr r = s₂.gpr r := by
  obtain ⟨_, h0, h1, h2⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2

/-- A state satisfying the preconditions: `ws` at `0x1000`, the elements at
offset 0, all zero. -/
def satF : State where
  gpr r := match r with
    | .r0 => 0x1000 | _ => 0
  sp := 0x10000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem limbs_zero (ws : Addr) : Proof.X448.Field16.Limbs (fun _ => 0) ws 0 := by
  intro i _
  simp only [Proof.X448.Field16.limbAt, Mem.readW, Mem.read]
  decide

theorem fits_zero : Proof.X448.Field16.Fits 0 := by decide

theorem bin_sat (r : Nat → Nat → Nat → Prop) : (Proof.X448.Field16.binContract Arm.abi r).pre satF := by
  unfold Proof.X448.Field16.binContract
  exact Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Proof.X448.Field16.sig, Arm.abi, Arm.argRegs, Arm.Loc.val, satF]
    exact ⟨by decide, fits_zero, fits_zero, fits_zero, limbs_zero _, limbs_zero _⟩)

theorem gf448_mul_ct : ConstantTime isa mulArm.pre mulArm.pub mulFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem gf448_add_ct : ConstantTime isa addArm.pre addArm.pub addFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem gf448_sub_ct : ConstantTime isa subArm.pre subArm.pub subFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2, .r3])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub_agree hp)) (by native_taint_decide)

theorem gf448_mulA24_ct : ConstantTime isa mulA24Arm.pre mulA24Arm.pub mulA24Fn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1, .r2])
    (fun _ _ _ _ hp => Taint.agree_ofRegs (armPub1_agree hp)) (by native_taint_decide)

theorem gf448_mul_verified : Verified Arm.target mulFn (Proof.X448.Field16.mulContract Arm.abi) :=
  Verified.of_correct mul_arm gf448_mul_ct
    { pre := by sig_implies_pre [Proof.X448.Field16.mulContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, mulArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Proof.X448.Field16.mulContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, mulArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Proof.X448.Field16.mulContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, mulArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, bin_sat _⟩ }

theorem gf448_add_verified : Verified Arm.target addFn (Proof.X448.Field16.addContract Arm.abi) :=
  Verified.of_correct add_arm gf448_add_ct
    { pre := by sig_implies_pre [Proof.X448.Field16.addContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, addArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Proof.X448.Field16.addContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, addArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Proof.X448.Field16.addContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, addArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, bin_sat _⟩ }

theorem gf448_sub_verified : Verified Arm.target subFn (Proof.X448.Field16.subContract Arm.abi) :=
  Verified.of_correct sub_arm gf448_sub_ct
    { pre := by sig_implies_pre [Proof.X448.Field16.subContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, subArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Proof.X448.Field16.subContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, subArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Proof.X448.Field16.subContract, Proof.X448.Field16.binContract,
        Proof.X448.Field16.sig, subArm, binArm, armPre, armPub, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, bin_sat _⟩ }

theorem a24_sat : (Proof.X448.Field16.mulA24Contract Arm.abi).pre satF := by
  unfold Proof.X448.Field16.mulA24Contract
  exact Sig.contract_pre_of_check (by decide +kernel) (by
    sig_reduce [Sig.wfPre, Proof.X448.Field16.sig1, Arm.abi, Arm.argRegs, Arm.Loc.val, satF]
    exact ⟨by decide, fits_zero, fits_zero, limbs_zero _⟩)

theorem gf448_mulA24_verified : Verified Arm.target mulA24Fn (Proof.X448.Field16.mulA24Contract Arm.abi) :=
  Verified.of_correct mulA24_arm gf448_mulA24_ct
    { pre := by sig_implies_pre [Proof.X448.Field16.mulA24Contract, Proof.X448.Field16.sig1, mulA24Arm,
        armPre1, armPub1, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      post := by sig_implies_post [Proof.X448.Field16.mulA24Contract, Proof.X448.Field16.sig1, mulA24Arm,
        armPre1, armPub1, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      pub := by sig_implies_pub [Proof.X448.Field16.mulA24Contract, Proof.X448.Field16.sig1, mulA24Arm,
        armPre1, armPub1, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      sat := ⟨satF, a24_sat⟩ }

end VG.Proof.X448.Arm
