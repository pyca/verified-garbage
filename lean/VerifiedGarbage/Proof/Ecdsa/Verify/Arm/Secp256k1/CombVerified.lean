module

public import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Contract
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Hash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
public import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Secp256k1.CombCT
meta import VerifiedGarbage.Proof.Secp256k1.Arm.CombSat
meta import VerifiedGarbage.Proof.Ecdsa.Arm.SavedAbi
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.PlainSimp

/-! The generator comb satisfies the public verification contract. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.Arm.Secp256k1
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Secp256k1.Arm in
/-- A state satisfying the precondition without the tables, which it holds
in `constMem`: the comb's at `0x100000`, then the setup's constants at
`0x125000`. -/
def combVerifyBase (um : Bool) : State := {combSatState with
  gpr := fun r => match r with | .r0 => 0x10000 | .r1 => 0x12000 | .r2 => 0x14000 | _ => 0
  mem := constMem ((0x100000 : BitVec 32).setWidth 64) (secp256k1CombWords ++ (secp256k1With um).constTbl)
  rd := [⟨0x10000,65⟩,⟨0x12000,32⟩,⟨0x14000,64⟩]
  wr := [⟨0,8192⟩]
  syms := fun n => if n = (secp256k1With um).constSym then 0x125000 else 0x100000 }

/-- `combVerifyBase` with the tables' regions. -/
abbrev combVerifySat (um : Bool) : State :=
  { combVerifyBase um with rd := (combVerifyBase um).rd ++ constRegs (combVerifyK um) (combVerifyBase um) }

theorem combVerifyBase_regs (um : Bool) :
    constRegs (combVerifyK um) (combVerifyBase um) = [⟨0x100000, 8 * secp256k1CombWords.length⟩, ⟨0x125000, 8 * (17 * 4)⟩] :=
  VG.Proof.Ecdsa.Arm.constRegs_two (secp256k1With um) (T := 0x100000) (T₂ := 0x125000) (by cases um <;> decide) (by cases um <;> decide)

open VG.Proof.Secp256k1.Arm in
theorem combVerify_sat (um : Bool) : (combVerifySpec um).pre (combVerifySat um) :=
  pre_consts_append
    (by
      cases um <;>
      (sig_pre [Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.verifyContract,Proof.Ecdsa.verifySig,
    Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,Loc.val,State.addr,combVerifyBase,combSatState]
       sig_and_intros
       all_goals first
         | rfl
         | decide
         | exact Region.disjoint_of_sep (by decide)))
    (VG.Proof.Ecdsa.Arm.constsOk_two _ (T := 0x100000) (T₂ := 0x125000) (by cases um <;> decide) (by cases um <;> decide)
      (by rw [comb_words_length]; decide) rfl (by cases um <;> decide) (by decide) (by decide)
      (by rw [comb_words_length]; cases um <;> decide) (by cases um <;> decide)
      (by rw [comb_words_length]; cases um <;> decide) (by cases um <;> decide))

def combVerifyLocal (um : Bool) : Contract isa where
  pre := combVerifyPre um
  post := VPost (secp256k1With um)
  pub := combVerifyPub um

theorem combVerifyWith_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) (um : Bool)
    (hct : ConstantTime isa (combVerifyPre um) (combVerifyPub um) (verifySecp256k1CombWith um)) :
    Verified Arm.target (verifySecp256k1CombWith um) (combVerifySpec um) := by
  refine Verified.of_correct (k := combVerifyLocal um) (fun s hs => ?_) hct
    ⟨fun _ h => combVerify_pre h,?_,?_,⟨combVerifySat um,combVerify_sat um⟩⟩
  · obtain ⟨tr,t,exec,keep,post⟩ := combVerify_ok hC hs
    exact ⟨tr,t,exec,VG.Proof.Ecdsa.Arm.abi_of_saved keep.saved keep.sp,post⟩
  · intro s t _ post
    sig_post [combVerifySpec,Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr,Abi.withConsts]
    rw [show (t.gpr .r1++t.gpr .r0).setWidth 32=t.gpr .r0 from BitVec.setWidth_append_eq_right]
    exact post
  · intro s t _ _ pub
    obtain ⟨pub, sy⟩ := pub_consts.mp pub
    sig_pub [Spec.Ecdsa.Secp256k1.inst,Proof.Ecdsa.verifyContract,
      Proof.Ecdsa.verifySig,Spec.Secp256k1.curve,Spec.Ecdsa.scratchWords,abi,argRegs,reduceClassify,
      Loc.val,State.addr] at pub
    obtain ⟨sp,inputs,h0,h1,h2,h3⟩ := pub
    exact ⟨⟨⟨sp,h0,h1,h2,h3⟩,symAddr_eq_iff.mp (sy (secp256k1Comb.tsym, secp256k1CombWords) List.mem_cons_self),
      symAddr_eq_iff.mp (sy ((secp256k1With um).constSym, (secp256k1With um).constTbl)
        (List.mem_cons_of_mem _ (List.mem_singleton_self _)))⟩,VPub.of_leak h3 rfl rfl inputs⟩

theorem combVerify_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target verifySecp256k1Comb (combVerifySpec false) :=
  combVerifyWith_verified hC false (combVerify_ct hC)

theorem combVerifyU_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target verifySecp256k1CombU (combVerifySpec true) :=
  combVerifyWith_verified hC true (combVerifyU_ct hC)

/-- `combVerifySat`'s 100 bytes below `sp + 4` are free. -/
theorem hash_sat (um : Bool) :
    ∃ s, (Spec.Ecdsa.Secp256k1.inst.verifyHashContract (Arm.abi.withConsts (combVerifyK um)) 96).pre s := by
  cases um <;>
  exact VG.Proof.Ecdsa.Verify.Arm.Hash.hashSat_cons (by decide) (combVerify_sat _) (by decide) (by decide) fun r hr => by
    simp only [combVerifyBase_regs, List.mem_append] at hr
    rw [VG.Proof.Secp256k1.Arm.comb_words_length] at hr
    simp only [combVerifyBase, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with ((rfl | rfl | rfl) | rfl | rfl) | rfl <;> exact Region.disjoint_of_sep (by decide)

/-- `vg_ecdsa_secp256k1_verify`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false verifySecp256k1Comb)
      (Spec.Ecdsa.Secp256k1.inst.verifyHashContract (Arm.abi.withConsts (combVerifyK false)) 96) :=
  VG.Proof.Ecdsa.Verify.Arm.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.secp256k1_len (by decide) (combVerify_verified hC)
    ⟨_, by taint_decide⟩ (hash_sat false)

/-- `vg_ecdsa_secp256k1_verify_umaal`, taking the hash function's output: the
verification above, run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHashU_verified (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    Verified Arm.target (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false verifySecp256k1CombU)
      (Spec.Ecdsa.Secp256k1.inst.verifyHashContract (Arm.abi.withConsts (combVerifyK true)) 96) :=
  VG.Proof.Ecdsa.Verify.Arm.Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.secp256k1_len (by decide) (combVerifyU_verified hC)
    ⟨_, by taint_decide⟩ (hash_sat true)

end VG.Proof.Ecdsa.Verify.Arm.Secp256k1
