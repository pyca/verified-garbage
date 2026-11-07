module

public import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
public import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Impl.Cast5.Arm.FbFinal
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
public import VerifiedGarbage.Proof.Framework.ConstMem
import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
import VerifiedGarbage.Proof.Modes.Arm.Cbc
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Cast5.Arm.ModesVerified
meta import VerifiedGarbage.Proof.Modes.Arm.SeqFinalCT
meta import VerifiedGarbage.Proof.Cast5.CfbFinal
meta import VerifiedGarbage.Impl.Cast5.Arm.FbFinal
meta import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
meta import VerifiedGarbage.Proof.Framework.ConstMem
meta import VerifiedGarbage.Proof.Modes.Arm.OfbCfb
meta import VerifiedGarbage.Proof.Cast5.Arm.EcbVerified
meta import VerifiedGarbage.Proof.Cast5.Table
meta import VerifiedGarbage.Proof.Modes.Arm.Cbc
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# CAST5-CFB64 and CAST5-OFB of a message's last piece on ARMv7 meet their contracts

The generic CFB and OFB over a message's last piece (`Proof.Modes.Arm.seqFinal_verified`)
over CAST5's ECB encryption (`ecbSpec true`, a core taking the number of
rounds and its working space as a stack argument, and reading the table
`VG_CAST5_S1234`) meet the contracts on the subkeys at the schedule
(`Proof.Cast5.cfbEncFinalPost`, …) with a scratch buffer of 39 words, as the
whole-block functions do (`ModesVerified.lean`), with the specification's
results (`Proof.Modes.Arm.cfbEncFinal_post`, …,
`Proof.Modes.Arm.ofbFinal_post`); the `_framed` theorems keep
the buffer on the stack, zeroed on return: 328 bytes more.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Impl.Cast5.Arm VG.Impl.Modes.Arm VG.Proof.Modes.Arm
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

theorem cfbFinal_sat (post : Spec.Cast5.cfbFinalSig.Post Arm.abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 39
      (Spec.Cast5.cfbFinalPre Arm.abi.ptrBits) post 8).pre s := by
  refine ⟨modeSatC true, ?_⟩
  have a0 := modeSatC_arg true (i := 0) (by decide)
  have a1 := modeSatC_arg true (i := 1) (by decide)
  have held := modeSatMem_held
  generalize e : modeSatC true = s at a0 a1
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0, a1]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0, 312⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem cfbFinalFrame_sat (post : Spec.Cast5.cfbFinalSig.Post Arm.abi.ptrBits) :
    ∃ s, (Spec.Cast5.cfbFinalSig.contract (Arm.abi.withConsts ecbConsts) (Spec.Cast5.cfbFinalPre Arm.abi.ptrBits) post
      true (8 + 328)).pre s := by
  refine ⟨frameSatC true, ?_⟩
  have a0 := frameSatC_arg true (i := 0) (by decide)
  have held := modeSatMem_held
  generalize e : frameSatC true = s at a0
  sig_pre [Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem cfbEncryptFinalTaint : FinalTaint (ecbCore true) cfbEnc :=
  ⟨cfbEncryptTaint.pro, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, cfbEncryptTaint.epi⟩

theorem cfbEncryptFinal_implies : (seqFinalArm (ecbCore true) (ecbSpec true) cfbEnc).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 39
      (Spec.Cast5.cfbFinalPre Arm.abi.ptrBits) (Proof.Cast5.cfbEncFinalPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm)
      (rd' := (stripConsts ecbConsts s).rd) ?_ (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbEncFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbEncFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR (M := byteMode) h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := cfbFinal_sat _

theorem cfbEncryptFinal_verified : Verified Arm.target cfbEncryptFinal
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 39
      (Spec.Cast5.cfbFinalPre Arm.abi.ptrBits) (Proof.Cast5.cfbEncFinalPost Arm.abi.ptrBits) 8) :=
  seqFinal_verified (ecbSpec true) (cfbEnc_finalOk _ (by decide) (by decide) (by decide)) cfbEncryptFinalTaint
    cfbEncryptFinal_implies

/-- `cfbEncryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbEncryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cfbEncryptFinal)
      (Proof.Cast5.cfbEncryptFinalRoundsContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 39) (pre := Spec.Cast5.cfbFinalPre Arm.abi.ptrBits)
    (post := Proof.Cast5.cfbEncFinalPost Arm.abi.ptrBits) (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cfbEncryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cfbEncFinalPost_local _)
    (Proof.Cast5.cfbEncFinalPostOut_local _) (cfbFinalFrame_sat _)

theorem cfbDecryptFinalTaint : FinalTaint (ecbCore true) cfbDecF :=
  ⟨cfbDecryptTaint.pro, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, cfbDecryptTaint.epi⟩

theorem cfbDecryptFinal_implies : (seqFinalArm (ecbCore true) (ecbSpec true) cfbDecF).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 39
      (Spec.Cast5.cfbFinalPre Arm.abi.ptrBits) (Proof.Cast5.cfbDecFinalPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm)
      (rd' := (stripConsts ecbConsts s).rd) ?_ (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Spec.Cast5.cfbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Proof.Cast5.cfbDecFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := cfbDecFinal_post h
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.cfbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR (M := byteMode) h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := cfbFinal_sat _

theorem cfbDecryptFinal_verified : Verified Arm.target cfbDecryptFinal
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.cfbFinalSig 39
      (Spec.Cast5.cfbFinalPre Arm.abi.ptrBits) (Proof.Cast5.cfbDecFinalPost Arm.abi.ptrBits) 8) :=
  seqFinal_verified (ecbSpec true) (cfbDecF_finalOk _ (by decide) (by decide) (by decide)) cfbDecryptFinalTaint
    cfbDecryptFinal_implies

/-- `cfbDecryptFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem cfbDecryptFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 cfbDecryptFinal)
      (Proof.Cast5.cfbDecryptFinalRoundsContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.cfbFinalSig)
    (nm := "scratch") (e := .u64) (n := 39) (pre := Spec.Cast5.cfbFinalPre Arm.abi.ptrBits)
    (post := Proof.Cast5.cfbDecFinalPost Arm.abi.ptrBits) (wa := true) (stack := 8) (m := 1) (bytes := 328)
    cfbDecryptFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.cfbFinalPre_local _ vs m₁ m₂ hl h) (Proof.Cast5.cfbDecFinalPost_local _)
    (Proof.Cast5.cfbDecFinalPostOut_local _) (cfbFinalFrame_sat _)

/-! ## OFB of a message's last piece -/

theorem ofbFinal_sat (post : Spec.Cast5.ofbFinalSig.Post Arm.abi.ptrBits) :
    ∃ s, (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.ofbFinalSig 39
      (Spec.Cast5.ofbFinalPre Arm.abi.ptrBits) post 8).pre s := by
  refine ⟨modeSatC true, ?_⟩
  have a0 := modeSatC_arg true (i := 0) (by decide)
  have a1 := modeSatC_arg true (i := 1) (by decide)
  have held := modeSatMem_held
  generalize e : modeSatC true = s at a0 a1
  sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
    Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, ecbConsts_eq,
    Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0, a1]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩, ⟨0, 312⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem ofbFinalFrame_sat (post : Spec.Cast5.ofbFinalSig.Post Arm.abi.ptrBits) :
    ∃ s, (Spec.Cast5.ofbFinalSig.contract (Arm.abi.withConsts ecbConsts) (Spec.Cast5.ofbFinalPre Arm.abi.ptrBits) post
      true (8 + 328)).pre s := by
  refine ⟨frameSatC true, ?_⟩
  have a0 := frameSatC_arg true (i := 0) (by decide)
  have held := modeSatMem_held
  generalize e : frameSatC true = s at a0
  sig_pre [Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
    ecbConsts_eq, Abi.withConsts, Abi.constRegions, Abi.constsHeld, stackBelow, s1234_length]
  subst e
  rw [a0]
  refine ⟨by decide, by decide, by decide, fun i hi => held i (by rw [s1234_length]; exact hi), by decide, ?_, ?_⟩
  · intro r hr
    change r ∈ ([⟨0x2000, 8⟩, ⟨0x3000, 0⟩] : List Region) at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact Region.disjoint_of_sep (by decide)
  · repeat' apply And.intro
    all_goals first | exact Region.disjoint_of_sep (by decide) | decide | rfl | exact Or.inl rfl

theorem ofbFinalTaint : FinalTaint (ecbCore true) VG.Impl.Modes.Arm.ofb :=
  ⟨ofbTaint.pro, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ofbTaint.epi⟩

theorem ofbFinal_implies : (seqFinalArm (ecbCore true) (ecbSpec true) VG.Impl.Modes.Arm.ofb).Implies
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.ofbFinalSig 39
      (Spec.Cast5.ofbFinalPre Arm.abi.ptrBits) (Proof.Cast5.ofbFinalPost Arm.abi.ptrBits) 8) where
  pre s h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h1, hk⟩ := pre_consts.mp h
    refine seqArm_pre_rwR' (M := byteMode) rfl (len := fun n => n) (fun n => (Nat.mul_one n).symm)
      (rd' := (stripConsts ecbConsts s).rd) ?_ (fun r hr => stripConsts_rd_mem hr) (tabsOk_of hk (by decide))
    sig_pre [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbFinalSig, Spec.Cast5.ofbFinalPre, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h1
    exact h1
  post s s' _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract
    refine post_consts.mpr ?_
    sig_post [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbFinalSig, Proof.Cast5.ofbFinalPost, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    have e := ofbFinal_post h fun b => by
      show _ = 8
      simp [ecbSpec, Proof.Cast5.dirCipher, Spec.Cast5.cipher]
    obtain ⟨e1, e2, e3, -, -⟩ := args_rounds (c := ecbCore true) rfl s
    simp only [show (ecbCore true).bs = 8 from rfl, e1, e2, e3] at e
    simp only [ecbSpec, Proof.Cast5.dirCipher, ↓reduceIte, State.addr] at e
    exact e
  pub s₁ s₂ _ _ h := by
    unfold Proof.Cast5.modeScratchContract Sig.scratchContract at h
    obtain ⟨h, hsy⟩ := pub_consts.mp h
    sig_pub [Proof.Cast5.modeScratchContract, Sig.scratchContract, Sig.withScratch, Curry.withScratch,
      Spec.Cast5.ofbFinalSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
    exact seqArm_pubR (M := byteMode) h fun x hx => symAddr_eq_iff.mp (hsy x hx)
  sat := ofbFinal_sat _

theorem ofbFinal_verified : Verified Arm.target ofbFinal
    (Proof.Cast5.modeScratchContract (Arm.abi.withConsts ecbConsts) Spec.Cast5.ofbFinalSig 39
      (Spec.Cast5.ofbFinalPre Arm.abi.ptrBits) (Proof.Cast5.ofbFinalPost Arm.abi.ptrBits) 8) :=
  seqFinal_verified (ecbSpec true) (ofb_finalOk _ (by decide) (by decide) (by decide)) ofbFinalTaint
    ofbFinal_implies

/-- `ofbFinal`, with its scratch buffer on the stack (zeroed on return). -/
theorem ofbFinal_framed :
    Verified Arm.target (Impl.StackScratch.Arm.withStackScratchWiped 328 1 78 ofbFinal)
      (Proof.Cast5.ofbFinalRoundsContract (Arm.abi.withConsts ecbConsts) 336) :=
  Arm.Verified.stackScratchWipedC (c₀ := (s1234Sym, s1234)) (cs := []) (sig := Spec.Cast5.ofbFinalSig)
    (nm := "scratch") (e := .u64) (n := 39) (pre := Spec.Cast5.ofbFinalPre Arm.abi.ptrBits)
    (post := Proof.Cast5.ofbFinalPost Arm.abi.ptrBits) (wa := true) (stack := 8) (m := 1) (bytes := 328)
    ofbFinal_verified (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun vs m₁ m₂ hl _ h => Proof.Cast5.ofbFinalPre_local _ vs m₁ m₂ hl h) (Proof.Cast5.ofbFinalPost_local _)
    (Proof.Cast5.ofbFinalPostOut_local _) (ofbFinalFrame_sat _)

end VG.Proof.Cast5.Arm
