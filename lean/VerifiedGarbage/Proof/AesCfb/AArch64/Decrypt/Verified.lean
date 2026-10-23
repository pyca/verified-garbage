module

import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Correct
import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Lit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCfb.AArch64.Decrypt.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCfb.AArch64.Decrypt
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call
public import VerifiedGarbage.Spec.Cfb.Contract
public import VerifiedGarbage.Proof.AesCfb.Spec

/-! # The existing CFB contract, ABI, constant time, and scratch-write bound -/

@[expose] public section

namespace VG.Proof.AesCfb.AArch64.Decrypt

open VG VG.AArch64
open VG.Proof.AesCbc VG.Proof.AesCbc.AArch64
open VG.Impl.AesCfb.AArch64.Decrypt (code)

theorem correct (s : State) (hp : (modeAArch64 (cfbMode false)).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (modeAArch64 (cfbMode false)).post s t := by
  have hk := instrs_keeps (c := code) (rs := preserved) (by lit_decide)
  have hg : code.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
    rwa [Code.allInstrs_eq]
  obtain ⟨tr,t,he,hq,hg⟩ := WP.gprs (rs := preserved) (code_ok (UPre.of hp)) hg (by lit_decide)
  exact ⟨tr,t,he,⟨hg,Exec.sp he,Exec.preservedV he (by lit_decide)⟩,hq.1⟩

theorem ct : ConstantTime isa (modeAArch64 (cfbMode false)).pre (modeAArch64 (cfbMode false)).pub code := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0,h1,h2,h3,h4,h5,hsp⟩
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem implies : (modeAArch64 (cfbMode false)).Implies (Spec.Cfb.aesDecryptContract AArch64.abi) := by
  sig_implies [Spec.Cfb.aesDecryptContract,Spec.Cfb.aesSig,Spec.Cbc.aesSig,modeAArch64,cfbMode,cfb,cts,AArch64.abi,AArch64.argRegs] [sat] using sat

theorem verified : Verified AArch64.target code (Spec.Cfb.aesDecryptContract AArch64.abi) :=
  Verified.of_correct correct ct implies

/-- This path never writes scratch; no scratch bytes require clearing afterwards. -/
theorem written (s : State) (tr : List Leak) (t : State)
    (hp : (Spec.Cfb.aesDecryptContract AArch64.abi).pre s) (he : Exec isa code s tr t) :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Cfb.aesSig [("scratch",0)] s t := by
  have h := UPre.of (implies.pre s hp)
  obtain ⟨tr',t',he',_,hf⟩ := code_ok h
  obtain ⟨_,rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin,AArch64.abi,AArch64.argRegs,Abi.withConsts,Spec.Cfb.aesSig,Spec.Cbc.aesSig,
    Sig.words,Sig.arrays,Param.words,ArgWord.bits]
  intro i hi
  apply hf
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  have hi' : i < 2176 := by simpa [Elem.size] using hi
  have hc : (scrR s).Contains (S s+BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega) (by omega)
  rcases hr with rfl | rfl
  · exact fun hi => h.iv_scr _ hi hc
  · exact fun hi => h.data_scr _ hi hc

end VG.Proof.AesCfb.AArch64.Decrypt
