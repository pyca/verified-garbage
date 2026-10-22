module

import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Correct
import VerifiedGarbage.Proof.AesCbc.AArch64.Verified
import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.AesCbc.AArch64.Decrypt.Lit
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Impl.AesCbc.AArch64.Decrypt
public import VerifiedGarbage.Proof.AesCbc.AArch64.Block
public import VerifiedGarbage.Proof.AesCbc.AArch64.Call

/-! # The existing CBC contract, ABI, constant time, and scratch-write bound -/

@[expose] public section

namespace VG.Proof.AesCbc.AArch64.Decrypt

open VG VG.AArch64
open VG.Impl.AesCbc.AArch64.Decrypt (code)

theorem correct (s : State) (hp : (cbcAArch64 false).pre s) :
    ∃ tr t, Exec isa code s tr t ∧ abiPreserved s t ∧ (cbcAArch64 false).post s t := by
  have hk := instrs_keeps (c := code) (rs := preserved) (by lit_decide)
  have hg : code.allInstrs (fun i => preserved.all fun r => !clobbers i r) = true := by
    rwa [Code.allInstrs_eq]
  obtain ⟨tr,t,he,hq,hg⟩ := WP.gprs (rs := preserved) (code_ok (UPre.of hp)) hg (by lit_decide)
  exact ⟨tr,t,he,⟨hg,Exec.sp he,Exec.preservedV he (by lit_decide)⟩,hq.1⟩

theorem ct : ConstantTime isa (cbcAArch64 false).pre (cbcAArch64 false).pub code := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0,.x1,.x2,.x3,.x4,.x5])
    ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0,h1,h2,h3,h4,h5,hsp⟩
  refine ⟨hsp,fun r hr => ?_⟩
  simp only [VG.AArch64.Taint.mem_ofRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem implies : (cbcAArch64 false).Implies (Spec.Cbc.aesDecryptContract AArch64.abi) := by
  sig_implies [Spec.Cbc.aesDecryptContract,Spec.Cbc.aesSig,cbcAArch64,modeAArch64,cbcMode,
    ciphOf,cbc,cts,AArch64.abi,AArch64.argRegs] [sat] using sat

theorem verified : Verified AArch64.target code (Spec.Cbc.aesDecryptContract AArch64.abi) :=
  Verified.of_correct correct ct implies

/-- This path never writes scratch; no scratch bytes require clearing afterwards. -/
theorem written (s : State) (tr : List Leak) (t : State)
    (hp : (Spec.Cbc.aesDecryptContract AArch64.abi).pre s) (he : Exec isa code s tr t) :
    Sig.writtenWithin (AArch64.abi.withConsts []) Spec.Cbc.aesSig [("scratch",0)] s t := by
  have h := UPre.of (implies.pre s hp)
  obtain ⟨tr',t',he',_,hf⟩ := code_ok h
  obtain ⟨_,rfl⟩ := Exec.det he he'
  simp [Sig.writtenWithin,AArch64.abi,AArch64.argRegs,Abi.withConsts,Spec.Cbc.aesSig,
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

end VG.Proof.AesCbc.AArch64.Decrypt
