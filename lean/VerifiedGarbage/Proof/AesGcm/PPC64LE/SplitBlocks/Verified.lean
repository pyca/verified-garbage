module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
public import VerifiedGarbage.Proof.Gcm.SplitBlocksContract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

-- separate module: verification of the callable source-prefix helper.
/-! # Verified whole-block AES-GCM with an external plaintext prefix -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SplitBlocks
open VG VG.PPC64LE
open Contract (prepared scratch)


/-- The blocks the helper processes: the source prefix, then the rest of the
destination. -/
def inBlocks (s : State) : List Spec.Gcm.Block :=
  Spec.Gcm.blocksAt s.mem (s.gpr .r7) (s.gpr .r8).toNat ++
    (Spec.Gcm.blocksAt s.mem (s.gpr .r9) (s.gpr .r10).toNat).drop (s.gpr .r8).toNat

def outBlocks (s : State) : List Spec.Gcm.Block :=
  Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat) (Spec.Gcm.blockAt s.mem (s.gpr .r5))
    (inBlocks s)

/-- Encryption (`dec = false`) or decryption: the output at `dst`, the
counter advanced, and GHASH over the ciphertext, the output or the input. -/
structure CryptPost (dec : Bool) (s t : State) : Prop where
  saved : ∀ r ∈ preserved, t.gpr r=s.gpr r
  lr : t.lr=s.lr
  out : Spec.Gcm.blocksAt t.mem (s.gpr .r9) (s.gpr .r10).toNat=outBlocks s
  counter : Spec.Gcm.blockAt t.mem (s.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (s.gpr .r10).toNat
    (Spec.Gcm.blockAt s.mem (s.gpr .r5))
  y : Spec.Gcm.blockAt t.mem (s.gpr .r6)=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem (s.gpr .r3))
    (Spec.Gcm.blockAt s.mem (s.gpr .r6)) (bif dec then inBlocks s else outBlocks s)


/-- After the arguments are in place (`Contract.prep`): the helper's body. -/
theorem rest_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] (dec : Bool)
    (t : State) (lay : Wrapper.Layout (Contract.prep t) (t.gpr .r10).toNat (t.gpr .r8).toNat)
    (hv : (t.gpr .r4).toNat=10 ∨ (t.gpr .r4).toNat=12 ∨ (t.gpr .r4).toNat=14)
    (hwork : Covers [⟨t.gpr .r11,2112⟩] t.wr) :
    WP isa (Impl.AesGcm.PPC64LE.SplitBlocks.restOf dec) t (CryptPost dec t) := by
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.restOf]
  apply WP.seq
  refine WP.mono (Wrapper.rest_ok t (by
    intro p hp
    have ho : ∀ p ∈ Impl.AesGcm.PPC64LE.SplitBlocks.extraSaved, p.2+8≤2112 := by decide
    exact hwork _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ (ho p hp) (by have := ho p hp; omega)⟩))
    fun restState hr => ?_
  subst restState
  refine WP.mono (Wrapper.body_ok dec (Contract.prep t) (t.gpr .r10).toNat (t.gpr .r4).toNat (t.gpr .r8).toNat lay
    (by change t.gpr .r10=BitVec.ofNat 64 (t.gpr .r10).toNat; simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq])
    (by change t.gpr .r4=BitVec.ofNat 64 (t.gpr .r4).toNat; simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq])
    hv t.gpr (Contract.prep_saved t)) fun u hu => ?_
  have hnr : (t.gpr .r4).toNat<15 := by rcases hv with h | h | h <;> omega
  have hc := hu.ciphertext
  have hctr := hu.counter
  have hy := hu.y
  change Spec.Gcm.blocksAt u.mem (t.gpr .r9) (t.gpr .r10).toNat=
    Wrapper.ciphertext (Contract.prep t) (t.gpr .r4).toNat (t.gpr .r8).toNat (t.gpr .r10).toNat at hc
  change Spec.Gcm.blockAt u.mem (t.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (t.gpr .r10).toNat
    (Spec.Gcm.blockAt (Contract.prep t).mem (t.gpr .r5)) at hctr
  change Spec.Gcm.blockAt u.mem (t.gpr .r6)=Spec.Gcm.ghashFrom
    (Spec.Gcm.ctxH (Contract.prep t).mem (t.gpr .r3)) (Spec.Gcm.blockAt (Contract.prep t).mem (t.gpr .r6))
    (Wrapper.hashed dec (Contract.prep t) (t.gpr .r4).toNat (t.gpr .r8).toNat (t.gpr .r10).toNat) at hy
  have hh : Wrapper.hashed dec (Contract.prep t) (t.gpr .r4).toNat (t.gpr .r8).toNat (t.gpr .r10).toNat=
      bif dec then inBlocks t else outBlocks t := by
    cases dec
    · exact Contract.prep_ciphertext lay hnr
    · exact Contract.prep_blocks lay
  rw [Contract.prep_ciphertext lay hnr] at hc
  rw [Contract.prep_counter lay] at hctr
  rw [Contract.prep_h lay,Contract.prep_y lay,hh] at hy
  exact ⟨fun r hr => (hu.saved r hr).trans (Contract.prep_preserved t r hr),hu.lr,hc,hctr,hy⟩


theorem crypt_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] (dec : Bool)
    (s : State) (hs : (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre s) :
    WP isa (Impl.AesGcm.PPC64LE.SplitBlocks.cryptOf dec) s (CryptPost dec s) := by
  obtain ⟨lay,hv,hread,hwork⟩ := Contract.shared_pre s hs
  rw [Impl.AesGcm.PPC64LE.SplitBlocks.cryptOf]
  by_cases hz : s.gpr .r10=0
  · have hn0 : (s.gpr .r10).toNat=0 := by rw [hz]; rfl
    have hcount : (s.gpr .r8).toNat=0 := by
      have hb := lay.bound
      change (s.gpr .r8).toNat≤(s.gpr .r10).toNat at hb
      rw [hz] at hb
      exact Nat.eq_zero_of_le_zero hb
    have hi : inBlocks s=[] := by
      simp only [inBlocks,hn0,hcount,Spec.Gcm.blocksAt,List.range_zero,List.map_nil,List.drop_nil,
        List.nil_append]
    have ho : outBlocks s=[] := by
      simp only [outBlocks,hi,Spec.Gcm.ctr32,Spec.Gcm.keystream,List.length_nil,List.zipWith_nil_left]
    refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hz]; rfl)
      (fun _ => WP.block_nil ⟨fun _ _ => rfl,rfl,?_,?_,?_⟩) (by simp)
    · simp only [ho,hn0,Spec.Gcm.blocksAt,List.range_zero,List.map_nil]
    · simp only [hn0]; rfl
    · cases dec <;> simp only [hi,ho,Bool.cond_true,Bool.cond_false,Spec.Gcm.ghashFrom,List.foldl_nil]
  · refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
      Option.some.injEq,beq_eq_false_iff_ne] using hz) (by simp) (fun _ => ?_)
    apply WP.seq
    refine WP.mono (Wrapper.head_ok s hread) fun headState hh => ?_
    subst headState
    refine WP.mono (rest_wp dec (Wrapper.headState s) lay hv hwork) fun u ⟨hsv,hl,ho,hc,hy⟩ => ?_
    have hf : ∀ r ∈ preserved, r≠.r11 ∧ r≠.r12 := by decide
    refine ⟨fun r hr => (hsv r hr).trans ?_,hl,ho,hc,hy⟩
    simp only [Wrapper.headState,RegUpd.gpr_write,(hf r hr).1,(hf r hr).2,ite_false]


theorem encrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (hs : (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre s) :
    ∃ tr t, Exec isa Impl.AesGcm.PPC64LE.SplitBlocks.encrypt s tr t ∧ abiPreserved s t ∧
      (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).post s t := by
  obtain ⟨tr,t,he,hp⟩ := crypt_wp false s hs
  refine ⟨tr,t,he,⟨hp.saved,Exec.sp he,hp.lr⟩,?_⟩
  sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPost,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
  exact ⟨hp.out,hp.counter,hp.y⟩


theorem toArgs_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.SplitBlocks.toArgs) s (· = Contract.toArgsState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SplitBlocks.toArgs,Impl.Aes.PPC64LE.Crypto.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    exec_addi (n := .r5) (imm := 32) (by decide) (by decide),
    RegUpd.gpr_write,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl


theorem decryptTo_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (hs : (Proof.Gcm.decryptBlocksToContract PPC64LE.abi).pre s) :
    ∃ tr t, Exec isa Impl.AesGcm.PPC64LE.SplitBlocks.decryptTo s tr t ∧ abiPreserved s t ∧
      (Proof.Gcm.decryptBlocksToContract PPC64LE.abi).post s t := by
  obtain ⟨lay,hv,hwork⟩ := Contract.to_pre s hs
  have hfunc : WP isa Impl.AesGcm.PPC64LE.SplitBlocks.decryptTo s fun t =>
      (∀ r ∈ preserved, t.gpr r=s.gpr r) ∧ t.lr=s.lr ∧
      (Proof.Gcm.decryptBlocksToContract PPC64LE.abi).post s t := by
    rw [Impl.AesGcm.PPC64LE.SplitBlocks.decryptTo]
    by_cases hz : s.gpr .r7=0
    · have hn0 : (s.gpr .r7).toNat=0 := by rw [hz]; rfl
      refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hz]; rfl)
        (fun _ => WP.block_nil ⟨fun _ _ => rfl,rfl,?_⟩) (by simp)
      sig_eval [Proof.Gcm.decryptBlocksToContract,Proof.Gcm.decryptBlocksToSig,Proof.Gcm.decryptBlocksToPost,
        PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
      simp only [hn0,Spec.Gcm.blocksAt,List.range_zero,List.map_nil,
        Spec.Gcm.ctr32,Spec.Gcm.keystream,List.length_nil,List.zipWith_nil_left,Spec.Gcm.ghashFrom,List.foldl_nil]
      exact ⟨trivial,rfl,trivial⟩
    · refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
        Option.some.injEq,beq_eq_false_iff_ne] using hz) (by simp) (fun _ => ?_)
      apply WP.seq
      refine WP.mono (toArgs_ok s) fun t ht => ?_
      subst t
      refine WP.mono (rest_wp true (Contract.toArgsState s) lay hv hwork) fun u ⟨hsv,hl,ho,hc,hy⟩ => ?_
      have hf : ∀ r ∈ preserved, r≠.r5 ∧ r≠.r6 ∧ r≠.r7 ∧ r≠.r8 ∧ r≠.r9 ∧ r≠.r10 ∧ r≠.r11 := by decide
      refine ⟨fun r hr => (hsv r hr).trans ?_,hl,?_⟩
      · obtain ⟨a,b,c,d,e,f,g⟩ := hf r hr
        simp only [Contract.toArgsState,RegUpd.gpr_write,a,b,c,d,e,f,g,ite_false]
      · have hd : (Spec.Gcm.blocksAt s.mem (s.gpr .r8) (s.gpr .r7).toNat).drop (s.gpr .r7).toNat=[] :=
          List.drop_eq_nil_of_le (by simp only [Spec.Gcm.blocksAt,List.length_map,List.length_range,Nat.le_refl])
        simp only [outBlocks,inBlocks,Bool.cond_true,Contract.toArgsState,RegUpd.gpr_write,RegUpd.mem_write,
          reduceCtorEq,ite_true,ite_false,hd,List.append_nil] at ho hc hy
        sig_eval [Proof.Gcm.decryptBlocksToContract,Proof.Gcm.decryptBlocksToSig,Proof.Gcm.decryptBlocksToPost,
          PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
        exact ⟨ho,hc,hy⟩
  obtain ⟨tr,t,he,hg,hlr,hpost⟩ := hfunc
  exact ⟨tr,t,he,⟨hg,Exec.sp he,hlr⟩,hpost⟩

end VG.Proof.AesGcm.PPC64LE.SplitBlocks
