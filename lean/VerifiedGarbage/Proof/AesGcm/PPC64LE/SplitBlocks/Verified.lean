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


theorem encrypt_correct [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (s : State) (hs : (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre s) :
    ∃ tr t, Exec isa Impl.AesGcm.PPC64LE.SplitBlocks.encrypt s tr t ∧ abiPreserved s t ∧
      (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).post s t := by
  obtain ⟨lay,hv,hread,hwork⟩ := Contract.shared_pre s hs
  have hfunc : WP isa Impl.AesGcm.PPC64LE.SplitBlocks.encrypt s fun t =>
      (∀ r ∈ preserved, t.gpr r=s.gpr r) ∧ t.lr=s.lr ∧
      (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).post s t := by
    rw [Impl.AesGcm.PPC64LE.SplitBlocks.encrypt]
    by_cases hz : s.gpr .r10=0
    · have hn0 : (s.gpr .r10).toNat=0 := by rw [hz]; rfl
      have hcount : (s.gpr .r8).toNat=0 := by
        have hb := lay.bound
        change (s.gpr .r8).toNat≤(s.gpr .r10).toNat at hb
        rw [hz] at hb
        exact Nat.eq_zero_of_le_zero hb
      refine WP.ite true (by simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,hz]; rfl)
        (fun _ => WP.block_nil ⟨fun _ _ => rfl,rfl,?_⟩) (by simp)
      sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPost,
        PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
      simp only [hn0,hcount,Spec.Gcm.blocksAt,List.range_zero,List.map_nil,List.drop_nil,List.nil_append,
        Spec.Gcm.ctr32,Spec.Gcm.keystream,List.length_nil,List.zipWith_nil_left,Spec.Gcm.ghashFrom,List.foldl_nil]
      exact ⟨trivial,rfl,trivial⟩
    · refine WP.ite false (by simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,
        Option.some.injEq,beq_eq_false_iff_ne] using hz) (by simp) (fun _ => ?_)
      apply WP.seq
      refine WP.mono (Wrapper.head_ok s hread) fun headState hh => ?_
      subst headState
      rw [Impl.AesGcm.PPC64LE.SplitBlocks.rest]
      apply WP.seq
      refine WP.mono (Wrapper.rest_ok (Wrapper.headState s) (by
        intro p hp
        have ho : ∀ p ∈ Impl.AesGcm.PPC64LE.SplitBlocks.extraSaved, p.2+8≤2112 := by decide
        exact hwork _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ (ho p hp) (by have := ho p hp; omega)⟩))
        fun restState hr => ?_
      subst restState
      refine WP.mono (Wrapper.body_ok (prepared s) (s.gpr .r10).toNat (s.gpr .r4).toNat (s.gpr .r8).toNat lay
        (by change s.gpr .r10=BitVec.ofNat 64 (s.gpr .r10).toNat; simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq])
        (by change s.gpr .r4=BitVec.ofNat 64 (s.gpr .r4).toNat; simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]) hv s.gpr (Contract.prepared_saved s)) fun t ht => ?_
      refine ⟨fun r hr => (ht.saved r hr).trans (Contract.prepared_preserved s r hr),ht.lr,?_⟩
      sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPost,
        PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
      have hc := ht.ciphertext
      have hctr := ht.counter
      have hy := ht.y
      change Spec.Gcm.blocksAt t.mem (s.gpr .r9) (s.gpr .r10).toNat=
        Wrapper.ciphertext (prepared s) (s.gpr .r4).toNat (s.gpr .r8).toNat (s.gpr .r10).toNat at hc
      change Spec.Gcm.blockAt t.mem (s.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (s.gpr .r10).toNat
        (Spec.Gcm.blockAt (prepared s).mem (s.gpr .r5)) at hctr
      change Spec.Gcm.blockAt t.mem (s.gpr .r6)=Spec.Gcm.ghashFrom
        (Spec.Gcm.ctxH (prepared s).mem (s.gpr .r3)) (Spec.Gcm.blockAt (prepared s).mem (s.gpr .r6))
        (Wrapper.ciphertext (prepared s) (s.gpr .r4).toNat (s.gpr .r8).toNat (s.gpr .r10).toNat) at hy
      rw [Contract.prepared_ciphertext lay (by rcases hv with h | h | h <;> omega)] at hc hy
      rw [Contract.prepared_counter lay] at hctr
      rw [Contract.prepared_h lay,Contract.prepared_y lay] at hy
      exact ⟨hc,hctr,hy⟩
  obtain ⟨tr,t,he,hg,hlr,hpost⟩ := hfunc
  exact ⟨tr,t,he,⟨hg,Exec.sp he,hlr⟩,hpost⟩



def encryptSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 10 | .r5 => 0x2000 | .r6 => 0x3000 | .r7 => 0x4000 | .r9 => 0x5000 | _ => 0
  lr := 0
  sp := 0x8000
  mem := Mem.writeW (fun _ => 0) (0x8000+96) (0x6000#64)
  rd := [⟨0x1000,256⟩,⟨0x4000,0⟩,⟨0x8000+96,8⟩]
  wr := [⟨0x2000,16⟩,⟨0x3000,16⟩,⟨0x5000,0⟩,⟨0x6000,2112⟩]


theorem encrypt_sat : (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre encryptSat := by
  sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPre,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop,encryptSat]
  refine ⟨by decide,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
  all_goals exact Offset.disjoint_of_le (by decide) (by decide)


theorem encrypt_verified [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw] :
    Verified PPC64LE.target Impl.AesGcm.PPC64LE.SplitBlocks.encrypt (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi) :=
  ⟨encrypt_correct,encrypt_ct,⟨encryptSat,encrypt_sat⟩⟩

end VG.Proof.AesGcm.PPC64LE.SplitBlocks
