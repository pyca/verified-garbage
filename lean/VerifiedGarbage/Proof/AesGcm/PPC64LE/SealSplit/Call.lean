module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Input
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Verified
public import VerifiedGarbage.Proof.Gcm.SplitBlocksContract
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Offset

-- separate module: the split-seal caller's outgoing block-helper argument.
/-! # Calling the verified source-prefix block helper -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealSplit.Call
open VG VG.PPC64LE


def registers : List Reg := [.r0,.r3,.r4,.r5,.r6,.r8,.r9,.r10,.r12]

def argsRegs (s : State) : State :=
  ((((((((s.write .r3 (s.gpr .r29)).write .r4 (s.gpr .r28)).write .r5 (s.gpr .r30+48)).write
    .r6 (s.gpr .r30+16)).write .r8 (s.gpr .r8 >>> 4)).write .r9 (s.gpr .r27)).write
    .r10 (s.gpr .r23 >>> 4)).write .r0 (s.gpr .r31+448)).write .r12 s.sp

def argsState (s : State) : State :=
  {argsRegs s with mem := s.mem.writeW (s.sp+96) (s.gpr .r31+448)}


theorem args_ok (s : State) (hw : InRegions s.wr (s.sp+96) 8) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealSplit.blockArgs) s (· = argsState s) := by
  have ha : ∀ u : State, exec (.addSp .r12 0) u=some (u.write .r12 u.sp) := by
    intro u
    simp only [exec,Nat.reducePow,Nat.reduceLT,ite_true,BitVec.add_zero]
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SealSplit.blockArgs,Impl.AesGcm.PPC64LE.mov,
    runBlock_cons,runStep_some,exec_logic,BitVec.or_self,
    exec_addi (n := .r30) (imm := 48) (by decide) (by decide),
    exec_addi (n := .r30) (imm := 16) (by decide) (by decide),
    exec_addi (n := .r31) (imm := 448) (by decide) (by decide),exec_lsr_d (sh := 4) (by decide),ha,
    RegUpd.gpr_write,RegUpd.sp_write,reduceCtorEq,ite_false]
  change ∃ t, runStep isa (exec (.store .d .r0 .r12 96) (argsRegs s)) []=some t ∧ t=argsState s
  have hw' : InRegions (argsRegs s).wr ((argsRegs s).gpr .r12+96) 8 := hw
  rw [exec_store_d (s := argsRegs s) (n := .r12) (off := 96) (by decide) ⟨by decide,by decide⟩ hw']
  simp only [runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left']
  rfl


theorem args_keep (s : State) (hw : InRegions s.wr (s.sp+96) 8) :
    Keep registers s (argsState s) := by
  obtain ⟨_,_,_,he,hk⟩ := WP.keep registers (args_ok s hw) (by decide) (by decide)
  subst he
  exact hk



theorem args_frame (s : State) : Frame [⟨s.sp+96,8⟩] s.mem (argsState s).mem := by
  change Frame _ s.mem (s.mem.writeW (s.sp+96) (s.gpr .r31+448))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)


def reads (s : State) : List Region :=
  [⟨s.gpr .r3,256⟩,⟨s.gpr .r7,(s.gpr .r8).toNat*16⟩,⟨s.sp+96,8⟩]
def writes (s : State) : List Region :=
  [⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩,⟨s.gpr .r9,(s.gpr .r10).toNat*16⟩,
    ⟨s.mem.readW (s.sp+96) 64,2112⟩]

structure Config (s : State) : Prop where
  pre : (Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi).pre (s.callEntry.withRegions (reads s) (writes s))
  reads : Covers (Call.reads s++writes s) (s.rd++s.wr)
  writes : Covers (Call.writes s) s.wr

structure Result (s t : State) : Prop where
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  saved : ∀ r ∈ preserved, t.gpr r=s.gpr r
  frame : Frame (writes s) s.mem t.mem
  ciphertext : Spec.Gcm.blocksAt t.mem (s.gpr .r9) (s.gpr .r10).toNat=
    Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph s.mem (s.gpr .r3) (s.gpr .r4).toNat)
      (Spec.Gcm.blockAt s.mem (s.gpr .r5))
      (Spec.Gcm.blocksAt s.mem (s.gpr .r7) (s.gpr .r8).toNat++
        (Spec.Gcm.blocksAt s.mem (s.gpr .r9) (s.gpr .r10).toNat).drop (s.gpr .r8).toNat)
  counter : Spec.Gcm.blockAt t.mem (s.gpr .r5)=Nat.repeat Spec.Gcm.inc32 (s.gpr .r10).toNat
    (Spec.Gcm.blockAt s.mem (s.gpr .r5))
  hash : Spec.Gcm.blockAt t.mem (s.gpr .r6)=Spec.Gcm.ghashFrom (Spec.Gcm.ctxH s.mem (s.gpr .r3))
    (Spec.Gcm.blockAt s.mem (s.gpr .r6)) (Spec.Gcm.blocksAt t.mem (s.gpr .r9) (s.gpr .r10).toNat)


theorem ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} (cfg : Config s) :
    WP isa (.call "vg_aes_gcm_encrypt_blocks_split" Impl.AesGcm.PPC64LE.SplitBlocks.encrypt) s (Result s) := by
  refine WP.call (k := Proof.Gcm.encryptBlocksSplitContract PPC64LE.abi)
    VG.Proof.AesGcm.PPC64LE.SplitBlocks.encrypt_correct (rd := reads s) (wr := writes s)
    cfg.pre cfg.reads cfg.writes ?_
  intro t hrd hwr hsp hf hcs _ hp
  sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPost,
    PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop] at hp
  exact ⟨hrd,hwr,hsp,hcs,hf,hp.1,hp.2.1,by rw [hp.1]; exact hp.2.2⟩

end VG.Proof.AesGcm.PPC64LE.SealSplit.Call
