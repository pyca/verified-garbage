module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE.SealFused
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Crypt
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Ghash
public import VerifiedGarbage.Proof.Gcm.PPC64LE.Vpmsum.Groups
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Gcm.Compose
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Tag
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.OneShot
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.Proof.Gcm.Contract
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Blocks
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.CryptOk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.AesGcm.PPC64LE.FinTag
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.SigEval

-- separate module: the one-shot caller composes the block proof with tail and tag proofs.
/-! # The fused AES-GCM whole-block call from one-shot seal -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.SealFused
open VG VG.PPC64LE

def blockReads (s : State) : List Region := [⟨s.gpr .r3,256⟩]
def blockWrites (s : State) : List Region :=
  [⟨s.gpr .r5,16⟩,⟨s.gpr .r6,16⟩,⟨s.gpr .r7,(s.gpr .r8).toNat*16⟩,⟨s.gpr .r9,2112⟩]

structure BlockCall (s : State) : Prop where
  pre : (Proof.Gcm.encryptBlocksContract PPC64LE.abi).pre
    (s.callEntry.withRegions (blockReads s) (blockWrites s))
  reads : Covers (blockReads s++blockWrites s) (s.rd++s.wr)
  writes : Covers (blockWrites s) s.wr

structure BlockPost (s t : State) : Prop where
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp
  saved : ∀ r ∈ preserved, t.gpr r=s.gpr r
  frame : Frame (blockWrites s) s.mem t.mem
  out : (Proof.Gcm.encryptBlocksContract PPC64LE.abi).post s t


theorem block_call [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {s : State} (h : BlockCall s) :
    WP isa (.call "vg_aes_gcm_encrypt_blocks" Impl.AesGcm.PPC64LE.Blocks.encrypt) s (BlockPost s) := by
  refine WP.call (k := Proof.Gcm.encryptBlocksContract PPC64LE.abi)
    VG.Proof.AesGcm.PPC64LE.Blocks.encrypt_correct (rd := blockReads s) (wr := blockWrites s)
    h.pre h.reads h.writes ?_
  intro t hrd hwr hsp hf hcs _ hp
  refine ⟨hrd,hwr,hsp,hcs,hf,?_⟩
  sig_eval [Proof.Gcm.encryptBlocksContract,Proof.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs] at hp ⊢
  exact hp

def argsState (s : State) : State :=
  ((((((s.write .r3 (s.gpr .r29)).write .r4 (s.gpr .r28)).write .r5 (s.gpr .r30+48)).write
    .r6 (s.gpr .r30+16)).write .r7 (s.gpr .r27)).write .r8 (s.gpr .r23 >>> 4)).write .r9 (s.gpr .r31+448)


theorem args_ok (s : State) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs) s (· = argsState s) := by
  apply WP.of_runBlock
  simp only [Impl.AesGcm.PPC64LE.SealFused.blockArgs,Impl.AesGcm.PPC64LE.mov,
    runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    exec_addi (n := .r30) (imm := 48) (by decide) (by decide),
    exec_addi (n := .r30) (imm := 16) (by decide) (by decide),
    exec_addi (n := .r31) (imm := 448) (by decide) (by decide),exec_lsr_d (sh := 4) (by decide),
    RegUpd.gpr_write,reduceCtorEq,ite_false,Option.some.injEq,exists_eq_left']
  rfl


theorem args_env {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    Env V sp (argsState s) := by
  have hk : Keep VG.Proof.AesGcm.PPC64LE.Blocks.coreVolatile s (argsState s) := by
    obtain ⟨_,_,_,hx,hk⟩ := WP.keep VG.Proof.AesGcm.PPC64LE.Blocks.coreVolatile (args_ok s) (by decide +kernel)
    subst hx
    exact hk
  exact he.keep (fun r hr => hk.gpr (by
    have hp : ∀ r ∈ frozen, r ∉ VG.Proof.AesGcm.PPC64LE.Blocks.coreVolatile := by decide
    exact hp r hr)) rfl hk.2.1 hk.2.2


theorem args_count {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    (argsState s).gpr .r8=BitVec.ofNat 64 ((V .r23).toNat/16) := by
  have hx : (argsState s).gpr .r8=s.gpr .r23 >>> 4 := by
    simp only [argsState,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true]
  rw [hx,he.fr .r23 (by decide)]
  calc
    _ = BitVec.ofNat 64 (V .r23).toNat >>> 4 := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
    _ = _ := shr4 (V .r23).isLt


theorem fit_offset (p : Addr) {bound off n : Nat} (hf : p.toNat+bound≤2^64)
    (hb : bound<2^64) (ho : off+n≤bound) : (p+BitVec.ofNat 64 off).toNat+n≤2^64 := by
  rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a := off) (b := 2^64) (by omega)]
  have := Nat.mod_le (p.toNat+off) (2^64)
  omega


theorem args_call_pre {V : Reg → BitVec 64} {sp : Addr} {s : State} {R : Nat}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14) :
    (Proof.Gcm.encryptBlocksContract PPC64LE.abi).pre
      ((argsState s).callEntry.withRegions (blockReads (argsState s)) (blockWrites (argsState s))) := by
  have hnlt : (V .r23).toNat/16<2^64 := by have := (V .r23).isLt; omega
  have h8 : (s.gpr .r23 >>> 4).toNat=(V .r23).toNat/16 := by
    change ((argsState s).gpr .r8).toNat=(V .r23).toNat/16
    rw [args_count he,toNat64 hnlt]
  have hr : (s.gpr .r28).toNat=R := by
    rw [he.fr .r28 (by decide),hR,toNat64 (by rcases hv with h | h | h <;> omega)]
  have hc := hd.take (k := ((V .r23).toNat/16)*16) (by omega)
  sig_eval [Proof.Gcm.encryptBlocksContract,Proof.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs,
    blockReads,blockWrites]
  simp only [he.r29,he.r30,he.r31,he.fr .r27 (by decide),h8,hr]
  refine ⟨?_,?_,hc.ctx,?_,?_,?_,?_,?_,?_,?_,L.cw,?_,?_,hc.ok.fit,?_,?_⟩
  · simpa only [BitVec.add_zero,BitVec.ofNat_eq_ofNat] using L.ctx_st (a := 0) (n := 256) (d := 48) (k := 16) (by decide) (by decide)
  · simpa only [BitVec.add_zero,BitVec.ofNat_eq_ofNat] using L.ctx_st (a := 0) (n := 256) (d := 16) (k := 16) (by decide) (by decide)
  · simpa only [BitVec.add_zero,BitVec.ofNat_eq_ofNat] using L.ctx_w (a := 0) (n := 256) (d := 448) (k := 2112) (by decide) (by decide)
  · exact Lay.st_st (a := 48) (n := 16) (d := 16) (k := 16) (by omega) (by decide) (by decide)
  · exact hc.ok.st.symm.sub_left (Lay.stSub (d := 48) (n := 16) (by decide))
  · exact L.st_w (a := 48) (n := 16) (d := 448) (k := 2112) (by decide) (.inr ⟨by decide,by decide⟩)
  · exact hc.ok.st.symm.sub_left (Lay.stSub (d := 16) (n := 16) (by decide))
  · exact L.st_w (a := 16) (n := 16) (d := 448) (k := 2112) (by decide) (.inr ⟨by decide,by decide⟩)
  · exact hc.ok.w.sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))
  · exact fit_offset _ L.sw (by decide) (off := 48) (n := 16) (by decide)
  · exact fit_offset _ L.sw (by decide) (off := 16) (n := 16) (by decide)
  · exact fit_offset _ L.ww (by decide) (off := 448) (n := 2112) (by decide)
  · exact hv


theorem args_regions {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    blockReads (argsState s)=[⟨V .r29,256⟩] ∧
    blockWrites (argsState s)=[⟨V .r30+48,16⟩,⟨V .r30+16,16⟩,
      ⟨V .r27,((V .r23).toNat/16)*16⟩,⟨V .r31+448,2112⟩] := by
  constructor
  · simp only [blockReads,argsState,RegUpd.gpr_write,reduceCtorEq,ite_false,ite_true,he.r29]
  · have hnlt : (V .r23).toNat/16<2^64 := by have := (V .r23).isLt; omega
    have hc : (s.gpr .r23 >>> 4).toNat=(V .r23).toNat/16 := by
      change ((argsState s).gpr .r8).toNat=(V .r23).toNat/16
      rw [args_count he,toNat64 hnlt]
    simp only [blockWrites,argsState,RegUpd.gpr_write,reduceCtorEq,
      ite_false,ite_true,he.r30,he.r31,he.fr .r27 (by decide),hc]


theorem args_call {V : Reg → BitVec 64} {sp : Addr} {s : State} {R : Nat}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14) : BlockCall (argsState s) := by
  have hr := args_regions he
  have hw : Covers (blockWrites (argsState s)) (argsState s).wr := by
    rw [hr.2]
    have hc := hd.take (k := ((V .r23).toNat/16)*16) (by omega)
    exact Covers.cons (he.perm.stC (d := 48) (n := 16) (by decide))
      (Covers.cons (he.perm.stC (d := 16) (n := 16) (by decide))
        (Covers.cons hc.wr (he.perm.wC (d := 448) (n := 2112) (by decide))))
  refine ⟨args_call_pre L he hd hR hv,?_,hw⟩
  apply Covers.append_left
  · rw [hr.1]
    exact he.perm.ctx
  · exact Covers.right hw


/-- The fused call preserves the one-shot environment and returns the three
whole-block results in the caller's state and data buffers. -/
structure WholeOutWith (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (m : Mem)
    (plaintext : List Spec.Gcm.Block) (t : State) : Prop where
  env : Env V sp t
  data : Spec.Gcm.blocksAt t.mem (V .r27) ((V .r23).toNat/16) =
    Spec.Gcm.ctr32 (Spec.Gcm.ctxCiph m (V .r29) R) (Spec.Gcm.blockAt m (V .r30+48))
      plaintext
  counter : Spec.Gcm.blockAt t.mem (V .r30+48) =
    Nat.repeat Spec.Gcm.inc32 ((V .r23).toNat/16) (Spec.Gcm.blockAt m (V .r30+48))
  hash : Spec.Gcm.blockAt t.mem (V .r30+16) =
    Spec.Gcm.ghashFrom (Spec.Gcm.ctxH m (V .r29)) (Spec.Gcm.blockAt m (V .r30+16))
      (Spec.Gcm.blocksAt t.mem (V .r27) ((V .r23).toNat/16))
  frame : Frame [⟨V .r30+48,16⟩,⟨V .r30+16,16⟩,
    ⟨V .r27,((V .r23).toNat/16)*16⟩,⟨V .r31+448,2112⟩] m t.mem

abbrev WholeOut (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (m : Mem) (t : State) :=
  WholeOutWith V sp R m (Spec.Gcm.blocksAt m (V .r27) ((V .r23).toNat/16)) t


theorem whole_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → BitVec 64} {sp : Addr} {s : State} {R : Nat}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14) :
    WP isa (.seq (.block Impl.AesGcm.PPC64LE.SealFused.blockArgs)
      (.call "vg_aes_gcm_encrypt_blocks" Impl.AesGcm.PPC64LE.Blocks.encrypt)) s
      (WholeOut V sp R s.mem) := by
  refine WP.seq (WP.mono (args_ok s) fun a ha => ?_)
  subst a
  refine WP.mono (block_call (args_call L he hd hR hv)) fun t ht => ?_
  have hm : (argsState s).mem=s.mem := by simp only [argsState,RegUpd.mem_write]
  have h8 : (s.gpr .r23 >>> 4).toNat=(V .r23).toNat/16 := by
    change ((argsState s).gpr .r8).toNat=(V .r23).toNat/16
    rw [args_count he,toNat64 (by have := (V .r23).isLt; omega)]
  have hr : (s.gpr .r28).toNat=R := by
    rw [he.fr .r28 (by decide),hR,toNat64 (by rcases hv with h | h | h <;> omega)]
  have hp := ht.out
  sig_eval [Proof.Gcm.encryptBlocksContract,Proof.Gcm.cryptBlocksSig,PPC64LE.abi,PPC64LE.argRegs] at hp
  simp only [he.r29,he.r30,he.fr .r27 (by decide),hr,h8] at hp
  refine ⟨(args_env he).of_saved ht.saved ht.sp ht.rd ht.wr,hp.1,hp.2.1,?_,?_⟩
  · rw [hp.1]; exact hp.2.2
  · have hf := ht.frame
    rw [(args_regions he).2,hm] at hf
    exact hf

/-- The helper's block contract establishes the byte-stream invariant used
by the existing final partial-block proof. -/
theorem WholeOut.ctr {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {m : Mem} {t : State}
    (h : WholeOut V sp R m t) {icb : Spec.Gcm.Block}
    (hc : Proof.Gcm.Ctr m (V .r30+48) (V .r30+64) (Spec.Gcm.ctxCiph m (V .r29) R) icb 0) :
    Spec.Aes.bytesAt t.mem (V .r27) (16*((V .r23).toNat/16)) =
      Proof.Gcm.xorKs (Spec.Gcm.ctxCiph m (V .r29) R) icb 0
        (Spec.Aes.bytesAt m (V .r27) (16*((V .r23).toNat/16))) ∧
    Proof.Gcm.Ctr t.mem (V .r30+48) (V .r30+64) (Spec.Gcm.ctxCiph m (V .r29) R) icb
      (16*((V .r23).toNat/16)) := by
  simpa only [Nat.zero_add] using Proof.Gcm.ctr_whole hc (by decide) h.data h.counter

/-- Whole ciphertext blocks extend the padded AAD's GHASH state without
re-reading the ciphertext through the separate absorber. -/
theorem WholeOutWith.absorbed {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {m : Mem} {t : State} {plaintext : List Spec.Gcm.Block}
    (h : WholeOutWith V sp R m plaintext t) {x : List Byte}
    (hx : Proof.Gcm.Absorbed m (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH m (V .r29)) x)
    (hx0 : x.length%16=0) :
    Proof.Gcm.Absorbed t.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH m (V .r29))
      (x++Spec.Aes.bytesAt t.mem (V .r27) (16*((V .r23).toNat/16))) := by
  apply Proof.Gcm.absorb_whole hx hx0
  · rw [length_bytesAt]; omega
  · rw [h.hash,Proof.Gcm.blocksAt_eq]

theorem tailSetup_ok {V : Reg → BitVec 64} {sp : Addr} {s : State} (he : Env V sp s) :
    WP isa (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) s fun t =>
      t.gpr .r24=V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16)) ∧
      t.gpr .r25=BitVec.ofNat 64 ((V .r23).toNat%16) ∧
      t.gpr .r26=0 ∧
      (∀ r, r≠.r0 → r≠.r12 → r≠.r24 → r≠.r25 → r≠.r26 → t.gpr r=s.gpr r) ∧
      Keeps s t := by
  have h23 := he.fr .r23 (by decide)
  have h27 := he.fr .r27 (by decide)
  have hand := and15 (V .r23)
  have hsub : V .r23-BitVec.ofNat 64 ((V .r23).toNat%16)=
      BitVec.ofNat 64 (16*((V .r23).toNat/16)) := by
    calc
      _ = BitVec.ofNat 64 (V .r23).toNat-BitVec.ofNat 64 ((V .r23).toNat%16) := by
        rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
      _ = _ := by rw [ofNat_sub64 (Nat.mod_le _ _) (V .r23).isLt]; congr 1; omega
  simp only [Impl.AesGcm.PPC64LE.SealFused.tailSetup]
  crun [h23,h27,hand,hsub]
  exact ⟨fun r a b c d e => by simp [a,b,c,d,e],⟨rfl,rfl,rfl,rfl,rfl⟩⟩

/-- A suffix may be empty when the text ends on a block boundary. -/
theorem data_suffix {c st w : Addr} {s : State} {D : Addr} {n j : Nat}
    (h : DataW c st w s D n) (hj : j≤n) : DataW c st w s (D+BitVec.ofNat 64 j) (n-j) := by
  have hs : Region.Sub ⟨D+BitVec.ofNat 64 j,n-j⟩ ⟨D,n⟩ := Offset.sub_base _ (by omega)
  refine ⟨⟨covers_off h.ok.rd (by omega) h.ok.lt,by have := h.ok.lt; omega,?_,
    h.ok.st.sub_left hs,h.ok.w.sub_left hs⟩,covers_off h.wr (by omega) h.ok.lt,h.ctx.sub_right hs⟩
  by_cases hz : n-j=0
  · rw [hz,Nat.add_zero]; exact Nat.le_of_lt (D+BitVec.ofNat 64 j).isLt
  · rw [h.ok.toNat_add (by omega)]; have := h.ok.fit; omega

theorem WholeOutWith.rest {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {s t : State} {plaintext : List Spec.Gcm.Block}
    (h : WholeOutWith V sp R s.mem plaintext t)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    Spec.Aes.bytesAt t.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16)))
      ((V .r23).toNat%16) =
    Spec.Aes.bytesAt s.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16)))
      ((V .r23).toNat%16) := by
  have hj : 16*((V .r23).toNat/16)≤(V .r23).toNat := by omega
  have hs := data_suffix hd hj
  have hn : (V .r23).toNat-16*((V .r23).toNat/16)=(V .r23).toNat%16 := by omega
  rw [hn] at hs
  apply bytesAt_frame h.frame _ (by omega)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hs.ok.st.sub_right (Lay.stSub (d := 48) (n := 16) (by decide))
  · exact hs.ok.st.sub_right (Lay.stSub (d := 16) (n := 16) (by decide))
  · have hsplit := (split_disj (D := V .r27) hj hd.ok.lt).symm
    rw [hn] at hsplit
    simpa only [Nat.mul_comm] using hsplit
  · exact hs.ok.w.sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))

/-- Finish only the partial block after the fused whole-block pass. -/
theorem tail_ok {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {s : State} {icb : Spec.Gcm.Block}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14) :
    WP isa (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup) Impl.AesGcm.PPC64LE.cryptTail) s
      fun t => CrOut V sp R icb (16*((V .r23).toNat/16))
        (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16) s.mem t ∧
        t.gpr .r24=V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16)) ∧
        t.gpr .r25=BitVec.ofNat 64 ((V .r23).toNat%16) ∧ t.gpr .r26=0 := by
  refine WP.seq (WP.mono (tailSetup_ok he) fun t ⟨h24,h25,h26,hg,hk⟩ => ?_)
  have het : Env V sp t := he.keep (fun r hr => hg r (by revert r; decide)
    (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide))
    hk.sp hk.rd hk.wr
  have hd' := data_suffix hd (j := 16*((V .r23).toNat/16)) (by omega)
  have hn : (V .r23).toNat-16*((V .r23).toNat/16)=(V .r23).toNat%16 := by omega
  rw [hn] at hd'
  have mid : CrMid V sp R icb (16*((V .r23).toNat/16))
      (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16) s.mem 0 t := by
    refine ⟨het,by omega,?_,?_,hR,hv,hd'.of_eq hk.rd hk.wr,?_,?_,?_,.inr (by omega),?_⟩
    · simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h24
    · simpa only [Nat.sub_zero] using h25
    · intro hc; rw [hk.mem,Nat.add_zero]; exact hc
    · intro _; simp only [Spec.Aes.bytesAt,List.range_zero,List.map_nil,Proof.Gcm.xorKs_nil]
    · rw [hk.mem]
    · rw [hk.mem]; exact Frame.refl _ _
  refine WP.ite (decide ((V .r23).toNat%16=0))
    (by simpa only [Nat.sub_zero] using eval_zero mid.r25 (by omega)) (fun hz => ?_) (fun hz => ?_)
  · have hz' : (V .r23).toNat%16=0 := by simpa using hz
    have ho : CrOut V sp R icb (16*((V .r23).toNat/16))
        (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16) s.mem t := by
      refine ⟨het,?_,?_,mid.frame⟩
      · intro hh; simpa only [hz',Nat.add_zero] using mid.ctr hh
      · intro _; simp only [hz',Spec.Aes.bytesAt,List.range_zero,List.map_nil,Proof.Gcm.xorKs_nil]
    exact WP.block_nil ⟨ho,h24,h25,h26⟩
  · have hz' : (V .r23).toNat%16-0≠0 := by simpa using hz
    refine WP.seq (WP.mono (tailKs_ok L mid (by rw [hk.mem])) fun v hv => ?_)
    have hx := tailXor_ok hv (by omega) hz'
    have hx24 := WP.gpr hx (r := .r24) (by decide +kernel)
    have hx25 := WP.gpr hx24 (r := .r25) (by decide +kernel)
    have hx26 := WP.gpr hx25 (r := .r26) (by decide +kernel)
    refine WP.mono hx26 fun u ⟨⟨⟨ho,h24'⟩,h25'⟩,h26'⟩ => ?_
    refine ⟨ho,?_,?_,?_⟩
    · rw [h24',hv.r24,BitVec.add_zero]
    · simpa only [Nat.sub_zero] using h25'.trans hv.r25
    · rw [h26',hv.r26,h26]

theorem tail_prefix {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {s t u : State}
    {icb : Spec.Gcm.Block}
    (ht : CrOut V sp R icb (16*((V .r23).toNat/16))
      (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16) t.mem u)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    Spec.Aes.bytesAt u.mem (V .r27) (16*((V .r23).toNat/16)) =
      Spec.Aes.bytesAt t.mem (V .r27) (16*((V .r23).toNat/16)) := by
  have hj : 16*((V .r23).toNat/16)≤(V .r23).toNat := by omega
  have hn : (V .r23).toNat-16*((V .r23).toNat/16)=(V .r23).toNat%16 := by omega
  apply bytesAt_frame ht.frame _ (by have := hd.ok.lt; omega)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have hsplit := split_disj (D := V .r27) hj hd.ok.lt
    rw [hn] at hsplit
    exact hsplit
  · exact (hd.take hj).ok.st.sub_right (Lay.stSub (d := 48) (n := 32) (by decide))
  · exact (hd.take hj).ok.w.sub_right (Lay.wSub (d := 512) (n := 2048) (by decide))

theorem whole_tail_ciphertext {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {s t u : State}
    {icb : Spec.Gcm.Block} (hw : WholeOut V sp R s.mem t)
    (ht : CrOut V sp R icb (16*((V .r23).toNat/16))
      (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16) t.mem u)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hc : ciphOf t.mem (V .r29) R=Spec.Gcm.ctxCiph s.mem (V .r29) R)
    (hctr : Proof.Gcm.Ctr s.mem (V .r30+48) (V .r30+64)
      (Spec.Gcm.ctxCiph s.mem (V .r29) R) icb 0) :
    Spec.Aes.bytesAt u.mem (V .r27) (V .r23).toNat =
      Spec.Gcm.gctr (Spec.Gcm.ctxCiph s.mem (V .r29) R) icb
        (Spec.Aes.bytesAt s.mem (V .r27) (V .r23).toNat) := by
  obtain ⟨hp,hc₁⟩ := hw.ctr hctr
  have hc₂ : Proof.Gcm.Ctr t.mem (V .r30+48) (V .r30+64) (ciphOf t.mem (V .r29) R) icb
      (16*((V .r23).toNat/16)) := by rw [hc]; exact hc₁
  have htail := ht.out hc₂
  rw [hc,hw.rest hd] at htail
  have hprefix := tail_prefix ht hd
  have hp' := hprefix.trans hp
  have hall := done_append (m₀ := s.mem) (P := 0) hp' (by simpa only [Nat.zero_add] using htail)
  have he : 16*((V .r23).toNat/16)+(V .r23).toNat%16=(V .r23).toNat := by omega
  rw [he,← Proof.Gcm.gctr_eq] at hall
  exact hall

theorem whole_ctx_disjoint {V : Reg → BitVec 64} {s : State}
    (L : Lay (V .r29) (V .r30) (V .r31))
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    ∀ r ∈ [⟨V .r30+48,16⟩,⟨V .r30+16,16⟩,
      ⟨V .r27,((V .r23).toNat/16)*16⟩,⟨V .r31+448,2112⟩],
      (⟨V .r29,256⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.cs.sub_right (Lay.stSub (d := 48) (n := 16) (by decide))
  · exact L.cs.sub_right (Lay.stSub (d := 16) (n := 16) (by decide))
  · exact hd.ctx.sub_right (Region.sub_prefix (by omega))
  · exact L.cw'.sub_right (Lay.wSub (d := 448) (n := 2112) (by decide))

theorem WholeOutWith.cipher {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {s t : State} {plaintext : List Spec.Gcm.Block}
    (h : WholeOutWith V sp R s.mem plaintext t) (L : Lay (V .r29) (V .r30) (V .r31))
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hv : R=10 ∨ R=12 ∨ R=14) :
    ciphOf t.mem (V .r29) R=Spec.Gcm.ctxCiph s.mem (V .r29) R :=
  ciph_keep h.frame (whole_ctx_disjoint L hd) hv

theorem WholeOutWith.hashKey {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {s t : State} {plaintext : List Spec.Gcm.Block}
    (h : WholeOutWith V sp R s.mem plaintext t) (L : Lay (V .r29) (V .r30) (V .r31))
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    Spec.Gcm.blockAt t.mem (V .r29+240)=Spec.Gcm.ctxH s.mem (V .r29) :=
  ctxH_keep h.frame (whole_ctx_disjoint L hd)

theorem WholeOutWith.j0 {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {s t : State} {plaintext : List Spec.Gcm.Block}
    (h : WholeOutWith V sp R s.mem plaintext t) (L : Lay (V .r29) (V .r30) (V .r31))
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    Spec.Gcm.blockAt t.mem (V .r30)=Spec.Gcm.blockAt s.mem (V .r30) := by
  apply blockAt_frame h.frame
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa only [BitVec.add_zero,BitVec.ofNat_eq_ofNat] using Lay.st_st (st := V .r30) (a := 0) (n := 16)
      (d := 48) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · simpa only [BitVec.add_zero,BitVec.ofNat_eq_ofNat] using Lay.st_st (st := V .r30) (a := 0) (n := 16)
      (d := 16) (k := 16) (.inl (by decide)) (by decide) (by decide)
  · exact (hd.ok.st.sub_right (Region.sub_prefix (by decide))).symm.sub_right (Region.sub_prefix (by omega))
  · simpa only [BitVec.add_zero,BitVec.ofNat_eq_ofNat] using L.st_w (a := 0) (n := 16) (d := 448) (k := 2112)
      (by decide) (.inr ⟨by decide,by decide⟩)

def bodyFrame (V : Reg → BitVec 64) : List Region :=
  [⟨V .r27,(V .r23).toNat⟩,⟨V .r30,80⟩,⟨V .r31,16⟩,
    ⟨V .r31+96,16⟩,⟨V .r31+448,2112⟩]

theorem whole_body_sub (V : Reg → BitVec 64) :
    ∀ r ∈ [⟨V .r30+48,16⟩,⟨V .r30+16,16⟩,
      ⟨V .r27,((V .r23).toNat/16)*16⟩,⟨V .r31+448,2112⟩],
      ∃ r' ∈ bodyFrame V, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_,by simp [bodyFrame],Lay.stSub (by decide)⟩
  · exact ⟨_,by simp [bodyFrame],Lay.stSub (by decide)⟩
  · exact ⟨⟨V .r27,(V .r23).toNat⟩,by simp [bodyFrame],Region.sub_prefix (by omega)⟩
  · exact ⟨_,by simp [bodyFrame],fun _ h => h⟩

theorem cr_body_sub (V : Reg → BitVec 64) {j k : Nat} (hk : j+k≤(V .r23).toNat) :
    ∀ r ∈ crFrame (V .r30) (V .r31) (V .r27+BitVec.ofNat 64 j) k,
      ∃ r' ∈ bodyFrame V, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_,by simp [bodyFrame],Offset.sub_base _ hk⟩
  · exact ⟨_,by simp [bodyFrame],Lay.stSub (by decide)⟩
  · exact ⟨⟨V .r31+448,2112⟩,by simp [bodyFrame],Offset.sub _ (by decide) (by decide)⟩

theorem abs_body_sub (V : Reg → BitVec 64) :
    ∀ r ∈ absFrame (V .r30) (V .r31) 16,
      ∃ r' ∈ bodyFrame V, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_,by simp [bodyFrame],Lay.stSub (by decide)⟩
  · exact ⟨_,by simp [bodyFrame],Lay.stSub (by decide)⟩
  · exact ⟨⟨V .r31+448,2112⟩,by simp [bodyFrame],Offset.sub _ (by decide) (by decide)⟩

theorem tag_body_sub (V : Reg → BitVec 64) :
    ∀ r ∈ tagFrame (V .r30) (V .r31) 0,
      ∃ r' ∈ bodyFrame V, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨V .r30,80⟩,by simp [bodyFrame],Region.sub_prefix (by decide)⟩
  · exact ⟨_,by simp [bodyFrame],fun _ h => h⟩
  · exact ⟨⟨V .r31,16⟩,by simp [bodyFrame],by rw [BitVec.add_zero]; exact fun _ h => h⟩
  · exact ⟨⟨V .r31+448,2112⟩,by simp [bodyFrame],Offset.sub _ (by decide) (by decide)⟩

structure BodyOutWith (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (H : Spec.Gcm.Block)
    (a : List Byte) (m : Mem) (plaintext : List Byte) (t : State) (extra : List Region := []) : Prop where
  env : Env V sp t
  ciphertext : Spec.Aes.bytesAt t.mem (V .r27) (V .r23).toNat =
    Spec.Gcm.gctr (Spec.Gcm.ctxCiph m (V .r29) R) (Spec.Gcm.blockAt m (V .r30+48))
      plaintext
  tag : Spec.Aes.bytesAt t.mem (V .r31) 16 =
    Spec.Gcm.toBytes (Spec.Gcm.ghashFrom H
      (Spec.Gcm.ghash H (Spec.Gcm.blocks (Proof.Gcm.padded a
        (Spec.Aes.bytesAt t.mem (V .r27) (V .r23).toNat))))
      [Spec.Gcm.ofBytes (Proof.Gcm.lensBlock a.length (V .r23).toNat)] ^^^
      Spec.Gcm.ctxCiph m (V .r29) R (Spec.Gcm.blockAt m (V .r30)))
  frame : Frame (bodyFrame V++extra) m t.mem


theorem BodyOutWith.rebase {V : Reg → BitVec 64} {sp : Addr} {R : Nat} {H : Spec.Gcm.Block}
    {a p : List Byte} {m m₀ : Mem} {t : State} {extra : List Region}
    (h : BodyOutWith V sp R H a m p t extra) (hf : Frame (bodyFrame V++extra) m₀ m)
    (hc : Spec.Gcm.ctxCiph m (V .r29) R=Spec.Gcm.ctxCiph m₀ (V .r29) R)
    (hb : Spec.Gcm.blockAt m (V .r30+48)=Spec.Gcm.blockAt m₀ (V .r30+48))
    (hj : Spec.Gcm.blockAt m (V .r30)=Spec.Gcm.blockAt m₀ (V .r30)) :
    BodyOutWith V sp R H a m₀ p t extra := by
  refine ⟨h.env,?_,?_,hf.trans h.frame⟩
  · rw [h.ciphertext,hc,hb]
  · rw [h.tag,hc,hj]


abbrev BodyOut (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (H : Spec.Gcm.Block)
    (a : List Byte) (m : Mem) (t : State) :=
  BodyOutWith V sp R H a m (Spec.Aes.bytesAt m (V .r27) (V .r23).toNat) t


theorem data_tag_disjoint {V : Reg → BitVec 64} {s : State} {D : Addr} {n : Nat}
    (hd : DataOk (V .r30) (V .r31) s D n) :
    ∀ r ∈ tagFrame (V .r30) (V .r31) 0, (⟨D,n⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hd.st.sub_right (Region.sub_prefix (by decide))
  · exact hd.w.sub_right (Lay.wSub (by decide))
  · simpa only [BitVec.add_zero] using hd.w.sub_right (Region.sub_prefix (by decide : 16≤2560))
  · exact hd.w.sub_right (Lay.wSub (by decide))

structure WholeDone (V : Reg → BitVec 64) (sp : Addr) (R : Nat) (a : List Byte)
    (m : Mem) (pWhole pTail : List Byte) (t : State) (extra : List Region := []) : Prop where
  env : Env V sp t
  wholeLen : pWhole.length=16*((V .r23).toNat/16)
  wholeCiphertext : Spec.Aes.bytesAt t.mem (V .r27) (16*((V .r23).toNat/16))=
    Proof.Gcm.xorKs (Spec.Gcm.ctxCiph m (V .r29) R) (Spec.Gcm.blockAt m (V .r30+48)) 0 pWhole
  ctr : Proof.Gcm.Ctr t.mem (V .r30+48) (V .r30+64)
    (Spec.Gcm.ctxCiph m (V .r29) R) (Spec.Gcm.blockAt m (V .r30+48)) (16*((V .r23).toNat/16))
  abs : Proof.Gcm.Absorbed t.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH m (V .r29))
    ((a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))++
      Spec.Aes.bytesAt t.mem (V .r27) (16*((V .r23).toNat/16)))
  cipher : ciphOf t.mem (V .r29) R=Spec.Gcm.ctxCiph m (V .r29) R
  hashKey : Spec.Gcm.blockAt t.mem (V .r29+240)=Spec.Gcm.ctxH m (V .r29)
  j0 : Spec.Gcm.blockAt t.mem (V .r30)=Spec.Gcm.blockAt m (V .r30)
  pending : Spec.Aes.bytesAt t.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16)=pTail
  frame : Frame (bodyFrame V++extra) m t.mem


theorem finishWhole_ok [VG.Proof.Gcm.PPC64LE.GhashLaw]
    {V : Reg → BitVec 64} {sp : Addr} {t : State} {R : Nat} {a pWhole pTail : List Byte} {m : Mem} {extra : List Region}
    (L : Lay (V .r29) (V .r30) (V .r31)) (mid : WholeDone V sp R a m pWhole pTail t extra)
    (hd : DataW (V .r29) (V .r30) (V .r31) t (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14)
    (ha : (V .r22).toNat=a.length) (hbig : 0<(V .r23).toNat) :
    WP isa (.seq (.seq (.block Impl.AesGcm.PPC64LE.SealFused.tailSetup)
      Impl.AesGcm.PPC64LE.cryptTail) (.seq (Impl.AesGcm.PPC64LE.absorb 16) (Impl.AesGcm.PPC64LE.finTag 0))) t
      (fun z => BodyOutWith V sp R (Spec.Gcm.ctxH m (V .r29)) a m (pWhole++pTail) z extra) := by
  have hj : 16*((V .r23).toNat/16)≤(V .r23).toNat := by omega
  have hnrem : (V .r23).toNat-16*((V .r23).toNat/16)=(V .r23).toNat%16 := by omega
  have hxpad : (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length)).length%16=0 := by
    rw [List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  have hdt := hd
  have hds := data_suffix hdt hj
  rw [hnrem] at hds
  have hcw := mid.cipher
  refine WP.seq (WP.mono (WP.with_rdwr (tail_ok (icb := Spec.Gcm.blockAt m (V .r30+48))
    L mid.env hdt hR hv)) fun u ⟨⟨ht,h24,h25,h26⟩,rdu,wru,_⟩ => ?_)
  have hHu : Spec.Gcm.blockAt u.mem (V .r29+BitVec.ofNat 64 240)=Spec.Gcm.ctxH m (V .r29) := by
    rw [blockAt_frame ht.frame (fun r hr => (ctx_crFrame L hds r hr).sub_left
      (Lay.ctxSub (d := 240) (n := 16) (by decide)))]
    exact mid.hashKey
  let x := (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))++
    Spec.Aes.bytesAt t.mem (V .r27) (16*((V .r23).toNat/16))
  have hx0 : x.length%16=0 := by
    simp only [x,List.length_append,length_bytesAt] at hxpad ⊢; omega
  have habu : Proof.Gcm.Absorbed u.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH m (V .r29)) x := by
    apply mid.abs.congr
    · exact blockAt_frame ht.frame (stp_crFrame L hds (by decide))
    · change Spec.Aes.bytesAt u.mem (V .r30+32) (x.length%16)=
        Spec.Aes.bytesAt t.mem (V .r30+32) (x.length%16)
      simp only [hx0,Spec.Aes.bytesAt,List.range_zero,List.map_nil]
  have hctr : Proof.Gcm.Ctr t.mem (V .r30+48) (V .r30+64) (ciphOf t.mem (V .r29) R)
      (Spec.Gcm.blockAt m (V .r30+48)) (16*((V .r23).toNat/16)) := by
    rw [hcw]; exact mid.ctr
  have htail := ht.out hctr
  rw [hcw,mid.pending] at htail
  have hprefix := (tail_prefix ht hd).trans mid.wholeCiphertext
  have hciph : Spec.Aes.bytesAt u.mem (V .r27) (V .r23).toNat=
      Spec.Gcm.gctr (Spec.Gcm.ctxCiph m (V .r29) R) (Spec.Gcm.blockAt m (V .r30+48)) (pWhole++pTail) := by
    rw [show (V .r23).toNat=16*((V .r23).toNat/16)+(V .r23).toNat%16 by omega,bytesAt_add,hprefix,htail,
      Proof.Gcm.gctr_eq,Proof.Gcm.xorKs_append,mid.wholeLen,Nat.zero_add]
  have ai : AbsIn V sp 16 (Spec.Gcm.ctxH m (V .r29)) x
      (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16) u :=
    ⟨ht.env,h24,h25,by rw [hx0]; exact h26,hds.ok.of_eq rdu wru,hHu⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun v ⟨ab,rdv,wrv,_⟩ => ?_)
  have hcv : Spec.Aes.bytesAt v.mem (V .r27) (V .r23).toNat =
      Spec.Aes.bytesAt u.mem (V .r27) (V .r23).toNat :=
    bytesAt_frame ab.frame (data_absFrame (.inr rfl) hd.ok) (by have := hd.ok.lt; omega)
  have habv := ab.abs habu
  have hxfull : x++Spec.Aes.bytesAt u.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16)))
      ((V .r23).toNat%16)=Spec.Gcm.ghashInput a (Spec.Aes.bytesAt v.mem (V .r27) (V .r23).toNat) := by
    have hne : Spec.Aes.bytesAt v.mem (V .r27) (V .r23).toNat≠[] := by
      intro hz; have hh := congrArg List.length hz; rw [length_bytesAt,List.length_nil] at hh; omega
    rw [Proof.Gcm.ghashInput_of_ne hne,hcv]
    simp only [x,List.append_assoc]
    rw [← tail_prefix ht hd,← bytesAt_add]
    rw [show 16*((V .r23).toNat/16)+(V .r23).toNat%16=(V .r23).toNat by omega]
  rw [hxfull] at habv
  have hHv : Spec.Gcm.blockAt v.mem (V .r29+BitVec.ofNat 64 240)=Spec.Gcm.ctxH m (V .r29) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hHu
  refine WP.mono (finTag_ok L (o := 0) (.inl rfl) (a := a)
    (ct := Spec.Aes.bytesAt v.mem (V .r27) (V .r23).toNat) ab.env hR hv hHv
    (by rw [ha]) (length_bytesAt _ _ _).symm) fun z fg => ?_
  have hcz : Spec.Aes.bytesAt z.mem (V .r27) (V .r23).toNat =
      Spec.Aes.bytesAt v.mem (V .r27) (V .r23).toNat :=
    bytesAt_frame fg.frame (data_tag_disjoint hd.ok) (by have := hd.ok.lt; omega)
  refine ⟨fg.env,by rw [hcz,hcv]; exact hciph,?_,?_⟩
  · have hf := fg.out habv
    rw [BitVec.add_zero,length_bytesAt,ha] at hf
    rw [hcz]
    rw [hf]
    rw [ciph_frame (abs_taFrame ab.frame) (ctx_taFrame L) hv,
      ciph_frame ht.frame (ctx_crFrame L hds) hv,hcw,
      blockAt_frame (abs_taFrame ab.frame) (by
        simpa only [BitVec.add_zero] using stp_taFrame L (d := 0) (k := 16) (.inl (by decide))),
      blockAt_frame ht.frame (by simpa only [BitVec.add_zero] using
        (stp_crFrame L hds (d := 0) (k := 16) (by decide))),mid.j0]
  · exact mid.frame.trans (((ht.frame.sub (cr_body_sub V (by omega))).trans
      ((ab.frame.sub (abs_body_sub V)).trans (fg.frame.sub (tag_body_sub V)))).mono (fun _ hr => List.mem_append_left _ hr))

theorem fastBody_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → BitVec 64} {sp : Addr} {s : State} {R : Nat} {a : List Byte}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14)
    (ha : (V .r22).toNat=a.length) (hn : 0<(V .r23).toNat)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WP isa Impl.AesGcm.PPC64LE.SealFused.fastBody s
      (BodyOut V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a s.mem) := by
  have hxpad : (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length)).length%16=0 := by
    rw [List.length_append,Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  refine WP.seq (WP.mono (WP.with_rdwr (whole_ok L he hd hR hv)) fun t ⟨hw,rdt,wrt,_⟩ => ?_)
  have hctr := hw.ctr (Proof.Gcm.ctr_zero s.mem _ _ _ rfl)
  have mid : WholeDone V sp R a s.mem
      (Spec.Aes.bytesAt s.mem (V .r27) (16*((V .r23).toNat/16)))
      (Spec.Aes.bytesAt s.mem (V .r27+BitVec.ofNat 64 (16*((V .r23).toNat/16))) ((V .r23).toNat%16)) t := by
    refine ⟨hw.env,length_bytesAt _ _ _,hctr.1,?_,hw.absorbed hab hxpad,hw.cipher L hd hv,hw.hashKey L hd,
      hw.j0 L hd,?_,hw.frame.sub (whole_body_sub V)⟩
    · simpa only [Nat.zero_add] using hctr.2
    · exact hw.rest hd
  refine WP.mono (finishWhole_ok L mid (hd.of_eq rdt wrt) hR hv ha hn) fun z hz => ?_
  have hp := bytesAt_add s.mem (V .r27) (16*((V .r23).toNat/16)) ((V .r23).toNat%16)
  rw [show 16*((V .r23).toNat/16)+(V .r23).toNat%16=(V .r23).toNat by omega] at hp
  simpa only [← hp] using hz


theorem ot_body_sub (V : Reg → BitVec 64) :
    ∀ r ∈ otFrame (V .r30) (V .r31) 0,
      ∃ r' ∈ bodyFrame V, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨V .r30,80⟩,by simp [bodyFrame],Region.sub_prefix (by decide)⟩
  · exact ⟨_,by simp [bodyFrame],fun _ h => h⟩
  · exact ⟨⟨V .r31,16⟩,by simp [bodyFrame],by rw [BitVec.add_zero]; exact fun _ h => h⟩
  · exact ⟨⟨V .r31+448,2112⟩,by simp [bodyFrame],Offset.sub _ (by decide) (by decide)⟩

theorem smallBody_ok [VG.Proof.Gcm.PPC64LE.GhashLaw]
    {V : Reg → BitVec 64} {sp : Addr} {s : State} {R : Nat} {a : List Byte}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14)
    (ha : (V .r22).toNat=a.length)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WP isa (.seq Impl.AesGcm.PPC64LE.oneCrypt (Impl.AesGcm.PPC64LE.oneTag 0)) s
      (BodyOut V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a s.mem) := by
  refine WP.seq (WP.mono (WP.with_rdwr (oneCrypt_ok L he hR hv hd rfl)) fun t ⟨oc,rdt,wrt,_⟩ => ?_)
  have hH : Spec.Gcm.blockAt t.mem (V .r29+BitVec.ofNat 64 240)=Spec.Gcm.ctxH s.mem (V .r29) := by
    rw [blockAt_frame oc.frame (fun r hr => (ctx_crFrame L hd r hr).sub_left
      (Lay.ctxSub (d := 240) (n := 16) (by decide)))]
    rfl
  have hxlt := Nat.mod_lt (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length)).length (by decide : 0<16)
  have habt := hab.congr (blockAt_frame oc.frame (stp_crFrame L hd (d := 16) (k := 16) (by decide)))
    (bytesAt_frame oc.frame (stp_crFrame L hd (d := 32) (by omega)) (by omega))
  refine WP.mono (oneTag_ok L (o := 0) (.inl rfl) oc.env hR hv hH ha habt
    (hd.ok.of_eq rdt wrt)) fun u ot => ?_
  have hct : Spec.Aes.bytesAt u.mem (V .r27) (V .r23).toNat =
      Spec.Aes.bytesAt t.mem (V .r27) (V .r23).toNat := by
    apply bytesAt_frame ot.frame _ (by have := hd.ok.lt; omega)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hd.ok.st.sub_right (Region.sub_prefix (by decide))
    · exact hd.ok.w.sub_right (Lay.wSub (by decide))
    · simpa only [BitVec.add_zero] using hd.ok.w.sub_right (Region.sub_prefix (by decide : 16≤2560))
    · exact hd.ok.w.sub_right (Lay.wSub (by decide))
  refine ⟨ot.env,?_,?_,?_⟩
  · rw [hct,oc.out]; rfl
  · have ho := ot.out
    rw [BitVec.add_zero,length_bytesAt,ciph_keep oc.frame (ctx_crFrame L hd) hv,
      blockAt_frame oc.frame (by simpa only [BitVec.add_zero] using
        (stp_crFrame L hd (d := 0) (k := 16) (by decide)))] at ho
    rw [hct]; exact ho
  · have hcr : Frame (bodyFrame V) s.mem t.mem := by
      apply oc.frame.sub
      simpa only [BitVec.add_zero] using cr_body_sub V (j := 0) (k := (V .r23).toNat) (by omega)
    exact hcr.trans (ot.frame.sub (ot_body_sub V))

theorem shr9 {n : Nat} (hn : n<2^64) : BitVec.ofNat 64 n >>> 9=BitVec.ofNat 64 (n/512) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow,Nat.mod_eq_of_lt (by omega)]

theorem body_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → BitVec 64} {sp : Addr} {s : State} {R : Nat} {a : List Byte}
    (L : Lay (V .r29) (V .r30) (V .r31)) (he : Env V sp s)
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat)
    (hR : V .r28=BitVec.ofNat 64 R) (hv : R=10 ∨ R=12 ∨ R=14)
    (ha : (V .r22).toNat=a.length)
    (hab : Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length))) :
    WP isa Impl.AesGcm.PPC64LE.SealFused.body s
      (BodyOut V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a s.mem) := by
  have hshift : V .r23 >>> 9=BitVec.ofNat 64 ((V .r23).toNat/512) := by
    calc
      _ = BitVec.ofNat 64 (V .r23).toNat >>> 9 := by rw [BitVec.ofNat_toNat,BitVec.setWidth_eq]
      _ = _ := shr9 (V .r23).isLt
  have hs : WP isa (.block [.lsr .d .r12 .r23 9]) s fun t =>
      t.gpr .r12=BitVec.ofNat 64 ((V .r23).toNat/512) ∧
      (∀ r, r≠.r12 → t.gpr r=s.gpr r) ∧ Keeps s t := by
    crun [he.fr .r23 (by decide),hshift]
    exact ⟨fun r h => by simp [h],⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  refine WP.seq (WP.mono hs fun t ⟨h12,hg,hk⟩ => ?_)
  have het := he.keep (fun r hr => hg r (by revert r; decide)) hk.sp hk.rd hk.wr
  have hdt := hd.of_eq hk.rd hk.wr
  have habt : Proof.Gcm.Absorbed t.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH t.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length)) := by rw [hk.mem]; exact hab
  refine WP.ite (decide ((V .r23).toNat/512=0))
    (eval_zero h12 (by have := (V .r23).isLt; omega)) (fun _ => ?_) (fun hbig => ?_)
  · simpa only [hk.mem] using smallBody_ok L het hdt hR hv ha habt
  · have hbig' : (V .r23).toNat/512≠0 := by simpa using hbig
    simpa only [hk.mem] using fastBody_ok L het hdt hR hv ha (by omega) habt

/-- The interface between the shared one-shot entry/return proof and the
implementation that encrypts and authenticates the text. -/
def BodyCorrect (sealBody : Prog isa) : Prop :=
  ∀ {V : Reg → BitVec 64} {sp : Addr} {s : State} {R : Nat} {a : List Byte},
    Lay (V .r29) (V .r30) (V .r31) → Env V sp s →
    DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat →
    V .r28=BitVec.ofNat 64 R → (R=10 ∨ R=12 ∨ R=14) → (V .r22).toNat=a.length →
    Proof.Gcm.Absorbed s.mem (V .r30+16) (V .r30+32) (Spec.Gcm.ctxH s.mem (V .r29))
      (a++Spec.Gcm.zeros (Spec.Gcm.padLen a.length)) →
    WP isa sealBody s (BodyOut V sp R (Spec.Gcm.ctxH s.mem (V .r29)) a s.mem)

theorem saved_bodyFrame {V : Reg → BitVec 64} {s : State}
    (L : Lay (V .r29) (V .r30) (V .r31))
    (hd : DataW (V .r29) (V .r30) (V .r31) s (V .r27) (V .r23).toNat) :
    ∀ r ∈ bodyFrame V, (savedR (V .r31)).Disjoint r := by
  intro r hr
  simp only [bodyFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact (hd.ok.w.sub_right (Lay.wSub (d := 128) (n := 120) (by decide))).symm
  · simpa only [BitVec.add_zero] using L.saved_st (d := 0) (k := 80) (by decide)
  · simpa only [BitVec.add_zero] using saved_w (w := V .r31) (d := 0) (k := 16)
      (by decide) (.inl (by decide))
  · exact saved_w (by decide) (.inl (by decide))
  · exact saved_w (by decide) (.inr (by decide))

end VG.Proof.AesGcm.PPC64LE.SealFused
