module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Call
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Contract
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.Env
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealFused
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SplitBlocks.Buffers
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Piece
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Ghash1
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Input
import VerifiedGarbage.Proof.AesGcm.PPC64LE.StreamCrypt
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.Mem

/-! # The fused call for a long prefix, with every block coming from the input -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE
open VG.Proof.AesGcm.PPC64LE.SealSplit (Call.Config)
open VG.Proof.AesGcm.PPC64LE.SealSplit.Call (reads writes)
open VG.Spec.Gcm (Block)

structure BulkSpace (sp C S E : Addr) (n : Nat) (s : State) : Prop where
  fit : sp.toNat+1280 ≤ 2^64
  keyFit : C.toNat+256 ≤ 2^64
  srcFit : S.toNat+n ≤ 2^64
  dstFit : E.toNat+n ≤ 2^64
  key : Covers [⟨C,256⟩] (s.rd++s.wr)
  source : Covers [⟨S,n⟩] (s.rd++s.wr)
  dst : Covers [⟨E,n⟩] s.wr
  stack : Covers [⟨sp+32,1248⟩] s.wr
  stackCtx : (⟨sp,1280⟩ : Region).Disjoint ⟨C,256⟩
  stackSrc : (⟨sp,1280⟩ : Region).Disjoint ⟨S,n⟩
  stackDst : (⟨sp,1280⟩ : Region).Disjoint ⟨E,n⟩
  srcDst : (⟨S,n⟩ : Region).Disjoint ⟨E,n⟩
  ctxDst : (⟨C,256⟩ : Region).Disjoint ⟨E,n⟩

theorem frameCovers {sp : Addr} {wr : List Region} (stack : Covers [⟨sp+32,1248⟩] wr)
    {d n : Nat} (lo : 32≤d) (hi : d+n≤1280) : Covers [⟨sp+BitVec.ofNat 64 d,n⟩] wr := by
  have sub := covers_off stack (d := d-32) (n := n) (by omega_using [lo,hi]) (by decide)
  have x : sp+32+BitVec.ofNat 64 (d-32)=sp+BitVec.ofNat 64 d := by
    change sp+BitVec.ofNat 64 32+BitVec.ofNat 64 (d-32)=_
    rw [add_ofNat_assoc,Nat.add_sub_of_le lo]
  rwa [x] at sub

theorem BulkSpace.sub {sp C S E : Addr} {n k : Nat} {s t : State} (h : BulkSpace sp C S E n s)
    (hkn : k≤n) (rd : t.rd=s.rd) (wr : t.wr=s.wr) : BulkSpace sp C S E k t :=
  ⟨h.fit,h.keyFit,by have hf := h.srcFit; omega_using [hf,hkn],by have hf := h.dstFit; omega_using [hf,hkn],
   by rw [rd,wr]; exact h.key,by rw [rd,wr]; exact covers_prefix h.source hkn,by rw [wr]; exact covers_prefix h.dst hkn,
   by rw [wr]; exact h.stack,h.stackCtx,h.stackSrc.sub_right (Region.sub_prefix hkn),
   h.stackDst.sub_right (Region.sub_prefix hkn),(h.srcDst.sub_left (Region.sub_prefix hkn)).sub_right (Region.sub_prefix hkn),
   h.ctxDst.sub_right (Region.sub_prefix hkn)⟩

structure BulkAbi (sp C S E : Addr) (R b : Nat) (s : State) : Prop where
  stack : s.sp=sp
  key : s.gpr .r3=C
  rounds : (s.gpr .r4).toNat=R
  counter : s.gpr .r5=sp+192
  hash : s.gpr .r6=sp+160
  src : s.gpr .r7=S
  readBlocks : (s.gpr .r8).toNat=b
  dst : s.gpr .r9=E
  writeBlocks : (s.gpr .r10).toNat=b
  scratch : s.mem.readW (sp+96) 64=sp+576
  scratchReg : s.gpr .r0=sp+576

theorem bulkConfig {sp C S E : Addr} {R b : Nat} {s : State} (a : BulkAbi sp C S E R b s)
    (h : BulkSpace sp C S E (b*16) s) (rounds : R=10 ∨ R=12 ∨ R=14) :
    SealSplit.Call.Config s := by
  have off : ∀ d n : Nat, d+n≤1280 → Region.Sub ⟨sp+BitVec.ofNat 64 d,n⟩ ⟨sp,1280⟩ :=
    fun d n hn => Offset.sub_base _ hn
  have apart : ∀ d₁ n₁ d₂ n₂ : Nat, d₁+n₁≤1280 → d₂+n₂≤1280 → (d₁+n₁≤d₂ ∨ d₂+n₂≤d₁) →
      (⟨sp+BitVec.ofNat 64 d₁,n₁⟩ : Region).Disjoint ⟨sp+BitVec.ofNat 64 d₂,n₂⟩ :=
    fun _ _ _ _ hl hr hs => Offset.disjoint sp hs (by omega_using [hl]) (by omega_using [hr])
  have cv (d n : Nat) (lo : 32≤d) (hi : d+n≤1280) := frameCovers h.stack lo hi
  have fit : ∀ d n : Nat, d+n ≤ 1280 → (sp+BitVec.ofNat 64 d).toNat+n ≤ 2^64 :=
    fun d n hd => SealFused.fit_offset _ h.fit (by omega_using [hd]) (off := d) (n := n) hd
  have hw : Covers (writes s) s.wr := by
    rw [writes,a.counter,a.hash,a.dst,a.writeBlocks,a.stack,a.scratch]
    exact Covers.cons (cv 192 16 (by decide) (by decide)) (Covers.cons (cv 160 16 (by decide) (by decide)) (Covers.cons h.dst (cv 576 704 (by decide) (by decide))))
  refine ⟨?_,?_,hw⟩
  · sig_eval [Proof.Gcm.encryptBlocksSplitContract,Proof.Gcm.encryptBlocksSplitSig,Proof.Gcm.encryptBlocksSplitPre,
      PPC64LE.abi,PPC64LE.argRegs,stackArg,stackArgAddr,List.getD,List.range,List.range.loop]
    simp only [reads,writes,a.key,a.rounds,a.counter,a.hash,a.src,a.readBlocks,a.dst,a.writeBlocks,a.stack,a.scratch]
    have slot : s.mem.readW (sp+96#64) 64 = sp+576 := a.scratch
    rw [slot]
    refine ⟨by have hf := h.fit; omega_using [hf],rfl,rfl,?_,?_,h.ctxDst,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.srcDst,?_,?_,?_,?_,
       h.keyFit,fit 192 16 (by decide),fit 160 16 (by decide),h.srcFit,h.dstFit,fit 576 704 (by decide),rounds,Nat.le_refl _⟩
    · exact h.stackCtx.symm.sub_right (off 192 16 (by decide))
    · exact h.stackCtx.symm.sub_right (off 160 16 (by decide))
    · exact h.stackCtx.symm.sub_right (off 576 704 (by decide))
    · exact apart 192 16 160 16 (by decide) (by decide) (by decide)
    · exact h.stackSrc.sub_left (off 192 16 (by decide))
    · exact h.stackDst.sub_left (off 192 16 (by decide))
    · exact apart 192 16 576 704 (by decide) (by decide) (by decide)
    · exact apart 192 16 96 8 (by decide) (by decide) (by decide)
    · exact h.stackSrc.sub_left (off 160 16 (by decide))
    · exact h.stackDst.sub_left (off 160 16 (by decide))
    · exact apart 160 16 576 704 (by decide) (by decide) (by decide)
    · exact apart 160 16 96 8 (by decide) (by decide) (by decide)
    · exact h.stackSrc.symm.sub_right (off 576 704 (by decide))
    · exact h.stackDst.symm.sub_right (off 576 704 (by decide))
    · exact h.stackDst.symm.sub_right (off 96 8 (by decide))
    · exact apart 576 704 96 8 (by decide) (by decide) (by decide)
  · apply Covers.append_left _ (Covers.right hw)
    rw [reads,a.key,a.src,a.readBlocks,a.stack]
    exact Covers.cons h.key (Covers.cons h.source (covers_left (cv 96 8 (by decide) (by decide))))

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Cursors and scratch slots for the fused prefix -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.DirectGather (takeBulk bulkRegs)

theorem shrNat {n : Nat} (sh : Nat) (h : n<2^64) :
    BitVec.ofNat 64 n >>> sh = BitVec.ofNat 64 (n / 2^sh) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt h,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem shlNat (n sh : Nat) : BitVec.ofNat 64 n <<< sh = BitVec.ofNat 64 ((2^sh)*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  have eq : BitVec.twoPow 64 sh = BitVec.ofNat 64 (2^sh) := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [eq]
  rw [← BitVec.ofNat_mul,Nat.mul_comm]

abbrev blocks (n : Nat) := 8*(n/128)
abbrev bulkLen (n : Nat) := 128*(n/128)

theorem bulk_size (n : Nat) : blocks n * 16 = bulkLen n := by
  dsimp [blocks,bulkLen]; omega

structure BulkTaken (V : Reg → Addr) (sp S E : Addr) (n : Nat) (s t : State) : Prop where
  env : Env (cursors V (E+BitVec.ofNat 64 (bulkLen n))) sp t
  ptr : t.gpr .r24=S+BitVec.ofNat 64 (bulkLen n)
  left : t.gpr .r25=BitVec.ofNat 64 (n-bulkLen n)
  r11 : t.gpr .r11=BitVec.ofNat 64 (bulkLen n)
  r7 : t.gpr .r7=S
  r8 : t.gpr .r8=BitVec.ofNat 64 (blocks n)
  r9 : t.gpr .r9=E
  r10 : t.gpr .r10=BitVec.ofNat 64 (blocks n)
  keeps : Keeps s t

theorem takeBulk_wp {V : Reg → Addr} {sp S E : Addr} {n : Nat} {s : State} (env : Env (cursors V E) sp s)
    (h24 : s.gpr .r24=S) (h25 : s.gpr .r25=BitVec.ofNat 64 n) (hn : n<2^64) :
    WP isa (.block takeBulk) s (BulkTaken V sp S E n s) := by
  have h21 : s.gpr .r21=E := env.fr _ (by decide)
  have shr : s.gpr .r25 >>> 7=BitVec.ofNat 64 (n/128) := h25 ▸ shrNat 7 hn
  have n7 : BitVec.ofNat 64 (n/128) <<< 7=BitVec.ofNat 64 (bulkLen n) := shlNat _ _
  have n3 : BitVec.ofNat 64 (n/128) <<< 3=BitVec.ofNat 64 (blocks n) := shlNat _ _
  have sz : bulkLen n≤n := by dsimp [bulkLen]; omega
  obtain ⟨tr,t,hx,⟨dest,ptr,left,r11,r7,r8,r9,r10,kept⟩,regs⟩ : WP isa (.block takeBulk) s (fun t =>
      (t.gpr .r21=E+BitVec.ofNat 64 (bulkLen n) ∧ t.gpr .r24=S+BitVec.ofNat 64 (bulkLen n) ∧
       t.gpr .r25=BitVec.ofNat 64 (n-bulkLen n) ∧ t.gpr .r11=BitVec.ofNat 64 (bulkLen n) ∧ t.gpr .r7=S ∧
       t.gpr .r8=BitVec.ofNat 64 (blocks n) ∧ t.gpr .r9=E ∧ t.gpr .r10 = BitVec.ofNat 64 (blocks n) ∧ Keeps s t)
      ∧ Keep wholeRegs s t) := by
    refine WP.keep wholeRegs ?_ (by decide)
    simp only [takeBulk]
    crun [mov,BitVec.or_self,h21,h24,shr,shrNat 7 hn,n7,n3,h25,ofNat_sub64 sz hn]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  exact ⟨tr,t,hx,advanceEnv env dest regs kept.sp,ptr,left,r11,r7,r8,r9,r10,kept⟩

theorem saveWord {s : State} {r b : Reg} {d : Nat} (hb : b ≠ .r0) (hd : d<2^15 ∧ d%4=0)
    (hw : InRegions s.wr (s.gpr b+BitVec.ofNat 64 d) 8) :
    WP isa (.block [.store .d r b d]) s
      (· = {s with mem := s.mem.writeW (s.gpr b+BitVec.ofNat 64 d) (s.gpr r)}) := by
  apply WP.of_runBlock
  simp only [runBlock_cons,exec_store_d hb hd hw,runStep_some,runBlock_nil,Option.some.injEq,exists_eq_left']

structure BulkArgs (sp C : Addr) (R : Nat) (s t : State) : Prop where
  key : t.gpr .r3=C
  rounds : (t.gpr .r4).toNat=R
  counter : t.gpr .r5=sp+192
  hash : t.gpr .r6=sp+160
  scratch : t.gpr .r0=sp+576
  slot : t.gpr .r12=sp
  keep : Keep [.r0,.r3,.r4,.r5,.r6,.r12] s t
  plain : Keeps s t

theorem bulkRegs_wp {V : Reg → Addr} {sp E : Addr} {s : State} {R : Nat} (env : Env (cursors V E) sp s)
    (w : V .r31=sp+128) (st : V .r30=sp+144) (hR : (V .r28).toNat=R) :
    WP isa (.block bulkRegs) s (BulkArgs sp (V .r29) R s) := by
  have r29 : s.gpr .r29=V .r29 := env.r29
  have r28 : (s.gpr .r28).toNat=R := env.r28 ▸ hR
  have r30 : s.gpr .r30=sp+144 := env.r30.trans st
  have r31 : s.gpr .r31=sp+128 := env.r31.trans w
  have spEq := env.sp
  obtain ⟨tr,t,hx,⟨key,rounds,counter,hash,scratch,slot,kept⟩,regs⟩ : WP isa (.block bulkRegs) s (fun t =>
      (t.gpr .r3 = V .r29 ∧ (t.gpr .r4).toNat=R ∧ t.gpr .r5=sp+192 ∧ t.gpr .r6=sp+160 ∧
       t.gpr .r0=sp+576 ∧ t.gpr .r12=sp ∧ Keeps s t) ∧ Keep [.r0,.r3,.r4,.r5,.r6,.r12] s t) := by
    refine WP.keep _ ?_ (by decide)
    simp only [bulkRegs]
    crun [mov,BitVec.or_self,r29,r28,r30,r31,spEq,BitVec.add_assoc]
    repeat' first | constructor | rfl | exact spEq.symm
  exact ⟨tr,t,hx,key,rounds,counter,hash,scratch,slot,regs,kept⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Fused counter mode and authentication of the first long gather piece -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Impl.AesGcm.PPC64LE.DirectGather (bulkRun)
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)

def callAreas (sp E : Addr) (k : Nat) : List Region :=
  [⟨sp+192,16⟩,⟨sp+160,16⟩,⟨E,k⟩,⟨sp+576,704⟩]

def bulkAreas (sp E : Addr) (k : Nat) : List Region := ⟨sp+240,8⟩ :: ⟨sp+96,8⟩ :: callAreas sp E k

def bulkMem (m : Mem) (sp : Addr) (k : Nat) : Mem :=
  (m.writeW (sp+240) (BitVec.ofNat 64 k)).writeW (sp+96) (sp+576)

theorem bulkMem_frame (m : Mem) (sp : Addr) (k : Nat) :
    Frame [⟨sp+240,8⟩,⟨sp+96,8⟩] m (bulkMem m sp k) := by
  exact ((Frame.refl _ m).writeW (List.mem_cons_self ..) (BitVec.ofNat 64 k) (Region.contains_self _ _)).writeW
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (sp+576) (Region.contains_self _ _)

structure Fused (V : Reg → Addr) (sp S E : Addr) (R n k b : Nat) (s t : State) : Prop where
  env : Env (cursors V (E+BitVec.ofNat 64 k)) sp t
  ptr : t.gpr .r24=S+BitVec.ofNat 64 k
  left : t.gpr .r25=BitVec.ofNat 64 (n-k)
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  count : t.mem.readW (sp+240) 64 = BitVec.ofNat 64 k
  frame : Frame (bulkAreas sp E k) s.mem t.mem
  cipher : blocksAt t.mem E b = Spec.Gcm.ctr32 (ciphOf s.mem (V .r29) R) (blockAt s.mem (sp+192))
    (blocksAt s.mem S b)
  counter : blockAt t.mem (sp+192)=Nat.repeat Spec.Gcm.inc32 b (blockAt s.mem (sp+192))
  hash : blockAt t.mem (sp+160)=ghashFrom (ctxH s.mem (V .r29)) (blockAt s.mem (sp+160)) (blocksAt t.mem E b)

structure Prepared (V : Reg → Addr) (sp S E : Addr) (R n : Nat) (s y : State) : Prop where
  abi : BulkAbi sp (V .r29) S E R (blocks n) y
  cfg : SealSplit.Call.Config y
  env : Env (cursors V (E+BitVec.ofNat 64 (bulkLen n))) sp y
  ptr : y.gpr .r24=S+BitVec.ofNat 64 (bulkLen n)
  left : y.gpr .r25=BitVec.ofNat 64 (n-bulkLen n)
  rd : y.rd=s.rd
  wr : y.wr=s.wr
  plain : y.mem = bulkMem s.mem sp (bulkLen n)

theorem bulkPrepare_wp
    {V : Reg → Addr} {sp S E : Addr} {R n : Nat} {s : State} (env : Env (cursors V E) sp s)
    (w : V .r31=sp+128) (st : V .r30=sp+144) (h24 : s.gpr .r24=S) (h25 : s.gpr .r25=BitVec.ofNat 64 n)
    (hn : n<2^64) (hR : (V .r28).toNat=R) (rounds : R=10 ∨ R=12 ∨ R=14)
    (space : BulkSpace sp (V .r29) S E n s) :
    WP isa Impl.AesGcm.PPC64LE.DirectGather.bulkPrepare s (Prepared V sp S E R n s) := by
  let k := bulkLen n
  let b := blocks n
  have hkn : k≤n := by dsimp [k,bulkLen]; omega
  have hb : b<2^64 := by dsimp [b,blocks]; omega_using [hn]
  refine WP.seq (WP.mono (takeBulk_wp env h24 h25 hn) fun u taken => ?_)
  have uw : u.gpr .r31=sp+128 := taken.env.r31.trans w
  have slot : u.gpr .r31+BitVec.ofNat 64 112=sp+240 := by rw [uw,BitVec.add_assoc]; rfl
  have canWrite (d : Nat) (lo : 32≤d) (hd : d+8≤1280) : InRegions s.wr (sp+BitVec.ofNat 64 d) 8 :=
    frameCovers space.stack lo hd _ _ ⟨_,List.mem_singleton_self _,Region.contains_self _ _⟩
  have wh : InRegions u.wr (u.gpr .r31+BitVec.ofNat 64 112) 8 := by
    rw [taken.keeps.wr,slot]; exact canWrite 240 (by decide) (by decide)
  refine WP.seq (WP.mono (saveWord (r := .r11) (by decide) (by decide) wh) fun v eq => ?_)
  subst v
  let v := {u with mem := u.mem.writeW (u.gpr .r31+BitVec.ofNat 64 112) (u.gpr .r11)}
  have envV : Env (cursors V (E+BitVec.ofNat 64 k)) sp v :=
    ⟨taken.env.fr,taken.env.sp,taken.env.perm.of_eq rfl rfl⟩
  refine WP.seq (WP.mono (bulkRegs_wp envV w st hR) fun x xa => ?_)
  have x12 : x.gpr .r12+BitVec.ofNat 64 96=sp+96 := by rw [xa.slot]; rfl
  have wh' : InRegions x.wr (x.gpr .r12+BitVec.ofNat 64 96) 8 := by
    rw [x12,xa.plain.wr]; change InRegions u.wr _ _; rw [taken.keeps.wr]; exact canWrite 96 (by decide) (by decide)
  refine WP.mono (saveWord (r := .r0) (by decide) (by decide) wh') fun y eq => ?_
  subst y
  let y := {x with mem := x.mem.writeW (x.gpr .r12+BitVec.ofNat 64 96) (x.gpr .r0)}
  have plain : y.mem=bulkMem s.mem sp k := by
    change x.mem.writeW _ _ = _
    rw [x12,xa.scratch,xa.plain.mem]
    change (u.mem.writeW _ _).writeW _ _ = _
    rw [taken.keeps.mem,slot,taken.r11]; rfl
  have rd : y.rd=s.rd := xa.plain.rd.trans taken.keeps.rd
  have wr : y.wr=s.wr := xa.plain.wr.trans taken.keeps.wr
  have cap := space.sub (t := y) (k := b*16) (by change blocks n*16≤_; rw [bulk_size]; exact hkn) rd wr
  have abi : BulkAbi sp (V .r29) S E R b y :=
    ⟨xa.plain.sp.trans taken.env.sp,xa.key,xa.rounds,xa.counter,xa.hash,
     (xa.keep.gpr (by decide)).trans taken.r7,by change (x.gpr .r8).toNat=_; rw [xa.keep.gpr (by decide),taken.r8,toNat64 hb],
     (xa.keep.gpr (by decide)).trans taken.r9,by change (x.gpr .r10).toNat=_; rw [xa.keep.gpr (by decide),taken.r10,toNat64 hb],
     by rw [plain]; exact Mem.readW_writeW_self64 _ _ _,xa.scratch⟩
  have renv : Env (cursors V (E+BitVec.ofNat 64 k)) sp y :=
    envV.keep (fun r hr => xa.keep.gpr (by revert r; decide)) xa.plain.sp xa.plain.rd xa.plain.wr
  exact ⟨abi,bulkConfig abi cap rounds,renv,(xa.keep.gpr (by decide)).trans taken.ptr,
    (xa.keep.gpr (by decide)).trans taken.left,rd,wr,plain⟩

theorem sharedArgs_ok (s : State) :
    WP isa (.block [VG.Impl.AesGcm.PPC64LE.mov .r10 .r0]) s (· = s.write .r10 (s.gpr .r0)) := by
  apply WP.of_runBlock
  simp only [VG.Impl.AesGcm.PPC64LE.mov,runBlock_cons,runStep_some,runBlock_nil,exec_logic,BitVec.or_self,
    Option.some.injEq,exists_eq_left']

theorem sharedCall_ok [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {sp C S E : Addr} {R n : Nat} {s : State} (a : BulkAbi sp C S E R (blocks n) s)
    (cfg : SealSplit.Call.Config s) :
    WP isa Impl.AesGcm.PPC64LE.DirectGather.sharedCall s (SealSplit.Call.Result s) := by
  let rd := SealSplit.Call.reads s
  let wr := SealSplit.Call.writes s
  let u := (s.write .r10 (s.gpr .r0)).callEntry.withRegions rd wr
  let v := s.callEntry.withRegions rd wr
  obtain ⟨layout,rounds,_,scratch⟩ := SplitBlocks.Contract.shared_pre _ cfg.pre
  have count : (s.gpr .r8).toNat=(s.gpr .r10).toNat := a.readBlocks.trans a.writeBlocks.symm
  have groupsFit : SplitBlocks.prefixCount u=(s.gpr .r8).toNat := by
    rw [SplitBlocks.prefixCount_eq]
    change (s.gpr .r8).toNat / 8 * 8 = _
    rw [a.readBlocks]; dsimp [blocks]; omega
  have reg : s.gpr .r0=s.mem.readW (s.sp+96) 64 := by rw [a.stack,a.scratch,a.scratchReg]
  have sameN : u.gpr .r8=v.gpr .r10 := BitVec.eq_of_toNat_eq count
  have sameK : (SplitBlocks.bufferState u).gpr .r8 = v.gpr .r8 := BitVec.eq_of_toNat_eq groupsFit
  have sameS : (SplitBlocks.bufferState u).gpr .r11 = SplitBlocks.Contract.scratch v := reg
  have pre : SplitBlocks.BufferPre u := by
    refine ⟨?_,rounds,?_,Or.inr groupsFit⟩
    · rw [groupsFit,sameN]
      exact SplitBlocks.sameLayout (b := SplitBlocks.Contract.prep (SplitBlocks.bufferState u)) layout rfl rfl rfl rfl sameS rfl sameK rfl rfl
    · change Covers [⟨s.gpr .r0,704⟩] wr
      rw [reg]; exact scratch
  apply WP.seq
  refine WP.mono (sharedArgs_ok s) fun _ eq => ?_
  subst_vars
  refine WP.call (k := SplitBlocks.bufferContract) SplitBlocks.encryptBuffers_correct
    (rd := rd) (wr := wr) pre cfg.reads cfg.writes ?_
  intro t hrd hwr hsp hf hcs _ hp
  have hd := hp.data
  change Spec.Gcm.blocksAt t.mem (s.gpr .r9) (s.gpr .r8).toNat=SplitBlocks.bufferOutput u at hd
  have drop : (Spec.Gcm.blocksAt s.mem (s.gpr .r9) (s.gpr .r10).toNat).drop (s.gpr .r8).toNat=[] := by
    apply List.drop_eq_nil_of_le
    simp only [Spec.Gcm.blocksAt,List.length_map,List.length_range,←count,Nat.le_refl]
  refine ⟨hrd,hwr,hsp,?_,hf,?_,?_,?_⟩
  · intro r hr
    have keep : ∀ r ∈ preserved, r ≠ .r10 := by decide
    simpa only [RegUpd.gpr_write,keep r hr,ite_false] using hcs r hr
  · rw [drop,List.append_nil,←count]; exact hd
  · rw [←count]; exact hp.ctr
  · rw [←count,hd]; exact hp.hash

/-- Compose the argument stores and the data helper. The caller's descriptor
may be larger than the multiple of 128 bytes passed to the fused helper. -/
theorem bulkRun_at [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → Addr} {sp S E : Addr} {R n : Nat} {s : State} (env : Env (cursors V E) sp s)
    (w : V .r31=sp+128) (st : V .r30=sp+144) (h24 : s.gpr .r24=S) (h25 : s.gpr .r25=BitVec.ofNat 64 n)
    (hn : n<2^64) (hR : (V .r28).toNat=R) (rounds : R=10 ∨ R=12 ∨ R=14)
    (space : BulkSpace sp (V .r29) S E n s) :
    WP isa bulkRun s (Fused V sp S E R n (bulkLen n) (blocks n) s) := by
  let k := bulkLen n
  let b := blocks n
  have hkn : k≤n := by dsimp [k,bulkLen]; omega
  refine WP.seq (WP.mono (bulkPrepare_wp env w st h24 h25 hn hR rounds space) fun y ⟨abi,cfg,renv,ptr,left,rd,wr,plain⟩ => ?_)
  refine WP.mono (sharedCall_ok abi cfg) fun t post => ?_
  have frame := post.frame
  rw [SealSplit.Call.writes,abi.counter,abi.hash,abi.dst,abi.writeBlocks,abi.stack,abi.scratch] at frame
  change Frame (callAreas sp E (b*16)) y.mem t.mem at frame
  rw [show b*16=k from bulk_size n] at frame
  have fp := bulkMem_frame s.mem sp k
  rw [← plain] at fp
  have subW (d : Nat) (hd : d+8≤1280) : Region.Sub ⟨sp+BitVec.ofNat 64 d,8⟩ ⟨sp,1280⟩ := Offset.sub_base _ hd
  have smallStack : ∀ r ∈ [⟨sp+240,8⟩,⟨sp+96,8⟩], Region.Sub r ⟨sp,1280⟩ := by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl; exacts [subW 240 (by decide),subW 96 (by decide)]
  have ciph := ciph_frame fp (fun r hr => space.stackCtx.symm.sub_right (smallStack r hr)) rounds
  have hh := ctxH_keep fp (fun r hr => space.stackCtx.symm.sub_right (smallStack r hr))
  have before (d : Nat) (ha : d+16≤240) (hb' : 104≤d) :
      blockAt y.mem (sp+BitVec.ofNat 64 d)=blockAt s.mem (sp+BitVec.ofNat 64 d) := by
    apply blockAt_frame fp
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint _ (.inl ha) (by omega_using [ha]) (by decide)
    · exact Offset.disjoint _ (.inr hb') (by omega_using [ha]) (by decide)
  have srcBlocks : blocksAt y.mem S b=blocksAt s.mem S b := by
    apply SealSplit.Input.blocksAt_frame fp
    intro r hr
    exact (space.stackSrc.symm.sub_left (Region.sub_prefix (by change 16*blocks n≤n; dsimp [blocks]; omega))).sub_right (smallStack r hr)
  have hc0 : blockAt y.mem (sp+192)=blockAt s.mem (sp+192) := before 192 (by decide) (by decide)
  have hy0 : blockAt y.mem (sp+160)=blockAt s.mem (sp+160) := before 160 (by decide) (by decide)
  have data := post.ciphertext
  rw [abi.dst,abi.writeBlocks,abi.key,abi.rounds,abi.counter,abi.src,abi.readBlocks,srcBlocks,hc0,
    List.drop_eq_nil_of_le (by rw [Proof.Gcm.length_blocksAt]),List.append_nil] at data
  have ctr := post.counter
  rw [abi.counter,abi.writeBlocks,hc0] at ctr
  have hash := post.hash
  rw [abi.hash,abi.key,abi.dst,abi.writeBlocks,hy0] at hash
  refine ⟨renv.of_saved post.saved post.sp post.rd post.wr,
    (post.saved _ (by decide)).trans ptr,
    (post.saved _ (by decide)).trans left,post.rd.trans rd,post.wr.trans wr,?_,?_,?_,ctr,?_⟩
  · have sf : Frame [⟨sp+96,8⟩] (s.mem.writeW (sp+240) (BitVec.ofNat 64 k)) y.mem := by
      rw [plain]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have beforeCount : t.mem.readW (sp+240) 64=y.mem.readW (sp+240) 64 := by
      apply frame.readW (Region.contains_self _ _) _ (by decide)
      intro r hr; simp only [callAreas,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)
      · exact (space.stackDst.sub_left (subW 240 (by decide))).sub_right (Region.sub_prefix hkn)
      · exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
    rw [beforeCount,sf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint _ (.inr (by decide)) (by decide) (by decide)) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  · exact (fp.mono (by simp [bulkAreas])).trans (frame.mono (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
  · change blocksAt t.mem E b = Spec.Gcm.ctr32 (ciphOf y.mem (V .r29) R) _ _ at data
    rwa [ciph] at data
  · rw [show ctxH y.mem (V .r29)=ctxH s.mem (V .r29) from hh] at hash
    exact hash

def prefixLen (n : Nat) := if n<512 then 0 else bulkLen n
def prefixBlocks (n : Nat) := if n<512 then 0 else blocks n

theorem prefixLe (n : Nat) : prefixLen n ≤ n := by dsimp [prefixLen,bulkLen]; split <;> omega
theorem prefixEq (n : Nat) : 16*prefixBlocks n = prefixLen n := by
  dsimp [prefixLen,prefixBlocks,blocks,bulkLen]; split <;> omega

theorem bulk_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → Addr} {sp S E : Addr} {R n : Nat} {s : State} (env : Env (cursors V E) sp s)
    (w : V .r31=sp+128) (st : V .r30=sp+144) (h24 : s.gpr .r24=S) (h25 : s.gpr .r25=BitVec.ofNat 64 n)
    (hn : n<2^64) (hR : (V .r28).toNat=R) (rounds : R=10 ∨ R=12 ∨ R=14)
    (space : BulkSpace sp (V .r29) S E n s) (initial : s.mem.readW (sp+240) 64=0) :
    WP isa Impl.AesGcm.PPC64LE.DirectGather.bulk s (Fused V sp S E R n (prefixLen n) (prefixBlocks n) s) := by
  let u := s.write .r12 (BitVec.ofNat 64 (n/512))
  have sh : s.gpr .r25 >>> 9=BitVec.ofNat 64 (n/512) := by rw [h25]; exact shrNat 9 hn
  have prep : WP isa (.block [.lsr .d .r12 .r25 9]) s (· = u) := by crun [u,sh]
  obtain ⟨tr,t,hx,rfl,keep⟩ := WP.keep [.r12] prep (by decide)
  have e := env.keep (s' := u) (fun r hr => keep.gpr (by revert r; decide)) (Exec.sp hx) rfl rfl
  have r12 : u.gpr .r12=BitVec.ofNat 64 (n/512) := by simp [u,State.write]
  refine WP.seq ⟨tr,u,hx,?_⟩
  refine WP.ite (decide (n/512=0)) (eval_zero r12 (by omega_using [hn])) (fun h => ?_) (fun h => ?_)
  · have hz : n/512=0 := by simpa using h
    have lt : n<512 := by omega_using [hz]
    simp only [prefixLen,prefixBlocks,ite_eq_left lt]
    apply WP.block_nil
    refine ⟨by simpa using e,by change s.gpr .r24 = S+BitVec.ofNat 64 0; simpa using h24,by change s.gpr .r25=BitVec.ofNat 64 (n-0); simpa using h25,rfl,rfl,initial,Frame.refl _ _,?_,rfl,?_⟩
    · simp [blocksAt,Spec.Gcm.ctr32,Spec.Gcm.keystream]
    · rfl
  · have hz : n/512≠0 := by simpa using h
    have lt : ¬n<512 := by omega_using [hz]
    simp only [prefixLen,prefixBlocks,ite_eq_right lt]
    exact WP.mono (bulkRun_at e w st h24 h25 hn hR rounds (space.sub (Nat.le_refl _) rfl rfl)) fun t post =>
      ⟨post.env,post.ptr,post.left,post.rd,post.wr,post.count,post.frame,post.cipher,post.counter,post.hash⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather
