module

public import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Bulk
import VerifiedGarbage.Proof.AesGcm.PPC64LE.DirectGather.Piece
import VerifiedGarbage.Proof.AesGcm.PPC64LE.SealSplit.Input
import VerifiedGarbage.Proof.AesGcm.PPC64LE.Absorb
import VerifiedGarbage.Proof.Gcm.StreamTo
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Gather.PPC64LE.Loop
import VerifiedGarbage.Proof.Gcm.SealGather
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.AesGcm.PPC64LE.J0
import VerifiedGarbage.Proof.Framework.Block

/-! # The fused prefix followed by the directly encrypted remainder -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom ctxH)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Gcm (Ctr xorKs)

/-- Each stack write of the fused prefix is separate from the descriptor
and the caller's data. -/
theorem bulkArea_mem {sp E : Addr} {k : Nat} {r : Region} (hr : r ∈ bulkAreas sp E k) :
    Region.Sub r ⟨sp,1280⟩ ∨ r=⟨E,k⟩ := by
  simp only [bulkAreas,callAreas,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (Offset.sub_base _ (by decide : 240+8≤1280))
  · exact .inl (Offset.sub_base _ (by decide : 96+8≤1280))
  · exact .inl (Offset.sub_base _ (by decide : 192+16≤1280))
  · exact .inl (Offset.sub_base _ (by decide : 160+16≤1280))
  · exact .inr rfl
  · exact .inl (Offset.sub_base _ (by decide : 576+704≤1280))

/-- Return all the ciphertext for this descriptor. Only the first `b`
blocks were already absorbed; the suffix remains for the final pass. -/
structure FirstPiece (V : Reg → Addr) (sp S E : Addr) (R n : Nat) (icb : Block) (s t : State) : Prop where
  env : Env (cursors V (E+BitVec.ofNat 64 n)) sp t
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  count : t.mem.readW (sp+240) 64 = BitVec.ofNat 64 (prefixLen n)
  cipher : bytesAt t.mem E n = xorKs (ciphOf s.mem (V .r29) R) icb 0 (bytesAt s.mem S n)
  ctr : Ctr t.mem (sp+192) (sp+208) (ciphOf s.mem (V .r29) R) icb n
  hash : blockAt t.mem (sp+160)=ghashFrom (ctxH s.mem (V .r29)) (blockAt s.mem (sp+160))
    (blocksAt t.mem E (prefixBlocks n))
  frame : Frame (⟨sp+192,32⟩ :: bulkAreas sp E n) s.mem t.mem

theorem firstPiece_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {V : Reg → Addr} {sp S E : Addr} {R n : Nat} {s : State} {icb : Block}
    (env : Env (cursors V E) sp s) (w : V .r31=sp+128) (st : V .r30=sp+144) (base : V .r27=E)
    (h24 : s.gpr .r24=S) (h25 : s.gpr .r25=BitVec.ofNat 64 n) (hR : (V .r28).toNat=R)
    (rounds : R=10 ∨ R=12 ∨ R=14) (space : BulkSpace sp (V .r29) S E n s)
    (a : Range V s S E n) (L : Lay (V .r29) (V .r30) (V .r31))
    (count : s.mem.readW (sp+240) 64=0)
    (ctr : Ctr s.mem (sp+192) (sp+208) (ciphOf s.mem (V .r29) R) icb 0) :
    WP isa (.seq Impl.AesGcm.PPC64LE.DirectGather.bulk Impl.AesGcm.PPC64LE.DirectGather.piece) s
      (FirstPiece V sp S E R n icb s) := by
  let k := prefixLen n
  let b := prefixBlocks n
  have fit := a.src.lt
  have hk : k≤n := prefixLe n
  have kb : 16*b=k := prefixEq n
  have cb : V .r30+BitVec.ofNat 64 48 = sp+192 := by rw [st,BitVec.add_assoc]; rfl
  have ks : V .r30+BitVec.ofNat 64 64 = sp+208 := by rw [st,BitVec.add_assoc]; rfl
  refine WP.seq (WP.mono (bulk_wp env w st h24 h25 fit hR rounds space count) fun u q => ?_)
  have apart {p : Addr} {len : Nat} (hs : (⟨p,len⟩ : Region).Disjoint ⟨sp,1280⟩)
      (hd : (⟨p,len⟩ : Region).Disjoint ⟨E,n⟩) :
      ∀ r ∈ bulkAreas sp E k, (⟨p,len⟩ : Region).Disjoint r := by
    intro r hr
    rcases bulkArea_mem hr with h | rfl
    · exact hs.sub_right h
    · exact hd.sub_right (Region.sub_prefix hk)
  have cph := ciph_frame q.frame (apart space.stackCtx.symm space.ctxDst) rounds
  have ct := Proof.Gcm.ctr_wholeTo (nb := b) ctr (by decide) q.cipher q.counter
  rw [kb,Nat.zero_add] at ct
  have rem : Range V u (S+BitVec.ofNat 64 k) (E+BitVec.ofNat 64 k) (n-k) :=
    a.drop hk q.rd q.wr
  have cr : Ctr u.mem (V .r30+BitVec.ofNat 64 48) (V .r30+BitVec.ofNat 64 64) (ciphOf u.mem (V .r29) R)
      icb k := by rw [cb,ks,cph]; exact ct.2
  have rc : V .r28=BitVec.ofNat 64 R := by rw [←hR,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine WP.mono (piece_wp q.env q.ptr q.left (by rw [base]) (Nat.lt_of_le_of_lt hk fit)
    rem L rounds rc cr) fun t out => ?_
  have sum : k+(n-k)=n := Nat.add_sub_of_le hk
  have endE : E+BitVec.ofNat 64 k+BitVec.ofNat 64 (n-k)=E+BitVec.ofNat 64 n := by rw [add_ofNat_assoc,sum]
  have f := out.frame
  change Frame [⟨E+BitVec.ofNat 64 k,n-k⟩,⟨V .r30+BitVec.ofNat 64 48,32⟩] u.mem t.mem at f
  rw [cb] at f
  have suffix : Region.Sub ⟨E+BitVec.ofNat 64 k,n-k⟩ ⟨E,n⟩ := Offset.sub_base _ (Nat.le_of_eq sum)
  have oldPrefix : ∀ r ∈ [⟨E+BitVec.ofNat 64 k,n-k⟩,⟨sp+192,32⟩], (⟨E,k⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact split_disj hk fit
    · exact (space.stackDst.symm.sub_left (Region.sub_prefix hk)).sub_right (Offset.sub_base _ (by decide : 192+32≤1280))
  have oldSlot (d z : Nat) (hd : d+z≤1280) (hs : d+z≤192 ∨ 224≤d) :
      ∀ r ∈ [⟨E+BitVec.ofNat 64 k,n-k⟩,⟨sp+192,32⟩], (⟨sp+BitVec.ofNat 64 d,z⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact (space.stackDst.sub_left (Offset.sub_base _ hd)).sub_right suffix
    · exact Offset.disjoint _ hs (by omega_using [hd]) (by decide)
  have sr := (space.stackSrc.symm.sub_left (Offset.sub_base _ (Nat.le_of_eq sum)))
  have sd := (space.srcDst.sub_left (Offset.sub_base _ (Nat.le_of_eq sum)))
  have source := bytesAt_frame q.frame (apart sr sd) (by omega_using [fit] : n-k≤2^64)
  obtain ⟨pieceEnv,rd,wr,finish,bytes,frame⟩ := out
  rw [endE] at pieceEnv
  rw [cb,ks,cph,sum] at finish
  rw [source,cph] at bytes
  have joined := done_appendTo ((bytesAt_frame f oldPrefix (Nat.le_trans hk (Nat.le_of_lt fit))).trans ct.1)
    (by simpa only [Nat.zero_add] using bytes)
  rw [sum] at joined
  refine ⟨pieceEnv,rd.trans q.rd,wr.trans q.wr,?_,joined,finish,?_,?_⟩
  · exact (f.readW (Region.contains_self _ _) (oldSlot 240 8 (by decide) (.inr (by decide))) (by decide)).trans q.count
  · have hy : blockAt t.mem (sp+160)=blockAt u.mem (sp+160) := blockAt_frame f (oldSlot 160 16 (by decide) (.inl (by decide)))
    have kept : blocksAt t.mem E b=blocksAt u.mem E b :=
      SealSplit.Input.blocksAt_frame f (by rwa [kb])
    rw [hy,kept]; exact q.hash
  · refine (q.frame.sub ?_).trans (f.sub ?_)
    · intro r hr; simp only [bulkAreas,callAreas,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      case inr.inr.inr.inr.inl => exact ⟨⟨E,n⟩,by simp [bulkAreas,callAreas],Region.sub_prefix hk⟩
      all_goals exact ⟨_,by simp [bulkAreas,callAreas],fun _ h => h⟩
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_,by simp [bulkAreas,callAreas],suffix⟩
      · exact ⟨_,List.mem_cons_self ..,fun _ h => h⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Memory and register invariants across POWER8 GCM gather descriptors -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxH ghashFrom gathered gatheredLen)
open VG.Proof.Gcm (Ctr xorKs)
open VG.Proof.Gather.PPC64LE (sb sl gl_succ gl_mono pt_succ)

structure LoopArgs where
  V : Reg → Addr
  sp : Addr
  desc : Addr
  count : Nat
  rounds : Nat
  icb : Block

abbrev LoopArgs.O (a : LoopArgs) := a.V .r27
abbrev LoopArgs.C (a : LoopArgs) := a.V .r29
abbrev LoopArgs.pos (a : LoopArgs) (entry : State) (i : Nat) := gatheredLen 64 entry.mem a.desc i
abbrev LoopArgs.text (a : LoopArgs) (entry : State) (i : Nat) := gathered 64 entry.mem a.desc i
abbrev LoopArgs.base (a : LoopArgs) (entry : State) (i : Nat) := sb entry.mem a.desc i
abbrev LoopArgs.len (a : LoopArgs) (entry : State) (i : Nat) := sl entry.mem a.desc i
abbrev LoopArgs.dp (a : LoopArgs) (i : Nat) := a.desc+BitVec.ofNat 64 (16*i)

def LoopArgs.regs (a : LoopArgs) (i : Nat) (r : Reg) : Addr :=
  if r=.r19 then a.dp i else if r=.r18 then BitVec.ofNat 64 (a.count-i) else a.V r

/-- The combined write set: the hash, the counter and partial keystream, the
two caller slots, the fused workspace, and the bytes written to the output. -/
abbrev loopFrame (a : LoopArgs) (p : Nat) := ⟨a.sp+192,32⟩ :: bulkAreas a.sp a.O p

structure LoopInput (a : LoopArgs) (entry : State) : Prop where
  work : a.V .r31=a.sp+128
  state : a.V .r30=a.sp+144
  roundReg : (a.V .r28).toNat=a.rounds
  rounds : a.rounds=10 ∨ a.rounds=12 ∨ a.rounds=14
  layout : Lay a.C (a.V .r30) (a.V .r31)
  countFit : a.count*16 < 2^64
  totalFit : a.pos entry a.count < 2^64
  stackFit : a.sp.toNat+1280 ≤ 2^64
  keyFit : a.C.toNat+256 ≤ 2^64
  dstFit : a.O.toNat+a.pos entry a.count ≤ 2^64
  keyRead : Covers [⟨a.C,256⟩] (entry.rd++entry.wr)
  descRead : Covers [⟨a.desc,16*a.count⟩] (entry.rd++entry.wr)
  dstWrite : Covers [⟨a.O,a.pos entry a.count⟩] entry.wr
  stackWrite : Covers [⟨a.sp+32,1248⟩] entry.wr
  stackCtx : (⟨a.sp,1280⟩ : Region).Disjoint ⟨a.C,256⟩
  stackDesc : (⟨a.sp,1280⟩ : Region).Disjoint ⟨a.desc,16*a.count⟩
  stackDst : (⟨a.sp,1280⟩ : Region).Disjoint ⟨a.O,a.pos entry a.count⟩
  ctxDst : (⟨a.C,256⟩ : Region).Disjoint ⟨a.O,a.pos entry a.count⟩
  descDst : (⟨a.desc,16*a.count⟩ : Region).Disjoint ⟨a.O,a.pos entry a.count⟩
  srcRead : ∀ i<a.count, Covers [⟨a.base entry i,a.len entry i⟩] (entry.rd++entry.wr)
  srcFit : ∀ i<a.count, (a.base entry i).toNat + a.len entry i ≤ 2^64
  stackSrc : ∀ i<a.count, (⟨a.sp,1280⟩ : Region).Disjoint ⟨a.base entry i,a.len entry i⟩
  srcDst : ∀ i<a.count, (⟨a.base entry i,a.len entry i⟩ : Region).Disjoint ⟨a.O,a.pos entry a.count⟩

structure LoopAt (a : LoopArgs) (entry : State) (i b : Nat) (s : State) : Prop where
  idx : i ≤ a.count
  hashLe : 16*b ≤ a.pos entry i
  env : Env (cursors (a.regs i) (a.O+BitVec.ofNat 64 (a.pos entry i))) a.sp s
  rd : s.rd=entry.rd
  wr : s.wr=entry.wr
  hashed : s.mem.readW (a.sp+240) 64=BitVec.ofNat 64 (16*b)
  hash : blockAt s.mem (a.sp+160)=ghashFrom (ctxH entry.mem a.C) (blockAt entry.mem (a.sp+160)) (blocksAt s.mem a.O b)
  ctr : Ctr s.mem (a.sp+192) (a.sp+208) (ciphOf entry.mem a.C a.rounds) a.icb (a.pos entry i)
  out : bytesAt s.mem a.O (a.pos entry i) = xorKs (ciphOf entry.mem a.C a.rounds) a.icb 0 (a.text entry i)
  frame : Frame (loopFrame a (a.pos entry i)) entry.mem s.mem

variable {a : LoopArgs} {entry s : State} {i b : Nat}

theorem LoopArgs.bound (a : LoopArgs) (entry : State) (hi : i<a.count) :
    a.pos entry i + a.len entry i ≤ a.pos entry a.count := by
  have bound := gl_mono entry.mem a.desc (Nat.succ_le_of_lt hi)
  rwa [gl_succ] at bound

theorem loopFrame_mem {p : Nat} {r : Region} (hr : r ∈ loopFrame a p) :
    Region.Sub r ⟨a.sp,1280⟩ ∨ r=⟨a.O,p⟩ := by
  rcases List.mem_cons.mp hr with rfl | h
  · exact .inl (Offset.sub_base _ (by decide : 192+32≤1280))
  · exact bulkArea_mem h

theorem LoopAt.original {r : Region} (v : LoopAt a entry i b s) (stack : r.Disjoint ⟨a.sp,1280⟩)
    (dst : r.Disjoint ⟨a.O,a.pos entry a.count⟩) : ∀ r' ∈ loopFrame a (a.pos entry i), r.Disjoint r' := by
  intro r' hr
  rcases loopFrame_mem hr with h | rfl
  · exact stack.sub_right h
  · exact dst.sub_right (Region.sub_prefix (gl_mono entry.mem a.desc v.idx))

theorem LoopAt.cipher (h : LoopInput a entry) (v : LoopAt a entry i b s) :
    ciphOf s.mem a.C a.rounds = ciphOf entry.mem a.C a.rounds :=
  ciph_frame v.frame (v.original h.stackCtx.symm h.ctxDst) h.rounds

theorem LoopAt.keyH (h : LoopInput a entry) (v : LoopAt a entry i b s) : ctxH s.mem a.C=ctxH entry.mem a.C :=
  blockAt_frame v.frame (fun r hr => (v.original h.stackCtx.symm h.ctxDst r hr).sub_left (Offset.sub_base _ (by decide : 240+16≤256)))

theorem LoopAt.range (h : LoopInput a entry) (v : LoopAt a entry i b s) (hi : i<a.count) :
    Range (a.regs (i+1)) s (a.base entry i) (a.O+BitVec.ofNat 64 (a.pos entry i)) (a.len entry i) := by
  let p := a.pos entry i
  let n := a.len entry i
  let total := a.pos entry a.count
  have fit : n<2^64 := (entry.mem.readW _ 64).isLt
  have bd := a.bound entry hi
  have hs := h.stackSrc i hi
  have ds : Region.Sub ⟨a.O+BitVec.ofNat 64 p,n⟩ ⟨a.O,total⟩ := Offset.sub_base _ bd
  have st : Region.Sub ⟨a.V .r30,80⟩ ⟨a.sp,1280⟩ := by rw [h.state]; exact Offset.sub_base _ (by decide : 144+80≤1280)
  have w : Region.Sub ⟨a.V .r31,288⟩ ⟨a.sp,1280⟩ := by rw [h.work]; exact Offset.sub_base _ (by decide : 128+288≤1280)
  have wr : Covers [⟨a.O+BitVec.ofNat 64 p,n⟩] s.wr := by rw [v.wr]; exact covers_off h.dstWrite bd h.totalFit
  have dfit : (a.O+BitVec.ofNat 64 p).toNat+n ≤ 2^64 := SealFused.fit_offset _ h.dstFit h.totalFit bd
  refine ⟨⟨by rw [v.rd,v.wr]; exact h.srcRead i hi,fit,h.srcFit i hi,hs.symm.sub_right st,hs.symm.sub_right w⟩,
    ⟨⟨covers_left wr,fit,dfit,(h.stackDst.symm.sub_left ds).sub_right st,(h.stackDst.symm.sub_left ds).sub_right w⟩,
     wr,h.ctxDst.sub_right ds⟩,.inr ((h.srcDst i hi).sub_right ds)⟩

theorem LoopAt.space (h : LoopInput a entry) (v : LoopAt a entry i b s) (hi : i<a.count)
    (start : a.pos entry i=0) : BulkSpace a.sp a.C (a.base entry i) a.O (a.len entry i) s := by
  have bound := a.bound entry hi
  rw [start,Nat.zero_add] at bound
  refine ⟨h.stackFit,h.keyFit,h.srcFit i hi,?_,by rw [v.rd,v.wr]; exact h.keyRead,
    by rw [v.rd,v.wr]; exact h.srcRead i hi,by rw [v.wr]; exact covers_prefix h.dstWrite bound,
    by rw [v.wr]; exact h.stackWrite,h.stackCtx,h.stackSrc i hi,
    h.stackDst.sub_right (Region.sub_prefix bound),(h.srcDst i hi).sub_right (Region.sub_prefix bound),
    h.ctxDst.sub_right (Region.sub_prefix bound)⟩
  exact Nat.le_trans (Nat.add_le_add_left bound _) h.dstFit

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Read the next descriptor and preserve the previous fragment's counters -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Proof.Gather.PPC64LE (sb sl)

structure Read (a : LoopArgs) (entry s : State) (i : Nat) (u : State) : Prop where
  env : Env (cursors (a.regs (i+1)) (a.O+BitVec.ofNat 64 (a.pos entry i))) a.sp u
  ptr : u.gpr .r24=a.base entry i
  left : u.gpr .r25=BitVec.ofNat 64 (a.len entry i)
  offset : u.gpr .r11=BitVec.ofNat 64 (a.pos entry i)
  keeps : Keeps s u

theorem read_at {a : LoopArgs} {entry s : State} {i b : Nat} (h : LoopInput a entry)
    (v : LoopAt a entry i b s) (hi : i<a.count) : WP isa (.block (next ++ ([.sub .r11 .r21 .r27] : List Instr))) s (Read a entry s i) := by
  have r19 : s.gpr .r19=a.dp i := v.env.fr _ (by decide)
  have r18 : s.gpr .r18=BitVec.ofNat 64 (a.count-i) := v.env.fr _ (by decide)
  have r21 : s.gpr .r21=a.O+BitVec.ofNat 64 (a.pos entry i) := v.env.fr _ (by decide)
  have r27 : s.gpr .r27=a.O := v.env.fr _ (by decide)
  have fit := h.countFit
  have allowed (d : Nat) (hd : 16*i+d+8≤16*a.count) : InRegions (s.rd++s.wr) (a.dp i+BitVec.ofNat 64 d) 8 := by
    rw [v.rd,v.wr,LoopArgs.dp,add_ofNat_assoc]
    exact h.descRead _ _ ⟨_,List.mem_singleton_self _,Offset.contains_base _ hd (by omega_using [hd,fit])⟩
  have unchanged (d : Nat) (hd : 16*i+d+8≤16*a.count) :
      s.mem.readW (a.dp i+BitVec.ofNat 64 d) 64=entry.mem.readW (a.dp i+BitVec.ofNat 64 d) 64 := by
    rw [LoopArgs.dp,add_ofNat_assoc]
    exact v.frame.readW (Offset.contains_base _ hd (by omega_using [hd,fit]))
      (v.original h.stackDesc.symm h.descDst) (by decide)
  have fit0 : 16*i+0+8≤16*a.count := by omega_using [hi]
  have fit8 : 16*i+8+8≤16*a.count := by omega_using [hi]
  let u := s.write .r24 (a.base entry i)
  let z := u.write .r25 (BitVec.ofNat 64 (a.len entry i))
  let y := z.write .r19 (a.dp (i+1))
  let x := y.write .r18 (BitVec.ofNat 64 (a.count-(i+1)))
  let t := x.write .r11 (BitVec.ofNat 64 (a.pos entry i))
  have hptr : exec (.load .d .r24 .r19 0) s = some u := by
    rw [exec_load_d (by decide) (by decide) (by rw [r19]; exact allowed 0 fit0),r19,unchanged 0 fit0]
    simp only [BitVec.add_zero]; rfl
  have hlen : exec (.load .d .r25 .r19 8) u = some z := by
    have h19 : u.gpr .r19=a.dp i := r19
    rw [exec_load_d (by decide) (by decide) (by rw [h19]; exact allowed 8 fit8),h19]
    change some (u.write .r25 (s.mem.readW (a.dp i+BitVec.ofNat 64 8) 64)) = _
    rw [unchanged 8 fit8]
    simp only [z,LoopArgs.len,sl,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hnext : exec (.addi .r19 .r19 16) z = some y := by
    rw [exec_addi (by decide) (by decide)]
    have h19 : z.gpr .r19=a.dp i := r19
    rw [h19,LoopArgs.dp,add_ofNat_assoc]
    congr 3
  have hdec : exec (.subi .r18 .r18 1) y = some x := by
    have h18 : y.gpr .r18=BitVec.ofNat 64 (a.count-i) := r18
    rw [exec_subi (by decide) (by decide),h18,ofNat_sub64 (by omega_using [hi]) (by omega_using [fit])]
    congr 3
  have hoff : exec (.sub .r11 .r21 .r27) x=some t := by
    have h21 : x.gpr .r21=a.O+BitVec.ofNat 64 (a.pos entry i) := r21
    have h27 : x.gpr .r27=a.O := r27
    rw [exec_sub,h21,h27,Offset.add_sub_cancel_left]
  have result : WP isa (.block (next ++ ([.sub .r11 .r21 .r27] : List Instr))) s (·=t) := by
    exact WP.block_cons_iff.mpr ⟨u,hptr,WP.block_cons_iff.mpr ⟨z,hlen,WP.block_cons_iff.mpr ⟨y,hnext,
      WP.block_cons_iff.mpr ⟨x,hdec,WP.block_cons_iff.mpr ⟨t,hoff,WP.block_nil rfl⟩⟩⟩⟩⟩
  refine WP.mono result fun e eq => ?_
  subst e
  refine ⟨⟨?_,v.env.sp,v.env.perm.of_eq rfl rfl⟩,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl⟩⟩
  intro r hr
  by_cases hr19 : r=.r19
  · subst hr19; rfl
  by_cases hr18 : r=.r18
  · subst hr18; rfl
  have hOther : r≠.r24 ∧ r≠.r25 ∧ r≠.r11 := by revert r; decide
  have kept := v.env.fr r hr
  simpa only [t,x,y,z,u,RegUpd.gpr_write,hr18,hr19,hOther.1,hOther.2.1,hOther.2.2,
    ite_false,cursors,LoopArgs.regs] using kept

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Append an encrypted gather descriptor and retain the authenticated prefix -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt ctxH ghashFrom)
open VG.Proof.Gcm (xorKs Ctr)
open VG.Proof.Gather.PPC64LE (gl_mono gl_succ pt_succ)

variable {a : LoopArgs} {entry s u : State} {i b : Nat}

theorem loopFrame_mono {j k : Nat} (hj : j≤k) {r : Region} (hr : r ∈ loopFrame a j) :
    ∃ r' ∈ loopFrame a k, Region.Sub r r' := by
  simp only [loopFrame,bulkAreas,callAreas,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inr.inr.inr.inl => exact ⟨⟨a.O,k⟩,by simp [loopFrame,bulkAreas,callAreas],Region.sub_prefix hj⟩
  all_goals exact ⟨_,by simp [loopFrame,bulkAreas,callAreas],fun _ h => h⟩

theorem regularStep (h : LoopInput a entry) (v : LoopAt a entry i b s) (opened : Read a entry s i u)
    (hi : i<a.count) : WP isa piece u (LoopAt a entry (i+1) b) := by
  let P := a.pos entry i
  let n := a.len entry i
  let E := a.O+BitVec.ofNat 64 P
  let S := a.base entry i
  have pLe := gl_mono entry.mem a.desc v.idx
  have total := h.totalFit
  have pj : P+n = a.pos entry (i+1) := (gl_succ entry.mem a.desc i).symm
  have cb : a.V .r30+BitVec.ofNat 64 48 = a.sp+192 := by rw [h.state,BitVec.add_assoc]; rfl
  have ks : a.V .r30+BitVec.ofNat 64 64 = a.sp+208 := by rw [h.state,BitVec.add_assoc]; rfl
  have old : ciphOf u.mem a.C a.rounds = ciphOf entry.mem a.C a.rounds := opened.keeps.mem ▸ v.cipher h
  have ctr : Ctr u.mem (a.V .r30+BitVec.ofNat 64 48) (a.V .r30+BitVec.ofNat 64 64)
      (ciphOf u.mem a.C a.rounds) a.icb P := by rw [old,opened.keeps.mem,cb,ks]; exact v.ctr
  have ra := v.range h hi
  have data : Range (a.regs (i+1)) u S E n :=
    ⟨ra.src.of_eq opened.keeps.rd opened.keeps.wr,ra.dst.of_eq opened.keeps.rd opened.keeps.wr,ra.buffers⟩
  have hR : (a.regs (i+1)) .r28=BitVec.ofNat 64 a.rounds := by
    change a.V .r28=_; rw [←h.roundReg,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  refine WP.mono (piece_wp opened.env opened.ptr opened.left rfl (Nat.lt_of_le_of_lt pLe total)
    data h.layout h.rounds hR ctr) fun t p => ?_
  obtain ⟨env,rd,wr,count,ct,fr⟩ := p
  change Frame [⟨E,n⟩,⟨a.V .r30+BitVec.ofNat 64 48,32⟩] u.mem t.mem at fr
  rw [cb,opened.keeps.mem] at fr
  have bound : P+n ≤ a.pos entry a.count := a.bound entry hi
  have rest : Region.Sub ⟨E,n⟩ ⟨a.O,a.pos entry a.count⟩ := Offset.sub_base _ bound
  have sep : (⟨a.O,P⟩ : Region).Disjoint ⟨E,n⟩ :=
    Offset.disjoint_base a.O (by omega_using []) (by omega_using [bound,total]) |>.symm
  have before {j : Nat} (hj : j≤P) : ∀ r ∈ [⟨E,n⟩,⟨a.sp+192,32⟩], (⟨a.O,j⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact sep.sub_left (Region.sub_prefix hj)
    · obtain rfl := List.mem_singleton.mp hr
      exact (h.stackDst.symm.sub_left (Region.sub_prefix (Nat.le_trans hj pLe))).sub_right (Offset.sub_base _ (by decide : 192+32≤1280))
  have slot (d l : Nat) (hd : d+l≤1280) (hs : d+l≤192 ∨ 224≤d) :
      ∀ r ∈ [⟨E,n⟩,⟨a.sp+192,32⟩], (⟨a.sp+BitVec.ofNat 64 d,l⟩ : Region).Disjoint r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact (h.stackDst.sub_left (Offset.sub_base _ hd)).sub_right rest
    · obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ hs (by omega_using [hd]) (by decide)
  have src : bytesAt u.mem S n = bytesAt entry.mem S n := by
    rw [opened.keeps.mem]
    exact bytesAt_frame v.frame (v.original (h.stackSrc i hi).symm (h.srcDst i hi)) (by omega_using [bound,total])
  have joined : E+BitVec.ofNat 64 n = a.O+BitVec.ofNat 64 (a.pos entry (i+1)) := by
    rw [←pj,←add_ofNat_assoc]
  change Ctr t.mem (a.V .r30+BitVec.ofNat 64 48) (a.V .r30+BitVec.ofNat 64 64) (ciphOf u.mem a.C a.rounds) a.icb (P+n) at count
  rw [cb,ks,old,pj] at count
  change bytesAt t.mem E n=xorKs (ciphOf u.mem a.C a.rounds) a.icb P (bytesAt u.mem S n) at ct
  rw [old,src] at ct
  refine ⟨Nat.succ_le_of_lt hi,Nat.le_trans v.hashLe (pj ▸ Nat.le_add_right P n),by rwa [joined] at env,
    rd.trans (opened.keeps.rd.trans v.rd),wr.trans (opened.keeps.wr.trans v.wr),?_,?_,count,?_,?_⟩
  · exact (fr.readW (Region.contains_self _ _) (slot 240 8 (by decide) (.inr (by decide))) (by decide)).trans v.hashed
  · have hy := blockAt_frame fr (slot 160 16 (by decide) (.inl (by decide)))
    have kept := SealSplit.Input.blocksAt_frame fr (before v.hashLe)
    rw [kept]
    exact hy.trans v.hash
  · rw [←pj,bytesAt_add,LoopArgs.text,pt_succ,Proof.Gcm.xorKs_append,Proof.Gcm.length_gathered,Nat.zero_add]
    rw [bytesAt_frame fr (before (Nat.le_refl P)) (Nat.le_trans pLe (Nat.le_of_lt total)),v.out,ct]
  · refine (v.frame.sub (fun _ hh => loopFrame_mono (a := a) (pj ▸ Nat.le_add_right P n) hh)).trans (fr.sub ?_)
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ⟨⟨a.O,a.pos entry (i+1)⟩,by simp [loopFrame,bulkAreas,callAreas],Offset.sub_base _ (Nat.le_of_eq pj)⟩
    · obtain rfl := List.mem_singleton.mp hr
      exact ⟨_,List.mem_cons_self ..,fun _ h => h⟩

theorem firstStep [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    (h : LoopInput a entry) (v : LoopAt a entry i b s) (opened : Read a entry s i u)
    (hi : i<a.count) (start : a.pos entry i = 0) :
    WP isa (.seq bulk piece) u (LoopAt a entry (i+1) (prefixBlocks (a.len entry i))) := by
  let n := a.len entry i
  have b0 : b=0 := by have bound := v.hashLe; rw [start] at bound; omega_using [bound]
  have idx : a.pos entry (i+1)=n := by change a.pos entry (i+1)=_; rw [show a.pos entry (i+1)=a.pos entry i+n from gl_succ ..,start,Nat.zero_add]
  have he := opened.env
  rw [start,add_ofNat_zero] at he
  have ra := v.range h hi
  rw [start,add_ofNat_zero] at ra
  have range : Range (a.regs (i+1)) u (a.base entry i) a.O n :=
    ⟨ra.src.of_eq opened.keeps.rd opened.keeps.wr,ra.dst.of_eq opened.keeps.rd opened.keeps.wr,ra.buffers⟩
  have space := v.space h hi start
  have old : ciphOf u.mem a.C a.rounds=ciphOf entry.mem a.C a.rounds := by rw [opened.keeps.mem]; exact v.cipher h
  have ct := v.ctr
  rw [start] at ct
  have cph : Ctr u.mem (a.sp+192) (a.sp+208) (ciphOf u.mem a.C a.rounds) a.icb 0 := by rw [old,opened.keeps.mem]; exact ct
  have hv : u.mem.readW (a.sp+240) 64=0 := by rw [opened.keeps.mem,v.hashed,b0]; rfl
  refine WP.mono (firstPiece_wp he h.work h.state rfl opened.ptr opened.left h.roundReg h.rounds
    (space.sub (Nat.le_refl _) opened.keeps.rd opened.keeps.wr) range h.layout hv cph) fun t post => ?_
  obtain ⟨env,rd,wr,hashed,ct,ctr,hash,frame⟩ := post
  have hy := v.hash
  rw [b0] at hy
  change blockAt s.mem (a.sp+160) = blockAt entry.mem (a.sp+160) at hy
  change blockAt t.mem (a.sp+160)=ghashFrom (ctxH u.mem a.C) (blockAt u.mem (a.sp+160)) _ at hash
  rw [opened.keeps.mem,v.keyH h,hy] at hash
  change Ctr t.mem (a.sp+192) (a.sp+208) (ciphOf u.mem a.C a.rounds) a.icb n at ctr
  rw [old] at ctr
  change bytesAt t.mem a.O n = xorKs (ciphOf u.mem a.C a.rounds) a.icb 0 (bytesAt u.mem (a.base entry i) n) at ct
  rw [old,opened.keeps.mem,bytesAt_frame v.frame (v.original (h.stackSrc i hi).symm (h.srcDst i hi)) (Nat.le_of_lt (entry.mem.readW _ 64).isLt)] at ct
  have nil : a.text entry i = [] := List.length_eq_zero_iff.mp ((Proof.Gcm.length_gathered ..).trans start)
  refine ⟨Nat.succ_le_of_lt hi,?_,by rwa [idx],rd.trans (opened.keeps.rd.trans v.rd),wr.trans (opened.keeps.wr.trans v.wr),?_,
    hash,by rwa [idx],?_,?_⟩
  · rw [prefixEq,idx]; exact prefixLe n
  · rw [prefixEq]; exact hashed
  · rw [idx,LoopArgs.text,pt_succ]
    change bytesAt t.mem a.O n = xorKs _ _ 0 (a.text entry i ++ _)
    rw [nil,List.nil_append]; exact ct
  · rw [idx]
    change Frame (loopFrame a n) u.mem t.mem at frame
    rw [opened.keeps.mem] at frame
    exact (v.frame.sub (fun _ hr => loopFrame_mono (a := a) (by rw [start]; exact Nat.zero_le n) hr)).trans frame

end VG.Proof.AesGcm.PPC64LE.DirectGather

/-! # Every gather descriptor encrypts and authenticates the same byte stream -/

@[expose] public section
namespace VG.Proof.AesGcm.PPC64LE.DirectGather
open VG VG.PPC64LE VG.Impl.AesGcm.PPC64LE.DirectGather
open VG.Proof.Gather.PPC64LE (gl_mono)

/-- Number of blocks already authenticated at a descriptor boundary. Empty
leading descriptors leave the fused call available to the next descriptor. -/
def LoopArgs.hashed (a : LoopArgs) (entry : State) : Nat → Nat
  | 0 => 0
  | i+1 => if a.pos entry i=0 then prefixBlocks (a.len entry i) else a.hashed entry i

theorem iteration_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {a : LoopArgs} {entry s : State} {i : Nat} (h : LoopInput a entry)
    (v : LoopAt a entry i (a.hashed entry i) s) (hi : i<a.count) :
    WP isa (.seq (.block (next ++ ([.sub .r11 .r21 .r27] : List Instr))) (.seq (.ite (.zero .d .r11) bulk (.block [])) piece)) s
      (LoopAt a entry (i+1) (a.hashed entry (i+1))) := by
  refine WP.seq (WP.mono (read_at h v hi) fun u opened => WP.seq ?_)
  have fit : a.pos entry i < 2^64 := Nat.lt_of_le_of_lt (gl_mono entry.mem a.desc v.idx) h.totalFit
  refine WP.ite (decide (a.pos entry i=0)) (eval_zero opened.offset fit) (fun yes => ?_) (fun no => ?_)
  · have yes' : a.pos entry i=0 := by simpa using yes
    rw [LoopArgs.hashed,ite_eq_left yes']
    exact WP.seq_iff.mp (firstStep h v opened hi yes')
  · have no' : a.pos entry i≠0 := by simpa using no
    rw [LoopArgs.hashed,ite_eq_right no']
    exact WP.block_nil (regularStep h v opened hi)

theorem pieces_exact [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {a : LoopArgs} {entry s : State} (h : LoopInput a entry) (start : LoopAt a entry 0 0 s) :
    WP isa pieces s (LoopAt a entry a.count (a.hashed entry a.count)) := by
  have fit := h.countFit
  have r18 : s.gpr .r18=BitVec.ofNat 64 a.count := by simpa [LoopArgs.regs,cursors] using start.env.fr .r18 (by decide)
  refine WP.ite (decide (a.count=0)) (eval_zero r18 (by omega_using [fit])) (fun b => ?_) (fun b => ?_)
  · have z : a.count=0 := by simpa using b
    rw [z,LoopArgs.hashed]
    exact WP.block_nil start
  · have nz : a.count≠0 := by simpa using b
    let I (measure : Nat) (t : State) := ∃ i, measure=a.count-i ∧ i<a.count ∧ LoopAt a entry i (a.hashed entry i) t
    refine WP.loop (M := isa) I (fun m t ⟨i,measure,hi,v⟩ => WP.mono (iteration_wp h v hi) fun u q => ?_)
      a.count s ⟨0,rfl,Nat.pos_of_ne_zero nz,start⟩
    have left : u.gpr .r18=BitVec.ofNat 64 (a.count-(i+1)) := q.env.fr _ (by decide)
    by_cases last : i+1=a.count
    · refine .inl ⟨?_,last ▸ q⟩
      have z : u.gpr .r18=0 := by rw [left,last,Nat.sub_self]; rfl
      simp only [eval,State.read,Size.bits,BitVec.setWidth_eq,z]; rfl
    · have nn : a.count-(i+1)≠0 := by omega_using [hi,last]
      refine .inr ⟨?_,a.count-(i+1),by omega_using [measure,hi],i+1,rfl,by omega_using [hi,last],q⟩
      have nonzero : u.gpr .r18 ≠ 0 := by
        intro z; have hz := congrArg BitVec.toNat (left.symm.trans z)
        rw [toNat64 (by omega_using [fit])] at hz
        exact nn hz
      simpa only [eval,State.read,Size.bits,BitVec.setWidth_eq,Option.some.injEq] using (bne_iff_ne.mpr nonzero)

theorem pieces_wp [VG.Proof.Gcm.PPC64LE.GhashLaw] [VG.Proof.Gcm.PPC64LE.Vpmsum.FoldLaw]
    {a : LoopArgs} {entry s : State} (h : LoopInput a entry) (start : LoopAt a entry 0 0 s) :
    WP isa pieces s (fun t => ∃ b, LoopAt a entry a.count b t) :=
  WP.mono (pieces_exact h start) fun _ q => ⟨_,q⟩

end VG.Proof.AesGcm.PPC64LE.DirectGather
