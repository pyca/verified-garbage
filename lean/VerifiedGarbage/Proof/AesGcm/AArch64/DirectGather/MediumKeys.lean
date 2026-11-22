module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.AesGcm.AArch64.DirectGather.LeafCT
public import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium
public import VerifiedGarbage.Proof.AesGcm.AArch64.Crypt
import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortSeal
import VerifiedGarbage.Proof.Aes.AArch64.Aese.Rounds
import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.AesGcm.AArch64.Rel
import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Proof.AesGcm.AArch64.RelBase
meta import VerifiedGarbage.Impl.AesGcm.AArch64.DirectGather.Medium
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Counter zero yields the tag mask, and the remaining encrypted zero blocks
give the keystream from the first data counter onward. -/
@[expose] public section
namespace VG.Proof.AesGcm.AArch64.DirectGather
open VG VG.AArch64
open VG.Spec.Gcm (Block blockAt blocksAt ctr32 inc32)
open VG.Proof.Gcm (ksByte)

private theorem ctrZeroLanes {m m' : Mem} {D : Addr} {n : Nat} {J : Block} {ciph : Block → Block}
    (out : blocksAt m' D n = ctr32 ciph J (blocksAt m D n))
    (z : ∀ i < n, blockAt m (D+BitVec.ofNat 64 (16*i)) = 0) {i : Nat} (hi : i<n) :
    blockAt m' (D+BitVec.ofNat 64 (16*i)) = ciph (Nat.repeat inc32 i J) := by
  have e := congrArg (fun xs => xs.getD i 0) out
  rw [Proof.Gcm.blocksAt_getD _ _ _ hi,Proof.Gcm.ctr32_getD _ _ _ (by rwa [Proof.Gcm.length_blocksAt]),
    Proof.Gcm.blocksAt_getD _ _ _ hi,z i hi] at e
  simpa using e

theorem mediumCtrBytes {m m' : Mem} {D : Addr} {n : Nat} {J : Block} {ciph : Block → Block}
    (out : blocksAt m' D (n+1) = ctr32 ciph J (blocksAt m D (n+1)))
    (z : ∀ i < n+1, blockAt m (D+BitVec.ofNat 64 (16*i)) = 0) :
    blockAt m' D = ciph J ∧ ∀ k < 16*n, m' (D+16+BitVec.ofNat 64 k) = ksByte ciph (inc32 J) k := by
  refine ⟨by simpa [Nat.repeat] using ctrZeroLanes out z (i := 0) (by omega),?_⟩
  intro k hk
  have eq : D+16+BitVec.ofNat 64 k = D+BitVec.ofNat 64 (16*(k/16+1))+BitVec.ofNat 64 (k%16) := by
    change D+BitVec.ofNat 64 16+_ = _
    rw [Offset.add_add,Offset.add_add]
    congr 2
    omega
  have h := ctrZeroLanes out z (i := k/16+1) (by omega)
  rw [eq,Proof.Gcm.bytes_toBytes_blockAt m' _ (Nat.mod_lt k (by decide)),h,ksByte,Proof.Gcm.repeat_add]
  rfl


open VG.Impl.AesGcm.AArch64 VG.AArch64.RegUpd
open VG.Impl.AesGcm.AArch64.DirectGather (Medium.work Medium.keyO)
open VG.Proof.Aes.Vector (getD_st getD_ofFn)

structure MediumKeysPre (W K : Addr) (R blocks : Nat) (s : State) : Prop where
  x19 : s.gpr .x19 = W
  x21 : s.gpr .x21 = K
  x22 : s.gpr .x22 = BitVec.ofNat 64 R
  x25 : s.gpr .x25 = BitVec.ofNat 64 (16*blocks)
  rounds : R=10 ∨ R=12 ∨ R=14
  bound : blocks ≤ 15
  wrap : W.toNat + 752 ≤ 2^64
  work : Covers [⟨W,752⟩] s.wr
  key : Covers [⟨K,240⟩] (s.rd++s.wr)
  apart : (⟨K,240⟩ : Region).Disjoint ⟨W,752⟩
  nonce0 : InRegions (s.rd++s.wr) (s.gpr .x23+BitVec.ofNat 64 0) 8
  nonce8 : InRegions (s.rd++s.wr) (s.gpr .x23+BitVec.ofNat 64 8) 4
  zero : ∀ i < blocks+1, blockAt s.mem (W+224+BitVec.ofNat 64 (16*i)) = 0

abbrev medD (W : Addr) := W+BitVec.ofNat 64 224
abbrev medS (W : Addr) := W+BitVec.ofNat 64 736
abbrev seedLane (s : State) := setLane (Counters.seedVec s) 32 3 (Counters.countWord 0)

private theorem seedBlock (s : State) (W : Addr) : blockAt (s.mem.write W 16 (seedLane s)) W = Counters.jZero s := by
  apply Proof.Aes.block_ext
  intro k hk
  rw [Proof.Aes.toBytes_blockAt _ _ hk,Stitch.write16_at _ _ _ hk,← getD_st _ hk,
    Counters.count_state s (i := 0) (by decide),Proof.Aes.ctrState,getD_ofFn hk]
  rfl

abbrev medKept := [Reg.x19,.x21,.x22,.x23,.x24,.x25,.x26]

private structure SeedPost (s : State) (W K : Addr) (R blocks : Nat) (t : State) : Prop where
  call : CtrCall t K W (medD W) (medS W) R (blocks+1) 0
  mem : t.mem = s.mem.write W 16 (seedLane s)
  reg : ∀ r ∈ medKept, t.gpr r = s.gpr r
  desc : t.gpr .x27 = s.gpr .x6
  count : t.gpr .x28 = s.gpr .x7
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

private abbrev seedRest : List Instr :=
  [.movz .w .x12 256 1,.vop (.ins .s4 .v31 3 .x12),.strq .v31 .x19 0,
   mov .x0 .x21,mov .x1 .x22,mov .x2 .x19,ptr .x3 .x19 224,.lsr .x .x4 .x25 4,
   .addImm .x .x4 .x4 1,ptr .x5 .x19 736,mov .x27 .x6,mov .x28 .x7]

private theorem mediumSeed_ok {W K : Addr} {R blocks : Nat} {s : State} (p : MediumKeysPre W K R blocks s) :
    WP isa (.block Impl.AesGcm.AArch64.DirectGather.Medium.seed) s (SeedPost s W K R blocks) := by
  change WP isa (.block (Counters.seedCode ++ seedRest)) _ _
  rw [WP.block_append_iff]
  refine (Counters.seed_ok s p.nonce0 p.nonce8).mono fun u ⟨lane,f⟩ => ?_
  have c {r : Reg} (h : r ∉ Counters.seedRegs) := f.gpr r h
  have w := (c (r := .x19) (by decide)).trans p.x19
  have k := (c (r := .x21) (by decide)).trans p.x21
  have r := (c (r := .x22) (by decide)).trans p.x22
  have z := (c (r := .x25) (by decide)).trans p.x25
  have store : InRegions u.wr (u.gpr .x19+0#64) 16 := by
    rw [f.wr,w]; exact in_off (d:=0) p.work (by decide) (by decide)
  have count : (u.gpr .x25 >>> 4) + 1 = BitVec.ofNat 64 (blocks+1) := by
    rw [z,lsr_ofNat _ _ (by have := p.bound; omega)]
    simp [BitVec.ofNat_add]
  have reads := p.key
  have wc := covers_off (d:=0) (n:=16) p.work (by decide) (by decide)
  simp only [BitVec.add_zero] at wc
  have wd := covers_off (d:=224) (n:=16*(blocks+1)) p.work (by have := p.bound; omega) (by decide)
  have ws := covers_off (d:=736) (n:=0) p.work (by decide) (by decide)
  have writes : Covers [⟨W,16⟩,⟨medD W,16*(blocks+1)⟩,⟨medS W,0⟩] s.wr :=
    Covers.cons wc (Covers.cons wd ws)
  have wrap := p.wrap
  have wb : (medD W).toNat + 16*(blocks+1) ≤ 2^64 := by
    simp only [medD,BitVec.toNat_add,BitVec.toNat_ofNat]
    have := p.bound; omega
  have sparse (d n : Nat) (h : d+n ≤ 752) := p.apart.sub_right (Offset.sub_base W h)
  have sd := sparse 224 (16*(blocks+1)) (by have := p.bound; omega)
  have ss := sparse 736 0 (by decide)
  have cd := Offset.disjoint_base W (d:=224) (n:=16*(blocks+1)) (k:=16) (by decide) (by have := p.bound; omega)
  have cs := Offset.disjoint_base W (d:=736) (n:=0) (k:=16) (by decide) (by decide)
  have ds := Offset.disjoint W (d:=224) (n:=16*(blocks+1)) (e:=736) (k:=0)
    (.inl (by have := p.bound; omega)) (by have := p.bound; omega) (by decide)
  rw [show seedRest = [.movz .w .x12 256 1,.vop (.ins .s4 .v31 3 .x12)] ++ seedRest.drop 2 from rfl,
    WP.block_append_iff]
  rw [WP.block_cons_iff]; refine ⟨_,rfl,?_⟩
  rw [WP.block_cons_iff]; refine ⟨_,rfl,?_⟩
  rw [WP.block_nil_iff]
  let a := u.write .w .x12 (Counters.countWord 0)
  change WP isa (.block (seedRest.drop 2)) (a.setV .v31 (setLane (u.v .v31) 32 3 (Counters.countWord 0))) _
  rw [lane]
  let v := a.setV .v31 (seedLane s)
  change WP isa (.block (.strq .v31 .x19 0 :: seedRest.drop 3)) v _
  rw [WP.block_cons_iff]
  refine ⟨_,Proof.Gcm.AArch64.Pmull.exec_strq (t := .v31) (n := .x19) (off := 0) (s := v) (by decide) (by decide) (by exact store),?_⟩
  let u₀ := {v with mem := u.mem.write W 16 (seedLane s)}
  have ev : v.gpr .x19 + BitVec.ofNat 64 0 = W := by change u.gpr .x19+0#64 = W; simpa using w
  rw [ev]
  change WP isa (.block (seedRest.drop 3)) u₀ _
  refine WP.of_runBlock ⟨_,by arun [seedRest,List.drop],?_⟩
  refine ⟨⟨?_,?_,?_,?_,?_,?_,p.rounds,wb,by have := p.bound; omega,
    p.apart.sub_right (Region.sub_prefix (by decide)),sd,ss,cd.symm,cs.symm,ds,?_,?_⟩,?_,?_,?_,?_,f.sp,f.rd,f.wr⟩
  all_goals try simp only [gpr_write,gpr_setV,ite_true,ite_false,reduceCtorEq,BitVec.setWidth_eq,
    BitVec.add_zero,medD,medS,u₀,v,a,w,k,r,mem_write,f.mem,wr_write,rd_write,rd_setV,wr_setV]
  · exact count
  · rw [f.rd,f.wr]
    exact Covers.append_left reads (Covers.right writes)
  · rw [f.wr]; exact writes
  · intro j hj
    simp only [medKept,List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact c (by decide)
  · exact c (by decide)
  · exact c (by decide)



structure MediumKeysPost (W K : Addr) (R blocks : Nat) (s t : State) : Prop where
  mask : blockAt t.mem (medD W) = ciphOf s.mem K R (Counters.jZero s)
  stream : ∀ k < 16*blocks, t.mem (W+240+BitVec.ofNat 64 k) = ksByte (ciphOf s.mem K R) (inc32 (Counters.jZero s)) k
  frame : Frame [⟨W,16⟩,⟨medD W,256⟩] s.mem t.mem
  kept : ∀ r ∈ medKept, t.gpr r = s.gpr r
  desc : t.gpr .x27 = s.gpr .x6
  count : t.gpr .x28 = s.gpr .x7
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem mediumKeys_ok {W K : Addr} {R blocks : Nat} {s : State} (v : GcmImpl)
    (zeroScratch : v.ctr.scratch = 0) (p : MediumKeysPre W K R blocks s) :
    WP isa (Impl.AesGcm.AArch64.DirectGather.Medium.keys v.callees) s (MediumKeysPost W K R blocks s) := by
  refine WP.seq ((mediumSeed_ok p).mono fun u z => ?_)
  refine (ctr_callLe v.ctr (Nat.le_of_eq zeroScratch) z.call).mono fun t c => ?_
  have F : Frame [⟨W,16⟩] s.mem u.mem := by
    rw [z.mem]
    exact (Frame.refl _ _).write (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have ks : 16*(R+1) ≤ 240 := by rcases p.rounds with eq|eq|eq <;> omega
  have key : ciphOf u.mem K R = ciphOf s.mem K R := by
    unfold ciphOf
    rw [bytesAt_frame F (fun r hr => List.mem_singleton.mp hr ▸
      (p.apart.sub_right (Region.sub_prefix (by decide : 16 ≤ 752))).sub_left (Region.sub_prefix ks)) (by omega)]
  have y : blockAt u.mem W = Counters.jZero s := by rw [z.mem,seedBlock]
  have out : blocksAt t.mem (medD W) (blocks+1) =
      ctr32 (ciphOf s.mem K R) (Counters.jZero s) (blocksAt u.mem (medD W) (blocks+1)) := by
    rw [← key,← y]; exact c.out
  have zero (i : Nat) (hi : i<blocks+1) : blockAt u.mem (medD W+BitVec.ofNat 64 (16*i)) = 0 := by
    have le := p.bound
    rw [blockAt_frame F (fun r hr => List.mem_singleton.mp hr ▸ (by
      rw [medD,Offset.add_add]; exact Offset.disjoint_base W (by omega) (by omega)))]
    exact p.zero _ hi
  obtain ⟨mask,stream⟩ := mediumCtrBytes out zero
  have ss : (fun r : Region => r ∈ [⟨W,16⟩,⟨medD W,256⟩]) ⟨W,16⟩ := List.mem_cons_self ..
  have cf : Frame [⟨W,16⟩,⟨medD W,256⟩] u.mem t.mem := c.frame.sub fun r hr => by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact ⟨_,ss,fun _ h => h⟩
    · exact ⟨⟨medD W,256⟩,by simp,Region.sub_prefix (by have := p.bound; omega)⟩
    · exact ⟨_,ss,fun _ h => by simp [Region.Contains] at h⟩
  refine ⟨mask,?_,(F.mono (fun _ h => List.mem_cons.mpr (.inl (List.mem_singleton.mp h)))).trans cf,
    fun r hr => ?_,(c.saved .x27 (by decide) (by decide)).trans z.desc,
    (c.saved .x28 (by decide) (by decide)).trans z.count,c.sp.trans z.sp,c.rd.trans z.rd,c.wr.trans z.wr⟩
  · have d : medD W+16 = W+240 := by change W+224#64+16#64 = W+240#64; simp [BitVec.add_assoc]
    simpa only [d] using stream
  · have k := (by decide : ∀ j ∈ medKept, j ∈ preserved ∧ j ≠ .x30) r hr
    exact (c.saved r k.1 k.2).trans (z.reg r hr)

theorem mediumKeys_rel {W K : Addr} {R n : Nat} {s t : State} (v : GcmImpl) (zeroScratch : v.ctr.scratch=0)
    (a : MediumKeysPre W K R n s) (b : MediumKeysPre W K R n t) (sp : s.sp=t.sp) (nonce : s.gpr .x23=t.gpr .x23) :
    RelCT isa (Eq2 s t) (Impl.AesGcm.AArch64.DirectGather.Medium.keys v.callees) TT := by
  refine rel_seq (rel_taint [.x19,.x23] sp (by agree_tac [a.x19,b.x19,nonce]) ⟨_,by taint_decide⟩)
    (mediumSeed_ok a) (mediumSeed_ok b) fun _ _ x y => ?_
  exact rel_ctrLe v.ctr (Nat.le_of_eq zeroScratch) x.call y.call (x.sp.trans (sp.trans y.sp.symm))

end VG.Proof.AesGcm.AArch64.DirectGather
