module

-- separate module: The standalone GHASH callee contract is independent of its AES-GCM caller and of the caller’s workspace layout.

public import VerifiedGarbage.Impl.Gcm.RISCV64.Prepared
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.Framework.RISCV64.MRun
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
public import VerifiedGarbage.Proof.Framework.RISCV64.Steps
public import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Gcm.RISCV64.Prepared.Block
public import VerifiedGarbage.Proof.Gcm.RISCV64.Lit
public import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Correctness and ABI preservation of the complete prepared GHASH update -/

@[expose] public section
namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64 VG.WriteBytes
structure CompactFrame (B : Addr) (s : State) : Prop where
  al : B.toNat % 16 = 0
  fit : B.toNat + 112 ≤ 2 ^ 64
  wr : (⟨B,112⟩ : Region) ∈ s.wr
theorem CompactFrame.of_wr {B : Addr} {s t : State} (h : CompactFrame B s) (z : t.wr = s.wr) : CompactFrame B t :=
  ⟨h.al,h.fit,z ▸ h.wr⟩
theorem CompactFrame.al8 {B : Addr} {s : State} (h : CompactFrame B s) {d : Nat} (hd : d % 8 = 0) (hd' : d < 112) :
    (B + BitVec.ofNat 64 d).toNat % 8 = 0 := Wp.al8 h.al hd (by omega_using [hd'])
theorem CompactFrame.inW {B : Addr} {s : State} (h : CompactFrame B s) {d : Nat} (hd : d + 8 ≤ 112) :
    InRegions s.wr (B + BitVec.ofNat 64 d) 8 :=
  ⟨_, h.wr, Offset.contains_base _ hd (by omega_using [hd])⟩
theorem CompactFrame.inR {B : Addr} {s : State} (h : CompactFrame B s) {d : Nat} (hd : d + 8 ≤ 112) :
    InRegions (s.rd++s.wr) (B + BitVec.ofNat 64 d) 8 := by
  obtain ⟨r,hr,hc⟩ := h.inW hd
  exact ⟨r,List.mem_append_right _ hr,hc⟩
def compactSaveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) : Mem :=
  compactSaved.foldl (fun m (r, d) => m.writeW (B + BitVec.ofNat 64 d) (g r)) m

theorem compact_save_ok (s : State) (hF : CompactFrame s.sp s) :
    WP isa (.block (.addSp .t0 0 :: compactSave ++ ([.addi FP HP 0, .addSp HP 0] : List Instr))) s fun t =>
      t.gpr FP = s.gpr HP ∧ t.gpr HP = s.sp ∧ Keep [.t0, .s9, .a0] s t ∧ t.sp = s.sp ∧ t.mem = compactSaveMem s.mem s.sp s.gpr := by
  obtain W : ∀ k, 4 ≤ k → k < 14 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions s.wr (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega_using [h2], hF.al8 (by omega_using []) (by omega_using [h2])⟩, hF.inW (by omega_using [h2])⟩
  obtain W0 := W 4 (by decide) (by decide); have W1 := W 5 (by decide) (by decide)
  obtain W2 := W 6 (by decide) (by decide); have W3 := W 7 (by decide) (by decide)
  obtain W4 := W 8 (by decide) (by decide); have W5 := W 9 (by decide) (by decide)
  obtain W6 := W 10 (by decide) (by decide); have W7 := W 11 (by decide) (by decide)
  obtain W8 := W 12 (by decide) (by decide); have W9 := W 13 (by decide) (by decide)
  simp only [Nat.reduceMul] at W0 W1 W2 W3 W4 W5 W6 W7 W8 W9
  simp only [compactSave, compactSaved, saved, slot, List.map, FP, HP, Nat.reduceMul, Nat.reduceSub, List.cons_append, List.nil_append, Nat.reduceMul, Nat.reduceSub]
  mrun [W0.1, W1.1, W2.1, W3.1, W4.1, W5.1, W6.1, W7.1, W8.1, W9.1,
    W0.2, W1.2, W2.2, W3.2, W4.2, W5.2, W6.2, W7.2, W8.2, W9.2]
  simp only [compactSaveMem, compactSaved, saved, slot, List.map, List.foldl, Nat.reduceMul, Nat.reduceSub]
  glue_close

theorem compact_restore_ok (s : State) (hF : CompactFrame s.sp s) (v : Reg → BitVec 64)
    (hm : ∀ p ∈ compactSaved, s.mem.readW (s.sp + BitVec.ofNat 64 p.2) 64 = v p.1) :
    WP isa (.block (.addSp .t0 0 :: compactRestore)) s fun t =>
      (∀ r ∈ savedRegs, t.gpr r = v r) ∧ Keep (.t0 :: savedRegs) s t ∧ t.mem = s.mem ∧ t.sp = s.sp := by
  obtain R : ∀ k, 4 ≤ k → k < 14 → (8 * k < 2048 ∧ (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0) ∧
      InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * k)) 8 :=
    fun k h1 h2 => ⟨⟨by omega_using [h2], hF.al8 (by omega_using []) (by omega_using [h2])⟩, hF.inR (by omega_using [h2])⟩
  obtain R0 := R 4 (by decide) (by decide); have R1 := R 5 (by decide) (by decide)
  obtain R2 := R 6 (by decide) (by decide); have R3 := R 7 (by decide) (by decide)
  obtain R4 := R 8 (by decide) (by decide); have R5 := R 9 (by decide) (by decide)
  obtain R6 := R 10 (by decide) (by decide); have R7 := R 11 (by decide) (by decide)
  obtain R8 := R 12 (by decide) (by decide); have R9 := R 13 (by decide) (by decide)
  simp only [Nat.reduceMul] at R0 R1 R2 R3 R4 R5 R6 R7 R8 R9
  obtain m0 := hm (.s0, 32) (by decide)
  obtain m1 := hm (.s1, 40) (by decide)
  obtain m2 := hm (.s2, 48) (by decide)
  obtain m3 := hm (.s3, 56) (by decide)
  obtain m4 := hm (.s4, 64) (by decide)
  obtain m5 := hm (.s5, 72) (by decide)
  obtain m6 := hm (.s6, 80) (by decide)
  obtain m7 := hm (.s7, 88) (by decide)
  obtain m8 := hm (.s8, 96) (by decide)
  obtain m9 := hm (.s9, 104) (by decide)
  simp only at m0 m1 m2 m3 m4 m5 m6 m7 m8 m9
  simp only [compactRestore, compactSaved, saved, slot, List.map, Nat.reduceMul, Nat.reduceSub]
  mrun [R0.1, R1.1, R2.1, R3.1, R4.1, R5.1, R6.1, R7.1, R8.1, R9.1,
    R0.2, R1.2, R2.2, R3.2, R4.2, R5.2, R6.2, R7.2, R8.2, R9.2, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9]
  refine ⟨fun r hr => ?_, ?_⟩
  · simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp only [savedRegs, saved, List.map]
    glue_close

/-! ## The function -/

/-- The saves, read back. -/
theorem readW_compactSaveMem (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    ∀ p ∈ compactSaved, (compactSaveMem m B g).readW (B + BitVec.ofNat 64 p.2) 64 = g p.1 := by
  intro p hp
  simp only [compactSaved, saved, slot, List.map, List.mem_cons, List.not_mem_nil, or_false, Nat.reduceMul, Nat.reduceSub] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega_using []) only [compactSaveMem, compactSaved, saved, slot, List.map, List.foldl, Nat.reduceMul, Nat.reduceSub, readW_wr_ne,
      Mem.readW_writeW_self64]

/-- The saves write inside the frame. -/
theorem compactSaveMem_frame (m : Mem) (B : Addr) (g : Reg → BitVec 64) :
    Frame [⟨B, 112⟩] m (compactSaveMem m B g) := by
  obtain c : ∀ d, d + 8 ≤ 112 → (⟨B, 112⟩ : Region).Contains (B + BitVec.ofNat 64 d) (64 / 8) :=
    fun d hd => Offset.contains_base _ hd (by omega_using [hd])
  simp only [compactSaveMem, compactSaved, saved, slot, List.map, List.foldl, Nat.reduceMul, Nat.reduceSub]
  repeat (first
    | exact Frame.refl _ _
    | refine Frame.writeW ?_ List.mem_cons_self _ (c _ (by decide)))


end VG.Proof.Gcm.RISCV64

namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

structure CachedPre (H : Block) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0,288⟩,⟨s.gpr .a2,16*(s.gpr .a3).toNat⟩]
  wr : s.wr = [⟨s.gpr .a1,16⟩,⟨s.gpr .a4,256⟩]
  tableAlign : (s.gpr .a0).toNat % 8 = 0
  stackTable : (⟨(allocd 112 s).sp,112⟩ : Region).Disjoint ⟨s.gpr .a0,288⟩
  stackY : (⟨(allocd 112 s).sp,112⟩ : Region).Disjoint ⟨s.gpr .a1,16⟩
  stackData : (⟨(allocd 112 s).sp,112⟩ : Region).Disjoint ⟨s.gpr .a2,16*(s.gpr .a3).toNat⟩
  fd : (s.gpr .a2).toNat + 16*(s.gpr .a3).toNat ≤ 2^64
  frame : CompactFrame (allocd 112 s).sp (allocd 112 s)
  key : ∃ h0 h1, H = h0 ++ h1 ∧ Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1)
    (fun d => s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 d) 64)

structure SplitHead (H : Block) (s a sY : State) : Prop where
  loop : SplitLoopPre H (s.gpr .a2) s.mem (s.gpr .a3).toNat sY
  inv : SplitInv H (blockAt s.mem (s.gpr .a1)) (s.gpr .a2) s.mem (s.gpr .a3).toNat sY 0 sY
  yp : sY.gpr YP=s.gpr .a1
  wr : sY.wr=a.wr
  sp : sY.sp=a.sp
  spill : sY.gpr .a0=a.sp
  slots : ∀ p ∈ compactSaved, sY.mem.readW (a.sp+BitVec.ofNat 64 p.2) 64=s.gpr p.1
  fy : Frame [⟨a.sp,112⟩] s.mem sY.mem

theorem cached_head_ok {H : Block} (s : State) (hp : CachedPre H s) :
    WP isa (.block (.addSp .t0 0 :: compactSave ++ [.addi FP HP 0, .addSp HP 0] ++ maskCode ++ loadY)) (allocd 112 s)
      (SplitHead H s (allocd 112 s)) := by
  set a := allocd 112 s with ha
  have ard : a.rd = s.rd := rfl
  have awr : a.wr = ⟨a.sp,112⟩ :: s.wr := rfl
  have amem : a.mem = s.mem := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (compact_save_ok a hp.frame) fun u1 ⟨fp1,sp1,k1,p1,m1⟩ => ?_
  refine WP.mono (maskCode_ok u1) fun u2 ⟨K2,k2,m2,p2⟩ => ?_
  obtain hYr : InRegions (u2.rd ++ u2.wr) (u2.gpr YP) 16 := by
    rw [k2.2.1,k2.2.2,Keep.gpr k2 (by decide),k1.2.1,k1.2.2,Keep.gpr k1 (by decide)]
    exact ⟨⟨s.gpr .a1,16⟩,List.mem_append_right _ (by rw [awr,hp.wr];simp),Region.contains_self _ _⟩
  refine WP.mono (ld2_ok (d₀ := Y0) (d₁ := Y1) (tmp := .t2) (n := YP) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) u2 hYr) fun sY ⟨y0,y1,k3,m3,p3⟩ => ?_
  obtain FY : Frame [⟨a.sp,112⟩] s.mem sY.mem := by
    rw [m3,m2,m1,←amem]; exact compactSaveMem_frame _ _ _
  have keep := Keep.trans k2 k3
  have total := Keep.trans k1 keep
  obtain fpY : sY.gpr FP=s.gpr .a0 := (Keep.gpr keep (by decide)).trans fp1
  obtain spillY : sY.gpr .a0=a.sp := (Keep.gpr keep (by decide)).trans sp1
  obtain hF : CompactFrame (sY.gpr .a0) sY := by rw [spillY]; exact hp.frame.of_wr total.2.2
  obtain dataY : sY.gpr DP = s.gpr .a2 := Keep.gpr total (by decide)
  obtain countY : sY.gpr N = s.gpr .a3 := Keep.gpr total (by decide)
  obtain keyRead : ∀ k < 36, Rd8 sY (8*k) := by
    intro k hk
    refine ⟨by omega_using [hk], ?_, ?_⟩
    · rw [fpY]
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a:=8*k) (by omega_using [hk])]
      have := (s.gpr .a0).isLt
      omega_using [hp.tableAlign]
    · rw [total.2.1,total.2.2,ard,hp.rd,fpY]
      exact ⟨_,List.mem_append_left _ List.mem_cons_self,Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  obtain S : SpillSlots sY .a0 0 := by
    refine ⟨by decide,fun k hk => ⟨by simp only [slot,Nat.zero_add];omega_using [hk], hF.al8 (by simp [slot]) (by simp only [slot,Nat.zero_add];omega_using [hk]),
      hF.inW (by simp only [slot,Nat.zero_add];omega_using [hk])⟩,?_⟩
    intro j hj k hk x hx hz
    rw [fpY] at hx
    simp only [spillY, slot, Nat.zero_add] at hz
    have shrink (B : Addr) {i n : Nat} (hi : 8*i + 8 ≤ n) (fit : n < 2^64) {x : Addr} (h : (x-(B+BitVec.ofNat 64 (8*i))).toNat < 8) :
        (⟨B,n⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]
      rw [Offset.toNat_sub_add x B (by omega_using [hi,fit])] at h
      omega_using [hi,fit,h]
    apply hp.stackTable x (shrink a.sp (i:=k) (by omega_using [hk]) (by decide) hz)
    exact shrink _ (i:=j) (by omega_using [hj]) (by decide) hx
  obtain keySame : ∀ k < 36, fw sY (8*k) = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (8*k)) 64 := by
    intro k hk
    unfold fw
    rw [fpY]
    exact FY.readW (Offset.contains_base (s.gpr .a0) (d:=8*k) (by omega_using [hk]) (by omega_using [hk]) :
      (⟨s.gpr .a0,288⟩ : Region).Contains _ (64/8)) (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hp.stackTable.symm) (by decide)
  obtain out : ∀ {m : Mem}, Frame [⟨a.sp,112⟩] s.mem m → ∀ {R : Region}, (⟨a.sp,112⟩ : Region).Disjoint R →
      R.len ≤ 2^64 → ∀ i < R.len, m (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
    fun hm R hd hR i hi => hm _ fun r hr hc => by
      simp only [List.mem_singleton] at hr
      subst r
      exact hd _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hR,hi]))
  obtain hYk : blockAt s.mem (s.gpr .a1) = w2 (sY.gpr Y0) (sY.gpr Y1) := by
    rw [y0, y1, Keep.gpr k2 (by decide), Keep.gpr k1 (by decide),
      show w2 (ByteLoad.be64 u2.mem (a.gpr YP) 0) (ByteLoad.be64 u2.mem (a.gpr YP) 8) = hOf u2.mem (s.gpr .a1) from rfl,
      ← blockAt_hOf, ← m3]
    exact (Proof.Gcm.blockAt_congr fun i hi => out FY (R := ⟨s.gpr .a1,16⟩) hp.stackY (by simp) i hi).symm
  refine ⟨⟨S,keyRead,Keep.masks k3 K2 (fun i hi => by interval_cases i <;> decide),?_,?_,?_⟩,
    ⟨?_,?_,?_,Keep.refl _ _,rfl,fun _ _ => rfl,Frame.refl _ _⟩,
    Keep.gpr total (by decide),total.2.2,p3.trans (p2.trans p1),spillY,?_,FY⟩
  · obtain ⟨h0,h1,hH,hk⟩ := hp.key
    exact ⟨h0,h1,hH,fun i hi j hj => (keySame (4*i+j) (by omega_using [hi,hj])).trans (hk i hi j hj)⟩
  · intro i hi
    rw [total.2.1,total.2.2,ard]
    exact ⟨⟨s.gpr .a2,16*(s.gpr .a3).toNat⟩,List.mem_append_left _ (by rw [hp.rd];simp),
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hp.fd,hi])⟩
  · intro i hi j hj m hm
    have hm' : Frame [⟨a.sp,112⟩] s.mem m := FY.trans (hm.sub fun r hr => ⟨_,List.mem_cons_self,by
      simp only [List.mem_singleton] at hr;subst r;rw [spillY];simpa using Offset.sub_base a.sp (d:=0) (n:=32) (k:=112) (by decide)⟩)
    have := out hm' hp.stackData (by simp;omega_using [hp.fd]) (16*i+j) (by simp;omega_using [hi,hj])
    rwa [BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  · rw [Proof.Gcm.ghashFrom_blocksAt_zero,hYk]
  · rw [dataY];simp
  · rw [countY,Nat.sub_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · intro p ht
    rw [m3,m2,m1]
    exact readW_compactSaveMem _ _ _ _ ht

end VG.Proof.Gcm.RISCV64

namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

theorem wipe14_ok (u : State) {B : Addr} (hR : (⟨B, 112⟩ : Region) ∈ u.wr) (hsp : u.sp = B)
    (hal : B.toNat % 16 = 0) :
    WP isa (.block (Impl.StackScratch.RISCV64.wipe 14)) u fun u' => Frame [⟨B, 112⟩] u.mem u'.mem ∧
      (∀ r, r ≠ .t5 → r ≠ .t6 → u'.gpr r = u.gpr r) ∧ u'.sp = u.sp := by
  obtain ⟨u', he, hf, ho, hs, -, -⟩ := wipe_run ⟨B, 112⟩ u 14 hR (by rw [hsp]; omega_using [hal])
    (fun k hk => by rw [hsp]; exact Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk]))
  exact ⟨_, _, Exec.block_iff.mpr he, hf, ho, hs⟩

theorem cached_tail_ok {H : Block} (s : State) (hp : CachedPre H s) (u : State) {Y : Block} (hy : w2 (u.gpr Y0) (u.gpr Y1) = Y)
    (hyp : u.gpr YP = s.gpr .a1) (hwrU : u.wr = (allocd 112 s).wr) (hsp : u.sp = (allocd 112 s).sp)
    (hslot : ∀ p ∈ compactSaved, u.mem.readW ((allocd 112 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1) :
    WP isa (.block (storeY ++ (.addSp .t0 0 :: compactRestore) ++ Impl.StackScratch.RISCV64.wipe 14)) u
      fun t => blockAt t.mem (s.gpr .a1) = Y ∧ (∀ r ∈ savedRegs, t.gpr r = s.gpr r) ∧ t.sp = u.sp := by
  obtain ⟨hrd, hwr, _, hsh, hsy, hsd, hfd, hF, _⟩ := hp
  set a := allocd 112 s with ha
  have awr : a.wr = ⟨a.sp, 112⟩ :: s.wr := rfl
  obtain hwy : ∀ off, off ≤ 8 → ∀ j < 8, InRegions u.wr (s.gpr .a1 + BitVec.ofNat 64 (off + j)) 1 :=
    fun off ho j hj => ⟨⟨s.gpr .a1, 16⟩, by rw [hwrU, awr, hwr]; simp,
      Offset.contains_base _ (by omega_using [ho, hj]) (by omega_using [ho, hj])⟩
  rw [WP.block_append_iff, WP.block_append_iff, storeY, WP.block_append_iff]
  refine WP.mono (ByteLoad.storeBE_ok (s := u) (v := Y0) (tmp := .t2) (n := YP) (off := 0) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [hyp]; exact hwy 0 (by decide)))
    fun s₁ e₁ => ?_
  subst e₁
  refine WP.mono (ByteLoad.storeBE_ok (v := Y1) (tmp := .t2) (n := YP) (off := 8) (w := 8)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; show ∀ j < 8, InRegions u.wr _ 1
        rw [hyp]; exact hwy 8 (by decide)))
    fun s₂ e₂ => ?_
  subst e₂
  simp only [RegUpd.gpr_write_of_ne _ _ (show YP ≠ .t2 by decide), RegUpd.gpr_write_of_ne _ _ (show Y1 ≠ .t2 by decide),
    hyp]
  obtain Fy : Frame [⟨s.gpr .a1, 16⟩] u.mem
      (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0) (ByteLoad.beBytes 8 (u.gpr Y0)))
        (s.gpr .a1 + BitVec.ofNat 64 8) (ByteLoad.beBytes 8 (u.gpr Y1))) :=
    (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide))).trans
      (writeBytes_frame _ _ _ (Offset.contains_base _ (by simp [ByteLoad.beBytes_length]) (by decide)))
  obtain hm : ∀ p ∈ compactSaved, (writeBytes (writeBytes u.mem (s.gpr .a1 + BitVec.ofNat 64 0)
      (ByteLoad.beBytes 8 (u.gpr Y0))) (s.gpr .a1 + BitVec.ofNat 64 8)
        (ByteLoad.beBytes 8 (u.gpr Y1))).readW (a.sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    obtain hd : 32 ≤ p.2 ∧ p.2 + 8 ≤ 112 := by
      simp only [compactSaved, saved, slot, List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain c : (⟨a.sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains (a.sp + BitVec.ofNat 64 p.2) 8 :=
      Region.contains_self _ _
    simp only [Mem.readW]
    rw [Frame.read Fy c (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
          exact sub_disj (Offset.sub_base _ (by omega_using [hd])) hsy) (by decide)]
    have := hslot p hp
    simp only [Mem.readW] at this
    exact this
  refine WP.mono (compact_restore_ok _ ?_ s.gpr ?_) fun s₃ ⟨r3, k4, m4, p4⟩ => ?_
  · simp only [RegUpd.sp_write, RegUpd.wr_write]; rw [hsp]; exact hF.of_wr hwrU
  · simp only [RegUpd.sp_write, RegUpd.mem_write]; rw [hsp]; exact hm
  obtain sp3 : s₃.sp = a.sp := by rw [p4]; simp only [RegUpd.sp_write]; exact hsp
  obtain hRw : (⟨a.sp, 112⟩ : Region) ∈ s₃.wr := by
    rw [k4.2.2]; simp only [RegUpd.wr_write]; rw [hwrU, awr]; exact List.mem_cons_self
  refine WP.mono (wipe14_ok s₃ hRw sp3 hF.al) fun t ⟨ft, gt, pt⟩ => ?_
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · have hyb : blockAt t.mem (s.gpr .a1) = blockAt s₃.mem (s.gpr .a1) :=
      Proof.Gcm.blockAt_congr fun i hi => ft _ fun r hr hc => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
        exact hsy _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
    rw [hyb, m4]
    simp only [RegUpd.mem_write]
    rw [blockAt_store, hy]
  · have h56 : r ≠ .t5 ∧ r ≠ .t6 := by
      simp only [savedRegs, saved, List.map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h56.1 h56.2, r3 r hr]
  · rw [pt, p4]; simp only [RegUpd.sp_write]


end VG.Proof.Gcm.RISCV64

namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.WriteBytes
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)


def hashDone (H : Block) (s t : State) : Prop := blockAt t.mem (s.gpr .a1) =
    ghashFrom H (blockAt s.mem (s.gpr .a1)) (blocksAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
theorem preparedHash_ok {H : Block} (s : State) (hp : CachedPre H s) (hsp : 112 ≤ s.sp.toNat) :
    WP isa cachedHash s fun s' => hashDone H s s' ∧ ∀ r ∈ savedRegs, s'.gpr r = s.gpr r := by

  refine WP.ite _ (eval_zero s N) (fun h0 => WP.block_nil ⟨?_, fun _ _ => rfl⟩) (fun h0 => ?_)
  · have hn : (s.gpr .a3).toNat = 0 := by
      have := beq_iff_eq.mp h0; simp [N] at this; simp [this]
    show blockAt s.mem (s.gpr .a1) = _
    rw [hn]; rfl
  obtain hpos : 0 < (s.gpr .a3).toNat := by
    have := beq_eq_false_iff_ne.mp h0
    refine Nat.pos_of_ne_zero fun h => this ?_
    exact BitVec.eq_of_toNat_eq (by simpa [N] using h)
  refine WP.allocLe ⟨by decide, by decide, by decide⟩ hsp ?_
  unfold cachedBody
  refine WP.seq (WP.mono (cached_head_ok s hp) fun sY hH => ?_)
  refine WP.seq (WP.mono (split_loop hH.loop (s.gpr .a3).isLt hpos hH.inv) fun sL hBL => ?_)
  have hfp := hH.spill
  obtain hslot : ∀ p ∈ compactSaved, sL.mem.readW ((allocd 112 s).sp + BitVec.ofNat 64 p.2) 64 = s.gpr p.1 := by
    intro p hp
    obtain hd : 32 ≤ p.2 ∧ p.2 + 8 ≤ 112 := by
      simp only [compactSaved, saved, slot, List.map, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    obtain c : (⟨(allocd 112 s).sp + BitVec.ofNat 64 p.2, 8⟩ : Region).Contains
        ((allocd 112 s).sp + BitVec.ofNat 64 p.2) 8 := Region.contains_self _ _
    have := hH.slots p hp
    simp only [Mem.readW] at this ⊢
    rw [Frame.read hBL.frame c (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      rw [hfp]; simpa using slot_disj (allocd 112 s).sp (d:=p.2) (e:=0) (n:=32) (by omega_using [hd]) (by omega_using [hd])) (by decide)]
    exact this
  obtain hyp : sL.gpr YP = s.gpr .a1 := by rw [Keep.gpr hBL.keep (by decide), hH.yp]
  obtain hwrL : sL.wr = (allocd 112 s).wr := by rw [hBL.keep.2.2, hH.wr]
  obtain hspL : sL.sp = (allocd 112 s).sp := by rw [hBL.sp, hH.sp]
  obtain T := cached_tail_ok s hp sL hBL.y hyp hwrL hspL hslot
  refine WP.mono T fun t h mL _ fl => ?_
  refine ⟨?_, fun r hr => h.2.1 r hr⟩
  have h1 := h.1
  simp only [hashDone] at h1 ⊢
  -- The `free` loses the frame's bytes, which lie apart from `Y`.
  exact Eq.trans (Proof.Gcm.blockAt_congr fun i hi =>
    lost_byte fl (R := ⟨s.gpr .a1, 16⟩) hp.stackY.symm hi) h1


theorem preparedHash_law {H : Block} (s : State) (hp : CachedPre H s) (hsp : 112 ≤ s.sp.toNat) :
    ∃ tr t, Exec isa cachedHash s tr t ∧ abiPreserved s t ∧ hashDone H s t := by
  obtain ⟨tr,t,hx,⟨post,hsv⟩,hkeep⟩ := WP.keep (.a0 :: written) (preparedHash_ok s hp hsp) (by lit_decide) (by lit_decide)
  refine ⟨tr,t,hx,⟨fun r hr => ?_,Exec.sp hx,hkeep.gpr (by decide)⟩,post⟩
  by_cases h : r ∈ saved.map Prod.fst
  · exact hsv r h
  · exact hkeep.gpr (by revert hr h; revert r; decide)
end VG.Proof.Gcm.RISCV64
