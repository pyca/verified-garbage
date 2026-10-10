import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackOne
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackValue
import VerifiedGarbage.Proof.Framework.Offset

/-! ## From `ResidentUnpackLoad.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_ldrq)

/-- Three overlapping vector loads consume exactly the packed sixteen-field
block. Their addresses are fixed by the public width. -/
theorem loads_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20)
    (h0 : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (h1 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (2*d-16)) 16) :
    WP isa (.block [.ldrq .v0 .x0 0,.ldrq .v1 .x0 16,
      .addImm .x .x9 .x0 (2*d-16),.ldrq .v2 .x9 0]) s fun t =>
      t.v .v0=s.mem.read (s.gpr .x0) 16 ∧
      t.v .v1=s.mem.read (s.gpr .x0+BitVec.ofNat 64 16) 16 ∧
      t.v .v2=s.mem.read (s.gpr .x0+BitVec.ofNat 64 (2*d-16)) 16 ∧
      (∀ r, r≠.x9 → t.gpr r=s.gpr r) ∧
      (∀ v, v≠.v0 → v≠.v1 → v≠.v2 → t.v v=s.v v) ∧
      t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  refine wp_ldrq (by decide) (by simp) h0 fun a ha => ?_
  refine wp_ldrq (by decide) rfl (by simpa only [ha.gpr,ha.rd,ha.wr] using h1) fun b hb => ?_
  let c := b.write .x .x9 (b.gpr .x0+BitVec.ofNat 64 (2*d-16))
  have hc : exec (.addImm .x .x9 .x0 (2*d-16)) b=some c := by
    simp only [exec,show 2*d-16<4096 by omega,ite_true,State.read,c,Size.bits,BitVec.setWidth_eq]
  refine WP.block_cons_iff.mpr ⟨c,hc,?_⟩
  have cg : c.gpr .x9=s.gpr .x0+BitVec.ofNat 64 (2*d-16) := by
    simp only [c,RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq,ite_true,hb.gpr,ha.gpr]
  refine wp_ldrq (a := s.gpr .x0+BitVec.ofNat 64 (2*d-16)) (by decide) (by simpa only [BitVec.add_zero] using cg)
    (by simpa only [show c.rd=b.rd from rfl,show c.wr=b.wr from rfl,hb.rd,hb.wr,ha.rd,ha.wr] using h2)
    fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.other .v0 (by decide),show c.v=b.v from rfl,hb.other .v0 (by decide),ha.v]
  · rw [ht.other .v1 (by decide),show c.v=b.v from rfl,hb.v,ha.mem,ha.gpr]
  · rw [ht.v,show c.mem=b.mem from rfl,hb.mem,ha.mem]
  · intro r hr
    rw [ht.gpr]
    simp only [c,RegUpd.gpr_write,hr,ite_false,hb.gpr,ha.gpr]
  · intro v hv0 hv1 hv2
    rw [ht.other v hv2,show c.v=b.v from rfl,hb.other v hv1,ha.other v hv0]
  · rw [ht.mem,show c.mem=b.mem from rfl,hb.mem,ha.mem]
  · rw [ht.rd,show c.rd=b.rd from rfl,hb.rd,ha.rd]
  · rw [ht.wr,show c.wr=b.wr from rfl,hb.wr,ha.wr]
  · rw [ht.sp,show c.sp=b.sp from rfl,hb.sp,ha.sp]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentUnpackFrame.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

/-- The parser never consumes the output-vector temporaries as table data. -/
theorem gatherValue_congr {v w : VReg → BitVec 128} (h0 : v .v0=w .v0)
    (h1 : v .v1=w .v1) (h2 : v .v2=w .v2) (d g : Nat) :
    gatherValue v d g=gatherValue w d g := by
  unfold gatherValue
  congr 1
  funext e
  let ix := (vbyte (gatherIndex d g) e).toNat
  change (if ix<48 then tableByte v .v0 ix else 0) =
    (if ix<48 then tableByte w .v0 ix else 0)
  split
  · rename_i h
    unfold tableByte
    have hi : ix/16=0 ∨ ix/16=1 ∨ ix/16=2 := by omega
    rcases hi with hi | hi | hi
    · simp only [hi,show Nat.repeat VReg.succ 0 .v0=.v0 from rfl,h0]
    · simp only [hi,show Nat.repeat VReg.succ 1 .v0=.v1 from rfl,h1]
    · simp only [hi,show Nat.repeat VReg.succ 2 .v0=.v2 from rfl,h2]
  · rfl

theorem parsedVector_congr {s t : State}
    (h0 : t.v .v0=s.v .v0) (h1 : t.v .v1=s.v .v1) (h2 : t.v .v2=s.v .v2)
    (h20 : t.v .v20=s.v .v20) (h21 : t.v .v21=s.v .v21)
    (h22 : t.v .v22=s.v .v22) (h23 : t.v .v23=s.v .v23) (d g : Nat) :
    parsedVector t d g=parsedVector s d g := by
  simp only [parsedVector,gatherValue_congr h0 h1 h2,h20,h21,h22,h23]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentUnpackInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

def initVectors : List VReg := [.v16,.v17,.v18,.v19,.v20,.v21,.v22,.v23]

private theorem constantLanes : ∀ d ∈ [18,20], ∀ e<4,
    vword (vectorValue ((List.range 4).map fun i => 2^((if d=20 then 4 else 6)-d*i%8))) e =
      BitVec.ofNat 32 (2^((if d=20 then 4 else 6)-d*e%8)) ∧
    vword (vectorValue [2^d-1,2^d-1,2^d-1,2^d-1]) e=BitVec.ofNat 32 (2^d-1) ∧
    vword (vectorValue [8380417,8380417,8380417,8380417]) e=8380417#32 ∧
    vword (vectorValue [2^(d-1),2^(d-1),2^(d-1),2^(d-1)]) e=BitVec.ofNat 32 (2^(d-1)) := by
  decide +kernel

private theorem init_code {d : Nat} (hd : d=18 ∨ d=20) : Unpack.init d =
    (Unpack.byteIndices .v16 (Unpack.indices d 0)) ++
    (Unpack.byteIndices .v17 (Unpack.indices d 1)) ++
    (Unpack.byteIndices .v18 (Unpack.indices d 2)) ++
    (Unpack.byteIndices .v19 (Unpack.indices d 3)) ++
    (Unpack.vector .v23 ((List.range 4).map fun i => 2^((if d=20 then 4 else 6)-d*i%8))) ++
    (Unpack.vector .v22 [2^d-1,2^d-1,2^d-1,2^d-1]) ++
    (Unpack.vector .v20 [8380417,8380417,8380417,8380417]) ++
    (Unpack.vector .v21 [2^(d-1),2^(d-1),2^(d-1),2^(d-1)]) ++
    ([.movz .x .x11 16 0] : List Instr) := by
    have hn : ¬ d=10 := by omega
    simp only [Unpack.init,ite_eq_right hn,show List.range 4=[0,1,2,3] from rfl,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,
      show Unpack.idxRegs[0]! = .v16 from rfl,show Unpack.idxRegs[1]! = .v17 from rfl,
      show Unpack.idxRegs[2]! = .v18 from rfl,show Unpack.idxRegs[3]! = .v19 from rfl,
      List.append_assoc,Impl.MlDsa.AArch64.Pack.qNat]


/-- Initialize all table indices, per-lane powers, masks and the public
sixteen-group counter, without touching input or output memory. -/
theorem init_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20) :
    WP isa (.block (Unpack.init d)) s fun t =>
      ParseConstants d t ∧
      (∀ g<4, t.v Unpack.idxRegs[g]! = gatherIndex d g) ∧
      t.gpr .x11=16 ∧
      (∀ r, r≠.x9 → r≠.x11 → t.gpr r=s.gpr r) ∧
      (∀ v, v∉initVectors → t.v v=s.v v) ∧
      t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  rw [init_code hd]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (indexConst_ok s .v16 hd (by decide : 0<4)) ?_
  intro a0 h0
  rw [WP.block_append_iff]
  refine WP.mono (indexConst_ok a0 .v17 hd (by decide : 1<4)) ?_
  intro a1 h1
  rw [WP.block_append_iff]
  refine WP.mono (indexConst_ok a1 .v18 hd (by decide : 2<4)) ?_
  intro a2 h2
  rw [WP.block_append_iff]
  refine WP.mono (indexConst_ok a2 .v19 hd (by decide : 3<4)) ?_
  intro a3 h3
  rw [WP.block_append_iff]
  refine WP.mono (vectorConst_ok a3 .v23 _) ?_
  intro a4 h4
  rw [WP.block_append_iff]
  refine WP.mono (vectorConst_ok a4 .v22 _) ?_
  intro a5 h5
  rw [WP.block_append_iff]
  refine WP.mono (vectorConst_ok a5 .v20 _) ?_
  intro a6 h6
  rw [WP.block_append_iff]
  refine WP.mono (vectorConst_ok a6 .v21 _) ?_
  intro a7 h7
  let t := a7.write .x .x11 16
  refine WP.block_cons_iff.mpr ⟨t,rfl,WP.block_nil_iff.mpr ?_⟩
  have tv : t.v=a7.v := rfl
  have v16 : t.v .v16 = gatherIndex d 0 := by
    rw [tv,h7.1.vec .v16 (by decide),h6.1.vec .v16 (by decide),h5.1.vec .v16 (by decide),h4.1.vec .v16 (by decide),h3.1.vec .v16 (by decide),h2.1.vec .v16 (by decide),h1.1.vec .v16 (by decide),h0.2]
  have v17 : t.v .v17 = gatherIndex d 1 := by
    rw [tv,h7.1.vec .v17 (by decide),h6.1.vec .v17 (by decide),h5.1.vec .v17 (by decide),h4.1.vec .v17 (by decide),h3.1.vec .v17 (by decide),h2.1.vec .v17 (by decide),h1.2]
  have v18 : t.v .v18 = gatherIndex d 2 := by
    rw [tv,h7.1.vec .v18 (by decide),h6.1.vec .v18 (by decide),h5.1.vec .v18 (by decide),h4.1.vec .v18 (by decide),h3.1.vec .v18 (by decide),h2.2]
  have v19 : t.v .v19 = gatherIndex d 3 := by
    rw [tv,h7.1.vec .v19 (by decide),h6.1.vec .v19 (by decide),h5.1.vec .v19 (by decide),h4.1.vec .v19 (by decide),h3.2]
  have v23 : t.v .v23 = vectorValue ((List.range 4).map fun i => 2^((if d=20 then 4 else 6)-d*i%8)) := by
    rw [tv,h7.1.vec .v23 (by decide),h6.1.vec .v23 (by decide),h5.1.vec .v23 (by decide),h4.2]
  have v22 : t.v .v22 = vectorValue [2^d-1,2^d-1,2^d-1,2^d-1] := by
    rw [tv,h7.1.vec .v22 (by decide),h6.1.vec .v22 (by decide),h5.2]
  have v20 : t.v .v20 = vectorValue [8380417,8380417,8380417,8380417] := by
    rw [tv,h7.1.vec .v20 (by decide),h6.2]
  have v21 : t.v .v21 = vectorValue [2^(d-1),2^(d-1),2^(d-1),2^(d-1)] := by
    rw [tv,h7.2]
  have hl := constantLanes d (by rcases hd with rfl | rfl <;> simp) 
  refine ⟨⟨?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro e he; rw [v23]; exact (hl e he).1
  · intro e he; rw [v22]; exact (hl e he).2.1
  · intro e he; rw [v21]; exact (hl e he).2.2.2
  · intro e he; rw [v20]; exact (hl e he).2.2.1
  · intro g hg
    rcases (show g=0 ∨ g=1 ∨ g=2 ∨ g=3 by omega) with rfl | rfl | rfl | rfl
    · exact v16
    · exact v17
    · exact v18
    · exact v19
  · rfl
  · intro r hr9 hr11
    change (if r=.x11 then 16 else a7.gpr r)=s.gpr r
    rw [ite_eq_right hr11,h7.1.gpr r hr9,h6.1.gpr r hr9,h5.1.gpr r hr9,h4.1.gpr r hr9,h3.1.gpr r hr9,h2.1.gpr r hr9,h1.1.gpr r hr9,h0.1.gpr r hr9]
  · intro v hv
    have hn : ∀ r ∈ initVectors, v≠r := by intro r hr he; exact hv (he ▸ hr)
    rw [tv,h7.1.vec v (hn .v21 (by decide)),h6.1.vec v (hn .v20 (by decide)),h5.1.vec v (hn .v22 (by decide)),h4.1.vec v (hn .v23 (by decide)),h3.1.vec v (hn .v19 (by decide)),h2.1.vec v (hn .v18 (by decide)),h1.1.vec v (hn .v17 (by decide)),h0.1.vec v (hn .v16 (by decide))]
  · change a7.mem=s.mem
    rw [h7.1.mem,h6.1.mem,h5.1.mem,h4.1.mem,h3.1.mem,h2.1.mem,h1.1.mem,h0.1.mem]
  · change a7.rd=s.rd
    rw [h7.1.rd,h6.1.rd,h5.1.rd,h4.1.rd,h3.1.rd,h2.1.rd,h1.1.rd,h0.1.rd]
  · change a7.wr=s.wr
    rw [h7.1.wr,h6.1.wr,h5.1.wr,h4.1.wr,h3.1.wr,h2.1.wr,h1.1.wr,h0.1.wr]
  · change a7.sp=s.sp
    rw [h7.1.sp,h6.1.sp,h5.1.sp,h4.1.sp,h3.1.sp,h2.1.sp,h1.1.sp,h0.1.sp]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentUnpackCounter.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64

/-- Advance one public sixteen-field group. The counter controls a fixed
sixteen-iteration loop and does not depend on sampled data. -/
theorem advance_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20) :
    WP isa (.block [.addImm .x .x0 .x0 (2*d),.addImm .x .x4 .x4 64,
      .subImm .x .x11 .x11 1]) s fun t =>
      t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (2*d) ∧
      t.gpr .x4=s.gpr .x4+64 ∧ t.gpr .x11=s.gpr .x11-1 ∧
      (∀ r, r≠.x0 → r≠.x4 → r≠.x11 → t.gpr r=s.gpr r) ∧
      t.v=s.v ∧ t.mem=s.mem ∧ t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  let a := s.write .x .x0 (s.gpr .x0+BitVec.ofNat 64 (2*d))
  let b := a.write .x .x4 (a.gpr .x4+64)
  let t := b.write .x .x11 (b.gpr .x11-1)
  refine WP.block_cons_iff.mpr ⟨a,by simp [isa,exec,show 2*d<4096 by omega,State.read,a],?_⟩
  refine WP.block_cons_iff.mpr ⟨b,rfl,?_⟩
  refine WP.block_cons_iff.mpr ⟨t,rfl,?_⟩
  apply WP.block_nil_iff.mpr
  dsimp only [t,b,a]
  simp only [RegUpd.gpr_write,Size.bits,BitVec.setWidth_eq]
  simp only [show Reg.x0≠.x11 by decide,show Reg.x0≠.x4 by decide,
    show Reg.x4≠.x11 by decide,show Reg.x4≠.x0 by decide,
    show Reg.x11≠.x4 by decide,show Reg.x11≠.x0 by decide,ite_false,ite_true,true_and]
  constructor
  · intro r h0 h4 h11
    simp only [h0,h4,h11,ite_false]
  · exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentUnpackGroups.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

def groupTemps : List VReg := [.v4,.v5,.v6,.v7,.v24]

structure GroupKeep (s t : State) : Prop where
  gpr : t.gpr=s.gpr
  vec : ∀ v, v∉groupTemps → t.v v=s.v v
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

def groupMem (s : State) (d : Nat) : Nat → Mem
  | 0 => s.mem
  | n+1 => (groupMem s d n).write (s.gpr .x4+BitVec.ofNat 64 (16*n)) 16 (parsedVector s d n)

theorem groupMem_frame (s : State) (d : Nat) {n : Nat} (hn : n≤4) :
    Frame [⟨s.gpr .x4,64⟩] s.mem (groupMem s d n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    exact (ih (by omega)).write (r := ⟨s.gpr .x4,64⟩) (by simp) _ (Offset.contains_base _ (by omega) (by omega))

theorem groupMem_read (s : State) (d : Nat) {n g : Nat} (hn : n≤4) (hg : g<n) :
    (groupMem s d n).read (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16=parsedVector s d g := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [groupMem]
    by_cases he : g=n
    · subst g
      simpa only [Mem.readW,Mem.writeW,Nat.reduceMul,Nat.reduceDiv,BitVec.setWidth_eq] using
        Mem.readW_writeW_self (groupMem s d n) _ 16 (parsedVector s d n) (by decide)
    · rw [Mem.read_write_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact ih (by omega) (by omega)

theorem GroupKeep.parsed {s t : State} (h : GroupKeep s t) (d g : Nat) :
    parsedVector t d g=parsedVector s d g :=
  parsedVector_congr (h.vec .v0 (by decide)) (h.vec .v1 (by decide))
    (h.vec .v2 (by decide)) (h.vec .v20 (by decide)) (h.vec .v21 (by decide))
    (h.vec .v22 (by decide)) (h.vec .v23 (by decide)) d g

/-- All four unrolled groups preserve their common input vectors and constants;
the only memory writes are the four adjacent sixteen-byte output chunks. -/
theorem groups_ok (s : State) {d n : Nat} (hd : d=18 ∨ d=20) (hn : n≤4)
    (hi : ∀ g<4, s.v Unpack.idxRegs[g]! = gatherIndex d g)
    (hw : ∀ g<4, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (.block ((List.range n).flatMap (Unpack.one d))) s fun t =>
      GroupKeep s t ∧ t.mem=groupMem s d n := by
  induction n with
  | zero =>
    exact WP.block_nil_iff.mpr ⟨⟨rfl,fun _ _ => rfl,rfl,rfl,rfl⟩,rfl⟩
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (ih (by omega)) ?_
    intro a ha
    have hn4 : n<4 := by omega
    have hnidx : Unpack.idxRegs[n]! ∉groupTemps := by
      rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl | rfl | rfl | rfl <;> decide
    have hout : Unpack.outRegs[n]! ∈groupTemps := by
      rcases (show n=0 ∨ n=1 ∨ n=2 ∨ n=3 by omega) with rfl | rfl | rfl | rfl <;> decide
    refine WP.mono (one_ok a hd hn4 (by rw [ha.1.vec _ hnidx]; exact hi n hn4)
      (by simpa only [ha.1.wr,ha.1.gpr] using hw n hn4)) ?_
    intro t ht
    refine ⟨⟨ht.1.trans ha.1.gpr,?_,ht.2.2.2.1.trans ha.1.rd,
      ht.2.2.2.2.1.trans ha.1.wr,ht.2.2.2.2.2.trans ha.1.sp⟩,?_⟩
    · intro v hv
      have hr : v≠Unpack.outRegs[n]! := by intro he; exact hv (he ▸ hout)
      have h24 : v≠.v24 := by intro he; subst v; exact hv (by decide)
      rw [ht.2.1 v hr h24,ha.1.vec v hv]
    · rw [ht.2.2.1,ha.2,ha.1.gpr,ha.1.parsed]
      rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentUnpackBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

def bodyTemps : List VReg := [.v0,.v1,.v2,.v4,.v5,.v6,.v7,.v24]

structure ParseReady (d : Nat) (s : State) : Prop where
  constants : ParseConstants d s
  indices : ∀ g<4, s.v Unpack.idxRegs[g]! = gatherIndex d g

theorem ParseReady.keep {d : Nat} {s t : State} (h : ParseReady d s)
    (hv : ∀ v, v∈initVectors → t.v v=s.v v) : ParseReady d t := by
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  · intro e he; rw [hv .v23 (by decide)]; exact h.constants.powers e he
  · intro e he; rw [hv .v22 (by decide)]; exact h.constants.mask e he
  · intro e he; rw [hv .v21 (by decide)]; exact h.constants.bound e he
  · intro e he; rw [hv .v20 (by decide)]; exact h.constants.modulus e he
  · intro g hg
    rw [hv _ (by rcases (show g=0 ∨ g=1 ∨ g=2 ∨ g=3 by omega) with rfl | rfl | rfl | rfl <;> decide)]
    exact h.indices g hg

structure BodyPost (d : Nat) (s t : State) : Prop where
  ready : ParseReady d t
  input : t.gpr .x0=s.gpr .x0+BitVec.ofNat 64 (2*d)
  output : t.gpr .x4=s.gpr .x4+64
  count : t.gpr .x11=s.gpr .x11-1
  gpr : ∀ r, r≠.x0 → r≠.x4 → r≠.x9 → r≠.x11 → t.gpr r=s.gpr r
  vec : ∀ v, v∉bodyTemps → t.v v=s.v v
  frame : Frame [⟨s.gpr .x4,64⟩] s.mem t.mem
  values : ∀ g<4, ∀ e<4,
    (vword (t.mem.read (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16) e).toNat =
      (2^(d-1)+8380417-fieldValue s.mem (s.gpr .x0) d (4*g+e))%8380417
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

private theorem body_code {d : Nat} (hd : d=18 ∨ d=20) : Unpack.body d =
    ([.ldrq .v0 .x0 0,.ldrq .v1 .x0 16,.addImm .x .x9 .x0 (2*d-16),.ldrq .v2 .x9 0] : List Instr) ++
    ((List.range 4).flatMap (Unpack.one d)) ++
    ([.addImm .x .x0 .x0 (2*d),.addImm .x .x4 .x4 64,.subImm .x .x11 .x11 1] : List Instr) := by
  simp only [Unpack.body,ite_eq_right (by omega : ¬ d=10),List.cons_append,List.nil_append]

/-- One fixed-count parser iteration consumes sixteen packed fields and
produces their canonical coefficients in sixty-four bytes. -/
theorem body_ok (s : State) {d : Nat} (hd : d=18 ∨ d=20) (hr : ParseReady d s)
    (h0 : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (h1 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 16) 16)
    (h2 : InRegions (s.rd++s.wr) (s.gpr .x0+BitVec.ofNat 64 (2*d-16)) 16)
    (hw : ∀ g<4, InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (.block (Unpack.body d)) s (BodyPost d s) := by
  rw [body_code hd,List.append_assoc,WP.block_append_iff]
  refine WP.mono (loads_ok s hd h0 h1 h2) ?_
  intro a ha
  have ac : ParseReady d a := hr.keep fun v hv => ha.2.2.2.2.1 v
    (by intro h; subst v; simp [initVectors] at hv)
    (by intro h; subst v; simp [initVectors] at hv)
    (by intro h; subst v; simp [initVectors] at hv)
  rw [WP.block_append_iff]
  refine WP.mono (groups_ok a hd (Nat.le_refl 4) ac.indices ?_) ?_
  · intro g hg
    simpa only [ha.2.2.2.2.2.2.2.1,ha.2.2.2.1 .x4 (by decide)] using hw g hg
  intro b hb
  have bc : ParseReady d b := ac.keep fun v hv => hb.1.vec v
    (by simp only [initVectors,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine WP.mono (advance_ok b hd) ?_
  intro t ht
  refine ⟨bc.keep (fun v _ => congrFun ht.2.2.2.2.1 v),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [ht.1,hb.1.gpr,ha.2.2.2.1 .x0 (by decide)]
  · rw [ht.2.1,hb.1.gpr,ha.2.2.2.1 .x4 (by decide)]
  · rw [ht.2.2.1,hb.1.gpr,ha.2.2.2.1 .x11 (by decide)]
  · intro r h0 h4 h9 h11
    rw [ht.2.2.2.1 r h0 h4 h11,hb.1.gpr,ha.2.2.2.1 r h9]
  · intro v hv
    have hn : v≠.v0 ∧ v≠.v1 ∧ v≠.v2 ∧ v∉groupTemps := by
      simpa only [bodyTemps,groupTemps,List.mem_cons,List.not_mem_nil,or_false,not_or] using hv
    rw [ht.2.2.2.2.1,hb.1.vec v hn.2.2.2,ha.2.2.2.2.1 v hn.1 hn.2.1 hn.2.2.1]
  · rw [ht.2.2.2.2.2.1,hb.2,← ha.2.2.2.2.2.1,← ha.2.2.2.1 .x4 (by decide)]
    exact groupMem_frame a d (Nat.le_refl 4)
  · intro g hg e he
    rw [ht.2.2.2.2.2.1,hb.2,← ha.2.2.2.1 .x4 (by decide),groupMem_read a d (Nat.le_refl 4) hg]
    exact parsed_word hd hg he ac.constants ha.1 ha.2.1 ha.2.2.1
  · exact ht.2.2.2.2.2.2.1.trans (hb.1.rd.trans ha.2.2.2.2.2.2.1)
  · exact ht.2.2.2.2.2.2.2.1.trans (hb.1.wr.trans ha.2.2.2.2.2.2.2.1)
  · exact ht.2.2.2.2.2.2.2.2.trans (hb.1.sp.trans ha.2.2.2.2.2.2.2.2)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
