import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackValue

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
