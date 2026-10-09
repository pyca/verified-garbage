import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackValue

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask
open VG.Proof.MlKem.AArch64 (wp_vop wp_strq)

def parsedVector (s : State) (d g : Nat) : BitVec 128 :=
  correctVec (alignVec (gatherValue s.v d g) (s.v .v23) (s.v .v22)
    (if d=20 then 4 else 6)) (s.v .v21) (s.v .v20)

/-- One parser group writes four coefficients and leaves every other memory
byte alone. Constants and the three overlapping input vectors are preserved. -/
theorem one_ok (s : State) {d g : Nat} (hd : d=18 ∨ d=20) (hg : g<4)
    (hi : s.v Unpack.idxRegs[g]! = gatherIndex d g)
    (hw : InRegions s.wr (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16) :
    WP isa (.block (Unpack.one d g)) s fun t =>
      t.gpr=s.gpr ∧
      (∀ v, v≠Unpack.outRegs[g]! → v≠.v24 → t.v v=s.v v) ∧
      t.mem=s.mem.write (s.gpr .x4+BitVec.ofNat 64 (16*g)) 16 (parsedVector s d g) ∧
      t.rd=s.rd ∧ t.wr=s.wr ∧ t.sp=s.sp := by
  have hn : ¬ d=10 := by omega
  let r := Unpack.outRegs[g]!
  have hr : r≠.v0 ∧ r≠.v1 ∧ r≠.v2 ∧ r≠.v20 ∧ r≠.v21 ∧ r≠.v22 ∧ r≠.v23 ∧ r≠.v24 := by
    rcases (show g=0 ∨ g=1 ∨ g=2 ∨ g=3 by omega) with rfl | rfl | rfl | rfl <;> decide
  have code : Unpack.one d g =
      [.vop (.tblN false 3 r .v0 Unpack.idxRegs[g]!)] ++
      [.vop (.mul r r .v23),.vop (.shift .ushr .s4 r r (if d=20 then 4 else 6)),
       .vop (.logic .and r r .v22),.vop (.sub .s4 r .v21 r),
       .vop (.shift .sshr .s4 .v24 r 31),.vop (.logic .and .v24 .v24 .v20),
       .vop (.add .s4 r r .v24)] ++ [.strq r .x4 (16*g)] := by
    simp only [Unpack.one,ite_eq_right hn]
    rfl
  rw [code]
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := r) (x := gatherValue s.v d g) (by simp only [VOp.eval,hi]; rfl) fun a ha => ?_
  rw [show ([Instr.vop (.mul r r .v23),.vop (.shift .ushr .s4 r r (if d=20 then 4 else 6)),
      .vop (.logic .and r r .v22),.vop (.sub .s4 r .v21 r),
      .vop (.shift .sshr .s4 .v24 r 31),.vop (.logic .and .v24 .v24 .v20),
      .vop (.add .s4 r r .v24),.strq r .x4 (16*g)] : List Instr) =
      ([.vop (.mul r r .v23),.vop (.shift .ushr .s4 r r (if d=20 then 4 else 6)),
      .vop (.logic .and r r .v22),.vop (.sub .s4 r .v21 r),
      .vop (.shift .sshr .s4 .v24 r 31),.vop (.logic .and .v24 .v24 .v20),
      .vop (.add .s4 r r .v24)] : List Instr) ++ [.strq r .x4 (16*g)] from rfl,
    WP.block_append_iff]
  refine WP.mono (arithmetic_ok a r hd hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.2) ?_
  intro b hb
  have hv : b.v r=parsedVector s d g := by
    rw [hb.2,ha.v,ha.other .v23 (Ne.symm hr.2.2.2.2.2.2.1),
      ha.other .v22 (Ne.symm hr.2.2.2.2.2.1),ha.other .v21 (Ne.symm hr.2.2.2.2.1),
      ha.other .v20 (Ne.symm hr.2.2.2.1)]
    rfl
  refine wp_strq (by omega) rfl (by simpa only [hb.1.wr,ha.wr,hb.1.gpr,ha.gpr] using hw)
    fun t ht => WP.block_nil_iff.mpr ?_
  refine ⟨ht.gpr.trans (hb.1.gpr.trans ha.gpr),?_,?_,
    ht.rd.trans (hb.1.rd.trans ha.rd),ht.wr.trans (hb.1.wr.trans ha.wr),
    ht.sp.trans (hb.1.sp.trans ha.sp)⟩
  · intro v hv hv24
    rw [ht.v,hb.1.vec v hv hv24,ha.other v hv]
  · rw [ht.mem,hv,hb.1.mem,ha.mem,hb.1.gpr,ha.gpr]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
