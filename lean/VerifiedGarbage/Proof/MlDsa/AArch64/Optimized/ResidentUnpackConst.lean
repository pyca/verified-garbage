import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackGather
import VerifiedGarbage.Proof.MlKem.AArch64.Vec

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask
open VG.Proof.MlKem.AArch64 (wp_vop)

structure ConstKeep (d : VReg) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → t.gpr r=s.gpr r
  vec : ∀ r, r ≠ d → t.v r=s.v r
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

/-- Build a full vector constant using the selected caller-saved scalar
register, without changing any other vector. -/
theorem pairConst_ok (s : State) (d : VReg) (lo hi : BitVec 64) :
    WP isa (.block (Impl.MlKem.AArch64.movImm .x9 lo ++
      ([.vop (.dup .d2 d .x9)] : List Instr) ++ Impl.MlKem.AArch64.movImm .x9 hi ++
      ([.vop (.ins .d2 d 1 .x9)] : List Instr))) s fun t =>
      ConstKeep d s t ∧ t.v d=ofVDwords lo hi := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 lo) ?_
  intro a ha
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := d) rfl fun b hb => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok b .x9 hi) ?_
  intro c hc
  refine wp_vop (d := d) rfl fun t ht => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr => ?_,fun r hr => ?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,hc.2.1 r hr,hb.gpr,ha.2.1 r hr]
    · rw [ht.other r hr,hc.2.2,hb.other r hr,ha.2.2]
    · rw [ht.mem,hc.2.2,hb.mem,ha.2.2]
    · rw [ht.rd,hc.2.2,hb.rd,ha.2.2]
    · rw [ht.wr,hc.2.2,hb.wr,ha.2.2]
    · rw [ht.sp,hc.2.2,hb.sp,ha.2.2]
  · rw [ht.v,hc.1,hc.2.2,hb.v,ha.1]
    exact setLane_pair_hi _ _ _

def bytesValue (xs : List Nat) : BitVec 128 :=
  let lo := ((List.range 8).map fun i => xs[i]! * 2^(8*i)).foldl (·+·) 0
  let hi := ((List.range 8).map fun i => xs[i+8]! * 2^(8*i)).foldl (·+·) 0
  ofVDwords (BitVec.ofNat 64 lo) (BitVec.ofNat 64 hi)

theorem byteIndices_ok (s : State) (d : VReg) (xs : List Nat) :
    WP isa (.block (Unpack.byteIndices d xs)) s fun t =>
      ConstKeep d s t ∧ t.v d=bytesValue xs := by
  exact pairConst_ok s d _ _

private theorem indexValue18 : ∀ g<4, bytesValue (Unpack.indices 18 g)=gatherIndex 18 g := by
  decide +kernel
private theorem indexValue20 : ∀ g<4, bytesValue (Unpack.indices 20 g)=gatherIndex 20 g := by
  decide +kernel

theorem indexValue_eq {d g : Nat} (hd : d=18 ∨ d=20) (hg : g<4) :
    bytesValue (Unpack.indices d g)=gatherIndex d g := by
  rcases hd with rfl | rfl
  · exact indexValue18 g hg
  · exact indexValue20 g hg

theorem indexConst_ok (s : State) (r : VReg) {d g : Nat} (hd : d=18 ∨ d=20) (hg : g<4) :
    WP isa (.block (Unpack.byteIndices r (Unpack.indices d g))) s fun t =>
      ConstKeep r s t ∧ t.v r=gatherIndex d g := by
  simpa only [indexValue_eq hd hg] using byteIndices_ok s r (Unpack.indices d g)


theorem ConstKeep.trans {d : VReg} {s t u : State} (h : ConstKeep d s t) (k : ConstKeep d t u) :
    ConstKeep d s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr),
   fun r hr => (k.vec r hr).trans (h.vec r hr),k.mem.trans h.mem,k.rd.trans h.rd,
   k.wr.trans h.wr,k.sp.trans h.sp⟩

theorem dupConst_ok (s : State) (d : VReg) (v : BitVec 64) :
    WP isa (.block (Impl.MlKem.AArch64.movImm .x9 v ++
      ([.vop (.dup .s4 d .x9)] : List Instr))) s fun t =>
      ConstKeep d s t ∧ t.v d=ofVWords (v.setWidth 32) (v.setWidth 32) (v.setWidth 32) (v.setWidth 32) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 v) ?_
  intro a ha
  refine wp_vop (d := d) rfl fun t ht => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr => ?_,fun r hr => ?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,ha.2.1 r hr]
    · rw [ht.other r hr,ha.2.2]
    · rw [ht.mem,ha.2.2]
    · rw [ht.rd,ha.2.2]
    · rw [ht.wr,ha.2.2]
    · rw [ht.sp,ha.2.2]
  · rw [ht.v,ha.1]

theorem insertConst_ok (s : State) (d : VReg) (v : BitVec 64) {i : Nat} (hi : i<4) :
    WP isa (.block (Impl.MlKem.AArch64.movImm .x9 v ++
      ([.vop (.ins .s4 d i .x9)] : List Instr))) s fun t =>
      ConstKeep d s t ∧ t.v d=setLane (s.v d) 32 i (v.setWidth 32) := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.AArch64.Tbl.const64_ok s .x9 v) ?_
  intro a ha
  refine wp_vop (d := d) (x := setLane (a.v d) 32 i ((a.gpr .x9).setWidth 32))
    (by simp [VOp.eval,hi]) fun t ht =>
    WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨fun r hr => ?_,fun r hr => ?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,ha.2.1 r hr]
    · rw [ht.other r hr,ha.2.2]
    · rw [ht.mem,ha.2.2]
    · rw [ht.rd,ha.2.2]
    · rw [ht.wr,ha.2.2]
    · rw [ht.sp,ha.2.2]
  · rw [ht.v,ha.1,ha.2.2]


def vectorValue (xs : List Nat) : BitVec 128 :=
  let a := BitVec.ofNat 32 xs[0]!
  setLane (setLane (setLane (ofVWords a a a a) 32 1 (BitVec.ofNat 32 xs[1]!))
    32 2 (BitVec.ofNat 32 xs[2]!)) 32 3 (BitVec.ofNat 32 xs[3]!)

theorem vectorConst_ok (s : State) (d : VReg) (xs : List Nat) :
    WP isa (.block (Unpack.vector d xs)) s fun t => ConstKeep d s t ∧ t.v d=vectorValue xs := by
  let head := Impl.MlKem.AArch64.movImm .x9 (BitVec.ofNat 64 xs[0]!) ++
    ([.vop (.dup .s4 d .x9)] : List Instr)
  let ins (i : Nat) := Impl.MlKem.AArch64.movImm .x9 (BitVec.ofNat 64 xs[i]!) ++
    ([.vop (.ins .s4 d i .x9)] : List Instr)
  have he : Unpack.vector d xs=head ++ ins 1 ++ ins 2 ++ ins 3 := by rfl
  rw [he]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (dupConst_ok s d _) ?_
  intro a ha
  rw [WP.block_append_iff]
  refine WP.mono (insertConst_ok a d _ (by decide : 1<4)) ?_
  intro b hb
  rw [WP.block_append_iff]
  refine WP.mono (insertConst_ok b d _ (by decide : 2<4)) ?_
  intro c hc
  refine WP.mono (insertConst_ok c d _ (by decide : 3<4)) ?_
  intro t ht
  refine ⟨((ha.1.trans hb.1).trans hc.1).trans ht.1,?_⟩
  rw [ht.2,hc.2,hb.2,ha.2]
  simp only [vectorValue,BitVec.setWidth_ofNat_of_le (by decide : 32≤64)]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
