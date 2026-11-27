module

public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MlKem.AArch64.Vec
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.Tbl
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackIndex
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem

/-! ### `MlDsa.AArch64.Optimized.ResidentUnpackGather`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

private theorem vbyte_read (m : Mem) (a : Addr) {e : Nat} (he : e<16) :
    vbyte (m.read a 16) e=m (a+BitVec.ofNat 64 e) := Mem.extractLsb'_read m a he

/-- Byte lookup from the two full input vectors and the overlapping tail. -/
theorem tableByte_three {v : VReg → BitVec 128} {m : Mem} {a : Addr} {d : Nat}
    (hd : d=18 ∨ d=20)
    (h0 : v .v0=m.read a 16) (h1 : v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16)
    {i : Nat} (hi : i<48) : tableByte v .v0 i=m (a+BitVec.ofNat 64 (tableOffset d i)) := by
  unfold tableByte
  by_cases h16 : i<16
  · rw [show i/16=0 by omega_using [h16],show Nat.repeat VReg.succ 0 .v0=.v0 from rfl,h0,
      vbyte_read _ _ (by omega_using []),Nat.mod_eq_of_lt h16]
    simp only [tableOffset,ite_eq_left (by omega_using [h16] : i<32)]
  · by_cases h32 : i<32
    · rw [show i/16=1 by omega_using [h16, h32],show Nat.repeat VReg.succ 1 .v0=.v1 from rfl,h1,
        vbyte_read _ _ (by omega_using []),Offset.add_add]
      simp only [tableOffset,ite_eq_left h32]
      rw [show 16+i%16=i by omega_using [h16, h32]]
    · rw [show i/16=2 by omega_using [hi, h32],show Nat.repeat VReg.succ 2 .v0=.v2 from rfl,h2,
        vbyte_read _ _ (by omega_using []),Offset.add_add]
      simp only [tableOffset,ite_eq_right h32]
      rw [show 2*d-16+i%16=i+2*d-48 by rcases hd with rfl | rfl <;> omega_using [hi, h32]]

/-- Mathematical index vector installed by `Unpack.init`. -/
def gatherIndex (d g : Nat) : BitVec 128 :=
  ofVBytes fun i => BitVec.ofNat 8 ((Unpack.indices d g)[i]!)

/-- Every gathered word consists of exactly three consecutive input bytes
and a zero top byte, before alignment and masking. -/
theorem gather_byte {v : VReg → BitVec 128} {m : Mem} {a : Addr} {d g e : Nat}
    (hd : d=18 ∨ d=20) (hg : g<4) (he : e<16)
    (h0 : v .v0=m.read a 16) (h1 : v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16) :
    (let ix := (vbyte (gatherIndex d g) e).toNat
      if ix<48 then tableByte v .v0 ix else 0) =
    if e%4<3 then m (a+BitVec.ofNat 64 (d*(4*g+e/4)/8+e%4)) else 0 := by
  have hc := indexCorrect_of_width hd g hg e he
  simp only [gatherIndex,vbyte_ofVBytes _ he,BitVec.toNat_ofNat]
  by_cases hl : e%4<3
  · have hi := hc.1 hl
    rw [Nat.mod_eq_of_lt (by omega_using [hi] : (Unpack.indices d g)[e]!<256),ite_eq_left hi.1,
      ite_eq_left hl,tableByte_three hd h0 h1 h2 hi.1,hi.2.1]
  · have hi := hc.2 (by omega_using [hl])
    rw [hi]
    simp only [ite_eq_right (by decide : ¬ (255:Nat)<48),ite_eq_right hl]

def gatherValue (v : VReg → BitVec 128) (d g : Nat) : BitVec 128 :=
  ofVBytes fun e =>
    let ix := (vbyte (gatherIndex d g) e).toNat
    if ix<48 then tableByte v .v0 ix else 0

/-- Each gathered 32-bit lane contains a zero-extended 24-bit input window. -/
theorem gather_word {v : VReg → BitVec 128} {m : Mem} {a : Addr} {d g e : Nat}
    (hd : d=18 ∨ d=20) (hg : g<4) (he : e<4)
    (h0 : v .v0=m.read a 16) (h1 : v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16) :
    vword (gatherValue v d g) e =
      (m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vword,BitVec.getLsbD_extractLsb',gatherValue]
  rw [show 32*e+i=8*(4*e+i/8)+i%8 by omega_using [],
    getLsbD_ofVBytes _ (by omega_using [he, hi]) (by omega_using []),gather_byte hd hg (by omega_using [he, hi]) h0 h1 h2]
  simp only [show (4*e+i/8)%4=i/8 by omega_using [hi],show (4*e+i/8)/4=e by omega_using [hi],
    BitVec.getLsbD_setWidth]
  by_cases hl : i<24
  · rw [ite_eq_left (by omega_using [hl] : i/8<3),getLsbD_read m 3 _ i hl,Offset.add_add]
  · rw [ite_eq_right (by omega_using [hl] : ¬ i/8<3),BitVec.getLsbD_of_ge (m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3) i (by omega_using [hl])]
    simp [BitVec.getLsbD]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

end

@[expose] public section

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
