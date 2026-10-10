import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackWord
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentUnpackConst

/-! ## From `ResidentUnpackArithmetic.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (wp_vop)

def alignVec (x powers mask : BitVec 128) (sh : Nat) : BitVec 128 :=
  let p := VArr.s4.map2 (fun _ a b => a*b) x powers
  VArr.s4.map2 (fun _ _ a => a >>> sh) p p &&& mask

def correctVec (x bound modulus : BitVec 128) : BitVec 128 :=
  let r := VArr.s4.map2 (fun _ a b => a-b) bound x
  let sign := VArr.s4.map2 (fun _ _ a => a.sshiftRight 31) r r
  VArr.s4.map2 (fun _ a b => a+b) r (sign &&& modulus)

theorem vword_and (a b : BitVec 128) (e : Nat) :
    vword (a &&& b) e=vword a e &&& vword b e := by
  simp only [vword,BitVec.extractLsb'_and]

theorem alignVec_word (x powers mask : BitVec 128) {d e : Nat}
    (hd : d=18 ∨ d=20) (he : e<4)
    (hp : vword powers e=BitVec.ofNat 32 (2^((if d=20 then 4 else 6)-d*e%8)))
    (hm : vword mask e=BitVec.ofNat 32 (2^d-1)) :
    vword (alignVec x powers mask (if d=20 then 4 else 6)) e =
      ((vword x e).extractLsb' (d*e%8) d).setWidth 32 := by
  simp only [alignVec,vword_and,VG.AArch64.vword_map2 _ _ _ he,hp,hm]
  exact align_mul_field _ hd

theorem correctVec_word (x bound modulus : BitVec 128) {e : Nat} (he : e<4)
    (hq : vword modulus e=8380417#32) :
    vword (correctVec x bound modulus) e=unpackWord (vword bound e) (vword x e) := by
  simp only [correctVec,VG.AArch64.vword_map2 _ _ _ he,vword_and,hq,unpackWord]

structure ArithmeticKeep (r : VReg) (s t : State) : Prop where
  gpr : t.gpr=s.gpr
  vec : ∀ v, v≠r → v≠.v24 → t.v v=s.v v
  mem : t.mem=s.mem
  rd : t.rd=s.rd
  wr : t.wr=s.wr
  sp : t.sp=s.sp

/-- Exact selected vector arithmetic, separate from the TBL gather and store.
The lane-wise result is independently related to packed fields above. -/
theorem arithmetic_ok (s : State) (r : VReg) {d : Nat} (hd : d=18 ∨ d=20)
    (h20 : r≠.v20) (h21 : r≠.v21) (h22 : r≠.v22) (h24 : r≠.v24) :
    WP isa (.block [
      .vop (.mul r r .v23),.vop (.shift .ushr .s4 r r (if d=20 then 4 else 6)),
      .vop (.logic .and r r .v22),.vop (.sub .s4 r .v21 r),
      .vop (.shift .sshr .s4 .v24 r 31),.vop (.logic .and .v24 .v24 .v20),
      .vop (.add .s4 r r .v24)]) s fun t =>
      ArithmeticKeep r s t ∧ t.v r=correctVec
        (alignVec (s.v r) (s.v .v23) (s.v .v22) (if d=20 then 4 else 6))
        (s.v .v21) (s.v .v20) := by
  have hs : VShiftOp.ok .ushr 32 (if d=20 then 4 else 6)=true := by
    rcases hd with rfl | rfl <;> decide
  refine wp_vop (d := r) rfl fun a ha => ?_
  refine wp_vop (d := r) (x := VArr.s4.map2 (fun _ _ y => y >>> (if d=20 then 4 else 6)) (a.v r) (a.v r)) (by simp only [VOp.eval,VArr.esize,hs,ite_true,VShiftOp.eval]) fun b hb => ?_
  refine wp_vop (d := r) rfl fun c hc => ?_
  refine wp_vop (d := r) rfl fun f hf => ?_
  refine wp_vop (d := .v24) rfl fun g hg => ?_
  refine wp_vop (d := .v24) rfl fun h hh => ?_
  refine wp_vop (d := r) rfl fun t ht => WP.block_nil_iff.mpr ⟨?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [ht.gpr,hh.gpr,hg.gpr,hf.gpr,hc.gpr,hb.gpr,ha.gpr]
    · intro v hv hv24
      rw [ht.other v hv,hh.other v hv24,hg.other v hv24,hf.other v hv,
        hc.other v hv,hb.other v hv,ha.other v hv]
    · rw [ht.mem,hh.mem,hg.mem,hf.mem,hc.mem,hb.mem,ha.mem]
    · rw [ht.rd,hh.rd,hg.rd,hf.rd,hc.rd,hb.rd,ha.rd]
    · rw [ht.wr,hh.wr,hg.wr,hf.wr,hc.wr,hb.wr,ha.wr]
    · rw [ht.sp,hh.sp,hg.sp,hf.sp,hc.sp,hb.sp,ha.sp]
  · rw [ht.v,hh.other r h24,hg.other r h24,hh.v,hg.v]
    simp only [hf.v,hf.other .v20 (Ne.symm h20),hc.other .v20 (Ne.symm h20),
      hb.other .v20 (Ne.symm h20),ha.other .v20 (Ne.symm h20),
      hc.v,hc.other .v21 (Ne.symm h21),hb.other .v21 (Ne.symm h21),
      ha.other .v21 (Ne.symm h21),hb.v,ha.v,
      hb.other .v22 (Ne.symm h22),ha.other .v22 (Ne.symm h22),
      hg.other .v20 (by decide),VShiftOp.eval,alignVec,correctVec]
    rfl

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end

/-! ## From `ResidentUnpackValue.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentMask

/-- Constants consumed by the arithmetic part of each four-field group. -/
structure ParseConstants (d : Nat) (s : State) : Prop where
  powers : ∀ e<4, vword (s.v .v23) e=BitVec.ofNat 32 (2^((if d=20 then 4 else 6)-d*e%8))
  mask : ∀ e<4, vword (s.v .v22) e=BitVec.ofNat 32 (2^d-1)
  bound : ∀ e<4, vword (s.v .v21) e=BitVec.ofNat 32 (2^(d-1))
  modulus : ∀ e<4, vword (s.v .v20) e=8380417#32

def fieldValue (m : Mem) (a : Addr) (d i : Nat) : Nat :=
  (((m.read (a+BitVec.ofNat 64 (d*i/8)) 3).setWidth 32).extractLsb' (d*i%8) d).toNat

/-- The composed TBL, alignment and signed correction computes precisely the
canonical representative of gamma minus the packed little-endian field. -/
theorem parsed_word {s : State} {m : Mem} {a : Addr} {d g e : Nat}
    (hd : d=18 ∨ d=20) (hg : g<4) (he : e<4) (hc : ParseConstants d s)
    (h0 : s.v .v0=m.read a 16) (h1 : s.v .v1=m.read (a+BitVec.ofNat 64 16) 16)
    (h2 : s.v .v2=m.read (a+BitVec.ofNat 64 (2*d-16)) 16) :
    (vword (correctVec (alignVec (gatherValue s.v d g) (s.v .v23) (s.v .v22)
      (if d=20 then 4 else 6)) (s.v .v21) (s.v .v20)) e).toNat =
      (2^(d-1)+8380417-fieldValue m a d (4*g+e))%8380417 := by
  rw [correctVec_word _ _ _ he (hc.modulus e he),
    alignVec_word _ _ _ hd he (hc.powers e he) (hc.mask e he),hc.bound e he,
    gather_word hd hg he h0 h1 h2]
  have hd32 : d≤32 := by omega
  have hb : (BitVec.ofNat 32 (2^(d-1))).toNat<8380417 := by
    rcases hd with rfl | rfl <;> decide
  have hx : (BitVec.setWidth 32
      (((m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3).setWidth 32).extractLsb' (d*e%8) d)).toNat<8380417 := by
    rw [BitVec.toNat_setWidth_of_le hd32]
    have h := (((m.read (a+BitVec.ofNat 64 (d*(4*g+e)/8)) 3).setWidth 32).extractLsb' (d*e%8) d).isLt
    rcases hd with rfl | rfl <;> omega
  rw [unpackWord_toNat hb hx,BitVec.toNat_setWidth_of_le hd32]
  have hp : (BitVec.ofNat 32 (2^(d-1))).toNat=2^(d-1) := by
    rcases hd with rfl | rfl <;> decide
  simp only [hp,fieldValue,(fieldShift_bounds (g := g) (e := e) hd).1]

end VG.Proof.MlDsa.AArch64.Optimized.ResidentMask

end
