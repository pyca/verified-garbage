module

public import VerifiedGarbage.Impl.AesGcm.AArch64.Contiguous.Tag
public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.Gcm.Be64
public import VerifiedGarbage.Proof.Gcm.Compose
import VerifiedGarbage.Proof.Gcm.Spec
import VerifiedGarbage.Proof.Cmac.Dbl32
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section
namespace VG.Proof.AesGcm.AArch64.Contiguous.Tag
open VG VG.AArch64 VG.Proof.Gcm.AArch64.Pmull
open VG.Spec.Gcm (toBytes be64 ofBytes)
open VG.Impl.AesGcm.AArch64 (alenO)
open VG.Impl.AesGcm.AArch64.Contiguous.Tag
open VG.Impl.Gcm.AArch64.Pmull (A Y mul tReg sReg)

private theorem toBytes_append64 (a c : BitVec 64) : toBytes (a ++ c) = be64 a.toNat ++ be64 c.toNat := by
  have ha := a.isLt; have hc := c.isLt
  have e : (a ++ c).toNat = a.toNat * 2 ^ 64 + c.toNat := Proof.Gcm.toNat_append a c
  simp only [toBytes, be64, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat, e]
    omega_using []

private theorem beShift (a : BitVec 64) : be64 (a <<< 3).toNat = be64 (8*a.toNat) := by
  rw [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mul_comm a.toNat]
  exact Proof.Gcm.be64_mod _

theorem lenWord (a n : BitVec 64) :
    (n <<< 3) ++ (a <<< 3) = ext8 (ofBytes (Proof.Gcm.lensBlock a.toNat n.toNat))
      (ofBytes (Proof.Gcm.lensBlock a.toNat n.toNat)) := by
  have e : (a <<< 3) ++ (n <<< 3) = ofBytes (Proof.Gcm.lensBlock a.toNat n.toNat) := by
    rw [←Proof.Cmac.ofBytes_toBytes ((a <<< 3) ++ (n <<< 3)),toBytes_append64,beShift,beShift]
    rfl
  rw [←e,ext8_eq,vdword_append_0,vdword_append_1]

private theorem shift (s : State) (d r : Reg) :
    exec (.lsl .x d r 3) s = some (s.write .x d (s.gpr r <<< 3)) := rfl

abbrev aadLength (s : State) := s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 alenO) 64

/-- The length block uses two volatile integer registers and preserves the tag mask. -/
structure HashFrame (s t : State) : Prop where
  mask : t.v .v28 = s.v .v28
  gpr : ∀ r, r ≠ .x9 → r ≠ .x10 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

private theorem input_ok {s : State} {H y : Spec.Gcm.Block} (key : Fast.HKey H s)
    (hy : s.v Y = ext8 y y) (rd : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 alenO) 8) :
    let w := ofBytes (Proof.Gcm.lensBlock (aadLength s).toNat (s.gpr .x26).toNat)
    WP isa (.block lengthInput) s fun t => t.v A = ext8 (w ^^^ y) (w ^^^ y) ∧ Fast.HKey H t ∧ HashFrame s t := by
  dsimp only
  unfold lengthInput
  refine WP.block_cons_iff.mpr ⟨_, exec_ldr_x (by decide) rd, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, shift _ _ _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, shift _ _ _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ins_d2 (i := 0) (by decide) _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_ins_d2 (i := 1) (by decide) _, ?_⟩
  refine WP.block_cons_iff.mpr ⟨_, exec_eor _ _ _ _, ?_⟩
  refine WP.block_nil ⟨?_,?_,?_⟩
  · simp only [RegUpd.v_setV,RegUpd.gpr_setV,RegUpd.v_write,RegUpd.gpr_write,reduceCtorEq,
      ↓reduceIte,Size.bits,BitVec.setWidth_eq,setLane_pair]
    rw [Fast.ext8_xor,←lenWord,hy]
  · exact key.of_v rfl rfl rfl
  · refine ⟨rfl,?_,rfl,rfl,rfl,rfl⟩
    intro r h9 h10
    simp only [RegUpd.gpr_setV,RegUpd.gpr_write,h9,h10,ite_false]

theorem lengths_ok {s : State} {H y : Spec.Gcm.Block} (law : MulKey) (key : Fast.HKey H s)
    (hy : s.v Y = ext8 y y) (rd : InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 alenO) 8) :
    let w := ofBytes (Proof.Gcm.lensBlock (aadLength s).toNat (s.gpr .x26).toNat)
    let z := Spec.Gcm.mul (y ^^^ w) H
    WP isa (.block lengths) s fun t => t.v Y = VRevOp.eval .rev64b (ext8 z z) ∧ HashFrame s t := by
  dsimp only
  rw [lengths,List.append_assoc,WP.block_append_iff]
  refine (input_ok key hy rd).mono ?_
  intro u ⟨a,k,f⟩
  rw [WP.block_append_iff]
  refine (mulV_ok Y A (sReg 1) (tReg 1) u free_A (sReg_free _) (tReg_free _) k.sw k.c).mono ?_
  intro v ⟨m,o⟩
  rw [WP.block_cons_iff]
  refine ⟨_,exec_rev64b Y Y v,WP.block_nil ⟨?_,?_⟩⟩
  · simp only [RegUpd.v_setV,ite_true,m,a,k.t,BitVec.xor_comm]
    rw [law]
  · exact ⟨(o.v _ (by decide)).trans f.mask, fun r a b => (congrFun o.gpr r).trans (f.gpr r a b),
      o.mem.trans f.mem,o.sp.trans f.sp,o.rd.trans f.rd,o.wr.trans f.wr⟩

end VG.Proof.AesGcm.AArch64.Contiguous.Tag
