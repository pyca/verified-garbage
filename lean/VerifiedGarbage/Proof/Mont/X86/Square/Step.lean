module

public import VerifiedGarbage.Impl.Mont.X86.MulRt
public import VerifiedGarbage.Proof.Mont.X86.Square.Packed
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Framework.X86.Wp

@[expose] public section

namespace VG.Proof.Mont.X86.Square
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt
open VG.X86.RegUpd

def accumState (s : State) : State :=
  let s1 := (XOp.movd .xmm2 .eax).exec s
  let s2 := (XOp.bin .paddq .xmm0 .xmm2).exec s1
  let s3 := (XOp.movd .xmm2 .edx).exec s2
  (XOp.bin .paddq .xmm1 .xmm2).exec s3

theorem run_accum (s : State) : runBlock isa VG.Impl.Mont.X86.Rt.Square.accum s = some (accumState s) := by
  simp only [VG.Impl.Mont.X86.Rt.Square.accum, runBlock_cons, runStep_some, runBlock_nil, exec, accumState]

theorem movd_packed (a : BitVec 32) : (0 : BitVec 96) ++ a = packed (a.setWidth 64) := by
  rw [← packed_of32]
  exact (BitVec.setWidth_eq_append (by decide)).symm

theorem accum_values {s : State} {lo hi : BitVec 64}
    (hl : s.xmm .xmm0 = packed lo) (hh : s.xmm .xmm1 = packed hi) :
    (accumState s).xmm .xmm0 = packed (lo + (s.gpr .eax).setWidth 64) ∧
    (accumState s).xmm .xmm1 = packed (hi + (s.gpr .edx).setWidth 64) ∧
    (accumState s).xmm .xmm3 = s.xmm .xmm3 ∧
    (accumState s).xmm .xmm7 = s.xmm .xmm7 := by
  simp only [accumState, XOp.exec]
  simp (disch := decide) only [xmm_setXmm_self, xmm_setXmm_of_ne, gpr_setXmm, hl, hh,
    movd_packed, packed_add, and_self]

theorem accum_scalar (s : State) :
    (accumState s).gpr = s.gpr ∧ (accumState s).mem = s.mem ∧
    (accumState s).rd = s.rd ∧ (accumState s).wr = s.wr := by
  simp only [accumState, XOp.exec, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, and_self]

def prodState (s : State) (a b : BitVec 32) : State :=
  accumState (execMul .edx ((s.setReg .eax a).setReg .edx b))

theorem prod_ok {s : State} {W : Addr} {L x y : Nat} (hw : Ws s W L)
    (hx : PtrAt s W .ecx x) (hy : PtrAt s W .ebp y) (xl : x+4 ≤ L) (yl : y+4 ≤ L) :
    WP isa (.block VG.Impl.Mont.X86.Rt.Square.prod) s fun t =>
      t = prodState s (s.mem.readW (off W x) 32) (s.mem.readW (off W y) 32) := by
  apply WP.of_runBlock
  refine ⟨_, ?_, rfl⟩
  have h1 := readSrc_ptr hw hx (d := 0) (by omega)
  have K : Keeps [.eax] s (s.setReg .eax (s.mem.readW (off W x) 32)) := (Upd.setReg ..).keeps
  have hw1 := hw.of_keeps K
  have hy1 : PtrAt (s.setReg .eax (s.mem.readW (off W x) 32)) W .ebp y := by
    rw [PtrAt, K.1 _ (by decide)]; exact hy
  have h2 := readSrc_ptr hw1 hy1 (d := 0) (by omega)
  simp only [Nat.add_zero] at h1 h2
  simp only [State.setReg] at h2
  simp only [VG.Impl.Mont.X86.Rt.Square.prod, List.cons_append, List.nil_append, runBlock_cons, exec,
    h1, Option.map_some, runStep_some]
  rw [show readSrc (s.setReg .eax (s.mem.readW (off W x) 32)) (.mem (VG.Impl.Mont.X86.at_ .ebp 0)) =
    some (s.mem.readW (off W y) 32) from h2]
  simp only [Option.map_some, runStep_some, runBlock_cons, exec, run_accum, prodState]

theorem widen_low (p : Nat) : (BitVec.ofNat 32 p).setWidth 64 = BitVec.ofNat 64 (p % 2^32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

theorem widen_high (a b : BitVec 32) :
    (BitVec.ofNat 32 (a.toNat*b.toNat / 2^32)).setWidth 64 =
      BitVec.ofNat 64 (a.toNat*b.toNat / 2^32) := by
  have bound : a.toNat*b.toNat < 2^32 * 2^32 := Nat.mul_lt_mul'' a.isLt b.isLt
  have hi : a.toNat*b.toNat / 2^32 < 2^32 := (Nat.div_lt_iff_lt_mul (by decide)).2 bound
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem prod_values {s : State} {lo hi : BitVec 64} (a b : BitVec 32)
    (hl : s.xmm .xmm0 = packed lo) (hh : s.xmm .xmm1 = packed hi) :
    let t := prodState s a b
    t.xmm .xmm0 = packed (lo + BitVec.ofNat 64 (a.toNat*b.toNat % 2^32)) ∧
    t.xmm .xmm1 = packed (hi + BitVec.ofNat 64 (a.toNat*b.toNat / 2^32)) ∧
    t.xmm .xmm3 = s.xmm .xmm3 ∧ t.xmm .xmm7 = s.xmm .xmm7 := by
  have v := accum_values (s := execMul .edx ((s.setReg .eax a).setReg .edx b))
    (by simpa only [execMul, xmm_setReg, xmm_setFlags] using hl)
    (by simpa only [execMul, xmm_setReg, xmm_setFlags] using hh)
  have ea : (execMul .edx ((s.setReg .eax a).setReg .edx b)).gpr .eax =
      BitVec.ofNat 32 (a.toNat*b.toNat) := by
    simp [execMul, State.setReg, State.setFlags]
  have ed : (execMul .edx ((s.setReg .eax a).setReg .edx b)).gpr .edx =
      BitVec.ofNat 32 (a.toNat*b.toNat / 2^32) := by
    simp [execMul, State.setReg, State.setFlags]
  rw [ea, ed, widen_high, widen_low] at v
  exact v

theorem prod_frame (s : State) (a b : BitVec 32) :
    Keeps [.eax, .edx] s (prodState s a b) ∧ (prodState s a b).mem = s.mem := by
  have v := accum_scalar (execMul .edx ((s.setReg .eax a).setReg .edx b))
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro r hr
    rw [prodState, v.1]
    simp only [execMul, State.setReg, State.setFlags]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hr.1, hr.2]
  · rw [prodState, v.2.2.1]; rfl
  · rw [prodState, v.2.2.2]; rfl
  · rw [prodState, v.2.1]; rfl

end VG.Proof.Mont.X86.Square
