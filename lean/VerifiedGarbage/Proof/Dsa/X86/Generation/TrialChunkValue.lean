module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.RandomScan
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Two-byte input chunks keep reciprocal dividends within one word -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86

private theorem rotate_byte (b : Byte) :
    (b.setWidth 32).rotateRight 24 = BitVec.ofNat 32 (b.toNat * 256) := by
  have hb := b.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_rotateRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reduceMod, Nat.reduceSub, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 4294967296), Nat.div_eq_of_lt (by omega), Nat.zero_or]

private theorem rotate_half {r : Nat} (hr : r < 65536) :
    (BitVec.ofNat 32 r).rotateRight 16 = BitVec.ofNat 32 (r * 65536) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.reduceMod, Nat.reduceSub, Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega : r < 4294967296), Nat.div_eq_of_lt hr, Nat.zero_or]

theorem trialChunkValue_ok {s : State} {input : BitVec 32} {r : Nat} (hr : r < 65536)
    (bp : s.gpr .ebp = input) (xb : s.gpr .ebx = BitVec.ofNat 32 r)
    (fit : input.toNat + 2 ≤ 2 ^ 32)
    (rd : ∀ i < 2, InRegions (s.rd ++ s.wr) (off (input.setWidth 64) i) 1) :
    WP isa (.block [.movzx8 .eax (at_ .ebp 0), .shift .ror .eax 24,
      .movzx8 .edx (at_ .ebp 1), .alu .add .eax (.reg .edx),
      .shift .ror .ebx 16, .alu .add .ebx (.reg .eax)]) s fun t =>
      t.gpr .ebx = BitVec.ofNat 32 (r * 65536 + (s.mem (input.setWidth 64)).toNat * 256 +
        (s.mem (off (input.setWidth 64) 1)).toNat) ∧ t.mem = s.mem ∧ Keeps [.eax, .ebx, .edx] s t := by
  have addr0 : s.ea (at_ .ebp 0) = input.setWidth 64 := by
    change (s.gpr .ebp + 0#32).setWidth 64 = _; rw [BitVec.add_zero, bp]
  have rd0 : InRegions (s.rd ++ s.wr) (input.setWidth 64) 1 := by simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using rd 0 (by decide)
  refine wp_load8 addr0 rd0 fun a sa _ _ => wp_ror (by decide) fun b ab => ?_
  have addr1 : b.ea (at_ .ebp 1) = off (input.setWidth 64) 1 := by
    change (b.gpr .ebp + BitVec.ofNat 32 1).setWidth 64 = _
    rw [ab.other _ (by decide), sa.other _ (by decide), bp]; exact addr_eq (by omega)
  refine wp_load8 addr1 (by rw [ab.rd, ab.wr, sa.rd, sa.wr]; exact rd 1 (by decide)) fun c bc _ _ =>
    wp_addS rfl fun d cd _ => wp_ror (by decide) fun e de => wp_addS rfl fun t et _ => WP.block_nil ?_
  have k : Keeps [.eax, .ebx, .edx] s t := (((((sa.keeps.mono (by decide)).trans
    (ab.keeps.mono (by decide))).trans (bc.keeps.mono (by decide))).trans
    (cd.keeps.mono (by decide))).trans (de.keeps.mono (by decide))).trans (et.keeps.mono (by decide))
  refine ⟨?_, by rw [et.mem, de.mem, cd.mem, bc.mem, ab.mem, sa.mem], k⟩
  rw [et.gpr, de.gpr, cd.other _ (by decide), bc.other _ (by decide), ab.other _ (by decide),
    sa.other _ (by decide), xb, rotate_half hr, de.other _ (by decide), cd.gpr,
    bc.other _ (by decide), ab.gpr, sa.gpr, rotate_byte, bc.gpr, ab.mem, sa.mem]
  apply BitVec.eq_of_toNat_eq
  have h0 := (s.mem (input.setWidth 64)).isLt
  have h1 := (s.mem (off (input.setWidth 64) 1)).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  omega
end VG.Proof.Dsa.X86.Generation
