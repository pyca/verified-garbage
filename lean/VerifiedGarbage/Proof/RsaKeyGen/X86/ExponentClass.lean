module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words

/-! # Branches on the public exponent inspect its complete native 64-bit value -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentFilter

theorem exponent_word (m : Mem) (base : Addr) (offset : Nat) :
    Mod64.exponentValue m base offset = (word m base offset).toNat := by
  rw [word_eq_w32]
  rfl

theorem pair_parity (low high : BitVec 32) : Mod64.pair low high % 2 = low.toNat % 2 := by
  unfold Mod64.pair
  omega

theorem pair_equal (low high : BitVec 32) {value : Nat} (bound : value < 2 ^ 32) :
    (low ^^^ BitVec.ofNat 32 value ||| high == 0#32) = decide (Mod64.pair low high = value) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  change (low.toNat = value ∧ high.toNat = 0) ↔ low.toNat + 2 ^ 32 * high.toNat = value
  have := low.isLt
  omega

theorem parity_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (fit : 136 ≤ size) :
    WP isa (.block parity) s fun t =>
      t.zf = some (decide (Mod64.exponentValue s.mem base 128 % 2 = 0)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold parity
  refine wp_movS (readSrc_sc S (d := 128) (by omega)) fun a A _ => wp_andi fun b B =>
    wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (B.mem.trans A.mem), (A.keeps.trans B.keeps).trans (T.keeps _)⟩
  rw [Z, B.gpr, A.gpr]
  change some ((s.mem.readW (off base 128) 32 &&& 1#32) - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_and]
  change (s.mem.readW (off base 128) 32).toNat &&& 1 = 0 ↔ Mod64.exponentValue s.mem base 128 % 2 = 0
  rw [Nat.and_one_is_mod]
  change (s.mem.readW (off base 128) 32).toNat % 2 = 0 ↔ Mod64.exponentValue s.mem base 128 % 2 = 0
  unfold Mod64.exponentValue
  rw [pair_parity]

theorem equal_ok {s : State} {base : Addr} {size value : Nat} (S : Scr s base size)
    (fit : 136 ≤ size) (bound : value < 2 ^ 32) :
    WP isa (.block (equal value)) s fun t =>
      t.zf = some (decide (Mod64.exponentValue s.mem base 128 = value)) ∧
      t.mem = s.mem ∧ Keeps [.eax] s t := by
  unfold equal
  refine wp_movS (readSrc_sc S (d := 128) (by omega)) fun a A _ =>
    wp_logicS (Or.inr rfl) rfl fun b B => ?_
  have K : Keeps [.eax] s b := A.keeps.trans B.keeps
  refine wp_orS (readSrc_sc (S.of_keeps K (by decide)) (d := 132) (by omega)) fun d D =>
    wp_cmpS rfl fun t T Z => WP.block_nil ?_
  refine ⟨?_, T.mem.trans (D.mem.trans (B.mem.trans A.mem)), (K.trans D.keeps).trans (T.keeps _)⟩
  rw [Z, D.gpr, B.gpr, A.gpr, B.mem, A.mem]
  simp only [show AluOp.xor ≠ AluOp.and by decide, ite_false]
  change some (((s.mem.readW (off base 128) 32 ^^^ BitVec.ofNat 32 value) ||| s.mem.readW (off base 132) 32) - 0#32 == 0#32) = _
  rw [BitVec.sub_zero]
  change some ((s.mem.readW (off base 128) 32 ^^^ BitVec.ofNat 32 value) ||| s.mem.readW (off base 132) 32 == 0#32) = _
  rw [pair_equal _ _ bound]
  rfl

end VG.Proof.RsaKeyGen.X86.ExponentFilter
