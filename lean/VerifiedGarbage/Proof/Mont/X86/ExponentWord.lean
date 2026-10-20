module

public import VerifiedGarbage.Impl.Mont.X86.Exponent
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Shifting a secret exponent word without branches on its value -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem lowBit_nat (x : BitVec 32) : (x &&& 1).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl, Nat.and_one_is_mod]

theorem rotate_lowBit (x : BitVec 32) :
    ((x &&& 1).rotateRight 1).toNat = 2 ^ 31 * (x.toNat % 2) := by
  have h : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
  rcases h with h | h
  · have e : x &&& 1 = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [lowBit_nat, h]
      rfl
    rw [e, h]
    rfl
  · have e : x &&& 1 = 1 := by
      apply BitVec.eq_of_toNat_eq
      rw [lowBit_nat, h]
      rfl
    rw [e, h]
    rfl

theorem shifted_word (x y : BitVec 32) :
    ((x >>> 1) + (y &&& 1).rotateRight 1).toNat = x.toNat / 2 + 2 ^ 31 * (y.toNat % 2) := by
  rw [BitVec.toNat_add, rotate_lowBit, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hx := x.isLt
  have hy : y.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  apply Nat.mod_eq_of_lt
  omega

/-- Only the current word changes; the next word is read before it shifts. -/
theorem shiftWord_ok {s : State} {base : Addr} {size out : Nat} (hs : Scr s base size)
    (last : Bool) (ho : out + 4 ≤ size) (hn : last = false → out + 8 ≤ size) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.shiftWord out last)) s fun t =>
      Outside base out 4 s.mem t.mem ∧
      w32 t.mem base out = w32 s.mem base out / 2 +
        2 ^ 31 * (if last then 0 else w32 s.mem base (out + 4) % 2) ∧
      Keeps [.eax, .edx] s t := by
  let upper : BitVec 32 := if last then 0 else s.mem.readW (off base (out + 4)) 32
  have load : readSrc s (if last then .imm 0 else .mem (sc (out + 4))) = some upper := by
    cases last with
    | true => rfl
    | false => exact readSrc_sc hs (by have := hn rfl; omega)
  unfold VG.Impl.Mont.X86.Dynamic.shiftWord
  refine wp_movS load fun s₁ u₁ _ => ?_
  refine wp_logicS (.inl rfl) rfl fun s₂ u₂ => ?_
  refine wp_ror (by decide) fun s₃ u₃ => ?_
  have k₃ : Keeps [.eax, .edx] s s₃ := ((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps
  have hs₃ := hs.of_keeps k₃ (by decide)
  refine wp_movS (readSrc_sc hs₃ ho) fun s₄ u₄ _ => ?_
  refine wp_shr (by decide) fun s₅ u₅ _ => ?_
  refine wp_addS rfl fun s₆ u₆ _ => ?_
  have k₆ : Keeps [.eax, .edx] s s₆ := ((k₃.widen u₄.keeps).widen u₅.keeps).widen u₆.keeps
  have hs₆ := hs.of_keeps k₆ (by decide)
  refine wp_storeS (hs₆.ea (by omega)) (hs₆.write ho) fun t mt => WP.block_nil ⟨?_, ?_, k₆.trans (mt.keeps _)⟩
  · rw [mt.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)
  · rw [mt.mem, w32_write_self, u₆.gpr, u₅.gpr, u₄.gpr,
      u₅.other .eax (by decide), u₄.other .eax (by decide), u₃.gpr, u₂.gpr, u₁.gpr,
      u₃.mem, u₂.mem, u₁.mem, ite_eq_left rfl, shifted_word]
    cases last <;> rfl

end VG.Proof.Mont.X86.Dynamic
