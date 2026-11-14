module

public import VerifiedGarbage.Proof.Ed25519.Word64
public import VerifiedGarbage.Proof.X25519.Field
public import VerifiedGarbage.Proof.Ed25519.AArch64.Mem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Ed25519.Field64`, which only this module used -/

section

/-! Target-independent facts for folding carries modulo 2^255 - 19. -/

@[expose] public section

namespace VG.Proof.Ed25519.Word64
open VG.Proof.X25519

/-- After adding a small word to a four-word number, folding a final
carry back as 38 cannot overflow the low word. -/
theorem foldCarry_low (r0 r1 r2 r3 : Word) (c : Bool) {a v : Nat}
    (ha : a < 2 ^ 256) (hv : v < 2 ^ 58)
    (h : val4 r0 r1 r2 r3 + 2 ^ 256 * c.toNat = a + v) :
    (r0 + BitVec.ofNat 64 (38 * c.toNat)).toNat = r0.toNat + 38 * c.toNat := by
  have hl := low_le_val4 r0 r1 r2 r3
  cases c with
  | false =>
    change (r0 + 0).toNat = r0.toNat + 0
    exact congrArg BitVec.toNat (BitVec.add_zero r0)
  | true =>
    have hb : r0.toNat + 38 < 2 ^ 64 := by
      simp only [Bool.toNat_true, Nat.mul_one] at h
      omega_using [ha, hv, hl, h]
    change (r0 + 38).toNat = r0.toNat + 38
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hb

theorem foldCarry_field (r0 r1 r2 r3 : Word) (c : Bool) {a v : Nat}
    (ha : a < 2 ^ 256) (hv : v < 2 ^ 58)
    (h : val4 r0 r1 r2 r3 + 2 ^ 256 * c.toNat = a + v) :
    toFe (val4 (r0 + BitVec.ofNat 64 (38 * c.toNat)) r1 r2 r3) = toFe (a + v) := by
  have hn : val4 (r0 + BitVec.ofNat 64 (38 * c.toNat)) r1 r2 r3 =
      val4 r0 r1 r2 r3 + 38 * c.toNat := by
    simp only [val4]
    rw [foldCarry_low r0 r1 r2 r3 c ha hv h]
    omega_using []
  apply toFe_congr
  rw [hn, ← h]
  exact (fold256 _ _).symm

end VG.Proof.Ed25519.Word64

end

end


/-! Merged from `Proof.Ed25519.AArch64.Carry`. -/

@[expose] public section

section
/-! Reduction of the carry above four 64-bit field limbs. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

private theorem carry38_word (c : Bool) :
    (if c = true then (38 : Word) else 0) = BitVec.ofNat 64 (38 * c.toNat) := by
  cases c <;> decide

private theorem carry38_arith (a0 a1 a2 a3 v : Word) (hv : v.toNat < 2 ^ 58) :
    let c0 := carryOut a0 v false
    let c1 := carryOut a1 0 c0
    let c2 := carryOut a2 0 c1
    let c3 := carryOut a3 0 c2
    toFe (val4 (addCarry a0 v false + if c3 = true then 38 else 0)
      (addCarry a1 0 c0) (addCarry a2 0 c1) (addCarry a3 0 c2)) =
      toFe (val4 a0 a1 a2 a3 + v.toNat) := by
  intro c0 c1 c2 c3
  rw [carry38_word]
  apply foldCarry_field _ _ _ _ _ (val4_lt a0 a1 a2 a3) hv
  simpa only [val4, Bool.toNat_false, Nat.add_zero, Nat.mul_zero, show (0 : Word).toNat = 0 from rfl] using
    add4_value a0 a1 a2 a3 v 0 0 0 false

theorem carry38_ok (s : State) (hz : s.gpr .x10 = 0) (h38 : s.gpr .x11 = 38)
    (hv : (s.gpr .x8).toNat < 2 ^ 58) :
    WP isa (.block carry38) s fun s' =>
      toFe (val4 (s'.gpr .x4) (s'.gpr .x5) (s'.gpr .x6) (s'.gpr .x7)) =
        toFe (val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) + (s.gpr .x8).toNat) ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s s' := by
  apply WP.of_runBlock
  simp only [carry38, carryValue38, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz, h38,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · have h := carry38_arith (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) (s.gpr .x8) hv
    dsimp only [addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1,
      hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Memory and register frames for field operations. -/
namespace VG.Proof.Ed25519.AArch64
variable {large : Bool}

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 Word64 VG.Proof.X25519

abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X25519.Fe := toFe (fe m base o)

def clob : List Reg :=
  [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17,
    .x20, .x21, .x22, .x23, .x24]

structure Op (base : Addr) (o : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o 32 s.mem t.mem

theorem Op.of_store {base : Addr} {o : Nat} {s t : State} (ho : FieldRange o large) (h : Keeps clob s t)
    (a b c d : Word) : Op base o s { t with mem := st4 t.mem base o a b c d } := by
  have _hcap := workSize_le large
  have _hmin := workSize_ge large
  refine ⟨h.gpr, h.rd, h.wr, h.sp, ?_⟩
  rw [h.mem]
  exact st4_outside _ _ (by have := ho.2; omega_using [_hcap, this]) _ _ _ _

theorem fieldInit_ok (s : State) (v : BitVec 16 := 38) :
    WP isa (.block [.movz .w .x10 0 0, .movz .w .x11 v 0]) s fun t =>
      t.gpr .x10 = 0 ∧ t.gpr .x11 = v.setWidth 64 ∧ Keeps [.x10, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), RegUpd.gpr_write_self]
    rfl
  · rw [RegUpd.gpr_write_self, BitVec.shiftLeft_zero, BitVec.setWidth_setWidth (by decide)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_write_of_ne _ _ _ hr.2, RegUpd.gpr_write_of_ne _ _ _ hr.1]

end VG.Proof.Ed25519.AArch64
