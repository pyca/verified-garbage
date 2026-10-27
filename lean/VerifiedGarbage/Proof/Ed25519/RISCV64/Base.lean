module

public import VerifiedGarbage.Impl.X25519.RISCV64
public import VerifiedGarbage.Impl.Ed25519.RISCV64.Scalar
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Signing

/-!
# Ed25519 on RISC-V: the working space and the bytes of elements

The functions round their working space `scratch` up to a multiple of 8
(`align`): the elements are then at offsets of `base q` (`align_ok`), in
`scratch` (`base_sub`). An element's eight words are its 32 bytes,
little-endian (`read_V`, `out_bytes`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Proof.X25519.RISCV64
open VG.Spec.Ed25519 (decodeLE bytesAt)

theorem eACC_eq : Impl.Ed25519.RISCV64.ACC = 864 := rfl

/-- `q` rounded up to a multiple of 8. -/
abbrev base (q : Addr) : Addr := q + BitVec.ofNat 64 (Align.pad q)

/-- A range of the rounded working space, in the working space of 8192 bytes. -/
theorem base_sub (q : Addr) {o n : Nat} (h : o + n ≤ 2048) :
    Region.Sub ⟨base q + BitVec.ofNat 64 o, n⟩ ⟨q, 8192⟩ := by
  have := Align.pad_lt q
  rw [Offset.add_add]
  exact Offset.sub_base _ (by omega)

/-- `align`, from a working space of 8192 bytes at `q` in `a3`. -/
theorem align_ok {s : State} {q : Addr} (h3 : s.gpr .a3 = q) (hws : (⟨q, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block Impl.X25519.RISCV64.align) s fun t =>
      Ctx (base q) t ∧ Rest [.a3] s t ∧ t.mem = s.mem := by
  unfold Impl.X25519.RISCV64.align
  refine wp_addi (by decide) fun s1 u1 => wp_andi (by decide) fun s2 u2 => WP.block_nil ?_
  have e7 : (BitVec.ofNat 64 7 : BitVec 64) = BitVec.ofInt 64 7 := by decide
  have e : s2.gpr .a3 = base q := by rw [u2.gpr, u1.gpr, h3, e7, Align.align_eq]
  have hr : Rest [.a3] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  refine ⟨⟨e, Align.align_al _, fun d n hd => ?_⟩, hr, by rw [u2.mem, u1.mem]⟩
  have := Align.pad_lt q
  rw [hr.wr, Offset.add_add]
  exact in_base hws (by omega) (by omega)

/-- The 32 bytes of an element, as a number. -/
theorem read_V (m : Mem) (b : Addr) (o : Nat) : (m.read (b + BitVec.ofNat 64 o) 32).toNat = V m b o := by
  have e : ∀ k, b + BitVec.ofNat 64 (o + 4 * k) = b + BitVec.ofNat 64 o + BitVec.ofNat 64 (4 * k) :=
    fun k => by rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [← Proof.X25519.leNum_bytesAt_read, Proof.X25519.leNum_bytesAt_words32]
  simp only [V, Proof.X25519.val32, limb, wd, e]
  simp only [Nat.mul_zero, Nat.mul_one, BitVec.ofNat_eq_ofNat, Nat.zero_add, Nat.pow_zero, Nat.one_mul]
  simp only [Nat.reduceMul, BitVec.add_zero]

/-- The 32 bytes at `q` whose words are an element's. -/
theorem bytes_of_words {m m₀ : Mem} {q b : Addr} {a : Nat} (h : ∀ j < 8, wd m q (4 * j) = limb m₀ b a j) :
    decodeLE (bytesAt m q 32) = V m₀ b a := by
  have e : decodeLE (bytesAt m q 32) = V m q 0 := by
    rw [Proof.Ed25519.decodeLE_eq]
    show Proof.X25519.leNum (Spec.X25519.bytesAt m q 32) = _
    rw [Proof.X25519.leNum_bytesAt_read, ← read_V, BitVec.add_zero]
  rw [e, V, V]
  exact Proof.X25519.val32_congr fun j hj => by rw [limb, Nat.zero_add]; exact h j hj

/-- The 32 bytes at `q`, encoding the element whose words they are. -/
theorem out_bytes {m m₀ : Mem} {q b : Addr} {a : Nat} (h : ∀ j < 8, wd m q (4 * j) = limb m₀ b a j) {x : Nat}
    (hv : V m₀ b a = x) : bytesAt m q 32 = Spec.Ed25519.encodeLE 32 x := by
  rw [Proof.Ed25519.bytesAt_encodeLE, bytes_of_words h, hv]

/-- The low word of a sign-extended word. -/
theorem sext32_lo (c : BitVec 32) : (sext32 c).toNat % 2 ^ 32 = c.toNat := by
  have e : (sext32 c).setWidth 32 = c := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_setWidth, sext32, BitVec.getLsbD_signExtend]
    simp [hi, show i < 64 by omega]
  rw [← BitVec.toNat_setWidth, e]

/-- A word built by `li32` and zero-extended by two shifts. -/
theorem li32_zext (c : BitVec 32) : (((sext32 c) <<< 32) >>> 32).toNat = c.toNat := by
  rw [toNat_shr, toNat_shl, show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _), sext32_lo]

/-- A word below `2^31`, sign-extended. -/
theorem sext_ofNat {v : Nat} (h : v < 2 ^ 31) : sext32 (BitVec.ofNat 32 v) = BitVec.ofNat 64 v := by
  rw [sext32, BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega

end VG.Proof.Ed25519.RISCV64
