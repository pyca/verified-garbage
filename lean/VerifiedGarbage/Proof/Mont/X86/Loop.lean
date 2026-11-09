module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Mont.X86.RedRow
import VerifiedGarbage.Proof.Mont.X86.Row
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# Montgomery arithmetic on x86 (32-bit): the loop of the multiplication

An iteration of `mul`'s loop (`row`), at `ebp = edi + 4i`, adds `a_i [b]`
and then `q m` to the window at `acc + 4i`, which holds `T`, the number
below `2m` in the accumulator's words from `i` up: `q` makes the
sum's low word zero, so the accumulator's words from `i + 1` up hold
`(T + a_i B + q m) / 2³²`, below `2m` again; `ZF` is whether `i + 1 = N`.
-/

@[expose] public section

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The registers the arithmetic changes. -/
def clob : List Reg := [.eax, .ebx, .ecx, .edx, .ebp]

/-- `t₀ + (t₀ m' mod 2³²) m ≡ 0 (mod 2³²)` when `m m' ≡ -1`. -/
theorem mont_low32 (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 32 = 0) :
    (t0 + t0 * minv % 2 ^ 32 * m) % 2 ^ 32 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 32), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod, show t0 + t0 * minv * m = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m]; omega_using [],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

/-- `-m⁻¹ mod 2⁶⁴` gives `-m⁻¹ mod 2³²`. -/
theorem minv32_inv {M : Mod} {m : Nat} (h : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    (m * (minv32 M).toNat + 1) % 2 ^ 32 = 0 := by
  rw [minv32, BitVec.toNat_setWidth, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    ← Nat.mod_mod_of_dvd (m * M.minv.toNat + 1) (show 2 ^ 32 ∣ 2 ^ 64 from ⟨2 ^ 32, by decide⟩), h]

/-- A row's sum stays below `2m` once divided. -/
theorem row_lt {T a B q m : Nat} (hT : T < 2 * m) (ha : a < 2 ^ 32) (hB : B < m) (hq : q < 2 ^ 32) :
    T + a * B + q * m < 2 ^ 32 * (2 * m) := by
  have h1 : a * B ≤ (2 ^ 32 - 1) * B := Nat.mul_le_mul_right _ (by omega_using [ha])
  have h2 : q * m ≤ (2 ^ 32 - 1) * m := Nat.mul_le_mul_right _ (by omega_using [hq])
  omega_using [hT, hB, h1, h2]

/-- The offsets of a multiplication: `[a]`, `[b]` and the modulus (`N`
words) in the working space and apart from the accumulator (`2N + 1` words
at `acc`). -/
structure MulLay (N size acc a b mo : Nat) : Prop where
  acc_le : acc + 4 * (2 * N + 1) ≤ size
  a_le : a + 4 * N ≤ size
  b_le : b + 4 * N ≤ size
  mo_le : mo + 4 * N ≤ size
  sa : a + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ a
  sb : b + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ b
  smo : mo + 4 * N ≤ acc ∨ acc + 4 * (2 * N + 1) ≤ mo

/-- `ZF` after the loop's comparison: whether `ebp` reached `edi + 4N`. -/
theorem row_zf (e : BitVec 32) {i N : Nat} (hi : i < N) (hN : 4 * N < 2 ^ 32) :
    (e + BitVec.ofNat 32 (4 * i) + 4 - (e + BitVec.ofNat 32 (4 * N)) == 0) = decide (i + 1 = N) := by
  by_cases h : i + 1 = N
  · subst h; simp only [decide_true, beq_iff_eq]; bv_omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]; bv_omega

theorem row_ebp (e : BitVec 32) (i : Nat) :
    e + BitVec.ofNat 32 (4 * i) + 4 = e + BitVec.ofNat 32 (4 * (i + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have : (4 : BitVec 32).toNat = 4 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, this]
  omega_using []

end VG.Proof.Mont.X86
