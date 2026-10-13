module

public import VerifiedGarbage.Proof.X448.X86.Env
public import VerifiedGarbage.Proof.X448.X86.RowMem
public import VerifiedGarbage.Proof.X448.X86.Bits
public import VerifiedGarbage.Proof.Ed448.Scalar
public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Ed448 base-point multiplication on x86 (32-bit): the entry

Every slot set to its initial value (`initSlots_ok`): `R = (0 : 1 : 1)`, `B`
the base point, `d`, and zero elsewhere, every limb below `2¹⁶`. Then the
scalar's 57 bytes expanded into its 456 bits at `BITS` (`baseBytes_ok`), by
X448's `bitsLoop`.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (initVal initLimb initStep initSlot initSlots)
open VG.Impl.X448.X86 (slot ACC st BITS bitsLoop at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-! ## The slots -/

theorem initVal_lt (i : Nat) : initVal i < Spec.X448.P := by
  unfold initVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | split)
  decide +kernel

theorem initLimb_lt (i k : Nat) : initLimb i k < 65536 := Nat.mod_lt _ (by decide)

theorem valN_digits (v : Nat) : ∀ n, valN (fun k => v / 2 ^ (16 * k) % 65536) n = v % radix ^ n
  | 0 => by simp [valN, Nat.mod_one]
  | n + 1 => by
    rw [valN_succ, valN_digits v n, Nat.mod_pow_succ, radix, ← Nat.pow_mul]

theorem initStep_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) (hb : s.gpr .ebx = 0) {i k : Nat}
    (hi : i < 22) (hk : k < 28) :
    WP isa (.block (initStep i k)) s fun t =>
      t.mem = s.mem.writeW (off base (slot i + 4 * k)) (BitVec.ofNat 32 (initLimb i k)) ∧
        Keeps [.eax] s t := by
  have hsl : slot i + 4 * k + 4 ≤ 4096 := by simp only [slot]; omega
  have ea : ∀ u : State, Scr u base → u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * 16) →
      u.ea (at_ .ebp (128 * i + 4 * k)) = off base (slot i + 4 * k) := fun u hu hpu => by
    rw [rowEa hu hpu (by omega)]; congr 1; simp only [slot]; omega
  unfold initStep
  split
  · rename_i h0
    refine wp_store (ea s hs hp) (hs.write (by omega)) fun t ht => WP.block_nil ⟨?_, ht.rest _⟩
    rw [ht.mem, hb, h0]; rfl
  · refine wp_mov rfl fun u hu => ?_
    have hsu := hs.of_upd hu (by decide)
    refine wp_store (ea u hsu (by rw [hu.other .ebp (by decide), hu.other .edi (by decide)]; exact hp))
      (hsu.write (by omega)) fun t ht =>
      WP.block_nil ⟨by rw [ht.mem, hu.mem, hu.gpr], (hu.rest (by decide)).trans (ht.rest _)⟩

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) (hb : s.gpr .ebx = 0) {i : Nat}
    (hi : i < 22) :
    WP isa (.block (initSlot i)) s fun t =>
      (∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  have hsl : slot i + 112 ≤ 4096 := by simp only [slot]; omega
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t
  refine wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩
  refine WP.mono (initStep_ok (hs.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp) ((tk.1 _ (by decide)).trans hb) hi hn)
    fun u ⟨um, uk⟩ => ⟨fun k hk => ?_, tm.trans ?_, tk.trans uk⟩
  · change (word u.mem base (slot i + 4 * k)).toNat = _
    rw [um, word_write t.mem base (by omega) (by omega)]
    by_cases h : k = n
    · rw [ite_eq_left h, h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := initLimb_lt i n; omega)]
    · rw [ite_eq_right h]; exact tf k (by omega)
  · rw [um]; exact (writeW_outside _ _ _ (by omega)).mono (by omega) (by omega)

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block initSlots) s fun t =>
      (∀ i < 22, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t := by
  unfold initSlots
  refine wp_mov rfl fun u₁ hu₁ => wp_alu (Or.inl rfl) rfl fun u₂ hu₂ _ => wp_mov rfl fun u hu => ?_
  have hsu := ((hs.of_upd hu₁ (by decide)).of_upd hu₂ (by decide)).of_upd hu (by decide)
  have ku : Keeps [.eax, .ebx, .ebp] s u :=
    (hu₁.rest (by decide)).trans ((hu₂.rest (by decide)).trans (hu.rest (by decide)))
  have hpu : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * 16) := by
    rw [hu.other .ebp (by decide), hu.other .edi (by decide), hu₂.gpr, hu₂.other .edi (by decide),
      hu₁.other .edi (by decide)]
    change u₁.gpr .ebp + BitVec.ofNat 32 64 = _
    rw [hu₁.gpr]
  have mu : u.mem = s.mem := by rw [hu.mem, hu₂.mem, hu₁.mem]
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
    Outside base 64 2816 u.mem t.mem ∧ Keeps [.eax] u t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, tm, tk⟩ => ?_) 22
    (by decide) u ⟨fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, tm, tk⟩ => ⟨tf, by rw [← mu]; exact tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (initSlot_ok (hsu.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hpu) ((tk.1 _ (by decide)).trans hu.gpr) hn)
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, tm.trans (vm.mono (by simp only [slot]; omega)
      (by simp only [slot]; omega)), tk.trans vk⟩
  by_cases h : i = n
  · subst h; exact vf k hk
  · rw [vm.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) hk]
    exact tf i (by omega) k hk

/-- The slots' values. -/
theorem initSlots_E {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) (i : Index) :
    E m base i = Proof.X448.toFe (initVal i.val) := by
  simp only [E, F, fe]
  rw [valN_congr (g := fun k => initVal i.val / 2 ^ (16 * k) % 65536) (h i.val i.isLt), valN_digits,
    Nat.mod_eq_of_lt (Nat.lt_trans (initVal_lt _) (by decide +kernel))]

theorem initSlots_bounded {m : Mem} {base : Addr}
    (h : ∀ i < 22, ∀ k < 28, limbs m base (slot i) k = initLimb i k) : BoundedEnv m base :=
  fun i k hk => by rw [h i.val i.isLt k hk]; exact initLimb_lt _ _

/-! ## The scalar's bits -/

/-- The 57 bytes at `esi` expanded into their bits at `BITS` (X448's `bitsLoop_ok`). -/
theorem baseBytes_ok {s : State} {base k : Addr} (hs : Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ i < 57, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < 57, 8192 ≤ ofs base (off k i)) :
    WP isa (bitsLoop BITS 57) s fun t =>
      Keeps bitRegs s t ∧ Outside base BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> j) &&& 1) :=
  WP.mono (bitsLoop_ok hs (by decide) (by decide) (by decide) hk hfit hr hd) fun t ⟨tk, tm, tb, _⟩ =>
    ⟨tk, tm, fun j hj => by rw [tb j hj, Proof.Ed448.scalar_bit _ _ hj]⟩

end VG.Proof.Ed448.X86
