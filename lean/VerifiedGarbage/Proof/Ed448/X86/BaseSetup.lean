import VerifiedGarbage.Proof.X448.X86.Env
import VerifiedGarbage.Proof.X448.X86.RowMem
import VerifiedGarbage.Proof.X448.X86.BitWrite
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Impl.Ed448.X86.ScalarBase

/-!
# Ed448 base-point multiplication on x86 (32-bit): the entry

Every slot set to its initial value (`initSlots_ok`): `R = (0 : 1 : 1)`, `B`
the base point, `d`, and zero elsewhere, every limb below `2¹⁶`. Then the
scalar's 57 bytes expanded into its 456 bits at `BITS` (`baseBytes_ok`), as
X448 expands its scalar (`bitJ`).
-/

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Impl.Ed448.X86 (initVal initLimb initStep initSlot initSlots baseByte)
open VG.Impl.X448.X86 (slot ACC st BITS bitJ at_)
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

/-- `bitJ i j` for the 57 bytes of a scalar (X448's `bitJ_ok`, which is for
56). -/
theorem bitJ57_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJ i j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ Keeps [.edx] s t := by
  rw [Impl.X448.X86.bitJ, WP.block_append_iff]
  refine WP.mono (bitShift_ok hj) fun t ⟨tv, tm, tk⟩ => ?_
  refine wp_alu (by simp [plain]) rfl fun u hu _ => ?_
  have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
  have ea := us.ea (d := BITS + 8 * i + j) (by simp only [BITS]; omega)
  have wr := us.write (d := BITS + 8 * i + j) (n := 1) (by simp only [BITS]; omega)
  refine wp_store8 ea wr fun v hv => WP.block_nil ⟨?_, tk.trans ?_⟩
  · rw [hv.mem, hu.mem, tm, Reg8.reg, hu.gpr]
    change s.mem.writeW _ ((t.gpr .edx &&& (1 : BitVec 32)).setWidth 8) = _
    rw [tv, ha, bit_byte b j hj, Nat.add_assoc]
  · exact (hu.rest (by decide)).trans (hv.rest _)

theorem byteBits57_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 57)
    {b : BitVec 8} (ha : s.gpr .eax = b.setWidth 32) :
    WP isa (.block ((List.range 8).flatMap (bitJ i))) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.edx] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitJ i n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (bitJ57_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

/-- The 57 bytes at `esi` expanded into their bits at `BITS`. -/
theorem baseBytes_ok {s : State} {base k : Addr} (hs : Scr s base)
    (hk : (s.gpr .esi).setWidth 64 = k) (hfit : (s.gpr .esi).toNat + 57 ≤ 2 ^ 32)
    (hr : ∀ i < 57, InRegions (s.rd ++ s.wr) (off k i) 1)
    (hd : ∀ i < 57, 8192 ≤ ofs base (off k i)) :
    WP isa (.block ((List.range 57).flatMap baseByte)) s fun t =>
      Keeps [.eax, .edx] s t ∧ Outside base BITS 456 s.mem t.mem ∧
      ∀ j < 456, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> j) &&& 1) := by
  let inv := fun n (t : State) => Keeps [.eax, .edx] s t ∧ Outside base BITS (8 * n) s.mem t.mem ∧
    ∀ j < 8 * n, t.mem (off base (BITS + j)) =
      BitVec.ofNat 8 (((s.mem (off k (j / 8))).toNat >>> (j % 8)) &&& 1)
  have step : ∀ n t, n < 57 → inv n t → WP isa (.block (baseByte n)) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tm, tb⟩
    have ea : t.ea (at_ .esi n) = off k n := by
      change addr (t.gpr .esi) n = _
      rw [tk.1 _ (by decide), addr_eq (by omega), hk]
    unfold baseByte
    refine wp_load8 ea (by rw [tk.2.1, tk.2.2]; exact hr n hn) fun u hu => ?_
    have us := (hs.of_keeps tk (by decide)).of_upd hu (by decide)
    refine WP.mono (byteBits57_ok us hn hu.gpr) fun v ⟨vb, vm, vk⟩ => ?_
    have byte : t.mem (off k n) = s.mem (off k n) :=
      tm _ (Or.inr (by have := hd n hn; simp only [BITS]; omega))
    refine ⟨tk.trans ((hu.rest (by decide)).trans (vk.mono (by simp))), ?_, ?_⟩
    · rw [hu.mem] at vm
      exact (tm.mono (by omega) (by omega)).trans (vm.mono (by omega) (by omega))
    · intro j hj
      rcases Nat.lt_or_ge j (8 * n) with h | h
      · rw [vm _ (Or.inl (by rw [ofs_off' base (by simp only [BITS]; omega)]; omega)), hu.mem]
        exact tb j h
      · have e := vb (j - 8 * n) (by omega)
        rw [show 8 * n + (j - 8 * n) = j by omega, byte] at e
        rw [e, show j / 8 = n by omega, show j % 8 = j - 8 * n by omega]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 57) inv step 57 (by decide) s
    ⟨Keeps.refl _ _, Outside.refl _ _ _ _, fun _ hj => by omega⟩) fun t ⟨tk, tm, tb⟩ =>
    ⟨tk, tm, fun j hj => by rw [tb j hj, Proof.Ed448.scalar_bit _ _ hj]⟩

end VG.Proof.Ed448.X86
