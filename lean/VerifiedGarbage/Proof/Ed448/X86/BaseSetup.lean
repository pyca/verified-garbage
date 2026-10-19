module

public import VerifiedGarbage.Proof.X448.X86.Env
import VerifiedGarbage.Proof.X448.X86.RowMem
public import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.Ed448.Scalar
public import VerifiedGarbage.Impl.Ed448.X86.ScalarBase
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Framework.Range

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
open VG.Impl.Ed448.X86 (initVal initLimb initStep initSlot zeroSlots initSlots)
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

/-- The 704 words of the slots zeroed. -/
theorem zeroSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa zeroSlots s fun t => (∀ j < 704, word t.mem base (64 + 4 * j) = 0) ∧
      Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t := by
  -- After `n` words.
  let inv : Nat → State → Prop := fun n t => Scr t base ∧
    t.gpr .ebp = t.gpr .edi + BitVec.ofNat 32 (4 * (16 + n)) ∧ t.gpr .ebx = 0 ∧
    t.gpr .eax = BitVec.ofNat 32 (704 - n) ∧ (∀ j < n, word t.mem base (64 + 4 * j) = 0) ∧
    Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t
  unfold zeroSlots
  refine WP.seq (wp_mov rfl fun u₁ hu₁ => wp_alu (Or.inl rfl) rfl fun u₂ hu₂ _ => wp_mov rfl fun u₃ hu₃ =>
    wp_mov rfl fun u hu => WP.block_nil ?_)
  have ku : Keeps [.eax, .ebx, .ebp] s u :=
    (hu₁.rest (by decide)).trans ((hu₂.rest (by decide)).trans ((hu₃.rest (by decide)).trans (hu.rest (by decide))))
  have i₀ : inv 0 u := by
    refine ⟨hs.of_keeps ku (by decide), ?_, by rw [hu.other _ (by decide), hu₃.gpr], hu.gpr,
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [hu.mem, hu₃.mem, hu₂.mem, hu₁.mem]; exact Outside.refl _ _ _ _,
      ku⟩
    rw [hu.other _ (by decide), hu₃.other _ (by decide), hu₂.gpr, hu.other _ (by decide), hu₃.other _ (by decide),
      hu₂.other _ (by decide), hu₁.gpr, hu₁.other _ (by decide)]
    rfl
  refine WP.mono (WP.loop (M := isa) (Q := inv 704) (fun m t => ∃ n, m = 704 - n ∧ n < 704 ∧ inv n t) ?_ 704 u
    ⟨0, rfl, by decide, i₀⟩) fun t ⟨_, _, _, _, z, o, k⟩ => ⟨z, o, k⟩
  rintro m t ⟨n, rfl, hn, ts, tp, tb, ta, tz, tm, tk⟩
  refine wp_store (a := off base (64 + 4 * n)) (by rw [rowEa ts tp (by omega)]; congr 1; omega)
    (ts.write (by omega)) fun v hv => ?_
  refine wp_alu (Or.inl rfl) rfl fun w hw _ => wp_alu (Or.inr (Or.inl rfl)) rfl fun x hx hz => WP.block_nil ?_
  have kx : Keeps [.eax, .ebx, .ebp] t x :=
    (hv.rest _).trans ((hw.rest (by decide)).trans (hx.rest (by decide)))
  have mx : x.mem = t.mem.writeW (off base (64 + 4 * n)) (0 : BitVec 32) := by
    rw [hx.mem, hw.mem, hv.mem, tb]
  have ax : x.gpr .eax = BitVec.ofNat 32 (704 - (n + 1)) := by
    rw [hx.gpr, hw.other _ (by decide), hv.gpr, ta]
    simp only [aluVal]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega)
      (by omega)]
    congr 1
  have nx : inv (n + 1) x := by
    refine ⟨ts.of_keeps kx (by decide), ?_, ?_, ax, fun j hj => ?_, ?_, tk.trans kx⟩
    · rw [hx.other _ (by decide), hw.gpr, hv.gpr, tp, kx.1 _ (by decide)]
      simp only [aluVal]
      rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2
    · exact (hx.other _ (by decide)).trans ((hw.other _ (by decide)).trans ((congrFun hv.gpr _).trans tb))
    · rw [mx, word_write t.mem base (o := 64) (by omega) (by omega)]
      by_cases e : j = n
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact tz j (by omega)
    · rw [mx]; exact tm.trans ((writeW_outside _ _ _ (by omega)).mono (by omega) (by omega))
  simp only [eval, hz, Option.map_some]
  by_cases done : n + 1 = 704
  · refine .inl ⟨?_, done ▸ nx⟩
    rw [hw.other _ (by decide), hv.gpr, ta]
    simp only [aluVal]
    rw [show n = 703 by omega]; decide
  · refine .inr ⟨?_, 704 - (n + 1), by omega, n + 1, rfl, by omega, nx⟩
    rw [hw.other _ (by decide), hv.gpr, ta]
    simp only [aluVal]
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega)
      (by omega)]
    have hlt : 704 - n - 1 < 2 ^ 32 := by omega
    have h0 : BitVec.ofNat 32 (704 - n - 1) ≠ 0 := fun h => by
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this
      have h2 : 704 - n - 1 = 0 := this.trans rfl
      omega
    simpa using h0

theorem initStep_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) {i k : Nat} (hi : i < 22) (hk : k < 28)
    (hz : limbs s.mem base (slot i) k = 0) :
    WP isa (.block (initStep i k)) s fun t =>
      limbs t.mem base (slot i) k = initLimb i k ∧ Outside base (slot i + 4 * k) 4 s.mem t.mem ∧
        Keeps [.eax] s t := by
  have hsl : slot i + 4 * k + 4 ≤ 4096 := by simp only [slot]; omega
  unfold initStep
  split
  · rename_i h0
    exact WP.block_nil ⟨by rw [hz, h0], Outside.refl _ _ _ _, Keeps.refl _ _⟩
  · refine wp_mov rfl fun u hu => ?_
    have hsu := hs.of_upd hu (by decide)
    refine wp_store (a := off base (slot i + 4 * k))
      (by rw [rowEa hsu (by rw [hu.other .ebp (by decide), hu.other .edi (by decide)]; exact hp) (by omega)]
          congr 1; simp only [slot]; omega)
      (hsu.write (by omega)) fun t ht => WP.block_nil ⟨?_, ?_, (hu.rest (by decide)).trans (ht.rest _)⟩
    · change (Proof.X448.X86.word t.mem base (slot i + 4 * k)).toNat = _
      rw [ht.mem, hu.gpr, Proof.X448.X86.word, Mem.readW_writeW_self32, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := initLimb_lt i k; omega)]
    · rw [ht.mem, hu.mem]; exact writeW_outside _ _ _ (by omega)

theorem initSlot_ok {s : State} {base : Addr} (hs : Scr s base)
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * 16)) {i : Nat}
    (hi : i < 22) (hz : ∀ k < 28, limbs s.mem base (slot i) k = 0) :
    WP isa (.block (initSlot i)) s fun t =>
      (∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t := by
  have hsl : slot i + 112 ≤ 4096 := by simp only [slot]; omega
  let inv := fun n (t : State) => (∀ k < n, limbs t.mem base (slot i) k = initLimb i k) ∧
    (∀ k, n ≤ k → k < 28 → limbs t.mem base (slot i) k = 0) ∧
    Outside base (slot i) 112 s.mem t.mem ∧ Keeps [.eax] s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 28) inv (fun n t hn ⟨tf, t0, tm, tk⟩ => ?_) 28 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun k _ hk => hz k hk, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, tk⟩
  refine WP.mono (initStep_ok (hs.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hp) hi hn (t0 n (Nat.le_refl _) hn))
    fun u ⟨uf, um, uk⟩ => ⟨fun k hk => ?_, fun k hk hk' => ?_, tm.trans (um.mono (by omega) (by omega)),
      tk.trans uk⟩
  · by_cases h : k = n
    · rw [h]; exact uf
    · change (Proof.X448.X86.word u.mem base (slot i + 4 * k)).toNat = _
      rw [um.word (by omega) (by simp only [slot]; omega)]
      exact tf k (by omega)
  · change (Proof.X448.X86.word u.mem base (slot i + 4 * k)).toNat = _
    rw [um.word (by omega) (by simp only [slot]; omega)]
    exact t0 k (by omega) hk'

theorem initSlots_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa initSlots s fun t =>
      (∀ i < 22, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
        Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax, .ebx, .ebp] s t := by
  unfold initSlots
  refine WP.seq (WP.mono (zeroSlots_ok hs) fun s₀ ⟨z₀, o₀, k₀⟩ => ?_)
  have hs₀ := hs.of_keeps k₀ (by decide)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov rfl fun u₁ hu₁ => wp_alu (Or.inl rfl) rfl fun u hu _ => ?_
  have hsu := (hs₀.of_upd hu₁ (by decide)).of_upd hu (by decide)
  have ku : Keeps [.eax, .ebx, .ebp] s u :=
    k₀.trans ((hu₁.rest (by decide)).trans (hu.rest (by decide)))
  have hpu : u.gpr .ebp = u.gpr .edi + BitVec.ofNat 32 (4 * 16) := by
    rw [hu.gpr, hu.other .edi (by decide), hu₁.other .edi (by decide)]
    change u₁.gpr .ebp + BitVec.ofNat 32 64 = _
    rw [hu₁.gpr]
  have mu : u.mem = s₀.mem := by rw [hu.mem, hu₁.mem]
  let inv := fun n (t : State) => (∀ i < n, ∀ k < 28, limbs t.mem base (slot i) k = initLimb i k) ∧
    (∀ i, n ≤ i → i < 22 → ∀ k < 28, limbs t.mem base (slot i) k = 0) ∧
    Outside base 64 2816 s.mem t.mem ∧ Keeps [.eax] u t
  have zu : ∀ i, 0 ≤ i → i < 22 → ∀ k < 28, limbs u.mem base (slot i) k = 0 := fun i _ hi k hk => by
    change (Proof.X448.X86.word u.mem base (slot i + 4 * k)).toNat = 0
    rw [mu, show slot i + 4 * k = 64 + 4 * (32 * i + k) by simp only [slot]; omega, z₀ _ (by omega)]
    rfl
  have i0 : inv 0 u := ⟨fun _ h => absurd h (Nat.not_lt_zero _), zu, by rw [mu]; exact o₀, Keeps.refl _ _⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv (fun n t hn ⟨tf, t0, tm, tk⟩ => ?_) 22
    (by decide) u i0)
    fun t ⟨tf, _, tm, tk⟩ => ⟨tf, tm, ku.trans (tk.mono (by simp))⟩
  refine WP.mono (initSlot_ok (hsu.of_keeps tk (by decide))
    (by rw [tk.1 _ (by decide), tk.1 _ (by decide)]; exact hpu) hn (t0 n (Nat.le_refl _) hn))
    fun v ⟨vf, vm, vk⟩ => ⟨fun i hi k hk => ?_, fun i hi hi' k hk => ?_,
      tm.trans (vm.mono (by simp only [slot]; omega) (by simp only [slot]; omega)), tk.trans vk⟩
  · by_cases h : i = n
    · subst h; exact vf k hk
    · rw [vm.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) hk]
      exact tf i (by omega) k hk
  · rw [vm.limbs (by simp only [slot]; omega) (by simp only [slot]; omega) hk]
    exact t0 i (by omega) hi' k hk

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
