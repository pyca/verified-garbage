import VerifiedGarbage.Impl.Ed448.AArch64.ScalarBase
import VerifiedGarbage.Proof.X448.AArch64.BitBody
import VerifiedGarbage.Proof.X448.AArch64.Finish
import VerifiedGarbage.Proof.Ed448.Scalar

/-!
# Ed448 base-point multiplication on AArch64: the scalar's bits

`bits`: the 57 bytes of the scalar, each expanded into its eight bits at
`BITS` (byte `t` is bit `t`, X448's `bitHead` and `bitJ`), counting `x19`
up to 57; then the output pointer into `x1`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off Outside ofs bitHead bitJ bitHead_ok byteBits_ok bitRegs
  moveOutput_ok)
open VG.Impl.X448.AArch64 (BITS)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem bitTail_ok {s : State} {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) :
    WP isa (.block ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 57) ∧
      t.mem = s.mem ∧ Keeps [.x19, .x11] s t := by
  have check : ∀ n < 57,
      ((BitVec.ofNat 64 n + BitVec.ofNat 64 1 - BitVec.ofNat 64 57) == 0) = decide (n + 1 = 57) :=
    by decide +kernel
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write, hb, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨(BitVec.ofNat_add _ _).symm, check i hi, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem bitsBody_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) (hc : s.gpr .x8 = 1)
    (hkr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block bitsBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 57) ∧
      t.gpr .x8 = 1 ∧ Keeps bitRegs s t ∧
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (bitHead ++ (List.range 8).flatMap bitJ ++
    ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (bitHead_ok hs hk hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  have tc : t.gpr .x8 = 1 := (tk.1 _ (by decide)).trans hc
  rw [WP.block_append_iff]
  refine WP.mono (byteBits_ok (hs.of_keeps tk (by decide)) hi tp tc ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .x19 = BitVec.ofNat 64 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (bitTail_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tc), ?_, ?_, ?_⟩
  · refine (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_))
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The loop's invariant, after `i` bytes. -/
structure BInv (base k : Addr) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  x1 : s.gpr .x1 = k
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x8 = 1
  gpr : ∀ r, r ∉ bitRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base BITS 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (BITS + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsLoop_ok {s₀ : State} {base k : Addr}
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    ∀ i, ∀ s, i < 57 → BInv base k s₀ s i →
      WP isa (.loop (.block bitsBody) (.nonzero .x .x11)) s fun s' => BInv base k s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block bitsBody) (c := .nonzero .x .x11)
    (Q := fun s' => BInv base k s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ BInv base k s₀ s i) ?_ (57 - i) s ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBody_ok hb.scr hb.x1 hi hb.x19 hb.one (by rw [hb.rd, hb.wr]; exact hkr i hi))
    fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 i) = s₀.mem (k + BitVec.ofNat 64 i) :=
    hb.mem _ (by have := hkd i hi; simp only [BITS]; omega)
  have inv : BInv base k s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.x3, (g' _ (by decide)).trans hb.scr.mask, wr' ▸ hb.scr.wr,
      hb.scr.nowrap⟩, (g' _ (by decide)).trans hb.x1, b', one', fun r hr => (g' r hr).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)),
      fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · have hofs : ofs base (off base (BITS + t)) = BITS + t :=
        Mem.sub_ofNat_toNat base (by simp only [BITS]; omega)
      rw [o' _ (by rw [hofs]; omega), hb.bits t h]
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
  simp only [eval, State.read, BitVec.setWidth_eq, bne, z']
  rcases Nat.lt_or_ge (i + 1) 57 with h | h
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬i + 1 = 57), Bool.not_false],
      57 - (i + 1), by omega, i + 1, rfl, h, inv⟩
  · obtain rfl : i = 56 := by omega
    exact .inl ⟨rfl, inv⟩

/-- `bits`: byte `t` of `BITS` is bit `t` of the scalar, for `t < 456`; then
`x1` is the output pointer, from `x20`. -/
theorem bits_ok {s : State} {base k : Addr} (hs : Scr s base) (hk : s.gpr .x1 = k)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 q) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 q)) :
    WP isa bits s fun s' =>
      s'.gpr .x1 = s.gpr .x20 ∧ (∀ r, r ∉ .x1 :: bitRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Outside base BITS 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (BITS + t)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem k 57) >>> t) &&& 1) := by
  rw [bits]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => BInv base k s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      Option.some.injEq, exists_eq_left']
    refine ⟨⟨?_, ?_, hs.wr, hs.nowrap⟩, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
      VG.Proof.X448.AArch64.Outside.refl _ _ _ _, fun t ht => absurd ht (by omega)⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.x3
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.mask
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hk
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; rfl
    · rw [RegUpd.gpr_write_self]; rfl
    · have h19 : r ≠ .x19 := fun h => hr (by subst r; decide)
      have h8 : r ≠ .x8 := fun h => hr (by subst r; decide)
      simp only [RegUpd.gpr_write, h19, h8, ite_false]) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (bitsLoop_ok hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_)
  refine WP.mono (moveOutput_ok s₂) fun s₃ ⟨x1₃, m₃, k₃⟩ => ?_
  refine ⟨x1₃.trans (h₂.gpr _ (by decide)), fun r hr => ?_, k₃.2.1.trans h₂.rd, k₃.2.2.trans h₂.wr,
    by rw [m₃]; exact h₂.mem, fun t ht => ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    rw [k₃.1 r (by simp only [List.mem_singleton]; exact hr.1)]
    exact h₂.gpr r (by simp only [bitRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr ⊢; exact hr.2)
  · rw [m₃, h₂.bits t (by omega), scalar_bit s.mem k ht]

end VG.Proof.Ed448.AArch64
