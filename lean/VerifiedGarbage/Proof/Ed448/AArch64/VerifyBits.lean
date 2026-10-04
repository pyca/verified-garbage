import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
import VerifiedGarbage.Proof.X448.AArch64.BitBody
import VerifiedGarbage.Proof.Ed448.Scalar

/-!
# Ed448 verification's equation on AArch64: the scalars' bits

`bitsAt src so d1 d2`: the 57 bytes at `src + so`, each expanded into its
eight bits at `x3 + 8 x19 + d1 + d2` (X448's expansion, with the source and
the destination as parameters): the bits of `S` at `BITS`, and those of `k`
at `2 KOFF` (through `x11 + KOFF`, beyond `strb`'s immediates).
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off Outside ofs read1_eq write1_eq writeW8_apply writeW8_outside
  off_eq_iff bit_byte)
open VG.Spec.Ed448 (bytesAt decodeLE)

theorem bitHeadAt_ok {s : State} {base k : Addr} (hs : Scr s base) {src : Reg} (hk : s.gpr src = k)
    {so d1 i : Nat} (hso : so < 4096) (hd1 : d1 < 4096) (hb : s.gpr .x19 = BitVec.ofNat 64 i)
    (hkr : InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 (so + i)) 1) :
    WP isa (.block ([.add .x .x11 src .x19, .ldrb .x4 .x11 so, .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11,
        .addImm .x .x11 .x11 d1] : List Instr)) s fun t =>
      t.gpr .x4 = (s.mem (k + BitVec.ofNat 64 (so + i))).setWidth 64 ∧ t.gpr .x11 = off base (8 * i + d1) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x11] s t := by
  have enc : so % 1 = 0 ∧ so < 4096 := ⟨Nat.mod_one _, hso⟩
  have ha : k + BitVec.ofNat 64 i + BitVec.ofNat 64 so = k + BitVec.ofNat 64 (so + i) := by
    rw [Offset.add_add, Nat.add_comm]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, RegUpd.gpr_write, hd1,
    RegUpd.rd_write, RegUpd.wr_write, RegUpd.mem_write, hk, hb, hs.x3,
    addr, enc, and_self, ha,
    State.load, hkr, read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    have := (s.mem (k + BitVec.ofNat 64 (so + i))).isLt
    omega
  · rw [off, ← Offset.add_add]
    congr 1
    · apply congrArg (base + ·)
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      change (i % 2 ^ 64 * 8) % 2 ^ 64 = (8 * i) % 2 ^ 64
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

def bitJAt (d2 j : Nat) : List Instr :=
  [.lsr .x .x5 .x4 j, .logic .and .x .x5 .x5 .x8, .strb .x5 .x11 (d2 + j)]

theorem bitJAt_ok {s : State} {base : Addr} (hs : Scr s base) {d1 d2 i : Nat} (hd2 : d2 + 8 ≤ 4096)
    (hD : d1 + d2 + 8 * i + 8 ≤ 8192)
    (hp : s.gpr .x11 = off base (8 * i + d1)) (hc : s.gpr .x8 = 1)
    {b : BitVec 8} (ha : s.gpr .x4 = b.setWidth 64) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJAt d2 j)) s fun t =>
      t.mem = s.mem.writeW (off base (d1 + d2 + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Keeps [.x5] s t := by
  have w := hs.write (d := d1 + d2 + (8 * i + j)) (n := 1) (by omega)
  have enc : (d2 + j) % 1 = 0 ∧ d2 + j < 4096 := by omega
  have shift : j < 64 := by omega
  have ea : base + BitVec.ofNat 64 (8 * i + d1) + BitVec.ofNat 64 (d2 + j) =
      base + BitVec.ofNat 64 (d1 + d2 + (8 * i + j)) := by
    rw [Offset.add_add]; congr 2; omega
  apply WP.of_runBlock
  simp only [bitJAt, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, shift, addr, enc, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, hp, hc, ha, off, ea,
    State.store, w, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, write1_eq, bit_byte b j hj, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Expanding eight bits preserves each byte already written. -/
theorem byteBitsAt_ok {s : State} {base : Addr} (hs : Scr s base) {d1 d2 i : Nat} (hd2 : d2 + 8 ≤ 4096)
    (hD : d1 + d2 + 8 * i + 8 ≤ 8192)
    (hp : s.gpr .x11 = off base (8 * i + d1)) (hc : s.gpr .x8 = 1)
    {b : BitVec 8} (ha : s.gpr .x4 = b.setWidth 64) :
    WP isa (.block ((List.range 8).flatMap (bitJAt d2))) s fun t =>
      (∀ j < 8, t.mem (off base (d1 + d2 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (d1 + d2 + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (d1 + d2 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (d1 + d2 + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitJAt d2 n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (bitJAt_ok (hs.of_keeps tk (by decide)) hd2 hD
      ((tk.1 _ (by decide)).trans hp) ((tk.1 _ (by decide)).trans hc)
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (d1 + d2 + (8 * i + j)) = off base (d1 + d2 + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by omega) (by omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, VG.Proof.X448.AArch64.Outside.refl _ _ _ _, VG.Proof.X448.AArch64.Keeps.refl _ _⟩

theorem bitTailAt_ok {s : State} {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) :
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

def bitAtRegs : List Reg := [.x4, .x5, .x19, .x11]

theorem bitsBodyAt_ok {s : State} {base k : Addr} (hs : Scr s base) {src : Reg} (hk : s.gpr src = k)
    {so d1 d2 : Nat} (hso : so < 4096) (hd1 : d1 < 4096) (hd2 : d2 + 8 ≤ 4096)
    (hD : d1 + d2 + 456 ≤ 8192)
    {i : Nat} (hi : i < 57) (hb : s.gpr .x19 = BitVec.ofNat 64 i) (hc : s.gpr .x8 = 1)
    (hkr : InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 (so + i)) 1) :
    WP isa (.block (bitsBodyAt src so d1 d2)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x11 == 0) = decide (i + 1 = 57) ∧
      t.gpr .x8 = 1 ∧ Keeps bitAtRegs s t ∧
      (∀ j < 8, t.mem (off base (d1 + d2 + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 (so + i))).toNat >>> j) &&& 1)) ∧
      Outside base (d1 + d2 + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (([.add .x .x11 src .x19, .ldrb .x4 .x11 so, .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11,
      .addImm .x .x11 .x11 d1] : List Instr) ++ (List.range 8).flatMap (bitJAt d2) ++
      ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (bitHeadAt_ok hs hk hso hd1 hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  have tc : t.gpr .x8 = 1 := (tk.1 _ (by decide)).trans hc
  rw [WP.block_append_iff]
  refine WP.mono (byteBitsAt_ok (hs.of_keeps tk (by decide)) hd2 (by omega) tp tc ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .x19 = BitVec.ofNat 64 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (bitTailAt_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
  refine ⟨vb, vz, (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tc), ?_, ?_, ?_⟩
  · exact ((tk.mono (by decide)).trans (uk.mono (by decide))).trans (vk.mono (by decide))
  · rw [vm]; exact uf
  · rw [vm, ← tm]; exact um

/-- The loop's invariant, after `i` bytes. -/
structure BInvAt (base k : Addr) (src : Reg) (so D : Nat) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base
  src : s.gpr src = k
  x19 : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x8 = 1
  gpr : ∀ r, r ∉ .x8 :: bitAtRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base D 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (D + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (so + t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsAtLoop_ok {s₀ : State} {base k : Addr} {src : Reg} (hsrc : src ∉ .x8 :: bitAtRegs)
    {so d1 d2 : Nat} (hso : so + 57 ≤ 4096) (hd1 : d1 < 4096) (hd2 : d2 + 8 ≤ 4096) (hD : d1 + d2 + 456 ≤ 8192)
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 (so + q)) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 (so + q))) :
    ∀ i, ∀ s, i < 57 → BInvAt base k src so (d1 + d2) s₀ s i →
      WP isa (.loop (.block (bitsBodyAt src so d1 d2)) (.nonzero .x .x11)) s
        fun s' => BInvAt base k src so (d1 + d2) s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block (bitsBodyAt src so d1 d2)) (c := .nonzero .x .x11)
    (Q := fun s' => BInvAt base k src so (d1 + d2) s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ BInvAt base k src so (d1 + d2) s₀ s i) ?_ (57 - i) s
    ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (bitsBodyAt_ok hb.scr hb.src (by omega) hd1 hd2 hD hi hb.x19 hb.one
    (by rw [hb.rd, hb.wr]; exact hkr i hi)) fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 (so + i)) = s₀.mem (k + BitVec.ofNat 64 (so + i)) :=
    hb.mem _ (by have := hkd i hi; omega)
  have inv : BInvAt base k src so (d1 + d2) s₀ s' (i + 1) := by
    refine ⟨⟨(g' _ (by decide)).trans hb.scr.x3, (g' _ (by decide)).trans hb.scr.mask, wr' ▸ hb.scr.wr,
      hb.scr.nowrap⟩, (g' _ (fun h => hsrc (List.mem_cons_of_mem _ h))).trans hb.src, b', one',
      fun r hr => (g' r (fun h => hr (List.mem_cons_of_mem _ h))).trans (hb.gpr r hr),
      rd'.trans hb.rd, wr'.trans hb.wr, hb.mem.trans (o'.mono (by omega) (by omega)), fun t ht => ?_⟩
    rcases Nat.lt_or_ge t (8 * i) with h | h
    · have hofs : ofs base (off base (d1 + d2 + t)) = d1 + d2 + t := Mem.sub_ofNat_toNat base (by omega)
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

/-- `bitsAt src so d1 d2`: byte `t` at `d1 + d2` is bit `t` of the 57 bytes at `src + so`. -/
theorem bitsAt_ok {s : State} {base k : Addr} (hs : Scr s base) {src : Reg} (hk : s.gpr src = k)
    (hsrc : src ∉ .x8 :: bitAtRegs)
    {so d1 d2 : Nat} (hso : so + 57 ≤ 4096) (hd1 : d1 < 4096) (hd2 : d2 + 8 ≤ 4096) (hD : d1 + d2 + 456 ≤ 8192)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 (so + q)) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 (so + q))) :
    WP isa (bitsAt src so d1 d2) s fun s' =>
      (∀ r, r ∉ .x8 :: bitAtRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base (d1 + d2) 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (d1 + d2 + t)) =
        BitVec.ofNat 8 ((decodeLE (bytesAt s.mem (k + BitVec.ofNat 64 so) 57) >>> t) &&& 1) := by
  rw [bitsAt]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => BInvAt base k src so (d1 + d2) s s' 0) by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      Option.some.injEq, exists_eq_left']
    have h19 : src ≠ .x19 := fun h => hsrc (by subst h; decide)
    have h8 : src ≠ .x8 := fun h => hsrc (by subst h; decide)
    refine ⟨⟨?_, ?_, hs.wr, hs.nowrap⟩, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
      VG.Proof.X448.AArch64.Outside.refl _ _ _ _, fun t ht => absurd ht (by omega)⟩
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.x3
    · simpa only [RegUpd.gpr_write, reduceCtorEq, ite_false] using hs.mask
    · simpa only [RegUpd.gpr_write, h19, h8, ite_false] using hk
    · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true]; rfl
    · rw [RegUpd.gpr_write_self]; rfl
    · have h19 : r ≠ .x19 := fun h => hr (by subst r; decide)
      have h8 : r ≠ .x8 := fun h => hr (by subst r; decide)
      simp only [RegUpd.gpr_write, h19, h8, ite_false]) fun s₁ h₁ => ?_)
  refine WP.mono (bitsAtLoop_ok hsrc hso hd1 hd2 hD hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega), ← scalar_bit s.mem (k + BitVec.ofNat 64 so) ht, Offset.add_add]

end VG.Proof.Ed448.AArch64
