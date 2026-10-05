import VerifiedGarbage.Impl.Ed448.AArch64.VerifyEquation
import VerifiedGarbage.Proof.X448.AArch64.Main
import VerifiedGarbage.Proof.Ed448.Signing
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyChecks
import VerifiedGarbage.Proof.X448.AArch64.Weak.Main
import VerifiedGarbage.Proof.X448.AArch64.Base.Const

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyBits`. -/
section

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
    WP isa (.block (VG.Proof.Ed448.AArch64.bitJAt d2 j)) s fun t =>
      t.mem = s.mem.writeW (off base (d1 + d2 + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Keeps [.x5] s t := by
  have w := hs.write (d := d1 + d2 + (8 * i + j)) (n := 1) (by omega)
  have enc : (d2 + j) % 1 = 0 ∧ d2 + j < 4096 := by omega
  have shift : j < 64 := by omega
  have ea : base + BitVec.ofNat 64 (8 * i + d1) + BitVec.ofNat 64 (d2 + j) =
      base + BitVec.ofNat 64 (d1 + d2 + (8 * i + j)) := by
    rw [Offset.add_add]; congr 2; omega
  apply WP.of_runBlock
  simp only [VG.Proof.Ed448.AArch64.bitJAt, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
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
    WP isa (.block ((List.range 8).flatMap (VG.Proof.Ed448.AArch64.bitJAt d2))) s fun t =>
      (∀ j < 8, t.mem (off base (d1 + d2 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (d1 + d2 + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (d1 + d2 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (d1 + d2 + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (VG.Proof.Ed448.AArch64.bitJAt d2 n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (VG.Proof.Ed448.AArch64.bitJAt_ok (hs.of_keeps tk (by decide)) hd2 hD
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
      t.gpr .x8 = 1 ∧ Keeps VG.Proof.Ed448.AArch64.bitAtRegs s t ∧
      (∀ j < 8, t.mem (off base (d1 + d2 + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (k + BitVec.ofNat 64 (so + i))).toNat >>> j) &&& 1)) ∧
      Outside base (d1 + d2 + 8 * i) 8 s.mem t.mem := by
  change WP isa (.block (([.add .x .x11 src .x19, .ldrb .x4 .x11 so, .lsl .x .x11 .x19 3, .add .x .x11 .x3 .x11,
      .addImm .x .x11 .x11 d1] : List Instr) ++ (List.range 8).flatMap (VG.Proof.Ed448.AArch64.bitJAt d2) ++
      ([.addImm .x .x19 .x19 1, .subImm .x .x11 .x19 57] : List Instr))) s _
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.bitHeadAt_ok hs hk hso hd1 hb hkr) fun t ⟨ta, tp, tm, tk⟩ => ?_
  have tc : t.gpr .x8 = 1 := (tk.1 _ (by decide)).trans hc
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.byteBitsAt_ok (hs.of_keeps tk (by decide)) hd2 (by omega) tp tc ta) fun u ⟨uf, um, uk⟩ => ?_
  have ub : u.gpr .x19 = BitVec.ofNat 64 i := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hb)
  refine WP.mono (VG.Proof.Ed448.AArch64.bitTailAt_ok hi ub) fun v ⟨vb, vz, vm, vk⟩ => ?_
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
  gpr : ∀ r, r ∉ .x8 :: VG.Proof.Ed448.AArch64.bitAtRegs → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base D 456 s₀.mem s.mem
  bits : ∀ t < 8 * i, s.mem (off base (D + t)) =
    BitVec.ofNat 8 (((s₀.mem (k + BitVec.ofNat 64 (so + t / 8))).toNat >>> (t % 8)) &&& 1)

theorem bitsAtLoop_ok {s₀ : State} {base k : Addr} {src : Reg} (hsrc : src ∉ .x8 :: VG.Proof.Ed448.AArch64.bitAtRegs)
    {so d1 d2 : Nat} (hso : so + 57 ≤ 4096) (hd1 : d1 < 4096) (hd2 : d2 + 8 ≤ 4096) (hD : d1 + d2 + 456 ≤ 8192)
    (hkr : ∀ q < 57, InRegions (s₀.rd ++ s₀.wr) (k + BitVec.ofNat 64 (so + q)) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 (so + q))) :
    ∀ i, ∀ s, i < 57 → VG.Proof.Ed448.AArch64.BInvAt base k src so (d1 + d2) s₀ s i →
      WP isa (.loop (.block (bitsBodyAt src so d1 d2)) (.nonzero .x .x11)) s
        fun s' => VG.Proof.Ed448.AArch64.BInvAt base k src so (d1 + d2) s₀ s' 57 := by
  intro i s hi hb
  refine WP.loop (M := isa) (body := .block (bitsBodyAt src so d1 d2)) (c := .nonzero .x .x11)
    (Q := fun s' => VG.Proof.Ed448.AArch64.BInvAt base k src so (d1 + d2) s₀ s' 57)
    (fun m (s : State) => ∃ i, m = 57 - i ∧ i < 57 ∧ VG.Proof.Ed448.AArch64.BInvAt base k src so (d1 + d2) s₀ s i) ?_ (57 - i) s
    ⟨i, rfl, hi, hb⟩
  rintro m s ⟨i, rfl, hi, hb⟩
  refine WP.mono (VG.Proof.Ed448.AArch64.bitsBodyAt_ok hb.scr hb.src (by omega) hd1 hd2 hD hi hb.x19 hb.one
    (by rw [hb.rd, hb.wr]; exact hkr i hi)) fun s' ⟨b', z', one', keep', bits', o'⟩ => ?_
  obtain ⟨g', rd', wr'⟩ := keep'
  have hbyte : s.mem (k + BitVec.ofNat 64 (so + i)) = s₀.mem (k + BitVec.ofNat 64 (so + i)) :=
    hb.mem _ (by have := hkd i hi; omega)
  have inv : VG.Proof.Ed448.AArch64.BInvAt base k src so (d1 + d2) s₀ s' (i + 1) := by
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
    (hsrc : src ∉ .x8 :: VG.Proof.Ed448.AArch64.bitAtRegs)
    {so d1 d2 : Nat} (hso : so + 57 ≤ 4096) (hd1 : d1 < 4096) (hd2 : d2 + 8 ≤ 4096) (hD : d1 + d2 + 456 ≤ 8192)
    (hkr : ∀ q < 57, InRegions (s.rd ++ s.wr) (k + BitVec.ofNat 64 (so + q)) 1)
    (hkd : ∀ q < 57, 8192 ≤ ofs base (k + BitVec.ofNat 64 (so + q))) :
    WP isa (bitsAt src so d1 d2) s fun s' =>
      (∀ r, r ∉ .x8 :: VG.Proof.Ed448.AArch64.bitAtRegs → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base (d1 + d2) 456 s.mem s'.mem ∧
      ∀ t < 456, s'.mem (off base (d1 + d2 + t)) =
        BitVec.ofNat 8 ((VG.Spec.Ed448.decodeLE (VG.Spec.Ed448.bytesAt s.mem (k + BitVec.ofNat 64 so) 57) >>> t) &&& 1) := by
  rw [bitsAt]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .x .x19 0 0, .movz .x .x8 1 0]) s
      (fun s' => VG.Proof.Ed448.AArch64.BInvAt base k src so (d1 + d2) s s' 0) by
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
  refine WP.mono (VG.Proof.Ed448.AArch64.bitsAtLoop_ok hsrc hso hd1 hd2 hD hkr hkd 0 s₁ (by omega) h₁) fun s₂ h₂ => ?_
  refine ⟨h₂.gpr, h₂.rd, h₂.wr, h₂.mem, fun t ht => ?_⟩
  rw [h₂.bits t (by omega), ← scalar_bit s.mem (k + BitVec.ofNat 64 so) ht, Offset.add_add]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyBytes`. -/
section

/-!
# Ed448 verification's equation on AArch64: checks of the encodings' bytes

`sCheck`: `S < L` for the 57 bytes at `x1 + 57` (`carryK` of `2^448 - L`, and
byte 56). `decodeY`: the 56 bytes of `y` as eight seven-byte chunks in a
slot, `y < p` (`carryK` of `2^224 + 1`), bits 448–454 zero, and the sign bit
in `x17`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Proof.X25519 (leNum)
open VG.Impl.X448.AArch64 (ld st slot)

theorem ldrb5_ok (s : State) {rp : Reg} {p : Addr} (hp : s.gpr rp = p) {o : Nat} (ho : o < 4096)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 o) 1) :
    WP isa (.block [.ldrb .x5 rp o]) s fun t =>
      t.gpr .x5 = (s.mem (p + BitVec.ofNat 64 o)).setWidth 64 ∧ t.mem = s.mem ∧ Keeps [.x5] s t := by
  have enc : o % 1 = 0 ∧ o < 4096 := ⟨Nat.mod_one _, ho⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, enc, and_self, hp, State.load, hr,
    VG.Proof.X448.AArch64.read1_eq, RegUpd.gpr_write, RegUpd.mem_write,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, Size.bits]
    have := (s.mem (p + BitVec.ofNat 64 o)).isLt
    omega
  · simp only [List.mem_singleton] at hr
    simp only [State.write, hr, ite_false]

theorem setWidth8_eq_zero (b : Byte) : b.setWidth 64 = 0 ↔ b.toNat = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide))] at this
  · intro h; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt (by decide)), h]; rfl

theorem bytesAt_succ57 (m : Mem) (q : Addr) :
    Spec.Ed448.bytesAt m q 57 = Spec.X448.bytesAt m q 56 ++ [m (q + BitVec.ofNat 64 56)] := by
  simp only [Spec.Ed448.bytesAt, Spec.X448.bytesAt, List.range_succ, List.map_append, List.map_cons,
    List.map_nil]

/-- `sCheck`: `x20 |= c`, with `c = 0` exactly when the 57 bytes at `x1 + 57` are below `L`. -/
theorem sCheck_ok {s : State} {p : Addr} (hp : s.gpr .x1 = p)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 (57 + j)) 1) :
    WP isa (.block sCheck) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem (p + BitVec.ofNat 64 57) 57) <
        Spec.Ed448.L) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7, .x20] s t := by
  rw [sCheck]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.carryK_ok (rp := .x1) (o := 57) hp (by decide) (by decide)
    (fun j hj => hr j (by omega))) fun u ⟨u5, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.orBad_ok u) fun v ⟨v20, vm, vk⟩ => ?_
  rw [WP.block_append_iff]
  have pv : v.gpr .x1 = p := by rw [vk.1 _ (by decide), uk.1 _ (by decide)]; exact hp
  refine WP.mono (VG.Proof.Ed448.AArch64.ldrb5_ok v pv (o := 113) (by decide) (by
    rw [vk.2.1, vk.2.2, uk.2.1, uk.2.2]; exact hr 56 (by decide))) fun w ⟨w5, wm, wk⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.AArch64.orBad_ok w) fun t ⟨t20, tm, tk⟩ => ?_
  generalize hy : leNum (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56) = y at u5
  have hyl : y < 2 ^ 448 := by
    rw [← hy]
    have := VG.Proof.X25519.leNum_lt (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56)
    rw [VG.Proof.X448.length_bytesAt] at this
    exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))
  have hK : (2 ^ 448 - Spec.Ed448.L) % 2 ^ 448 = 2 ^ 448 - Spec.Ed448.L := by decide +kernel
  rw [hK] at u5
  have hb : v.mem (p + BitVec.ofNat 64 113) = s.mem (p + BitVec.ofNat 64 113) := by rw [vm, um]
  refine ⟨⟨u.gpr .x5 ||| w.gpr .x5, ?_, ?_⟩, ?_, ?_⟩
  · rw [VG.Proof.Ed448.AArch64.or_eq_zero64, w5, hb, VG.Proof.Ed448.AArch64.setWidth8_eq_zero, VG.Proof.Ed448.AArch64.bytesAt_succ57, VG.Proof.Ed448.decodeLE_append,
      Offset.add_add, VG.Proof.X448.length_bytesAt]
    rw [show Spec.Ed448.decodeLE [s.mem (p + BitVec.ofNat 64 (57 + 56))] = (s.mem (p + BitVec.ofNat 64 113)).toNat by
      simp [Spec.Ed448.decodeLE]]
    rw [show Spec.Ed448.decodeLE (Spec.X448.bytesAt s.mem (p + BitVec.ofNat 64 57) 56) = y by
      rw [← hy, VG.Proof.Ed448.decodeLE_eq]]
    have h1 := Nat.mod_add_div (y + (2 ^ 448 - Spec.Ed448.L)) (2 ^ 448)
    have h2 := Nat.mod_lt (y + (2 ^ 448 - Spec.Ed448.L)) (Nat.two_pow_pos 448)
    have h3 : (y + (2 ^ 448 - Spec.Ed448.L)) / 2 ^ 448 ≤ 1 := by
      apply Nat.le_of_lt_succ
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 448)]
      have := Nat.sub_le (2 ^ 448) Spec.Ed448.L
      omega
    have key := sCheck_nat (b := (s.mem (p + BitVec.ofNat 64 113)).toNat) hyl h2 h3 h1
    rw [← key]
    have hu : u.gpr .x5 = 0 ↔ (y + (2 ^ 448 - Spec.Ed448.L)) / 2 ^ 448 = 0 := by
      rw [← u5]
      exact ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
    rw [hu]
  · rw [t20, wk.1 _ (by decide), v20, uk.1 _ (by decide), BitVec.or_assoc]
  · rw [tm, wm, vm, um]
  · exact (((uk.mono (by decide)).trans (vk.mono (by decide))).trans (wk.mono (by decide))).trans (tk.mono (by decide))

/-! ## `y` -/

theorem wide_chunks (m : Mem) (q : Addr) :
    ∀ n, VG.Proof.X448.Wide.valN (fun i => VG.Proof.Ed448.AArch64.chunk7 m (q + BitVec.ofNat 64 (7 * i))) n =
      leNum (Spec.X448.bytesAt m q (7 * n))
  | 0 => rfl
  | n + 1 => by
    rw [VG.Proof.X448.Wide.valN_succ, VG.Proof.Ed448.AArch64.wide_chunks m q n, VG.Proof.Ed448.AArch64.leNum_chunks]
    congr 2
    rw [VG.Proof.X448.Wide.radix, ← Nat.pow_mul]

theorem byte56_val (b : Byte) :
    (b.setWidth 64 >>> 7) = BitVec.ofNat 64 (b.toNat / 128) ∧
      (b.setWidth 64 &&& BitVec.setWidth 64 (0x7f : BitVec 16)) = BitVec.ofNat 64 (b.toNat % 128) := by
  have hb := b.isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (BitVec.toNat (127 : BitVec 16)) % 2 ^ 64 = 2 ^ 7 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega : b.toNat % 2 ^ 7 < 2 ^ 64)]
    omega

/-- Byte 56: the sign bit into `x17`, and bits 448–454 into `x5`. -/
theorem byte56_ok (s : State) {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 56) 1) :
    WP isa (.block ([.ldrb .x5 rp 56, .lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0,
        .logic .and .x .x5 .x5 .x6] : List Instr)) s fun t =>
      t.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      t.gpr .x5 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) ∧
      t.mem = s.mem ∧ Keeps [.x5, .x6, .x17] s t := by
  rw [show ([.ldrb .x5 rp 56, .lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0, .logic .and .x .x5 .x5 .x6] : List Instr) =
    [.ldrb .x5 rp 56] ++ [.lsr .x .x17 .x5 7, .movz .x .x6 0x7f 0, .logic .and .x .x5 .x5 .x6] from rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.ldrb5_ok s hp (o := 56) (by decide) hr) fun u ⟨u5, um, uk⟩ => ?_
  have bv := VG.Proof.Ed448.AArch64.byte56_val (s.mem (p + BitVec.ofNat 64 56))
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, Nat.reduceMul,
    Nat.reduceLT, ite_true, BitVec.shiftLeft_zero, BitVec.setWidth_eq, RegUpd.gpr_write, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left', u5]
  refine ⟨bv.1, bv.2, um, (fun r hr => ?_), uk.2.1, uk.2.2⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [State.write, hr.1, hr.2.1, hr.2.2, ite_false]
  exact uk.1 r (by simp only [List.mem_singleton]; exact hr.1)

/-- The chunks of `y` into slot `yo`. -/
theorem yStores_ok {s : State} {base : Addr} (hs : Scr s base) {rp : Reg} {p : Addr} (hp : s.gpr rp = p)
    (h4 : rp ≠ .x4) (h7 : rp ≠ .x7) (yo : Fin 22)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (.block ((List.range 8).flatMap (fun i => bytes7 rp (7 * i) ++ [st .x4 (slot yo.val + 8 * i)]))) s
      fun t => (∀ i < 8, (VG.Proof.X448.AArch64.word t.mem base (slot yo.val + 8 * i)).toNat = VG.Proof.Ed448.AArch64.chunk7 s.mem (p + BitVec.ofNat 64 (7 * i))) ∧
        Outside base (slot yo.val) 64 s.mem t.mem ∧ Keeps [.x4, .x7] s t := by
  have hy := yo.isLt
  let inv := fun n (t : State) =>
    (∀ i < n, (VG.Proof.X448.AArch64.word t.mem base (slot yo.val + 8 * i)).toNat = VG.Proof.Ed448.AArch64.chunk7 s.mem (p + BitVec.ofNat 64 (7 * i))) ∧
      Outside base (slot yo.val) 64 s.mem t.mem ∧ Keeps [.x4, .x7] s t
  have step : ∀ n t, n < 8 → inv n t →
      WP isa (.block (bytes7 rp (7 * n) ++ [st .x4 (slot yo.val + 8 * n)])) t (inv (n + 1)) := by
    intro n t hn ⟨tv, tm, tk⟩
    have tp : t.gpr rp = p := by
      rw [tk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h7⟩)]; exact hp
    have hst : Scr t base := hs.of_keeps tk (by decide)
    rw [WP.block_append_iff]
    refine WP.mono (VG.Proof.Ed448.AArch64.bytes7_ok tp h4 h7 (o := 7 * n) (by omega) (fun j hj => by
      rw [tk.2.1, tk.2.2]; exact hr _ (by omega))) fun u ⟨u4, um, uk⟩ => ?_
    have hsu : Scr u base := hst.of_keeps uk (by decide)
    refine WP.mono (VG.Proof.X448.AArch64.store_ok hsu (d := slot yo.val + 8 * n) (by simp only [slot]; omega)
      (by simp only [slot]; omega) .x4) fun v ⟨vm, vk⟩ => ⟨fun i hi => ?_, ?_, (tk.trans uk).trans (vk.mono (by simp))⟩
    · rw [vm, VG.Proof.X448.AArch64.word_write_aligned _ _ (by simp only [slot]; omega) (by simp only [slot]; omega)
        (by simp only [slot]; omega) (by simp only [slot]; omega)]
      by_cases h : i = n
      · subst h
        rw [ite_eq_left rfl, u4]
        have hc : VG.Proof.Ed448.AArch64.chunk7 t.mem (p + BitVec.ofNat 64 (7 * i)) = VG.Proof.Ed448.AArch64.chunk7 s.mem (p + BitVec.ofNat 64 (7 * i)) := by
          apply congrArg leNum
          simp only [Spec.X448.bytesAt]
          refine List.map_congr_left fun j hj => ?_
          have hj := List.mem_range.mp hj
          rw [Offset.add_add]
          exact tm _ (Or.inr (by have := hfar (7 * i + j) (by omega); simp only [slot] at *; omega))
        exact hc
      · rw [ite_eq_right (by omega), um]; exact tv i (by omega)
    · intro x hx
      rw [vm, VG.Proof.X448.AArch64.writeW_outside _ _ _ (by simp only [slot]; omega) x (by omega), um]
      exact tm x hx
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), VG.Proof.X448.AArch64.Outside.refl _ _ _ _,
      VG.Proof.X448.AArch64.Keeps.refl _ _⟩

theorem P_add : Spec.X448.P + (2 ^ 224 + 1) = 2 ^ 448 := by decide +kernel

/-- `decodeY rp yo`: `y` (the first 56 bytes at `rp`) in slot `yo`, the sign bit in `x17`, and
`x20 |= c`, `c = 0` exactly when bits 448–454 are 0 and `y < p`. -/
theorem decodeY_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) {rp : Reg}
    {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (yo : Fin 22)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (.block (decodeY rp yo.val)) s fun t =>
      VG.Proof.X448.AArch64.Weak.E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ∧
      t.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) ∧
      (∃ c : BitVec 64, (c = 0 ↔ (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
          Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ i : Fin 22, i ≠ yo → VG.Proof.X448.AArch64.Weak.E t.mem base i = VG.Proof.X448.AArch64.Weak.E s.mem base i) ∧ BoundedEnv t.mem base ∧
      Keeps [.x4, .x5, .x6, .x7, .x17, .x20] s t ∧ Outside base (slot yo.val) 64 s.mem t.mem := by
  have hy := yo.isLt
  have h4 : rp ≠ .x4 := by rcases hrp with rfl | rfl <;> decide
  have h5 : rp ≠ .x5 := by rcases hrp with rfl | rfl <;> decide
  have h6 : rp ≠ .x6 := by rcases hrp with rfl | rfl <;> decide
  have h7 : rp ≠ .x7 := by rcases hrp with rfl | rfl <;> decide
  rw [decodeY]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.yStores_ok hs hp h4 h7 yo (fun j hj => hr j (by omega)) (fun j hj => hfar j (by omega)))
    fun a ⟨av, am, ak⟩ => ?_
  have hin : ∀ j < 57, a.mem (p + BitVec.ofNat 64 j) = s.mem (p + BitVec.ofNat 64 j) := fun j hj =>
    am _ (Or.inr (by have := hfar j hj; simp only [slot] at *; omega))
  have ap : a.gpr rp = p := by
    rw [ak.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h7⟩)]; exact hp
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.carryK_ok (o := 0) ap ⟨h4, h5, h6, h7⟩ (by decide) (fun j hj => by
    rw [ak.2.1, ak.2.2, Nat.zero_add]; exact hr j (by omega))) fun u ⟨u5, um, uk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.orBad_ok u) fun v ⟨v20, vm, vk⟩ => ?_
  have vp : v.gpr rp = p := by
    rw [vk.1 _ (by simp only [List.mem_singleton]; rcases hrp with rfl | rfl <;> decide),
      uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h4, h5, h6, h7⟩)]
    exact ap
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.byte56_ok v vp (by
    rw [vk.2.1, vk.2.2, uk.2.1, uk.2.2, ak.2.1, ak.2.2]; exact hr 56 (by decide))) fun w ⟨w17, w5, wm, wk⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.AArch64.orBad_ok w) fun t ⟨t20, tm, tk⟩ => ?_
  have hb56 : v.mem (p + BitVec.ofNat 64 56) = s.mem (p + BitVec.ofNat 64 56) := by
    rw [vm, um]; exact hin 56 (by decide)
  have hy56 : leNum (Spec.X448.bytesAt a.mem (p + BitVec.ofNat 64 0) 56) =
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) := by
    rw [BitVec.add_zero, VG.Proof.Ed448.decodeLE_eq]
    apply congrArg leNum
    simp only [Spec.X448.bytesAt, Spec.Ed448.bytesAt]
    exact List.map_congr_left fun j hj => hin j (by have := List.mem_range.mp hj; omega)
  have tmem : t.mem = a.mem := by rw [tm, wm, vm, um]
  -- The value of slot `yo`.
  have ey : VG.Proof.X448.AArch64.Weak.E t.mem base yo = VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) := by
    have w8 := VG.Proof.Ed448.AArch64.wide_chunks s.mem p 8
    rw [show 7 * 8 = 56 from rfl] at w8
    rw [VG.Proof.Ed448.decodeLE_eq, show Spec.Ed448.bytesAt s.mem p 56 = Spec.X448.bytesAt s.mem p 56 from rfl, ← w8, tmem]
    exact congrArg VG.Proof.X448.toFe (VG.Proof.X448.Wide.valN_congr fun i hi => av i hi)
  refine ⟨ey, ?_, ⟨u.gpr .x5 ||| w.gpr .x5, ?_, ?_⟩, fun i hi => ?_, fun i j hj => ?_, ?_, ?_⟩
  · rw [tk.1 _ (by decide), w17, hb56]
  · rw [VG.Proof.Ed448.AArch64.or_eq_zero64, w5, hb56]
    have hc : (u.gpr .x5).toNat = (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) + (2 ^ 224 + 1)) / 2 ^ 448 := by
      rw [u5, hy56, show ((2 : Nat) ^ 224 + 1) % 2 ^ 448 = 2 ^ 224 + 1 by decide +kernel]
    have hylt : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < 2 ^ 448 := by
      have := decodeLE_lt' (Spec.Ed448.bytesAt s.mem p 56)
      rw [show (Spec.Ed448.bytesAt s.mem p 56).length = 56 by simp [Spec.Ed448.bytesAt]] at this
      exact Nat.lt_of_lt_of_le this (Nat.le_of_eq (by decide +kernel))
    have hP := VG.Proof.Ed448.AArch64.P_add
    generalize Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) = y at hc hylt ⊢
    generalize (2 : Nat) ^ 448 = M at hc hylt hP
    have e1 : u.gpr .x5 = 0 ↔ y < Spec.X448.P := by
      constructor
      · intro h
        rw [h] at hc
        have : (y + (2 ^ 224 + 1)) / M = 0 := hc.symm
        rw [Nat.div_eq_zero_iff_lt (by omega)] at this
        omega
      · intro h
        apply BitVec.eq_of_toNat_eq
        rw [hc, Nat.div_eq_of_lt (by omega)]; rfl
    have e2 : BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128) = 0 ↔
        (s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      · intro h; rw [h]; rfl
    rw [e1, e2, and_comm]
  · rw [t20, wk.1 _ (by decide), v20, uk.1 _ (by decide), ak.1 _ (by decide), BitVec.or_assoc]
  · rw [tmem]
    exact VG.Proof.X448.AArch64.Weak.E_outside am i
      (by have := VG.Proof.X448.AArch64.Weak.slot_sep hi; omega)
  · rw [tmem]
    by_cases h : i = yo
    · subst h
      change (VG.Proof.X448.AArch64.word a.mem base (slot i.val + 8 * j)).toNat < _
      rw [av j hj]
      exact Nat.lt_of_lt_of_le (VG.Proof.Ed448.AArch64.chunk7_lt _ _) (by decide)
    · have := VG.Proof.X448.AArch64.Weak.slot_sep h
      have hil := i.isLt
      change (VG.Proof.X448.AArch64.word a.mem base (slot i.val + 8 * j)).toNat < _
      rw [am.word (by omega) (by simp only [slot]; omega)]
      exact hb i j hj
  · exact ((((ak.mono (by decide)).trans (uk.mono (by decide))).trans (vk.mono (by decide))).trans
      (wk.mono (by decide))).trans (tk.mono (by decide))
  · rw [tmem]; exact am

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyRoot`. -/
section

/-!
# Ed448 verification's equation on AArch64: the square root's power

`root 12` writes only the temporaries of X448's inversion (slots 14–21), the
products' coefficients and the counter `x19` (an `ISpec`, as X448's
inversion); slot 21 ends as `rootPow` of slot 12.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64.Weak (Env ISpec FieldOp applyOps opMul opCopy opSqn opsI sqnI)

/-- The slots after `root 12`. -/
def rootEnv (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.X448.AArch64.Weak.Env :=
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.copy 14 12] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 14 1 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 14 14 12, .copy 15 14] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 15 2 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 15 15 14, .copy 16 15] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 16 4 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 16 16 15, .copy 17 16] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 17 8 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 17 17 16, .copy 18 17] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 18 16 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 18 18 17, .copy 19 18] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 19 32 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 19 19 18, .copy 20 19] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 64 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 64 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 19] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 16 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 17] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 8 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 16] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 4 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 15] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 20 2 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 20 20 14, .copy 21 20] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 21 1 e
  let e := VG.Proof.X448.AArch64.Weak.applyOps [.mul 21 21 12] e
  let e := VG.Proof.X448.AArch64.Weak.opSqn 21 223 e
  VG.Proof.X448.AArch64.Weak.applyOps [.mul 21 21 20] e

theorem root_spec (base : Addr) : VG.Proof.X448.AArch64.Weak.ISpec base (root 12) VG.Proof.Ed448.AArch64.rootEnv := by
  have h : VG.Proof.X448.AArch64.Weak.ISpec base _ _ :=
    (VG.Proof.X448.AArch64.Weak.opsI base [.copy 14 12]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 14 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 14 14 12, .copy 15 14]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 15 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 15 15 14, .copy 16 15]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 16 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 16 16 15, .copy 17 16]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 17 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 17 17 16, .copy 18 17]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 18 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 18 18 17, .copy 19 18]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 19 (n := 32) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 19 19 18, .copy 20 19]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 64) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 19]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 16) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 17]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 8) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 16]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 4) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 15]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 20 (n := 2) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 20 20 14, .copy 21 20]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 21 (n := 1) (by decide) (by decide)).seq <|
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 21 21 12]).seq <|
    (VG.Proof.X448.AArch64.Weak.sqnI base 21 (n := 223) (by decide) (by decide)).seq
    (VG.Proof.X448.AArch64.Weak.opsI base [.mul 21 21 20])
  exact h

theorem rootEnv_eval (e : VG.Proof.X448.AArch64.Weak.Env) : VG.Proof.Ed448.AArch64.rootEnv e 21 = rootPow (e 12) := by
  simp only [↓reduceIte, VG.Proof.Ed448.AArch64.rootEnv, VG.Proof.X448.AArch64.Weak.applyOps, FieldOp.apply, opMul, opCopy, VG.Proof.X448.AArch64.Weak.opSqn,
    Function.update_apply]
  rfl

theorem rootEnv_keep (e : VG.Proof.X448.AArch64.Weak.Env) (i : Fin 22) (hi : i.val < 14) : VG.Proof.Ed448.AArch64.rootEnv e i = e i := by
  have h1 : i ≠ 14 := fun h => absurd hi (by rw [h]; decide)
  have h2 : i ≠ 15 := fun h => absurd hi (by rw [h]; decide)
  have h3 : i ≠ 16 := fun h => absurd hi (by rw [h]; decide)
  have h4 : i ≠ 17 := fun h => absurd hi (by rw [h]; decide)
  have h5 : i ≠ 18 := fun h => absurd hi (by rw [h]; decide)
  have h6 : i ≠ 19 := fun h => absurd hi (by rw [h]; decide)
  have h7 : i ≠ 20 := fun h => absurd hi (by rw [h]; decide)
  have h8 : i ≠ 21 := fun h => absurd hi (by rw [h]; decide)
  simp only [VG.Proof.Ed448.AArch64.rootEnv, VG.Proof.X448.AArch64.Weak.applyOps, FieldOp.apply, opMul, opCopy, VG.Proof.X448.AArch64.Weak.opSqn, Function.update_of_ne h1,
    Function.update_of_ne h2, Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5,
    Function.update_of_ne h6, Function.update_of_ne h7, Function.update_of_ne h8]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifySign`. -/
section

/-!
# Ed448 verification's equation on AArch64: the sign of `x`

`zeroSign`: `x` fully reduced into `X2`; `x20 |= c`, `c = 0` exactly when
`x ≠ 0` or the sign bit (`x17`) is 0. `negSwap`: `x` swapped with `-x` (slot 12)
by the mask of `x`'s low bit (from `X2`) differing from the sign bit.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv cswapE opSwap)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Impl.X448.AArch64 (ld st slot X2)

theorem orStep_ok {s : State} {base : Addr} (hs : Scr s base) {n : Nat} (hn : n < 16) :
    WP isa (.block ([ld .x4 (X2 + 8 * n), .logic .orr .x .x5 .x5 .x4] : List Instr)) s fun t =>
      t.gpr .x5 = s.gpr .x5 ||| word s.mem base (X2 + 8 * n) ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  have r1 := hs.read (d := X2 + 8 * n) (n := 8) (by simp only [X2, slot]; omega)
  have e1 : (X2 + 8 * n) % 8 = 0 ∧ X2 + 8 * n < 4096 * 8 := by simp only [X2, slot]; omega
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    State.load, State.read, e1, and_self, BitVec.setWidth_eq, hs.x3, r1,
    RegUpd.gpr_write, RegUpd.mem_write, Nat.reduceMul,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

/-- `x5` = the OR of `X2`'s sixteen words. -/
theorem orWords_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block (([.movz .x .x5 0 0] : List Instr) ++
        (List.range 16).flatMap (fun i => [ld .x4 (X2 + 8 * i), .logic .orr .x .x5 .x5 .x4]))) s fun t =>
      (t.gpr .x5 = 0 ↔ ∀ j < 16, VG.Proof.X448.AArch64.word s.mem base (X2 + 8 * j) = 0) ∧ t.mem = s.mem ∧ Keeps [.x4, .x5] s t := by
  rw [WP.block_append_iff]
  refine WP.mono (show WP isa (.block [.movz .x .x5 0 0]) s fun t =>
      t.gpr .x5 = 0 ∧ t.mem = s.mem ∧ Keeps [.x5] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
      RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
    refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]) fun t0 ⟨z0, m0, k0⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x5 = 0 ↔ ∀ j < n, VG.Proof.X448.AArch64.word s.mem base (X2 + 8 * j) = 0) ∧ u.mem = s.mem ∧ Keeps [.x4, .x5] t0 u
  have step : ∀ n u, n < 16 → inv n u →
      WP isa (.block ([ld .x4 (X2 + 8 * n), .logic .orr .x .x5 .x5 .x4] : List Instr)) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have hsu : Scr u base := (hs.of_keeps k0 (by decide)).of_keeps uk (by decide)
    refine WP.mono (VG.Proof.Ed448.AArch64.orStep_ok hsu hn) fun v ⟨v5, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
    rw [v5, VG.Proof.Ed448.AArch64.or_eq_zero64, uv, um]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h1 j hj
      · exact h2
    · intro h; exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
  refine WP.mono (wp_range_flatMap (M := isa) (N := 16) inv step 16 (by decide) t0
    ⟨⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ => z0⟩, m0, VG.Proof.X448.AArch64.Keeps.refl _ _⟩)
    fun u ⟨uv, um, uk⟩ => ⟨uv, um, (k0.mono (by decide)).trans uk⟩

theorem and17_ok (s : State) :
    WP isa (.block [.logic .and .x .x5 .x5 .x17]) s fun t =>
      t.gpr .x5 = s.gpr .x5 &&& s.gpr .x17 ∧ t.mem = s.mem ∧ Keeps [.x5] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, RegUpd.gpr_write_self, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem valN_zero_iff {f : Nat → Nat} : VG.Proof.X448.valN f 16 = 0 ↔ ∀ j < 16, f j = 0 := by
  constructor
  · intro h j hj
    by_contra hne
    have : 0 < VG.Proof.X448.valN f 16 := by
      rw [show (16 : Nat) = (j + 1) + (15 - j) by omega, VG.Proof.X448.valN_split, VG.Proof.X448.valN]
      have : 0 < VG.Proof.X448.radix ^ j * f j :=
        Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pos_of_ne_zero hne)
      omega
    omega
  · intro h
    rw [VG.Proof.X448.valN_congr (g := fun _ => 0) h]
    clear h
    generalize 16 = n
    induction n with
    | zero => rfl
    | succ n ih => rw [VG.Proof.X448.valN, ih]; rfl

theorem zeroSign_val (z : Bool) {sb : Nat} (hsb : sb < 2) :
    ((if z then (1 : BitVec 64) else 0) &&& BitVec.ofNat 64 sb = 0) ↔ ¬ (z = true ∧ sb = 1) := by
  rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;> cases z <;> decide

/-- `zeroSign xo`: `x20 |= c`, `c = 0` exactly when slot `xo` is not zero or the sign bit `x17`
is 0; and the low bit of `X2`'s first limb is `x`'s. -/
theorem zeroSign_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base) (xo : Fin 22)
    (hxo : xo ≠ 1) {sb : Nat} (hsb : sb < 2) (h17 : s.gpr .x17 = BitVec.ofNat 64 sb) :
    WP isa (.block (zeroSign xo.val)) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ ¬ (VG.Proof.X448.AArch64.Weak.E s.mem base xo = 0 ∧ sb = 1)) ∧ t.gpr .x20 = s.gpr .x20 ||| c) ∧
      VG.Proof.X448.AArch64.limbs t.mem base X2 0 % 2 = (VG.Proof.X448.AArch64.Weak.E s.mem base xo).val % 2 ∧
      VG.Proof.Ed448.AArch64.CKeep base s t ∧ BoundedEnv t.mem base := by
  rw [zeroSign]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.canon_ok hs hb xo hxo) fun u ⟨bu, fu, mu, ku⟩ => ?_
  have hsu := hs.of_keeps ku (by decide)
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.orWords_ok hsu) fun v ⟨v5, vm, vk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.isZero_ok v) fun w ⟨w5, wm, wk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.and17_ok w) fun x ⟨x5, xm, xk⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.AArch64.orBad_ok x) fun t ⟨t20, tm, tk⟩ => ?_
  have tmem : t.mem = u.mem := by rw [tm, xm, wm, vm]
  have x17 : w.gpr .x17 = BitVec.ofNat 64 sb := by
    rw [wk.1 _ (by decide), vk.1 _ (by decide), ku.1 _ (by decide)]; exact h17
  have hz : v.gpr .x5 = 0 ↔ VG.Proof.X448.AArch64.Weak.E s.mem base xo = 0 := by
    rw [v5]
    constructor
    · intro h
      apply Fin.ext
      rw [← fu, Fin.val_zero]
      exact valN_zero_iff.mpr fun j hj => by
        have := congrArg BitVec.toNat (h j hj)
        exact this
    · intro h j hj
      have h0 : VG.Proof.X448.AArch64.fe u.mem base X2 = 0 := by rw [fu, h, Fin.val_zero]
      apply BitVec.eq_of_toNat_eq
      exact valN_zero_iff.mp h0 j hj
  refine ⟨⟨x.gpr .x5, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [x5, w5, x17]
    have := VG.Proof.Ed448.AArch64.zeroSign_val (decide (v.gpr .x5 = 0)) hsb
    simp only [decide_eq_true_eq] at this
    rw [this, hz]
  · rw [t20, xk.1 _ (by decide), wk.1 _ (by decide), vk.1 _ (by decide), ku.1 _ (by decide)]
  · rw [tmem, ← fu]
    exact (valN_mod_two _).symm
  · refine CKeep.of_keeps (rs := [.x4, .x5, .x6, .x7, .x20] ++ workRegs)
      ((ku.mono (by decide)).trans ((((vk.mono (by decide)).trans (wk.mono (by decide))).trans
        (xk.mono (by decide))).trans (tk.mono (by decide)))) (by decide) ?_
    rw [tmem]; exact CFrame.of_field mu
  · rw [tmem]
    exact VG.Proof.Ed448.AArch64.bounded_check hb (CFrame.of_field mu) bu

/-! ## `-x` swapped in -/

theorem negMask_val (w : BitVec 64) {sb : Nat} (hsb : sb < 2) :
    (0 : BitVec 64) - ((w &&& 1) ^^^ BitVec.ofNat 64 sb) = VG.Proof.Curve448.AArch64.mask (decide (w.toNat % 2 ^^^ sb = 1)) := by
  have hw : w &&& 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [hw]
  have h2 : w.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize w.toNat % 2 = a at h2 ⊢
  rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;> decide

theorem negMask_ok {s : State} {base : Addr} (hs : Scr s base) {sb : Nat} (hsb : sb < 2)
    (h17 : s.gpr .x17 = BitVec.ofNat 64 sb) :
    WP isa (.block negMask) s fun t =>
      t.gpr .x17 = VG.Proof.Curve448.AArch64.mask (decide (VG.Proof.X448.AArch64.limbs s.mem base X2 0 % 2 ^^^ sb = 1)) ∧
      t.mem = s.mem ∧ Keeps [.x4, .x6, .x17] s t := by
  have r1 := hs.read (d := X2) (n := 8) (by decide)
  have e1 : X2 % 8 = 0 ∧ X2 < 4096 * 8 := by decide
  have e0 : BitVec.setWidth 64 (0 : BitVec 16) = 0 := rfl
  have e1' : BitVec.setWidth 64 (1 : BitVec 16) = 1 := rfl
  apply WP.of_runBlock
  simp only [negMask, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, Size.bits,
    State.load, State.read, e1, and_self, BitVec.setWidth_eq, hs.x3, r1, Nat.reduceLT,
    RegUpd.gpr_write, RegUpd.mem_write, Nat.reduceMul, BitVec.shiftLeft_zero,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, e0, e1', h17,
    VG.Proof.X448.AArch64.read8_eq, Option.some.injEq, exists_eq_left']
  refine ⟨VG.Proof.Ed448.AArch64.negMask_val _ hsb, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]

theorem mov6_ok (s : State) :
    WP isa (.block [.addImm .x .x6 .x17 0]) s fun t => t.gpr .x6 = s.gpr .x17 ∧ t.mem = s.mem ∧ Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Nat.reduceLT, BitVec.setWidth_eq, BitVec.add_zero, RegUpd.gpr_write,
    ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyDecode`. -/
section

/-!
# Ed448 verification's equation on AArch64: decoding a point

`decode rp xo yo`: the 57 bytes at `rp` decoded into slots `xo` and `yo`
(`decode_ok`): `x20 |= c`, `c = 0` exactly when they decode, given that
`recoverX` is `recoverRef` (`RecoverOk`), and then the slots hold the point.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off word limbs Outside Outside2 ofs workRegs FieldMem)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv cswapE opSwap IKeep)
open VG.Proof.Curve448.AArch64 (mask)
open VG.Impl.X448.AArch64 (ld st slot X2 ACC)

/-- What decoding writes: the slots, the coefficients and `CAN`. -/
def DFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < 64 ∨ 2880 ≤ ofs base x) → (ofs base x < ACC ∨ ACC + 512 ≤ ofs base x) →
    (ofs base x < CAN ∨ CAN + 128 ≤ ofs base x) → m' x = m x

theorem DFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : DFrame base m₁ m₂) (h₂ : DFrame base m₂ m₃) :
    DFrame base m₁ m₃ := fun x a b c => (h₂ x a b c).trans (h₁ x a b c)

theorem DFrame.of_outside2 {base : Addr} {m m' : Mem} {n : Nat} (hn : n ≤ 2816)
    (h : Outside2 base 64 n ACC 512 m m') : DFrame base m m' := fun x a b _ => h x (by omega) b

theorem DFrame.whole {base : Addr} {m m' : Mem} (h : DFrame base m m') : Outside base 0 8192 m m' :=
  fun x hx => h x (by omega) (by simp only [ACC]; omega) (by simp only [CAN]; omega)

theorem DFrame.word {base : Addr} {m m' : Mem} (h : DFrame base m m') {d : Nat}
    (h1 : d + 8 ≤ 64 ∨ 2880 ≤ d) (h2 : d + 8 ≤ ACC ∨ ACC + 512 ≤ d) (h3 : d + 8 ≤ CAN ∨ CAN + 128 ≤ d)
    (hd : d + 8 ≤ 8192) : word m' base d = word m base d :=
  Mem.readW_congr fun i hi => h _ (by
      simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)
    (by simp only [ofs]; rw [Offset.add_add, Mem.sub_ofNat_toNat base (by omega)]; omega)

theorem cframe_dframe {base : Addr} {m m' : Mem} (h : CFrame base m m') : DFrame base m m' :=
  fun x h1 h2 h3 => h x (by simp only [X2, slot] at *; omega) h3 h2

theorem keep_dframe {base : Addr} {s t : State} (h : Keep base s t) : DFrame base s.mem t.mem :=
  DFrame.of_outside2 (Nat.le_refl _) (h.mem.mono (Nat.le_refl _) (Nat.le_refl _))

theorem ikeep_dframe {base : Addr} {s t : State} (h : IKeep base s t) : DFrame base s.mem t.mem :=
  DFrame.of_outside2 (Nat.le_refl _) (h.mem.mono (Nat.le_refl _) (Nat.le_refl _))

theorem bytesAt57_take (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).take 56 = Spec.Ed448.bytesAt m p 56 := by
  simp only [Spec.Ed448.bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]
  rw [List.take_left' (by simp)]

theorem bytesAt57_getD (m : Mem) (p : Addr) :
    (Spec.Ed448.bytesAt m p 57).getD 56 0 = m (p + BitVec.ofNat 64 56) := by
  simp [Spec.Ed448.bytesAt, List.getD_eq_getElem?_getD]

theorem bytesAt57_len (m : Mem) (p : Addr) : (Spec.Ed448.bytesAt m p 57).length = 57 := by
  simp [Spec.Ed448.bytesAt]

theorem fopValid_decode (xo yo : Fin 22) (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9)) :
    (∀ op ∈ decodeUV yo.val xo.val, fopValid op) ∧
      (∀ op ∈ ([.mul xo.val xo.val 21, .sqr 12 xo.val, .mul 12 3 12] : List FOp), fopValid op) ∧
      (∀ op ∈ ([.sub 12 xo.val xo.val, .sub 12 12 xo.val] : List FOp), fopValid op) := by
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem decode_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {rp : Reg} {p : Addr} (hp : s.gpr rp = p) (hrp : rp = .x0 ∨ rp = .x1) (xo yo : Fin 22)
    (hxy : (xo = 6 ∧ yo = 7) ∨ (xo = 8 ∧ yo = 9))
    (h10 : E s.mem base 10 = 1) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa (decode rp xo.val yo.val) s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ pt, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some pt →
        E t.mem base xo = pt.X ∧ E t.mem base yo = pt.Y ∧ pt.Z = 1) ∧
      (∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ xo → i ≠ yo →
        E t.mem base i = E s.mem base i) ∧
      BoundedEnv t.mem base ∧ Keeps (.x17 :: .x19 :: .x20 :: workRegs) s t ∧ DFrame base s.mem t.mem := by
  obtain ⟨v1, v2, v3⟩ := fopValid_decode xo yo hxy
  have hxo1 : xo ≠ 1 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hxo12 : xo ≠ 12 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hyx : yo ≠ xo := by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hxlt : xo.val < 14 := by rcases hxy with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have hylt : yo.val < 14 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
  have hxo : xo = 6 ∨ xo = 8 := by rcases hxy with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  rw [decode]
  -- `y`, its checks and the sign bit.
  refine WP.seq (WP.mono (decodeY_ok hs hb hp hrp yo hr hfar)
    fun s1 ⟨y1, sg1, ⟨c1, hc1, b1⟩, e1, bd1, k1, o1⟩ => ?_)
  have hs1 : Scr s1 base := hs.of_keeps k1 (by decide)
  -- `u`, `v`, `u³v` and `u⁵v³`.
  refine WP.seq (WP.mono (field_ok _ v1 hs1 bd1) fun s2 ⟨k2, bd2, e2⟩ => ?_)
  have hs2 := k2.scr hs1
  -- The root.
  refine WP.seq (WP.mono (root_spec base s2 hs2 bd2) fun s3 ⟨k3, bd3, e3⟩ => ?_)
  have hs3 := k3.scr hs2
  -- `x` and `v x²`.
  refine WP.seq (WP.mono (field_ok _ v2 hs3 bd3) fun s4 ⟨k4, bd4, e4⟩ => ?_)
  have hs4 := k4.scr hs3
  -- The checks, and the mask of the sign.
  simp only [List.append_assoc]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (eqSlots_ok hs4 bd4 12 13 (by decide) (by decide)) fun s5 ⟨⟨c2, hc2, b5⟩, k5, bd5⟩ => ?_
  have hs5 := k5.scr hs4
  have sb17 : s5.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [k5.regs.1 _ (by decide), k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide)]
    exact sg1
  have hsb : (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 < 2 := by
    have := (s.mem (p + BitVec.ofNat 64 56)).isLt; omega
  rw [WP.block_append_iff]
  refine WP.mono (zeroSign_ok hs5 bd5 xo hxo1 hsb sb17) fun s6 ⟨⟨c3, hc3, b6⟩, lo6, k6, bd6⟩ => ?_
  have hs6 := k6.scr hs5
  have sb17' : s6.gpr .x17 = BitVec.ofNat 64 ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128) := by
    rw [k6.regs.1 _ (by decide)]; exact sb17
  refine WP.mono (negMask_ok hs6 hsb sb17') fun s7 ⟨m7, mm7, k7⟩ => ?_
  have hs7 : Scr s7 base := hs6.of_keeps k7 (by decide)
  have bd7 : BoundedEnv s7.mem base := mm7 ▸ bd6
  -- `-x`.
  refine WP.seq (WP.mono (field_ok _ v3 hs7 bd7) fun s8 ⟨k8, bd8, e8⟩ => ?_)
  have hs8 := k8.scr hs7
  have m8 : s8.gpr .x17 = s7.gpr .x17 := k8.regs.1 _ (by decide)
  -- The swap.
  rw [negSwap, WP.block_append_iff]
  refine WP.mono (mov6_ok s8) fun s9 ⟨x6, mm9, k9⟩ => ?_
  have hs9 : Scr s9 base := hs8.of_keeps k9 (by decide)
  have bd9 : BoundedEnv s9.mem base := mm9 ▸ bd8
  refine WP.mono (cswapE hs9 bd9 xo 12 hxo12 (sw := decide (VG.Proof.X448.AArch64.limbs s6.mem base X2 0 % 2 ^^^
    (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)) (by rw [x6, m8, m7]; rfl)) fun t ⟨kt, bdt, _, et⟩ => ?_
  -- The values.
  have e1' : ∀ i : Fin 22, i ≠ yo → E s1.mem base i = E s.mem base i := e1
  have h10' : E s1.mem base 10 = 1 := by
    rw [e1' 10 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h10]
  have h11' : E s1.mem base 11 = Spec.Ed448.d := by
    rw [e1' 11 (by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide), h11]
  obtain ⟨u2, vv2, t2, w2, k2'⟩ := decodeUV_eval xo yo hxy (E s1.mem base)
  simp only [h10', h11', y1] at u2 vv2 t2 w2
  simp only [← e2] at u2 vv2 t2 w2 k2'
  generalize hY : VG.Proof.X448.toFe (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) = Y at *
  have r21 : E s3.mem base 21 = rootPow (E s2.mem base 12) := by rw [e3, rootEnv_eval]
  have r3k : ∀ i : Fin 22, i.val < 14 → E s3.mem base i = E s2.mem base i := fun i hi => by
    rw [e3, rootEnv_keep _ _ hi]
  obtain ⟨x4, x12, x13, k4'⟩ := decodeXOps_eval xo hxo (E s3.mem base)
  rw [← e4] at x4 x12 x13 k4'
  rw [r3k xo hxlt, t2, r21, w2] at x4 x12
  rw [r3k 3 (by decide), vv2] at x12
  rw [x13, r3k 13 (by decide), u2] at hc2
  rw [x12] at hc2
  generalize hu : Y * Y - 1 = u at *
  generalize hv : Spec.Ed448.d * (Y * Y) - 1 = v at *
  generalize ht : u * u * u * v = tt at *
  generalize hx : tt * rootPow (tt * ((u * v) * (u * v))) = x at *
  -- `x` at `s5` and `s6`.
  have x5 : E s5.mem base xo = x := by rw [k5.mem.E hxo1, x4]
  rw [x5] at hc3 lo6
  have hD := Proof.Ed448.decodePoint_impl hR (Spec.Ed448.bytesAt s.mem p 57) (bytesAt57_len _ _)
    (Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56)) ((s.mem (p + BitVec.ofNat 64 56)).toNat)
    (by rw [bytesAt57_take]) (by rw [bytesAt57_getD]) Y u v tt x hY hu hv ht hx
  have s7x : E s7.mem base = E s6.mem base := by rw [mm7]
  have s9x : E s9.mem base = E s8.mem base := by rw [mm9]
  obtain ⟨n12, n8⟩ := subNeg_eval xo hxo12 (E s7.mem base)
  rw [← e8] at n12 n8
  have x7 : E s7.mem base xo = x := by rw [s7x, k6.mem.E hxo1, x5]
  -- The final `x`.
  have xt : E t.mem base xo =
      if (x.val % 2 == 1) == ((s.mem (p + BitVec.ofNat 64 56)).toNat / 128 == 1) then x else (x - x) - x := by
    rw [et, opSwap, Function.update_of_ne hxo12, Function.update_self, s9x, n12, n8 xo hxo12, x7]
    have hlo : VG.Proof.X448.AArch64.limbs s6.mem base X2 0 % 2 = x.val % 2 := lo6
    rw [hlo]
    have hx2 : x.val % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize x.val % 2 = a at hx2 ⊢
    generalize (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = sb at hsb ⊢
    rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl <;> rcases (by omega : sb = 0 ∨ sb = 1) with rfl | rfl <;>
      rfl
  -- What the rest keeps.
  have keepE : ∀ i : Fin 22, i ≠ 1 → i ≠ xo → i ≠ 12 → E t.mem base i = E s4.mem base i := by
    intro i h1 hx h12
    rw [et, opSwap, Function.update_of_ne h12, Function.update_of_ne hx, s9x, n8 i h12, s7x, k6.mem.E h1,
      k5.mem.E h1]
  have kY : E t.mem base yo = Y := by
    have hy1 : yo ≠ 1 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    have hy12 : yo ≠ 12 := by rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide
    rw [keepE yo hy1 hyx hy12, k4' yo hyx hy12, r3k yo hylt,
      k2' yo (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
        (by rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) hyx, y1]
  refine ⟨⟨c1 ||| c2 ||| c3, ?_, ?_⟩, fun pt hpt => ?_, fun i hi h1 h3 h4 h5 hix hiy => ?_, bdt, ?_, ?_⟩
  · rw [or_eq_zero64, or_eq_zero64, hc1, hc2, hc3, hD]
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall]
      exact ⟨fun _ => rfl, fun _ => ⟨⟨hall.1, hall.2.1⟩, hall.2.2⟩⟩
    · rw [ite_eq_right hall]
      exact ⟨fun h => absurd ⟨h.1.1, h.1.2, h.2⟩ hall, fun h => absurd h (by simp)⟩
  · rw [kt.regs.1 _ (by decide), k9.1 _ (by decide), k8.regs.1 _ (by decide), k7.1 _ (by decide), b6, b5,
      k4.regs.1 _ (by decide), k3.regs.1 _ (by decide), k2.regs.1 _ (by decide), b1]
    simp only [BitVec.or_assoc]
  · rw [hD] at hpt
    by_cases hall : ((s.mem (p + BitVec.ofNat 64 56)).toNat % 128 = 0 ∧
        Spec.Ed448.decodeLE (Spec.Ed448.bytesAt s.mem p 56) < Spec.X448.P) ∧ v * (x * x) = u ∧
        ¬ (x = 0 ∧ (s.mem (p + BitVec.ofNat 64 56)).toNat / 128 = 1)
    · rw [ite_eq_left hall] at hpt
      cases hpt
      exact ⟨xt, kY, rfl⟩
    · rw [ite_eq_right hall] at hpt
      cases hpt
  · have hi14 : i.val < 14 := by omega
    have h12 : i ≠ 12 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    have h13 : i ≠ 13 := fun h => by rw [h] at hi; exact absurd hi (by decide)
    rw [keepE i h1 hix h12, k4' i hix h12, r3k i hi14, k2' i h3 h4 h5 h12 h13 hix, e1' i hiy]
  · refine ((((((((k1.mono (by decide)).trans (k2.regs.mono (by decide))).trans (k3.regs.mono (by decide))).trans
      (k4.regs.mono (by decide))).trans (k5.regs.mono (by decide))).trans (k6.regs.mono (by decide))).trans
      (k7.mono (by decide))).trans (k8.regs.mono (by decide))).trans ((k9.mono (by decide)).trans
      (kt.regs.mono (by decide)))
  · have d1 : DFrame base s.mem s1.mem := fun x h1 _ _ =>
      o1 x (by have := yo.isLt; simp only [slot] at *; omega)
    have d7 : DFrame base s6.mem s7.mem := by rw [mm7]; exact fun _ _ _ _ => rfl
    have d9 : DFrame base s8.mem s9.mem := by rw [mm9]; exact fun _ _ _ _ => rfl
    exact ((((((((d1.trans (keep_dframe k2)).trans (ikeep_dframe k3)).trans (keep_dframe k4)).trans
      (cframe_dframe k5.mem)).trans (cframe_dframe k6.mem)).trans d7).trans (keep_dframe k8)).trans d9).trans
      (keep_dframe kt)

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyEntry`. -/
section

/-!
# Ed448 verification's equation on AArch64: the entry and the constants

`ventry`: `x12 = 2^28 - 1`, `x19` and `x20` saved in the working space's
first 16 bytes, `x20 = 0` (no check has failed), every slot zeroed, then `B`
in slots 8–10 and `d` in slot 11, each from immediates (`constSlot`). A
constant slot keeps every slot's limbs bounded (`constE_ok`), so `qInit`
sets `Q` to the neutral point after decoding `A`.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word limbs Outside Saved store_ok
  word_write_aligned writeW_outside fill_ok)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv E_outside slot_sep)
open VG.Proof.X448.AArch64.Base (constSlot_ok F_of_words limb_lt)
open VG.Impl.X448.AArch64 (ld st slot)
open VG.Impl.X448.AArch64.Base (constSlot limb)

theorem limb_zero (w : Nat) : limb 0 w = 0 := by
  rw [limb, Fin.val_zero, Nat.zero_shiftRight, Nat.zero_mod]; rfl

/-- `x12 := 2²⁸ - 1`. -/
theorem mask12_ok (s : State) :
    WP isa (.block ([.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] : List Instr)) s
      fun t => t.gpr .x12 = 0x0fffffff ∧ Keeps [.x12] s t ∧ t.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨by decide, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

theorem zero20_ok (s : State) :
    WP isa (.block [.movz .x .x20 0 0]) s fun t =>
      t.gpr .x20 = 0 ∧ t.mem = s.mem ∧ Keeps [.x20] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

/-- The mask, the saves of `x19` and `x20`, `x20 = 0` and `x4 = 0`. -/
theorem vhead_ok {s : State} {base : Addr} (hb : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ([.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1, st .x19 0, st .x20 8,
        .movz .x .x20 0 0, .movz .x .x4 0 0] : List Instr)) s fun t =>
      Scr t base ∧ t.gpr .x20 = 0 ∧ t.gpr .x4 = 0 ∧ VG.Proof.X448.AArch64.Saved base s.gpr t.mem ∧
      Outside base 0 16 s.mem t.mem ∧ Keeps [.x12, .x20, .x4] s t := by
  rw [show ([.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1, st .x19 0, st .x20 8,
      .movz .x .x20 0 0, .movz .x .x4 0 0] : List Instr) =
      [.movz .x .x12 0xffff 0, .movk .x .x12 0x0fff 1] ++
        ([st .x19 0] ++ ([st .x20 8] ++ ([.movz .x .x20 0 0] ++ [.movz .x .x4 0 0]))) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.mask12_ok s) fun a ⟨a12, ka, ma⟩ => ?_
  have ha : Scr a base := ⟨(ka.1 _ (by decide)).trans hb, a12, by rw [ka.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store_ok ha (d := 0) (by decide) (by decide) .x19) fun b ⟨mb, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store_ok hsb (d := 8) (by decide) (by decide) .x20) fun c ⟨mc, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.zero20_ok c) fun d ⟨d20, md, kd⟩ => ?_
  have hsd := hsc.of_keeps kd (by decide)
  refine WP.mono (VG.Proof.X448.AArch64.zeroX4_ok d) fun t ⟨t4, mt, kt⟩ => ?_
  have k : Keeps [.x12, .x20, .x4] s t :=
    ((((ka.mono (by simp)).trans (kb.mono (by simp))).trans (kc.mono (by simp))).trans
      (kd.mono (by simp))).trans (kt.mono (by simp))
  have ob : Outside base 0 16 s.mem b.mem := by
    rw [mb, ← ma]; exact (writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
  have oc : Outside base 0 16 b.mem c.mem := by
    rw [mc]; exact (writeW_outside _ _ _ (by decide)).mono (by omega) (by omega)
  refine ⟨hsd.of_keeps kt (by decide), by rw [kt.1 _ (by decide)]; exact d20, t4, ⟨?_, ?_⟩,
    by rw [mt, md]; exact ob.trans oc, k⟩
  · rw [mt, md, mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_right (by decide), mb, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, ka.1 _ (by decide)]
  · rw [mt, md, mc, word_write_aligned _ _ (by decide) (by decide) (by decide) (by decide),
      ite_eq_left rfl, kb.1 _ (by decide), ka.1 _ (by decide)]

/-- A constant slot, among bounded ones: its value, every slot still bounded,
and the other slots unchanged. -/
theorem constE_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (o : Fin 22) (v : Spec.X448.Fe) :
    WP isa (.block (constSlot (slot o.val) v)) s fun t =>
      BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base o = v ∧ (∀ i : Fin 22, i ≠ o → VG.Proof.X448.AArch64.Weak.E t.mem base i = VG.Proof.X448.AArch64.Weak.E s.mem base i) ∧
      Outside base (slot o.val) 64 s.mem t.mem ∧ Keeps [.x4] s t := by
  have ho := o.isLt
  refine WP.mono (constSlot_ok hs (o := slot o.val) (by simp only [slot]; omega) (by simp only [slot]; omega) v)
    fun t ⟨tv, tm, tk⟩ => ⟨fun i j hj => ?_, F_of_words tv, fun i hi => ?_, tm, tk⟩
  · by_cases h : i = o
    · subst h
      show (VG.Proof.X448.AArch64.word t.mem base (slot i.val + 8 * j)).toNat < _
      rw [tv j hj]
      exact Nat.lt_of_lt_of_le (limb_lt v j) (by decide)
    · have hsep := slot_sep h
      rw [show VG.Proof.X448.AArch64.limbs t.mem base (slot i.val) j = VG.Proof.X448.AArch64.limbs s.mem base (slot i.val) j from
        tm.limbs (by omega) (by have := i.isLt; simp only [slot]; omega) (by omega)]
      exact hb i j hj
  · have hsep := slot_sep hi
    exact E_outside tm i (by omega)

/-- The constants, from zeroed slots: every slot bounded, slot 0 zero, `B`
and `d`. -/
theorem vconsts_ok {s : State} {base : Addr} (hs : Scr s base)
    (hz : ∀ i : Fin 22, ∀ w < 8, VG.Proof.X448.AArch64.word s.mem base (slot i.val + 8 * w) = 0) :
    WP isa (.block (constSlot (slot 8) Spec.Ed448.basePoint.X ++ (constSlot (slot 9) Spec.Ed448.basePoint.Y ++
      (constSlot (slot 10) 1 ++ constSlot (slot 11) Spec.Ed448.d)))) s fun t =>
      BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Weak.E t.mem base 0 = 0 ∧ pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base 11 = Spec.Ed448.d ∧ Outside base 64 2816 s.mem t.mem ∧ Keeps [.x4] s t := by
  have b0 : BoundedEnv s.mem base := fun i w hw => by
    show (VG.Proof.X448.AArch64.word s.mem base (slot i.val + 8 * w)).toNat < _
    rw [hz i w hw]; decide
  have e0 : VG.Proof.X448.AArch64.Weak.E s.mem base 0 = 0 := F_of_words fun w hw => by rw [limb_zero]; exact hz 0 w hw
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.constE_ok hs b0 8 _) fun t1 ⟨b1, v1, o1, m1, k1⟩ => ?_
  have h1 := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.constE_ok h1 b1 9 _) fun t2 ⟨b2, v2, o2, m2, k2⟩ => ?_
  have h2 := h1.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.constE_ok h2 b2 10 1) fun t3 ⟨b3, v3, o3, m3, k3⟩ => ?_
  have h3 := h2.of_keeps k3 (by decide)
  refine WP.mono (VG.Proof.Ed448.AArch64.constE_ok h3 b3 11 _) fun t ⟨b4, v4, o4, m4, k4⟩ => ?_
  refine ⟨b4, ?_, ?_, v4, ?_, ((k1.trans k2).trans k3).trans k4⟩
  · rw [o4 0 (by decide), o3 0 (by decide), o2 0 (by decide), o1 0 (by decide), e0]
  · simp only [pt]
    rw [o4 8 (by decide), o3 8 (by decide), o2 8 (by decide), v1, o4 9 (by decide), o3 9 (by decide), v2,
      o4 10 (by decide), v3]
    rfl
  · simp only [slot] at m1 m2 m3 m4
    exact (((m1.mono (by omega) (by omega)).trans (m2.mono (by omega) (by omega))).trans
      (m3.mono (by omega) (by omega))).trans (m4.mono (by omega) (by omega))

/-- The entry: the registers, the saves, the zeroed slots and the constants. -/
theorem ventry_ok {s : State} {base : Addr} (hb : s.gpr .x3 = base) (hw : (⟨base, 8192⟩ : Region) ∈ s.wr)
    (hn : base.toNat + 8192 ≤ 2 ^ 64) :
    WP isa (.block ventry) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ VG.Proof.X448.AArch64.Saved base s.gpr t.mem ∧ t.gpr .x20 = 0 ∧
      Keeps [.x12, .x20, .x4] s t ∧ Outside base 0 8192 s.mem t.mem ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base 0 = 0 ∧ pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      VG.Proof.X448.AArch64.Weak.E t.mem base 11 = Spec.Ed448.d := by
  rw [ventry]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.vhead_ok hb hw hn) fun a ⟨ha, a20, a4, sa, oa, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fill_ok ha (o := slot 0) (n := 352) (by decide) (by decide) a4) fun b ⟨zb, ob, kb⟩ => ?_
  have hsb := ha.of_keeps kb (by decide)
  have zs : ∀ i : Fin 22, ∀ w < 8, VG.Proof.X448.AArch64.word b.mem base (slot i.val + 8 * w) = 0 := fun i w hw => by
    have := i.isLt
    have hz := zb (16 * i.val + w) (by omega)
    have e : slot 0 + 8 * (16 * i.val + w) = slot i.val + 8 * w := by simp only [slot]; omega
    rw [show VG.Proof.X448.AArch64.limbs b.mem base (slot 0) (16 * i.val + w) = (VG.Proof.X448.AArch64.word b.mem base (slot i.val + 8 * w)).toNat by
      simp only [VG.Proof.X448.AArch64.limbs]; rw [e]] at hz
    exact BitVec.eq_of_toNat_eq hz
  refine WP.mono (VG.Proof.Ed448.AArch64.vconsts_ok hsb zs) fun t ⟨bt, e0, pB, dt, ot, kt⟩ => ?_
  refine ⟨hsb.of_keeps kt (by decide), bt, (sa.outside ob (by decide)).outside ot (by decide),
    by rw [kt.1 _ (by decide), kb.1 _ (by decide)]; exact a20,
    (ka.trans (kb.mono (by simp))).trans (kt.mono (by simp)), ?_, e0, pB, dt⟩
  exact ((oa.mono (by omega) (by omega)).trans (ob.mono (by simp only [slot]; omega)
    (by simp only [slot]; omega))).trans (ot.mono (by omega) (by omega))

/-- `Q` the neutral point: slots 1 and 2 set to 1 (slot 0 is zero). -/
theorem qInit_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (h0 : VG.Proof.X448.AArch64.Weak.E s.mem base 0 = 0) :
    WP isa (.block qInit) s fun t =>
      BoundedEnv t.mem base ∧ pt (VG.Proof.X448.AArch64.Weak.E t.mem base) 0 1 2 = Spec.Ed448.identity ∧
      (∀ i : Fin 22, i ≠ 1 → i ≠ 2 → VG.Proof.X448.AArch64.Weak.E t.mem base i = VG.Proof.X448.AArch64.Weak.E s.mem base i) ∧
      Outside base 192 192 s.mem t.mem ∧ Keeps [.x4] s t := by
  rw [qInit, WP.block_append_iff]
  refine WP.mono (VG.Proof.Ed448.AArch64.constE_ok hs hb 1 1) fun t1 ⟨b1, v1, o1, m1, k1⟩ => ?_
  refine WP.mono (VG.Proof.Ed448.AArch64.constE_ok (hs.of_keeps k1 (by decide)) b1 2 1) fun t ⟨b2, v2, o2, m2, k2⟩ => ?_
  refine ⟨b2, ?_, fun i h1 h2 => by rw [o2 i h2, o1 i h1], ?_, k1.trans k2⟩
  · simp only [pt, Spec.Ed448.identity]
    rw [o2 0 (by decide), o1 0 (by decide), h0, o2 1 (by decide), v1, v2]
  · have m1' : Outside base 192 64 s.mem t1.mem := m1
    have m2' : Outside base 320 64 t1.mem t.mem := m2
    exact (m1'.mono (by decide) (by decide)).trans (m2'.mono (by decide) (by decide))

end VG.Proof.Ed448.AArch64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Ed448.AArch64.VerifyStages`. -/
section

/-!
# Ed448 verification's equation on AArch64: decoding `A`

`vdecodeA_ok`: `A` decoded and negated into slots 6, 7 and 10, and `Q` the
neutral point. The check ORs into `x20` a word that is 0 exactly when it
passes.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keep Keeps off Outside Outside2 ofs workRegs)
open VG.Proof.X448.AArch64.Weak (E BoundedEnv)
open VG.Impl.X448.AArch64 (slot BITS ACC)

/-- Bytes far from the working space, after writes only to it. -/
theorem far_bytes {base p : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hf : ∀ i < n, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.Ed448.bytesAt m' p n = Spec.Ed448.bytesAt m p n := by
  simp only [Spec.Ed448.bytesAt]
  exact List.map_congr_left fun i hi => h _ (Or.inr (hf i (List.mem_range.mp hi)))

theorem pt_congr {e e' : Fin 22 → Spec.X448.Fe} {a b c : Fin 22} (ha : e' a = e a) (hb : e' b = e b)
    (hc : e' c = e c) : pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

theorem sub6_keep (e : Fin 22 → Spec.X448.Fe) (i : Fin 22) (hi : i ≠ 6) :
    evalOps [.sub 6 0 6] e i = e i :=
  Function.update_of_ne hi _ _

/-- `A` decoded and negated into slots 6, 7 and 10, and `Q` the neutral point. -/
theorem vdecodeA_ok (hR : RecoverOk) {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {p : Addr} (hp : s.gpr .x0 = p) (h0 : E s.mem base 0 = 0)
    (hB : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint) (h11 : E s.mem base 11 = Spec.Ed448.d)
    (hr : ∀ j < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 j) 1)
    (hfar : ∀ j < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 j)) :
    WP isa vdecodeA s fun t =>
      (∃ c : BitVec 64, (c = 0 ↔ (Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57)).isSome) ∧
        t.gpr .x20 = s.gpr .x20 ||| c) ∧
      (∀ a, Spec.Ed448.decodePoint (Spec.Ed448.bytesAt s.mem p 57) = some a →
        pt (E t.mem base) 6 7 10 = negPoint a) ∧
      pt (E t.mem base) 0 1 2 = Spec.Ed448.identity ∧ pt (E t.mem base) 8 9 10 = Spec.Ed448.basePoint ∧
      E t.mem base 11 = Spec.Ed448.d ∧ Scr t base ∧ BoundedEnv t.mem base ∧
      Keeps (.x17 :: .x19 :: .x20 :: workRegs) s t ∧ DFrame base s.mem t.mem := by
  have h10 : E s.mem base 10 = 1 := congrArg Spec.Ed448.Point.Z hB
  rw [vdecodeA, WP.seq_iff]
  refine WP.mono (decode_ok hR hs hb hp (Or.inl rfl) 6 7 (Or.inl ⟨rfl, rfl⟩) h10 h11 hr hfar)
    fun s1 ⟨hc, v1, k1, b1, g1, f1⟩ => ?_
  have hs1 : Scr s1 base := hs.of_keeps g1 (by decide)
  rw [WP.seq_iff]
  refine WP.mono (field_ok [.sub 6 0 6] (by decide) hs1 b1) fun s2 ⟨k2, b2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  have e2k : ∀ i : Fin 22, i ≠ 6 → E s2.mem base i = E s1.mem base i := fun i hi => by
    rw [e2, sub6_keep _ _ hi]
  have z2 : E s2.mem base 0 = 0 := by
    rw [e2k 0 (by decide), k1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h0]
  refine WP.mono (qInit_ok hs2 b2 z2) fun t ⟨bt, qt, ot, mt, kt⟩ => ?_
  have kk : ∀ i : Fin 22, i.val < 12 → i ≠ 1 → i ≠ 2 → i ≠ 3 → i ≠ 4 → i ≠ 5 → i ≠ 6 → i ≠ 7 →
      E t.mem base i = E s.mem base i := fun i h h1 h2 h3 h4 h5 h6 h7 => by
    rw [ot i h1 h2, e2k i h6, k1 i h h1 h3 h4 h5 h6 h7]
  refine ⟨?_, fun a ha => ?_, qt, ?_, ?_, hs2.of_keeps kt (by decide), bt, ?_, ?_⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    exact ⟨c, hc1, by rw [kt.1 _ (by decide), k2.regs.1 _ (by decide), hc2]⟩
  · obtain ⟨vx, vy, vz⟩ := v1 a ha
    show (⟨E t.mem base 6, E t.mem base 7, E t.mem base 10⟩ : Spec.Ed448.Point) = ⟨0 - a.X, a.Y, a.Z⟩
    rw [ot 6 (by decide) (by decide), ot 7 (by decide) (by decide), ot 10 (by decide) (by decide),
      e2k 7 (by decide), e2k 10 (by decide), e2, vy, vz,
      k1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h10]
    show (⟨E s1.mem base 0 - E s1.mem base 6, a.Y, 1⟩ : Spec.Ed448.Point) = _
    rw [vx, k1 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h0]
  · rw [pt_congr (kk 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (kk 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (kk 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)), hB]
  · rw [kk 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h11]
  · exact (g1.trans (k2.regs.mono fun r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ hr)))).trans (kt.mono (by decide))
  · refine (f1.trans (keep_dframe k2)).trans ?_
    exact fun x h1 h2 _ => mt x (by simp only [ACC] at *; omega)

end VG.Proof.Ed448.AArch64

end
