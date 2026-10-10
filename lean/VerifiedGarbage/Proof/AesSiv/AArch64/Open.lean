import VerifiedGarbage.Proof.AesSiv.AArch64.Seal
import VerifiedGarbage.Proof.AesSiv.Mask

/-!
# AES-SIV on AArch64: the end of `vg_aes_siv_decrypt`

From S2V's state of the associated data on, `decrypt` sets the counter from
the IV it is given (`counter_ok`), decrypts the data in place with CTR
(`ctr_wp`), finishes S2V with the plaintext into `W + 112` (`finish_wp`),
compares the two IVs without a branch (`compare_ok`), ANDs the data with the
mask of the result, a word at a time and then its last bytes one at a time
(`maskData_wp`) and restores the registers
(`openTail_wp`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.AesSiv (or_xor_eq_zero le8_append_eq eqz)
open VG.Proof.CmacAes.AArch64 (k0 succ_ofNat read_one)
open VG.Proof.CmacAes.Stream.AArch64 (toNat_ofNat eval_zero eval_nonzero mz0 bytesAt_writeBytes_self)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The OR of the XORs of the halves of the IVs at `W` and `W + 112` is 0
exactly if they are equal. -/
theorem ivs_eq (m : Mem) (W : Addr) :
    ((m.readW (W + BitVec.ofNat 64 0) 64 ^^^ m.readW (W + BitVec.ofNat 64 tOff) 64) |||
        (m.readW (W + BitVec.ofNat 64 8) 64 ^^^ m.readW (W + BitVec.ofNat 64 (tOff + 8)) 64)) = 0 ↔
      Spec.Aes.bytesAt m W 16 = Spec.Aes.bytesAt m (W + BitVec.ofNat 64 tOff) 16 := by
  rw [or_xor_eq_zero, Proof.Cmac.bytesAt_split, Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, le8_append_eq, Offset.add_add, k0]

theorem rot0 (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem sw64 (x : BitVec (8 * 8)) : BitVec.setWidth 64 x = x := BitVec.setWidth_eq x

theorem compare_ok (h : Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .x0 = (if Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
        then 1 else 0) ∧
      s'.gpr .x11 = 0 - s'.gpr .x0 ∧
      (∀ r, r ≠ .x0 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₁ := h.inRW hrd hwr (d := tOff) (n := 8) (by decide)
  have r₂ := h.inRW hrd hwr (d := 8) (n := 8) (by decide)
  have r₃ := h.inRW hrd hwr (d := tOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, Impl.AesSiv.AArch64.compare, tOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀, r₁, r₂, r₃]
    rfl, ?_, ?_, ?_, by rfl, by rfl, by rfl, by rfl⟩
  · have e := ivs_eq s.mem W
    have rd8 (a : Addr) : s.mem.read a 8 = s.mem.readW a 64 := (sw64 _).symm
    simp only [gpr_write, reduceCtorEq, ite_true, ite_false, rot0]
    rw [sw64]
    simp only [rd8]
    refine (eqz _).trans ?_
    by_cases hb : Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
    · exact (ite_eq_left (e.mpr hb)).trans (ite_eq_left hb).symm
    · exact (ite_eq_right (mt e.mp hb)).trans (ite_eq_right hb).symm
  · simp [gpr_write]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_write, h₁, h₂, h₃, h₄]

/-! ## Masking the data -/

/-- A byte ANDed with the mask `0 − r` of a result `r` of 0 or 1. -/
theorem mask_byte (b : BitVec (8 * 1)) (c : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) &&&
      ((0 : BitVec 64) - (if c then 1 else 0)))) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp [hj]

/-- The loop body of `maskData`. -/
abbrev maskBody : List Instr :=
  [.ldrb .x9 .x6 0, .logic .and .x .x9 .x9 .x11, .strb .x9 .x6 0, .addImm .x .x6 .x6 1, .subImm .x .x8 .x8 1]

theorem maskStep_ok (s : State) {A : Addr} {c : Bool} (ha : s.gpr .x6 + BitVec.ofNat 64 0 = A)
    (h11 : s.gpr .x11 = 0 - (if c then 1 else 0)) (rq : InRegions (s.rd ++ s.wr) A 1) (wq : InRegions s.wr A 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW A ((if c then s.mem A else 0 : Byte)) ∧
      s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, ha, rq, wq]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃],
    rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, h11, mask_byte, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- What `maskData` leaves: the data, or zeros. -/
structure Masked (s : State) (P : Addr) (L : Nat) (c : Bool) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P L else Spec.Siv.zeros L)
  other : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The loop body of `maskData`'s words. -/
abbrev maskWordBody : List Instr :=
  [.ldr .x .x9 .x6 0, .logic .and .x .x9 .x9 .x11, .str .x .x9 .x6 0, .addImm .x .x6 .x6 8, .subImm .x .x8 .x8 1]

theorem maskWord_ok (s : State) {A : Addr} {c : Bool} (ha : s.gpr .x6 + BitVec.ofNat 64 0 = A)
    (h11 : s.gpr .x11 = 0 - (if c then 1 else 0)) (rq : InRegions (s.rd ++ s.wr) A 8) (wq : InRegions s.wr A 8) :
    ∃ s', runBlock isa maskWordBody s = some s' ∧
      s'.mem = s.mem.writeW A (s.mem.readW A 64 &&& (0 - if c then 1 else 0)) ∧
      s'.gpr .x6 = s.gpr .x6 + 8 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskWordBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, rq, wq]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃],
    rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, Mem.readW, h11, BitVec.setWidth_eq]

theorem shr3 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 3 = BitVec.ofNat 64 (c / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem low3 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c <<< 61 >>> 61 = BitVec.ofNat 64 (c % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 2 ^ 3 * 2 ^ 61 from rfl, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by decide),
    Nat.mod_eq_of_lt (a := c % 2 ^ 3) (by omega)]

/-- The data from `P + j` on, where the bytes before are done. -/
structure MaskInv (s : State) (P : Addr) (c : Bool) (j : Nat) (t : State) : Prop where
  x6 : t.gpr .x6 = P + BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j)
  other : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem maskData_wp (s : State) {P : Addr} {L : Nat} {c : Bool} (hL : L < 2 ^ 64) (hwP : P.toNat + L ≤ 2 ^ 64)
    (h26 : s.gpr .x26 = P) (h27 : s.gpr .x27 = BitVec.ofNat 64 L) (h11 : s.gpr .x11 = 0 - (if c then 1 else 0))
    (hr : ∀ i n, i + n ≤ L → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) n)
    (hw : ∀ i n, i + n ≤ L → InRegions s.wr (P + BitVec.ofNat 64 i) n) :
    WP isa maskData s (Masked s P L c) := by
  have g27 {t : State} (ht : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) :
      t.gpr .x27 = BitVec.ofNat 64 L := by
    rw [ht _ (by decide) (by decide) (by decide), h27]
  have g11 {t : State} (ht : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) :
      t.gpr .x11 = 0 - (if c then 1 else 0) := by
    rw [ht _ (by decide) (by decide) (by decide), h11]
  -- What the data before `P + j` is written to.
  have fP {t : State} {j : Nat}
      (hm : t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j)) :
      Frame [⟨P, j⟩] s.mem t.mem := by
    rw [hm]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  rw [maskData]
  obtain ⟨s₁, run₁, x6₁, x8₁, g₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [mov .x6 .x26, .lsr .x .x8 .x27 3] s =
      some s₁ ∧ s₁.gpr .x6 = P ∧ s₁.gpr .x8 = BitVec.ofNat 64 (L / 8) ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
      rfl, ?_, ?_, fun r a b => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h26]
    · simp [gpr_write, h27, shr3 hL]
    · simp [gpr_write, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have inv₁ : MaskInv s P c 0 s₁ :=
    ⟨by rw [x6₁]; simp, by rw [m₁]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil],
      fun r a b _ => g₁ r a b, sp₁, rd₁, wr₁⟩
  -- The words.
  have words : WP isa (.ite (.zero .x .x8) (.block [])
      (.loop (.block maskWordBody) (.nonzero .x .x8))) s₁ (MaskInv s P c (8 * (L / 8))) := by
    refine WP.ite (decide (L / 8 = 0)) (eval_zero (by omega) x8₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₁
    have hn0 : L / 8 ≠ 0 := of_decide_eq_false hb
    refine WP.loop (M := isa) (c := .nonzero .x .x8)
      (fun (k : Nat) (t : State) => ∃ j, k = L / 8 - j ∧ j < L / 8 ∧ t.gpr .x8 = BitVec.ofNat 64 (L / 8 - j) ∧
        MaskInv s P c (8 * j) t) ?_ (L / 8 - 0) _ ⟨0, rfl, by omega, x8₁, inv₁⟩
    rintro k t ⟨j, rfl, hj, x8, it⟩
    obtain ⟨t', run', mem', x6', x8', g', sp', rd', wr'⟩ := maskWord_ok t (A := P + BitVec.ofNat 64 (8 * j)) (c := c)
      (by rw [it.x6, BitVec.add_zero]) (g11 it.other) (by rw [it.rd, it.wr]; exact hr _ _ (by omega))
      (by rw [it.wr]; exact hw _ _ (by omega))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    have hlen := length_mask s.mem P c (8 * j)
    have hmem : t'.mem = writeBytes s.mem P
        (if c then Spec.Aes.bytesAt s.mem P (8 * (j + 1)) else Spec.Siv.zeros (8 * (j + 1))) := by
      have hv : t.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 = s.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 :=
        (fP it.mem).readW (w := 64) (Region.contains_self _ _) (fun r hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (Offset.base_disjoint P (e := 8 * j) (n := 8) (k := 8 * j) (by omega) (by omega)).symm) (by decide)
      have hwa := writeBytes_append s.mem P (if c then Spec.Aes.bytesAt s.mem P (8 * j) else Spec.Siv.zeros (8 * j))
        (Proof.Cmac.le8 (s.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 &&& (0 - if c then 1 else 0)))
        (by rw [Proof.Cmac.length_le8, hlen]; omega)
      rw [hlen] at hwa
      rw [mem', hv, it.mem, writeW_le8, hwa, ← mask_word, show 8 * (j + 1) = 8 * j + 8 by omega]
    have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L / 8 - (j + 1)) := by
      rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
    have ev' := eval_nonzero (s := t') (x := L / 8 - (j + 1)) (by omega) x8''
    have gg : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
      rw [g' r h₁ h₂ h₃, it.other r h₁ h₂ h₃]
    have x6'' : t'.gpr .x6 = P + BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [x6', it.x6, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
        show 8 * j + 8 = 8 * (j + 1) by omega]
    by_cases he : j + 1 = L / 8
    · left
      refine ⟨by rw [ev']; simp [he], ⟨by rw [x6'', he], ?_, gg, by rw [sp', it.sp], by rw [rd', it.rd],
        by rw [wr', it.wr]⟩⟩
      rw [hmem, he]
    · right
      refine ⟨by rw [ev']; simp; omega, L / 8 - (j + 1), by omega, j + 1, rfl, by omega, x8'',
        ⟨x6'', hmem, gg, by rw [sp', it.sp], by rw [rd', it.rd], by rw [wr', it.wr]⟩⟩
  refine WP.seq (WP.mono words fun t it => ?_)
  -- The bytes.
  have hj₀ : 8 * (L / 8) ≤ L := by omega
  obtain ⟨t₁, run₁', x8₁', g₁', sp₁', m₁', rd₁', wr₁'⟩ : ∃ t₁, runBlock isa [.lsl .x .x8 .x27 61, .lsr .x .x8 .x8 61] t =
      some t₁ ∧ t₁.gpr .x8 = BitVec.ofNat 64 (L - 8 * (L / 8)) ∧ (∀ r, r ≠ .x8 → t₁.gpr r = t.gpr r) ∧
      t₁.sp = t.sp ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits]
      rfl, ?_, fun r a => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, State.read, BitVec.setWidth_eq, ↓reduceIte, g27 it.other, low3 hL]
      rw [show L % 8 = L - 8 * (L / 8) by omega]
    · simp [gpr_write, a]
    all_goals rfl
  have it₁ : MaskInv s P c (8 * (L / 8)) t₁ :=
    ⟨by rw [g₁' _ (by decide), it.x6], by rw [m₁', it.mem],
      fun r h₁ h₂ h₃ => by rw [g₁' r h₂, it.other r h₁ h₂ h₃], by rw [sp₁', it.sp], by rw [rd₁', it.rd],
      by rw [wr₁', it.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁', ?_⟩)
  refine WP.ite (decide (L - 8 * (L / 8) = 0)) (eval_zero (by omega) x8₁') (fun hb => WP.block_nil ?_)
    (fun hb => ?_)
  · have he : 8 * (L / 8) = L := by have := of_decide_eq_true hb; omega
    rw [he] at it₁
    exact ⟨it₁.mem, it₁.other, it₁.sp, it₁.rd, it₁.wr⟩
  have hlt₀ : 8 * (L / 8) < L := by have := of_decide_eq_false hb; omega
  refine WP.loop (M := isa) (body := .block maskBody) (c := .nonzero .x .x8)
    (fun (k : Nat) (t : State) => ∃ j, k = L - j ∧ j < L ∧ t.gpr .x8 = BitVec.ofNat 64 (L - j) ∧
      MaskInv s P c j t) ?_ (L - 8 * (L / 8)) _ ⟨8 * (L / 8), rfl, hlt₀, x8₁', it₁⟩
  rintro k t ⟨j, rfl, hj, x8, it⟩
  obtain ⟨t', run', mem', x6', x8', g', sp', rd', wr'⟩ := maskStep_ok t (A := P + BitVec.ofNat 64 j) (c := c)
    (by rw [it.x6, BitVec.add_zero]) (g11 it.other) (by rw [it.rd, it.wr]; exact hr j 1 (by omega))
    (by rw [it.wr]; exact hw j 1 (by omega))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hq : t.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fP it.mem _ fun r hr' hcon => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega)] at hcon; omega
  have hmem : t'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, it.mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega), length_mask]
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (j + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev' := eval_nonzero (s := t') (x := L - (j + 1)) (by omega) x8''
  have gg : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, it.other r h₁ h₂ h₃]
  by_cases he : j + 1 = L
  · left
    exact ⟨by rw [ev']; simp [he], by rw [hmem, he], gg, by rw [sp', it.sp], by rw [rd', it.rd],
      by rw [wr', it.wr]⟩
  · right
    refine ⟨by rw [ev']; simp; omega, L - (j + 1), by omega, j + 1, rfl, by omega, x8'',
      ⟨by rw [x6', it.x6, BitVec.add_assoc, succ_ofNat], hmem, gg, by rw [sp', it.sp], by rw [rd', it.rd],
        by rw [wr', it.wr]⟩⟩

/-! ## From S2V's state on -/

theorem openTail_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State}
    (hs : SPre s₀ C D P W R L s) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) :
    WP isa (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (finish v.callee v.ctr.callee v.ctr.suffix tOff)
        (.seq (.block Impl.AesSiv.AArch64.compare) (.seq maskData (.block restore)))))) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧ s'.sp = s₀.sp ∧
        Frame (endRegions W P L) s.mem s'.mem ∧
        match Spec.Siv.openWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R)
            (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem W 16) (Spec.Aes.bytesAt s.mem P L) with
        | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
        | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  -- The counter.
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := counter_ok h hs.regs.x19 hs.regs.rd hs.regs.wr
  have hr₁ : Regs s₀ C D P W R L s₁ := hs.regs.keep' (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₁ rd₁ wr₁
  have fc : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have hcnt : ∃ hi lo : BitVec 64, s₁.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s₁.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) := by
    rw [m₁]; exact counter_cnt s.mem W
  -- CTR.
  refine WP.seq (WP.mono (ctr_wp v.ctr h hcp hPw hr₁ (length_counter _) (counter_low _) hcnt (by rw [g₁ _ (by decide) (by decide), hs.x26])
    (by rw [g₁ _ (by decide) (by decide), hs.x27])) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  -- S2V into `W + 112`.
  refine WP.seq (WP.mono (finish_wp v h h₂.regs (out := tOff) (Or.inr rfl)) fun s₃ h₃ => ?_)
  have f₃ := h₃.frame
  -- The comparison.
  obtain ⟨s₄, run₄, x0₄, x11₄, g₄, sp₄, m₄, rd₄, wr₄⟩ := compare_ok h h₃.regs.x19 h₃.regs.rd h₃.regs.wr
  have hr₄ : Regs s₀ C D P W R L s₄ := h₃.regs.keep' (fun r hr => g₄ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    sp₄ rd₄ wr₄
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  -- The mask.
  refine WP.seq (WP.mono (maskData_wp s₄ (c := decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) h.lt h.wP
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.hold.1, h₂.x26])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.hold.2, h₂.x27])
    (by rw [x11₄, x0₄]; simp only [decide_eq_true_eq]) (fun _ _ hin => h.inRP hr₄.rd hr₄.wr hin)
    (fun _ _ hin => h.inWP hPw hr₄.wr hin)) fun s₅ h₅ => ?_)
  have f₅ : Frame [⟨P, L⟩] s₄.mem s₅.mem := by
    rw [h₅.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  have hr₅ : Regs s₀ C D P W R L s₅ := hr₄.keep' (fun r hr => h₅.other r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)) h₅.sp h₅.rd h₅.wr
  have hsv₅ : Spill.Saved W g saved s₅.mem := by
    have hb := saved_bound
    refine (((hsv.frame fc fun p hp => ?_).frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame
      (m' := s₅.mem) (by rw [← m₄]; exact f₅) fun p hp => ?_
    · have := hb p hp; exact cnt_dis (by omega) (by omega)
    · have := hb p hp; exact ctr_dis h (by omega) (by omega)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega) (by simp only [tOff]; omega) (by omega) (by omega) (by omega)
    · have := hb p hp
      exact one_out (h.p_w.sub_right (h.sW (d := p.2) (n := 8) (by omega))).symm
  refine WP.mono (restore_wp h hr₅.x19 hr₅.rd hr₅.wr hsv₅) fun s₇ ⟨h₇a, h₇b, sp₇, m₇⟩ => ?_
  have x0₇ : s₇.gpr .x0 = s₄.gpr .x0 := by
    rw [h₇b _ (by decide), h₅.other _ (by decide) (by decide) (by decide)]
  -- The IV, the plaintext and S2V's end.
  have hV : Spec.Aes.bytesAt s₃.mem W 16 = Spec.Aes.bytesAt s.mem W 16 := by
    have d₃ := fin_dis h (out := tOff) (d := 0) (n := 16) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    have d₂ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    have dc := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at d₃ d₂ dc
    rw [Proof.Cmac.bytesAt_frame f₃ d₃ (by decide), Proof.Cmac.bytesAt_frame f₂ d₂ (by decide),
      Proof.Cmac.bytesAt_frame fc dc (by decide)]
  have hp : Spec.Aes.bytesAt s₂.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R)
      (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₂.data, ctxCiph_frame fc (cnt_out h.c_w) hRb, Proof.Cmac.bytesAt_frame fc (cnt_out h.p_w) hL]
  have hT : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) := by
    rw [h₃.out, hp, ctxMac_frame f₂ (ctr_out hcp h.c_w) hRb, ctxMac_frame fc (cnt_out h.c_w) hRb,
      Proof.Cmac.bytesAt_frame f₂ (ctr_out h.d_p h.d_w) (by decide),
      Proof.Cmac.bytesAt_frame fc (cnt_out h.d_w) (by decide)]
  have hd : Spec.Aes.bytesAt s₇.mem P L = if Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 then
        Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L) else Spec.Siv.zeros L := by
    have hl := length_mask s₄.mem P (decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) L
    have hw := bytesAt_writeBytes_self s₄.mem P (by rw [hl]; exact h.lt)
    rw [hl] at hw
    rw [m₇, h₅.mem, hw, m₄, Proof.Cmac.bytesAt_frame f₃ (fin_out (by decide) h.p_w) hL, hp]
    simp only [decide_eq_true_eq]
  have f₅' : Frame (endRegions W P L) s₄.mem s₅.mem :=
    f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₇a, by rw [sp₇, hr₅.sp], ?_, ?_⟩
  · rw [m₇]
    rw [m₄] at f₅'
    exact (((fc.sub (cnt_sub h)).trans (f₂.sub (ctr_sub h))).trans (f₃.sub (fin_sub h (by decide)))).trans f₅'
  · rw [x0₇, x0₄, hd, hV, hT]
    simp only [Spec.Siv.openWith]
    by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) = Spec.Aes.bytesAt s.mem W 16
    · rw [ite_eq_left hc, ite_eq_left hc.symm, ite_eq_left hc.symm]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), ite_eq_right (Ne.symm hc)]
      exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.AArch64
