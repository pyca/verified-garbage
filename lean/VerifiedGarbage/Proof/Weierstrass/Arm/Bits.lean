import VerifiedGarbage.Proof.Weierstrass.Arm.Loop
import VerifiedGarbage.Proof.Weierstrass.Words

/-!
# Short Weierstrass curves on 32-bit ARM: tables of bits, and masks of bits

`bits src dst (8 n)` writes the bits of the `n`-word number at `src`, one byte
each, to the table at `dst` (`bits_ok`): a loop over its bytes, from the top
one down, each giving eight bytes of the table (`bitsBody_ok`). `bitMask d`
makes the mask `r10` of the byte `r11` of the table at `d` (`bitMask_ok`):
all ones for a 1, zero for a 0 (`bitMask_bool_ok`).
-/

namespace VG.Proof.Weierstrass.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
  VG.Proof.Mont.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_dp wp_mov wp_ldrb wp_strb op2_imm op2_reg op2_lsr op2_lsl
  dpVal)

/-! ## Offsets past 4096 -/

/-- What `far r d` adds to `r`. -/
abbrev farOff (d : Nat) : Nat := if d < 4096 then 0 else 4096

theorem far_add {d : Nat} (hd : d < 8192) : farOff d + d % 4096 = d := by
  unfold farOff; split <;> omega

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `far r d`, for `r = r12 + k`: `r = r12 + k + farOff d`. -/
theorem wp_far {r : Reg} {d k : Nat} (hr : s.gpr r = s.gpr .r12 + BitVec.ofNat 32 k) (hrr : r ≠ .r12)
    (kk : ∀ t, Rest [r] s t → t.mem = s.mem → t.gpr r = t.gpr .r12 + BitVec.ofNat 32 (k + farOff d) →
      WP isa (.block is) t Q) :
    WP isa (.block (far r d ++ is)) s Q := by
  unfold far
  by_cases h : d < 4096
  · simp only [h, ite_true, List.nil_append]
    exact kk s (Rest.refl _ _) rfl (by rw [hr, farOff, ite_eq_left_of_eq_true _ _ (eq_true h), Nat.add_zero])
  · simp only [h, ite_false, List.cons_append, List.nil_append]
    refine wp_dp (op2_imm (by decide)) fun t u => kk t (u.rest (by simp)) u.mem ?_
    rw [u.gpr, dpVal, hr, u.other _ (Ne.symm hrr), farOff, ite_eq_right_of_eq_false _ _ (eq_false h),
      show (4096 : BitVec 32) = BitVec.ofNat 32 4096 from rfl, Offset.add_add]

end

/-! ## Masks -/

/-- `r10 = -[r12 + r11 + d]`, the byte zero-extended. -/
theorem bitMask_ok {s : State} {base : Addr} {size len : Nat} (hs : Scr s base size) (hf : Far s base len)
    {d t : Nat} (ht : s.gpr .r11 = BitVec.ofNat 32 t) (hd : d + t + 1 ≤ len) (hd8 : d < 8192) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = 0 - (s.mem (off base (d + t))).setWidth 32 ∧ Rest [.r4, .r5, .r10] s s' ∧
        s'.mem = s.mem := by
  simp only [bitMask, List.cons_append, List.nil_append]
  refine wp_dp (op2_reg _ _) fun s₁ u₁ => ?_
  have k₁ : Rest [.r4, .r5, .r10] s s₁ := u₁.rest (by simp)
  have e₁ : s₁.gpr .r4 = s₁.gpr .r12 + BitVec.ofNat 32 t := by
    rw [u₁.gpr, dpVal, ht, u₁.other _ (by decide)]
  refine wp_far e₁ (by decide) fun s₂ k₂ m₂ e₂ => ?_
  have k₂' : Rest [.r4, .r5, .r10] s s₂ := k₁.trans (k₂.mono (by simp))
  have hs₂ := hs.of_rest k₂' (by decide)
  have hf₂ := hf.of_rest k₂'
  have ea : State.addr (s₂.gpr .r4 + BitVec.ofNat 32 (d % 4096)) = off base (d + t) := by
    rw [hf₂.ea_reg hs₂ e₂ (by have := far_add hd8; omega)]
    have := far_add hd8
    congr 1; omega
  refine wp_ldrb (by omega) ea (hf₂.read (d := d + t) (n := 1) hd) fun s₃ u₃ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₄ u₄ => ?_
  refine wp_dp (op2_reg _ _) fun s₅ u₅ => WP.block_nil ⟨?_, k₂'.trans ((u₃.rest (by simp)).trans
    ((u₄.rest (by simp)).trans (u₅.rest (by simp)))), by rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem]⟩
  rw [u₅.gpr, dpVal, u₄.gpr, u₄.other _ (by decide), u₃.gpr, m₂, u₁.mem]

theorem neg_bit (c : Bool) :
    0 - ((if c then 1 else 0 : BitVec 8)).setWidth 32 = (if c then BitVec.allOnes 32 else 0) := by
  cases c <;> decide

/-- The mask of a byte that is 0 or 1. -/
theorem bitMask_bool_ok {s : State} {base : Addr} {size len : Nat} (hs : Scr s base size) (hf : Far s base len)
    {d t : Nat} (ht : s.gpr .r11 = BitVec.ofNat 32 t) (hd : d + t + 1 ≤ len) (hd8 : d < 8192) {c : Bool}
    (hc : s.mem (off base (d + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = (if c then BitVec.allOnes 32 else 0) ∧ Rest [.r4, .r5, .r10] s s' ∧ s'.mem = s.mem :=
  WP.mono (bitMask_ok hs hf ht hd hd8) fun _ ⟨e, k, m⟩ => ⟨by rw [e, hc, neg_bit], k, m⟩

/-! ## The table of bits -/

/-- The body of `bits`' loop. -/
def bitsBody (src dst : Nat) : List Instr :=
  [decCounter, .dp .add .r4 wb (.reg .r11), .ldrb .r4 .r4 src, .dp .add .r5 wb (.shifted .r11 .lsl 3)] ++
    far .r5 dst ++ (List.range 8).flatMap (bitJ dst) ++ [testCounter]

theorem bits_eq (src dst nbytes : Nat) :
    bits src dst nbytes = .seq (.block [.mov .r11 (.imm (BitVec.ofNat 32 nbytes))])
      (.loop (.block (bitsBody src dst)) .ne) :=
  rfl

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    ((((b.setWidth 32 >>> j) &&& 1).setWidth 8) : BitVec 8) = if b.getLsbD j then 1 else 0 := by
  decide +kernel

theorem bit_byte0 : ∀ b : BitVec 8,
    (((b.setWidth 32 &&& 1).setWidth 8) : BitVec 8) = if b.getLsbD 0 then 1 else 0 := by
  decide +kernel

/-- Byte `j` of the eight at `r5 + dst`: bit `j` of the byte in `r4`. -/
theorem bitJ_ok {s : State} {base : Addr} {size len : Nat} (hs : Scr s base size) (hf : Far s base len) {i : Nat}
    {dst : Nat} (hb : s.gpr .r5 = s.gpr .r12 + BitVec.ofNat 32 (8 * i + farOff dst)) {b : BitVec 8}
    (ha : s.gpr .r4 = b.setWidth 32) {j : Nat} (hj : j < 8) (hd : dst + (8 * i + j) + 1 ≤ len)
    (hd8 : dst < 8192) (hal : dst % 8 = 0) :
    WP isa (.block (bitJ dst j)) s fun s' => Rest [.r7] s s' ∧
      s'.mem = s.mem.writeW (off base (dst + (8 * i + j))) (if b.getLsbD j then 1 else 0 : BitVec 8) := by
  have fa := far_add hd8
  have hoff : dst % 4096 + j < 4096 := by omega
  have e : 8 * i + farOff dst + (dst % 4096 + j) = dst + (8 * i + j) := by omega
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.cons_append, List.nil_append]
    refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => ?_
    have k₁ : Rest [.r7] s s₁ := u₁.rest (by simp)
    have hs₁ := hs.of_rest k₁ (by decide)
    have hf₁ := hf.of_rest k₁
    have hb₁ : s₁.gpr .r5 = s₁.gpr .r12 + BitVec.ofNat 32 (8 * i + farOff dst) := by
      rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hb]
    refine wp_strb hoff (by rw [hf₁.ea_reg hs₁ hb₁ (by omega), e])
      (hf₁.write (d := dst + (8 * i + 0)) (n := 1) (by omega)) fun s₂ m₂ => WP.block_nil
      ⟨k₁.trans (m₂.rest _), ?_⟩
    rw [m₂.mem, u₁.mem, u₁.gpr, dpVal, ha]
    exact congrArg _ (bit_byte0 b)
  · simp only [bitJ, show ¬j = 0 by omega, ite_false, List.cons_append, List.nil_append]
    refine wp_mov (op2_lsr (by omega)) fun s₁ u₁ => ?_
    refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
    have k₂ : Rest [.r7] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
    have hs₂ := hs.of_rest k₂ (by decide)
    have hf₂ := hf.of_rest k₂
    have hb₂ : s₂.gpr .r5 = s₂.gpr .r12 + BitVec.ofNat 32 (8 * i + farOff dst) := by
      rw [k₂.gpr _ (by decide), k₂.gpr _ (by decide), hb]
    refine wp_strb hoff (by rw [hf₂.ea_reg hs₂ hb₂ (by omega), e])
      (hf₂.write (d := dst + (8 * i + j)) (n := 1) (by omega)) fun s₃ m₃ => WP.block_nil
      ⟨k₂.trans (m₃.rest _), ?_⟩
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.gpr, dpVal, u₁.gpr, ha]
    exact congrArg _ (bit_byte b j hj)

/-- The first `k` bits of the byte in `r4`. -/
theorem bitJs_ok {s : State} {base : Addr} {size len : Nat} (hs : Scr s base size) (hf : Far s base len)
    {i dst : Nat} (hb : s.gpr .r5 = s.gpr .r12 + BitVec.ofNat 32 (8 * i + farOff dst)) {b : BitVec 8}
    (ha : s.gpr .r4 = b.setWidth 32) (hd : dst + 8 * i + 8 ≤ len) (hd8 : dst < 8192) (hal : dst % 8 = 0) :
    ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap (bitJ dst))) s fun s' => Rest [.r7] s s' ∧
      (∀ j < k, s'.mem (off base (dst + (8 * i + j))) = if b.getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) k s.mem s'.mem
  | 0, _ => WP.block_nil ⟨Rest.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hf.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (bitJs_ok hs hf hb ha hd hd8 hal k (by omega)) fun s₁ ⟨k₁, e₁, O₁⟩ => ?_
    refine WP.mono (bitJ_ok (hs.of_rest k₁ (by decide)) (hf.of_rest k₁) (i := i)
      (by rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hb]) (b := b) (by rw [k₁.gpr _ (by decide), ha])
      (j := k) (by omega) (by omega) hd8 hal) fun s₂ ⟨k₂, m₂⟩ => ?_
    have O₂ : Outside base (dst + (8 * i + k)) 1 s₁.mem s₂.mem := by
      rw [m₂]; exact writeW8_outside _ _ _ (by omega)
    refine ⟨k₁.trans k₂, fun j hj => ?_,
      (O₁.mono (Nat.le_refl _) (by omega)).trans (O₂.mono (by omega) (by omega))⟩
    rcases Nat.lt_or_ge j k with h | h
    · rw [O₂ _ (by rw [ofs_off0 base (d := dst + (8 * i + j)) (by omega)]; omega), e₁ j h]
    · obtain rfl : j = k := by omega
      rw [m₂, writeW8_self]

/-- `r12 + (i << 3)`. -/
theorem rowAddr (e : BitVec 32) (i : Nat) : e + BitVec.ofNat 32 i <<< 3 = e + BitVec.ofNat 32 (8 * i) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [VG.Proof.X25519.Arm.toNat_shl, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- One byte of the number at `src`, the one below `r11 = i + 1`: its bits to
the table at `dst`. -/
theorem bitsBody_ok {s : State} {base : Addr} {size len : Nat} (hs : Scr s base size) (hf : Far s base len)
    {src dst i : Nat} (ht : s.gpr .r11 = BitVec.ofNat 32 (i + 1)) (hi : i + 1 < 2 ^ 32)
    (hsrc : src + i + 1 ≤ size) (hd : dst + 8 * i + 8 ≤ len) (hd8 : dst < 8192) (hal : dst % 8 = 0) :
    WP isa (.block (bitsBody src dst)) s fun s' =>
      s'.gpr .r11 = BitVec.ofNat 32 i ∧ s'.z = decide (i = 0) ∧
      Rest [.r4, .r5, .r7, .r11] s s' ∧
      (∀ j < 8, s'.mem (off base (dst + (8 * i + j))) =
        if (s.mem (off base (src + i))).getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) 8 s.mem s'.mem := by
  simp only [bitsBody, List.cons_append, List.append_assoc]
  refine wp_decCounter (j := i + 1) (by omega) ht fun s₁ u₁ => ?_
  have c₁ : s₁.gpr .r11 = BitVec.ofNat 32 i := by rw [u₁.gpr, Nat.add_sub_cancel]
  refine wp_dp (op2_reg _ _) fun s₂ u₂ => ?_
  have k₂ : Rest [.r4, .r5, .r7, .r11] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  have hs₂ := hs.of_rest k₂ (by decide)
  have e₂ : s₂.gpr .r4 = s₂.gpr .r12 + BitVec.ofNat 32 i := by
    rw [u₂.gpr, dpVal, c₁, u₂.other _ (by decide)]
  refine wp_ldrb (hs.off_lt (by omega)) (hs₂.ea_reg e₂ (d := src) (by omega))
    (hs₂.read (d := i + src) (n := 1) (by omega)) fun s₃ u₃ => ?_
  refine wp_dp (op2_lsl (by decide)) fun s₄ u₄ => ?_
  have k₄ : Rest [.r4, .r5, .r7, .r11] s s₄ := k₂.trans ((u₃.rest (by simp)).trans (u₄.rest (by simp)))
  have r5₄ : s₄.gpr .r5 = s₄.gpr .r12 + BitVec.ofNat 32 (8 * i) := by
    have r11₃ : s₃.gpr .r11 = BitVec.ofNat 32 i := by rw [u₃.other _ (by decide), u₂.other _ (by decide), c₁]
    rw [u₄.gpr, dpVal, r11₃, u₄.other _ (by decide)]
    exact rowAddr _ i
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r4₄ : s₄.gpr .r4 = (s.mem (off base (src + i))).setWidth 32 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, Nat.add_comm i src]
  rw [← List.append_assoc]
  refine wp_far r5₄ (by decide) fun s₅ k₅ m₅ r5₅ => ?_
  have k₅' : Rest [.r4, .r5, .r7, .r11] s s₅ := k₄.trans (k₅.mono (by simp))
  have hs₅ := hs.of_rest k₅' (by decide)
  have hf₅ := hf.of_rest k₅'
  have r11₅ : s₅.gpr .r11 = BitVec.ofNat 32 i := by
    rw [k₅.gpr _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), c₁]
  have r4₅ : s₅.gpr .r4 = (s.mem (off base (src + i))).setWidth 32 := by
    rw [k₅.gpr _ (by decide), r4₄]
  refine VG.Proof.X25519.Arm.WP.append (bitJs_ok hs₅ hf₅ r5₅ r4₅ (dst := dst) (by omega) hd8 hal 8
    (Nat.le_refl _)) fun s₆ ⟨k₆, e₆, O₆⟩ => ?_
  have r11₆ : s₆.gpr .r11 = BitVec.ofNat 32 i := by rw [k₆.gpr _ (by decide), r11₅]
  refine wp_testCounter (by omega) r11₆ fun s₇ f₇ z₇ => WP.block_nil
    ⟨by rw [f₇.gpr, r11₆], z₇, (k₅'.trans (k₆.mono (by simp))).trans (f₇.rest _), ?_, ?_⟩
  · rw [f₇.mem]; exact e₆
  · rw [f₇.mem, ← mem₄, ← m₅]; exact O₆

/-- `bits`' loop invariant, at `r11 = i`: the bytes from `i` up are done. -/
structure BInv (base : Addr) (size len src dst n : Nat) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base size
  far : Far s base len
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  keep : Rest [.r4, .r5, .r7, .r11] s₀ s
  mem : Outside base dst (64 * n) s₀.mem s.mem
  bits : ∀ t, 8 * i ≤ t → t < 64 * n → s.mem (off base (dst + t)) =
    if (s₀.mem (off base (src + t / 8))).getLsbD (t % 8) then 1 else 0

/-- `bits src dst (8 n)`: byte `t` of the table at `dst` is bit `t` of the
`n`-word number at `src`. -/
theorem bits_ok {s : State} {base : Addr} {size len : Nat} (hs : Scr s base size) (hf : Far s base len)
    {n src dst : Nat} (hn0 : 0 < n) (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ len)
    (hd8 : dst < 8192) (hal : dst % 8 = 0)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) (henc : encodable (BitVec.ofNat 32 (8 * n)) = true) :
    WP isa (bits src dst (8 * n)) s fun s' =>
      (∀ t < 64 * n, s'.mem (off base (dst + t)) =
        if (wordsVal s.mem base src n).testBit t then 1 else 0) ∧
      Rest [.r4, .r5, .r7, .r11] s s' ∧ Outside base dst (64 * n) s.mem s'.mem := by
  have hnw := hf.nowrap
  rw [bits_eq]
  have h0 : WP isa (.block [.mov .r11 (.imm (BitVec.ofNat 32 (8 * n)))]) s fun s' =>
      BInv base size len src dst n s s' (8 * n) :=
    wp_mov (op2_imm henc) fun s₁ u₁ => WP.block_nil ⟨hs.of_rest (u₁.rest (ws := [.r4, .r5, .r7, .r11])
      (by simp)) (by decide), hf.of_rest (u₁.rest (ws := [.r4, .r5, .r7, .r11]) (by simp)), u₁.gpr,
      u₁.rest (by simp), by rw [u₁.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _,
      fun t ht ht' => absurd ht' (by omega)⟩
  refine WP.seq (WP.mono h0 fun s₁ h₁ => ?_)
  refine countLoop_ok (Inv := fun j s' => BInv base size len src dst n s s' j) (n := 8 * n)
    (fun j s' h1 h2 hb => ?_) (fun s' hb => ⟨fun t ht => ?_, hb.keep, hb.mem⟩) (by omega) h₁
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine WP.mono (bitsBody_ok hb.scr hb.far hb.r11 (by omega) (by omega) (by omega) hd8 hal)
      fun s'' ⟨b', z', k', bits', O'⟩ => ?_
    have hbyte : s'.mem (off base (src + i)) = s.mem (off base (src + i)) :=
      hb.mem _ (by rw [ofs_off0 base (d := src + i) (by have := hs.nowrap; omega)]; omega)
    refine ⟨⟨hb.scr.of_rest k' (by decide), hb.far.of_rest k', b', hb.keep.trans k',
      hb.mem.trans (O'.mono (by omega) (by omega)), fun t ht ht' => ?_⟩, by rw [z']; rfl⟩
    rcases Nat.lt_or_ge t (8 * (i + 1)) with h | h
    · have e := bits' (t - 8 * i) (by omega)
      rw [show 8 * i + (t - 8 * i) = t by omega, hbyte] at e
      rw [e, show t / 8 = i by omega, show t % 8 = t - 8 * i by omega]
    · rw [O' _ (by rw [ofs_off0 base (d := dst + t) (by omega)]; omega), hb.bits t h ht']
  · rw [hb.bits t (by omega) ht, show t = 8 * (t / 8) + t % 8 from (Nat.div_add_mod t 8).symm,
      VG.Proof.Weierstrass.testBit_byte s.mem base (a := src) (n := n) (by omega) (Nat.mod_lt _ (by decide))]
    simp only [show (8 * (t / 8) + t % 8) / 8 = t / 8 by omega, show (8 * (t / 8) + t % 8) % 8 = t % 8 by omega]

end VG.Proof.Weierstrass.Arm
