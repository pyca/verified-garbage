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

/-! ## Masks -/

/-- `r10 = -[r12 + r11 + d]`, the byte zero-extended. -/
theorem bitMask_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .r11 = BitVec.ofNat 32 t) (hd : d + t + 1 ≤ size) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = 0 - (s.mem (off base (d + t))).setWidth 32 ∧ Rest [.r4, .r5, .r10] s s' ∧
        s'.mem = s.mem := by
  simp only [bitMask]
  refine wp_dp (op2_reg _ _) fun s₁ u₁ => ?_
  have hs₁ := hs.of_rest (u₁.rest (ws := [.r4]) (by simp)) (by decide)
  have e₁ : s₁.gpr .r4 = s₁.gpr .r12 + BitVec.ofNat 32 t := by
    rw [u₁.gpr, dpVal, ht, u₁.other _ (by decide)]
  refine wp_ldrb (hs.off_lt (by omega)) (hs₁.ea_reg e₁ (d := d) (by omega))
    (hs₁.read (d := t + d) (n := 1) (by omega)) fun s₂ u₂ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₃ u₃ => ?_
  refine wp_dp (op2_reg _ _) fun s₄ u₄ => WP.block_nil ⟨?_, (u₁.rest (by simp)).trans ((u₂.rest (by simp)).trans
    ((u₃.rest (by simp)).trans (u₄.rest (by simp)))), by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  rw [u₄.gpr, dpVal, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₁.mem, Nat.add_comm t d]

theorem neg_bit (c : Bool) :
    0 - ((if c then 1 else 0 : BitVec 8)).setWidth 32 = (if c then BitVec.allOnes 32 else 0) := by
  cases c <;> decide

/-- The mask of a byte that is 0 or 1. -/
theorem bitMask_bool_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d t : Nat}
    (ht : s.gpr .r11 = BitVec.ofNat 32 t) (hd : d + t + 1 ≤ size) {c : Bool}
    (hc : s.mem (off base (d + t)) = if c then 1 else 0) :
    WP isa (.block (bitMask d)) s fun s' =>
      s'.gpr .r10 = (if c then BitVec.allOnes 32 else 0) ∧ Rest [.r4, .r5, .r10] s s' ∧ s'.mem = s.mem :=
  WP.mono (bitMask_ok hs ht hd) fun _ ⟨e, k, m⟩ => ⟨by rw [e, hc, neg_bit], k, m⟩

/-! ## The table of bits -/

/-- The body of `bits`' loop. -/
def bitsBody (src dst : Nat) : List Instr :=
  [decCounter, .dp .add .r4 wb (.reg .r11), .ldrb .r4 .r4 src, .dp .add .r5 wb (.shifted .r11 .lsl 3)] ++
    (List.range 8).flatMap (bitJ dst) ++ [testCounter]

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
theorem bitJ_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (hb : s.gpr .r5 = s.gpr .r12 + BitVec.ofNat 32 (8 * i)) {b : BitVec 8} (ha : s.gpr .r4 = b.setWidth 32)
    {dst j : Nat} (hj : j < 8) (hd : dst + (8 * i + j) + 1 ≤ size) :
    WP isa (.block (bitJ dst j)) s fun s' => Rest [.r7] s s' ∧
      s'.mem = s.mem.writeW (off base (dst + (8 * i + j))) (if b.getLsbD j then 1 else 0 : BitVec 8) := by
  have e : 8 * i + (dst + j) = dst + (8 * i + j) := by omega
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [bitJ, ite_true, List.cons_append, List.nil_append]
    refine wp_dp (op2_imm (by decide)) fun s₁ u₁ => ?_
    have k₁ : Rest [.r7] s s₁ := u₁.rest (by simp)
    have hs₁ := hs.of_rest k₁ (by decide)
    have hb₁ : s₁.gpr .r5 = s₁.gpr .r12 + BitVec.ofNat 32 (8 * i) := by
      rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hb]
    refine wp_strb (hs.off_lt (by omega)) (hs₁.ea_reg hb₁ (d := dst + 0) (by omega))
      (hs₁.write (d := 8 * i + (dst + 0)) (n := 1) (by omega)) fun s₂ m₂ => WP.block_nil
      ⟨k₁.trans (m₂.rest _), ?_⟩
    rw [m₂.mem, e, u₁.mem, u₁.gpr, dpVal, ha]
    exact congrArg _ (bit_byte0 b)
  · simp only [bitJ, show ¬j = 0 by omega, ite_false, List.cons_append, List.nil_append]
    refine wp_mov (op2_lsr (by omega)) fun s₁ u₁ => ?_
    refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
    have k₂ : Rest [.r7] s s₂ := (u₁.rest (by simp)).trans (u₂.rest (by simp))
    have hs₂ := hs.of_rest k₂ (by decide)
    have hb₂ : s₂.gpr .r5 = s₂.gpr .r12 + BitVec.ofNat 32 (8 * i) := by
      rw [k₂.gpr _ (by decide), k₂.gpr _ (by decide), hb]
    refine wp_strb (hs.off_lt (by omega)) (hs₂.ea_reg hb₂ (d := dst + j) (by omega))
      (hs₂.write (d := 8 * i + (dst + j)) (n := 1) (by omega)) fun s₃ m₃ => WP.block_nil
      ⟨k₂.trans (m₃.rest _), ?_⟩
    rw [m₃.mem, e, u₂.mem, u₁.mem, u₂.gpr, dpVal, u₁.gpr, ha]
    exact congrArg _ (bit_byte b j hj)

/-- The first `k` bits of the byte in `r4`. -/
theorem bitJs_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {i : Nat}
    (hb : s.gpr .r5 = s.gpr .r12 + BitVec.ofNat 32 (8 * i)) {b : BitVec 8} (ha : s.gpr .r4 = b.setWidth 32)
    {dst : Nat} (hd : dst + 8 * i + 8 ≤ size) : ∀ k ≤ 8,
    WP isa (.block ((List.range k).flatMap (bitJ dst))) s fun s' => Rest [.r7] s s' ∧
      (∀ j < k, s'.mem (off base (dst + (8 * i + j))) = if b.getLsbD j then 1 else 0) ∧
      Outside base (dst + 8 * i) k s.mem s'.mem
  | 0, _ => WP.block_nil ⟨Rest.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _),
      VG.Proof.Mont.Outside.refl _ _ _ _⟩
  | k + 1, hk => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine VG.Proof.X25519.Arm.WP.append (bitJs_ok hs hb ha hd k (by omega)) fun s₁ ⟨k₁, e₁, O₁⟩ => ?_
    refine WP.mono (bitJ_ok (hs.of_rest k₁ (by decide)) (i := i)
      (by rw [k₁.gpr _ (by decide), k₁.gpr _ (by decide), hb]) (b := b) (by rw [k₁.gpr _ (by decide), ha])
      (dst := dst) (j := k) (by omega) (by omega)) fun s₂ ⟨k₂, m₂⟩ => ?_
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
theorem bitsBody_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {src dst i : Nat}
    (ht : s.gpr .r11 = BitVec.ofNat 32 (i + 1)) (hi : i + 1 < 2 ^ 32)
    (hsrc : src + i + 1 ≤ size) (hd : dst + 8 * i + 8 ≤ size) :
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
  have hs₄ := hs.of_rest k₄ (by decide)
  have r11₄ : s₄.gpr .r11 = BitVec.ofNat 32 i := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), c₁]
  have r5₄ : s₄.gpr .r5 = s₄.gpr .r12 + BitVec.ofNat 32 (8 * i) := by
    have r11₃ : s₃.gpr .r11 = BitVec.ofNat 32 i := by rw [u₃.other _ (by decide), u₂.other _ (by decide), c₁]
    rw [u₄.gpr, dpVal, r11₃, u₄.other _ (by decide)]
    exact rowAddr _ i
  have mem₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have r4₄ : s₄.gpr .r4 = (s.mem (off base (src + i))).setWidth 32 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.mem, u₁.mem, Nat.add_comm i src]
  rw [List.nil_append]
  refine VG.Proof.X25519.Arm.WP.append (bitJs_ok hs₄ r5₄ r4₄ (dst := dst) (by omega) 8 (Nat.le_refl _))
    fun s₅ ⟨k₅, e₅, O₅⟩ => ?_
  have r11₅ : s₅.gpr .r11 = BitVec.ofNat 32 i := by rw [k₅.gpr _ (by decide), r11₄]
  refine wp_testCounter (by omega) r11₅ fun s₆ f₆ z₆ => WP.block_nil
    ⟨by rw [f₆.gpr, r11₅], z₆, (k₄.trans (k₅.mono (by simp))).trans (f₆.rest _), ?_, ?_⟩
  · rw [f₆.mem]; exact e₅
  · rw [f₆.mem, ← mem₄]; exact O₅

/-- `bits`' loop invariant, at `r11 = i`: the bytes from `i` up are done. -/
structure BInv (base : Addr) (size src dst n : Nat) (s₀ s : State) (i : Nat) : Prop where
  scr : Scr s base size
  r11 : s.gpr .r11 = BitVec.ofNat 32 i
  keep : Rest [.r4, .r5, .r7, .r11] s₀ s
  mem : Outside base dst (64 * n) s₀.mem s.mem
  bits : ∀ t, 8 * i ≤ t → t < 64 * n → s.mem (off base (dst + t)) =
    if (s₀.mem (off base (src + t / 8))).getLsbD (t % 8) then 1 else 0

/-- `bits src dst (8 n)`: byte `t` of the table at `dst` is bit `t` of the
`n`-word number at `src`. -/
theorem bits_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n src dst : Nat}
    (hn0 : 0 < n) (hsrc : src + 8 * n ≤ size) (hdst : dst + 64 * n ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 64 * n ≤ src) (henc : encodable (BitVec.ofNat 32 (8 * n)) = true) :
    WP isa (bits src dst (8 * n)) s fun s' =>
      (∀ t < 64 * n, s'.mem (off base (dst + t)) =
        if (wordsVal s.mem base src n).testBit t then 1 else 0) ∧
      Rest [.r4, .r5, .r7, .r11] s s' ∧ Outside base dst (64 * n) s.mem s'.mem := by
  have hnw := hs.nowrap
  have hsm := hs.small
  rw [bits_eq]
  have h0 : WP isa (.block [.mov .r11 (.imm (BitVec.ofNat 32 (8 * n)))]) s fun s' =>
      BInv base size src dst n s s' (8 * n) :=
    wp_mov (op2_imm henc) fun s₁ u₁ => WP.block_nil ⟨hs.of_rest (u₁.rest (ws := [.r4, .r5, .r7, .r11])
      (by simp)) (by decide), u₁.gpr, u₁.rest (by simp),
      by rw [u₁.mem]; exact VG.Proof.Mont.Outside.refl _ _ _ _, fun t ht ht' => absurd ht' (by omega)⟩
  refine WP.seq (WP.mono h0 fun s₁ h₁ => ?_)
  refine countLoop_ok (Inv := fun j s' => BInv base size src dst n s s' j) (n := 8 * n)
    (fun j s' h1 h2 hb => ?_) (fun s' hb => ⟨fun t ht => ?_, hb.keep, hb.mem⟩) (by omega) h₁
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    refine WP.mono (bitsBody_ok hb.scr hb.r11 (by omega) (by omega) (by omega))
      fun s'' ⟨b', z', k', bits', O'⟩ => ?_
    have hbyte : s'.mem (off base (src + i)) = s.mem (off base (src + i)) :=
      hb.mem _ (by rw [ofs_off0 base (d := src + i) (by omega)]; omega)
    refine ⟨⟨hb.scr.of_rest k' (by decide), b', hb.keep.trans k',
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
