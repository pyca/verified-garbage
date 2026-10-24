module
public import VerifiedGarbage.Proof.X448.PPC64LE.Ladder
public import VerifiedGarbage.Spec.X448.Contract

import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# X448 on PPC64LE: the bits of the scalar

`bits` stores bit `t` of the decoded (clamped) scalar at byte `BITS + t` of
the working space, for `t < 448` (`bits_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X448 (bit)

/-- Bit `t` of the scalar's bytes at `SC`, unclamped. -/
def rawBit (m : Mem) (SC : Addr) (t : Nat) : Nat := ((m (SC + BitVec.ofNat 64 (t / 8))).toNat >>> (t % 8)) &&& 1

theorem getD_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- Bit `j` of a register, by shifting it to the top and back. -/
theorem bit_shift (x : BitVec 64) {j : Nat} (hj : j < 64) :
    ((x <<< (63 - j)) >>> 63).toNat = (x.toNat >>> j) &&& 1 := by
  rw [toNat_shr, toNat_shl, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod,
    show (2 : Nat) ^ 64 = 2 ^ (j + 1) * 2 ^ (63 - j) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_mod_mul_right, show (2 : Nat) ^ 63 = 2 ^ j * 2 ^ (63 - j) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mul_div_mul_right _ _ (Nat.two_pow_pos _), Nat.pow_succ, Nat.mod_mul_right_div_self]

theorem stb_byte {v : BitVec 64} {x : Nat} (h : v.toNat = x) :
    v.setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

section
variable {b : Addr}

/-- While storing the bits of byte `i`, from `s1` (with the byte in `r7`),
after `j` bits. -/
structure JInv (b : Addr) (i : Nat) (x : Nat) (s1 : State) (j : Nat) (s : State) : Prop where
  rest : Rest [.r8] s1 s
  frame : Frame [⟨b + BitVec.ofNat 64 (BITS + 8 * i), j⟩] s1.mem s.mem
  bits : ∀ j' < j, s.mem (b + BitVec.ofNat 64 (BITS + 8 * i + j')) = BitVec.ofNat 8 ((x >>> j') &&& 1)

theorem bitStep_ok {i j : Nat} (hi : i < 56) (hj : j < 8) {x : Nat} {s1 s : State}
    (hc : Ctx b s1) (h7 : (s1.gpr .r7).toNat = x) (h9 : s1.gpr .r9 = b + BitVec.ofNat 64 (8 * i))
    (h : JInv b i x s1 j s) :
    WP isa (.block [.lsl .r8 .r7 (63 - j), .lsr .d .r8 .r8 63, .stb .r8 .r9 (BITS + j)]) s
      (JInv b i x s1 (j + 1)) := by
  have hB : BITS = 1064 := rfl
  have e7 : (s.gpr .r7).toNat = x := by rw [h.rest.gpr _ (by decide), h7]
  have e9 : s.gpr .r9 = b + BitVec.ofNat 64 (8 * i) := by rw [h.rest.gpr _ (by decide), h9]
  refine wp_lsl (by omega) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
  have e8 : (s3.gpr .r8).toNat = (x >>> j) &&& 1 := by
    rw [u3.gpr, u2.gpr, bit_shift _ (by omega), e7]
  refine wp_stb (a := b + BitVec.ofNat 64 (BITS + 8 * i + j)) (by decide) (by omega_using [hj, hB])
    (by rw [u3.other _ (by decide), u2.other _ (by decide), e9, Offset.add_add]; congr 2; omega_using [])
    (by rw [u3.wr, u2.wr, h.rest.wr]; exact hc.inW (by omega_using [hi, hj, hB])) fun s4 u4 =>
      WP.block_nil ⟨?_, ?_, fun j' hj' => ?_⟩
  · exact h.rest.trans ((u2.rest (by decide)).trans ((u3.rest (by decide)).trans (u4.rest _)))
  · rw [u4.mem, u3.mem, u2.mem]
    exact (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW
      (List.mem_singleton_self _) _ (Offset.contains _ (by omega_using []) (by omega_using []) (by omega_using [hi, hj, hB]))
  · rw [u4.mem, VG.WriteBytes.writeW8_apply, u3.mem, u2.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · rw [iteF (Offset.add_ofNat_ne _ (by omega) (by omega_using [hi, hj, hB]) (by omega))]; exact h.bits j' hj'
    · rw [iteT rfl]; exact stb_byte e8

/-- The loop invariant of `bits` from `s0`, before byte `i`. -/
structure BInv (b : Addr) (sc : Addr) (s0 : State) (i : Nat) (s : State) : Prop where
  ctx : Ctx b s
  rest : Rest [.r4, .r7, .r8, .r9, .r11] s0 s
  r4 : s.gpr .r4 = sc + BitVec.ofNat 64 i
  r9 : s.gpr .r9 = b + BitVec.ofNat 64 (8 * i)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (56 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 BITS, 8 * i⟩] s0.mem s.mem
  bits : ∀ t < 8 * i, s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (rawBit s0.mem sc t)

theorem bitsBody_ok {sc : Addr} {s0 : State}
    (hin : (⟨sc, 56⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨sc, 56⟩ ⟨b, 4096⟩) {i : Nat} (hi : i < 56) {s : State}
    (h : BInv b sc s0 i s) :
    WP isa (.block bitsBody) s fun s' => BInv b sc s0 (i + 1) s' ∧
      (s'.gpr .r11 != 0) = decide (56 - (i + 1) ≠ 0) := by
  have hB : BITS = 1064 := rfl
  unfold bitsBody
  simp only [List.cons_append, List.nil_append]
  refine wp_lbz (a := sc + BitVec.ofNat 64 i) (by decide) (by decide)
    (by rw [h.r4]; simp)
    (by rw [h.rest.rd, h.rest.wr]; exact in_base hin (by omega_using [hi]) (by omega_using [hi])) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := h.ctx.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide)
  -- The byte, as in `s0`.
  have hx : (s1.gpr .r7).toNat = (s0.mem (sc + BitVec.ofNat 64 i)).toNat := by
    rw [u1.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (BitVec.isLt _) (by decide))]
    congr 1
    refine h.frame _ fun r hr hcon => ?_
    rw [List.mem_singleton.mp hr] at hcon
    exact hd _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))
      ((Offset.sub_base b (d := BITS) (n := 8 * i) (k := 4096) (by omega_using [hi, hB])) _ hcon)
  refine WP.append (wp_range_flatMap (M := isa) (JInv b i (s0.mem (sc + BitVec.ofNat 64 i)).toNat s1)
    (fun j s' hj h' => bitStep_ok hi hj hc1 hx (by rw [u1.other _ (by decide), h.r9]) h') 8 (Nat.le_refl _) s1
    ⟨Rest.refl _ _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩) fun s2 h2 => ?_
  refine wp_addi (by decide) (by decide) fun s3 u3 => wp_addi (by decide) (by decide) fun s4 u4 =>
    wp_subi (by decide) (by decide) fun s5 u5 => WP.block_nil ?_
  have hr5 : Rest [.r4, .r7, .r8, .r9, .r11] s s5 :=
    (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  have hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  have r11' : s5.gpr .r11 = BitVec.ofNat 64 (56 - (i + 1)) := by
    rw [u5.gpr, u4.other _ (by decide), u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r11, ofNat_sub_one (by omega_using [hi]) (by omega_using [hi]), Nat.sub_sub]
  refine ⟨⟨h.ctx.of_rest hr5 (by decide), h.rest.trans hr5, ?_, ?_, r11', ?_, fun t ht => ?_⟩, ?_⟩
  · rw [u5.other _ (by decide), u4.other _ (by decide), u3.gpr, h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r4, Offset.add_add]
  · rw [u5.other _ (by decide), u4.gpr, u3.other _ (by decide), h2.rest.gpr _ (by decide),
      u1.other _ (by decide), h.r9, Offset.add_add, Nat.mul_succ]
  · rw [hm5]
    refine (h.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).trans ?_
    rw [← u1.mem]
    exact h2.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr]; exact Offset.sub _ (by omega_using []) (by omega_using [])⟩
  · rw [hm5]
    rcases Nat.lt_or_ge t (8 * i) with ht' | ht'
    · rw [h2.frame _ fun r hr hcon => by
        rw [List.mem_singleton.mp hr] at hcon
        exact Offset.disjoint b (d := BITS + t) (n := 1) (e := BITS + 8 * i) (k := 8)
          (.inl (by omega_using [ht'])) (by omega_using [hi, hB, ht']) (by omega_using [hi, hB]) _ (Region.contains_self _ _) hcon, u1.mem]
      exact h.bits t ht'
    · have := h2.bits (t - 8 * i) (by omega_using [ht])
      rw [show BITS + 8 * i + (t - 8 * i) = BITS + t by omega_using [ht']] at this
      rw [this]
      simp only [rawBit, show t / 8 = i by omega_using [ht, ht'], show t % 8 = t - 8 * i by omega_using [ht, ht']]
  · rw [r11', ofNat_ne_zero (by omega_using [])]

theorem bits_ok {sc : Addr} {s : State} (hc : Ctx b s) (h4 : s.gpr .r4 = sc)
    (hin : (⟨sc, 56⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨sc, 56⟩ ⟨b, 4096⟩) :
    WP isa bits s fun s' => Ctx b s' ∧ Rest [.r4, .r7, .r8, .r9, .r11] s s' ∧
      Frame [⟨b + BitVec.ofNat 64 BITS, 448⟩] s.mem s'.mem ∧
      Bits b (VG.Spec.X448.decodeScalar448 (bytesAt s.mem sc 56)) s'.mem := by
  have hB : BITS = 1064 := rfl
  unfold bits
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_)
  have hr2 : Rest [.r9, .r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have h0 : BInv b sc s2 0 s2 :=
    ⟨hc.of_rest hr2 (by decide), Rest.refl _ _, by rw [hr2.gpr _ (by decide), h4]; exact (BitVec.add_zero _).symm,
      by rw [u2.other _ (by decide), u1.gpr, hc.r6], by rw [u2.gpr],
      Frame.refl _ _, fun t ht => absurd ht (by omega_using [])⟩
  refine WP.seq (WP.mono (Q := BInv b sc s2 56) (WP.loop (M := isa)
    (fun m s' => ∃ i, m = 56 - i ∧ i < 56 ∧ BInv b sc s2 i s') ?_ 56 s2 ⟨0, rfl, by decide, h0⟩)
    fun s3 h3 => ?_)
  · rintro m s' ⟨i, rfl, hi, hb⟩
    refine WP.mono (bitsBody_ok (by rw [hr2.rd, hr2.wr]; exact hin) hd hi hb) fun s'' ⟨hb', hz⟩ => ?_
    by_cases h56 : i + 1 = 56
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h56], by rw [h56] at hb'; exact hb'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_using [hi, h56], 56 - (i + 1), by omega_using [hi], i + 1, rfl,
        by omega_using [hi, h56], hb'⟩
  -- The clamping.
  have hc3 := h3.ctx
  refine wp_li (by decide) fun s4 u4 => ?_
  have hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r7]) (by decide)) (by decide)
  have st : ∀ (t : State), Ctx b t → ∀ d, t.gpr .r6 + BitVec.ofNat 64 d = b + BitVec.ofNat 64 d :=
    fun t ht d => by rw [ht.r6]
  refine wp_stb (a := b + BitVec.ofNat 64 BITS) (by decide) (by decide) (st _ hc4 _)
    (hc4.inW (by omega_using [hB])) fun s5 u5 => ?_
  have hc5 : Ctx b s5 := hc4.of_rest (u5.rest []) (by decide)
  refine wp_stb (a := b + BitVec.ofNat 64 (BITS + 1)) (by decide) (by decide) (st _ hc5 _)
    (hc5.inW (by omega_using [hB])) fun s6 u6 => ?_
  have hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  refine wp_li (by decide) fun s8 u8 => ?_
  have hc8 : Ctx b s8 := hc6.of_rest (u8.rest (ws := [.r7]) (by decide)) (by decide)
  refine wp_stb (a := b + BitVec.ofNat 64 (BITS + 447)) (by decide) (by decide) (st _ hc8 _)
    (hc8.inW (by omega_using [hB])) fun s9 u9 => WP.block_nil ?_
  have v0 : (s4.gpr .r7).setWidth 8 = 0 := by rw [u4.gpr]; rfl
  have v1 : (s8.gpr .r7).setWidth 8 = 1 := by rw [u8.gpr]; rfl
  have hm9 : s9.mem = ((s3.mem.writeW (b + BitVec.ofNat 64 BITS) (0 : BitVec 8)).writeW
      (b + BitVec.ofNat 64 (BITS + 1)) (0 : BitVec 8)).writeW
      (b + BitVec.ofNat 64 (BITS + 447)) (1 : BitVec 8) := by
    rw [u9.mem, v1, u8.mem, u6.mem, u5.gpr, u5.mem, v0, u4.mem]
  have ne : ∀ a c : Nat, a < 448 → c < 448 → a ≠ c →
      b + BitVec.ofNat 64 (BITS + a) ≠ b + BitVec.ofNat 64 (BITS + c) :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega_using [hB, ha]) (by omega_using [hB, hc']) (by omega_using [hac])
  have hr9 : Rest [.r4, .r7, .r8, .r9, .r11] s s9 :=
    (hr2.mono (by decide)).trans ((h3.rest).trans ((u4.rest (by decide)).trans ((u5.rest _).trans
      ((u6.rest _).trans ((u8.rest (by decide)).trans (u9.rest _))))))
  refine ⟨hc3.of_rest ((u4.rest (ws := [.r7]) (by decide)).trans ((u5.rest _).trans ((u6.rest _).trans
    ((u8.rest (by decide)).trans (u9.rest _))))) (by decide), hr9, ?_, fun t ht => ?_⟩
  · rw [hm9, ← hm2]
    have m := List.mem_singleton_self (⟨b + BitVec.ofNat 64 BITS, 448⟩ : Region)
    refine (((h3.frame.sub fun r hr => ⟨_, m, by
        rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_using [])⟩).writeW m _ ?_).writeW m _ ?_).writeW
      m _ ?_ <;> exact Offset.contains _ (n := 8 / 8) (by omega_using []) (by omega_using []) (by omega_using [hB])
  · have hbit := VG.Proof.X448.scalar_bit (VG.Proof.X448.length_bytesAt s.mem sc 56) ht
    rw [getD_bytesAt _ _ (by omega_using [ht])] at hbit
    rw [hbit, hm9]
    simp only [VG.WriteBytes.writeW8_apply]
    by_cases t447 : t = 447
    · subst t447; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega_using [ht]) (by omega_using []) t447)]
    by_cases t1 : t = 1
    · subst t1; rw [iteT rfl]; rfl
    rw [iteF (ne _ _ (by omega_using [ht]) (by omega_using []) t1)]
    by_cases t0 : t = 0
    · subst t0; rw [iteT (by rfl)]; rfl
    rw [iteF (show b + BitVec.ofNat 64 (BITS + t) ≠ b + BitVec.ofNat 64 BITS from
      fun e => ne t 0 (by omega_using [ht]) (by omega_using []) t0 (by rw [e]; rfl)), h3.bits t (by omega_using [ht]), hm2,
      iteF (show ¬ t < 2 by omega_using [t1, t0]), iteF t447]
    rfl

end

end VG.Proof.X448.PPC64LE
