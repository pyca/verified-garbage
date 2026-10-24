module

public import VerifiedGarbage.Impl.Ed448.PPC64LE.ScalarBase
import VerifiedGarbage.Proof.X448.PPC64LE.Field
public import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.Ed448.Scalar
import VerifiedGarbage.Proof.X448.PPC64LE.Invert
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.X448.PPC64LE
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field

/-!
# Ed448 on PPC64LE: the bits of the scalar

`baseBits` stores bit `t` of the 456-bit scalar at byte `BITS + t` of the
working space (`baseBits_ok`), with X448's code for a byte (`bitsBody`) and
its proof (`Proof/X448/PPC64LE/Bits.lean`), for 57 bytes and no clamping.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Impl.Ed448.PPC64LE VG.Proof.X448.PPC64LE
open VG.Proof.X25519.PPC64LE hiding V FS V_lt pass_ok limb_frame
open VG.Spec.Ed448 (bytesAt decodeLE)

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

theorem bitStep_ok {i j : Nat} (hi : i < 57) (hj : j < 8) {x : Nat} {s1 s : State}
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
  r11 : s.gpr .r11 = BitVec.ofNat 64 (57 - i)
  frame : Frame [⟨b + BitVec.ofNat 64 BITS, 8 * i⟩] s0.mem s.mem
  bits : ∀ t < 8 * i, s.mem (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 (rawBit s0.mem sc t)

theorem bitsBody_ok {sc : Addr} {s0 : State}
    (hin : (⟨sc, 57⟩ : Region) ∈ s0.rd ++ s0.wr)
    (hd : Region.Disjoint ⟨sc, 57⟩ ⟨b, 4096⟩) {i : Nat} (hi : i < 57) {s : State}
    (h : BInv b sc s0 i s) :
    WP isa (.block bitsBody) s fun s' => BInv b sc s0 (i + 1) s' ∧
      (s'.gpr .r11 != 0) = decide (57 - (i + 1) ≠ 0) := by
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
  have r11' : s5.gpr .r11 = BitVec.ofNat 64 (57 - (i + 1)) := by
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

/-- The bits of the scalar `k` in `BITS`. -/
def Bits (b : Addr) (k : Nat) (m : Mem) : Prop :=
  ∀ t < 456, m (b + BitVec.ofNat 64 (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1)

theorem baseBits_ok {sc : Addr} {s : State} (hc : Ctx b s) (h4 : s.gpr .r4 = sc)
    (hin : (⟨sc, 57⟩ : Region) ∈ s.rd ++ s.wr)
    (hd : Region.Disjoint ⟨sc, 57⟩ ⟨b, 4096⟩) :
    WP isa baseBits s fun s' => Ctx b s' ∧ Rest [.r4, .r7, .r8, .r9, .r11] s s' ∧
      Frame [⟨b + BitVec.ofNat 64 BITS, 456⟩] s.mem s'.mem ∧
      Bits b (decodeLE (bytesAt s.mem sc 57)) s'.mem := by
  have hB : BITS = 1064 := rfl
  unfold baseBits
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => wp_li (by decide) fun s2 u2 => WP.block_nil ?_)
  have hr2 : Rest [.r9, .r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  have hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  have h0 : BInv b sc s2 0 s2 :=
    ⟨hc.of_rest hr2 (by decide), Rest.refl _ _, by rw [hr2.gpr _ (by decide), h4]; exact (BitVec.add_zero _).symm,
      by rw [u2.other _ (by decide), u1.gpr, hc.r6], by rw [u2.gpr],
      Frame.refl _ _, fun t ht => absurd ht (by omega_using [])⟩
  refine WP.mono (Q := BInv b sc s2 57) (WP.loop (M := isa)
    (fun m s' => ∃ i, m = 57 - i ∧ i < 57 ∧ BInv b sc s2 i s') ?_ 57 s2 ⟨0, rfl, by decide, h0⟩)
    fun s3 h3 => ⟨h3.ctx, (hr2.mono (ws' := [.r4, .r7, .r8, .r9, .r11]) (by decide)).trans h3.rest, ?_, fun t ht => ?_⟩
  · rintro m s' ⟨i, rfl, hi, hb⟩
    refine WP.mono (bitsBody_ok (by rw [hr2.rd, hr2.wr]; exact hin) hd hi hb) fun s'' ⟨hb', hz⟩ => ?_
    by_cases h57 : i + 1 = 57
    · exact .inl ⟨by rw [eval_nonzero, hz]; simp [h57], by rw [h57] at hb'; exact hb'⟩
    · exact .inr ⟨by rw [eval_nonzero, hz]; simp; omega_using [hi, h57], 57 - (i + 1), by omega_using [hi], i + 1, rfl,
        by omega_using [hi, h57], hb'⟩
  · rw [← hm2]; exact h3.frame
  · rw [h3.bits t (by omega_using [ht]), hm2, rawBit, Proof.Ed448.scalar_bit s.mem sc ht]

end

end VG.Proof.Ed448.PPC64LE
