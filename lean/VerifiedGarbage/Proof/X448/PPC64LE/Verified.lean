module

public import VerifiedGarbage.Proof.X448.Contract
public import VerifiedGarbage.Proof.X448.PPC64LE.Invert
public import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.X448.PPC64LE.Freeze
import VerifiedGarbage.Proof.X448.PPC64LE.Slots
import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.X448.PPC64LE.CT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.PPC64LE.Untouched
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint

/-! ### `X448.PPC64LE.Main`, which only this module used -/

section

/-! ### `X448.PPC64LE.Bits`, which only this module used -/

section

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
    show (2 : Nat) ^ 64 = 2 ^ (j + 1) * 2 ^ (63 - j) by rw [← Nat.pow_add]; congr 1; omega_using [hj],
    Nat.mul_mod_mul_right, show (2 : Nat) ^ 63 = 2 ^ j * 2 ^ (63 - j) by rw [← Nat.pow_add]; congr 1; omega_using [hj],
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
  obtain e7 : (s.gpr .r7).toNat = x := by rw [h.rest.gpr _ (by decide), h7]
  obtain e9 : s.gpr .r9 = b + BitVec.ofNat 64 (8 * i) := by rw [h.rest.gpr _ (by decide), h9]
  refine wp_lsl (by omega_using []) fun s2 u2 => wp_lsr (by decide) fun s3 u3 => ?_
  obtain e8 : (s3.gpr .r8).toNat = (x >>> j) &&& 1 := by
    rw [u3.gpr, u2.gpr, bit_shift _ (by omega_using [hj]), e7]
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
    · rw [iteF (Offset.add_ofNat_ne _ (by omega_arith) (by omega_using [hi, hj, hB]) (by omega_using [hj']))]; exact h.bits j' hj'
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
  obtain hc1 : Ctx b s1 := h.ctx.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide)
  -- The byte, as in `s0`.
  obtain hx : (s1.gpr .r7).toNat = (s0.mem (sc + BitVec.ofNat 64 i)).toNat := by
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
  obtain hr5 : Rest [.r4, .r7, .r8, .r9, .r11] s s5 :=
    (u1.rest (by decide)).trans ((h2.rest.mono (by decide)).trans ((u3.rest (by decide)).trans
      ((u4.rest (by decide)).trans (u5.rest (by decide)))))
  obtain hm5 : s5.mem = s2.mem := by rw [u5.mem, u4.mem, u3.mem]
  obtain r11' : s5.gpr .r11 = BitVec.ofNat 64 (56 - (i + 1)) := by
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
  obtain hr2 : Rest [.r9, .r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  obtain h0 : BInv b sc s2 0 s2 :=
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
  obtain hc4 : Ctx b s4 := hc3.of_rest (u4.rest (ws := [.r7]) (by decide)) (by decide)
  obtain st : ∀ (t : State), Ctx b t → ∀ d, t.gpr .r6 + BitVec.ofNat 64 d = b + BitVec.ofNat 64 d :=
    fun t ht d => by rw [ht.r6]
  refine wp_stb (a := b + BitVec.ofNat 64 BITS) (by decide) (by decide) (st _ hc4 _)
    (hc4.inW (by omega_using [hB])) fun s5 u5 => ?_
  obtain hc5 : Ctx b s5 := hc4.of_rest (u5.rest []) (by decide)
  refine wp_stb (a := b + BitVec.ofNat 64 (BITS + 1)) (by decide) (by decide) (st _ hc5 _)
    (hc5.inW (by omega_using [hB])) fun s6 u6 => ?_
  obtain hc6 : Ctx b s6 := hc5.of_rest (u6.rest []) (by decide)
  refine wp_li (by decide) fun s8 u8 => ?_
  obtain hc8 : Ctx b s8 := hc6.of_rest (u8.rest (ws := [.r7]) (by decide)) (by decide)
  refine wp_stb (a := b + BitVec.ofNat 64 (BITS + 447)) (by decide) (by decide) (st _ hc8 _)
    (hc8.inW (by omega_using [hB])) fun s9 u9 => WP.block_nil ?_
  obtain v0 : (s4.gpr .r7).setWidth 8 = 0 := by rw [u4.gpr]; rfl
  obtain v1 : (s8.gpr .r7).setWidth 8 = 1 := by rw [u8.gpr]; rfl
  obtain hm9 : s9.mem = ((s3.mem.writeW (b + BitVec.ofNat 64 BITS) (0 : BitVec 8)).writeW
      (b + BitVec.ofNat 64 (BITS + 1)) (0 : BitVec 8)).writeW
      (b + BitVec.ofNat 64 (BITS + 447)) (1 : BitVec 8) := by
    rw [u9.mem, v1, u8.mem, u6.mem, u5.gpr, u5.mem, v0, u4.mem]
  obtain ne : ∀ a c : Nat, a < 448 → c < 448 → a ≠ c →
      b + BitVec.ofNat 64 (BITS + a) ≠ b + BitVec.ofNat 64 (BITS + c) :=
    fun a c ha hc' hac => Offset.add_ofNat_ne _ (by omega_using [hB, ha]) (by omega_using [hB, hc']) (by omega_using [hac])
  obtain hr9 : Rest [.r4, .r7, .r8, .r9, .r11] s s9 :=
    (hr2.mono (by decide)).trans ((h3.rest).trans ((u4.rest (by decide)).trans ((u5.rest _).trans
      ((u6.rest _).trans ((u8.rest (by decide)).trans (u9.rest _))))))
  refine ⟨hc3.of_rest ((u4.rest (ws := [.r7]) (by decide)).trans ((u5.rest _).trans ((u6.rest _).trans
    ((u8.rest (by decide)).trans (u9.rest _))))) (by decide), hr9, ?_, fun t ht => ?_⟩
  · rw [hm9, ← hm2]
    obtain m := List.mem_singleton_self (⟨b + BitVec.ofNat 64 BITS, 448⟩ : Region)
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

end

end


/-!
# X448 on PPC64LE: the whole function

`vg_x448` writes `X448(k, u)` to `out`, and restores `r15`–`r31`, which it
saves at `NV` for `mul` (`x448_correct`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.X448 (P Fe bytesAt)
open VG.Proof.X25519 (leBytes)
open VG.Proof.X448 (toFe ladderAfter ladderAfter_swap_le)
open VG.PPC64LE.Spill (saveMem Saved saveMem_saved saveMem_frame_base)

/-- `vg_x448(out = r3, scalar = r4, point = r5, scratch = r6)`. -/
def x448PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 56⟩
    let sc : Region := ⟨s.gpr .r4, 56⟩
    let pt : Region := ⟨s.gpr .r5, 56⟩
    let ws : Region := ⟨s.gpr .r6, 8192⟩
    s.rd = [sc, pt] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint pt ∧ out.Disjoint ws ∧
      sc.Disjoint ws ∧ pt.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .r3) 56 =
    VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .r4) 56) (bytesAt s.mem (s.gpr .r5) 56)
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

/-- `vg_x448_base(out = r3, scalar = r4, scratch = r5)`. -/
def x448BasePPC64LE : Contract PPC64LE.isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, 56⟩
    let sc : Region := ⟨s.gpr .r4, 56⟩
    let ws : Region := ⟨s.gpr .r5, 8192⟩
    s.rd = [sc] ∧ s.wr = [out, ws] ∧ out.Disjoint sc ∧ out.Disjoint ws ∧ sc.Disjoint ws
  post s s' := bytesAt s'.mem (s.gpr .r3) 56 =
    VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .r4) 56) VG.Spec.X448.basePoint
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.sp = s₂.sp

theorem XPre.of {s : State} (h : x448PPC64LE.pre s) : XPre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

section
variable {b : Addr}

theorem lastSwap_ok {s : State} (hc : Ctx b s) {sw : Nat} (hsw : sw ≤ 1)
    (h0 : s.gpr .r0 = BitVec.ofNat 64 sw) {v : Nat → Fe} (hS : SlotsOk s.mem b LQ v) :
    WP isa (.block lastSwap) s fun s' => Stp b s s' ∧ Ctx b s' ∧
      SlotsOk s'.mem b LQ (swapV Z2 Z3 sw (swapV X2 X3 sw v)) := by
  simp only [lastSwap, mask, List.cons_append, List.nil_append]
  refine wp_li (by decide) fun s1 u1 => wp_sub fun s2 u2 => ?_
  obtain hr2 : Rest [.r11] s s2 := (u1.rest (by decide)).trans (u2.rest (by decide))
  obtain hc2 : Ctx b s2 := hc.of_rest hr2 (by decide)
  obtain e11 : s2.gpr .r11 = 0 - BitVec.ofNat 64 sw := by
    rw [u2.gpr, u1.gpr, u1.other _ (by decide), h0]; rfl
  obtain hm2 : s2.mem = s.mem := by rw [u2.mem, u1.mem]
  refine WP.append (cswapS (v := v) (qs := LQ) (by decide) (by decide) (by decide) (by decide) (by decide) hc2
    hsw e11 (by rw [hm2]; exact hS)) fun s3 ⟨hr3, hf3, hS3⟩ => ?_
  obtain hc3 : Ctx b s3 := hc2.of_rest hr3 (by decide)
  refine WP.mono (cswapS (by decide) (by decide) (by decide) (by decide) (by decide) hc3 hsw
    (by rw [hr3.gpr _ (by decide), e11]) hS3) fun s4 ⟨hr4, hf4, hS4⟩ =>
    ⟨⟨(hr2.mono (by decide)).trans ((hr3.mono (by decide)).trans (hr4.mono (by decide))),
      by rw [← hm2]; exact hf3.trans hf4⟩, hc3.of_rest hr4 (by decide), hS4⟩

/-- The slots stay through a write above `BITS`. -/
theorem SlotsOk.above {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m b qs v)
    (hq : (qs.all fun q => q + 56 ≤ BITS) = true) {d n : Nat} (hd : BITS ≤ d) (hdn : d + n ≤ 4096)
    (hf : Frame [⟨b + BitVec.ofNat 64 d, n⟩] m m') : SlotsOk m' b qs v := by
  intro q hq'
  obtain h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1064 := rfl
  obtain e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [hd, h, hk])) (by omega_using [h, hB, hk]) (by omega_using [hdn])
  rw [FS, V, val32_congr e]; exact hS q hq'

/-- The slots stay through a write of `BITS`. -/
theorem SlotsOk.bits {m m' : Mem} {qs : List Nat} {v : Nat → Fe} (hS : SlotsOk m b qs v)
    (hq : (qs.all fun q => q + 56 ≤ BITS) = true)
    (hf : Frame [⟨b + BitVec.ofNat 64 BITS, 448⟩] m m') : SlotsOk m' b qs v := by
  intro q hq'
  obtain h := List.all_eq_true.mp hq q hq'
  simp only [decide_eq_true_eq] at h
  have hB : BITS = 1064 := rfl
  obtain e := limb_frame (o := q) hf fun r hr k hk => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ (.inl (by omega_using [h, hk])) (by omega_using [h, hB, hk]) (by omega_using [hB])
  rw [FS, V, val32_congr e]; exact hS q hq'

end

theorem bytesAt_frame {m m' : Mem} {rs : List Region} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 56⟩ r) : bytesAt m' p 56 = bytesAt m p 56 := by
  simp only [bytesAt]
  refine List.map_congr_left fun i hi => ?_
  obtain hi := List.mem_range.mp hi
  exact hf _ fun r hr hc => hd r hr _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) hc

/-- The code after the setup, from the ladder's initial state for the
u-coordinate `pb` in the working space at `r6` of `s`: it saves `r15`–`r31`
at `NV`, and restores them before the final reduction. -/
theorem afterSetup_correct {s s1 : State} {pb : List Byte}
    (hsc_in : (⟨s.gpr .r4, 56⟩ : Region) ∈ s.rd ++ s.wr) (hout : (⟨s.gpr .r3, 56⟩ : Region) ∈ s.wr)
    (sc_ws : Region.Disjoint ⟨s.gpr .r4, 56⟩ ⟨s.gpr .r6, 8192⟩)
    (out_ws : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r6, 8192⟩)
    (hc1 : Ctx (s.gpr .r6) s1) (hf1 : Frame [⟨s.gpr .r6, 8192⟩] s.mem s1.mem)
    (hS1 : SlotsOk s1.mem (s.gpr .r6) LQ (ladV (toFe (VG.Spec.X448.decodeUCoordinate pb))
      (VG.Proof.X448.init (toFe (VG.Spec.X448.decodeUCoordinate pb)))))
    (hr1 : Rest [.r5, .r7, .r8] s s1) :
    WP isa afterSetup s1 fun s' =>
      bytesAt s'.mem (s.gpr .r3) 56 = VG.Spec.X448.x448 (bytesAt s.mem (s.gpr .r4) 56) pb ∧
      ∀ i < 17, s'.gpr (nvR i) = s1.gpr (nvR i) := by
  have hB : BITS = 1064 := rfl
  have hNV : NV = 1512 := rfl
  have hA := ACC_eq
  unfold afterSetup
  -- `r14`–`r31` saved at `NV`.
  rw [← List.append_nil (stdsAt NV (slotsOf nvR 17))]
  refine WP.seq (stdsAt_ok (l := slotsOf nvR 17) (by decide) (slotsOf_fit (by decide) (by decide)) hc1
    fun s1' g1' rd1' wr1' sp1' mem1' => WP.block_nil ?_)
  obtain hc1' : Ctx (s.gpr .r6) s1' := ⟨by rw [g1']; exact hc1.r6, by rw [wr1']; exact hc1.wr⟩
  obtain hfNV : Frame [⟨s.gpr .r6 + BitVec.ofNat 64 NV, 136⟩] s1.mem s1'.mem := by
    rw [mem1']; exact saveMem_frame_base (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega)
      (by decide) _ _ _
  obtain hsv1 : Saved (s.gpr .r6 + BitVec.ofNat 64 NV) s1.gpr (slotsOf nvR 17) s1'.mem := by
    rw [mem1']; exact saveMem_saved (by decide) _ _ _
  obtain hS1' := hS1.above (by decide) (by rw [hB]; decide) (by omega_using [hNV]) hfNV
  obtain hf1' : Frame [⟨s.gpr .r6, 8192⟩] s.mem s1'.mem := hf1.trans (hfNV.sub fun r hr =>
    ⟨_, List.mem_singleton_self _, by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_using [hNV])⟩)
  obtain hr1' : Rest [.r5, .r7, .r8] s s1' := ⟨fun r hr => by rw [congrFun g1']; exact hr1.gpr r hr,
    by rw [rd1', hr1.rd], by rw [wr1', hr1.wr], by rw [sp1', hr1.sp]⟩
  refine WP.seq (WP.mono (bits_ok hc1' (hr1'.gpr .r4 (by decide)) (by rw [hr1'.rd, hr1'.wr]; exact hsc_in)
    (disj4096 sc_ws)) fun s2 ⟨hc2, hr2, hf2, hb2⟩ => ?_)
  obtain hS2 := hS1'.bits (by decide) hf2
  refine WP.seq (WP.mono (ladder_ok hc2 hb2 hS2) fun s3 ⟨hst3, hc3, h0, hS3⟩ => ?_)
  refine WP.seq (WP.mono (lastSwap_ok hc3 (ladderAfter_swap_le _ _ (by decide)) h0 hS3)
    fun s4 ⟨hst4, hc4, hS4⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok hc4 (hS4.mono (by decide)) rfl) fun s5 ⟨hst5, hc5, hS5⟩ => ?_)
  refine WP.seq (WP.mono (mulS (o := X2) (x := X2) (y := R) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hc5 hS5) fun s6 ⟨hr6, hf6, hS6⟩ => ?_)
  -- The registers and regions along the way.
  obtain hst6 : StpW work (s.gpr .r6) s2 s6 :=
    hst3.trans ((hst4.mono (by decide)).trans (hst5.trans ⟨hr6.mono (by decide), hf6⟩))
  obtain hc6 : Ctx (s.gpr .r6) s6 := hc5.of_rest hr6 (by decide)
  -- `r14`–`r31` restored.
  obtain hsv6 : Saved (s.gpr .r6 + BitVec.ofNat 64 NV) s1.gpr (slotsOf nvR 17) s6.mem := by
    obtain h2 := hsv1.frame_in (lo := 0) (n := 136) (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega)
      hf2 (fun r hr => by
        rw [List.mem_singleton.mp hr]; simpa using Offset.disjoint (s.gpr .r6) (d := NV) (n := 136)
          (e := BITS) (k := 448) (.inr (by omega_using [hB, hNV])) (by omega_using [hNV]) (by omega_using [hB]))
    exact h2.frame_in (lo := 0) (n := 136) (fun p hp => by obtain ⟨i, hi, rfl⟩ := slotsOf_mem hp; omega)
      hst6.frame (fun r hr => by
        rw [List.mem_singleton.mp hr]; simpa using Offset.disjoint_base (s.gpr .r6) (d := NV) (n := 136)
          (k := ACC + 112) (by omega_using [hNV, hA]) (by omega_using [hNV]))
  refine ldsAt_ok (l := slotsOf nvR 17) (by decide) (slotsOf_fit (by decide) (by decide)) (by decide)
    (by decide) hc6 fun s7 hc7 r7 m7 _ v7 => ?_
  obtain nv7 : ∀ i < 17, s7.gpr (nvR i) = s1.gpr (nvR i) := fun i hi => by
    rw [v7 (nvR i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)]
    exact hsv6 (nvR i, 8 * i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  obtain h3' : s7.gpr .r3 = s.gpr .r3 := by
    rw [r7.gpr _ (by decide), hst6.rest.gpr _ (by decide), hr2.gpr _ (by decide), hr1'.gpr _ (by decide)]
  obtain hwr7 : s7.wr = s.wr := by rw [r7.wr, hst6.rest.wr, hr2.wr, hr1'.wr]
  refine WP.mono (freeze_ok hc7 h3'
    (fun k hk => in_base (len := 56) (by rw [hwr7]; exact hout) (by omega_using [hk]) (by omega_using [hk])) (disj4096 out_ws).symm)
    fun s8 ⟨hbytes, hr8, _⟩ => ⟨?_, fun i hi => by
      rw [hr8.gpr _ (by revert i; decide), nv7 i hi]⟩
  -- The result.
  rw [hbytes, m7, VG.Proof.X448.x448_eq]
  -- The scalar, as read by `bits`.
  obtain hk : bytesAt s1'.mem (s.gpr .r4) 56 = bytesAt s.mem (s.gpr .r4) 56 :=
    bytesAt_frame hf1' fun r hr => by rw [List.mem_singleton.mp hr]; exact sc_ws
  rw [hk] at hS3 h0 hS4 hS5 hS6
  obtain e6 : FS s6.mem (s.gpr .r6) X2 = _ := hS6 X2 (by decide)
  rw [← VG.Proof.X448.toFe_val, ← VG.Proof.X448.encodeUCoordinate_eq]
  change VG.Spec.X448.encodeUCoordinate (FS s6.mem (s.gpr .r6) X2) = _
  rw [e6]
  simp only [upd, swapV, ladV, sel, iteT, VG.Proof.X448.invert_eq, VG.Proof.X448.pow_pw, cswap_fst,
    X1, X2, Z2, X3, Z3, R, Nat.reduceEqDiff, ite_false]

theorem x448_correct {s : State} (hp : XPre s) :
    WP isa x448 s fun s' => x448PPC64LE.post s s' ∧ ∀ i < 17, s'.gpr (nvR i) = s.gpr (nvR i) := by
  unfold x448
  exact WP.seq (WP.mono (setup_ok hp) fun s1 ⟨hc1, hf1, hS1, hr1⟩ =>
    WP.mono (afterSetup_correct (by rw [hp.rd]; simp) (by rw [hp.wr]; simp) hp.sc_ws hp.out_ws hc1 hf1 hS1 hr1)
      fun s' ⟨h1, h2⟩ => ⟨h1, fun i hi => by rw [h2 i hi, hr1.gpr _ (by revert i; decide)]⟩)

/-- `vg_x448_base`'s precondition, by field. -/
structure BPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .r4, 56⟩]
  wr : s.wr = [⟨s.gpr .r3, 56⟩, ⟨s.gpr .r5, 8192⟩]
  out_sc : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r4, 56⟩
  out_ws : Region.Disjoint ⟨s.gpr .r3, 56⟩ ⟨s.gpr .r5, 8192⟩
  sc_ws : Region.Disjoint ⟨s.gpr .r4, 56⟩ ⟨s.gpr .r5, 8192⟩

theorem BPre.of {s : State} (h : x448BasePPC64LE.pre s) : BPre s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem x448Base_correct {s : State} (hp : BPre s) :
    WP isa x448Base s fun s' => x448BasePPC64LE.post s s' ∧ ∀ i < 17, s'.gpr (nvR i) = s.gpr (nvR i) := by
  unfold x448Base
  refine WP.seq ?_
  rw [List.singleton_append]
  refine wp_addi (imm := 0) (by decide) (by decide) fun s0 u0 => ?_
  obtain e0 : s0.gpr .r6 = s.gpr .r5 := by rw [u0.gpr]; exact BitVec.add_zero _
  obtain a3 : s0.gpr .r3 = s.gpr .r3 := u0.other _ (by decide)
  obtain a4 : s0.gpr .r4 = s.gpr .r4 := u0.other _ (by decide)
  refine WP.mono (setupBase_ok (by rw [e0, u0.wr, hp.wr]; simp)) fun s1 ⟨hc1, hf1, hS1, hr1⟩ => ?_
  refine WP.mono (afterSetup_correct (s := s0) (by rw [a4, u0.rd, hp.rd]; simp) (by rw [a3, u0.wr, hp.wr]; simp)
    (by rw [a4, e0]; exact hp.sc_ws) (by rw [a3, e0]; exact hp.out_ws) hc1 hf1 hS1 hr1) fun s' ⟨h, hnv⟩ =>
      ⟨?_, fun i hi => by rw [hnv i hi, hr1.gpr _ (by revert i; decide), u0.other _ (by revert i; decide)]⟩
  show bytesAt s'.mem (s.gpr .r3) 56 = _
  rw [← a3, h, a4, u0.mem]

end VG.Proof.X448.PPC64LE

end

end


/-!
# X448 on PPC64LE: verified

`vg_x448` meets the shared contract of `Spec/X448/Contract.lean`: the
proof against `x448PPC64LE`, which it implies, and a state satisfying it.
The code restores the nonvolatile registers `r15`–`r31` it uses
(`x448_correct`), never writes `r2`, `r14` or the link register, and calls no
function, so the ABI's obligations hold of every execution.
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE

theorem x448_ok (s : State) (hs : x448PPC64LE.pre s) :
    ∃ t s', Exec isa Impl.X448.PPC64LE.x448 s t s' ∧ abiPreserved s s' ∧ x448PPC64LE.post s s' := by
  obtain ⟨t, s', he, h, hnv⟩ := x448_correct (XPre.of hs)
  obtain hd : ∀ r ∈ [Reg.r2, .r14], ∀ i ∈ instrs Impl.X448.PPC64LE.x448, dstOf i ≠ some r :=
    nv_of_avoids (by decide +kernel)
  obtain hpre : ∀ r ∈ preserved, r ∈ [Reg.r2, .r14] ∨ ∃ i < 17, Impl.X448.PPC64LE.nvR i = r := by decide
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
  rcases hpre r hr with h2 | ⟨i, hi, rfl⟩
  · exact Exec.gpr (hd _ h2) he (.inl (by decide +kernel))
  · exact hnv i hi

theorem x448_ct' : ConstantTime isa x448PPC64LE.pre x448PPC64LE.pub Impl.X448.PPC64LE.x448 :=
  x448_ct fun _ _ _ _ ⟨h3, h4, h5, h6, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying the precondition. -/
def x448Sat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 56⟩, ⟨0x3000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448_verified :
    Verified PPC64LE.target Impl.X448.PPC64LE.x448 (Proof.X448.x448Contract PPC64LE.abi) :=
  Verified.of_correct x448_ok x448_ct' (by
    contract_implies [Proof.X448.x448Contract, Proof.X448.x448Sig, Proof.X448.PPC64LE.x448PPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [Proof.X448.PPC64LE.x448Sat] using Proof.X448.PPC64LE.x448Sat)

theorem x448Base_ok (s : State) (hs : x448BasePPC64LE.pre s) :
    ∃ t s', Exec isa Impl.X448.PPC64LE.x448Base s t s' ∧ abiPreserved s s' ∧
      x448BasePPC64LE.post s s' := by
  obtain ⟨t, s', he, h, hnv⟩ := x448Base_correct (BPre.of hs)
  obtain hd : ∀ r ∈ [Reg.r2, .r14], ∀ i ∈ instrs Impl.X448.PPC64LE.x448Base, dstOf i ≠ some r :=
    nv_of_avoids (by decide +kernel)
  obtain hpre : ∀ r ∈ preserved, r ∈ [Reg.r2, .r14] ∨ ∃ i < 17, Impl.X448.PPC64LE.nvR i = r := by decide
  refine ⟨t, s', he, ⟨fun r hr => ?_, Exec.sp he,
    Exec.lr he (by decide +kernel) (by rw [← Code.allInstrs_eq]; decide +kernel)⟩, h⟩
  rcases hpre r hr with h2 | ⟨i, hi, rfl⟩
  · exact Exec.gpr (hd _ h2) he (.inl (by decide +kernel))
  · exact hnv i hi

theorem x448Base_ct' : ConstantTime isa x448BasePPC64LE.pre x448BasePPC64LE.pub
    Impl.X448.PPC64LE.x448Base :=
  x448Base_ct fun _ _ _ _ ⟨h3, h4, h5, hsp⟩ => ⟨hsp, fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption⟩

/-- A state satisfying `vg_x448_base`'s precondition. -/
def x448BaseSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x4000 | _ => 0
  lr := 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x2000, 56⟩]
  wr := [⟨0x1000, 56⟩, ⟨0x4000, 8192⟩]

theorem x448Base_verified :
    Verified PPC64LE.target Impl.X448.PPC64LE.x448Base (Spec.X448.x448BaseContract PPC64LE.abi) :=
  Verified.of_correct x448Base_ok x448Base_ct' (by
    contract_implies [Spec.X448.x448BaseContract, Spec.X448.x448BaseSig, Proof.X448.PPC64LE.x448BasePPC64LE,
      PPC64LE.abi, PPC64LE.argRegs] [Proof.X448.PPC64LE.x448BaseSat] using Proof.X448.PPC64LE.x448BaseSat)

end VG.Proof.X448.PPC64LE
