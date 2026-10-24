module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
public import VerifiedGarbage.Spec.Ffdh
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.Mem
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Mont.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubFn

/-!
# An FFDH parameter candidate on PPC64LE: a modulus's working space

`phase_ok`: for the modulus of `mb` bits (`bits − 1` for q, `bits` for p),
`w = ⌈mb / 64⌉`, the header (`Ph`: `mb`, `⌈mb / 8⌉`, `w`, the arrays'
addresses and size, the number of checks and the top word's mask) and the
registers of the arrays.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

/-- The working space of a modulus of `mb` bits: `w = ⌈mb / 64⌉`. -/
abbrev wOf (mb : Nat) : Nat := (mb + 63) / 64

/-- The header and the registers after `phase`. -/
structure Ph (p : PP) (mb : Nat) (s : State) : Prop where
  r10 : s.gpr .r10 = off p.B (slot (wOf mb) 0)
  r11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wOf mb)
  r29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wOf mb + 2))
  mbW : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb
  kW : word s.mem p.B (8 * hK) = BitVec.ofNat 64 ((mb + 7) / 8)
  wW : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)
  strideW : word s.mem p.B (8 * hStride) = BitVec.ofNat 64 (8 * (wOf mb + 2))
  arrW : ∀ j < 8, word s.mem p.B (8 * (8 + j)) = off p.B (slot (wOf mb) j)
  checksW : word s.mem p.B (8 * hChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb)
  topW : word s.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1)

/-- The bit length of the modulus: `bits − 1` for q, `bits` for p. -/
abbrev mbOf (p : PP) (q : Bool) : Nat := if q then p.bits - 1 else p.bits

theorem add_shr (x a k : Nat) (h : x + a < 2 ^ 64) :
    (BitVec.ofNat 64 x + BitVec.ofNat 64 a) >>> k = BitVec.ofNat 64 ((x + a) / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.add_mod_mod, Nat.mod_add_mod, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)]

theorem checks_eq {mb : Nat} (h : mb ≤ 8192) :
    BitVec.ofNat 64 128 - ((BitVec.ofNat 64 mb - BitVec.ofNat 64 2049) >>> 63) <<< 6 =
      BitVec.ofNat 64 (Spec.Ffdh.primeChecks mb) := by
  unfold Spec.Ffdh.primeChecks
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  split
  · have e : (2 ^ 64 - 2049 % 2 ^ 64 + mb % 2 ^ 64) % 2 ^ 64 / 2 ^ 63 = 1 := by
      rw [Nat.mod_eq_of_lt (show 2049 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show mb < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
    rw [e]; rfl
  · have e : (2 ^ 64 - 2049 % 2 ^ 64 + mb % 2 ^ 64) % 2 ^ 64 / 2 ^ 63 = 0 := by
      rw [Nat.mod_eq_of_lt (show 2049 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show mb < 2 ^ 64 by omega)]
      omega
    rw [e]; rfl

/-- The registers `phaseHead` writes. -/
def phRegs : List Reg := [.r3, .r4, .r5, .r6, .r10, .r11, .r29]

/-- The ranges `phaseHead` changes: words 6–15, 21, 27, 28 and 31. -/
def phRanges : List (Nat × Nat) := [(48, 80), (168, 8), (216, 16), (248, 8)]

theorem phaseHead_ok {p : PP} {s : State} (h : St p s) (q : Bool) :
    WP isa (.block (phaseHead q)) s fun t =>
      (t.gpr .r10 = off p.B (slot (wOf (mbOf p q)) 0) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wOf (mbOf p q)) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (wOf (mbOf p q) + 2)) ∧
        word t.mem p.B (8 * hMb) = BitVec.ofNat 64 (mbOf p q) ∧
        word t.mem p.B (8 * hK) = BitVec.ofNat 64 ((mbOf p q + 7) / 8) ∧
        word t.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf (mbOf p q)) ∧
        word t.mem p.B (8 * hStride) = BitVec.ofNat 64 (8 * (wOf (mbOf p q) + 2)) ∧
        (∀ j < 8, word t.mem p.B (8 * (8 + j)) = off p.B (slot (wOf (mbOf p q)) j)) ∧
        word t.mem p.B (8 * hChecks) = BitVec.ofNat 64 (Spec.Ffdh.primeChecks (mbOf p q)) ∧
        Frm p.B phRanges s.mem t.mem) ∧ Keep phRegs s t := by
  have hb1 := h.dims.b1
  have hb2 := h.dims.b2
  cases q <;> refine WP.keep _ ?_ (by decide) <;> unfold phaseHead <;>
    simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil, List.flatMap, List.range, List.range.loop,
      List.map, List.flatten, List.cons_append, List.nil_append, List.append_eq, ldh, sth, hBits, hMb, hK, hW, hStride,
      hChecks, hdrBytes, mbOf]
  · have ew : (BitVec.ofNat 64 p.bits + 63#64) >>> 6 = BitVec.ofNat 64 (wOf p.bits) := add_shr _ _ _ (by omega)
    have ek : (BitVec.ofNat 64 p.bits + 7#64) >>> 3 = BitVec.ofNat 64 ((p.bits + 7) / 8) := add_shr _ _ _ (by omega)
    have e29 : BitVec.ofNat 64 (8 * wOf p.bits) + 16#64 = BitVec.ofNat 64 (8 * (wOf p.bits + 2)) := by
      rw [BitVec.ofNat_add_ofNat]; congr 1
    prun [h.r31, h.ld (d := 40) (by decide), h.args.bits', h.st (d := 248) (by decide), h.st (d := 216) (by decide),
      h.st (d := 48) (by decide), h.st (d := 224) (by decide), h.st (d := 64) (by decide), h.st (d := 72) (by decide),
      h.st (d := 80) (by decide), h.st (d := 88) (by decide), h.st (d := 96) (by decide), h.st (d := 104) (by decide),
      h.st (d := 112) (by decide), h.st (d := 120) (by decide), h.st (d := 168) (by decide), ew, ek,
      Pub.ofNat_shl3, Pub.ofNat_shl1, e29, checks_eq hb2]
    refine ⟨by simp [off, slot, hdrBytes], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals simp (disch := decide) only [word, off, rw_off, rw_self]
    · intro j hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
      all_goals first
        | (simp (disch := decide) only [rw_off, rw_self, Nat.reduceMul, Nat.reduceAdd]
           congr 1; simp only [slot, hdrBytes]; omega)
        | omega
    · iterate 13 refine frm_writeW ?_ _ (by decide) (by decide)
      exact Frm.refl _ _ _
  · have e1 : BitVec.ofNat 64 p.bits - 1#64 = BitVec.ofNat 64 (p.bits - 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have ew : (BitVec.ofNat 64 (p.bits - 1) + 63#64) >>> 6 = BitVec.ofNat 64 (wOf (p.bits - 1)) :=
      add_shr _ _ _ (by omega)
    have ek : (BitVec.ofNat 64 (p.bits - 1) + 7#64) >>> 3 = BitVec.ofNat 64 ((p.bits - 1 + 7) / 8) :=
      add_shr _ _ _ (by omega)
    have e29 : BitVec.ofNat 64 (8 * wOf (p.bits - 1)) + 16#64 = BitVec.ofNat 64 (8 * (wOf (p.bits - 1) + 2)) := by
      rw [BitVec.ofNat_add_ofNat]; congr 1
    have ec := checks_eq (mb := p.bits - 1) (by omega)
    prun [h.r31, h.ld (d := 40) (by decide), h.args.bits', h.st (d := 248) (by decide), h.st (d := 216) (by decide),
      h.st (d := 48) (by decide), h.st (d := 224) (by decide), h.st (d := 64) (by decide), h.st (d := 72) (by decide),
      h.st (d := 80) (by decide), h.st (d := 88) (by decide), h.st (d := 96) (by decide), h.st (d := 104) (by decide),
      h.st (d := 112) (by decide), h.st (d := 120) (by decide), h.st (d := 168) (by decide), e1, ew, ek,
      Pub.ofNat_shl3, Pub.ofNat_shl1, e29, ec]
    refine ⟨by simp [off, slot, hdrBytes], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    any_goals simp (disch := decide) only [word, off, rw_off, rw_self]
    · intro j hj
      rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j
      all_goals first
        | (simp (disch := decide) only [rw_off, rw_self, Nat.reduceMul, Nat.reduceAdd]
           congr 1; simp only [slot, hdrBytes]; omega)
        | omega
    · iterate 13 refine frm_writeW ?_ _ (by decide) (by decide)
      exact Frm.refl _ _ _

/-- `topMask`'s first block: its count `k = mb + 64 − 64 w` in `r3`. -/
theorem topT1_ok {p : PP} {s : State} (h : St p s) {mb : Nat}
    (hm : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb) (hw : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)) :
    WP isa (.block [ldh .r3 hMb, ldh .r4 hW, .lsl .r4 .r4 6, .sub .r3 .r3 .r4, .addi .r3 .r3 64, .li .r5 0]) s
      fun u => (u.gpr .r3 = BitVec.ofNat 64 (mb + 64 - 64 * wOf mb) ∧ u.gpr .r5 = BitVec.ofNat 64 0 ∧
        u.mem = s.mem) ∧ Keep [.r3, .r4, .r5] s u := by
  have hk1 : 1 ≤ mb + 64 - 64 * wOf mb := by simp only [wOf]; omega
  have hk2 : mb + 64 - 64 * wOf mb ≤ 64 := by simp only [wOf]; omega
  generalize hkd : mb + 64 - 64 * wOf mb = k at hk1 hk2 ⊢
  have ek : BitVec.ofNat 64 mb - BitVec.ofNat 64 (wOf mb) <<< 6 + BitVec.ofNat 64 64 = BitVec.ofNat 64 k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp only [wOf] at hkd ⊢
    omega
  refine WP.keep [.r3, .r4, .r5] ?_ (by decide)
  simp only [ldh, hMb, hW]
  prun [h.r31, h.ld (d := 248) (by decide), h.ld (d := 48) (by decide), show s.mem.readW (p.B + 248#64) 64 =
    BitVec.ofNat 64 mb from hm, show s.mem.readW (p.B + 48#64) 64 = BitVec.ofNat 64 (wOf mb) from hw]
  exact ek

/-- `topMask`: `hTop := 2^k − 1` for `k = mb + 64 − 64 w`, in 1..=64. -/
theorem topMask_ok {p : PP} {s : State} (h : St p s) {mb : Nat}
    (hm : word s.mem p.B (8 * hMb) = BitVec.ofNat 64 mb) (hw : word s.mem p.B (8 * hW) = BitVec.ofNat 64 (wOf mb)) :
    WP isa topMask s fun t =>
      (word t.mem p.B (8 * hTop) = BitVec.ofNat 64 (2 ^ (mb + 64 - 64 * wOf mb) - 1) ∧
        Frm p.B [(8 * hTop, 8)] s.mem t.mem) ∧ Keep [.r3, .r4, .r5] s t := by
  have hk1 : 1 ≤ mb + 64 - 64 * wOf mb := by simp only [wOf]; omega
  have hk2 : mb + 64 - 64 * wOf mb ≤ 64 := by simp only [wOf]; omega
  unfold topMask
  refine WP.seq (WP.mono (topT1_ok h hm hw) fun u ⟨⟨u3, u5, um⟩, ku⟩ => ?_)
  generalize hkd : mb + 64 - 64 * wOf mb = k at hk1 hk2 u3 ⊢
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r5 = BitVec.ofNat 64 (2 ^ i - 1) ∧ t.mem = s.mem) ∧ Keep [.r3, .r4, .r5] s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .r3) (N := k) (by omega) (by omega) Inv
    (fun i hi t ⟨⟨t5, tm⟩, kt⟩ _ => ?_) ⟨⟨u5, um⟩, ku⟩ u3) fun t ⟨⟨t5, tm⟩, kt⟩ => ?_)
  · refine WP.mono (WP.keep [.r3, .r5] (Q := fun t' => t'.gpr .r5 = BitVec.ofNat 64 (2 ^ (i + 1) - 1) ∧
      t'.mem = t.mem ∧ t'.gpr .r3 = t.gpr .r3 - BitVec.ofNat 64 1) ?_ (by decide))
      fun t' ⟨⟨a, b, c⟩, k'⟩ => ⟨⟨⟨a, b.trans tm⟩, (kt.trans k').mono (by decide)⟩, c⟩
    prun [t5]
    apply BitVec.eq_of_toNat_eq
    have : 2 ^ i ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.pow_succ]
    omega
  · have hst : InRegions t.wr (p.B + BitVec.ofNat 64 192) 8 := by rw [kt.wr]; exact h.st (d := 192) (by decide)
    refine WP.mono (WP.keep [] (Q := fun t' => t'.mem = t.mem.writeW (p.B + BitVec.ofNat 64 192) (t.gpr .r5)) ?_
      (by decide)) fun t' ⟨e, k'⟩ => ⟨⟨?_, ?_⟩, (kt.trans k').mono (by decide)⟩
    · simp only [sth, hTop]
      prun [(kt.gpr .r31 (by decide)).trans h.r31, hst]
    · show (t'.mem).readW (p.B + BitVec.ofNat 64 192) 64 = _
      rw [e, rw_self, t5]
    · rw [e, ← tm]; exact (frm_writeW (Frm.refl _ _ _) _ (by decide) (by decide))

/-- The registers `phase` writes. -/
def phaseRegs : List Reg := phRegs

theorem phRanges_mut (n : Nat) : ∀ r ∈ phRanges ++ [(8 * hTop, 8)], InMut n r := by
  intro r hr
  simp only [phRanges, hTop, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩
  all_goals exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), by decide, by decide⟩

/-- `phase`: `Ph` for the modulus of `mbOf p q` bits. -/
theorem phase_ok {p : PP} {s : State} (h : St p s) (q : Bool) :
    WP isa (phase q) s fun t => (St p t ∧ Ph p (mbOf p q) t ∧ Frm p.B (phRanges ++ [(8 * hTop, 8)]) s.mem t.mem) ∧
      Keep phaseRegs s t := by
  unfold phase
  refine WP.seq (WP.mono (phaseHead_ok h q) fun u ⟨⟨u10, u11, u29, um, uk, uw, us, ua, uc, uf⟩, ku⟩ => ?_)
  have fu : Frm p.B (mutR p.n) s.mem u.mem := Frm.toMut (uf.mono fun r hr => List.mem_append_left _ hr)
    (phRanges_mut p.n)
  have hu := h.step fu ku
  refine WP.mono (topMask_ok hu um uw) fun t ⟨⟨tt, tf⟩, kt⟩ => ?_
  have ft : Frm p.B (mutR p.n) u.mem t.mem := Frm.toMut (tf.mono fun r hr => List.mem_append_right _ hr)
    (phRanges_mut p.n)
  have e : ∀ {d : Nat}, d + 8 ≤ 192 ∨ (200 ≤ d ∧ d + 8 ≤ 256) → word t.mem p.B d = word u.mem p.B d := fun hd =>
    tf.word_eq (fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp only [hTop]; omega) (by omega)
  refine ⟨⟨hu.step ft kt, ⟨(kt.gpr .r10 (by decide)).trans u10, (kt.gpr .r11 (by decide)).trans u11,
    (kt.gpr .r29 (by decide)).trans u29, (e (by simp only [hMb]; omega)).trans um,
    (e (by simp only [hK]; omega)).trans uk, (e (by simp only [hW]; omega)).trans uw,
    (e (by simp only [hStride]; omega)).trans us, fun j hj => (e (by omega)).trans (ua j hj),
    (e (by simp only [hChecks]; omega)).trans uc, tt⟩,
    (uf.mono fun r hr => List.mem_append_left _ hr).trans (tf.mono fun r hr => List.mem_append_right _ hr)⟩,
    (ku.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
