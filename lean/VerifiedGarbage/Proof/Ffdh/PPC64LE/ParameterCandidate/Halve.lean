module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordHalf
import VerifiedGarbage.Proof.RsaKeyGen.Bits
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An FFDH parameter candidate on PPC64LE: q

`halveQ_ok`: array 0 halved in place (p into q = (p − 1) / 2, p being odd),
and `hBad` nonzero when q is even.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search VG.Proof.MillerRabin.PPC64LE.Search

theorem low_flag (x : BitVec 64) : (x &&& 1#64) ^^^ 1#64 = 0#64 ↔ x.toNat % 2 = 1 := by
  have e : x &&& 1#64 = BitVec.ofNat 64 (x.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod]
    omega
  rw [e]
  rcases Nat.mod_two_eq_zero_or_one x.toNat with h | h <;> rw [h] <;> decide

theorem wv_mod_two (m : Mem) (p : Addr) (d : Nat) {w : Nat} (hw : 1 ≤ w) :
    wv m p d w % 2 = (word m p d).toNat % 2 := by
  have e := VG.Proof.RsaKeyGen.testBit_wv m p d w 0 (by omega)
  simp only [Nat.zero_div, Nat.mul_zero, Nat.add_zero, Nat.zero_mod, Nat.testBit_zero, decide_eq_decide] at e
  omega

/-- The registers `halveQ` writes. -/
def hqRegs : List Reg := [.r3, .r4, .r5, .r6]

/-- Word `j` of the halved number. -/
abbrev halfW (m : Mem) (B : Addr) (a j : Nat) : BitVec 64 :=
  (word m B (a + 8 * j) >>> 1) ||| (word m B (a + 8 * (j + 1)) <<< 63)

theorem halveQ_ok {p : PP} {s : State} {w x : Nat} (hs : St p s) (h10 : s.gpr .r10 = off p.B (slot w 0))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hx : wv s.mem p.B (slot w 0) w = x) (hw2 : 2 ≤ w)
    (hw : w < 2 ^ 31) (hZ : slot w 0 + 8 * w ≤ p.Z) :
    WP isa halveQ s fun t =>
      (wv t.mem p.B (slot w 0) w = x / 2 ∧
        (word t.mem p.B (8 * hBad) = 0#64 ↔ word s.mem p.B (8 * hBad) = 0#64 ∧ x / 2 % 2 = 1) ∧
        Frm p.B [(slot w 0, 8 * w), (8 * hBad, 8)] s.mem t.mem) ∧ Keep hqRegs s t := by
  have hnw := hs.scr.nowrap
  have h0 : slot w 0 = 256 := by simp [slot, hdrBytes]
  rw [h0] at h10 hx hZ ⊢
  simp only [PP.Z] at hZ hnw
  unfold halveQ
  refine WP.seq (WP.mono (WP.keep [.r5, .r6] (Q := fun u => u.gpr .r5 = off p.B 256 ∧
      u.gpr .r6 = BitVec.ofNat 64 (w - 1) ∧ u.mem = s.mem) ?_ (by decide)) fun u ⟨⟨u5, u6, um⟩, ku⟩ => ?_)
  · prun [h10, h11, BitVec.add_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    omega
  let Inv : Nat → State → Prop := fun i t =>
    (t.gpr .r5 = off p.B (256 + 8 * i) ∧ (∀ j < i, word t.mem p.B (256 + 8 * j) = halfW s.mem p.B 256 j) ∧
      (∀ j, i ≤ j → j < w → word t.mem p.B (256 + 8 * j) = word s.mem p.B (256 + 8 * j)) ∧
      Frm p.B [(256, 8 * w)] s.mem t.mem) ∧ Keep hqRegs s t
  refine WP.seq (WP.mono (wp_countdown (cnt := .r6) (N := w - 1) (by omega) (by omega) Inv
    (fun i hi t ⟨⟨t5, tlo, thi, tf⟩, kt⟩ _ => ?_)
    ⟨⟨by rw [u5], fun j hj => absurd hj (Nat.not_lt_zero _), fun j _ _ => by rw [um],
      by rw [um]; exact Frm.refl _ _ _⟩, ku.mono (by decide)⟩ u6) fun t ht => ?_)
  · have hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.wr
    have l0 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * i)) 8 := hsc.ld (by omega)
    have l1 : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (i + 1))) 8 := hsc.ld (by omega)
    have s0 : InRegions t.wr (off p.B (256 + 8 * i)) 8 := hsc.st (by omega)
    have e8 : off p.B (256 + 8 * i) + BitVec.ofNat 64 8 = off p.B (256 + 8 * (i + 1)) := by
      rw [show off p.B (256 + 8 * i) + BitVec.ofNat 64 8 = off (off p.B (256 + 8 * i)) 8 from rfl, off_off,
        show 256 + 8 * i + 8 = 256 + 8 * (i + 1) by omega]
    have r0 : t.mem.readW (off p.B (256 + 8 * i)) 64 = word s.mem p.B (256 + 8 * i) := thi i (by omega) (by omega)
    have r1 : t.mem.readW (off p.B (256 + 8 * (i + 1))) 64 = word s.mem p.B (256 + 8 * (i + 1)) :=
      thi (i + 1) (by omega) (by omega)
    refine WP.mono (WP.keep [.r3, .r4, .r5, .r6] (Q := fun u => u.gpr .r5 = off p.B (256 + 8 * (i + 1)) ∧
        u.mem = t.mem.writeW (off p.B (256 + 8 * i)) (halfW s.mem p.B 256 i) ∧
        u.gpr .r6 = t.gpr .r6 - BitVec.ofNat 64 1) ?_ (by decide))
      fun u ⟨⟨u5, um, u6⟩, ku⟩ => ⟨⟨⟨u5, ?_, ?_, ?_⟩, (kt.trans ku).mono (by decide)⟩, u6⟩
    · prun [t5, BitVec.add_zero, e8, l0, l1, s0, r0, r1]
    · intro j hj
      rw [um]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [word, rw_off _ _ _ (by omega) (by omega) (by omega)]; exact tlo j hj
      · exact rw_self _ _ _
    · intro j hj hj'
      rw [um, word, rw_off _ _ _ (by omega) (by omega) (by omega)]
      exact thi j (by omega) hj'
    · rw [um]
      exact frm_writeW tf _ ⟨_, List.mem_singleton_self _, by dsimp only; omega, by dsimp only; omega⟩ (by omega)
  obtain ⟨⟨t5, tlo, thi, tf⟩, kt⟩ := ht
  have hsc : Scr t p.B (8 * p.n) := hs.scr.congr kt.wr
  have lT : InRegions (t.rd ++ t.wr) (off p.B (256 + 8 * (w - 1))) 8 := hsc.ld (by omega)
  have sT : InRegions t.wr (off p.B (256 + 8 * (w - 1))) 8 := hsc.st (by omega)
  have rT : t.mem.readW (off p.B (256 + 8 * (w - 1))) 64 = word s.mem p.B (256 + 8 * (w - 1)) :=
    thi (w - 1) (by omega) (by omega)
  have h31 : t.gpr .r31 = p.B := (kt.gpr .r31 (by decide)).trans hs.r31
  have t10 : t.gpr .r10 = off p.B 256 := (kt.gpr .r10 (by decide)).trans h10
  have lB : InRegions (t.rd ++ t.wr) (p.B + BitVec.ofNat 64 200) 8 := hsc.ld (d := 200) (by omega)
  have sB : InRegions t.wr (p.B + BitVec.ofNat 64 200) 8 := hsc.st (d := 200) (by omega)
  have l0 : InRegions (t.rd ++ t.wr) (off p.B 256) 8 := hsc.ld (by omega)
  have rB : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (p.B + BitVec.ofNat 64 200) 64 =
      word s.mem p.B 200 := fun v => by
    rw [rw_off _ _ _ (by omega) (by omega) (by omega)]
    exact tf.word_eq (fun r hr => by rw [List.mem_singleton] at hr; subst hr; dsimp only; omega) (by omega)
  have r0 : ∀ v : BitVec 64, (t.mem.writeW (off p.B (256 + 8 * (w - 1))) v).readW (off p.B 256) 64 =
      halfW s.mem p.B 256 0 := fun v => by
    rw [show off p.B 256 = off p.B (256 + 8 * 0) from rfl, rw_off _ _ _ (by omega) (by omega) (by omega)]
    exact tlo 0 (by omega)
  refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun u => u.mem =
      (t.mem.writeW (off p.B (256 + 8 * (w - 1))) (word s.mem p.B (256 + 8 * (w - 1)) >>> 1)).writeW
        (p.B + BitVec.ofNat 64 200) (word s.mem p.B 200 ||| ((halfW s.mem p.B 256 0 &&& 1#64) ^^^ 1#64))) ?_
      (by decide)) fun u ⟨um, ku⟩ => ⟨?_, (kt.trans ku).mono (by decide)⟩
  · simp only [ldh, sth, hBad]
    prun [t5, t10, h31, BitVec.add_zero, lT, sT, rT, lB, sB, l0, rB, r0]
  have hv : wv u.mem p.B 256 w = x / 2 := by
    rw [← hx]
    refine Proof.Ffdh.ParameterCandidate.wv_half (by omega) (fun j hj => ?_) ?_
    · rw [um, word, rw_off _ _ _ (by omega) (by omega) (by omega), rw_off _ _ _ (by omega) (by omega) (by omega)]
      exact tlo j (by omega)
    · rw [um, word, rw_off _ _ _ (by omega) (by omega) (by omega), rw_self]
  refine ⟨hv, ?_, ?_⟩
  · have e := wv_mod_two u.mem p.B 256 (w := w) (by omega)
    have t0 : t.mem.readW (p.B + BitVec.ofNat 64 256) 64 = halfW s.mem p.B 256 0 := tlo 0 (by omega)
    rw [hv, um, word, rw_off _ _ _ (by omega) (by omega) (by omega), rw_off _ _ _ (by omega) (by omega) (by omega),
      t0] at e
    simp only [word, off, hBad, Nat.reduceMul, um, rw_self, BitVec.or_eq_zero_iff, low_flag]
    rw [e]
  · rw [um]
    refine frm_writeW (frm_writeW (tf.mono fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self) _
        ⟨_, List.mem_cons_self, by dsimp only; omega, by dsimp only; omega⟩ (by omega)) _
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by decide, by decide⟩ (by omega)

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
