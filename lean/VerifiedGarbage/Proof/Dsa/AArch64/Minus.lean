module

public import VerifiedGarbage.Proof.Dsa.AArch64.Frame
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import Aesop.BuiltinRules
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Bignum.AArch64.Row

/-! ### `Dsa.AArch64.MinusStep`, which this module and modules that import it used -/

section

/-! # Fixed-count borrow propagation for modulus-minus constants -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

structure MinusInv (s₀ : State) (B : Addr) (Z eN eY amount : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.x3, .x14, .x16, .x17] s₀ t
  source : t.gpr .x16 = off B (eN + 8 * j)
  dest : t.gpr .x17 = off B (eY + 8 * j)
  out : Outside B eY (8 * j) s₀.mem t.mem
  val : wv t.mem B eY j + amount = wv s₀.mem B eN j + 2 ^ (64 * j) * (!t.c).toNat

abbrev minusTail : List Instr :=
  [ld .x3 .x16, .sbcs .x .x3 .x3 .x7, st .x3 .x17, next .x16, next .x17]

theorem minus_word (a z : BitVec 64) (c : Bool) (hz : z.toNat = 0) :
    (a + ~~~z + BitVec.ofNat 64 c.toNat).toNat + (!c).toNat =
      a.toNat + 2 ^ 64 * (!decide (2 ^ 64 ≤ a.toNat + (~~~z).toNat + c.toNat)).toNat := by
  have h := sbcs_toNat a z c
  rw [hz, Nat.add_zero] at h
  exact h

theorem minusStep_ok {s₀ : State} {B : Addr} {Z w eN eY amount : Nat}
    (h7 : s₀.gpr .x7 = 0) (hY : eY + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eY + 8 * w ≤ eN ∨ eN + 8 * w ≤ eY) {j : Nat} (hj : j < w) {t : State}
    (hI : MinusInv s₀ B Z eN eY amount j t) :
    WP isa (.block (minusTail ++ ([.subImm .x .x14 .x14 1] : List Instr))) t
      fun t' => MinusInv s₀ B Z eN eY amount (j + 1) t' ∧ t'.gpr .x14 = t.gpr .x14 - BitVec.ofNat 64 1 := by
  have hn := hI.scr.nowrap
  have t7 := (hI.keep.gpr .x7 (by decide)).trans h7
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.x3, .x16, .x17] (Q := fun u =>
    ∃ r : BitVec 64, u.mem = t.mem.writeW (off B (eY + 8 * j)) r ∧
      r.toNat + (!t.c).toNat = (word t.mem B (eN + 8 * j)).toNat + 2 ^ 64 * (!u.c).toNat ∧
      u.gpr .x16 = off B (eN + 8 * j + 8) ∧ u.gpr .x17 = off B (eY + 8 * j + 8)) ?_ rfl rfl rfl)
    fun u ⟨⟨r, hm, hr, hp, hq⟩, hk⟩ => ?_
  · unfold minusTail
    brun [hI.source, hI.dest, hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega_using [hN, hj]),
      hI.scr.st (show eY + 8 * j + 8 ≤ Z by omega_using [hY, hj])]
    refine ⟨_, rfl, ?_⟩
    exact minus_word _ _ t.c (by rw [t7]; rfl)

  refine WP.mono (dec_ok u .x14) fun v ⟨⟨h14, hvm, hc⟩, hkv⟩ => ⟨?_, by rw [h14, hk.gpr .x14 (by decide)]⟩
  have hx : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega_using [hsep, hj]) (by omega_using [hN, hj, hn])
  rw [hx] at hr
  refine ⟨hI.scr.congr (hkv.wr.trans hk.wr), ((hI.keep.trans hk).trans hkv).mono (by decide),
    ?_, ?_, ?_, ?_⟩
  · rw [hkv.gpr .x16 (by decide), hp, Nat.mul_succ, Nat.add_assoc]
  · rw [hkv.gpr .x17 (by decide), hq, Nat.mul_succ, Nat.add_assoc]
  · rw [hvm, hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega_using [hY, hj, hn]) x (by omega_using [hx'])]
    exact hI.out x (by omega_using [hx'])
  · have hlow : wv t.mem B eY j = wv (t.mem.writeW (off B (eY + 8 * j)) r) B eY j :=
      ((writeW_outside t.mem B r (by omega_using [hY, hj, hn])).wv (Or.inl (by omega_using [])) (by omega_using [hY, hj, hn])).symm
    rw [hvm, hm, hc]
    simp only [wv]
    rw [← hlow, word_writeW_self, pow64_succ]
    have hv := hI.val
    have hh := congrArg (fun x : Nat => 2 ^ (64 * j) * x) hr
    simp only [Nat.mul_add] at hh
    simp only [Nat.mul_assoc]
    omega_using [hv, hh]

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.MinusHead`, which this module and modules that import it used -/

section

/-! # First limb and public counter for modulus-minus constants -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev minusHead (amount : Nat) : List Instr :=
  [ldh .x14 sW, ldh .x16 (sArr aN), ldh .x17 (sArr aY), movi .x4 amount,
    movi .x7 0, ld .x3 .x16, .subs .x .x3 .x3 .x4, st .x3 .x17,
    next .x16, next .x17, .subImm .x .x14 .x14 1]

theorem minusHead_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (ha : amount < 2 ^ 16) :
    WP isa (.block (minusHead amount)) s fun t =>
      t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.gpr .x16 = off B (slot w aN + 8) ∧
      t.gpr .x17 = off B (slot w aY + 8) ∧ t.gpr .x7 = 0 ∧ Outside B (slot w aY) 8 s.mem t.mem ∧
      wv t.mem B (slot w aY) 1 + amount = wv s.mem B (slot w aN) 1 + 2 ^ 64 * (!t.c).toNat ∧
      Keep mmRegs s t := by
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
    fun i hi => hg.ld hZ hi
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hz := hg.scr.nowrap
  have ham : (BitVec.ofNat 16 amount).setWidth 64 = BitVec.ofNat 64 amount := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hsub : BitVec.ofNat 64 w - (1#64) = BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega
  refine WP.mono (WP.keep [.x14, .x16, .x17, .x4, .x7, .x3] (Q := fun t =>
    t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.gpr .x16 = off B (slot w aN + 8) ∧
    t.gpr .x17 = off B (slot w aY + 8) ∧ t.gpr .x7 = 0 ∧ ∃ r : BitVec 64,
    t.mem = s.mem.writeW (off B (slot w aY)) r ∧
    r.toNat + amount = (word s.mem B (slot w aN)).toNat + 2 ^ 64 * (!t.c).toNat) ?_ rfl rfl rfl)
    fun t ⟨⟨ht14, ht16, ht17, ht7, r, htm, hv⟩, hk⟩ => ?_
  · unfold minusHead
    brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aN < 32 by decide), hdr_enc (show sArr aY < 32 by decide),
      hl sW (by decide), hl (sArr aN) (by decide), hl (sArr aY) (by decide),
      hg.hdr.hw, hg.hdr.harr aN (by decide), hg.hdr.harr aY (by decide), ham, hsub,
      hg.scr.ld (show slot w aN + 8 ≤ Z by omega), hg.scr.st (show slot w aY + 8 ≤ Z by omega)]
    refine ⟨_, rfl, ?_⟩
    simpa only [Bool.toNat_true, Bool.not_true, Bool.toNat_false, Nat.add_zero,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show amount < 2 ^ 64 by omega)] using
      sbcs_toNat (word s.mem B (slot w aN)) (BitVec.ofNat 64 amount) true
  · refine ⟨ht14, ht16, ht17, ht7, ?_, ?_, hk.mono (by decide)⟩
    · rw [htm]; exact writeW_outside _ _ _ (by omega)
    · rw [htm]
      simpa only [wv, Nat.mul_zero, Nat.add_zero, Nat.zero_add, Nat.pow_zero, Nat.one_mul,
        word_writeW_self] using hv

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.MinusCore`, which only this module used -/

section

/-! # Exact subtraction of a small public value from the modulus -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem minusCore_ok {s : State} {B : Addr} {Z w amount : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (ha : amount < 2 ^ 16) (hm : amount ≤ wv s.mem B (slot w aN) w) :
    WP isa (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) s fun t =>
      wv t.mem B (slot w aY) w = wv s.mem B (slot w aN) w - amount ∧
      Outside B (slot w aY) (8 * w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hz := hg.scr.nowrap
  have hy := Nat.le_trans (slot_le (w := w) (show aY < 8 by decide)) hZ
  have hn := Nat.le_trans (slot_le (w := w) (show aN < 8 by decide)) hZ
  have hsep := slot_sep (w := w) (show aY ≠ aN by decide)
  refine WP.seq (WP.mono (minusHead_ok hg hZ (by omega_using [hw]) hw' ha)
    fun u ⟨hu14, hu16, hu17, hu7, hfu, hv, hku⟩ => ?_)
  have huN : ∀ k ≤ w, wv u.mem B (slot w aN) k = wv s.mem B (slot w aN) k :=
    fun k hk => hfu.wv (by omega_using [hsep, hk]) (by omega_using [hz, hn, hk])
  have h0 : MinusInv u B Z (slot w aN) (slot w aY) amount (0 + 1) u :=
    ⟨hg.scr.congr hku.wr, Keep.refl _ _, by simpa using hu16, by simpa using hu17,
      Outside.refl _ _ _ _, by rw [huN 1 (by omega_using [hw])]; exact hv⟩
  refine WP.mono (wp_countdown (N := w - 1) (by omega_using [hw']) (by omega_using [hw])
    (fun j t => MinusInv u B Z (slot w aN) (slot w aY) amount (j + 1) t)
    (fun j hj t hi _ => minusStep_ok hu7 (by omega) (by omega_using [hn]) (by omega_using [hsep]) (by omega_using [hj]) hi) h0 hu14)
    fun t ht => ?_
  have he : w - 1 + 1 = w := by omega_using [hw]
  rw [he] at ht
  have hv := ht.val
  rw [huN w (Nat.le_refl _)] at hv
  have hvlt := wv_lt t.mem B (slot w aY) w
  refine ⟨?_, (hfu.mono (Nat.le_refl _) (by omega_using [hw])).trans ht.out, (hku.trans ht.keep).mono (by decide)⟩
  cases hc : t.c <;> simp only [hc, Bool.not_false, Bool.not_true, Bool.toNat_false, Bool.toNat_true,
    Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hv <;> omega_arith

end VG.Proof.Dsa.AArch64

end

end

/-! # Modulus-minus constants in a linked DSA workspace -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem minus_ok {s : State} {B : Addr} {Z o w wx m amount : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw : 2 ≤ wx) (hw' : wx < 2 ^ 31) (ha : amount < 2 ^ 16) (ham : amount ≤ m) :
    WP isa (.seq (.block (minusHead amount)) (countLoop .x14 minusTail)) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = m - amount ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  refine WP.mono (minusCore_ok hc.good (Nat.le_refl _) hw hw' ha (by rw [hm.modulus]; exact ham))
    fun t ⟨ht, hf, hk⟩ => ?_
  have harr : Arrays (off B o) wx [aY] s.mem t.mem :=
    Arrays.of_outside (List.mem_singleton_self aY) hf (Nat.le_refl _) (by omega_using [])
  have hct := arrays_context hc harr (by decide) hk
  have hz := hc.good.scr.nowrap
  have hn := (harr.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hm.modulus
  have hi : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [harr.word0_of_not_mem (by decide) (by decide) hz (by omega_using [hw])]
    exact hm.inverse
  rw [hm.modulus] at ht
  exact ⟨hct, ⟨hct.good, hn, hi⟩, ht, arrays_work harr (by decide), hk⟩

end VG.Proof.Dsa.AArch64
