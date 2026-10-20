module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs

/-! # DSA exponentiation, including conversion out of Montgomery form -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The ordinary result of exponentiation, for an odd (possibly composite)
modulus. The exponent may be caller bytes or bytes in the scratch suffix. -/
theorem encodedPower_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m x : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    (hxl : wv s.mem (off B o) (slot wx Crt.aXc) wx < m)
    (hxc : wv s.mem (off B o) (slot wx Crt.aXc) wx % m = x * 2 ^ (64 * wx) % m)
    (hyl : wv s.mem (off B o) (slot wx aY) wx < m)
    (hyc : wv s.mem (off B o) (slot wx aY) wx % m = 2 ^ (64 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (Arithmetic.encodedPower Sq.mm M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hmctx : ModCtx s (off B o) (slot wx 8) wx minv m := ⟨hc.good, hn, hinv⟩
  have hnZ := hc.good.scr.nowrap
  have hR := coprime_pow2 hodd (64 * wx)
  unfold Arithmetic.encodedPower
  refine WP.seq (WP.mono (expLoop_ok M Sq hc hw2 hwx hw30 hn hinv hodd hxl hxc hyl hyc
    hsp hsl hep hel hL1 hL2 he) fun u ⟨hu, hlt, hv, hf, hk⟩ => ?_)
  have hmu := modCtx_exp hmctx hu.good hf (Nat.le_refl _)
  have oneSep := crtExpRanges_arr wx (j := aOne) (by decide) (by decide) (by decide) (by decide) (by decide)
  have oneSlot := slot_le (w := wx) (show aOne < 8 by decide)
  have huone : wv u.mem (off B o) (slot wx aOne) wx = 1 :=
    (hf.wv_eq (fun r hr => by have := oneSep r hr; omega) (by omega)).trans hone
  refine WP.mono (mont_step M hmu (Nat.le_refl _) hw2 (by omega)
    (by unfold MmUse; decide) (by rw [huone]; exact hm)) fun t ⟨hmt, hlt', hv', hf', hk'⟩ => ?_
  rw [huone] at hv'
  have result := VG.Proof.Dsa.mont_decode hR hv hv'
  rw [Nat.mod_eq_of_lt hlt', Nat.mod_eq_of_lt (VG.Proof.Dsa.powMod_lt _ _ (by omega))] at result
  exact ⟨arrays_context hu hf' (by decide) hk', result, hmt,
    (exp_work hf).trans (arrays_work hf' (by decide)), (hk.trans hk').mono (by decide)⟩

/-- Exponentiation of an ordinary, possibly unreduced base, using the
prepared constants and an exponent from the parent call header. -/
theorem powerCore_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m x : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hone : wv s.mem (off B o) (slot wx aOne) wx = 1)
    (hx : wv s.mem (off B o) (slot wx aX) wx = x)
    (hR2 : wv s.mem (off B o) (slot wx aR2) wx = 2 ^ (128 * wx) % m)
    {sp sl : Nat} (hsp : sp < 32) (hsl : sl < 32) {ep : Addr} {eb : List Byte}
    (hep : word s.mem B (8 * sp) = ep) (hel : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hL1 : 1 ≤ eb.length) (hL2 : eb.length ≤ 1024) (he : Src s B Z ep eb) :
    WP isa (Arithmetic.powerCore Sq.mm M.mm sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.powMod x (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  have hR2' : wv s.mem (off B o) (slot wx aR2) wx =
      (2 ^ (64 * wx) * 2 ^ (64 * wx)) % m := by
    rw [hR2, ← Nat.pow_add, show 64 * wx + 64 * wx = 128 * wx by omega]
  unfold Arithmetic.powerCore
  refine WP.seq (WP.mono (encodePower_ok M ⟨hc.good, hn, hinv⟩ (Nat.le_refl _) hw2 (by omega)
    hm hodd hx hR2' hone) fun u ⟨hu, hux, huy, huone, hf, hk⟩ => ?_)
  have hcu := arrays_context hc hf (by decide) hk
  have hfu := arrays_work hf (by decide)
  have hsrc := work_source hc hfu hk he
  refine WP.mono (encodedPower_ok M Sq hcu hw2 hwx hw30 hm hodd hu.modulus hu.inverse huone
    (by rw [hux]; exact Nat.mod_lt _ (by omega))
    (by rw [hux, Nat.mod_mod])
    (by rw [huy]; exact Nat.mod_lt _ (by omega))
    (by rw [huy, Nat.mod_mod]) hsp hsl
    ((work_parent hc hfu hsp).trans hep) ((work_parent hc hfu hsl).trans hel) hL1 hL2 hsrc)
    fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hfu.trans hft, (hk.trans hkt).mono (by decide)⟩

/-- Complete exponentiation, including constants setup and loading the base.
Both byte buffers remain valid when they occupy the inactive scratch suffix. -/
theorem power_ok (M : Mont) (Sq : MontS) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {bp bl sp sl : Nat} (hbp : bp < 32) (hbl : bl < 32) (hsp : sp < 32) (hsl : sl < 32)
    {base exp : Addr} {bb eb : List Byte}
    (hb : word s.mem B (8 * bp) = base)
    (hblen : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z base bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (he : word s.mem B (8 * sp) = exp)
    (helen : word s.mem B (8 * sl) = BitVec.ofNat 64 eb.length)
    (hes : Src s B Z exp eb) (he1 : 1 ≤ eb.length) (he2 : eb.length ≤ 1024) :
    WP isa (Arithmetic.power Sq.mm M.mm bp bl sp sl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx =
        Spec.Dsa.powMod (Spec.Dsa.decodeBE bb) (Spec.Dsa.decodeBE eb) m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.power
  refine WP.seq (WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (load_ok hcu hw2 hwx hw30 (by decide) hbp hbl
    ((work_parent hc hfu hbp).trans hb) ((work_parent hc hfu hbl).trans hblen)
    (work_source hc hfu hku hbs) hb1 (by omega) hbw)
    fun v ⟨hcv, hvbase, hfv, hkv⟩ => ?_)
  have hfa : Arrays (off B o) wx [aX] u.mem v.mem :=
    Arrays.of_outside (List.mem_singleton_self aX) hfv (Nat.le_refl _) (Nat.le_refl _)
  have hfw := arrays_work hfa (by decide)
  have hz := hcu.good.scr.nowrap
  have vn := (hfa.wv_of_not_mem (show aN < 8 by decide) (by decide) hz).trans hmu.modulus
  have vi : ((word v.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hfa.word0_of_not_mem (by decide) (by decide) hz (by omega)]
    exact hmu.inverse
  have vone := (hfa.wv_of_not_mem (show aOne < 8 by decide) (by decide) hz).trans huone
  have vr2 := (hfa.wv_of_not_mem (show aR2 < 8 by decide) (by decide) hz).trans hur2
  have hf := hfu.trans hfw
  have hk := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.mono (powerCore_ok M Sq hcv hw2 hwx hw30 hm hodd vn vi vone hvbase vr2
    hsp hsl ((work_parent hc hf hsp).trans he) ((work_parent hc hf hsl).trans helen)
    he1 he2 (work_source hc hf hk hes)) fun t ⟨hct, hresult, hmt, hft, hkt⟩ =>
      ⟨hct, hresult, hmt, hf.trans hft, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
