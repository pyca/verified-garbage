module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import Mathlib.Tactic.Set

/-! # Loading and adding reduced DSA scalars -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- The ordinary addition body used by signing. Inputs are reduced by the
preceding product and digest-reduction operations. -/
theorem add_ok {s : State} {B : Addr} {Z o w wx m : Nat} {minv : BitVec 64}
    (hc : SubCtx s B Z o w wx minv) (hm : ModCtx s (off B o) (slot wx 8) wx minv m)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    {ap al bp bl : Nat} (hap : ap < 32) (hal : al < 32) (hbp : bp < 32) (hbl : bl < 32)
    {pa pb : Addr} {ba bb : List Byte}
    (ha : word s.mem B (8 * ap) = pa)
    (halen : word s.mem B (8 * al) = BitVec.ofNat 64 ba.length)
    (has : Src s B Z pa ba) (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb : word s.mem B (8 * bp) = pb)
    (hblen : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx)
    (haReduced : Spec.Dsa.decodeBE ba < m) (hbReduced : Spec.Dsa.decodeBE bb < m) :
    WP isa (seqs [Arithmetic.load aX ap al, Arithmetic.load aXm bp bl, Crt.addMod aY aX aXm]) s fun t =>
      SubCtx t B Z o w wx minv ∧ ModCtx t (off B o) (slot wx 8) wx minv m ∧
      wv t.mem (off B o) (slot wx aY) wx = (Spec.Dsa.decodeBE ba + Spec.Dsa.decodeBE bb) % m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold seqs
  refine WP.seq (WP.mono (load_mod_ok hc hm hw2 hwx hw30 (by decide) (by decide) hap hal
    ha halen has ha1 (by omega) haw) fun u ⟨hcu, hmu, hua, _, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (load_mod_ok hcu hmu hw2 hwx hw30 (by decide) (by decide) hbp hbl
    ((work_parent hc hfu hbp).trans hb) ((work_parent hc hfu hbl).trans hblen)
    (work_source hc hfu hku hbs) hb1 (by omega) hbw) fun v ⟨hcv, hmv, hvb, hvkeep, hfv, hkv⟩ => ?_)
  have hva := (hvkeep aX (by decide) (by decide)).trans hua
  refine WP.mono (addMod_ok hcv.good.scr hcv.good.rdi hcv.good.hdr (Nat.le_refl _) hw2 (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hva, hmv.modulus]; exact haReduced) (by rw [hvb, hmv.modulus]; exact hbReduced))
    fun t ⟨htv, hft, hkt⟩ => ?_
  have hct := arrays_context hcv hft (by decide) hkt
  have hn := hcv.good.scr.nowrap
  have hnt := (hft.wv_of_not_mem (show aN < 8 by decide) (by decide) hn).trans hmv.modulus
  have hit : ((word t.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 := by
    rw [hft.word0_of_not_mem (by decide) (by decide) hn (by omega)]
    exact hmv.inverse
  rw [hva, hvb, hmv.modulus] at htv
  exact ⟨hct, ⟨hct.good, hnt, hit⟩, htv, (hfu.trans hfv).trans (arrays_work hft (by decide)),
    ((hku.trans hkv).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
