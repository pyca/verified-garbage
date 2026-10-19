module
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Dsa.X86_64.Frame
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import Mathlib.Tactic.Set

/-! # Complete ordinary modular multiplication for DSA -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

/-- Load both ordinary operands, prepare Montgomery constants and produce
their reduced product. Neither input must already be reduced. -/
theorem product_ok (M : Mont) {s : State} {B : Addr} {Z o w wx m : Nat}
    {minv : BitVec 64} (hc : SubCtx s B Z o w wx minv)
    (hw2 : 2 ≤ wx) (hw48 : wx ≤ 48) (hwx : wx ≤ w) (hw30 : w < 2 ^ 30)
    (hm : 1 < m) (hodd : m % 2 = 1)
    (hn : wv s.mem (off B o) (slot wx aN) wx = m)
    (hinv : ((word s.mem (off B o) (slot wx aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    {ap al bp bl : Nat} (hap : ap < 32) (hal : al < 32) (hbp : bp < 32) (hbl : bl < 32)
    {pa pb : Addr} {ba bb : List Byte}
    (ha : word s.mem B (8 * ap) = pa)
    (halen : word s.mem B (8 * al) = BitVec.ofNat 64 ba.length)
    (has : Src s B Z pa ba) (ha1 : 1 ≤ ba.length) (haw : (ba.length + 7) / 8 ≤ wx)
    (hb : word s.mem B (8 * bp) = pb)
    (hblen : word s.mem B (8 * bl) = BitVec.ofNat 64 bb.length)
    (hbs : Src s B Z pb bb) (hb1 : 1 ≤ bb.length) (hbw : (bb.length + 7) / 8 ≤ wx) :
    WP isa (Arithmetic.product M.mm ap al bp bl) s fun t =>
      SubCtx t B Z o w wx minv ∧
      wv t.mem (off B o) (slot wx aY) wx = Spec.Dsa.decodeBE ba * Spec.Dsa.decodeBE bb % m ∧
      ModCtx t (off B o) (slot wx 8) wx minv m ∧
      Frm (off B o) (workRanges wx) s.mem t.mem ∧ Keep mmRegs s t := by
  unfold Arithmetic.product seqs
  refine WP.seq (WP.mono (prepare_ok M hc hw2 hw48 hm hodd hn hinv)
    fun u ⟨hcu, hmu, huone, hur2, hfu, hku⟩ => ?_)
  refine WP.seq (WP.mono (load_mod_ok hcu hmu hw2 hwx hw30 (by decide) (by decide) hap hal
    ((work_parent hc hfu hap).trans ha) ((work_parent hc hfu hal).trans halen)
    (work_source hc hfu hku has) ha1 (by omega) haw)
    fun v ⟨hcv, hmv, hva, hkeepv, hfv, hkv⟩ => ?_)
  have hfs := hfu.trans hfv
  have hks := (hku.trans hkv).mono (show ∀ r ∈ mmRegs ++ mmRegs, r ∈ mmRegs by decide)
  refine WP.seq (WP.mono (load_mod_ok hcv hmv hw2 hwx hw30 (by decide) (by decide) hbp hbl
    ((work_parent hc hfs hbp).trans hb) ((work_parent hc hfs hbl).trans hblen)
    (work_source hc hfs hks hbs) hb1 (by omega) hbw)
    fun z ⟨hcz, hmz, hzb, hkeepz, hfz, hkz⟩ => ?_)
  have hza := (hkeepz aX (by decide) (by decide)).trans hva
  have hzone := ((hkeepz aOne (by decide) (by decide)).trans
    (hkeepv aOne (by decide) (by decide))).trans huone
  have hzr2 := ((hkeepz aR2 (by decide) (by decide)).trans
    (hkeepv aR2 (by decide) (by decide))).trans hur2
  rw [show 128 * wx = 64 * wx + 64 * wx by omega, Nat.pow_add] at hzr2
  refine WP.mono (productCore_ok M hmz (Nat.le_refl _) hw2 (by omega) hm hodd hza hzb hzr2 hzone)
    fun t ⟨hmt, hresult, hft, hkt⟩ =>
      ⟨arrays_context hcz hft (by decide) hkt, hresult, hmt,
        (hfs.trans hfz).trans (arrays_work hft (by decide)),
        ((hks.trans hkz).trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
