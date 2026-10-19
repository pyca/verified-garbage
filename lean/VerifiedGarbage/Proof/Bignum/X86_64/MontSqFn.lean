module

public import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
public import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
public import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontSq
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
meta import VerifiedGarbage.Impl.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyVerified
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazyCT
meta import VerifiedGarbage.Proof.Bignum.X86_64.MontFnLazy
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Lazy squarings by calls of `vg_rsa_lazy_mont_mul` and `vg_rsa_lazy_mont_mul_adx`

`MontS.fnLazy` and `MontS.fnLazyAdx`: the squarings of `aY` by calls of the
lazy Montgomery multiplications, inlined, whose results are below `R`. A call
of `vg_rsa_lazy_mont_mul`, inlined, is `vg_rsa_mont_mul`'s (`mmFnBase`),
whose timing `Mont.fnBase` already proves.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The call of `vg_rsa_lazy_mont_mul_adx`, inlined. -/
def mmFnAdxLazy (o a b : Nat) : Prog isa := (call "vg_rsa_lazy_mont_mul_adx" mulAdxLazy o a b).inline

theorem mmFnAdxLazy_eq (o a b : Nat) : mmFnAdxLazy o a b = .seq (.block (args o a b)) mulAdxLazy := rfl

theorem mmFnAdxLazy_ct {o a b : Nat} (op : Opnds o a b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.seq (.block (args o a b)) (.block (enter ++ slotsIn))) hc).isSome = true) :
    RelCT isa (Two GoodW) (mmFnAdxLazy o a b) fun _ _ => True := by
  rw [mmFnAdxLazy_eq]
  unfold mulAdxLazy
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := fun L s => AdxMid ⟨L.B, L.Z, L.w, o, a, b⟩ s) [.rdi] pins_goodW h
    fun L s ⟨_, hg, hZ⟩ => ?_) (two_map (fun L : Ws => (⟨L.B, L.Z, L.w, o, a, b⟩ : CallData)) (fun _ _ h => h)
      adxTailLazy_ct))
  refine WP.seq (WP.mono (fnArgs_ok s o a b) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
  exact WP.mono (adxHead_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op.1 op.2.1
    op.2.2.1 hdx hcx h8) fun u ⟨hm', hdx', hcx', h8', k', _⟩ =>
      AdxMid.of_head (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op hm' hdx' hcx' h8' k'

/-- Squarings by calls of `vg_rsa_lazy_mont_mul`, inlined: `vg_rsa_mont_mul`'s
code, whose result is below `R` for any operand below `R`. -/
def MontS.fnLazy : MontS where
  mm := mmFnBase aY aY aY
  bd _ R := R
  le h := h
  ok hg hZ hw hw' hinv _ := by
    rw [mmFnBase_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv ⊢
    refine WP.mono (MontFn.mulBaseLazy_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr)
      hZ hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hdx hcx h8
      hinv) fun t' ⟨h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      wv_lt _ _ _ _, h2, h3, (k.trans k').mono (by decide)⟩
  ct := Mont.fnBase.ct (.inr (.inl ⟨rfl, rfl, rfl⟩))

/-- Squarings by calls of `vg_rsa_lazy_mont_mul_adx`, inlined. -/
def MontS.fnLazyAdx : MontS where
  mm := mmFnAdxLazy aY aY aY
  bd _ R := R
  le h := h
  ok hg hZ hw hw' hinv _ := by
    rw [mmFnAdxLazy_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv ⊢
    refine WP.mono (mulAdxLazy_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ hw hw'
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hdx hcx h8 hinv) fun t' ⟨h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      wv_lt _ _ _ _, h2, h3, (k.trans k').mono (by decide)⟩
  ct := by exact mmFnAdxLazy_ct (by unfold Opnds; decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
