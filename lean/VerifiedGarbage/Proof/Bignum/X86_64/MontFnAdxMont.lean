import VerifiedGarbage.Proof.Bignum.X86_64.MontFnAdxCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# `vg_rsa_mont_mul_adx` as the Montgomery multiplication of the RSA code

Calls of `vg_rsa_mont_mul_adx`, inlined (`Mont.fnAdx`), for the proofs of
its callers (`Verified.of_inline`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.MontFn
open VG.Proof.MlKem.X86_64

/-- The call of `vg_rsa_mont_mul_adx`, inlined: what calls of it run as. -/
def mmFnAdx (o a b : Nat) : Prog isa := (call "vg_rsa_mont_mul_adx" mulAdx o a b).inline

theorem mmFnAdx_eq (o a b : Nat) : mmFnAdx o a b = .seq (.block (args o a b)) mulAdx := rfl

theorem mmFnAdx_ct {o a b : Nat} (op : Opnds o a b) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (h : (taint.check (Taint.ofRegs [.rdi]) (.seq (.block (args o a b)) (.block (enter ++ slotsIn))) hc).isSome = true) :
    RelCT isa (Two GoodW) (mmFnAdx o a b) fun _ _ => True := by
  rw [mmFnAdx_eq]
  unfold mulAdx
  refine RelCT.assoc (RelCT.seq (two_piece (Ψ := fun L s => AdxMid ⟨L.B, L.Z, L.w, o, a, b⟩ s) [.rdi] pins_goodW h
    fun L s ⟨_, hg, hZ⟩ => ?_) (two_map (fun L : Ws => (⟨L.B, L.Z, L.w, o, a, b⟩ : CallData)) (fun _ _ h => h)
      adxTail_ct))
  refine WP.seq (WP.mono (fnArgs_ok s o a b) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
  exact WP.mono (adxHead_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op.1 op.2.1
    op.2.2.1 hdx hcx h8) fun u ⟨hm', hdx', hcx', h8', k', _⟩ =>
      AdxMid.of_head (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ op hm' hdx' hcx' h8' k'

/-- Montgomery multiplication by calls of `vg_rsa_mont_mul_adx`, as inlined code. -/
def Mont.fnAdx : Mont where
  mm := mmFnAdx
  ok hg hZ hw hw' _ _ _ ho ha hb d1 d2 d3 d5 d4 d6 hinv hB := by
    rw [mmFnAdx_eq]
    refine WP.seq (WP.mono (fnArgs_ok _ _ _ _) fun t ⟨hdx, hcx, h8, hm, k⟩ => ?_)
    rw [← hm] at hinv hB ⊢
    refine WP.mono (mulAdx_ok (hg.scr.congr k.2.2) ((k.gpr (by decide)).trans hg.rdi) (hm ▸ hg.hdr) hZ hw hw'
      ho ha hb d1 d2 d3 d5 d4 d6 hdx hcx h8 hinv hB) fun t' ⟨h1, h2, h3, k', _⟩ => ?_
    exact ⟨⟨hg.scr.congr ((k.trans k').2.2), ((k.trans k').gpr (by decide)).trans hg.rdi, h3.hdr (hm ▸ hg.hdr)⟩,
      h1, h2, h3, (k.trans k').mono (by decide)⟩
  ct := by
    intro o a b h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    exact mmFnAdx_ct (by unfold Opnds; decide) (by taint_decide)

end VG.Proof.Bignum.X86_64
