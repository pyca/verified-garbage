module

import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Base

/-!
# DSA domain checks on PPC64LE: constant time

`checkParameters_ct`: two runs from states that satisfy `pcContract` and
agree on its public data (the arguments' registers and the domain, all of it
public) leak the same trace. The entry (`pentry_rel`), the checks of the
domain shared with verification and signing (`sizes_rel`,
`paramsTail_rel`, for the public data `pvdOf`: the domain's octets, without
y), the result and `restore` follow one another.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- A call's public data: the layout, the domain and its octets; no
signature, digest or `out`. -/
def pvdOf (s : State) : VD :=
  ⟨playOf s, s.gpr .r3, 0, 0, 0,
    Spec.Rsa.bytesAt s.mem (s.gpr .r3) (2 * (s.gpr .r5).toNat + (s.gpr .r6).toNat),
    2 * (s.gpr .r5).toNat + (s.gpr .r6).toNat, 0, none, 2 * (s.gpr .r5).toNat + (s.gpr .r6).toNat⟩

/-- On entry. -/
def PC0 (v : VD) (s : State) : Prop := pcContract.pre s ∧ pvdOf s = v

theorem pins_PC0 : Pins PC0 [.r3, .r5, .r6, .r7] := by
  intro v s₁ s₂ h₁ h₂ r hr
  obtain ⟨-, e₁⟩ := h₁
  obtain ⟨-, e₂⟩ := h₂
  have := congrArg VD.key (e₁.trans e₂.symm)
  have hL := congrArg VD.L (e₁.trans e₂.symm)
  simp only [pvdOf, playOf, Lay.mk.injEq] at this hL
  obtain ⟨h7, -, h5, h6⟩ := hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact this
  · exact BitVec.eq_of_toNat_eq h5
  · exact BitVec.eq_of_toNat_eq h6
  · exact h7

/-- A buffer of no octets. -/
theorem src_zero (s : State) (L : Lay) (D : Addr) {n : Nat} (h : n = 0) : Src s L D n :=
  ⟨fun i hi => absurd hi (by omega), fun i hi => absurd hi (by omega)⟩

theorem pfront_S0 {v : VD} {s : State} (h : PC0 v s) : WP isa (.block Params.entry) s (S0 v) := by
  obtain ⟨hp, rfl⟩ := h
  have hL := playOf_ok hp
  have hZ := hL.z256
  refine WP.mono (pfront_ok hp) fun t ⟨⟨hr, scr, r2, _, out⟩, k⟩ => ?_
  have Out : Outside (playOf s).S 0 (playOf s).Z s.mem t.mem :=
    out.mono (Nat.le_refl _) (by simp only [playOf] at hZ ⊢; omega)
  exact ⟨⟨hL, hr, scr, pre_psrc hp k.rd k.wr, src_zero _ _ _ rfl, src_zero _ _ _ rfl,
    (pre_psrc hp rfl rfl).kept Out, pre_psrc hp k.rd k.wr, (fun _ h => nomatch h), (fun h => nomatch h),
    Nat.le_refl _⟩, r2, fixL_nil t, trivial⟩

theorem pentry_rel : RelCT isa (Two PC0) (.block Params.entry) (Two S0) :=
  two_post (two_taint _ pins_PC0 (by taint_decide)) fun _ _ h => pfront_S0 h

theorem one_rel {Φ : VD → State → Prop} (h : ∀ v s, Φ v s → Base v s) :
    RelCT isa (Two Φ) (.block [.li .r3 1]) (Two End) :=
  rel_end (two_taint [.r21] (fun v s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      rw [(h v _ h₁).regs.r21, (h v _ h₂).regs.r21])
    (by taint_decide)) (fun v s hs => (h v s hs).regs.r21) (by decide) (by decide)

theorem checkParams_rel :
    RelCT isa (Two S0) (checkParams (.block [.li .r3 1]) (.block [.li .r3 0])) (Two End) :=
  (sizes_rel (G := fun _ => True) (paramsTail_rel (one_rel fun _ _ h => h.1.1)
      fun _ h => fail_rel fun v s h' => (h v s h').1) fun _ h => fail_rel fun v s h' => (h v s h').1).mono
    (fun _ _ => two_mono fun _ _ h => ⟨h, trivial⟩) fun _ _ h => h

theorem checkParameters_rel : RelCT isa (Two PC0) Params.checkParameters fun _ _ => True := by
  unfold Params.checkParameters
  exact RelCT.seq pentry_rel (RelCT.seq checkParams_rel (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `pvdOf`. -/
theorem pvdOf_eq {s t : State} (hs : pcContract.pre s) (hp : pcContract.pub s t) : pvdOf s = pvdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, hl⟩ := hp
  have e := map_toNat_inj hl
  have hk := hs.2.2.2.2.2.2.1
  rw [← h3, ← h4, hk] at e
  simp only [pvdOf, playOf, ← h3, ← h5, ← h6, ← h7, ← h8, e]

theorem checkParameters_ct : ConstantTime isa pcContract.pre pcContract.pub Params.checkParameters :=
  RelCT.constantTime (checkParameters_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨pvdOf s, ⟨hs, rfl⟩, ⟨ht, (pvdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
