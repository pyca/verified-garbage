import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedScalars
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (SM' EM' RM' UM VM U V)

variable {c : Cfg}

/-- Values initialized immediately before inversion of the public signature. -/
structure InverseInput (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  mod : ModOkA c.MN' size c.C.n s.mem base
  lt : wordsVal s.mem base (c.sl KM) c.n<c.C.n
  val : toM c.C.n (2^(64*c.n)) (wordsVal s.mem base (c.sl KM) c.n)=Fin.ofNat c.C.n (sigS c s₀)

theorem scalarInput_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State}
    (hF : Front c s₀ base g s) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) (.block [])) s (InverseInput c s₀ base) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hF.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have F := hF.fixed
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have hr2lt : ∀ {m : Mem}, wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n →
      wordsVal m base (c.sl R2N) c.n < c.C.n := fun h => by rw [h]; exact Nat.mod_lt _ (by omega)
  rw [scalars_eq]
  -- The checks.
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono_syms (checkRange_ok c hF.scr h0 (sl_le c h7 (i := K) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf (sl_mod8 c K) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun s₁ ⟨_, k₁, O₁⟩ _ => ?_
  have hs₁ := hF.scr.of_keepRegs k₁ (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₁ i = sv c base s i := fun hi hf =>
    sv_flag O₁ h0 h7 hn hi hf
  refine WP.mono_syms (checkRange_ok c hs₁ h0 (sl_le c h7 (i := PT) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf (sl_mod8 c PT) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun s₂ ⟨_, k₂, O₂⟩ _ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_flag O₂ h0 h7 hn hi hf).trans (v₁ hi hf)
  have U₂ : Unch base [(c.sl FLAG, 8)] s.mem s₂.mem := by
    have := O₁.unch.trans O₂.unch
    exact this.mono fun w hw => by simpa using hw
  have F₂ := F.unch h7 hn fixedOk_flag U₂
  -- `s R mod n`.
  refine WP.mono_syms (mulN_ok hc hs₂ (modN_of hc F₂.mn) (o := SM') (a := PT) (b := R2N) (by decide) (by decide)
    (by decide) (hr2lt F₂.r2n) (by decide)) fun s₃ ⟨hs₃, M₃, _, _, _, _, _, lt₃, e₃⟩ _ => ?_
  have sm₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ SM') = Fin.ofNat c.C.n (sigS c s₀) := by
    rw [toM_r2 hnR (by rw [e₃, show sv c base s₂ R2N = _ from F₂.r2n]), v₂ (by decide) (by decide), hF.pt]
  exact WP.block_nil ⟨hs₃,M₃,lt₃,sm₃⟩

def beforeInverse (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) (.block [])

theorem beforeInverse_ok (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (beforeInverse c) s₀ (InverseInput c s₀ (s₀.gpr .x3)) := by
  exact front_ok hc hp fun _ _ _ hf => scalarInput_ok hc hf

theorem beforeInverse_ct : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (beforeInverse p256) := by
  jac_reg_ct [.x0,.x1,.x2,.x3]

theorem InverseInput.eq {s₀ t₀ s t : State} {base : Addr}
    (hc : CfgOk c) (hp : JacPublic c s₀ t₀)
    (hs : InverseInput c s₀ base s) (ht : InverseInput c t₀ base t) :
    wordsVal s.mem base (c.sl KM) c.n=wordsVal t.mem base (c.sl KM) c.n := by
  have he := hs.val.trans ((congrArg (Fin.ofNat c.C.n) hp.signature.2).trans ht.val.symm)
  have hu := mul_rinv (unitMod_pow_two hc.n_odd (64*c.n))
  have hf : Fin.ofNat c.C.n (wordsVal s.mem base (c.sl KM) c.n)=
      Fin.ofNat c.C.n (wordsVal t.mem base (c.sl KM) c.n) := by
    unfold toM at he
    grind
  have hv := congrArg Fin.val hf
  simpa only [Fin.val_ofNat,Nat.mod_eq_of_lt hs.lt,Nat.mod_eq_of_lt ht.lt] using hv

end VG.Proof.Ecdsa.Verify.AArch64
