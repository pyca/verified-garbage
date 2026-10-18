module

public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTCode
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMainPc
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTMainPc
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPcCode
import VerifiedGarbage.Proof.Framework.X86_64.Call
meta import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_private_crt_precomputed` on x86-64: constant time but for `n`

`entry`, the modulus' check and `fail` as for `vg_rsa_private_crt`
(`crtFront_ct`), and `main` with `pre` (`crtMainPc_ct`): `crtPcCode_ct`, and
the contract's `ConstantTime` (`crtPcCode_constantTime_of`). `pre`'s pointer
and length are public; its words need not be.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Crt
open VG.Proof.MlKem.X86_64

/-- The public data of `vg_rsa_private_crt_precomputed`: `vg_rsa_private_crt`'s
and `pre`'s pointer and length. -/
structure CCPubPc where
  c : CCPub
  P : Addr
  W : Nat

/-- A state the contract allows, with the public data `p`. -/
def CCRelPc (p : CCPubPc) (s : State) : Prop :=
  crtPcContract.pre s ∧ CCEq p.c s ∧ stackArg s 12 = p.P ∧ (stackArg s 13).toNat = p.W

theorem ccRelPc_ctx : ∀ (p : CCPubPc) s, CCRelPc p s → CrtCtx s ∧ CCEq p.c s :=
  fun _ _ h => ⟨(crtCtxPc_of h.1).1, h.2.1⟩

/-- `main`'s stage with `pre`, after the head and the check of a valid
modulus. -/
theorem cc3_stagePc {p : CCPubPc} {t : State} (h : CC3 CCRelPc CCPubPc.c p t ∧ isa.eval .ne t = some false) :
    StagePc R0 ⟨p.c.m, p.P, p.W, p.c.rsp⟩ t := by
  obtain ⟨σ, xb, pb, qb, dpb, dqb, qib, hpre, hv, hσ⟩ := cc3_stage ccRelPc_ctx h
  subst hσ
  obtain ⟨⟨s, t₁, ⟨hs, he, hP, hW⟩, h₁, hm, k, -⟩, -⟩ := h
  obtain ⟨-, hps, hW'⟩ := crtCtxPc_of hs
  obtain ⟨hsp, hB, hZ, hk, -, -, -, -, -, -, -, -, hpl, hql, -⟩ := he
  have i : InScr (stackArg s 10) ((stackArg s 11).toNat * 8) s.mem t.mem := by rw [hm]; exact h₁.inScr
  have kk := h₁.keep.trans k
  have hp := hps.congrK i kk (by decide)
  rw [hB, hZ, hP, hW] at hp
  have ha : PreAt p.c.m.B p.c.m.Z p.P p.W p.c.rsp t := ⟨hp, (kk.gpr (by decide)).trans hsp⟩
  refine ⟨t, xb, pb, qb, dpb, dqb, qib, hpre, hv, ha, ?_, rfl, ha⟩
  show 2 * ((p.c.m.k + 7) / 8) + wsWords p.c.m.pl + wsWords p.c.m.ql ≤ p.W
  rw [← hW, hW', ← hk, ← hpl, ← hql]
  unfold Spec.Rsa.privatePrecomputedWords Spec.Rsa.precomputedWords Spec.Rsa.primeWords Spec.Rsa.modulusWords
    wsWords
  omega

/-- Code constant time from `CCRelPc` is constant time for the contract. -/
theorem ccRelPc_constantTime {c : Prog isa} (h : RelCT isa (Two CCRelPc) c fun _ _ => True) :
    ConstantTime isa crtPcContract.pre crtPcContract.pub c := by
  refine RelCT.constantTime (h.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ =>
    ⟨⟨ccPubOf s₁, stackArg s₁ 12, (stackArg s₁ 13).toNat⟩, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, a12, a13, hn, -⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, ⟨r .rsp (by decide), a10.symm, by rw [← a11]; rfl, by rw [r .rcx (by decide)]; rfl,
      r .rdi (by decide), r .rdx (by decide), r .r8 (by decide), a0.symm, a2.symm, a4.symm, a6.symm, a8.symm,
      by rw [← a1]; rfl, by rw [← a3]; rfl, hn.symm⟩, a12.symm, by rw [← a13]⟩

/-- `main` with `pre` constant time from its stage makes the code constant
time from `CCRelPc`. -/
theorem crtFrontPc_ct {main : Prog isa} (h : RelCT isa (Two (StagePc R0)) main fun _ _ => True) :
    RelCT isa (Two CCRelPc) (.seq (.block (Crt.entry ++ ([.mov .rdx (.mem (hdr sN)), .mov .rcx (.mem (hdr sK))] :
      List Instr) ++ invalid)) (.ite .ne fail main)) fun _ _ => True :=
  crtFront_ct CCRelPc CCPubPc.c ccRelPc_ctx (h.mono (fun _ _ h => two_bind
    (fun p _ _ h₁ h₂ => ⟨⟨p.c.m, p.P, p.W, p.c.rsp⟩, cc3_stagePc h₁, cc3_stagePc h₂⟩) h) fun _ _ h => h)

variable (M : Mont) (E : CrtExpL M)

/-- `vg_rsa_private_crt_precomputed` leaks the same in runs that agree on the
public data, given that `main`'s parts do. -/
theorem crtPcCode_ct (hS : SetupCT) (hC : ChecksCT) (hQ : QPhasePcCT M E) (hP : PPhasePcCT M E) :
    RelCT isa (Two CCRelPc) (Crt.code M.mm E.code true) fun _ _ => True :=
  crtFrontPc_ct (crtMainPc_ct M E hS hC hQ hP)

/-- `vg_rsa_private_crt_precomputed` is constant time but for `n`, given that
`main`'s parts are. -/
theorem crtPcCode_constantTime_of (hS : SetupCT) (hC : ChecksCT) (hQ : QPhasePcCT M E) (hP : PPhasePcCT M E) :
    ConstantTime isa crtPcContract.pre crtPcContract.pub (Crt.code M.mm E.code true) :=
  ccRelPc_constantTime (crtPcCode_ct M E hS hC hQ hP)

end VG.Proof.Bignum.X86_64
