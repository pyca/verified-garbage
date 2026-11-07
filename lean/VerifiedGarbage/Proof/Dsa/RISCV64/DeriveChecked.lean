module

public import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public import VerifiedGarbage.Impl.Dsa.RISCV64.Generate
import VerifiedGarbage.Proof.Dsa.RISCV64.DeriveFn
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.PrevalidatedFn
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key derivation for a checked domain on RISC-V: the function

`dcContract`: `vg_dsa_derive_key_checked` (`Generate.deriveChecked`), with
`vg_dsa_derive_key`'s arguments, result and public data (`dContract`), for a
domain that passes the specification's checks (`checkParametersBytes`).
`setupParams_ok`: for a domain that passes `ParamsOk`,
`Prevalidated.setup rest fail` runs `rest` from what `checkParams` leaves
for it (`Checked`), as `setup_ok` does for a valid key.
`deriveChecked_correct`: the rest is the derivation's (`deriveWith_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_derive_key_checked`, on the registers and the stack. -/
def dcContract : Contract isa where
  pre s := dContract.pre s ∧ Spec.Dsa.checkParametersBytes (s.gpr .a4).toNat (s.gpr .a6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) = true
  post := dContract.post
  pub := dContract.pub

theorem setupParams_ok {s : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (2 * L.pl + L.ql))
    (hP : ParamsOk s.mem L key)
    (hrest : ∀ t, ParamsOk s.mem L key → Checked s t L key sig d → Kept L s.mem t.mem → Keep cpRegs s t →
      WP isa rest t Q) :
    WP isa (Prevalidated.setup rest fail) s Q := by
  have hSz : SizesOk s.mem L key := hP.1.1
  have hp2 : 2 ≤ pOf s.mem L key := (VG.Proof.Dsa.supported_bounds hSz).1
  have hpo : pOf s.mem L key % 2 = 1 := hP.1.2.2
  unfold Prevalidated.setup
  refine sizes_ok hL hs hr hlen hk hd (fun t₁ _ o₁ w₁ k₁ hr₁ => ?_) (fun _ hn _ _ _ => absurd hSz hn)
  have K₁ : Kept L s.mem t₁.mem := Kept.ofHdr hL o₁
  obtain ⟨ep₁, eq₁, -⟩ := params_kept hk K₁
  refine WP.seq (WP.mono (setupQ_ok hL (hs.congr k₁.2.2) hr₁ (hk.keep k₁.2.1 k₁.2.2))
    fun t₂ ⟨⟨_, q0₂, qtop₂, qb₂⟩, k₂⟩ => ?_)
  have B₂ := qb₂.body hL
  have K₂ := K₁.trans (Kept.ofBody hL B₂)
  obtain ⟨ep₂, -, -⟩ := params_kept hk K₂
  have k₁₂ := k₁.trans k₂
  refine WP.seq (WP.mono (setupP_ok hL (hs.congr k₁₂.2.2) (hr₁.keep k₂ B₂) (hk.keep k₁₂.2.1 k₁₂.2.2)
      (by rw [ep₂]; exact hp2) (by rw [ep₂]; exact hpo)) fun t₃ ⟨⟨ip₃, p0₃, ptop₃, inv₃, _, p24₃, pb₃⟩, k₃⟩ => ?_)
  rw [ep₂] at p0₃ p24₃
  rw [eq₁] at q0₂
  have B₃ := pb₃.body hL
  refine hrest t₃ hP ⟨ip₃, hs.congr (k₁₂.trans k₃).2.2, (hr₁.keep k₂ B₂).keep k₃ B₃, p0₃, ptop₃, inv₃, p24₃,
    (pb₃.arrQ hL).trans q0₂, (pb₃.qtop hL).trans qtop₂, ?_⟩ (K₂.trans (Kept.ofBody hL B₃))
    ((k₁₂.trans k₃).mono (by decide))
  rw [B₃.word (by decide), B₂.word (by decide)]; exact w₁

/-- The domain passes `ParamsOk`, from the precondition. -/
theorem dcParams {s : State} (h : dcContract.pre s) : ParamsOk s.mem (dlayOf s) (s.gpr .a2) := by
  obtain ⟨hd, hc⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, hpl, -, -, -⟩ := hd
  have e := checkParameters_spec (m := s.mem) (L := dlayOf s) (key := s.gpr .a2) hv
  rw [show 2 * (dlayOf s).pl + (dlayOf s).ql = (s.gpr .a3).toNat by simp only [dlayOf] at hpl ⊢; omega] at e
  exact of_decide_eq_true (e.symm.trans hc)

theorem deriveChecked_correct (s : State) (h : dcContract.pre s) :
    ∃ tr t, Exec isa Generate.deriveChecked s tr t ∧ abiPreserved s t ∧ dcContract.post s t := by
  have hP := dcParams h
  have hL := dlayOf_ok h.1
  exact deriveWith_ok (X := Prevalidated.setup) s h.1 fun Out hs hr hl hk hrest _ => by
    refine setupParams_ok (d := 0) hL hs hr hl (by decide) hk ?_ hrest
    simp only [ParamsOk, pOf, qOf, gOf] at hP ⊢
    rw [(hk.take (k := (dlayOf s).pl) (by omega)).bytes Out (by omega),
      (hk.sub (o := (dlayOf s).pl) (k := (dlayOf s).ql) (by omega)).bytes Out (by omega),
      (hk.sub (o := (dlayOf s).pl + (dlayOf s).ql) (k := (dlayOf s).pl) (by omega)).bytes Out (by omega)]
    exact hP

end VG.Proof.Dsa.RISCV64
