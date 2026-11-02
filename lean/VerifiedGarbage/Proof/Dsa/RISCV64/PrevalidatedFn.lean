module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.RISCV64.ValidateFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA prevalidated verification on RISC-V

As on PPC64LE (`Proof/Dsa/PPC64LE/Prevalidated/`). `vpContract`:
`vg_dsa_verify_prevalidated`, with `vg_dsa_verify`'s arguments, result and
public data (`vContract`), for a key that passes the specification's
validation. `setup_ok`: for a key that passes `KeyOk`,
`Prevalidated.setup rest fail` runs `rest` from what `checkKey` leaves for it
(`Checked`). `prevalidated_correct`: the rest is verification's
(`verifyLike_ok`).
-/

-- separate module: as `VerifyFn` from `VerifyImplies`, so that the constant-time proof and the registration
-- can import the correctness proof without the contract tactics `PrevalidatedImplies` uses.

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_verify_prevalidated`, on the registers and the stack. -/
def vpContract : Contract isa where
  pre s := vContract.pre s ∧ Spec.Dsa.validatePublicKeyBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) = true
  post := vContract.post
  pub := vContract.pub

theorem setup_ok {s : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop}
    {rest fail : Prog isa} (hL : L.Ok) (hs : ScrL s L) (hr : Regs s L key sig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql 0 d) (hd : d < 2 ^ 16) (hk : Src s L key (3 * L.pl + L.ql))
    (hK : KeyOk s.mem L key)
    (hrest : ∀ t, KeyOk s.mem L key → Checked s t L key sig d → Kept L s.mem t.mem → Keep ckRegs s t →
      WP isa rest t Q) :
    WP isa (Prevalidated.setup rest fail) s Q := by
  have hk2 : Src s L key (2 * L.pl + L.ql) := hk.take (by omega)
  have hSz : SizesOk s.mem L key := hK.1.1
  have hp2 : 2 ≤ pOf s.mem L key := (VG.Proof.Dsa.supported_bounds hSz).1
  have hpo : pOf s.mem L key % 2 = 1 := hK.1.2.2
  have hq0 : 0 < qOf s.mem L key := by have := VG.Proof.Dsa.supported_bounds hSz; omega
  unfold Prevalidated.setup
  refine sizes_ok hL hs hr hlen hk2 hd (fun t₁ _ o₁ w₁ k₁ hr₁ => ?_) (fun _ hn _ _ _ => absurd hSz hn)
  have K₁ : Kept L s.mem t₁.mem := Kept.ofHdr hL o₁
  obtain ⟨ep₁, eq₁, -⟩ := params_kept hk2 K₁
  refine WP.seq (WP.mono (setupQ_ok hL (hs.congr k₁.2.2) hr₁ (hk2.keep k₁.2.1 k₁.2.2))
    fun t₂ ⟨⟨_, q0₂, qtop₂, qb₂⟩, k₂⟩ => ?_)
  have B₂ := qb₂.body hL
  have K₂ := K₁.trans (Kept.ofBody hL B₂)
  obtain ⟨ep₂, -, -⟩ := params_kept hk2 K₂
  have k₁₂ := k₁.trans k₂
  refine WP.seq (WP.mono (setupP_ok hL (hs.congr k₁₂.2.2) (hr₁.keep k₂ B₂) (hk2.keep k₁₂.2.1 k₁₂.2.2)
      (by rw [ep₂]; exact hp2) (by rw [ep₂]; exact hpo)) fun t₃ ⟨⟨ip₃, p0₃, ptop₃, inv₃, _, p24₃, pb₃⟩, k₃⟩ => ?_)
  rw [ep₂] at p0₃ p24₃
  rw [eq₁] at q0₂
  have B₃ := pb₃.body hL
  refine hrest t₃ hK ⟨ip₃, hs.congr (k₁₂.trans k₃).2.2, (hr₁.keep k₂ B₂).keep k₃ B₃, p0₃, ptop₃, inv₃, p24₃,
    (pb₃.arrQ hL).trans q0₂, (pb₃.qtop hL).trans qtop₂, ?_⟩ (K₂.trans (Kept.ofBody hL B₃))
    ((k₁₂.trans k₃).mono (by decide))
  rw [B₃.word (by decide), B₂.word (by decide)]; exact w₁

theorem prevalidated_correct (s : State) (h : vpContract.pre s) :
    ∃ tr t, Exec isa Prevalidated.verify s tr t ∧ abiPreserved s t ∧ vpContract.post s t := by
  show WP isa Prevalidated.verify s fun t => abiPreserved s t ∧ vContract.post s t
  obtain ⟨hp, hval⟩ := h
  have hv := hp.2.2.2.2.2.2.2.2.2.2.1
  have hkl := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hK : KeyOk s.mem (layOf s) (s.gpr .a0) := by
    have e := validate_spec (m := s.mem) (L := layOf s) (key := s.gpr .a0) hv
    rw [show 3 * (layOf s).pl + (layOf s).ql = (s.gpr .a1).toNat by simp only [layOf]; omega] at e
    exact of_decide_eq_true (e.symm.trans hval)
  suffices main : WP isa Prevalidated.verify s fun t =>
      ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ vContract.post s t from
    WP.mono (WP.rdwr main) fun t ⟨⟨⟨hp, hra⟩, hpost⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, hpost⟩
  unfold Prevalidated.verify
  exact verifyLike_ok (X := Prevalidated.setup) (V := True)
    (fun hL hs hr h2 hd hk hV hrest _ => setup_ok hL hs hr h2 hd hk (hV trivial) hrest) hp fun _ => hK

end VG.Proof.Dsa.RISCV64
