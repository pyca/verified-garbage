module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public import VerifiedGarbage.Impl.Dsa.RISCV64.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Prevalidated
import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFn
import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFn
import VerifiedGarbage.Proof.Dsa.Validation
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA public-key validation on RISC-V: the contract on the registers, and the function

As on PPC64LE (`Proof/Dsa/PPC64LE/Validate/`). `vkContract`:
`vg_dsa_validate_public_key(key = a0, key_len = a1, p_len = a2, q_len = a3,
scratch = a4, scratch_len = a5)`, `pcContract`'s registers with the packed
key p||q||g||y in place of the domain. `validate_correct`: after
`vg_dsa_check_parameters`'s entry, `checkKey` leaves 1 or 0 as the key passes
`KeyOk` or not (`checkLike_ok`), which is the specification's validation
(`validate_spec`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- `vg_dsa_validate_public_key`, on the registers. -/
def vkContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let scr : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩
    s.rd = [key] ∧ s.wr = [scr] ∧ key.Disjoint scr ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a2).toNat (s.gpr .a3).toNat ∧
      (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .a2).toNat ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a4).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = if Spec.Dsa.validatePublicKeyBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .a2).toNat (s₁.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat) =
        Spec.Dsa.publicBytesLeak (s₂.gpr .a2).toNat (s₂.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat)

instance instDecidableKeyOk (m : Mem) (L : Lay) (key : Addr) : Decidable (KeyOk m L key) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem validate_spec {m : Mem} {L : Lay} {key : Addr} (hv : Spec.Dsa.lengthsValid L.pl L.ql) :
    Spec.Dsa.validatePublicKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m key (3 * L.pl + L.ql)) =
      decide (KeyOk m L key) :=
  VG.Proof.Dsa.validatePublicKeyBytes_eq hv (VG.Proof.Bignum.bytesAt_length _ _ _)
    (VG.Proof.Dsa.publicKeyBytes_at m key (Nat.le_refl _))

theorem validate_correct (s : State) (h : vkContract.pre s) :
    ∃ tr t, Exec isa Prevalidated.validate s tr t ∧ abiPreserved s t ∧ vkContract.post s t := by
  show WP isa Prevalidated.validate s fun t => abiPreserved s t ∧ vkContract.post s t
  have hL : (playOf s).Ok := playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1
  obtain ⟨hrd, hwr, dKS, -, nw, hv, hkl, -, alS, -⟩ := h
  have hplq : 3 * (playOf s).pl + (playOf s).ql = (s.gpr .a1).toNat := by simp only [playOf]; omega
  have hspec : Spec.Dsa.validatePublicKeyBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) = decide (KeyOk s.mem (playOf s) (s.gpr .a0)) := by
    rw [← hplq]; exact validate_spec hv
  have src : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr →
      Src t (playOf s) (s.gpr .a0) (3 * (playOf s).pl + (playOf s).ql) :=
    fun hr hw => psrc_of hrd dKS (Nat.le_of_eq hplq) hr hw
  unfold Prevalidated.validate
  refine WP.mono (WP.rdwr (checkLike_ok (X := checkKey) (Ok := KeyOk) hL hwr nw alS src (fun Out => ?_)
    (fun hs hr h2 hk hrest hfail => checkKey_ok hL hs hr h2 (by decide) hk hrest hfail)))
    fun w ⟨⟨⟨hp, hra⟩, w0⟩, _, _, hsp⟩ => ⟨⟨hp, hsp, hra⟩, ?_⟩
  · obtain ⟨ep, eq, eg, ey⟩ := keyVals_kept (src rfl rfl) Out
    simp only [KeyOk, ep, eq, eg, ey]
  · show ((w.gpr .a0).setWidth 32).toNat = _
    rw [w0, hspec]
    simp only [decide_eq_true_eq]

end VG.Proof.Dsa.RISCV64
