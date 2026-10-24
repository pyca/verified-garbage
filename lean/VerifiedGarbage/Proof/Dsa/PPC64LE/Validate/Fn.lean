module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Spec
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey

/-!
# DSA public-key validation on PPC64LE: the function

`validate_correct`: `vg_dsa_validate_public_key` meets `vkContract`. After
`vg_dsa_check_parameters`'s entry, `checkKey` leaves 1 or 0 as the key passes
`KeyOk` or not (`checkLike_ok`, with `checkKey_ok`), which is the
specification's validation (`validate_spec`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

theorem validate_correct (s : State) (h : vkContract.pre s) :
    ∃ tr t, Exec isa Prevalidated.validate s tr t ∧ abiPreserved s t ∧ vkContract.post s t := by
  show WP isa Prevalidated.validate s fun t => abiPreserved s t ∧ vkContract.post s t
  have hL := vkContract_lay h
  obtain ⟨hrd, hwr, dKS, -, nw, hv, hkl, -⟩ := h
  have hplq : 3 * (playOf s).pl + (playOf s).ql = (s.gpr .r4).toNat := by simp only [playOf]; omega
  have hspec : Spec.Dsa.validatePublicKeyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) = decide (KeyOk s.mem (playOf s) (s.gpr .r3)) := by
    rw [← hplq]; exact validate_spec hv
  have src : ∀ {t : State}, t.rd = s.rd → t.wr = s.wr →
      Src t (playOf s) (s.gpr .r3) (3 * (playOf s).pl + (playOf s).ql) :=
    fun hr hw => psrc_of hrd dKS (Nat.le_of_eq hplq) hr hw
  unfold Prevalidated.validate
  refine WP.mono (checkLike_ok (X := checkKey) (Ok := KeyOk) hL hwr nw src (fun Out => ?_)
    (fun hs hr h2 hk hrest hfail => checkKey_ok hL hs hr h2 (by decide) hk hrest hfail))
    fun w ⟨hab, w3⟩ => ⟨hab, ?_⟩
  · obtain ⟨ep, eq, eg, ey⟩ := key_kept (src rfl rfl) Out
    simp only [KeyOk, ep, eq, eg, ey]
  · show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, hspec]
    simp only [decide_eq_true_eq]

end VG.Proof.Dsa.PPC64LE
