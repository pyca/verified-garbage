module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Setup
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Spec
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn

/-!
# DSA prevalidated verification on PPC64LE: the function

`prevalidated_correct`: `vg_dsa_verify_prevalidated` meets `vpContract`. The
key passes `KeyOk` (`validate_spec`), so after `vg_dsa_verify`'s entry,
`Prevalidated.setup` leaves what `checkKey` would (`setup_ok`), and the rest
is verification's (`verifyLike_ok`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

theorem prevalidated_correct (s : State) (h : vpContract.pre s) :
    ∃ tr t, Exec isa Prevalidated.verify s tr t ∧ abiPreserved s t ∧ vpContract.post s t := by
  show WP isa Prevalidated.verify s fun t => abiPreserved s t ∧ vContract.post s t
  obtain ⟨hp, hval⟩ := h
  have hv := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hkl := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hK : KeyOk s.mem (layOf s) (s.gpr .r3) := by
    have e := validate_spec (m := s.mem) (L := layOf s) (key := s.gpr .r3) hv
    rw [show 3 * (layOf s).pl + (layOf s).ql = (s.gpr .r4).toNat by simp only [layOf]; omega] at e
    exact of_decide_eq_true (e.symm.trans hval)
  unfold Prevalidated.verify
  exact verifyLike_ok (X := Prevalidated.setup) (V := True)
    (fun hL hs hr h2 hd hk hV hrest _ => setup_ok hL hs hr h2 hd hk (hV trivial) hrest) hp fun _ => hK

end VG.Proof.Dsa.PPC64LE
