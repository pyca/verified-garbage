module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Entry
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Contract
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated

/-!
# DSA public-key validation on PPC64LE: constant time

`validate_ct`: two runs from states that satisfy `vkContract` and agree on its
public data (the arguments' registers and the key, all of it public) leak
the same trace. The entry is `vg_dsa_check_parameters`'s (`pentry_taint`,
`pfront_S0_of`, for the public data `vkvdOf`: the key's octets), the check
of the key verification's (`checkKey_rel`), then the result and `restore`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE

/-- A call's public data: the layout and the key's octets. -/
def vkvdOf (s : State) : VD := pvdN (3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat) s

/-- On entry. -/
def VK0 (v : VD) (s : State) : Prop := vkContract.pre s ∧ vkvdOf s = v

theorem vfront_S0 {v : VD} {s : State} (h : VK0 v s) :
    WP isa (.block Params.entry) s fun t => S0 v t ∧ KY v := by
  obtain ⟨hp, rfl⟩ := h
  have hL := vkContract_lay hp
  obtain ⟨hrd, hwr, dKS, -, nw, -, hkl, -⟩ := hp
  exact (pfront_S0_of hL hwr nw (fun hr hw => psrc_of hrd dKS (by omega) hr hw)
    (by simp only [playOf]; omega)).mono fun _ h => ⟨h, by simp only [KY, vkvdOf, pvdN, playOf]; omega⟩

theorem validate_rel : RelCT isa (Two VK0) Prevalidated.validate fun _ _ => True := by
  unfold Prevalidated.validate
  exact RelCT.seq (two_post (pentry_taint (pins_pvd fun _ _ h => h.2)) fun _ _ h => vfront_S0 h)
    (RelCT.seq (checkKey_rel (one_rel fun _ _ h => h.1)) (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `vkvdOf`. -/
theorem vkvdOf_eq {s t : State} (hs : vkContract.pre s) (hp : vkContract.pub s t) : vkvdOf s = vkvdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.1
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at hl
  have e := map_toNat_inj hl
  rw [← h3, ← h4, ← h5, ← h6, Nat.min_eq_right (by omega)] at e
  simp only [vkvdOf, pvdN, playOf, ← h3, ← h5, ← h6, ← h7, ← h8, e]

theorem validate_ct : ConstantTime isa vkContract.pre vkContract.pub Prevalidated.validate :=
  RelCT.constantTime (validate_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vkvdOf s, ⟨hs, rfl⟩, ⟨ht, (vkvdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
