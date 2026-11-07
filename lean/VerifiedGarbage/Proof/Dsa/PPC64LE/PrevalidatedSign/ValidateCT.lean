module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Validate
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Entry
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Validate
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign

/-!
# DSA private-key validation on PPC64LE: constant time

`validatePrivate_ct`: two runs from states that satisfy `vpkContract` and
agree on its public data (the arguments' registers, the key's public part
and the result) leak the same trace. The entry is
`vg_dsa_check_parameters`'s (`pentry_taint`, `pfront_S0_of`, for the public
data `vpkvdOf`: the key's public octets), the check of the key's public part
verification's (`checkKey_rel`), then `privateChecks`, which branches on
nothing (`privateChecks_rel`), and `restore`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE

/-- A call's public data: the layout and the key's public octets. -/
def vpkvdOf (s : State) : VD := pvdN (3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat) s

/-- On entry. -/
def VPK0 (v : VD) (s : State) : Prop := vpkContract.pre s ∧ vpkvdOf s = v

theorem vpkfront_S0 {v : VD} {s : State} (h : VPK0 v s) :
    WP isa (.block Params.entry) s fun t => S0 v t ∧ KY v := by
  obtain ⟨hp, rfl⟩ := h
  have hL := vpkContract_lay hp
  obtain ⟨hrd, hwr, dKS, -, nw, -, hkl, -⟩ := hp
  exact (pfront_S0_of hL hwr nw (fun hr hw => psrc_of hrd dKS (by omega) hr hw)
    (by simp only [playOf]; omega)).mono fun _ h => ⟨h, by simp only [KY, vpkvdOf, pvdN, playOf]; omega⟩

/-- The checks of the key leave the P space's registers fixed. -/
theorem pins_K9P : Pins K9 (coreRegs ++ envRegs') := by
  intro v s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (pins_fixL _ _ fun _ => rfl : Pins K9 (coreRegs ++ [])) v s₁ s₂ h₁ h₂ r (List.mem_append_left _ hr)
  · rw [show envRegs' = (envP v).map Prod.fst from rfl] at hr
    obtain ⟨p, hm, rfl⟩ := List.mem_map.mp hr
    rw [envP_of h₁.2.2.2.1.1 p hm, envP_of h₂.2.2.2.1.1 p hm]

theorem privateChecks_rel : RelCT isa (Two K9) PrevalidatedSign.privateChecks (Two End) :=
  rel_end (two_taint _ pins_K9P (by taint_decide)) (fun _ _ h => h.1.regs.r21)
    (by rw [← Code.allInstrs_eq]; decide +kernel) (by decide +kernel)

theorem validatePrivate_rel : RelCT isa (Two VPK0) PrevalidatedSign.validate fun _ _ => True := by
  unfold PrevalidatedSign.validate
  exact RelCT.seq (two_post (pentry_taint (pins_pvd fun _ _ h => h.2)) fun _ _ h => vpkfront_S0 h)
    (RelCT.seq (checkKey_rel privateChecks_rel) (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `vpkvdOf`. -/
theorem vpkvdOf_eq {s t : State} (hs : vpkContract.pre s) (hp : vpkContract.pub s t) : vpkvdOf s = vpkvdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, hl⟩ := hp
  have hk := hs.2.2.2.2.2.2.1
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← h3, ← h4, ← h5, ← h6, Nat.min_eq_right (by omega)] at e
  simp only [vpkvdOf, pvdN, playOf, ← h3, ← h5, ← h6, ← h7, ← h8, e]

theorem validatePrivate_ct : ConstantTime isa vpkContract.pre vpkContract.pub PrevalidatedSign.validate :=
  RelCT.constantTime (validatePrivate_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vpkvdOf s, ⟨hs, rfl⟩, ⟨ht, (vpkvdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
