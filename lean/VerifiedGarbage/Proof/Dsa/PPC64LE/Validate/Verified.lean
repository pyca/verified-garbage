module

public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Spec
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.CT
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
meta import VerifiedGarbage.Spec.Dsa.Prevalidated

/-! ### `Dsa.PPC64LE.Validate.Contract`, which only this module used -/

section

/-!
# DSA public-key validation on PPC64LE: the contract on the registers

`vkContract`: `vg_dsa_validate_public_key(key = r3, key_len = r4, p_len = r5,
q_len = r6, scratch = r7, scratch_len = r8)`, `pcContract`'s registers with
the packed key p||q||g||y in place of the domain.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- `vg_dsa_validate_public_key`, on the registers. -/
def vkContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let scr : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩
    s.rd = [key] ∧ s.wr = [scr] ∧ key.Disjoint scr ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r8).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = if Spec.Dsa.validatePublicKeyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .r5).toNat (s₁.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat) =
        Spec.Dsa.publicBytesLeak (s₂.gpr .r5).toNat (s₂.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat)

theorem vkContract_lay {s : State} (h : vkContract.pre s) : (playOf s).Ok :=
  playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Validate.Implies`, which only this module used -/

section

/-!
# `vg_dsa_validate_public_key` on PPC64LE: the contract on the registers

`validate_implies`: `vkContract` implies the shared contract.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE

/-- A state meeting `vkContract.pre`: 1024-bit p and 160-bit q, the key at
`0x1000` and the working space at `0x10000`. -/
def validateSatState : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 404 | .r5 => 128 | .r6 => 20 | .r7 => 0x10000 | .r8 => 2048 | _ => 0
  lr := 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x1000, 404⟩]
  wr := [⟨0x10000, 16384⟩]

theorem validate_implies : vkContract.Implies (Spec.Dsa.validatePublicKeyContract abi) := by
  sig_implies [Spec.Dsa.validatePublicKeyContract, Spec.Dsa.validatePublicKeySig, abi, argRegs, vkContract,
    List.getD_cons_succ, List.getD_cons_zero, Sig.pairFacts, List.filterMap_cons,
    List.filterMap_nil, Bool.cond_true, Bool.cond_false, Bool.or_true, Bool.or_false, List.cons_append,
    List.nil_append, List.append_nil, Sig.conj_cons, Sig.conj_append]
    [validateSatState] using validateSatState

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Validate.CT`, which only this module used -/

section

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
  exact (pfront_S0_of hL hwr nw (fun hr hw => psrc_of hrd dKS (by omega_using [hkl]) hr hw)
    (by simp only [playOf]; omega_using [])).mono fun _ h => ⟨h, by simp only [KY, vkvdOf, pvdN, playOf]; omega_using []⟩

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
  rw [← h3, ← h4, ← h5, ← h6, Nat.min_eq_right (by omega_using [hk])] at e
  simp only [vkvdOf, pvdN, playOf, ← h3, ← h5, ← h6, ← h7, ← h8, e]

theorem validate_ct : ConstantTime isa vkContract.pre vkContract.pub Prevalidated.validate :=
  RelCT.constantTime (validate_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vkvdOf s, ⟨hs, rfl⟩, ⟨ht, (vkvdOf_eq hs hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE

end

end

/-! ### `Dsa.PPC64LE.Validate.Fn`, which only this module used -/

section

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
  have hplq : 3 * (playOf s).pl + (playOf s).ql = (s.gpr .r4).toNat := by simp only [playOf]; omega_using [hkl]
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

end

end


/-!
# `vg_dsa_validate_public_key` on PPC64LE: verified against the shared contract

`vkContract` states the shared contract on the registers
(`validate_implies`, `Validate/Implies.lean`); with correctness
(`validate_correct`) and constant time (`validate_ct`),
`Prevalidated.validate` is verified (`validate_verified`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_validate_public_key`. -/
theorem validate_verified :
    Verified target Prevalidated.validate (Spec.Dsa.validatePublicKeyContract abi) :=
  Verified.of_correct validate_correct validate_ct validate_implies

end VG.Proof.Dsa.PPC64LE
