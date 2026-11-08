module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Body
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.CT
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Sizes
import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Spec
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.CT.Body
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.CT
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign

/-!
# DSA prevalidated signing on PPC64LE: constant time

`psign_ct`: two runs from states that satisfy `spContract` and agree on its
public data (`sContract`'s: the arguments' registers, the stack's arguments,
the key's public part and the result) leak the same trace. The entry is
signing's (`sentry_rel`); the public data name a key whose public part
passes validation (`KV`), since the whole key passes private-key validation
(`validatePrivate_spec`). The setup of the working spaces is prevalidated
verification's (`sizes_rel`, then `setupQ` and `setupP` as in
`setupV_rel`), the signing `sbody_rel`, and the sizes' failure, which the
precondition rules out, the zeroing of `out` (`zero_rel`); each branch
depends only on the key's public part.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- On entry. -/
def SP0 (v : VD) (s : State) : Prop := spContract.pre s ∧ svdOf s = v

/-- A key that passes private-key validation names public data whose key
passes public-key validation. -/
theorem kv_of_pre {s : State} (h : spContract.pre s) : KV (svdOf s) := by
  obtain ⟨hp, hval⟩ := h
  have hv := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hkl := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP : PrivOk s.mem (slayOf s) (s.gpr .r5) := by
    have e := validatePrivate_spec (m := s.mem) (L := slayOf s) (key := s.gpr .r5) hv
    rw [show 3 * (slayOf s).pl + 2 * (slayOf s).ql = (s.gpr .r6).toNat from hkl.symm] at e
    exact of_decide_eq_true (e.symm.trans hval)
  refine ⟨by simp only [svdOf, slayOf], ?_⟩
  show Spec.Dsa.validatePublicKeyBytes (slayOf s).pl (slayOf s).ql
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (3 * (slayOf s).pl + (slayOf s).ql)) = true
  rw [validate_spec hv]
  exact decide_eq_true hP.1

theorem psentry_rel : RelCT isa (Two SP0) (.block Sign.entry) (Two fun v s => S0 v s ∧ (SG v ∧ KV v)) :=
  two_post (sentry_rel.mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ => trivial)
    fun v s h => (sfront_S0 ⟨h.1.1, h.2⟩).mono fun _ ht => ⟨ht.1, ht.2, by rw [← h.2]; exact kv_of_pre h.1⟩

theorem w_PVS {v : VD} {s : State} (h : LQ v s ∧ (SG v ∧ KV v)) :
    WP isa setupP s fun t => PP KM v t ∧ (SG v ∧ KV v) := by
  obtain ⟨⟨B, r2, -, qf⟩, g⟩ := h
  exact (w_setupP (K := KM) (fun _ h => h.1) B r2 qf (B.pk g.2).1.1).mono fun _ ht => ⟨ht, g⟩

theorem setupS_rel :
    RelCT isa (Two fun v s => S0 v s ∧ (SG v ∧ KV v)) (Prevalidated.setup Sign.body Sign.zeroOut) (Two End) := by
  unfold Prevalidated.setup
  refine sizes_rel ?_ fun _ h => zero_rel fun v s h' => ⟨(h v s h').1, (h v s h').2.1⟩
  refine RelCT.seq (two_postG (rel_pins pins_S5' tQ) fun _ _ h => w_LQ h)
    (RelCT.seq (two_post (setupP_rel (pins_and pins_LQ)
      fun _ _ ⟨⟨B, r2, _, _⟩, g⟩ => ⟨B, r2, (B.pk g.2).1.1.1.2.1⟩) fun _ _ h => w_PVS h) ?_)
  exact sbody_rel.mono (fun _ _ => two_mono fun _ s ⟨⟨B, r2, _, pf, _⟩, sg, kv⟩ =>
    ⟨⟨B, r2, fixL_nil s, pf, B.pk kv⟩, sg⟩) fun _ _ h => h

theorem psign_rel : RelCT isa (Two SP0) PrevalidatedSign.sign fun _ _ => True := by
  unfold PrevalidatedSign.sign
  exact RelCT.seq psentry_rel (RelCT.seq setupS_rel (two_taint _ pins_End (by taint_decide)))

/-- Runs that agree on the contract's public data have the same public data `svdOf`. -/
theorem svdOf_eq {s t : State} (hs : sContract.pre s) (hp : sContract.pub s t) : svdOf s = svdOf t := by
  obtain ⟨-, h3, h4, h5, h6, h7, h8, h9, h10, a0, a1, a2, hl⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hkl, -⟩ := hs
  obtain ⟨e, -⟩ := List.append_inj' hl rfl
  simp only [Spec.Dsa.publicBytesLeak, bytesAt_take] at e
  have e := map_toNat_inj e
  rw [← h5, ← h6, ← h7, ← h9, Nat.min_eq_right (by omega)] at e
  simp only [svdOf, slayOf, ← h3, ← h5, ← h7, ← h8, ← h9, ← h10, ← a0, ← a1, ← a2, e]

theorem psign_ct : ConstantTime isa spContract.pre spContract.pub PrevalidatedSign.sign :=
  RelCT.constantTime (psign_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨svdOf s, ⟨hs, rfl⟩, ⟨ht, (svdOf_eq hs.1 hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
