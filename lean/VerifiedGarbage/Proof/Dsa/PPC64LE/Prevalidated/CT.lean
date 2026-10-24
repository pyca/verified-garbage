module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Contract
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Entry
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Spec
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem
import VerifiedGarbage.Proof.Dsa.SizeBounds
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Contract
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Entry
meta import VerifiedGarbage.Impl.Dsa.PPC64LE.Prevalidated
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyCT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest

/-!
# DSA prevalidated verification on PPC64LE: constant time

`prevalidated_ct`: two runs from states that satisfy `vpContract` and agree
on its public data (`vContract`'s) leak the same trace. The entry is
verification's (`entry_rel`), the check of the sizes too (`sizes_rel`); the
public data name a key that passes validation (`KV`), whose checks
verification's phases need (`Base.pk`): after `setupQ` and `setupP`, which
the taint analysis checks from the registers the phases fix, the state is
in verification's phase `K9`, and the rest is verification's (`body_rel`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Dsa.PPC64LE

/-- The public data name exactly the key, which passes validation. -/
def KV (v : VD) : Prop :=
  v.kn = 3 * v.L.pl + v.L.ql ∧ Spec.Dsa.validatePublicKeyBytes v.L.pl v.L.ql v.kb = true

/-- The key's checks verification's phases state on the public data. -/
def PK (v : VD) : Prop := (KM v ∧ EOk (fun L => L.pl + L.ql) v) ∧ EOk (fun L => 2 * L.pl + L.ql) v

theorem lengthsValid_of_validate {pl ql : Nat} {key : List Byte}
    (h : Spec.Dsa.validatePublicKeyBytes pl ql key = true) : Spec.Dsa.lengthsValid pl ql := by
  by_contra hn
  simp only [Spec.Dsa.validatePublicKeyBytes, hn, decide_false, Bool.not_false, Bool.true_or,
    ↓reduceIte, Bool.false_eq_true] at h

/-- A key that passes validation passes the checks. -/
theorem Base.pk {v : VD} {s : State} (B : Base v s) (h : KV v) : PK v := by
  obtain ⟨hkn, hval⟩ := h
  have e := validate_spec (m := s.mem) (L := v.L) (key := v.key) (lengthsValid_of_validate hval)
  rw [← hkn, B.kb] at e
  obtain ⟨⟨sz, qo, po⟩, ⟨g1, y1⟩, d, gq, yq⟩ := of_decide_eq_true (e.symm.trans hval)
  have hy : 3 * v.L.pl + v.L.ql ≤ v.kn := Nat.le_of_eq hkn.symm
  simp only [B.p, B.q, B.g, B.y hy] at sz qo po g1 y1 d gq yq
  have bd : 1 < v.p ∧ 255 < v.q ∧ v.q < v.p := VG.Proof.Dsa.supported_bounds sz
  exact ⟨⟨⟨⟨sz, po, qo⟩, (pmod_iff (p := v.p) (q := v.q) (by omega) (by omega)).mp d⟩, g1, gq⟩, y1, yq⟩

/-- On entry. -/
def PV0 (v : VD) (s : State) : Prop := vpContract.pre s ∧ vdOf s = v

theorem pentryV_rel : RelCT isa (Two PV0) (.block Verify.entry) (Two fun v s => S0 v s ∧ KV v) := by
  refine two_post (entry_rel.mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ => trivial)
    fun v s h => (front_S0 ⟨h.1.1, h.2⟩).mono fun _ ht => ⟨ht.1, ?_⟩
  obtain ⟨⟨hp, hval⟩, rfl⟩ := h
  have hkl := hp.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨by simp only [vdOf, layOf], ?_⟩
  show Spec.Dsa.validatePublicKeyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat)) = true
  rw [← hkl]; exact hval

/-- After `setupQ`: in the Q space, q in its array 0. -/
def LQ : VD → State → Prop := Ph VD.qb fun v s => FixL [] s ∧ QF v s

theorem pins_LQ : Pins LQ (coreRegs ++ []) := pins_fixL _ _ fun _ => rfl

theorem tQ : RelCT isa (Two (FixR (coreRegs ++ []))) setupQ fun _ _ => True :=
  two_taint _ (pins_fixR _) (by taint_decide)

theorem w_LQ {v : VD} {s : State} (h : S5 v s) : WP isa setupQ s (LQ v) := by
  obtain ⟨B, r2, -, -⟩ := h
  refine WP.mono (setupQ_ok B.ok B.scr B.regs (B.hk.take B.kn)) fun t ⟨⟨_, q0, qtop, qb⟩, k⟩ =>
    ⟨B.step k (qb.body B.ok), ?_, fixL_nil _, by rw [q0, B.q]; rfl, qtop⟩
  rw [k.gpr .r2 (by decide), r2]

theorem w_PV {v : VD} {s : State} (h : LQ v s ∧ KV v) : WP isa setupP s fun t => PP KM v t ∧ KV v := by
  obtain ⟨⟨B, r2, -, qf⟩, kv⟩ := h
  exact (w_setupP (K := KM) (fun _ h => h.1) B r2 qf (B.pk kv).1.1).mono fun _ ht => ⟨ht, kv⟩

theorem setupV_rel :
    RelCT isa (Two fun v s => S0 v s ∧ KV v) (Prevalidated.setup Verify.body (.block [.li .r3 0])) (Two End) := by
  unfold Prevalidated.setup
  refine sizes_rel ?_ fun _ h => fail_rel fun v s h' => (h v s h').1
  refine RelCT.seq (two_postG (rel_pins pins_S5' tQ) fun _ _ h => w_LQ h)
    (RelCT.seq (two_post (rel_pins (pins_and pins_LQ) t4) fun _ _ h => w_PV h) ?_)
  exact body_rel.mono (fun _ _ => two_mono fun _ s ⟨⟨B, r2, _, pf, _⟩, kv⟩ =>
    ⟨B, r2, fixL_nil s, pf, B.pk kv⟩) fun _ _ h => h

theorem prevalidated_rel : RelCT isa (Two PV0) Prevalidated.verify fun _ _ => True := by
  unfold Prevalidated.verify
  exact RelCT.seq pentryV_rel (RelCT.seq setupV_rel (two_taint _ pins_End (by taint_decide)))

theorem prevalidated_ct : ConstantTime isa vpContract.pre vpContract.pub Prevalidated.verify :=
  RelCT.constantTime (prevalidated_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨vdOf s, ⟨hs, rfl⟩, ⟨ht, (vdOf_eq hs.1 hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
