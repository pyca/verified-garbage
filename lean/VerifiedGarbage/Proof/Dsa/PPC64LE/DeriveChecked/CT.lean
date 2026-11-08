module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.DeriveChecked.Fn
public import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.CT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.Key
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.CT
meta import VerifiedGarbage.Proof.Dsa.PPC64LE.DeriveChecked.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.CT.SizesRest
import VerifiedGarbage.Proof.Dsa.PPC64LE.DeriveChecked.Check
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Fn
import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# DSA key derivation for a checked domain on PPC64LE: constant time

`deriveChecked_ct`: two runs from states that satisfy `dcContract` and agree
on its public data (`dContract`'s) leak the same trace. The public data name
a domain that passes the specification's checks (`KD`), so `g^q mod p = 1`
holds of them (`Base.gq`). The entry is `vg_dsa_derive_key`'s
(`dentry_rel`), the checks before g's too (`sizes_rel`, then the phases
`paramsTail_rel` goes through); g's range check (`rangeG_rel`) leaves the
state of `paramsTail_rel`'s `rest`, `K8`, with `Base.gq`, and the rest is
`vg_dsa_derive_key`'s (`dbody_rel`, `dzero_rel`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The public data name exactly the domain, which passes the specification's checks. -/
def KD (v : VD) : Prop :=
  v.kn = 2 * v.L.pl + v.L.ql ∧ Spec.Dsa.checkParametersBytes v.L.pl v.L.ql v.kb = true

/-- A domain that passes the specification's checks has `g^q mod p = 1`. -/
theorem Base.gq {v : VD} {s : State} (B : Base v s) (h : KD v) : v.e (v.L.pl + v.L.ql) ^ v.q % v.p = 1 := by
  obtain ⟨hkn, hc⟩ := h
  have hv : Spec.Dsa.lengthsValid v.L.pl v.L.ql := by
    simp only [Spec.Dsa.checkParametersBytes, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1
  have e := checkParameters_spec (m := s.mem) (L := v.L) (key := v.key) hv
  rw [← hkn, B.kb] at e
  have hP : ParamsOk s.mem v.L v.key := of_decide_eq_true (e.symm.trans hc)
  have := hP.2.2.2
  rw [B.p, B.q, B.g] at this
  exact this

/-- On entry. -/
def DCC0 (v : VD) (s : State) : Prop := dcContract.pre s ∧ dvdOf s = v

theorem dcentry_rel : RelCT isa (Two DCC0) (.block Derive.entry) (Two fun v s => S0 v s ∧ KD v) := by
  refine two_post (dentry_rel.mono (fun _ _ => two_mono fun _ _ h => ⟨h.1.1, h.2⟩) fun _ _ _ => trivial)
    fun v s h => (dfront_S0 ⟨h.1.1, h.2⟩).mono fun _ ht => ⟨ht, ?_⟩
  obtain ⟨⟨hp, hc⟩, rfl⟩ := h
  have hkl := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨rfl, ?_⟩
  show Spec.Dsa.checkParametersBytes (s.gpr .r7).toNat (s.gpr .r9).toNat
    (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (2 * (s.gpr .r7).toNat + (s.gpr .r9).toNat)) = true
  rw [← hkl]; exact hc

/-- g's pointer and `rangeElem`, from a state in the P space. -/
theorem w_rangeG {v : VD} {s : State} (h : PP KM v s) :
    WP isa (.seq (.block ptrG) Derive.rangeElem) s (CC KM (ERange fun L => L.pl + L.ql) v) := by
  obtain ⟨B, r2, -, ⟨ip, p0, ptop, p8, qf⟩, kv⟩ := h
  have hL := B.ok
  have hov : v.L.pl + v.L.ql + v.L.pl ≤ v.kn := by have := B.kn; omega
  refine WP.seq (WP.mono (ptrG_ok B.regs) fun t ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  have B1 := B.step k1 (by rw [m1]; exact Outside.refl _ _ _ _)
  refine WP.mono (rangeElem_ok (p := v.p) hL (ip.keep k1 (by decide))
      (B1.hk.sub (o := v.L.pl + v.L.ql) (k := v.L.pl) hov) a12 a6 (by rw [m1]; exact p0) (by rw [m1]; exact ptop))
    fun u ⟨⟨ip', p0', ptop', p8', r0, pb⟩, k2⟩ =>
      ⟨B1.step k2 (pb.body hL), ?_, envP_of ip', ⟨ip', p0', ptop', ?_,
        (pb.arrQ hL 0 (by decide)).trans (by rw [m1]; exact qf.1), (pb.qtop hL).trans (by rw [m1]; exact qf.2)⟩,
        kv, ?_⟩
  · rw [k2.gpr .r2 (by decide), k1.gpr .r2 (by decide), r2]
  · rw [p8', m1]; exact p8
  · rw [r0, B1.bytes hov]; rfl

theorem rangeG_rel :
    RelCT isa (Two fun v s => PP KM v s ∧ KD v) (.seq (.block ptrG) Derive.rangeElem)
      (Two fun v s => CC KM (ERange fun L => L.pl + L.ql) v s ∧ KD v) := by
  refine two_postG ?_ fun _ _ h => w_rangeG h
  unfold Derive.rangeElem
  exact RelCT.assoc (rel_pins (pins_PP KM) t5)

/-- The checks of `checkDomain` after the sizes, for a domain that passes the
specification's checks. -/
theorem domainTail_rel {rest fail : Prog isa} {Q : State → State → Prop}
    (hrest : RelCT isa (Two fun v s => K8 v s ∧ KD v) rest Q)
    (hfail : ∀ Φ : VD → State → Prop, (∀ v s, Φ v s → Base v s ∧ KD v) → RelCT isa (Two Φ) fail Q) :
    RelCT isa (Two fun v s => S5 v s ∧ KD v) (odds (andThen pModQ (.seq setupP (andThen (.seq (.block ptrG)
      Derive.rangeElem) rest fail)) fail) fail) Q := by
  unfold odds andThen
  refine RelCT.seq (two_postG (rel_pins pins_S5' t1) fun _ _ h => w_O1 h)
    (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.seq (two_postG (rel_pins (pins_and pins_O1) t2) fun _ _ h => w_O2 h)
    (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.seq (two_postG (rel_pins (pins_and pins_O2) t3) fun _ _ h => w_OM h)
    (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2) ?_ (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩))
  refine RelCT.seq (two_postG (setupP_rel (pins_and pins_OM)
      fun _ _ ⟨⟨B, r2, _, ⟨ko, _⟩, _⟩, _⟩ => ⟨B, r2, ko.2.1⟩) fun _ _ h => w_P h) (RelCT.seq
    rangeG_rel (rel_ite_zeroG (zero_iff_agree _ fun _ _ h => h.2.2.2.2.2) ?_
      (hfail _ fun _ _ h => ⟨h.1.1.1, h.2⟩)))
  exact hrest.mono (fun _ _ => two_mono fun _ _ ⟨⟨⟨B, r2, fx, pf, k, e⟩, z⟩, g⟩ =>
      ⟨⟨B, r2, fx, pf, k, e.mp z, B.gq g⟩, g⟩) fun _ _ h => h

theorem dccheck_rel : RelCT isa (Two fun v s => S0 v s ∧ KD v) (Derive.checkDomain Derive.body Derive.zeroOut)
    (Two End) :=
  sizes_rel (domainTail_rel (dbody_rel.mono (fun _ _ => two_mono fun _ _ h => ⟨h.1, trivial⟩) fun _ _ h => h)
      fun _ h => dzero_rel fun v s h' => (h v s h').1) fun _ h => dzero_rel fun v s h' => (h v s h').1

theorem deriveChecked_rel : RelCT isa (Two DCC0) Derive.deriveChecked fun _ _ => True := by
  unfold Derive.deriveChecked
  exact RelCT.seq dcentry_rel (RelCT.seq dccheck_rel (two_taint _ pins_End (by taint_decide)))

theorem deriveChecked_ct : ConstantTime isa dcContract.pre dcContract.pub Derive.deriveChecked :=
  RelCT.constantTime (deriveChecked_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨dvdOf s, ⟨hs, rfl⟩, ⟨ht, (dvdOf_eq hs.1 hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Dsa.PPC64LE
