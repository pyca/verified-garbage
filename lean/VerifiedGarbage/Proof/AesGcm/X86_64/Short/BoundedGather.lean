module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedReady
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedGuard
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Verified
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase

/-! Dispatch the verified gather entry to the bounded whole-record call or its existing bulk implementation. -/
@[expose] public section
namespace VG.Proof.AesGcm.X86_64.DirectGather
open VG VG.X86_64 Gather Short Layout VG.Impl.AesGcm.X86_64.DirectGather
open VG.Impl.AesGcm.X86_64 (Fn Callees)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
variable {s t u v : State} {fallback : Prog isa}

theorem Layout.withBounded_wp (p : Layout (CtxMode.flaggedT 48) s) (hf : ShortFacts) (e : Initial s u)
    (next : ∀ w, Initial s w → WP isa fallback w (BodyDone (CtxMode.flaggedT 48) s)) :
    WP isa (withBounded fallback) u (BodyDone (CtxMode.flaggedT 48) s) := by
  refine WP.seq (WP.mono (p.testBoth e) fun w h => WP.ite (decide ¬Eligible s) (by simp only [eval,h.2])
    (fun _ => next _ h.1) (fun ok => ?_))
  have good := Classical.not_not.mp (of_decide_eq_false ok)
  exact p.gather_wp hf good.2 good.1 h.1

theorem Layout.withBounded_rel (p : Layout (CtxMode.flaggedT 48) s) (q : Layout (CtxMode.flaggedT 48) t)
    (hf : ShortFacts) (pb : Pub s t) (e : Initial s u) (f : Initial t v)
    (next : ∀ x y, Initial s x → Initial t y → RelCT isa (fun a b => a=x ∧ b=y) fallback (fun _ _ => True)) :
    RelCT isa (fun a b => a=u ∧ b=v) (withBounded fallback) (fun _ _ => True) := by
  have check := (rel_next (p.testBoth_rel q pb) (fun _ h => p.testBoth h) (fun _ h => q.testBoth h)).mono
    (P':=fun a b => a=u ∧ b=v) (fun _ _ h => by obtain ⟨rfl,rfl⟩ := h; exact ⟨e,f⟩) (fun _ _ h => h)
  refine RelCT.seq check (rel_ite_e (fun _ _ h => by simp only [h.1.2,h.2.2,pubEligible pb]) ?_ ?_)
  · intro x y a b x' y' h ex ey
    exact next x y h.1.1.1 h.1.2.1 x y a b x' y' ⟨rfl,rfl⟩ ex ey
  · intro x y a b x' y' h ex ey
    have sh := Classical.not_not.mp (of_decide_eq_false (Option.some.inj (h.1.1.2.symm.trans h.2)))
    exact p.gather_rel q hf pb sh.2 sh.1 x y a b x' y' ⟨h.1.1.1,h.1.2.1⟩ ex ey

theorem bounded_rounds (hf : ShortFacts) {c : Callees} {ctr : Fn} (T : BlocksTo.SealFn (CtxMode.flaggedT 48))
    (h : InitializedProof (CtxMode.flaggedT 48) (general c ctr (some T.fn)))
    (safe : CoreSafe (dispatch (withBounded (quick T.fn)) (withBounded (general c ctr (some T.fn))))) :
    Verified X86_64.target (preparedBounded c ctr T.fn) (Proof.AesGcm.Flag.sealGatherFlaggedRoundsContract 48 X86_64.abi 2672) :=
  ready_framed (by decide)
    (fun p => p.dispatch_wp (fun _ e g => p.withBounded_wp hf e (fun _ ex => p.quick_wp hf T (by decide) ex g))
      (fun _ e => p.withBounded_wp hf e (fun _ ex => h.run p ex)))
    (fun p q pb => p.dispatch_rel q pb (fun _ _ e f g => p.withBounded_rel q hf pb e f
      (fun _ _ ex fx => p.quick_rel q hf T (by decide) pb ex fx g)) (fun _ _ e f =>
        p.withBounded_rel q hf pb e f (fun _ _ ex fx => h.rel p q pb ex fx))) safe

end VG.Proof.AesGcm.X86_64.DirectGather
