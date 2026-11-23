module
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedReady
public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.BoundedGuard
public import VerifiedGarbage.Proof.AesGcm.X86_64.DirectGather.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Leaves
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

theorem boundedSelected (v : GcmVariant) (leaf : Option (BlocksTo.SealFn (VG.Proof.Gcm.X86_64.Stitch.CtxMode.flaggedT 48)))
    (side : ∀ b ∈ leaf, X86_64.Scrub.calleeSide b.fn.code v.lvG.level 24=true) :
    let code := Impl.AesGcm.X86_64.DirectGather.directSeal48 v.lvTW v.lvT v.impl.short v.impl.callees (DirectGather.ctrFn v) (leaf.map (·.fn))
    VerifiedScrubbed X86_64.target code DirectGather.publicContract 0 ∧ code.all (fun i => !X86_64.isa.writesSp i)=true := by
  dsimp only
  cases leaf with
  | none => exact ⟨DirectGather.base_verified v,DirectGather.base_spSafe v⟩
  | some b =>
    have bt := side b (by simp)
    simp only [Option.map_some, Impl.AesGcm.X86_64.DirectGather.directSeal48]
    split
    · next eligible =>
      have level : 2≤v.lvT.level := by rw [eligible.2]; decide
      have cs := X86_64.Scrub.calleeSide_mono v.lvTW_le_lvT (Nat.le_refl _) (DirectGather.ctr_side v)
      have bs := X86_64.Scrub.calleeSide_mono (DirectGather.lvG_le_T v) (Nat.le_refl _) bt
      have ws := DirectGather.plain_safe v
      have rs := DirectGather.boundedSafe v.impl (DirectGather.ctrFn v) b.fn level (callees_sideT v) cs bs v.ctrTo.spSafe b.spAll
      exact ⟨DirectGather.bounded_scrub v.lvT level (callees_sideT v) cs bs (DirectGather.prepared_public (.inr rfl)
        (DirectGather.bounded_rounds Short.shortFacts b (DirectGather.readyProof v b) rs)
        (DirectGather.plain_rounds (DirectGather.plainProof v) ws)) rs ws,
        X86_64.Scrub.scrubKs_spSafe (X86_64.onFlag_spSafe (X86_64.withStackArgScratch_spSafe rs.sp)
          (X86_64.withStackArgScratch_spSafe ws.sp))⟩
    · exact ⟨DirectGather.prepared_verified v 48 (.inr rfl) b bt,DirectGather.prepared_spSafe v 48 b bt⟩

theorem bounded_selected_verified (v : GcmVariant) (leaf : Option (BlocksTo.SealFn (CtxMode.flaggedT 48)))
    (side : ∀ b ∈ leaf, X86_64.Scrub.calleeSide b.fn.code v.lvG.level 24=true) :
    VerifiedScrubbed X86_64.target (directSeal48 v.lvTW v.lvT v.impl.short v.impl.callees (ctrFn v) (leaf.map (·.fn))) publicContract 0 :=
  (boundedSelected v leaf side).1

theorem bounded_selected_spSafe (v : GcmVariant) (leaf : Option (BlocksTo.SealFn (CtxMode.flaggedT 48)))
    (side : ∀ b ∈ leaf, X86_64.Scrub.calleeSide b.fn.code v.lvG.level 24=true) :
    (directSeal48 v.lvTW v.lvT v.impl.short v.impl.callees (ctrFn v) (leaf.map (·.fn))).all (fun i => !isa.writesSp i)=true :=
  (boundedSelected v leaf side).2

end VG.Proof.AesGcm.X86_64.DirectGather
