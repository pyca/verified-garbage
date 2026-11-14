module

public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Base
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rsa.X86.Rd.Loops
import VerifiedGarbage.Proof.Mont.X86.Square.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Mont.X86.Rt.Step
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
meta import VerifiedGarbage.Impl.Rsa.X86.RecoverDetRt
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.Taint
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.SseTaint
meta import VerifiedGarbage.Proof.Rsa.X86.Rd.TimeBaseW
meta import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Base

/-! # The divisions' and the square root's timing on i686: the leaves

The stages' loops count, and address, by header words (`sC4`, `sB`, `sBc`, `sZ`, `oSteps`) that the
two runs hold equal, so each operation is checked on its own (`InvBatchRt.Time.leaf`), on the view of
the state with the working space as its only writable region, from a taint that makes those header
words public (`τK`).
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.RecoverRt (nar wid)
open VG.Impl.Rsa.X86.RecoverDetRt hiding aN aP aQ
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa.X86.InvBatchRt.Time (view Pre0 τ0 argBytes Public)

/-- The taint each leaf is checked from: `τ0` of the wide layout, and the header words `ds` public. -/
def τK (ds : List Nat) : VG.X86.Taint.T :=
  { τ0 wid with slots := VG.Slots.ofList (ds.map fun d => (0, d, 4)) }

section
variable {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
  {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- A stage's state is a leaf's start, in the wide layout. -/
theorem KS.pre0 (pg : PubG g) (h : KS g s0 A live AW liveW V ls s) :
    Pre0 wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp s :=
  ⟨h.rtW, by decide, ⟨h.argsOk pg, h.sp, fun i hi => h.arg (h.start.2 i hi).1 (by
    change i < 12 at hi; omega_using [hi])⟩⟩

/-- The geometry of the views: only the working space writable. -/
def Geo.vw (g : Geo) : Geo := { g with wr := [⟨g.B, g.Z⟩] }

/-- A stage holds of the views, in their geometry. -/
theorem KS.onView (h : KS g s0 A live AW liveW V ls s) :
    KS g.vw (VG.Proof.Rsa.X86.InvBatchRt.Time.view s0 g.B g.Z) A live AW liveW V ls
      (VG.Proof.Rsa.X86.InvBatchRt.Time.view s g.B g.Z) :=
  { rt := VG.Proof.Rsa.X86.InvBatchRt.Time.RtWs.view h.rt
    lower := h.lower
    upper := h.upper
    frame := h.frame
    sp := h.sp
    room := h.room
    top := h.top
    wsLen := VG.Proof.Rsa.X86.InvBatchRt.Time.callArg_view h.wsLen
    z8 := h.z8
    rest := ⟨h.rest.1, by simp only [VG.Proof.Rsa.X86.InvBatchRt.Time.view, State.withRegions_rd,
      h.rest.2.1, h.rest.2.2], rfl⟩
    arrs := h.arrs
    arrsW := h.arrsW
    sl := h.sl
    live_lt := h.live_lt
    liveW_lt := h.liveW_lt
    ls_ok := h.ls_ok
    start := ⟨rfl, fun i hi => ⟨VG.Proof.Rsa.X86.InvBatchRt.Time.callArg_view (h.start.2 i hi).1,
      (h.start.2 i hi).2⟩⟩ }

end

/-- Two runs at a leaf's start, with the header words `ds` equal, agree on `τK ds` in their views. -/
theorem agreeK {B : Addr} {Z len N : Nat} {args : Nat → BitVec 32} {sp : BitVec 32} {s t : State}
    {ds : List Nat} (hds : ∀ d ∈ ds, d + 4 ≤ 160)
    (hs : Pre0 wid B Z len N args sp s) (ht : Pre0 wid B Z len N args sp t)
    (eq : ∀ d ∈ ds, w32 s.mem B d = w32 t.mem B d) :
    VG.X86.Taint.Agree (τK ds) (view s B Z) (view t B Z) := by
  have A0 := VG.Proof.Rsa.X86.InvBatchRt.Time.agree0 hs ht
  have w₁ := A0.wf₁
  have w₂ := A0.wf₂
  refine ⟨A0.rf, A0.wr, ⟨w₁.lens, w₁.bases, w₁.wbases, w₁.args, w₁.argBases, w₁.stk, w₁.frames, w₁.room⟩,
    ⟨w₂.lens, w₂.bases, w₂.wbases, w₂.args, w₂.argBases, w₂.stk, w₂.frames, w₂.room⟩,
    VG.X86.Taint.slotsOk_of_list rfl (fun sl hsl => ?_), ?_, A0.sp, A0.argMem⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hsl
    change d + 4 ≤ ([160] : List Nat).getD 0 0
    exact hds d hd
  · intro i k hk
    rw [τK, VG.Slots.has_ofList] at hk
    obtain ⟨sl, hsl, rfl, h₁, h₂⟩ := hk
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hsl
    simp only at h₁ h₂
    change s.mem (B + BitVec.ofNat 64 k) = t.mem (B + BitVec.ofNat 64 k)
    have e : B + BitVec.ofNat 64 k = off B d + BitVec.ofNat 64 (k - d) := by
      simp only [off]; rw [VG.Offset.add_add]; congr 2; omega_using [h₁]
    rw [e, Mem.readW_byte s.mem _ (show k - d < 4 by omega_using [h₂]), Mem.readW_byte t.mem _ (show k - d < 4 by omega_using [h₂])]
    exact congrArg _ (BitVec.eq_of_toNat_eq (eq d hd))


/-- Code the analysis checks from `τK ds`. -/
def OkK (ds : List Nat) (c : Prog isa) : Prop :=
  ∃ hint, (VG.Taint.check sseTaint (τK ds) c hint).isSome = true

/-- A leaf: code checked from `τK ds`, run by both runs from states that hold the header words `ds`
at the same values, and that run it on their views. -/
theorem leafK {g : Geo} {P Q : State → Prop} {c : Prog isa} {ds : List Nat} (vals : Nat → Nat)
    (hds : ∀ d ∈ ds, d + 4 ≤ 160)
    (hpre : ∀ s, P s → Pre0 wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp s)
    (hval : ∀ s, P s → ∀ d ∈ ds, w32 s.mem g.B d = vals d)
    (hrun : ∀ s, P s → ∃ tr z, Exec isa c (view s g.B g.Z) tr z)
    (hf : ∀ s, P s → WP isa c s Q) (h : OkK ds c) :
    RelCT isa (fun s t => P s ∧ P t) c (fun s t => Q s ∧ Q t) := by
  obtain ⟨_, h⟩ := h
  have R := VG.Proof.Rsa.X86.InvBatchRt.Time.leaf (B := g.B) (Z := g.Z) (P := fun s t => P s ∧ P t) (τK ds)
    (fun s t ⟨ps, pt⟩ => agreeK hds (hpre s ps) (hpre t pt)
      (fun d hd => (hval s ps d hd).trans (hval t pt d hd).symm))
    (fun s t ⟨ps, pt⟩ => ⟨(hpre s ps).1.ws.workspace.wr, (hpre t pt).1.ws.workspace.wr⟩)
    (fun s t ⟨ps, pt⟩ => ⟨hrun s ps, hrun t pt⟩) h
  exact (RelCT.wp R (fun s t ⟨ps, pt⟩ => ⟨hf s ps, hf t pt⟩)).mono (fun _ _ h => h)
    (fun _ _ ⟨_, a, b⟩ => ⟨a, b⟩)

/-- A run on the view, from a WP on it. -/
theorem run_of {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) : ∃ tr z, Exec isa c s tr z :=
  let ⟨tr, z, e, _⟩ := h
  ⟨tr, z, e⟩

theorem wpRes {code : Prog isa} {s t : State} {trace : List Leak} {post : State → Prop}
    (W : WP isa code s post) (E : Exec isa code s trace t) : post t := by
  obtain ⟨_, u, F, P⟩ := W
  obtain ⟨_, rfl⟩ := Exec.det E F
  exact P

/-- Both runs at a stage. -/
def Both (P : State → Prop) (s t : State) : Prop := P s ∧ P t

/-- A leaf's start: the working space in the wide layout, and the call's public data. -/
abbrev P0 (g : Geo) (s : State) : Prop := Pre0 wid g.B g.Z (16 * g.n + 24) 22 g.args g.sp s

theorem eval_view (c : Cond) (s : State) (B : Addr) (Z : Nat) : isa.eval c (view s B Z) = isa.eval c s := by
  cases c <;> rfl

/-- A leaf between stages, given for every geometry (its views' too): the stage fixes the header
words `ds`, and the step runs from it. -/
theorem leafP {g : Geo} {P Q : Geo → State → Prop} {c : Prog isa} {ds : List Nat}
    (vals : Nat → Nat) (hds : ∀ d ∈ ds, d + 4 ≤ 160) (hpre : ∀ s, P g s → P0 g s)
    (hv : ∀ s, P g s → P g.vw (view s g.B g.Z))
    (hval : ∀ s, P g s → ∀ d ∈ ds, w32 s.mem g.B d = vals d)
    (hf : ∀ g' s, P g' s → WP isa c s (Q g')) (h : OkK ds c) :
    RelCT isa (Both (P g)) c (Both (Q g)) :=
  leafK vals hds hpre hval (fun s ps => run_of (hf g.vw _ (hv s ps))) (hf g) h

theorem leafG {g : Geo} (pg : PubG g) {P Q : Geo → State → Prop} {c : Prog isa} {ds : List Nat}
    (vals : Nat → Nat) (hds : ∀ d ∈ ds, d + 4 ≤ 160) (hks : ∀ s, P g s → MulPost g s)
    (hv : ∀ s, P g s → P g.vw (view s g.B g.Z))
    (hval : ∀ s, P g s → ∀ d ∈ ds, w32 s.mem g.B d = vals d)
    (hf : ∀ g' s, P g' s → WP isa c s (Q g')) (h : OkK ds c) :
    RelCT isa (Both (P g)) c (Both (Q g)) :=
  leafP vals hds (fun s ps => by obtain ⟨_, _, _, _, _, _, _, k⟩ := hks s ps; exact k.pre0 pg) hv hval hf h

/-- A stage: a frame with the arrays `live`, `liveW` and header words `ls`, their values satisfying `F`. -/
def St (g : Geo) (live liveW ls : List Nat) (F : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Prop)
    (s : State) : Prop :=
  ∃ s0 A AW V, KS g s0 A live AW liveW V ls s ∧ F A AW V

section
variable {g : Geo} {live liveW ls : List Nat} {F : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Prop} {s : State}

theorem St.onView (h : St g live liveW ls F s) : St g.vw live liveW ls F (view s g.B g.Z) :=
  let ⟨_, _, _, _, k, f⟩ := h
  ⟨_, _, _, _, k.onView, f⟩

theorem St.mul (h : St g live liveW ls F s) : MulPost g s :=
  let ⟨_, _, _, _, k, _⟩ := h
  ⟨_, _, _, _, _, _, _, k⟩

/-- The header words `ds` of a stage that fixes them. -/
theorem St.slots {ds : List Nat} {vals : Nat → Nat} (hin : ∀ d ∈ ds, d ∈ ls)
    (hv : ∀ A AW V, F A AW V → ∀ d ∈ ds, V d = vals d) (h : St g live liveW ls F s) :
    ∀ d ∈ ds, w32 s.mem g.B d = vals d := by
  obtain ⟨_, _, _, _, k, f⟩ := h
  intro d hd
  exact (k.sl d (hin d hd)).trans (hv _ _ _ f d hd)

end

/-- A leaf from a stage: the stage fixes the header words `ds` the leaf reads. -/
theorem leafSt {g : Geo} (pg : PubG g) {live liveW ls : List Nat}
    {F : (Nat → Nat) → (Nat → Nat) → (Nat → Nat) → Prop} {Q : Geo → State → Prop} {c : Prog isa}
    {ds : List Nat} (vals : Nat → Nat) (hds : ∀ d ∈ ds, d ∈ ls ∧ d + 4 ≤ 160)
    (hv : ∀ A AW V, F A AW V → ∀ d ∈ ds, V d = vals d)
    (hf : ∀ g' s, St g' live liveW ls F s → WP isa c s (Q g')) (h : OkK ds c) :
    RelCT isa (Both (St g live liveW ls F)) c (Both (Q g)) :=
  leafG (P := fun g => St g live liveW ls F) pg vals (fun d hd => (hds d hd).2) (fun _ h => h.mul)
    (fun _ h => h.onView) (fun _ h => h.slots (fun d hd => (hds d hd).1) hv) hf h

/-- A loop run `K ≥ 1` times by both runs, the same body each time, the condition (`c`) saying
whether another run follows. -/
theorem relLoop {body : Prog isa} {c : Cond} (L : Nat → State → Prop) {K : Nat} (pos : 0 < K)
    (rel : ∀ k, k < K → RelCT isa (fun s t => L k s ∧ L k t) body (fun _ _ => True))
    (step : ∀ k s, k < K → L k s → WP isa body s fun v =>
      L (k + 1) v ∧ isa.eval c v = some (decide (k + 1 < K))) :
    RelCT isa (fun s t => L 0 s ∧ L 0 t) (.loop body c) (fun s t => L K s ∧ L K t) := by
  have loop := VG.RelCT.loop (M := isa) (body := body) (c := c)
    (Q := fun s t => L K s ∧ L K t)
    (fun remaining s t => ∃ k, k + remaining = K ∧ 0 < remaining ∧ L k s ∧ L k t)
    (fun remaining s t tr ur sf tf ⟨k, sum, pos, hs, ht⟩ es et => by
      have trace := (rel k (by omega_using [sum, pos]) _ _ _ _ _ _ ⟨hs, ht⟩ es et).1
      obtain ⟨is, zs⟩ := wpRes (step k s (by omega_using [sum, pos]) hs) es
      obtain ⟨it, zt⟩ := wpRes (step k t (by omega_using [sum, pos]) ht) et
      refine ⟨trace, by rw [zs, zt], fun done => ?_, fun more => ?_⟩
      · rw [zs] at done
        simp only [Option.some.injEq, decide_eq_false_iff_not] at done
        have last : k + 1 = K := by omega_using [sum, pos, done]
        exact ⟨last ▸ is, last ▸ it⟩
      · rw [zs] at more
        simp only [Option.some.injEq, decide_eq_true_eq] at more
        exact ⟨remaining - 1, by omega_using [pos], k + 1, by omega_using [sum, pos], by omega_using [sum, more], is, it⟩) K
  exact loop.mono (fun s t ⟨hs, ht⟩ => ⟨0, by omega_using [], pos, hs, ht⟩) (fun _ _ h => h)

/-- A loop run `K ≥ 1` times, its body related from each count's stage to the next, the stages
saying whether another run follows. -/
theorem relLoopB {body : Prog isa} {c : Cond} (L : Nat → State → Prop) {K : Nat} (pos : 0 < K)
    (rel : ∀ k, k < K → RelCT isa (Both (L k)) body (Both (L (k + 1))))
    (fl : ∀ k s, 0 < k → k ≤ K → L k s → isa.eval c s = some (decide (k < K))) :
    RelCT isa (Both (L 0)) (.loop body c) (Both (L K)) := by
  have loop := VG.RelCT.loop (M := isa) (body := body) (c := c) (Q := Both (L K))
    (fun remaining s t => ∃ k, k + remaining = K ∧ 0 < remaining ∧ L k s ∧ L k t)
    (fun remaining s t tr ur sf tf ⟨k, sum, pos, hs, ht⟩ es et => by
      obtain ⟨trace, is, it⟩ := rel k (by omega_using [sum, pos]) _ _ _ _ _ _ ⟨hs, ht⟩ es et
      have zs := fl (k + 1) sf (by omega_using []) (by omega_using [sum, pos]) is
      have zt := fl (k + 1) tf (by omega_using []) (by omega_using [sum, pos]) it
      refine ⟨trace, by rw [zs, zt], fun done => ?_, fun more => ?_⟩
      · rw [zs] at done
        simp only [Option.some.injEq, decide_eq_false_iff_not] at done
        have last : k + 1 = K := by omega_using [sum, pos, done]
        exact ⟨last ▸ is, last ▸ it⟩
      · rw [zs] at more
        simp only [Option.some.injEq, decide_eq_true_eq] at more
        exact ⟨remaining - 1, by omega_using [pos], k + 1, by omega_using [sum, pos], by omega_using [sum, more], is, it⟩) K
  exact loop.mono (fun s t ⟨hs, ht⟩ => ⟨0, by omega_using [], pos, hs, ht⟩) (fun _ _ h => h)

theorem exec_seqs_append {y : Prog isa} {ys : List (Prog isa)} :
    ∀ {x : Prog isa} {xs : List (Prog isa)} {s t : State} {tr : List Leak},
    Exec isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs ++ y :: ys)) s tr t →
    ∃ tr₁ tr₂ u, tr = tr₁ ++ tr₂ ∧ Exec isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) s tr₁ u ∧
      Exec isa (VG.Impl.Rsa.X86.Keys.seqs (y :: ys)) u tr₂ t
  | _, [], _, _, _, e => by
    cases e with
    | seq a b => exact ⟨_, _, _, rfl, a, b⟩
  | _, _ :: _, _, _, _, e => by
    cases e with
    | seq a b =>
      obtain ⟨tr₁, tr₂, u, rfl, b₁, b₂⟩ := exec_seqs_append b
      exact ⟨_, _, u, (List.append_assoc _ _ _).symm, .seq a b₁, b₂⟩

/-- A sequence, related in two parts. -/
theorem relSeqs {P R Q : State → State → Prop} {x y : Prog isa} {xs ys : List (Prog isa)}
    (h₁ : RelCT isa P (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) R)
    (h₂ : RelCT isa R (VG.Impl.Rsa.X86.Keys.seqs (y :: ys)) Q) :
    RelCT isa P (VG.Impl.Rsa.X86.Keys.seqs (x :: xs ++ y :: ys)) Q := by
  intro s t tr ur sf tf hp es et
  obtain ⟨a₁, a₂, u, rfl, e₁, e₂⟩ := exec_seqs_append es
  obtain ⟨b₁, b₂, v, rfl, f₁, f₂⟩ := exec_seqs_append et
  obtain ⟨rfl, hr⟩ := h₁ _ _ _ _ _ _ hp e₁ f₁
  obtain ⟨rfl, hq⟩ := h₂ _ _ _ _ _ _ hr e₂ f₂
  exact ⟨rfl, hq⟩

/-! ## Runs on the views, carried through code

A leaf needs its run on the view of its start. A run on the view of a whole sequence ends each part
at the view of where the state's own run ends it (`view_end`), so a run on the view of the code still
to come is carried from leaf to leaf with the state's correctness (`wp_viewRun`, `wp_viewRunApp`,
`wp_viewRunLoop`). -/

/-- A run on the view ends at the view of the run's end. -/
theorem view_end {c : Prog isa} {s z s' : State} {B : Addr} {Z : Nat} {tr tr' : List Leak}
    (hs : (⟨B, Z⟩ : Region) ∈ s.wr) (he : Exec isa c (view s B Z) tr z) (e : Exec isa c s tr' s') :
    view s' B Z = z := by
  have L := VG.Proof.Rsa.X86.InvBatchRt.Time.lift_exec hs he
  obtain ⟨-, rfl⟩ := Exec.det e L
  obtain ⟨hrd, hwr⟩ := VG.X86.Exec.rdwr he
  simp only [view, State.withRegions_rd, State.withRegions_wr] at hrd hwr
  simp only [view, State.withRegions_withRegions, State.withRegions_rd, State.withRegions_wr]
  rw [← hrd, ← hwr, State.withRegions_self]

theorem run_seq_left {c d : Prog isa} {S : State} (h : ∃ tr z, Exec isa (.seq c d) S tr z) :
    ∃ tr z, Exec isa c S tr z := by
  obtain ⟨_, _, e⟩ := h
  cases e with
  | seq a _ => exact ⟨_, _, a⟩

theorem run_app_left {x y : Prog isa} {xs ys : List (Prog isa)} {S : State}
    (h : ∃ tr z, Exec isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs ++ y :: ys)) S tr z) :
    ∃ tr z, Exec isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) S tr z := by
  obtain ⟨_, _, e⟩ := h
  obtain ⟨_, _, _, _, a, _⟩ := exec_seqs_append e
  exact ⟨_, _, a⟩

theorem run_loop_body {b : Prog isa} {c : Cond} {S : State} (h : ∃ tr z, Exec isa (.loop b c) S tr z) :
    ∃ tr z, Exec isa b S tr z := by
  obtain ⟨_, _, e⟩ := h
  cases e with
  | loopExit a _ => exact ⟨_, _, a⟩
  | loopNext a _ _ => exact ⟨_, _, a⟩

theorem wp_viewRun {c d : Prog isa} {v : State} {B : Addr} {Z : Nat} {F : State → Prop}
    (hs : (⟨B, Z⟩ : Region) ∈ v.wr) (hw : WP isa c v F)
    (hr : ∃ tr z, Exec isa (.seq c d) (view v B Z) tr z) :
    WP isa c v fun w => F w ∧ ∃ tr z, Exec isa d (view w B Z) tr z := by
  obtain ⟨_, _, e⟩ := hr
  cases e with
  | seq e₁ e₂ =>
    obtain ⟨tw, w, ew, fw⟩ := hw
    exact ⟨tw, w, ew, fw, _, _, (view_end hs e₁ ew) ▸ e₂⟩

theorem wp_viewRunApp {x y : Prog isa} {xs ys : List (Prog isa)} {v : State} {B : Addr} {Z : Nat}
    {F : State → Prop} (hs : (⟨B, Z⟩ : Region) ∈ v.wr) (hw : WP isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) v F)
    (hr : ∃ tr z, Exec isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs ++ y :: ys)) (view v B Z) tr z) :
    WP isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) v
      fun w => F w ∧ ∃ tr z, Exec isa (VG.Impl.Rsa.X86.Keys.seqs (y :: ys)) (view w B Z) tr z := by
  obtain ⟨_, _, e⟩ := hr
  obtain ⟨_, _, _, _, e₁, e₂⟩ := exec_seqs_append e
  obtain ⟨tw, w, ew, fw⟩ := hw
  exact ⟨tw, w, ew, fw, _, _, (view_end hs e₁ ew) ▸ e₂⟩

theorem wp_viewRunLoop {b : Prog isa} {c : Cond} {v : State} {B : Addr} {Z : Nat} {F : State → Prop}
    (hs : (⟨B, Z⟩ : Region) ∈ v.wr) (hw : WP isa b v F)
    (hr : ∃ tr z, Exec isa (.loop b c) (view v B Z) tr z) :
    WP isa b v fun w => F w ∧ (isa.eval c w = some true → ∃ tr z, Exec isa (.loop b c) (view w B Z) tr z) := by
  obtain ⟨_, _, e⟩ := hr
  obtain ⟨tw, w, ew, fw⟩ := hw
  cases e with
  | loopExit e₁ hc =>
    refine ⟨tw, w, ew, fw, fun h => ?_⟩
    rw [← view_end hs e₁ ew, eval_view, h] at hc
    cases hc
  | loopNext e₁ _ el => exact ⟨tw, w, ew, fw, fun _ => ⟨_, _, (view_end hs e₁ ew) ▸ el⟩⟩

/-- A loop's correctness, after a run of its body. -/
theorem wp_loop_cont {b : Prog isa} {c : Cond} {v : State} {Q : State → Prop} (h : WP isa (.loop b c) v Q) :
    WP isa b v fun w => (isa.eval c w = some true → WP isa (.loop b c) w Q) ∧
      (isa.eval c w = some false → Q w) := by
  obtain ⟨_, _, e, q⟩ := h
  cases e with
  | loopExit e₁ hc => exact ⟨_, _, e₁, ⟨fun h => (by rw [hc] at h; cases h), fun _ => q⟩⟩
  | loopNext e₁ hc el => exact ⟨_, _, e₁, ⟨fun _ => ⟨_, _, el, q⟩, fun h => (by rw [hc] at h; cases h)⟩⟩

/-- A leaf's start, kept by code that keeps `edi`, `esp` and everything outside the working space. -/
theorem P0.keep {g : Geo} {s t : State} {rs : List Reg} (h : P0 g s) (K : Keeps rs s t) (edi : .edi ∉ rs)
    (esp : .esp ∉ rs) (O : Outside g.B 0 g.Z s.mem t.mem) : P0 g t :=
  ⟨h.1.keep K edi esp O, h.2.1, h.2.2.keep K esp O⟩

/-- Public facts of the geometry: `n`'s length `a` in argument `nl`, and `W' ≤ w`. -/
def GA (g : Geo) (a : Nat) : Prop :=
  g.args VG.Impl.Rsa.X86.RecoverDetRt.nl = BitVec.ofNat 32 a ∧ VG.Proof.Rsa.X86.WordRt.wq a ≤ g.w

/-- A leaf's start kept by a step that changes only arrays `js` and header words `ds`. -/
theorem P0.keepK {g : Geo} {s t : State} {js ds : List Nat} {rs : List Reg} (h : P0 g s)
    (k : Keep g.B (VG.Proof.Rsa.X86.KeyRt.kw (16 * g.n + 24)) js ds s.mem t.mem) (hj : ∀ j ∈ js, j < 22)
    (hd : ∀ d ∈ ds, d + 4 ≤ VG.Impl.Rsa.X86.Keys.hdr) (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs) :
    P0 g t :=
  h.keep K edi esp (VG.Proof.Rsa.X86.KeyRt.keep_outside h.1.ws k hj hd)

/-! ## Leaves in code whose run is known

A state at a leaf's start, with the code `d` still to run: the leaf's start (`P0`), the header words
`ds` it reads (`vals`), the code's correctness `Q` and its run on the view. A leaf then needs only its
frame: where it leaves `P0` and the next leaf's header words (`contSeq`, `contApp`, `contLast`). -/

def Cn (g : Geo) (ds : List Nat) (vals : Nat → Nat) (d : Prog isa) (Q : State → Prop) (s : State) : Prop :=
  P0 g s ∧ (∀ x ∈ ds, w32 s.mem g.B x = vals x) ∧ WP isa d s Q ∧ ∃ tr z, Exec isa d (view s g.B g.Z) tr z

theorem contSeq {g : Geo} {c d : Prog isa} {ds ds' : List Nat} {vals vals' : Nat → Nat} {Q : State → Prop}
    (hds : ∀ x ∈ ds, x + 4 ≤ 160)
    (frame : ∀ s, Cn g ds vals (.seq c d) Q s → WP isa c s fun w => P0 g w ∧ ∀ x ∈ ds', w32 w.mem g.B x = vals' x)
    (h : OkK ds c) : RelCT isa (Both (Cn g ds vals (.seq c d) Q)) c (Both (Cn g ds' vals' d Q)) :=
  leafK vals hds (fun _ h => h.1) (fun _ h => h.2.1) (fun _ h => run_seq_left h.2.2.2)
    (fun s h => WP.mono (WP.and (frame s h) (WP.and (WP.seq_iff.mp h.2.2.1)
      (wp_viewRun h.1.1.ws.workspace.wr (WP.mono (frame s h) fun _ _ => trivial) h.2.2.2)))
      fun _ ⟨⟨p, v⟩, q, _, r⟩ => ⟨p, v, q, r⟩) h

theorem contApp {g : Geo} {x y : Prog isa} {xs ys : List (Prog isa)} {ds ds' : List Nat}
    {vals vals' : Nat → Nat} {Q : State → Prop} (hds : ∀ x ∈ ds, x + 4 ≤ 160)
    (frame : ∀ s, Cn g ds vals (VG.Impl.Rsa.X86.Keys.seqs (x :: xs ++ y :: ys)) Q s →
      WP isa (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) s fun w => P0 g w ∧ ∀ x ∈ ds', w32 w.mem g.B x = vals' x)
    (h : OkK ds (VG.Impl.Rsa.X86.Keys.seqs (x :: xs))) :
    RelCT isa (Both (Cn g ds vals (VG.Impl.Rsa.X86.Keys.seqs (x :: xs ++ y :: ys)) Q))
      (VG.Impl.Rsa.X86.Keys.seqs (x :: xs)) (Both (Cn g ds' vals' (VG.Impl.Rsa.X86.Keys.seqs (y :: ys)) Q)) := by
  refine leafK vals hds (fun _ h => h.1) (fun _ h => h.2.1) (fun _ h => run_app_left h.2.2.2) (fun s h => ?_) h
  obtain ⟨_, _, e, q⟩ := h.2.2.1
  obtain ⟨_, _, u, _, e₁, e₂⟩ := exec_seqs_append e
  exact WP.mono (WP.and (frame s h) (WP.and ⟨_, u, e₁, _, _, e₂, q⟩
    (wp_viewRunApp h.1.1.ws.workspace.wr (WP.mono (frame s h) fun _ _ => trivial) h.2.2.2)))
    fun _ ⟨⟨p, v⟩, q, _, r⟩ => ⟨p, v, q, r⟩

theorem contLast {g : Geo} {c : Prog isa} {ds : List Nat} {vals : Nat → Nat} {Q : State → Prop}
    (hds : ∀ x ∈ ds, x + 4 ≤ 160) (h : OkK ds c) : RelCT isa (Both (Cn g ds vals c Q)) c (Both Q) :=
  leafK vals hds (fun _ h => h.1) (fun _ h => h.2.1) (fun _ h => h.2.2.2) (fun _ h => h.2.2.1) h

/-- Two runs at stages, related as `RA`. -/
theorem RA.of {g : Geo} (pg : PubG g) {P : State → Prop} (hP : ∀ s, P s → MulPost g s) {s t : State}
    (hs : P s) (ht : P t) : RA P P s t := by
  obtain ⟨_, _, _, _, _, _, _, h⟩ := hP s hs
  obtain ⟨_, _, _, _, _, _, _, j⟩ := hP t ht
  exact ⟨ks_agree pg h j, hs, ht⟩

/-! ## The stage loops -/

section
open VG.X86.Wp
open VG.Impl.Mont.X86 (sc)

/-- `wordStagesL`'s halving of `sC4`. -/
abbrev halfC4 : List Instr := [.mov .eax (.mem (sc sC4)), .shift .shr .eax 1, .store (sc sC4) .eax,
  .alu .cmp .eax (.imm (BitVec.ofNat 32 4))]

/-- The working space at a stage's geometry. -/
abbrev WsG (g : Geo) (s : State) : Prop := Ws s g.B g.Z g.w VG.Impl.Rsa.X86.Recover.nArr

/-- `wordStagesL`'s loop after `i` stages: before stage `2^(k - i)`, or done, and whether a stage
follows. -/
def WL (Pre : Geo → Nat → State → Prop) (Fin : Geo → State → Prop) (k : Nat) (g : Geo) (i : Nat)
    (s : State) : Prop :=
  (if i ≤ k then Pre g (k - i) s else Fin g s) ∧ (0 < i → isa.eval .ae s = some (decide (i < k + 1)))

/-- `wordStagesL_ok`'s loop, related: its blocks are leaves (the limit and the halving read `sC4`),
the stage `body` related by the caller where it runs. -/
theorem relWordStagesL {g : Geo} {k lim : Nat} {limit : List Instr} {body : Prog isa}
    {S Fin : Geo → State → Prop} (Pre Post : Geo → Nat → State → Prop) (hk : k ≤ 20)
    (p0S : ∀ s, S g s → P0 g s) (p0Pre : ∀ j s, Pre g j s → P0 g s) (p0Post : ∀ j s, Post g j s → P0 g s)
    (vS : ∀ s, S g s → S g.vw (view s g.B g.Z)) (vPre : ∀ j s, Pre g j s → Pre g.vw j (view s g.B g.Z))
    (vPost : ∀ j s, Post g j s → Post g.vw j (view s g.B g.Z))
    (hs : ∀ g' s, S g' s → WsG g' s)
    (hinit : ∀ g' s t, S g' s → Keep g'.B g'.w [] [sC4] s.mem t.mem → slot t.mem g'.B sC4 = 4 * 2 ^ k →
      Keeps [.eax] s t → Pre g' k t)
    (hpre : ∀ g' j t, j ≤ k → Pre g' j t → WsG g' t ∧ slot t.mem g'.B sC4 = 4 * 2 ^ j)
    (hlimit : ∀ g' j t, j ≤ k → Pre g' j t → ∀ (is : List Instr) (Q : State → Prop),
      (∀ u, Keeps opRegs t u → u.mem = t.mem → (u.gpr .eax).toNat = lim → WP isa (.block is) u Q) →
      WP isa (.block (limit ++ is)) t Q)
    (hstable : ∀ g' j t u, j ≤ k → Pre g' j t → Keeps opRegs t u → u.mem = t.mem → Pre g' j u)
    (hskip : ∀ g' j t, j ≤ k → Pre g' j t → lim ≤ 4 * 2 ^ j → Post g' j t)
    (hpost : ∀ g' j t, j ≤ k → Post g' j t → WsG g' t ∧ slot t.mem g'.B sC4 = 4 * 2 ^ j)
    (hnext : ∀ g' j t u, j ≤ k → Post g' j t → Keep g'.B g'.w [] [sC4] t.mem u.mem →
      slot u.mem g'.B sC4 = 2 * 2 ^ j → Keeps opRegs t u → (0 < j → Pre g' (j - 1) u) ∧ (j = 0 → Fin g' u))
    (rbody : ∀ j, j ≤ k → 4 * 2 ^ j < lim → RelCT isa (Both (Pre g j)) body (Both (Post g j)))
    (cinit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (4 * 2 ^ k))), .store (sc sC4) .eax]))
    (clim : OkK [sC4] (.block (limit ++ ([.mov .ecx (.mem (sc sC4)), .alu .cmp .ecx (.reg .eax)] : List Instr))))
    (chalf : OkK [sC4] (.block halfC4)) :
    RelCT isa (Both (S g)) (wordStagesL (2 ^ k) limit body) (Both (Fin g)) := by
  have p20 : 2 ^ k ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hk
  have hds : ∀ d ∈ [sC4], d + 4 ≤ 160 := by decide
  unfold wordStagesL
  refine VG.RelCT.seq (R := Both (WL Pre Fin k g 0))
    (leafP (P := S) (Q := fun g' => WL Pre Fin k g' 0) (fun _ => 0) (by simp) p0S vS (by simp)
      (fun g' s hs' => ?_) cinit) ?_
  · have hw := hs g' s hs'
    refine wp_movS (v := BitVec.ofNat 32 (4 * 2 ^ k)) rfl fun s₁ U₁ _ => ?_
    refine storeHdr (hw.rest U₁.keeps) (by decide) .eax fun s₂ K₂ e₂ k₂ _ _ => WP.block_nil ?_
    refine ⟨?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [ite_eq_left (Nat.zero_le _), Nat.sub_zero]
    exact hinit g' s s₂ hs' (by rw [U₁.mem] at K₂; exact K₂) (by rw [e₂, U₁.gpr, ofNat_lt_toNat (by omega_using [p20])])
      (U₁.keeps.trans (k₂.mono (by simp)))
  refine (relLoopB (WL Pre Fin k g) (K := k + 1) (by omega_using []) (fun i hi => ?_)
      (fun i s hi _ hs => hs.2 hi)).mono (fun _ _ h => h) (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩)
  rotate_left
  · have := hs.1; rwa [ite_eq_right (by omega_using [])] at this
  · have := ht.1; rwa [ite_eq_right (by omega_using [])] at this
  obtain ⟨j, hjd⟩ : ∃ j, j = k - i := ⟨_, rfl⟩
  have hj : j ≤ k := by omega_using [hjd]
  have pj : 2 ^ j ≤ 2 ^ 20 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hj) p20
  have Pi : ∀ g' s, WL Pre Fin k g' i s → Pre g' j s := fun g' s h => by
    have := h.1; rwa [ite_eq_left (by omega_using [hi]), ← hjd] at this
  simp only [VG.Impl.Rsa.X86.Keys.seqs]
  refine VG.RelCT.seq (R := Both (fun s => Pre g j s ∧ isa.eval .b s = some (decide (4 * 2 ^ j < lim))))
    (leafP (P := fun g' => WL Pre Fin k g' i)
      (Q := fun g' s => Pre g' j s ∧ isa.eval .b s = some (decide (4 * 2 ^ j < lim)))
      (fun _ => 4 * 2 ^ j) hds (fun s h => p0Pre j s (Pi g s h))
      (fun s h => ⟨by rw [ite_eq_left (by omega_using [hi]), ← hjd]; exact vPre j s (Pi g s h),
        fun hi => by rw [eval_view]; exact h.2 hi⟩)
      (fun s h d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact (hpre g j s hj (Pi g s h)).2)
      (fun g' v h => ?_) clim)
    (VG.RelCT.seq (R := Both (Post g j)) (VG.RelCT.ite (fun s t ⟨hs, ht⟩ => hs.2.trans ht.2.symm) ?_ ?_)
      (leafP (P := fun g' s => Post g' j s) (Q := fun g' => WL Pre Fin k g' (i + 1)) (fun _ => 4 * 2 ^ j) hds (p0Post j) (vPost j)
        (fun s h d hd => by
          simp only [List.mem_singleton] at hd; subst hd; exact (hpost g j s hj h).2)
        (fun g' t Po => ?_) chalf))
  · have P := Pi g' v h
    obtain ⟨wv, sv⟩ := hpre g' j v hj P
    refine hlimit g' j v hj P _ _ fun u₁ K₁ m₁ e₁ => ?_
    have wu : WsG g' u₁ := wv.rest K₁
    refine wp_movS (readHdr wu (by decide)) fun u₂ U₂ _ => ?_
    refine VG.Proof.Mont.X86.Square.wp_cmpCF (v := u₂.gpr .eax) rfl fun u₃ F₃ c₃ => WP.block_nil ?_
    have Pu := hstable g' j v u₃ hj P (K₁.trans ((U₂.keeps.mono (by simp)).trans (fupd_keeps F₃ _)))
      (by rw [F₃.mem, U₂.mem, m₁])
    have ecx : (u₂.gpr .ecx).toNat = 4 * 2 ^ j := by rw [U₂.gpr, m₁, sv, ofNat_lt_toNat (by omega_using [pj])]
    have eax : (u₂.gpr .eax).toNat = lim := by rw [U₂.other _ (by decide), e₁]
    rw [ecx, eax] at c₃
    exact ⟨Pu, c₃⟩
  · by_cases hl : 4 * 2 ^ j < lim
    · exact (rbody j hj hl).mono (fun s t ⟨⟨hs, ht⟩, _⟩ => ⟨hs.1, ht.1⟩) fun _ _ h => h
    · intro s t _ _ _ _ ⟨⟨hs, _⟩, e⟩ _ _
      rw [hs.2] at e
      simp [hl] at e
  · refine VG.RelCT.block_nil fun s t ⟨⟨hs, ht⟩, e⟩ => ?_
    rw [hs.2] at e
    have hl : lim ≤ 4 * 2 ^ j := by simp at e; omega_using [e]
    exact ⟨hskip g j s hj hs.1 hl, hskip g j t hj ht.1 hl⟩
  · obtain ⟨wt, st⟩ := hpost g' j t hj Po
    refine wp_movS (readHdr wt (by decide)) fun t₁ T₁ _ => ?_
    refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t₂ T₂ => ?_
    have e₂ : (t₂.gpr .eax).toNat = 2 * 2 ^ j := by
      rw [T₂.gpr, BitVec.toNat_ushiftRight, T₁.gpr, st, ofNat_lt_toNat (by omega_using [pj]), Nat.shiftRight_eq_div_pow]
      omega_using []
    have w₂ : WsG g' t₂ := wt.rest (T₁.keeps.trans T₂.keeps)
    refine storeHdr w₂ (by decide) .eax fun t₃ K₃ s₃ k₃ _ _ => ?_
    refine VG.Proof.Mont.X86.Square.wp_cmpCF (v := BitVec.ofNat 32 4) rfl fun t₄ F₄ c₄ => WP.block_nil ?_
    have m₂ : t₂.mem = t.mem := by rw [T₂.mem, T₁.mem]
    have N := hnext g' j t t₄ hj Po (by rw [F₄.mem, ← m₂]; exact K₃) (by rw [F₄.mem, s₃, e₂])
      ((T₁.keeps.mono (by simp)).trans ((T₂.keeps.mono (by simp)).trans ((k₃.mono (by simp)).trans
        (fupd_keeps F₄ _))))
    rw [k₃.1 .eax (by simp), e₂, ofNat_lt_toNat (by decide)] at c₄
    have ev : isa.eval .ae t₄ = t₄.cf.map (!·) := rfl
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · refine ⟨by rw [ite_eq_right (by omega_using [hjd, hj0])]; exact N.2 hj0, fun _ => ?_⟩
      rw [ev, c₄, hj0]
      simp only [Nat.pow_zero, Option.map_some]
      congr 1
      simp only [Nat.reduceMul, Nat.reduceLT, decide_true, Bool.not_true]
      exact (decide_eq_false (by omega_using [hjd, hj0])).symm
    · refine ⟨by rw [ite_eq_left (by omega_using [hjd, hj0]), show k - (i + 1) = j - 1 by omega_using [hjd]]; exact N.1 hj0, fun _ => ?_⟩
      have : ¬ 2 * 2 ^ j < 4 := by have := Nat.pow_le_pow_right (n := 2) (by decide) hj0; omega
      rw [ev, c₄]
      simp only [this, decide_false, Option.map_some, Bool.not_false]
      exact congrArg some (decide_eq_true (by omega_using [hjd, hj0])).symm

/-- `bitStagesL`'s halving of `sB`. -/
abbrev halfB (m : Nat) : List Instr := [.mov .eax (.mem (sc sB)), .shift .shr .eax 1, .store (sc sB) .eax,
  .alu .cmp .eax (.imm (BitVec.ofNat 32 (2 ^ m)))]

/-- `bitStagesL`'s loop after `i` stages: before stage `2^(k - i)`, or done, and whether a stage
follows. -/
def BL (Pre : Geo → Nat → State → Prop) (Fin : Geo → State → Prop) (k m : Nat) (g : Geo) (i : Nat)
    (s : State) : Prop :=
  (if i ≤ k - m then Pre g (k - i) s else Fin g s) ∧
    (0 < i → isa.eval .ae s = some (decide (i < k - m + 1)))

/-- `bitStagesL_ok`'s loop, related: the stages `body` related by the caller. -/
theorem relBitStagesL {g : Geo} {k m : Nat} {body : Prog isa}
    {S Fin : Geo → State → Prop} (Pre Post : Geo → Nat → State → Prop) (hk : k ≤ 20) (hmk : m ≤ k)
    (p0S : ∀ s, S g s → P0 g s) (p0Post : ∀ j s, Post g j s → P0 g s)
    (vS : ∀ s, S g s → S g.vw (view s g.B g.Z))
    (vPost : ∀ j s, Post g j s → Post g.vw j (view s g.B g.Z))
    (hs : ∀ g' s, S g' s → WsG g' s)
    (hinit : ∀ g' s t, S g' s → Keep g'.B g'.w [] [sB] s.mem t.mem → slot t.mem g'.B sB = 2 ^ k →
      Keeps [.eax] s t → Pre g' k t)
    (hpost : ∀ g' j t, m ≤ j → j ≤ k → Post g' j t → WsG g' t ∧ slot t.mem g'.B sB = 2 ^ j)
    (hnext : ∀ g' j t u, m ≤ j → j ≤ k → Post g' j t → Keep g'.B g'.w [] [sB] t.mem u.mem →
      slot u.mem g'.B sB = 2 ^ j / 2 → Keeps opRegs t u → (m < j → Pre g' (j - 1) u) ∧ (j = m → Fin g' u))
    (rbody : ∀ j, m ≤ j → j ≤ k → RelCT isa (Both (Pre g j)) body (Both (Post g j)))
    (cinit : OkK [] (.block [.mov .eax (.imm (BitVec.ofNat 32 (2 ^ k))), .store (sc sB) .eax]))
    (chalf : OkK [sB] (.block (halfB m))) :
    RelCT isa (Both (S g)) (bitStagesL (2 ^ k) (2 ^ m) body) (Both (Fin g)) := by
  have p20 : 2 ^ k ≤ 2 ^ 20 := Nat.pow_le_pow_right (by decide) hk
  have pm : 2 ^ m ≤ 2 ^ 20 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hmk) p20
  unfold bitStagesL
  refine VG.RelCT.seq (R := Both (BL Pre Fin k m g 0))
    (leafP (P := S) (Q := fun g' => BL Pre Fin k m g' 0) (fun _ => 0) (by simp) p0S vS (by simp)
      (fun g' s hs' => ?_) cinit) ?_
  · have hw := hs g' s hs'
    refine wp_movS (v := BitVec.ofNat 32 (2 ^ k)) rfl fun s₁ U₁ _ => ?_
    refine storeHdr (hw.rest U₁.keeps) (by decide) .eax fun s₂ K₂ e₂ k₂ _ _ => WP.block_nil ?_
    refine ⟨?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [ite_eq_left (Nat.zero_le _), Nat.sub_zero]
    exact hinit g' s s₂ hs' (by rw [U₁.mem] at K₂; exact K₂) (by rw [e₂, U₁.gpr, ofNat_lt_toNat (by omega_using [p20])])
      (U₁.keeps.trans (k₂.mono (by simp)))
  refine (relLoopB (BL Pre Fin k m g) (K := k - m + 1) (by omega_using []) (fun i hi => ?_)
      (fun i s hi _ hs => hs.2 hi)).mono (fun _ _ h => h) (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩)
  rotate_left
  · have := hs.1; rwa [ite_eq_right (by omega_using [])] at this
  · have := ht.1; rwa [ite_eq_right (by omega_using [])] at this
  obtain ⟨j, hjd⟩ : ∃ j, j = k - i := ⟨_, rfl⟩
  have hj : j ≤ k := by omega_using [hjd]
  have hmj : m ≤ j := by omega_using [hmk, hi, hjd]
  have pj : 2 ^ j ≤ 2 ^ 20 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hj) p20
  refine VG.RelCT.seq ((rbody j hmj hj).mono (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩) fun _ _ h => h)
    (leafP (P := fun g' s => Post g' j s) (Q := fun g' => BL Pre Fin k m g' (i + 1)) (fun _ => 2 ^ j)
      (by decide) (p0Post j) (vPost j)
      (fun s h d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact (hpost g j s hmj hj h).2)
      (fun g' t Po => ?_) chalf)
  · have := hs.1; rwa [ite_eq_left (by omega_using [hi]), ← hjd] at this
  · have := ht.1; rwa [ite_eq_left (by omega_using [hi]), ← hjd] at this
  obtain ⟨wt, st⟩ := hpost g' j t hmj hj Po
  refine wp_movS (readHdr wt (by decide)) fun t₁ T₁ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun t₂ T₂ => ?_
  have e₂ : (t₂.gpr .eax).toNat = 2 ^ j / 2 := by
    rw [T₂.gpr, BitVec.toNat_ushiftRight, T₁.gpr, st, ofNat_lt_toNat (by omega_using [pj]), Nat.shiftRight_eq_div_pow,
      Nat.pow_one]
  have w₂ : WsG g' t₂ := wt.rest (T₁.keeps.trans T₂.keeps)
  refine storeHdr w₂ (by decide) .eax fun t₃ K₃ s₃ k₃ _ _ => ?_
  refine VG.Proof.Mont.X86.Square.wp_cmpCF (v := BitVec.ofNat 32 (2 ^ m)) rfl fun t₄ F₄ c₄ => WP.block_nil ?_
  have m₂ : t₂.mem = t.mem := by rw [T₂.mem, T₁.mem]
  have Nx := hnext g' j t t₄ hmj hj Po (by rw [F₄.mem, ← m₂]; exact K₃) (by rw [F₄.mem, s₃, e₂])
    ((T₁.keeps.mono (by simp)).trans ((T₂.keeps.mono (by simp)).trans ((k₃.mono (by simp)).trans
      (fupd_keeps F₄ _))))
  rw [k₃.1 .eax (by simp), e₂, ofNat_lt_toNat (by omega_using [pm])] at c₄
  have ev : isa.eval .ae t₄ = t₄.cf.map (!·) := rfl
  rcases Nat.eq_or_lt_of_le hmj with hjm | hlt
  · have : 2 ^ m / 2 < 2 ^ m := Nat.div_lt_self (Nat.two_pow_pos _) (by decide)
    refine ⟨by rw [ite_eq_right (by omega_using [hjd, hjm])]; exact Nx.2 hjm.symm, fun _ => ?_⟩
    rw [ev, c₄, ← hjm]
    simp only [this, decide_true, Option.map_some, Bool.not_true]
    exact congrArg some (decide_eq_false (by omega_using [hjd, hjm])).symm
  · have : ¬ 2 ^ j / 2 < 2 ^ m := by
      have e : 2 ^ j = 2 ^ (j - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega_using [hlt]
      rw [e, Nat.mul_div_cancel _ (by decide)]
      exact Nat.not_lt.mpr (Nat.pow_le_pow_right (by decide) (by omega_using [hlt]))
    refine ⟨by rw [ite_eq_left (by omega_using [hjd, hlt]), show k - (i + 1) = j - 1 by omega_using [hjd]]; exact Nx.1 hlt, fun _ => ?_⟩
    rw [ev, c₄]
    simp only [this, decide_false, Option.map_some, Bool.not_false]
    exact congrArg some (decide_eq_true (by omega_using [hjd, hlt])).symm

/-- `timesH`'s count down in `sBc`. -/
abbrev downBc : List Instr := [.mov .eax (.mem (sc sBc)), .alu .sub .eax (.imm 1), .store (sc sBc) .eax]

/-- `timesH`'s loop after `i` runs, and whether a run follows. -/
def TL (Pre : Geo → Nat → State → Prop) (Fin : Geo → State → Prop) (b : Nat) (g : Geo) (i : Nat)
    (s : State) : Prop :=
  (if i < b then Pre g i s else Fin g s) ∧ (0 < i → isa.eval .ne s = some (decide (i < b)))

/-- `timesH_ok`'s loop, related: `body` related by the caller. -/
theorem relTimesH {g : Geo} {b : Nat} {body : Prog isa}
    {S Fin : Geo → State → Prop} (Pre Post : Geo → Nat → State → Prop) (hb : 0 < b) (hb32 : b < 2 ^ 32)
    (p0S : ∀ s, S g s → P0 g s) (p0Post : ∀ i s, Post g i s → P0 g s)
    (vS : ∀ s, S g s → S g.vw (view s g.B g.Z))
    (vPost : ∀ i s, Post g i s → Post g.vw i (view s g.B g.Z))
    (hs : ∀ g' s, S g' s → WsG g' s ∧ slot s.mem g'.B sB = b)
    (hinit : ∀ g' s t, S g' s → Keep g'.B g'.w [] [sBc] s.mem t.mem → slot t.mem g'.B sBc = b →
      Keeps [.eax] s t → Pre g' 0 t)
    (hpost : ∀ g' i t, i < b → Post g' i t → WsG g' t ∧ slot t.mem g'.B sBc = b - i)
    (hnext : ∀ g' i t u, i < b → Post g' i t → Keep g'.B g'.w [] [sBc] t.mem u.mem →
      slot u.mem g'.B sBc = b - (i + 1) → Keeps opRegs t u → (i + 1 < b → Pre g' (i + 1) u) ∧ (i + 1 = b → Fin g' u))
    (rbody : ∀ i, i < b → RelCT isa (Both (Pre g i)) body (Both (Post g i)))
    (cinit : OkK [sB] (.block [.mov .eax (.mem (sc sB)), .store (sc sBc) .eax]))
    (cdown : OkK [sBc] (.block downBc)) :
    RelCT isa (Both (S g)) (timesH body) (Both (Fin g)) := by
  unfold timesH
  refine VG.RelCT.seq (R := Both (TL Pre Fin b g 0))
    (leafP (P := S) (Q := fun g' => TL Pre Fin b g' 0) (fun _ => b) (by decide) p0S vS
      (fun s h d hd => by simp only [List.mem_singleton] at hd; subst hd; exact (hs g s h).2)
      (fun g' s hs' => ?_) cinit) ?_
  · obtain ⟨hw, hsB⟩ := hs g' s hs'
    refine wp_movS (readHdr hw (by decide)) fun s₁ U₁ _ => ?_
    refine storeHdr (hw.rest U₁.keeps) (by decide) .eax fun s₂ K₂ e₂ k₂ _ _ => WP.block_nil ?_
    refine ⟨?_, fun h => absurd h (Nat.lt_irrefl 0)⟩
    rw [ite_eq_left hb]
    exact hinit g' s s₂ hs' (by rw [U₁.mem] at K₂; exact K₂) (by rw [e₂, U₁.gpr, hsB, ofNat_lt_toNat hb32])
      (U₁.keeps.trans (k₂.mono (by simp)))
  refine (relLoopB (TL Pre Fin b g) (K := b) hb (fun i hi => ?_)
      (fun i s hi _ hs => hs.2 hi)).mono (fun _ _ h => h) (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩)
  rotate_left
  · have := hs.1; rwa [ite_eq_right (Nat.lt_irrefl _)] at this
  · have := ht.1; rwa [ite_eq_right (Nat.lt_irrefl _)] at this
  refine VG.RelCT.seq ((rbody i hi).mono (fun s t ⟨hs, ht⟩ => ⟨?_, ?_⟩) fun _ _ h => h)
    (leafP (P := fun g' s => Post g' i s) (Q := fun g' => TL Pre Fin b g' (i + 1)) (fun _ => b - i)
      (by decide) (p0Post i) (vPost i)
      (fun s h d hd => by
        simp only [List.mem_singleton] at hd; subst hd; exact (hpost g i s hi h).2)
      (fun g' t Po => ?_) cdown)
  · have := hs.1; rwa [ite_eq_left hi] at this
  · have := ht.1; rwa [ite_eq_left hi] at this
  obtain ⟨wt, st⟩ := hpost g' i t hi Po
  refine wp_movS (readHdr wt (by decide)) fun t₁ T₁ _ => ?_
  refine VG.Proof.Mont.X86.Rt.wp_subZ (v := BitVec.ofNat 32 1) rfl fun t₂ T₂ z₂ => ?_
  have e₂ : (t₂.gpr .eax).toNat = b - (i + 1) := by
    rw [T₂.gpr, T₁.gpr, st, BitVec.toNat_sub, ofNat_lt_toNat (x := b - i) (by omega_using [hb32]),
      ofNat_lt_toNat (x := 1) (by decide)]
    omega_using [hb32, hi]
  have w₂ : WsG g' t₂ := wt.rest (T₁.keeps.trans T₂.keeps)
  refine storeHdr w₂ (by decide) .eax fun t₃ K₃ s₃ k₃ zf₃ _ => WP.block_nil ?_
  have m₂ : t₂.mem = t.mem := by rw [T₂.mem, T₁.mem]
  have Nx := hnext g' i t t₃ hi Po (by rw [← m₂]; exact K₃) (by rw [s₃, e₂])
    ((T₁.keeps.mono (by simp)).trans ((T₂.keeps.mono (by simp)).trans (k₃.mono (by simp))))
  have zz : (t₁.gpr .eax - BitVec.ofNat 32 1 == 0) = decide (i + 1 = b) := by
    rw [← T₂.gpr]
    by_cases h : i + 1 = b
    · simp only [h, decide_true, beq_iff_eq]
      apply BitVec.eq_of_toNat_eq; rw [e₂]; simp; omega_using [h]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro e; have := congrArg BitVec.toNat e; rw [e₂] at this; simp at this; omega_using [hi, h, this]
  rw [zz] at z₂
  have ev : isa.eval .ne t₃ = t₃.zf.map (!·) := rfl
  by_cases h : i + 1 = b
  · refine ⟨by rw [ite_eq_right (by omega_using [h])]; exact Nx.2 h, fun _ => ?_⟩
    rw [ev, zf₃, z₂]
    simp [h]
  · refine ⟨by rw [ite_eq_left (by omega_using [hi, h])]; exact Nx.1 (by omega_using [hi, h]), fun _ => ?_⟩
    rw [ev, zf₃, z₂]
    simp only [h, decide_false, Option.map_some, Bool.not_false]
    exact congrArg some (decide_eq_true (by omega_using [hi, h])).symm

end

end VG.Proof.Rsa.X86.Recover
