module

public import VerifiedGarbage.Proof.Ffdh.X86.Stages
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
public import VerifiedGarbage.Impl.Ffdh.X86.Domain
meta import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimePower
meta import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeWindow
import VerifiedGarbage.Proof.Ffdh.X86.EntryCT
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.TimeMul
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Framework.X86.CallBody
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# FFDH on i686: the traces of the stages

Runs of the same stage from states with the same public values (`Both P`,
for a `P` that fixes them) leak the same traces: the stages without calls
are checked by the taint analysis from the arguments (`aRel`), a power
modulo p by private CRT's windowed power (`powP_trace`), and a branch on a
`Gate` whose condition `P` fixes takes the same side in both runs
(`gate_relCT`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt
open VG.Proof.Bignum.X86.PublicRt (Both relCT_both)

variable {Ex : List Region → List Region → Prop} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}
  {sp : BitVec 32}

/-- A run after a stage. -/
theorem run_step {s u : State} (R : Run Ex base bytes len args sp s) (S : Step Ex base bytes len args s u) :
    Run Ex base bytes len args sp u :=
  ⟨S.inp, R.2.1.keep S.keeps, S.esp.trans R.2.2⟩

/-- Code the taint analysis checks from the arguments, with what each run reaches. -/
theorem aRel {P F : State → Prop} {c : Prog isa} (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hc : ACheck c) (hw : ∀ x, P x → WP isa c x F) : RelCT isa (Both P) c (Both F) :=
  relCT_both (RelCT.taint (A := taint) τA (fun _ _ h => (hP _ h.1).agree (hP _ h.2)) hc) hw

/-- Code whose runs from `Run` leak the same traces, with what each run reaches. -/
theorem runRel {P F : State → Prop} {c : Prog isa} (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hct : RelCT isa (Both (Run Ex base bytes len args sp)) c fun _ _ => True) (hw : ∀ x, P x → WP isa c x F) :
    RelCT isa (Both P) c (Both F) :=
  relCT_both (hct.mono (fun _ _ h => ⟨hP _ h.1, hP _ h.2⟩) fun _ _ h => h) hw

/-- Code the taint analysis checks from the arguments, at the end. -/
theorem aEnd {P : State → Prop} {c : Prog isa} (hP : ∀ x, P x → Run Ex base bytes len args sp x)
    (hc : ACheck c) : RelCT isa (Both P) c fun _ _ => True :=
  RelCT.taint (A := taint) τA (fun _ _ h => (hP _ h.1).agree (hP _ h.2)) hc

/-- A branch on a gate the runs' `P` fixes. -/
theorem gate_relCT {P : State → Prop} {C : Prop} (hg : ∀ x, P x → Gate x C) {th el : Prog isa}
    {Q : State → State → Prop} (ht : RelCT isa (Both fun x => P x ∧ C) th Q)
    (he : RelCT isa (Both fun x => P x ∧ ¬ C) el Q) : RelCT isa (Both P) (.ite .e th el) Q := by
  refine VG.RelCT.ite (fun x y h => (hg _ h.1).agree (hg _ h.2)) (ht.mono (fun x y h => ?_) fun _ _ h => h)
    (he.mono (fun x y h => ?_) fun _ _ h => h)
  · obtain ⟨⟨P₁, P₂⟩, e⟩ := h
    obtain ⟨b, hb, i⟩ := hg _ P₁
    rw [hb] at e
    cases Option.some.inj e
    have c := i.mp rfl
    exact ⟨⟨P₁, c⟩, P₂, c⟩
  · obtain ⟨⟨P₁, P₂⟩, e⟩ := h
    obtain ⟨b, hb, i⟩ := hg _ P₁
    rw [hb] at e
    cases Option.some.inj e
    have c : ¬ C := fun c => by have := i.mpr c; cases this
    exact ⟨⟨P₁, c⟩, P₂, c⟩

theorem ctxP_check : ACheck (copy (.slot .wide 9) (.slot .wide 0) (one .wide)) := by
  dsimp only [ACheck]; taint_decide

/-- The callee, from the copy of the arguments: `prepare_relCT`, on its states narrowed to the working space. -/
theorem callee_relCT :
    RelCT isa (Both (CalleeAt base bytes len args sp)) (prepare .wide) fun _ _ => True := by
  have run : ∀ u, CalleeAt base bytes len args sp u →
      Run (fun _ _ => True) base bytes len args (sp - BitVec.ofNat 32 80) (u.withRegions (u.rd ++ u.wr) [⟨base, bytes⟩]) := fun u C =>
    ⟨VG.Proof.Ffdh.X86.In.narrow C.1 trivial, ⟨C.1.top, fun r hr => by rw [List.mem_singleton.mp hr]; exact C.2.2⟩, C.2.1⟩
  have cov : ∀ u, CalleeAt base bytes len args sp u →
      Covers ((u.rd ++ u.wr) ++ [⟨base, bytes⟩]) (u.rd ++ u.wr) ∧ Covers [⟨base, bytes⟩] u.wr := fun u C => by
    have c : Covers [⟨base, bytes⟩] u.wr :=
      Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact C.1.scratch.wr
    exact ⟨Covers.append_left (Covers.refl _) (Covers.right c), c⟩
  refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun u => u.rd ++ u.wr) (fun _ => [⟨base, bytes⟩])
    (fun f g ⟨C₁, C₂⟩ => ?_) ((prepare_relCT (Ex := fun _ _ => True) (base := base) (bytes := bytes) (len := len) (args := args)
      (sp := sp - BitVec.ofNat 32 80) .wide).mono
      (fun _ _ h => h) fun _ _ _ => trivial)
  exact ⟨(cov f C₁).1, (cov f C₁).2, (cov g C₂).1, (cov g C₂).2, ⟨_, prepCtx_ok (run f C₁).1 .wide⟩,
    ⟨_, prepCtx_ok (run g C₂).1 .wide⟩, run f C₁, run g C₂⟩

/-- The call of `prepare .wide`: the copy of the arguments checked by the taint analysis from `esp`, and the
callee by `callee_relCT`. -/
theorem prepCall_trace :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) Impl.Ffdh.X86.prepCall fun _ _ => True := by
  unfold Impl.Ffdh.X86.prepCall
  refine RelCT.callBody (R := fun a b => ∃ s₁ s₂,
      (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) s₁ s₂ ∧
        a = s₁.callEntry ∧ b = s₂.callEntry) ?_ (fun s t h => ⟨s, t, h, rfl, rfl⟩)
    (fun _ _ h => h.1.1.2.2.trans h.2.1.2.2.symm)
  refine RelCT.frameAlloc (R := fun _ _ => True) (VG.RelCT.seq ?_ (callee_relCT (base := base) (bytes := bytes) (len := len) (args := args) (sp := sp)))
  refine ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (hc := .block [])
    (by rfl)).wp (F₁ := CalleeAt base bytes len args sp) (F₂ := CalleeAt base bytes len args sp)
      fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
  · obtain rfl := List.mem_singleton.mp hr
    obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨⟨R₁, -⟩, ⟨R₂, -⟩⟩, rfl, rfl⟩, rfl, rfl⟩ := h
    rw [allocFrame_esp, allocFrame_esp, State.callEntry_esp, State.callEntry_esp, R₁.2.2, R₂.2.2]
  · obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨⟨R₁, F₁⟩, ⟨R₂, F₂⟩⟩, rfl, rfl⟩, rfl, rfl⟩ := h
    obtain w : ∀ {x : State}, Run Ex base bytes len args sp x → RoomF sp base bytes →
        WP isa (.block ((List.range 18).flatMap Impl.Ffdh.X86.copyArg)) (allocFrame Impl.Ffdh.X86.argsFrame x.callEntry)
          (CalleeAt base bytes len args sp) := fun {x} R F => by
      have e := R.2.2
      rw [← e] at F ⊢
      exact callee_at R.1 F
    exact ⟨w R₁ F₁, w R₂ F₂⟩

/-- One in slot 3 and `R²` modulo slot 0 in slot 4: what the windowed power needs of a prepared context. -/
abbrev PrepFacts (base : Addr) (len : Nat) (s : State) : Prop :=
  sv s.mem base len .wide 3 = 1 ∧ sv s.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % sv s.mem base len .wide 0

/-- The call of `prepare .wide`, with what each run reaches. -/
theorem prepCall_relCTF :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) Impl.Ffdh.X86.prepCall
      (Both fun u => WSt Ex base bytes len args sp .wide [3, 4] 0 u ∧ PrepFacts base len u) := by
  refine relCT_both prepCall_trace fun x ⟨R, F⟩ => ?_
  have e := R.2.2
  rw [← e] at F
  refine WP.mono (prepCall_ok R.1 F) fun u ⟨C, one, R2, _, K⟩ => ?_
  obtain hM := safeM_gt (sv x.mem base len .wide 0)
  refine ⟨⟨_, C, fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _), R.2.1.keep K, (K.1 _ (by decide)).trans e⟩,
    one, by rw [C.mod]; exact R2⟩
  rcases List.mem_cons.mp hj with rfl | hj
  · rw [one]; exact hM
  · rw [List.mem_singleton.mp hj, R2]; exact Nat.mod_lt _ (by omega_arith)

theorem prepCall_relCT :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) Impl.Ffdh.X86.prepCall
      (Both (WSt Ex base bytes len args sp .wide [3, 4] 0)) :=
  prepCall_relCTF.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2.1⟩

/-- A copy into slot 0 checked by the taint analysis, then `prepCall`. -/
theorem copyPrep_relCTF {j : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17)
    (hc : ACheck (copy (.slot .wide j) (.slot .wide 0) (one .wide))) :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes)
      (.seq (copy (.slot .wide j) (.slot .wide 0) (one .wide)) Impl.Ffdh.X86.prepCall)
      (Both fun u => WSt Ex base bytes len args sp .wide [3, 4] 0 u ∧ PrepFacts base len u) :=
  VG.RelCT.seq (taint_both (P := fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes)
    (F := fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes)
    (fun _ _ R₁ R₂ => R₁.1.agree R₂.1) _ hc fun _ R =>
      WP.mono (copyDown_run (j := j) (d := 0) hj9 hj (by decide) R.1) fun _ h => ⟨h, R.2⟩) prepCall_relCTF

theorem copyPrep_relCT {j : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17)
    (hc : ACheck (copy (.slot .wide j) (.slot .wide 0) (one .wide))) :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes)
      (.seq (copy (.slot .wide j) (.slot .wide 0) (one .wide)) Impl.Ffdh.X86.prepCall)
      (Both (WSt Ex base bytes len args sp .wide [3, 4] 0)) :=
  (copyPrep_relCTF hj9 hj hc).mono (fun _ _ h => h) fun _ _ h => ⟨h.1.1, h.2.1⟩

/-- The context of p: the copy of p checked by the taint analysis, and its setup by `prepCall`. -/
theorem ctxP_relCTF :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) Impl.Ffdh.X86.ctxP
      (Both fun u => WSt Ex base bytes len args sp .wide [3, 4] 0 u ∧ PrepFacts base len u) :=
  copyPrep_relCTF (by decide) (by decide) ctxP_check

theorem ctxP_relCT :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) Impl.Ffdh.X86.ctxP
      (Both (WSt Ex base bytes len args sp .wide [3, 4] 0)) :=
  copyPrep_relCT (by decide) (by decide) ctxP_check

/-! ## The calls of the windowed powers -/

/-- A run's callee: from a run of `P` by the copy of the arguments. -/
abbrev CalleeOf (P : State → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (sp : BitVec 32)
    (u : State) : Prop :=
  ∃ s, P s ∧ CalleeAt base bytes len args sp u ∧ Frame (frameF base sp []) s.mem u.mem

/-- A call by `argCall` of `b`: the copy of the arguments checked by the taint analysis from `esp`, and `b`
related on the callee's states narrowed to the working space. -/
theorem argCall_trace {name : String} {b : Prog isa} {P Pc : State → Prop}
    (hP : ∀ s, P s → Run Ex base bytes len args sp s ∧ RoomF sp base bytes)
    (hc : ∀ s u, P s → CalleeAt base bytes len args sp u → Frame (frameF base sp []) s.mem u.mem →
      Pc (u.withRegions (u.rd ++ u.wr) [⟨base, bytes⟩]) ∧ ∃ F, WP isa b (u.withRegions (u.rd ++ u.wr) [⟨base, bytes⟩]) F)
    (hb : RelCT isa (Both Pc) b fun _ _ => True) :
    RelCT isa (Both P) (Impl.Ffdh.X86.argCall name b) fun _ _ => True := by
  unfold Impl.Ffdh.X86.argCall
  refine RelCT.callBody (R := fun a b => ∃ s₁ s₂, Both P s₁ s₂ ∧ a = s₁.callEntry ∧ b = s₂.callEntry) ?_
    (fun s t h => ⟨s, t, h, rfl, rfl⟩) (fun _ _ h => (hP _ h.1).1.2.2.trans (hP _ h.2).1.2.2.symm)
  refine RelCT.frameAlloc (R := fun _ _ => True)
    (VG.RelCT.seq (R := Both (CalleeOf P base bytes len args sp)) ?_ ?_)
  · refine ((RelCT.taint (A := taint) (τr [.esp]) (fun a b h => agree_regs fun r hr => ?_) (hc := .block [])
      (by rfl)).wp (F₁ := CalleeOf P base bytes len args sp) (F₂ := CalleeOf P base bytes len args sp)
        fun a b h => ?_).mono (fun _ _ h => h) fun _ _ h => h.2
    · obtain rfl := List.mem_singleton.mp hr
      obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨P₁, P₂⟩, rfl, rfl⟩, rfl, rfl⟩ := h
      rw [allocFrame_esp, allocFrame_esp, State.callEntry_esp, State.callEntry_esp, (hP _ P₁).1.2.2,
        (hP _ P₂).1.2.2]
    · obtain ⟨c₁, c₂, ⟨x₁, x₂, ⟨P₁, P₂⟩, rfl, rfl⟩, rfl, rfl⟩ := h
      obtain w : ∀ {x : State}, P x →
          WP isa (.block ((List.range 18).flatMap Impl.Ffdh.X86.copyArg))
            (allocFrame Impl.Ffdh.X86.argsFrame x.callEntry) (CalleeOf P base bytes len args sp) := fun {x} Px => by
        obtain ⟨R, F⟩ := hP x Px
        have e := R.2.2
        rw [← e] at F
        exact WP.mono (callee_atF R.1 F) fun u ⟨C, Fs⟩ => ⟨x, Px, by rw [← e]; exact C, by rw [← e]; exact Fs⟩
      exact ⟨w P₁, w P₂⟩
  · have cov : ∀ u, CalleeAt base bytes len args sp u →
        Covers ((u.rd ++ u.wr) ++ [⟨base, bytes⟩]) (u.rd ++ u.wr) ∧ Covers [⟨base, bytes⟩] u.wr := fun u C => by
      have c : Covers [⟨base, bytes⟩] u.wr :=
        Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact C.1.scratch.wr
      exact ⟨Covers.append_left (Covers.refl _) (Covers.right c), c⟩
    refine VG.Proof.Bignum.X86.PublicRt.relCT_narrow (fun u => u.rd ++ u.wr) (fun _ => [⟨base, bytes⟩])
      (fun f g ⟨⟨x₁, P₁, C₁, F₁⟩, ⟨x₂, P₂, C₂, F₂⟩⟩ => ?_) hb
    obtain ⟨p₁, w₁⟩ := hc x₁ f P₁ C₁ F₁
    obtain ⟨p₂, w₂⟩ := hc x₂ g P₂ C₂ F₂
    exact ⟨(cov f C₁).1, (cov f C₁).2, (cov g C₂).1, (cov g C₂).2, w₁, w₂, p₁, p₂⟩

/-- Before a windowed power: a prepared context, the room below `sp`, one in slot 3 and `R²` in slot 4. -/
abbrev WinPre (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32)
    (sp : BitVec 32) (s : State) : Prop :=
  (WSt Ex base bytes len args sp .wide [3, 4] 0 s ∧ RoomF sp base bytes) ∧ PrepFacts base len s

/-- The callee's context from a caller's before a windowed power: on the narrowed state, the context
`prepare_relCT` leaves, with one in slot 3 and `R²` in slot 4. -/
theorem winPre_callee {s u : State} (W : WinPre Ex base bytes len args sp s)
    (C : CalleeAt base bytes len args sp u) (Fs : Frame (frameF base sp []) s.mem u.mem) :
    ∃ M, CtxOk (fun _ _ => True) base bytes len args .wide M (u.withRegions (u.rd ++ u.wr) [⟨base, bytes⟩]) ∧
      WSt (fun _ _ => True) base bytes len args (sp - BitVec.ofNat 32 80) .wide [3, 4] 0 (u.withRegions (u.rd ++ u.wr) [⟨base, bytes⟩]) ∧
      sv u.mem base len .wide 3 = 1 ∧ sv u.mem base len .wide 4 = 2 ^ (16 * bc len .wide) % M ∧
      (∀ j, j ≤ 27 → sv u.mem base len .wide j = sv s.mem base len .wide j) := by
  obtain ⟨⟨⟨M, Cs, Hk, -, A, e⟩, RF⟩, one, r2⟩ := W
  rw [← e] at RF Fs
  have eq := fun j (hj : j ≤ 27) => frameF_sv Cs.inp RF Fs hj
  obtain Cn : CtxOk (fun _ _ => True) base bytes len args .wide M (u.withRegions (u.rd ++ u.wr) [⟨base, bytes⟩]) :=
    ctx_callee Cs RF (VG.Proof.Ffdh.X86.In.narrow C.1 trivial) Fs
  refine ⟨M, Cn, ⟨M, Cn, fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _),
    ⟨C.1.top, fun r hr => by rw [List.mem_singleton.mp hr]; exact C.2.2⟩, C.2.1⟩,
    by rw [eq 3 (by decide)]; exact one, by rw [eq 4 (by decide), r2, Cs.mod], eq⟩
  have hj' : j ≤ 27 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hj; omega_arith
  show sv u.mem _ _ _ _ < _
  rw [eq j hj']; exact Hk j hj

/-- `winCall`: its runs from a prepared context leak the same traces, and each reaches slot 6 below p. -/
theorem winCall_relCT :
    RelCT isa (Both (WinPre Ex base bytes len args sp)) Impl.Ffdh.X86.winCall
      (Both (WSt Ex base bytes len args sp .wide [6] 0)) := by
  refine relCT_both (argCall_trace (Pc := WSt (fun _ _ => True) base bytes len args (sp - BitVec.ofNat 32 80) .wide [3, 4] 0)
    (fun _ W => ⟨W.1.1.run, W.1.2⟩) (fun s u W C Fs => ?_)
    ((windowPower_relCT (winChecks .wide)).mono (fun _ _ h => h) fun _ _ _ => trivial)) fun x W => ?_
  · obtain ⟨M, Cn, Wn, one, r2, -⟩ := winPre_callee W C Fs
    exact ⟨Wn, _, windowPower_ok Cn one r2⟩
  · obtain ⟨⟨⟨M, C, -, -, A, e⟩, RF⟩, one, r2⟩ := W
    rw [← e] at RF
    refine WP.mono (winCall_ok C RF one (by rw [r2, C.mod])) fun u ⟨Cu, _, K, Y⟩ =>
      ⟨M, Cu, fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _), A.keep K, (K.1 _ (by decide)).trans e⟩
    rw [List.mem_singleton.mp hj, Y]; exact Nat.mod_lt _ (by have := C.gt; omega_arith)

theorem lenCount_check : ACheck (.block (lenCount 11)) := by dsimp only [ACheck]; taint_decide

/-- `winTopCall`, for synthetic argument 11 the public length `L`. -/
theorem winTopCall_relCT {L : Nat} (hx : args 11 = BitVec.ofNat 32 L) (hL0 : 0 < L) (hL : L ≤ len)
    (hL32 : L ≤ 1024) :
    RelCT isa (Both (WinPre Ex base bytes len args sp)) Impl.Ffdh.X86.winTopCall
      (Both (WSt Ex base bytes len args sp .wide [6] 0)) := by
  refine relCT_both (argCall_trace (Pc := WSt (fun _ _ => True) base bytes len args (sp - BitVec.ofNat 32 80) .wide [3, 4] 0)
    (fun _ W => ⟨W.1.1.run, W.1.2⟩) (fun s u W C Fs => ?_)
    ((windowPowerWith_relCT (winChecks .wide) (N := 2 * L) (by omega_arith) (by omega_arith)
      lenCount_check fun _ W => lenCount_wst (by decide) hx W).mono
      (fun _ _ h => h) fun _ _ _ => trivial)) fun x W => ?_
  · obtain ⟨M, Cn, Wn, one, r2, -⟩ := winPre_callee W C Fs
    obtain lb := len_le_bc len
    exact ⟨Wn, _, windowPowerWith_ok Cn one r2 (N := 2 * L) (by omega_arith) (by omega_arith) fun t Ct =>
      wp_movS (Ct.inp.arg (i := 11) (by decide)) fun t₁ a₁ _ => wp_addS rfl fun t₂ a₂ _ => WP.block_nil
        ⟨a₁.keeps.trans (a₂.keeps.mono (by decide)), by rw [a₂.mem, a₁.mem], by
          rw [a₂.gpr, a₁.gpr, hx, BitVec.ofNat_add_ofNat]; congr 1; omega_arith⟩⟩
  · obtain ⟨⟨⟨M, C, -, -, A, e⟩, RF⟩, one, r2⟩ := W
    rw [← e] at RF
    obtain lb := len_le_bc len
    refine WP.mono (winTopCall_ok C RF one (by rw [r2, C.mod]) hx hL0 (by omega_arith)) fun u ⟨Cu, _, K, Y⟩ =>
      ⟨M, Cu, fun j hj => ?_, fun _ h => absurd h (Nat.not_lt_zero _), A.keep K, (K.1 _ (by decide)).trans e⟩
    rw [List.mem_singleton.mp hj, Y]; exact Nat.mod_lt _ (by have := C.gt; omega_arith)

/-- A fact every run's start has, kept to their ends. -/
theorem relCT_keepA {P Q : State → Prop} {A : Prop} {c : Prog isa} (h : RelCT isa (Both P) c (Both Q))
    (hA : ∀ x, P x → A) : RelCT isa (Both P) c (Both fun u => Q u ∧ A) := fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ =>
  let ⟨ht, q₁, q₂⟩ := h s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  ⟨ht, ⟨q₁, hA _ hp.1⟩, ⟨q₂, hA _ hp.2⟩⟩

/-- A copy into slot 5 or 8, checked by the taint analysis, before a windowed power. -/
theorem copyWin_relCT {j d : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 17) (hd : d = 5 ∨ d = 8)
    (hc : ACheck (copy (.slot .wide j) (.slot .wide d) (one .wide))) :
    RelCT isa (Both (WinPre Ex base bytes len args sp)) (copy (.slot .wide j) (.slot .wide d) (one .wide))
      (Both (WinPre Ex base bytes len args sp)) := by
  refine taint_both (fun _ _ W₁ W₂ => W₁.1.1.agree W₂.1.1) _ hc fun x W => ?_
  obtain ⟨⟨Wx, RF⟩, one, r2⟩ := W
  have h := Wx.run.1
  refine WP.mono (WP.and (copyDown_wst hj9 hj (by omega_arith) (by omega_arith)
    (fun i hi => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; omega_arith) (by decide) Wx)
    (copyDown_ok h hj9 hj (by omega_arith))) fun u ⟨Wu, O, _, _⟩ => ⟨⟨Wu, RF⟩, ?_, ?_⟩
  · rw [slotKeep h (by decide) (by omega_arith) O]; exact one
  · rw [slotKeep h (by decide) (by omega_arith) O, slotKeep h (by decide) (by omega_arith) O]; exact r2

/-- A power modulo p: the base in slot `b`, the exponent in slot `e`. -/
theorem powP_trace {b e : Nat} (hb9 : 9 ≤ b) (hb : b ≤ 17) (he9 : 9 ≤ e) (he : e ≤ 17)
    (hcb : ACheck (copy (.slot .wide b) (.slot .wide 5) (one .wide)))
    (hce : ACheck (copy (.slot .wide e) (.slot .wide 8) (one .wide))) :
    RelCT isa (Both fun s => Run Ex base bytes len args sp s ∧ RoomF sp base bytes) (Impl.Ffdh.X86.powP b e)
      (Both (Run Ex base bytes len args sp)) := by
  unfold Impl.Ffdh.X86.powP
  refine VG.RelCT.seq (R := Both (WinPre Ex base bytes len args sp))
    ((relCT_keepA (A := RoomF sp base bytes) ctxP_relCTF fun _ h => h.2).mono (fun _ _ h => h)
      fun _ _ h => ⟨⟨⟨h.1.1.1, h.1.2⟩, h.1.1.2⟩, ⟨⟨h.2.1.1, h.2.2⟩, h.2.1.2⟩⟩) ?_
  refine VG.RelCT.seq (copyWin_relCT hb9 hb (.inl rfl) hcb) ?_
  refine VG.RelCT.seq (copyWin_relCT he9 he (.inr rfl) hce) ?_
  exact winCall_relCT.mono (fun _ _ h => h) fun _ _ h => ⟨h.1.run, h.2.run⟩

end VG.Proof.Ffdh.X86
