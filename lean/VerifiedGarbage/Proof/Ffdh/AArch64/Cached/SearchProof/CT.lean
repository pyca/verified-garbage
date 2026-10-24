module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.BranchCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Start
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Correct
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Loop
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Guards
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.BranchCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Start
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Correct
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Loop
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Guards
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The key search's timing depends on its public descriptor and statuses (AArch64) -/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-! ## The loop -/

theorem key_iteration_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (iteration a.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.x19] key_ctl_pins (by taint_decide) keys_ready) ?_
  exact RelCT.seq (two_post (key_branch_ct a) (key_branch_ready a))
    (two_taint [.x19] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_x19 h₁).trans (branch_x19 h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then isa.eval (.zero .x .x9) s = some true ∧ KeyCTL (nextKeyPoint q) s
  else isa.eval (.zero .x .x9) s = some false

theorem key_ct_step (a : Attempt) (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (iteration a.call) s (KeyCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (keys_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (key_branch_ready a q u hu) fun t ht => ?_)
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl, hst⟩, hw⟩ := ht
    rw [← nextKeyPoint_inputs q] at hw
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [KeyCTStep, hc, ite_true]
    exact ⟨hz, original, hzl, hst⟩
  · simp only [KeyBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [KeyCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s ∧ KeyCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (a : Attempt) (n : Nat) :
    RelCT isa (LoopPair n) (iteration a.call) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧
      (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : KeyPoint) (s : State) (h : n = 128 * q.keys + q.scalars + 1 ∧ KeyCTL q s) :
      WP isa (iteration a.call) s fun t => n = 128 * q.keys + q.scalars + 1 ∧ KeyCTStep q t :=
    WP.mono (key_ct_step a q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((key_iteration_ct a).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : keyContinues q
  · simp only [KeyCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars + 1, ?_, nextKeyPoint q, rfl,
      h₁.2, h₂.2, hsp⟩
    have := nextKeyPoint_measure hb
    omega
  · simp only [KeyCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem key_loop_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (.loop (iteration a.call) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration a.call) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair a) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## The frame saving `x30` -/

/-- A frame saving `x30` around a body proven with the permissions outside
it (as `WP.frameReg` runs it) leaks what the body does there: the body's
run in the frame is that run, with more permissions (`Exec.widen`). -/
theorem relCT_pushX30 {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hwp : ∀ a b, P a b → (∃ t s', Exec isa body (pushedX30 a) t s') ∧
      (∃ t s', Exec isa body (pushedX30 b) t s'))
    (hct : RelCT isa (fun x y => ∃ a b, P a b ∧ x = pushedX30 a ∧ y = pushedX30 b) body
      fun _ _ => True) :
    RelCT isa P (.frame (.push .x30) body (.pop .x30)) fun _ _ => True := by
  refine RelCT.pushFrame (R := fun _ _ => True) hsp ?_
  have widen : ∀ a, ∀ {t s'}, Exec isa body (pushedX30 a) t s' →
      Exec isa body (pushed .x30 a) t (s'.withRegions a.rd (⟨a.sp - 16, 16⟩ :: a.wr)) := by
    intro a t s' e
    have := Exec.widen e (rd := a.rd) (wr := ⟨a.sp - 16, 16⟩ :: a.wr)
      (Covers.of_mem fun r hr => by
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ hr
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr))
      (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)
    exact this
  rintro x y tx ty x' y' ⟨a, b, hab, rfl, rfl⟩ ex ey
  obtain ⟨⟨ta, sa, ea⟩, ⟨tb, sb, eb⟩⟩ := hwp a b hab
  obtain ⟨rfl, -⟩ := Exec.det ex (widen a ea)
  obtain ⟨rfl, -⟩ := Exec.det ey (widen b eb)
  exact ⟨(hct _ _ _ _ _ _ ⟨a, b, hab, rfl, rfl⟩ ea eb).1, trivial⟩

/-! ## Entry and return -/

/-- A run's entry, with its public descriptor and its result's statuses. -/
def KeyStart (a : KeyPublic × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (keyResult s).statuses = a.2

private theorem entry_pointer (p : KeyPublic) (s : State) (h : KeyInput p s) :
    WP isa (.block (entry.take 6)) s fun t => t.gpr .x8 = p.control := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 32) 64 = p.control :=
    congrArg KeyPublic.control h.2
  have ha4 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 32) 8 := input_args h 4 (by decide)
  have ha0 : InRegions (s.rd ++ s.wr) s.sp 8 := by
    simpa only [Nat.mul_zero, BitVec.add_zero] using input_args h 0 (by decide)
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 := input_args h 1 (by decide)
  have ha2 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 16) 8 := input_args h 2 (by decide)
  have ha3 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 24) 8 := input_args h 3 (by decide)
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  brun [exec_addSp (show 0 < 4096 by decide), hd, ha0, ha1, ha2, ha3, ha4]

private theorem entry_ct : RelCT isa (Two KeyInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two KeyInput) (.block (entry.take 6 ++ entry.drop 6)) _
  refine RelCT.block_append (RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => by cases h)
    (by taint_decide) entry_pointer) ?_)
  exact two_taint [.x8] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.trans h₂.symm) (by taint_decide)

/-- After the entry: the controller's words written. -/
def KeyEntered (a : KeyPublic × List Nat) (t : State) : Prop :=
  ∃ s, KeyStart a s ∧ t.gpr .x19 = a.1.control ∧
    t.mem = writeController s.mem a.1.control (entryValues s) ∧
    Keep [.x8, .x9, .x10, .x11, .x12, .x13, .x14, .x19] s t

private theorem entry_ready (a : KeyPublic × List Nat) (s : State) (h : KeyStart a s) :
    WP isa (.block entry) s (KeyEntered a) :=
  WP.mono (entry_ok h.1) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, h, hx, hm, k⟩

private def initialPoint (a : KeyPublic × List Nat) : KeyPoint := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩

private theorem entered_ctl {a : KeyPublic × List Nat} {t : State} (h : KeyEntered a t) :
    KeyCTL (initialPoint a) (pushedX30 t) := by
  rcases a with ⟨p, l⟩
  obtain ⟨s, ⟨hi, hst⟩, hx, hm, k⟩ := h
  refine ⟨s, key_start hi hx hm k, ?_⟩
  show (p.tail (keyRand s) 0 p.keys p.scalars).statuses = l
  change (keyResult s).statuses = l at hst
  change KeyInput p s at hi
  rw [← hst]
  cases hi.2
  simp only [keyResult, KeyPublic.tail, Proof.Ffdh.GenerationSearch.keyTail,
    Proof.Ffdh.GenerationSearch.after,VG.Proof.Ffdh.GenerationPolicy.search, keyOfState, KeyPublic.a, List.drop_zero]

def KeyCTDone (p : KeyPublic) (s : State) : Prop := ∃ original r, KeyDone p original r s

private theorem search_ct (a : Attempt) : RelCT isa (Two KeyEntered) (search a.call) (fun _ _ => True) := by
  unfold search
  refine relCT_pushX30 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨original, hl, -⟩ := entered_ctl h₁
    obtain ⟨original', hl', -⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original) 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl, rfl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := key_loop a (n := 128 * q.1.keys + q.1.scalars + 1)
      (expected := (initialPoint q).inputs.tail (keyRand original') 0 q.1.keys q.1.scalars)
      ⟨0, _, _, rfl, hl', rfl, rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (key_loop_ct a).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨initialPoint q, entered_ctl h₁, entered_ctl h₂, by simp only [hsp]⟩

private theorem search_ready (a : Attempt) (q : KeyPublic × List Nat) (t : State) (h : KeyEntered q t) :
    WP isa (search a.call) t (KeyCTDone q.1) := by
  obtain ⟨s, ⟨hi, _⟩, hx, hm, k⟩ := h
  exact WP.mono (key_search a hi hx hm k) fun _ ⟨r, _, _, hd, _⟩ => ⟨s, r, hd⟩

private theorem finish_pointer (p : KeyPublic) (s : State) (h : KeyCTDone p s) :
    WP isa (.block (finish.take 4)) s fun t => t.gpr .x1 = p.up := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  simp only [Bignum.word, off] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.x19, hu, hl 120 (by decide), hl 88 (by decide), hl 112 (by decide), hl 32 (by decide)]

private theorem finish_ct : RelCT isa (Two KeyCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two KeyCTDone) (.block (finish.take 4 ++ finish.drop 4)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.x19] ?_ (by taint_decide) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.x19.trans h₂.x19.symm
  · exact two_taint [.x1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

theorem key_code_ct (a : Attempt) :
    RelCT isa (Two KeyStart) (code a.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post (two_map Prod.fst (fun _ _ h => h.1) entry_ct) entry_ready)
    (RelCT.seq (two_post (search_ct a) (search_ready a))
      (two_map Prod.fst (fun _ _ h => h) finish_ct))

private theorem key_public_descriptor {s t : State} (h : keyPub s t) : keyOfState s = keyOfState t := by
  obtain ⟨hsp, hr, ha, hdom, hw, -⟩ := h
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r0, -, r2, -, r4, r5, r6, r7⟩ := hr
  change [word s.mem (stackArg s 4) 0, word s.mem (stackArg s 4) 8, word s.mem (stackArg s 4) 16,
    word s.mem (stackArg s 4) 24] = [word t.mem (stackArg t 4) 0, word t.mem (stackArg t 4) 8,
      word t.mem (stackArg t 4) 16, word t.mem (stackArg t 4) 24] at hw
  have h0 : s.mem.readW (stackArg s 4) 64 = t.mem.readW (stackArg t 4) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have h1 : s.mem.readW (stackArg s 4 + 8) 64 = t.mem.readW (stackArg t 4 + 8) 64 := by
    have := (List.cons.inj (List.cons.inj hw).2).1
    simp only [Bignum.word, off] at this
    exact this
  unfold keyOfState
  rw [keyRetries, keyRetries, h0, h1, hdom, hsp, r0, r2, r4, r5, r6, keyLen, keyLen, r7, ha 0 (by decide),
    ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide),ha 5 (by decide),ha 6 (by decide)]

theorem key_constantTime (a : Attempt) :
    ConstantTime isa keyContract.pre keyContract.pub (code a.call) := by
  refine RelCT.constantTime ((key_code_ct a).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(keyOfState s, (keyResult s).statuses), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨⟨ht, (key_public_descriptor hp).symm⟩, hp.2.2.2.2.2.symm⟩, hp.1⟩

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
