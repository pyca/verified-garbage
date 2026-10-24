module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.BranchCT
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Entry
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Loop
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Guards
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CTCode
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.BranchCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Entry
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Correct
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Loop
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Guards
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CTCode
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The key search's timing depends on its public descriptor and statuses (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_map)
open VG.Proof.Ffdh.PPC64LE.Generation (relCT_pushR0)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-! ## The loop -/

theorem key_iteration_ct (a : Attempt) :
    RelCT isa (Two KeyCTL) (iteration a.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_post (two_taint [.r31] key_ctl_pins (by taint_decide)) keys_ready) ?_
  exact RelCT.seq (two_post (key_branch_ct a) (key_branch_ready a))
    (two_taint [.r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_r31 h₁).trans (branch_r31 h₂).symm) (by taint_decide))

def KeyCTStep (q : KeyPoint) (s : State) : Prop :=
  if keyContinues q then isa.eval (.zero .d .r9) s = some true ∧ KeyCTL (nextKeyPoint q) s
  else isa.eval (.zero .d .r9) s = some false

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
      isa.eval (.zero .d .r9) s = isa.eval (.zero .d .r9) t ∧
      (isa.eval (.zero .d .r9) s = some false → True) ∧
      (isa.eval (.zero .d .r9) s = some true → ∃ m < n, LoopPair m s t) := by
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
    RelCT isa (Two KeyCTL) (.loop (iteration a.call) (.zero .d .r9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration a.call) (c := .zero .d .r9)
    (Q := fun _ _ => True) LoopPair (iteration_pair a) (128 * q.keys + q.scalars + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

/-! ## Entry and return -/

/-- A run's entry, with its public descriptor and its result's statuses. -/
def KeyStart (a : KeyPublic × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (keyResult s).statuses = a.2

private theorem entry_pointer (p : KeyPublic) (s : State) (h : KeyInput p s) :
    WP isa (.block (entry.take 2)) s fun t =>
      t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96 := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 32) 64 = p.control :=
    (arg_value s 4).trans (congrArg KeyPublic.control h.2)
  have ha4 := input_args h 4 (by decide)
  have hd' := hd
  have ha4' := ha4
  simp only [Nat.reduceMul] at ha4 ha4'
  rw [VG.Offset.add_add] at hd' ha4'
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  prun [ea, hd, ha4, hd', ha4', h.sp_eq]

private theorem pins_E2 : Pins (fun (p : KeyPublic) (t : State) =>
    t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96) [.r11, .r12] := by
  rintro p s t ⟨a12, a11⟩ ⟨b12, b11⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a12, b12]

private theorem entry_ct : RelCT isa (Two KeyInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two KeyInput) (.block (entry.take 2 ++ entry.drop 2)) _
  exact RelCT.block_append (RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide)) entry_pointer)
    (two_taint _ pins_E2 (by taint_decide)))

/-- After the entry: the controller's words written. -/
def KeyEntered (a : KeyPublic × List Nat) (t : State) : Prop :=
  ∃ s, KeyStart a s ∧ t.gpr .r31 = a.1.control ∧
    t.mem = writeController s.mem a.1.control (entryValues s) ∧ Keep entryRegs s t

private theorem entry_ready (a : KeyPublic × List Nat) (s : State) (h : KeyStart a s) :
    WP isa (.block entry) s (KeyEntered a) :=
  WP.mono (entry_ok h.1) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, h, hx, hm, k⟩

private def initialPoint (a : KeyPublic × List Nat) : KeyPoint := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩

private theorem entered_ctl {a : KeyPublic × List Nat} {t : State} (h : KeyEntered a t) :
    KeyCTL (initialPoint a) (framed .r0 t) := by
  rcases a with ⟨p, l⟩
  obtain ⟨s, ⟨hi, hst⟩, hx, hm, k⟩ := h
  refine ⟨s, key_start hi hx hm k, ?_⟩
  show (p.tail (keyRand s) 0 p.keys p.scalars).statuses = l
  change (keyResult s).statuses = l at hst
  change KeyInput p s at hi
  rw [← hst, hi.tail_eq]

/-- `mflr r0` keeps the state after the entry. -/
private theorem mflr_ready (a : KeyPublic × List Nat) (t : State) (h : KeyEntered a t) :
    WP isa (.block [.mflr .r0]) t (KeyEntered a) := by
  obtain ⟨s, hi, hx, hm, k⟩ := h
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.mem = t.mem) (by prun [exec_mflr]) (by decide))
    fun u ⟨hu, ku⟩ => ⟨s, hi, (ku.gpr _ (by decide)).trans hx, hu.trans hm, k.trans' (ku.mono (by decide))⟩

def KeyCTDone (p : KeyPublic) (s : State) : Prop := ∃ original r, KeyDone p original r s

private theorem frame_ct (a : Attempt) : RelCT isa (Two KeyEntered)
    (.frame (.push .r0) (.loop (iteration a.call) (.zero .d .r9)) (.pop .r0)) fun x y => x.sp = y.sp := by
  refine relCT_pushR0 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
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
    exact ⟨initialPoint q, entered_ctl h₁, entered_ctl h₂, by simp only [framed, hsp]⟩

private theorem search_ct (a : Attempt) : RelCT isa (Two KeyEntered) (search a.call) (fun _ _ => True) := by
  unfold search
  refine RelCT.seq (two_post (two_taint [] key_no_pins (by taint_decide)) mflr_ready)
    (RelCT.seq (frame_ct a) ?_)
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] key_no_pins (by taint_decide)).mono
    (fun _ _ hsp => ⟨(), trivial, trivial, hsp⟩) fun _ _ h => h

private theorem search_ready (a : Attempt) (q : KeyPublic × List Nat) (t : State) (h : KeyEntered q t) :
    WP isa (search a.call) t (KeyCTDone q.1) := by
  obtain ⟨s, ⟨hi, _⟩, hx, hm, k⟩ := h
  exact WP.mono (key_body a hi hx hm k) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointer (p : KeyPublic) (s : State) (h : KeyCTDone p s) :
    WP isa (.block (finish.take 3)) s fun t => t.gpr .r4 = p.up ∧ t.gpr .r31 = p.control := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  simp only [Bignum.word, off] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  prun [ldf, h.r31, hu, hl 120 (by decide), hl 88 (by decide), hl 112 (by decide)]

private theorem finish_ct : RelCT isa (Two KeyCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two KeyCTDone) (.block (finish.take 3 ++ finish.drop 3)) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.r31] ?_ (by taint_decide)) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r31.trans h₂.r31.symm
  · exact two_taint [.r4, .r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

theorem key_code_ct (a : Attempt) :
    RelCT isa (Two KeyStart) (code a.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post (two_map Prod.fst (fun _ _ h => h.1) entry_ct) entry_ready)
    (RelCT.seq (two_post (search_ct a) (search_ready a))
      (two_map Prod.fst (fun _ _ h => h) finish_ct))

private theorem key_public_descriptor {s t : State} (h : keyPub s t) : keyOfState s = keyOfState t := by
  obtain ⟨hsp, hr, ha, hdom, hw, -⟩ := h
  simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hr
  obtain ⟨r3, -, r5, -, r7, r8, r9, r10⟩ := hr
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
  rw [keyRetries, keyRetries, h0, h1, hdom, hsp, r3, r5, r7, r8, keyLen, keyLen, r9, r10,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)]

theorem key_constantTime (a : Attempt) :
    ConstantTime isa keyContract.pre keyContract.pub (code a.call) := by
  refine RelCT.constantTime ((key_code_ct a).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(keyOfState s, (keyResult s).statuses), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨⟨ht, (key_public_descriptor hp).symm⟩, hp.2.2.2.2.2.symm⟩, hp.1⟩

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
