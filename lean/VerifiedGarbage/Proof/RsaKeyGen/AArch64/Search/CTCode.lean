module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.CT
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Correct
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.CT
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Correct
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # The RSA prime search's timing (AArch64)

Two runs whose public arguments, state words and result's trace agree start
at the same point of the search (`search_constantTime`): the entry loads
the state's pointer from a public stack argument, and the return stores
through the pointers in the frame's public words.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.RsaKeyGen.AArch64.Search

/-! ## The frame saving `x30` -/

/-- A frame saving `x30` around a body proven with the permissions outside
it (as `WP.frameReg` runs it) leaks what the body does there: the body's
run in the frame is that run, with more permissions (`Exec.widen`). As
`Proof/Ffdh/AArch64/Generation/Search/CTCode.lean`'s. -/
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

/-! ## The entry -/

/-- The search's inputs, with the trace of its result. -/
def STInput (d : SPub × List Nat) (s : State) : Prop := SInput d.1 s ∧ (searchResult s).trace = d.2

/-- In the search's frame. -/
def SAlloc (d : SPub × List Nat) (u : State) : Prop := ∃ s, STInput d s ∧ u = allocated frameBytes s

private theorem entry_pointer (d : SPub × List Nat) (u : State) (h : SAlloc d u) :
    WP isa (.block (entry.take 5)) u fun t => t.gpr .x12 = d.1.stp := by
  obtain ⟨s, ⟨hi, -⟩, rfl⟩ := h
  have ha3 : InRegions ((allocated frameBytes s).rd ++ (allocated frameBytes s).wr)
      (s.sp + BitVec.ofNat 64 (8 * 3)) 8 := by
    obtain ⟨r, hr, hc⟩ := input_args hi 3 (by decide)
    refine ⟨r, ?_, hc⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact List.mem_append_left _ hr
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  have hsp : s.sp - BitVec.ofNat 64 160 + BitVec.ofNat 64 160 = s.sp := BitVec.sub_add_cancel _ _
  have hd : d.1.stp = stackArg s 3 := by rw [← hi.2]; rfl
  rw [hd]
  unfold entry entryHead
  simp only [List.cons_append, List.take_succ_cons, List.take_zero, frameBytes, allocated] at ha3 ⊢
  simp only [Nat.reduceMul] at ha3
  have hrd : ∀ d', d' + 8 ≤ 32 → InRegions (s.rd ++ ⟨s.sp - BitVec.ofNat 64 160, 160⟩ :: s.wr)
      (s.sp + BitVec.ofNat 64 d') 8 := fun d' hd' => by
    obtain ⟨r, hr, hc⟩ := input_args hi 0 (by decide)
    refine ⟨inArgs s, ?_, ?_⟩
    · rw [hi.1.2.2.1]; exact List.mem_append_left _ (by simp [inReads])
    · simp only [inArgs, stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact Offset.contains_base _ hd' (by omega)
  have hrd0 : InRegions (s.rd ++ ⟨s.sp - BitVec.ofNat 64 160, 160⟩ :: s.wr) s.sp 8 := by
    simpa only [BitVec.add_zero] using hrd 0 (by decide)
  brun [exec_addSp (show 160 < 4096 by decide), hsp, hrd0, hrd 8 (by decide), hrd 16 (by decide),
    hrd 24 (by decide)]
  simp only [stackArg, stackArgAddr, Nat.reduceMul]

private theorem entry_ct : RelCT isa (Two SAlloc) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two SAlloc) (.block (entry.take 5 ++ entry.drop 5)) _
  refine RelCT.block_append (RelCT.seq (two_piece [] no_pins (by taint_decide) entry_pointer) ?_)
  exact two_taint [.x12] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.trans h₂.symm) (by taint_decide)

/-- After the entry: the frame's words written. -/
def SEntered (d : SPub × List Nat) (t : State) : Prop :=
  ∃ s, STInput d s ∧ t.gpr .x19 = d.1.F ∧
    t.mem = writeController s.mem d.1.F (entryValues s) ∧ Keep entryRegs (allocated frameBytes s) t

private theorem entry_ready (d : SPub × List Nat) (u : State) (h : SAlloc d u) :
    WP isa (.block entry) u (SEntered d) := by
  obtain ⟨s, hi, rfl⟩ := h
  exact WP.mono (entry_ok hi.1) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, hi, hx, hm, k⟩

private theorem entered_ctl {d : SPub × List Nat} {t : State} (h : SEntered d t) :
    SCTL ⟨d.1, 0, d.1.remaining, d.2⟩ (pushedX30 t) := by
  obtain ⟨s, ⟨hi, htr⟩, hx, hm, k⟩ := h
  refine ⟨s, search_start hi hx hm k, ?_⟩
  rw [← htr, hi.result_eq, consume_zero]

def SCTDone (p : SPub) (s : State) : Prop := ∃ original r, SDone p original r s

private theorem search_ct (c : Cand) : RelCT isa (Two SEntered) (search c.call) (fun _ _ => True) := by
  unfold search
  refine relCT_pushX30 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨d, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨original, hl, -⟩ := entered_ctl h₁
    obtain ⟨original', hl', -⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := search_loop c (n := d.1.randLen - 0 + 1)
      (final := (tailOf d.1 original 0 d.1.remaining).consume 0 []) ⟨0, _, rfl, hl, [], rfl⟩
    obtain ⟨t', s'', e', -⟩ := search_loop c (n := d.1.randLen - 0 + 1)
      (final := (tailOf d.1 original' 0 d.1.remaining).consume 0 []) ⟨0, _, rfl, hl', [], rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (s_loop_ct c).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨d, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨⟨d.1, 0, d.1.remaining, d.2⟩, entered_ctl h₁, entered_ctl h₂, by simp only [hsp]⟩

private theorem search_ready (c : Cand) (d : SPub × List Nat) (t : State) (h : SEntered d t) :
    WP isa (search c.call) t (SCTDone d.1) := by
  obtain ⟨s, ⟨hi, -⟩, hx, hm, k⟩ := h
  exact WP.mono (search_body c hi hx hm k) fun _ ⟨hd, _⟩ => ⟨s, _, hd⟩

/-! ## The return -/

/-- After the pointers are loaded. -/
def SFinishing (p : SPub) (t : State) : Prop :=
  t.gpr .x19 = p.F ∧ t.gpr .x12 = p.stp ∧ t.gpr .x1 = p.up

private theorem finish_pointers (p : SPub) (s : State) (h : SCTDone p s) :
    WP isa (.block (finish.take 6)) s (SFinishing p) := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.frame_scr h.wr
  have hl : ∀ d, d + 8 ≤ 160 → InRegions (s.rd ++ s.wr) (p.F + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  have hs := h.stp
  simp only [Bignum.word, off, Nat.reduceMul] at hu hs
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  brun [ldf, h.x19, hu, hs, hl 0 (by decide), hl 8 (by decide), hl 16 (by decide), hl 24 (by decide),
    hl 56 (by decide), hl 144 (by decide)]
  exact ⟨by simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; exact h.x19,
    by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq],
    by simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]⟩

private theorem finish_ct : RelCT isa (Two SCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two SCTDone) (.block (finish.take 6 ++ finish.drop 6)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.x19] ?_ (by taint_decide) finish_pointers) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.x19.trans h₂.x19.symm
  · exact two_taint [.x19, .x12, .x1] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

theorem search_code_ct (c : Cand) : RelCT isa (Two STInput) (code c.call) (fun _ _ => True) := by
  unfold code
  apply RelCT.alloc
  refine (RelCT.seq (two_post entry_ct entry_ready)
    (RelCT.seq (two_post (search_ct c) (search_ready c)) (two_map Prod.fst (fun _ _ h => h) finish_ct))).mono ?_ fun _ _ h => h
  rintro _ _ ⟨s, t, ⟨d, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨d, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

private theorem s_public_descriptor {s t : State} (h : searchPub s t) : sOfState s = sOfState t := by
  obtain ⟨hsp, r0, r1, r2, r3, r4, r5, r6, r7, ha, he, hw, -⟩ := h
  have h0 : s.mem.readW (stackArg s 3) 64 = t.mem.readW (stackArg t 3) 64 := by
    change [word s.mem (stackArg s 3) 0, word s.mem (stackArg s 3) 8, word s.mem (stackArg s 3) 16,
      word s.mem (stackArg s 3) 24] = [word t.mem (stackArg t 3) 0, word t.mem (stackArg t 3) 8,
        word t.mem (stackArg t 3) 16, word t.mem (stackArg t 3) 24] at hw
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  unfold sOfState
  rw [searchRemaining, searchRemaining, h0, he, hsp, r0, r2, r3, r5, r7, searchLen, searchLen, r1, r4, r6,
    ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide)]

theorem search_constantTime (c : Cand) :
    ConstantTime isa searchContract.pre searchContract.pub (code c.call) := by
  refine RelCT.constantTime ((search_code_ct c).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(sOfState s, (searchResult s).trace), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨⟨ht, (s_public_descriptor hp).symm⟩, hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm⟩, hp.1⟩

end VG.Proof.RsaKeyGen.AArch64.Search
