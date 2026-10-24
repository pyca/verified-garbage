module
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Entry
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT

import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Entry
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.CT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Correct
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith

/-! # The parameter search is constant time for its public data (PPC64LE) -/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-! ## The frame saving `r0` -/

/-- A frame saving `r0` around a body proven with the permissions outside
it (as `WP.frameRegAny` runs it) leaks what the body does there: the body's
run in the frame is that run, with more permissions (`Exec.widen`). -/
theorem relCT_pushR0 {body : Prog isa} {P : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hwp : ∀ a b, P a b → (∃ t s', Exec isa body (framed .r0 a) t s') ∧
      (∃ t s', Exec isa body (framed .r0 b) t s'))
    (hct : RelCT isa (fun x y => ∃ a b, P a b ∧ x = framed .r0 a ∧ y = framed .r0 b) body
      fun _ _ => True) :
    RelCT isa P (.frame (.push .r0) body (.pop .r0)) fun a b => a.sp = b.sp := by
  refine RelCT.frame (R := fun _ _ => True) hsp ?_
  have widen : ∀ a, ∀ {t s'}, Exec isa body (framed .r0 a) t s' →
      Exec isa body (pushed .r0 a) t (s'.withRegions a.rd (⟨a.sp - 48 + 32, 16⟩ :: a.wr)) := by
    intro a t s' e
    have := Exec.widen e (rd := a.rd) (wr := ⟨a.sp - 48 + 32, 16⟩ :: a.wr)
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

private theorem entry_pointer (p : SPub) (s : State) (h : SInput p s) :
    WP isa (.block (entry.take 2)) s fun t =>
      t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96 := by
  have hd : s.mem.readW (s.sp + BitVec.ofNat 64 104) 64 = p.control := by
    rw [← congrArg SPub.control h.2]
    simp only [sOfState, stackArg, stackArgAddr, Nat.reduceMul, Nat.reduceAdd]
  have ha1 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 104) 8 := by
    rw [← VG.Offset.add_add_eq s.sp (show 96 + 8 = 104 by rfl)]; exact input_args h 1 (by decide)
  have ea : exec (.addSp .r11 96) s = some (s.write .r11 (s.sp + BitVec.ofNat 64 96)) := by
    simp [exec]
  unfold entry
  simp only [List.take_succ_cons, List.take_zero]
  prun [ea, hd, ha1, h.sp_eq]

theorem pins_E2 : Pins (fun (p : SPub) (t : State) => t.gpr .r12 = p.control ∧ t.gpr .r11 = p.sp + BitVec.ofNat 64 96)
    [.r11, .r12] := by
  rintro p s t ⟨a12, a11⟩ ⟨b12, b11⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [a11, b11]
  · rw [a12, b12]

private theorem entry_ct : RelCT isa (Two SInput) (.block entry) (fun _ _ => True) := by
  change RelCT isa (Two SInput) (.block (entry.take 2 ++ entry.drop 2)) _
  exact RelCT.block_append (RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) entry_pointer)
    (two_taint _ pins_E2 (by taint_decide)))

/-- After the entry: the controller's words written. -/
def SEntered (p : SPub) (t : State) : Prop :=
  ∃ s, SInput p s ∧ t.gpr .r31 = p.control ∧
    t.mem = writeController s.mem p.control (entryValues s) ∧ Keep entryRegs s t

private theorem entry_ready (p : SPub) (s : State) (h : SInput p s) :
    WP isa (.block entry) s (SEntered p) :=
  WP.mono (entry_ok h) fun _ ⟨⟨hx, hm⟩, k⟩ => ⟨s, h, hx, hm, k⟩

private theorem entered_ctl {p : SPub} {t : State} (h : SEntered p t) :
    SCTL ⟨p, 0, p.attempts⟩ (framed .r0 t) := by
  obtain ⟨s, hi, hx, hm, k⟩ := h
  exact ⟨s, search_start hi hx hm k⟩

/-- `mflr r0` keeps the state after the entry. -/
private theorem mflr_ready (p : SPub) (t : State) (h : SEntered p t) :
    WP isa (.block [.mflr .r0]) t (SEntered p) := by
  obtain ⟨s, hi, hx, hm, k⟩ := h
  refine WP.mono (WP.keep [.r0] (Q := fun u => u.mem = t.mem) (by prun [exec_mflr]) (by decide))
    fun u ⟨hu, ku⟩ => ⟨s, hi, (ku.gpr _ (by decide)).trans hx, hu.trans hm, k.trans' (ku.mono (by decide))⟩

def SCTDone (p : SPub) (s : State) : Prop := ∃ original r, SDone p original r s

private theorem frame_ct (c : Cand) : RelCT isa (Two SEntered)
    (.frame (.push .r0) (.loop (iteration c.call) (.zero .d .r9)) (.pop .r0)) fun a b => a.sp = b.sp := by
  refine relCT_pushR0 (fun _ _ ⟨_, _, _, hsp⟩ => hsp) (fun x y ⟨q, h₁, h₂, _⟩ => ?_) ?_
  · obtain ⟨original, hl⟩ := entered_ctl h₁
    obtain ⟨original', hl'⟩ := entered_ctl h₂
    obtain ⟨t, s', e, -⟩ := search_loop c (n := q.attempts + 1) (expected := q.tail 0 q.attempts)
      ⟨0, _, rfl, hl, rfl⟩
    obtain ⟨t', s'', e', -⟩ := search_loop c (n := q.attempts + 1) (expected := q.tail 0 q.attempts)
      ⟨0, _, rfl, hl', rfl⟩
    exact ⟨⟨t, s', e⟩, ⟨t', s'', e'⟩⟩
  · refine (s_loop_ct c).mono ?_ fun _ _ h => h
    rintro _ _ ⟨x, y, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
    exact ⟨⟨q, 0, q.attempts⟩, entered_ctl h₁, entered_ctl h₂, by simp only [framed, hsp]⟩

private theorem search_ct (c : Cand) : RelCT isa (Two SEntered) (search c.call) (fun _ _ => True) := by
  unfold search
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) mflr_ready) (RelCT.seq (frame_ct c) ?_)
  exact (two_taint (Φ := fun (_ : Unit) (_ : State) => True) [] no_pins (by taint_decide)).mono
    (fun _ _ hsp => ⟨(), trivial, trivial, hsp⟩) fun _ _ h => h

private theorem search_ready (c : Cand) (p : SPub) (t : State) (h : SEntered p t) :
    WP isa (search c.call) t (SCTDone p) := by
  obtain ⟨s, hi, hx, hm, k⟩ := h
  exact WP.mono (search_body c hi hx hm k) fun _ ⟨hd, _, _⟩ => ⟨s, _, hd⟩

private theorem finish_pointer (p : SPub) (s : State) (h : SCTDone p s) :
    WP isa (.block (finish.take 3)) s fun t => t.gpr .r4 = p.up ∧ t.gpr .r31 = p.control := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  have hu := h.usedPtr
  simp only [Bignum.word, off] at hu
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  prun [ldf, h.r31, hu, hl 56 (by decide), hl 96 (by decide), hl 112 (by decide)]

private theorem finish_ct : RelCT isa (Two SCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two SCTDone) (.block (finish.take 3 ++ finish.drop 3)) _
  refine RelCT.block_append (RelCT.seq (two_post (two_taint [.r31] ?_ (by taint_decide)) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r31.trans h₂.r31.symm
  · exact two_taint [.r4, .r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

theorem search_code_ct (c : Cand) : RelCT isa (Two SInput) (code c.call) (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (two_post entry_ct entry_ready)
    (RelCT.seq (two_post (search_ct c) (search_ready c)) finish_ct)

private theorem s_public_descriptor {s t : State} (h : searchPub s t) : sOfState s = sOfState t := by
  obtain ⟨hsp, hr, hw, r3, r4, r5, r6, r7, r8, r9, r10, a0, a1⟩ := h
  have h0 : s.mem.readW (stackArg s 1) 64 = t.mem.readW (stackArg t 1) 64 := by
    change [word s.mem (stackArg s 1) 0, word s.mem (stackArg s 1) 8, word s.mem (stackArg s 1) 16,
      word s.mem (stackArg s 1) 24] = [word t.mem (stackArg t 1) 0, word t.mem (stackArg t 1) 8,
        word t.mem (stackArg t 1) 16, word t.mem (stackArg t 1) 24] at hw
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have hrand : genRand s = genRand t := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hr
  unfold sOfState
  rw [genAttempts, genAttempts, h0, hrand, hsp, r3, r5, r8, r10, genLen, genLen, r4, genBits, genBits, r6,
    genGen, genGen, r7, r9, a0, a1]

theorem search_constantTime (c : Cand) :
    ConstantTime isa searchContract.pre searchContract.pub (code c.call) := by
  refine RelCT.constantTime ((search_code_ct c).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨sOfState s, ⟨hs, rfl⟩, ⟨ht, (s_public_descriptor hp).symm⟩, hp.1⟩

end VG.Proof.Ffdh.PPC64LE.Generation
