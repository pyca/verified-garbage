module
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data

import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.LoopCT
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Correct
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Loop
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Start
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Data
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.LoopCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Correct
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Loop
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Start
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # The key search's timing depends on its public descriptor and statuses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-! ## Entry and return -/

private theorem entry_pointer (p : KeyPublic) (s : State) (h : KeyInput p s) :
    WP isa (.block (entryHead.take 1)) s fun t => t.gpr .rax = p.control := by
  have hd : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 56) 64 = p.control :=
    congrArg KeyPublic.control h.2
  have ha : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 56) 8 := input_args h 6 (by decide)
  unfold entryHead
  simp only [List.take_succ_cons, List.take_zero]
  xrun [State.ea, BitVec.ofInt_ofNat, hd, ha]

private theorem entry_head_ct : RelCT isa (Two KeyInput) (.block entryHead) (fun _ _ => True) := by
  change RelCT isa (Two KeyInput) (.block (entryHead.take 1 ++ entryHead.drop 1)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.rsp] ?_ (by taint_decide) entry_pointer) ?_)
  · intro p s t h₁ h₂ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (congrArg KeyPublic.sp h₁.2).trans (congrArg KeyPublic.sp h₂.2).symm
  · exact two_taint [.rax] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

def KeyEntryPins (p : KeyPublic) (s : State) : Prop := s.gpr .r12 = p.control ∧ s.gpr .rsp = p.sp

private theorem entry_head_pins (p : KeyPublic) (s : State) (h : KeyInput p s) :
    WP isa (.block entryHead) s (KeyEntryPins p) := by
  refine WP.mono (entry_head_ok h) fun t ⟨hr, _, k⟩ => ⟨hr, ?_⟩
  exact (k.gpr (by decide)).trans (congrArg KeyPublic.sp h.2)

theorem key_entry_ct : RelCT isa (Two KeyInput) (.block entry) (fun _ _ => True) := by
  unfold entry
  refine RelCT.block_append (RelCT.seq (two_post entry_head_ct entry_head_pins) ?_)
  exact two_taint [.r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

def KeyCTDone (p : KeyPublic) (s : State) : Prop := ∃ original r, KeyDone p original r s

private theorem finish_pointer (p : KeyPublic) (s : State) (h : KeyCTDone p s) :
    WP isa (.block (finish.take 4)) s fun t => t.gpr .rdx = p.up := by
  obtain ⟨original, r, h⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  xrun [State.ea, field, off, h.r12, h.usedPtr, Nat.reduceMul, BitVec.ofInt_natCast,
    hl 120 (by decide), hl 88 (by decide), hl 112 (by decide), hl 32 (by decide)]

theorem key_finish_ct : RelCT isa (Two KeyCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two KeyCTDone) (.block (finish.take 4 ++ finish.drop 4)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.r12] ?_ (by taint_decide) finish_pointer) ?_)
  · intro p s t ⟨_, _, h₁⟩ ⟨_, _, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r12.trans h₂.r12.symm
  · exact two_taint [.rdx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

/-! ## The whole search -/

/-- A run's entry, with its public descriptor and its result's statuses. -/
def KeyStart (a : KeyPublic × List Nat) (s : State) : Prop :=
  KeyInput a.1 s ∧ (keyResult s).statuses = a.2

private def initialPoint (a : KeyPublic × List Nat) : KeyPoint := ⟨a.1, 0, a.1.keys, a.1.scalars, a.2⟩

private theorem entry_started (a : KeyPublic × List Nat) (s : State) (h : KeyStart a s) :
    WP isa (.block entry) s (KeyCTL (initialPoint a)) :=
  WP.mono (key_start h.1) fun _ ht => ⟨s, ht, by
    show (a.1.tail (keyRand s) 0 a.1.keys a.1.scalars).statuses = a.2
    rw [← initial_key_result h.1]; exact h.2⟩

private theorem loop_done (v : RoundImpl) (a : KeyPublic × List Nat) (s : State)
    (h : KeyCTL (initialPoint a) s) :
    WP isa (.loop (iteration (attemptCall v)) .e) s (KeyCTDone a.1) := by
  obtain ⟨original, hl, _⟩ := h
  exact WP.mono (key_loop v (expected := a.1.tail (keyRand original) 0 a.1.keys a.1.scalars)
    ⟨0, _, _, rfl, hl, rfl, rfl⟩) fun _ ht => ⟨original, _, ht⟩

theorem key_code_ct (v : RoundImpl) :
    RelCT isa (Two KeyStart) (code (attemptCall v)) (fun _ _ => True) := by
  unfold code
  change RelCT isa _ (.seq _ (.seq _ _)) _
  exact RelCT.seq (two_post (two_map Prod.fst (fun _ _ h => h.1) key_entry_ct) entry_started)
    (RelCT.seq (two_post (two_map initialPoint (fun _ _ h => h) (key_loop_ct v)) (loop_done v))
      (two_map Prod.fst (fun _ _ h => h) key_finish_ct))

private theorem key_public_descriptor {s t : State} (h : keyPub s t) : keyOfState s = keyOfState t := by
  obtain ⟨hsp, r0, -, r2, -, r4, r5, ha, hdom, hw, -⟩ := h
  change [word s.mem (stackArg s 6) 0, word s.mem (stackArg s 6) 8, word s.mem (stackArg s 6) 16,
    word s.mem (stackArg s 6) 24] = [word t.mem (stackArg t 6) 0, word t.mem (stackArg t 6) 8,
      word t.mem (stackArg t 6) 16, word t.mem (stackArg t 6) 24] at hw
  have h0 : s.mem.readW (stackArg s 6) 64 = t.mem.readW (stackArg t 6) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  have h1 : s.mem.readW (stackArg s 6 + 8) 64 = t.mem.readW (stackArg t 6 + 8) 64 := by
    have := (List.cons.inj (List.cons.inj hw).2).1
    simp only [Bignum.word, off] at this
    exact this
  unfold keyOfState
  rw [keyRetries, keyRetries, h0, h1, hdom, hsp, r0, r2, r4, r5, keyLen, keyLen, ha 0 (by decide),
    ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide), ha 5 (by decide),
    ha 6 (by decide)]

theorem key_constantTime (v : RoundImpl) :
    ConstantTime isa keyContract.pre keyContract.pub (code (attemptCall v)) := by
  refine RelCT.constantTime ((key_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨(keyOfState s, (keyResult s).statuses), ⟨⟨hs, rfl⟩, rfl⟩,
    ⟨ht, (key_public_descriptor hp).symm⟩, hp.2.2.2.2.2.2.2.2.2.2.symm⟩

end VG.Proof.Ffdh.X86_64.KeyGeneration
