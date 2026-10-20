module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Compare
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Update
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Exit
import VerifiedGarbage.Proof.Framework.Block

/-! Composition of entropy consumption with acceptance and the two kinds of rejection. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

abbrev KeyClassified (p : KeyPublic) (original : State) (used keys scalars : Nat) (s : State) : Prop :=
  if currentStatus p original used = 1 then KeyDone p original (acceptedResult p original used) s
  else if currentStatus p original used = 2 then
    KeyLive p original (used + p.len) keys (scalars - 1) s ∧ lowWord s.mem p.control 14 = 4
  else KeyLive p original (used + p.len) (keys - 1) 128 s ∧ lowWord s.mem p.control 14 = 4

theorem classify_head {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (post : AttemptPost p original used s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.advance ++ [.cmp .r9 (.imm 1)])) s fun t =>
      KeyLive p original (used + p.len) keys scalars t ∧
      t.z = decide (currentStatus p original used = 1) ∧
      t.gpr .r9 = BitVec.ofNat 32 (currentStatus p original used) ∧
      Frame [rControl p] s.mem t.mem := by
  have bound : currentStatus p original used < 4 := by
    rcases currentStatus_cases p original used with eq | eq | eq <;> omega
  have native : s.gpr .r0 = BitVec.ofNat 32 (currentStatus p original used) := by
    rw [← post.status, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [WP.block_append_iff]
  refine WP.mono (h.advance room) ?_
  rintro u ⟨live, status, frame⟩
  refine WP.mono (compareStatus_ok u bound (by decide : 1 < 4) (status.trans native)) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨live.keep rest mem, flag, (rest.gpr .r9 (by simp)).trans (status.trans native), by rw [mem]; exact frame⟩

theorem classify {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (room : used + p.len ≤ p.randLen)
    (keysPositive : 0 < keys) (scalarsPositive : 0 < scalars) (post : AttemptPost p original used s) :
    WP isa VG.Impl.Ffdh.Arm.KeySearch.classify s (KeyClassified p original used keys scalars) := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.classify, WP.seq_iff]
  refine WP.mono (classify_head h room post) ?_
  rintro u ⟨live, flag, status, frame⟩
  rcases currentStatus_cases p original used with h1 | h2 | h3
  · simp only [h1, decide_true] at flag
    have target : KeyClassified p original used keys scalars =
        KeyDone p original (acceptedResult p original used) := by
      funext t
      simp only [KeyClassified, h1, ite_true]
    rw [target]
    refine WP.ite true (by change some u.z = some true; rw [flag]) ?_ (by intro bad; cases bad)
    intro _
    have oldOutput : KeyOutput p (acceptedResult p original used) s.mem := by
      simpa only [h1, ite_true, KeyOutput, acceptedResult] using post.output
    have output := oldOutput.control_frame h.input frame
    refine WP.mono (live.terminal (status := 1) (.inl rfl)) ?_
    rintro t ⟨done, result, request, high, terminalFrame⟩
    apply done.done (result := acceptedResult p original used) rfl result
    · exact done.policy (request := 0) (by decide) request high
    · exact output.control_frame h.input terminalFrame
  · simp only [h2, show (2 : Nat) ≠ 1 by decide, decide_false] at flag
    have target : KeyClassified p original used keys scalars = (fun t =>
        KeyLive p original (used + p.len) keys (scalars - 1) t ∧ lowWord t.mem p.control 14 = 4) := by
      funext t
      simp only [KeyClassified, h2, show (2 : Nat) ≠ 1 by decide, ite_false, ite_true]
    rw [target]
    refine WP.ite false (by change some u.z = some false; rw [flag]) (by intro bad; cases bad) ?_
    intro _
    rw [WP.seq_iff]
    refine WP.mono (compareStatus_ok u (by rw [h2]; decide) (by decide : 2 < 4) status) ?_
    rintro t ⟨⟨test, mem⟩, rest⟩
    have kept := live.keep rest mem
    simp only [h2, decide_true] at test
    refine WP.ite true (by change some t.z = some true; rw [test]) ?_ (by intro bad; cases bad)
    intro _
    exact kept.reject_scalar scalarsPositive
  · simp only [h3, show (3 : Nat) ≠ 1 by decide, decide_false] at flag
    have target : KeyClassified p original used keys scalars = (fun t =>
        KeyLive p original (used + p.len) (keys - 1) 128 t ∧ lowWord t.mem p.control 14 = 4) := by
      funext t
      simp only [KeyClassified, h3, show (3 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 2 by decide, ite_false]
    rw [target]
    refine WP.ite false (by change some u.z = some false; rw [flag]) (by intro bad; cases bad) ?_
    intro _
    rw [WP.seq_iff]
    refine WP.mono (compareStatus_ok u (by rw [h3]; decide) (by decide : 2 < 4) status) ?_
    rintro t ⟨⟨test, mem⟩, rest⟩
    have kept := live.keep rest mem
    have statusT := (rest.gpr .r9 (by simp)).trans status
    simp only [h3, show (3 : Nat) ≠ 2 by decide, decide_false] at test
    refine WP.ite false (by change some t.z = some false; rw [test]) (by intro bad; cases bad) ?_
    intro _
    rw [WP.seq_iff]
    refine WP.mono (compareStatus_ok t (by rw [h3]; decide) (by decide : 3 < 4) statusT) ?_
    rintro q ⟨⟨test3, mem3⟩, rest3⟩
    have kept3 := kept.keep rest3 mem3
    simp only [h3, decide_true] at test3
    refine WP.ite true (by change some q.z = some true; rw [test3]) ?_ (by intro bad; cases bad)
    intro _
    exact kept3.reject_public keysPositive

end VG.Proof.Ffdh.Arm.KeySearch
