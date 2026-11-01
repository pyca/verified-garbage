module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Contract
public import VerifiedGarbage.Impl.Sha3.PPC64LE.Stream
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Absorb
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Pad
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Squeeze
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.CT
import VerifiedGarbage.Proof.Sha3.PPC64LE.Stream.Lit
import VerifiedGarbage.Proof.MdStream.PPC64LE.Common
public import VerifiedGarbage.Proof.Framework.PPC64LE.Call
public import VerifiedGarbage.TCB.PPC64LE.Target
import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# The SHA-3 sponge on PPC64LE: `Verified`

`absorb`, `pad` and `squeeze` (`Stream/`), each run in a frame that saves the
link register (`WP.frameReg`): correctness, with constant time from `CT`, and
a state satisfying each precondition. They take their working space as an
argument; `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` run
them in a frame that allocates it (`Verified.stackScratch`): 640 bytes,
after the frame's 32-byte header.
-/

@[expose] public section

namespace VG.Proof.Sha3.PPC64LE.Stream

open VG VG.PPC64LE
open VG.Spec.Sha3 (stateAt bytesAt)
open VG.Proof.MdStream.PPC64LE (frame_sub write_frame_bytes WP.cons)

/-- The state a function's main part starts in: the link register moved to
`r0`, then pushed in a frame. -/
abbrev inner (s₀ : State) : State := framed .r0 (s₀.write .r0 s₀.lr)

theorem inner_gpr (s₀ : State) {r : Reg} (h : r ≠ .r0) : (inner s₀).gpr r = s₀.gpr r := by
  simp [framed, State.write, h]

/-- The bytes of a region disjoint from the frame are those before it. -/
theorem inner_bytes {s₀ : State} {R : Region} (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ R)
    (hR : R.len < 2 ^ 64) {i : Nat} (hi : i < R.len) :
    (inner s₀).mem (R.base + BitVec.ofNat 64 i) = s₀.mem (R.base + BitVec.ofNat 64 i) :=
  write_frame_bytes (v := s₀.lr) hd hR hi

theorem inner_state {s₀ : State} {p : Addr} (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ ⟨p, 200⟩) :
    stateAt (inner s₀).mem p = stateAt s₀.mem p :=
  Proof.Sha3.stateAt_congr fun _ hi => inner_bytes (R := ⟨p, 200⟩) hd (show 200 < 2 ^ 64 by decide) hi

theorem inner_bytesAt {s₀ : State} {p : Addr} {n : Nat} (hd : Region.Disjoint ⟨s₀.sp - 48, 48⟩ ⟨p, n⟩)
    (hn : n < 2 ^ 64) : bytesAt (inner s₀).mem p n = bytesAt s₀.mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => inner_bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

theorem pushFrames_of_noFrames {c : Prog isa} (h : c.noFrames = true) : pushFrames c = true := by
  induction c <;> simp_all [Code.noFrames, pushFrames]

/-- The epilogue of the frame: the link register is restored from `r0`, and
the callee-saved registers and the stack pointer are the caller's. -/
theorem withLr_ok {main : Prog isa} {s₀ : State} {Q : State → State → Prop}
    (hsp : 48 ≤ s₀.sp.toNat)
    (hd : ∀ R ∈ s₀.wr, Region.Disjoint ⟨s₀.sp - 48, 48⟩ R)
    (hmain : WP isa main (inner s₀) fun s' =>
      (∀ r ∈ preserved, s'.gpr r = (inner s₀).gpr r) ∧ s'.sp = (inner s₀).sp ∧ Q (inner s₀) s')
    (hQ : ∀ s' s'', s''.mem = s'.mem → s''.gpr .r3 = s'.gpr .r3 → Q (inner s₀) s' → Q s₀ s'')
    (hn : main.noFrames = true) :
    WP isa (Impl.Sha3.PPC64LE.Stream.withLr main) s₀ fun s' => abiPreserved s₀ s' ∧ Q s₀ s' := by
  unfold Impl.Sha3.PPC64LE.Stream.withLr
  refine WP.seq (MdStream.PPC64LE.WP.cons PPC64LE.exec_mflr (WP.block_nil (WP.seq ?_)))
  refine WP.frameReg (by exact hsp) (fun R hR => (hd R hR).sub_left (frame_sub _))
    (WP.mono hmain fun s' ⟨hk, _, hq⟩ => ?_)
    (by rw [fdepth_of_noFrames hn]; decide) (pushFrames_of_noFrames hn)
  refine MdStream.PPC64LE.WP.cons PPC64LE.exec_mtlr (WP.block_nil ⟨⟨fun r hr => ?_, rfl, ?_⟩, hQ s' _ rfl rfl hq⟩)
  · have h0 : r ≠ .r0 := by revert r hr; decide
    simp only [State.write, h0, ite_false]
    rw [hk r hr]
    simp only [framed, State.write, h0, ite_false]
  · simp [State.write]

/-! ## `absorb` -/

theorem absorbMain_noFrames : Impl.Sha3.PPC64LE.Stream.absorbMain.noFrames = true := by lit_decide

theorem absorb_correct (s : State) (hs : Proof.Sha3.absorbPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.Stream.absorb s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.absorbPPC64LE.post s s' := by
  obtain ⟨hp, hk⟩ := Absorb.pre_of hs
  have hpi : Absorb.Pre (inner s) := ⟨hp.rd, hp.wr, hp.st_scr, hp.d_st, hp.d_scr, hp.rate, hp.pos_lt⟩
  refine withLr_ok (Q := fun s₀ s' => Proof.Sha3.absorbPPC64LE.post s₀ s') hk.sp48
    (fun R hR => ?_) (WP.mono (Absorb.correctMain hpi) fun s' ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩)
    (fun s' s'' hm h3 ⟨h₁, h₂⟩ => ⟨fun msg hR hpm => ?_, by rw [h3]; simpa (disch := decide) only [inner_gpr] using h₂⟩) absorbMain_noFrames
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [hk.st, hk.scr]
  · simp (disch := decide) only [inner_gpr] at h₁
    have e := h₁ msg (by rw [Proof.Sha3.repr_iff, inner_state hk.st]; exact hR) hpm
    rw [Proof.Sha3.repr_iff, hm]
    rw [Proof.Sha3.repr_iff, inner_bytesAt hk.d (s.gpr .r7).isLt] at e
    exact e

/-- A state satisfying `absorb`'s precondition, with no data. -/
def absorbSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 72 | .r6 => 0x2000 | .r8 => 0x3000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem absorb_verified :
    Verified PPC64LE.target Impl.Sha3.PPC64LE.Stream.absorb (Spec.Sha3.absorbScratchContract PPC64LE.abi 48) :=
  Verified.of_correct absorb_correct absorb_ct (by
    sig_implies [Spec.Sha3.absorbScratchContract, Spec.Sha3.absorbScratchSig, Spec.Sha3.absorbPre,
      Spec.Sha3.absorbPost, Proof.Sha3.absorbPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [absorbSat]
      using absorbSat)

/-! ## `pad` -/

theorem padMain_noFrames : Impl.Sha3.PPC64LE.Stream.padMain.noFrames = true := by lit_decide

theorem pad_correct (s : State) (hs : Proof.Sha3.padPPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.Stream.pad s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.padPPC64LE.post s s' := by
  obtain ⟨hp, hk⟩ := Pad.pre_of hs
  have hpi : Pad.Pre (inner s) := ⟨hp.rd, hp.wr, hp.st_scr, hp.rate, hp.pos_lt⟩
  refine withLr_ok (Q := fun s₀ s' => Proof.Sha3.padPPC64LE.post s₀ s') hk.sp48
    (fun R hR => ?_) (WP.mono (Pad.correctMain hpi) fun s' ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩)
    (fun s' s'' hm _ h₁ msg hR hpm => ?_) padMain_noFrames
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl
    exacts [hk.st, hk.scr]
  · simp (disch := decide) only [Proof.Sha3.padPPC64LE, inner_gpr] at h₁
    rw [hm]
    exact h₁ msg (by rw [Proof.Sha3.repr_iff, inner_state hk.st]; exact hR) hpm

/-- A state satisfying `pad`'s precondition. -/
def padSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 136 | .r7 => 0x3000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x3000, 640⟩]

theorem pad_verified :
    Verified PPC64LE.target Impl.Sha3.PPC64LE.Stream.pad (Proof.Sha3.padScratchContract PPC64LE.abi 48) :=
  Verified.of_correct pad_correct pad_ct (by
    sig_implies [Proof.Sha3.padScratchContract, Proof.Sha3.padScratchSig, Spec.Sha3.padPre,
      Spec.Sha3.padPost, Proof.Sha3.padPPC64LE, PPC64LE.abi, PPC64LE.argRegs] [padSat]
      using padSat)

/-! ## `squeeze` -/

theorem squeezeMain_noFrames : Impl.Sha3.PPC64LE.Stream.squeezeMain.noFrames = true := by lit_decide

theorem squeeze_correct (s : State) (hs : Proof.Sha3.squeezePPC64LE.pre s) :
    ∃ t s', Exec isa Impl.Sha3.PPC64LE.Stream.squeeze s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.squeezePPC64LE.post s s' := by
  obtain ⟨hp, hk⟩ := Squeeze.pre_of hs
  have hpi : Squeeze.SPre (inner s) :=
    ⟨hp.rd, hp.wr, hp.st_o, hp.st_c, hp.o_c, hp.rate_mem, hp.pos_le⟩
  refine withLr_ok (Q := fun s₀ s' => Proof.Sha3.squeezePPC64LE.post s₀ s') hk.sp48
    (fun R hR => ?_) (WP.mono (Squeeze.correctMain hpi) fun s' ⟨h₁, h₂, h₃⟩ => ⟨h₁, h₂, h₃⟩)
    (fun s' s'' hm h3 h => ?_) squeezeMain_noFrames
  · rw [hp.wr] at hR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    exacts [hk.st, hk.o, hk.c]
  · simp (disch := decide) only [Proof.Sha3.squeezePPC64LE, inner_gpr] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    rw [inner_state hk.st] at h₁ h₃
    refine ⟨by rw [hm]; exact h₁, by rw [h3]; exact h₂, fun d => ?_⟩
    rw [hm, h3]
    exact h₃ d

/-- A state satisfying `squeeze`'s precondition, with no output. -/
def squeezeSat : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 72 | .r6 => 0x2000 | .r8 => 0x3000 | _ => 0
  lr := 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 200⟩, ⟨0x2000, 0⟩, ⟨0x3000, 640⟩]

theorem squeeze_verified :
    Verified PPC64LE.target Impl.Sha3.PPC64LE.Stream.squeeze
      (Proof.Sha3.squeezeScratchContract PPC64LE.abi 48) :=
  Verified.of_correct squeeze_correct squeeze_ct (by
    sig_implies [Proof.Sha3.squeezeScratchContract, Proof.Sha3.squeezeScratchSig, Spec.Sha3.squeezePre,
      Spec.Sha3.squeezePost, Proof.Sha3.squeezePPC64LE, PPC64LE.abi, PPC64LE.argRegs] [squeezeSat]
      using squeezeSat)

end VG.Proof.Sha3.PPC64LE.Stream
