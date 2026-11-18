module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorSearch
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeState
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.RsaOaep.AArch64.Hash
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInvariant
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeIteration
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStages
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorStages
import VerifiedGarbage.Proof.Dsa.Encoding
public import Mathlib.Data.Nat.Basic
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInput
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorStep
meta import VerifiedGarbage.Proof.Rsa.AArch64.CTBase
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInput
meta import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorModulus
public import VerifiedGarbage.Proof.Dsa.AArch64.ChildCT
import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFields
import VerifiedGarbage.Proof.Dsa.AArch64.Parent
meta import VerifiedGarbage.Proof.Dsa.AArch64.ChildCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorFields
meta import VerifiedGarbage.Proof.Dsa.AArch64.Parent
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
public import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorPower
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorPlan
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicFinishCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorPower
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorModulus
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
import VerifiedGarbage.Proof.Dsa.AArch64.Run
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.Workspace
meta import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorArguments
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorArguments
import Mathlib.Algebra.Group.Nat.Defs
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DecrementOdd
import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.DecrementOdd
meta import VerifiedGarbage.Proof.Dsa.AArch64.RangeCT
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.LoadCT
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.GeneratorRange
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.CandidateArithmetic
meta import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import Mathlib.Data.Nat.Basic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorInvariant
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchPlan
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.TapeLoop
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.GeneratorSearchMemory
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.TapeIteration

/-! ### `Dsa.AArch64.Generation.GeneratorLoopCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorIterationCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorSearchTailCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorDecisionCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorRangePlanCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorWorkspaceCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorFrameCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorRangeCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorLoadsCT`, which this module and modules that import it used -/

section

/-! # Public-address loads for generator range checks -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

structure GeneratorLoadPublic where
  modulus : LoadPublic
  candidate : Addr
  bytes : List Byte

def GeneratorLoadPublic.second (p : GeneratorLoadPublic) : LoadPublic :=
  ⟨p.modulus.B, p.modulus.Z, p.modulus.w, p.candidate, p.bytes⟩

def GeneratorLoadBefore (p : GeneratorLoadPublic) (s : State) : Prop :=
  LoadState 16 17 p.modulus s ∧ LoadState 18 19 p.second s

theorem generatorFirst_ready {p : GeneratorLoadPublic} {s : State}
    (h : GeneratorLoadBefore p s) :
    WP isa (seqs (loadA 0 16 17)) s (LoadState 18 19 p.second) := by
  refine WP.mono (loadCandidateArray_ok h.1.ws (by decide : 0 < 16) (by decide : 16 < 32)
    (by decide : 17 < 32) h.1.pointer h.1.length h.1.source h.1.positive h.1.fits)
    fun t ⟨ht, _, f, hk⟩ => ?_
  have hdr (d : Nat) (hd : d + 8 ≤ 256) :
      word t.mem p.modulus.B d = word s.mem p.modulus.B d := by
    apply f.word_eq
    · simp only [List.mem_singleton]; rintro r rfl
      left; simp only [slot, VG.Impl.Bignum.hdrBytes]; omega_using [hd]
    · have := h.1.ws.h256; have := h.1.ws.scr.nowrap; omega_using [hd]
  refine ⟨ht, (hdr 144 (by decide)).trans h.2.pointer,
    (hdr 152 (by decide)).trans h.2.length, h.2.source.congrK ?_ hk,
    h.2.positive, h.2.fits⟩
  intro a ha
  apply f a
  simp only [List.mem_singleton]; rintro r rfl
  right
  exact Nat.le_trans (h.1.ws.sl (by decide : 0 < 16)) ha

theorem generatorLoadPair_ct :
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.AArch64.Generation.generatorLoadPair
      (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.generatorLoadPair
  refine RelCT.seq (two_post ?_ (fun _ _ h => generatorFirst_ready h)) ?_
  · exact two_map GeneratorLoadPublic.modulus (fun _ _ h => h.1)
      (loadCandidate_ct (by decide : 0 < 16) (by decide : 16 < 32)
        (by decide : 17 < 32) (by taint_decide) (by taint_decide) (by taint_decide))
  · exact two_map GeneratorLoadPublic.second (fun _ _ h => h)
      (loadCandidate_ct (by decide : 1 < 16) (by decide : 18 < 32)
        (by decide : 19 < 32) (by taint_decide) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Timing of generator-input and generator-output range filtering -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys

def GeneratorRangeBefore (p : GeneratorLoadPublic) (s : State) : Prop :=
  GeneratorLoadBefore p s ∧ Spec.Rsa.os2ip p.modulus.bytes % 2 = 1

def GeneratorRangeLoaded (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w 0) p.w % 2 = 1

def GeneratorRangeWorkspace (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.AArch64.Ws s p.B p.Z p.w

theorem generatorRangeWorkspace_ct :
    RelCT isa (Two GeneratorRangeWorkspace) (Impl.Dsa.AArch64.Checks.rangeMask true)
      (fun _ _ => True) := by
  exact two_map (fun p : LoadPublic => (⟨p.B, p.Z, p.w⟩ : VG.Proof.Bignum.AArch64.Ws))
    (fun _ _ h => ⟨⟨_, h.good⟩, h.w1, by dsimp only; have := h.w2; omega_using [this]⟩)
    (VG.Proof.Dsa.AArch64.rangeMask_ct true)

theorem generatorLoadPair_ready {p : GeneratorLoadPublic} {s : State}
    (h : GeneratorLoadBefore p s) :
    WP isa Impl.Dsa.AArch64.Generation.generatorLoadPair s fun t =>
      VG.Proof.Rsa.AArch64.Ws t p.modulus.B p.modulus.Z p.modulus.w ∧
      wv t.mem p.modulus.B (slot p.modulus.w 0) p.modulus.w = Spec.Rsa.os2ip p.modulus.bytes :=
  WP.mono (generatorLoadPair_ok h.1.ws h.1.pointer h.1.length h.2.pointer h.2.length
    h.1.source h.2.source h.1.positive h.1.fits h.2.positive h.2.fits)
    (fun _ h => ⟨h.1, h.2.1⟩)

theorem generatorDecrement_ct :
    RelCT isa (Two GeneratorRangeLoaded) (.block (decA 0))
      (Two GeneratorRangeWorkspace) := by
  unfold decA
  simp only [List.append_assoc]
  exact ws_block_ct (fun p : LoadPublic => p.B) (fun p : LoadPublic => p.Z) (fun p : LoadPublic => p.w) (fun _ _ h => h.1)
    (by taint_decide) (fun _ _ h => WP.mono
      (decrementOdd_ok h.1 (by decide : 0 < 16) h.2) fun _ ht => ht.1)

theorem generatorRange_ct :
    RelCT isa (Two GeneratorRangeBefore) Impl.Dsa.AArch64.Generation.generatorRange
      (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.generatorRange
  refine RelCT.seq (two_post (generatorLoadPair_ct.mono
    (fun _ _ ⟨p, hs, ht, hsp⟩ => ⟨p, hs.1, ht.1, hsp⟩) (fun _ _ h => h))
    (fun p s h => WP.mono (generatorLoadPair_ready h.1) fun t ht =>
      show GeneratorRangeLoaded p.modulus t from ⟨ht.1, ht.2 ▸ h.2⟩)) ?_
  exact RelCT.seq (two_map GeneratorLoadPublic.modulus (fun _ _ h => h) generatorDecrement_ct)
    generatorRangeWorkspace_ct

theorem generatorResult_ct :
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.AArch64.Generation.generatorResult
      (fun _ _ => True) := by
  unfold Impl.Dsa.AArch64.Generation.generatorResult
  refine RelCT.seq (two_post generatorLoadPair_ct
    (fun p s h => WP.mono (generatorLoadPair_ready h) fun _ ht =>
      show GeneratorRangeWorkspace p.modulus _ from ht.1)) ?_
  exact two_map GeneratorLoadPublic.modulus
    (fun _ _ h => h) generatorRangeWorkspace_ct

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Bind public generator inputs through the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Dsa.Generation.Layout

structure GeneratorFramePublic where
  B : Addr
  F : Addr
  arena : Addr
  hp : Addr
  Z : Nat
  w : Nat
  width : w ≤ 48
  pb : List Byte
  xb : List Byte
  pLength : pb.length = 8 * w
  xLength : xb.length = pb.length
  separate : ∀ k < 34, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8

def GeneratorFramePublic.loads (c : GeneratorFramePublic) (result : Bool) : GeneratorLoadPublic :=
  ⟨⟨c.B, c.Z, c.w, off c.arena p, c.pb⟩, if result then off c.arena g else c.hp, c.xb⟩

structure GeneratorFrameInputs (result : Bool) (c : GeneratorFramePublic) (s : State) : Prop where
  stack : s.sp = c.F
  read : ∀ k < 34, InRegions (s.rd ++ s.wr) (off c.F (8 * k)) 8
  arena : word s.mem c.F 40 = c.arena
  candidate : word s.mem c.F 168 = c.hp
  modulus : Src s c.B c.Z (off c.arena p) c.pb
  source : Src s c.B c.Z (if result then off c.arena g else c.hp) c.xb
  odd : result = false → Spec.Rsa.os2ip c.pb % 2 = 1

def GeneratorFrameBefore (len : Nat) (result : Bool) (c : GeneratorFramePublic) (s : State) : Prop :=
  GeneratorFrameInputs result c s ∧ Ws s c.B c.Z c.w ∧ c.pb.length = len

def GeneratorFrameLoaded (result : Bool) (c : GeneratorFramePublic) (s : State) : Prop :=
  GeneratorLoadBefore (c.loads result) s ∧ (result = false → Spec.Rsa.os2ip c.pb % 2 = 1)

theorem generatorFrame_ready {len : Nat} {result : Bool} {c : GeneratorFramePublic} {s : State}
    (h : GeneratorFrameBefore len result c s) :
    WP isa (.block (headerArguments (generatorRangeArguments len result))) s (GeneratorFrameLoaded result c) := by
  have hl : len < 2 ^ 16 := by omega_using [c.width, c.pLength, h.2.2]
  refine WP.mono (generatorArguments_ok h.2.1 hl result h.1.stack h.1.read
    (W := fun k => word s.mem c.F (8 * k)) (fun _ _ => rfl) c.separate)
    fun t ⟨ht, hp, hpl, hx, hxl, hf, hk⟩ => ?_
  have frame : Frm c.B [(128, 128)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(128, 128)], r.1 + r.2 ≤ c.Z := by
    simp only [List.mem_singleton, forall_eq]; exact h.2.1.h256
  have sp := h.1.modulus.congrK (InScr.of_frm frame bound) hk
  have sx := h.1.source.congrK (InScr.of_frm frame bound) hk
  have pp : word t.mem c.B 128 = off c.arena p := by simpa only [h.1.arena] using hp
  have xp : word t.mem c.B 144 = if result then off c.arena g else c.hp := by
    simpa only [h.1.arena, h.1.candidate] using hx
  have pl : word t.mem c.B 136 = BitVec.ofNat 64 c.pb.length := by rw [h.2.2]; exact hpl
  have xl : word t.mem c.B 152 = BitVec.ofNat 64 c.xb.length := by
    rw [c.xLength, h.2.2]; exact hxl
  have positive : 1 ≤ c.pb.length := by omega_using [c.pLength, h.2.1.w1]
  exact ⟨⟨⟨ht, pp, pl, sp, positive, Nat.le_of_eq c.pLength⟩,
    ⟨ht, xp, xl, sx, c.xLength ▸ positive, Nat.le_of_eq (c.xLength.trans c.pLength)⟩⟩, h.1.odd⟩

theorem generatorFrame_ct (len : Nat) (result : Bool)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (generatorRangeArguments len result))) hc).isSome = true) :
    RelCT isa (Two (GeneratorFrameBefore len result))
      (.seq (.block (headerArguments (generatorRangeArguments len result)))
        (if result then generatorResult else generatorRange)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_taint [.x0] (fun _ _ _ hs ht r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.1.x0.trans ht.2.1.x0.symm) ht)
    (fun _ _ h => generatorFrame_ready h)) ?_
  cases result
  · exact two_map (fun c : GeneratorFramePublic => c.loads false)
      (fun _ _ h => ⟨h.1, h.2 rfl⟩) generatorRange_ct
  · exact two_map (fun c : GeneratorFramePublic => c.loads true)
      (fun _ _ h => h.1) generatorResult_ct

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Initialize generator range-check scratch while retaining source bytes and frame arguments -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.Rsa VG.Proof.Rsa.AArch64 VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Dsa.Generation.Layout

structure GeneratorWorkspacePublic where
  frame : GeneratorFramePublic
  base : frame.B = off frame.arena arithmetic
  room : slot frame.w 16 ≤ frame.Z
  lower : 2 ≤ frame.w
  upper : frame.w ≤ 48
  outside : ∀ k < 34, ∀ i < 8, frame.Z ≤ ofs frame.B (off (off frame.F (8 * k)) i)

def GeneratorWorkspaceBefore (w len : Nat) (result : Bool) (c : GeneratorWorkspacePublic) (s : State) : Prop :=
  GeneratorFrameInputs result c.frame s ∧ Scr s c.frame.B c.frame.Z ∧
    c.frame.w = w ∧ c.frame.pb.length = len

def GeneratorWorkspaceBase (w len : Nat) (result : Bool) (c : GeneratorWorkspacePublic) (s : State) : Prop :=
  GeneratorWorkspaceBefore w len result c s ∧ s.gpr .x0 = c.frame.B

theorem generatorWorkspace_base {w len : Nat} {result : Bool} {c : GeneratorWorkspacePublic} {s : State}
    (h : GeneratorWorkspaceBefore w len result c s) :
    WP isa (.block workspaceBase) s (GeneratorWorkspaceBase w len result c) := by
  have ld := h.1.read 5 (by decide)
  have hv : s.mem.readW (off c.frame.F 40) 64 = c.frame.arena := h.1.arena
  have step : WP isa (.block workspaceBase) s fun t => t.gpr .x0 = c.frame.B ∧ t.mem = s.mem := by
    brun [workspaceBase, exec_ldrSp (off := 40) (by decide), h.1.stack, ld, hv]
    change c.frame.arena + (BitVec.ofNat 16 arithmetic).setWidth 64 = _
    rw [show (BitVec.ofNat 16 arithmetic).setWidth 64 = BitVec.ofNat 64 arithmetic by decide]
    exact c.base.symm
  refine WP.mono (WP.keep [.x0, .x3] step rfl rfl rfl) fun t ⟨⟨hb, hm⟩, hk⟩ => ?_
  refine ⟨⟨?_, h.2.1.congr hk.wr, h.2.2⟩, hb⟩
  exact ⟨hk.sp.trans h.1.stack,
    (fun k hk' => by rw [hk.rd, hk.wr]; exact h.1.read k hk'),
    hm ▸ h.1.arena, hm ▸ h.1.candidate, h.1.modulus.congrK (fun _ _ => by rw [hm]) hk,
    h.1.source.congrK (fun _ _ => by rw [hm]) hk,
    h.1.odd⟩

theorem generatorWorkspace_ready {w len : Nat} {result : Bool} {c : GeneratorWorkspacePublic} {s : State}
    (h : GeneratorWorkspaceBase w len result c s) :
    WP isa (workspace w) s (GeneratorFrameBefore len result c.frame) := by
  have step := workspace_ok h.1.2.1 h.2 c.room c.lower c.upper
  rw [h.1.2.2.1] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have hz : 256 ≤ c.frame.Z := Nat.le_trans (Nat.le_add_right 256 _) c.room
  have bound : ∀ r ∈ workspaceRanges, r.1 + r.2 ≤ c.frame.Z := by
    simp only [workspaceRanges, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only <;> omega_using [hz]
  have ht' : Ws t c.frame.B c.frame.Z c.frame.w := by rw [h.1.2.2.1]; exact ht
  refine ⟨?_, ht', h.1.2.2.2⟩
  refine ⟨hk.sp.trans h.1.1.stack, ?_, ?_, ?_,
    h.1.1.modulus.congrK (InScr.of_frm ff bound) hk, h.1.1.source.congrK (InScr.of_frm ff bound) hk, h.1.1.odd⟩
  · intro k hk'; rw [hk.rd, hk.wr]; exact h.1.1.read k hk'
  · exact (frame_word_of_workspace ff bound (c.outside 5 (by decide))).trans h.1.1.arena
  · exact (frame_word_of_workspace ff bound (c.outside 21 (by decide))).trans h.1.1.candidate

theorem generatorRangeFromFrame_ct_of (w len : Nat) (result : Bool) {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (generatorRangeArguments len result))) hc₂).isSome = true) :
    RelCT isa (Two (GeneratorWorkspaceBefore w len result))
      (seqs [.block workspaceBase, workspace w, (.seq (.block (headerArguments (generatorRangeArguments len result)))
        (if result then generatorResult else generatorRange))]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => generatorWorkspace_base h))
    (RelCT.seq (two_post (two_taint [.x0] ?_ ht₁)
      (fun _ _ h => generatorWorkspace_ready h)) ?_)
  · intro c s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.2.trans ht.2.symm
  · exact two_map GeneratorWorkspacePublic.frame (fun _ _ h => h) (generatorFrame_ct len result ht₂)

theorem generatorRangeFromFrame_ct (len : Nat) (result : Bool)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorWorkspaceBefore (len / 8) len result))
      (generatorRangeFromFrame len result) (fun _ _ => True) := by
  unfold generatorRangeFromFrame
  rcases hl with rfl | rfl | rfl <;> cases result
  all_goals
    exact generatorRangeFromFrame_ct_of _ _ _ (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.GeneratorEvaluateCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorFreshCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorModulusCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.Generation.GeneratorPowerCT`, which only this module used -/

section

/-! # Generator exponentiation reuses the verified public-power timing proof -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64

def GeneratorPlan.powerCall (p : GeneratorPlan) (mi : BitVec 64) : Call3Public where
  bytes := ⟨⟨p.B, activeBytes, pWorkspace, outerWords, p.len / 8⟩,
    off p.B VG.Impl.Dsa.Generation.Layout.exponent, p.len⟩
  minv := mi
  modulus := Spec.Dsa.decodeBE p.pb
  base := p.hp
  baseLen := p.len
  output := off p.B VG.Impl.Dsa.Generation.Layout.g
  outputLen := p.len
  parentInverse := 0
  greater := p.pPositive
  odd := p.pOdd
  lower := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  fits := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  upper := by dsimp only; decide
  width48 := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  basePositive := by rcases p.width with h | h | h <;> rw [h] <;> decide
  baseFits := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  expPositive := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  expLimit := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  extent := by dsimp only; decide
  childLow := by dsimp only; decide
  childHigh := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  offsetBound := by dsimp only; decide
  outputPositive := by rcases p.width with h | h | h <;> rw [h] <;> decide
  outputBound := by rcases p.width with h | h | h <;> rw [h] <;> decide
  outputWidth := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide

structure GeneratorPowerReady (p : GeneratorPlan) (mi : BitVec 64) (s : State) : Prop where
  parent : Good s p.B activeBytes outerWords 0
  child : ChildReady s.mem p.B pWorkspace (p.len / 8) (Spec.Dsa.decodeBE p.pb) mi
  base : word s.mem p.B 272 = p.hp
  exponent : word s.mem p.B 288 = off p.B VG.Impl.Dsa.Generation.Layout.exponent
  length : word s.mem p.B 328 = BitVec.ofNat 64 p.len
  hSource : Src s p.B activeBytes p.hp p.hb
  eSource : Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.exponent) p.eb
  output : ∀ i < p.len, InRegions s.wr (off (off p.B VG.Impl.Dsa.Generation.Layout.g) i) 1

theorem generatorPower_call {p : GeneratorPlan} {mi : BitVec 64} {s : State}
    (h : GeneratorPowerReady p mi s) :
    PublicPower.CallPre ⟨.input .g, .pLen⟩ ⟨.input .x, .pLen⟩
      ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩ (p.powerCall mi, p.eb) s := by
  have hb : OperandBytes s p.B activeBytes ⟨.input .g, .pLen⟩ p.hb :=
    ⟨by change word s.mem p.B 328 = _; rw [p.hLength]; exact h.length,
      by change Src s p.B activeBytes (word s.mem p.B 272) p.hb; rw [h.base]; exact h.hSource⟩
  have he : OperandBytes s p.B activeBytes ⟨.input .x, .pLen⟩ p.eb :=
    ⟨by change word s.mem p.B 328 = _; rw [p.eLength]; exact h.length,
      by change Src s p.B activeBytes (word s.mem p.B 288) p.eb; rw [h.exponent]; exact h.eSource⟩
  exact ⟨⟨h.parent, h.child, ⟨p.hb, p.eb, hb, he, p.hLength, p.eLength⟩,
    h.base, h.exponent, rfl, h.length, h.output, p.gParentOutside⟩, h.eSource, p.eLength⟩

def GeneratorPowerBefore (p : GeneratorPlan) (s : State) : Prop := ∃ mi, GeneratorPowerReady p mi s

theorem generatorPower_inverse {p : GeneratorPlan} {s t : State} {mi mj : BitVec 64}
    (hs : GeneratorPowerReady p mi s) (ht : GeneratorPowerReady p mj t) : mi = mj := by
  have positive : 0 < p.len / 8 := by rcases p.width with h | h | h <;> omega_using [h]
  have ls : (word s.mem (off p.B pWorkspace) (slot (p.len / 8) VG.Impl.Bignum.Public.aN)).toNat =
      Spec.Dsa.decodeBE p.pb % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.len / 8) _ _ _ positive, hs.child.modulus]
  have lt : (word t.mem (off p.B pWorkspace) (slot (p.len / 8) VG.Impl.Bignum.Public.aN)).toNat =
      Spec.Dsa.decodeBE p.pb % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.len / 8) _ _ _ positive, ht.child.modulus]
  have hi := hs.child.inverse
  have hj := ht.child.inverse
  rw [ls] at hi
  rw [lt] at hj
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact p.pOdd) hi hj

theorem generatorPower_ct (M : Mont)  :
    RelCT isa (Two GeneratorPowerBefore) (Impl.Dsa.AArch64.Generation.generatorPower M.mm)
      (fun _ _ => True) := by
  apply (PublicPower.corePublicPow_ct M (a := ⟨.input .g, .pLen⟩)
    (b := ⟨.input .x, .pLen⟩) (output := ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩)
    (o := pWorkspace) (by trivial) (by trivial) (by change VG.Impl.Dsa.Generation.Layout.g < 2 ^ 16; decide) (by taint_decide)).mono
  · intro s t ⟨p, ⟨mi, hs⟩, ⟨mj, ht⟩, hsp⟩
    have eq := generatorPower_inverse hs ht
    subst mj
    exact ⟨(p.powerCall mi, p.eb), ⟨generatorPower_call hs, rfl⟩, ⟨generatorPower_call ht, rfl⟩, hsp⟩
  · exact fun _ _ h => h

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Timing of fresh generator modulus setup -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Impl.Dsa.AArch64.Generation

def GeneratorModulusBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  Scr s p.B activeBytes ∧ s.gpr .x0 = p.B ∧
  Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.p) p.pb ∧ p.len = len

def GeneratorModulusParent (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  Good s p.B activeBytes outerWords 0 ∧
  Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.p) p.pb ∧ p.len = len

def GeneratorPlan.childCall (p : GeneratorPlan) : ChildPublic where
  x := (p.powerCall 0).x
  ptr := off p.B VG.Impl.Dsa.Generation.Layout.p
  len := p.len
  extent := (p.powerCall 0).extent
  offset := (p.powerCall 0).offsetBound
  lo := (p.powerCall 0).childLow
  hi := (p.powerCall 0).childHigh
  widthPositive := (p.powerCall 0).lower
  widthParent := (p.powerCall 0).fits
  widthBound := (p.powerCall 0).upper
  positive := (p.powerCall 0).outputPositive
  lengthBound := (p.powerCall 0).outputBound
  width := (p.powerCall 0).outputWidth

theorem generatorModulus_parent {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorModulusBefore len p s) :
    WP isa (.block SignVerify.parent) s (GeneratorModulusParent len p) := by
  refine WP.mono (parent_ok h.1 h.2.1 (by decide)) fun t ⟨hg, hf, hk⟩ => ?_
  have ff : Frm p.B [(48, 80)] s.mem t.mem := Frm.of_outside hf (by simp)
  exact ⟨hg, h.2.2.1.congrK (InScr.of_frm ff (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide)) hk, h.2.2.2⟩

theorem generatorModulus_fields {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorModulusParent len p s) :
    WP isa (.block (generatorFields len)) s
      (ChildPre ⟨.input .p, .pLen⟩ p.childCall) := by
  have hl : len < 2 ^ 16 := by have he := h.2.2; rcases p.width with hh | hh | hh <;> omega
  refine WP.mono (generatorFields_ok h.1 (by decide) hl)
    fun t ⟨hg, hp, _, hlen, _, hf, hk⟩ => ?_
  have ff : Frm p.B [(256, 80)] s.mem t.mem := Frm.of_outside hf (by simp)
  have src := h.2.1.congrK (InScr.of_frm ff (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide)) hk
  refine ⟨⟨0, hg⟩, p.pb, hp, ?_, src, p.pLength⟩
  change word t.mem p.B 328 = BitVec.ofNat 64 p.pb.length
  rw [p.pLength, h.2.2]; exact hlen

theorem generatorModulus_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorModulusBefore len)) (generatorModulus len) (fun _ _ => True) := by
  unfold generatorModulus
  simp only [seqs]
  refine RelCT.seq (two_post (two_map (fun p : GeneratorPlan => p.B) (fun _ _ h => h.2.1) parent_ct)
    (fun _ _ h => generatorModulus_parent h)) ?_
  have fields : RelCT isa (Two (GeneratorModulusParent len)) (.block (generatorFields len))
      (fun _ _ => True) := by
    apply two_map (Φ' := BasePublic) (fun p : GeneratorPlan => p.B) (fun _ _ h => h.1.x0)
    rcases hl with rfl | rfl | rfl
    all_goals exact two_taint [.x0] pins_base (by taint_decide)
  refine RelCT.seq (two_post fields (fun _ _ h => generatorModulus_fields h)) ?_
  exact two_map GeneratorPlan.childCall (fun _ _ h => ⟨h, rfl⟩)
    (child_ct ⟨.input .p, .pLen⟩ (by trivial) pWorkspace (by taint_decide))

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Compose fresh workspace initialization with generator exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Impl.Dsa.AArch64.Generation

structure GeneratorFreshBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop where
  modulus : GeneratorModulusBefore len p s
  base : word s.mem p.B 272 = p.hp
  hSource : Src s p.B activeBytes p.hp p.hb
  eSource : Src s p.B activeBytes (off p.B VG.Impl.Dsa.Generation.Layout.exponent) p.eb
  output : ∀ i < p.len, InRegions s.wr (off (off p.B VG.Impl.Dsa.Generation.Layout.g) i) 1

theorem generatorFresh_ready {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorFreshBefore len p s) :
    WP isa (generatorModulus len) s (GeneratorPowerBefore p) := by
  have step := generatorModulus_ok h.modulus.1 h.modulus.2.1 p.width p.pLength
    h.modulus.2.2.1 p.pOdd
  rw [h.modulus.2.2.2] at step
  refine WP.mono step fun t ⟨mi, hg, child, _, ep, plen, gh, ff, hk⟩ => ?_
  have bounds : ∀ r ∈ [(48, 80), (256, 80)] ++ initRanges pWorkspace (len / 8),
      r.1 + r.2 ≤ activeBytes := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, initRanges] at hr
    rcases hr with (rfl | rfl) | (rfl | rfl)
    · decide
    · decide
    · decide
    · rw [← h.modulus.2.2.2]
      rcases p.width with hh | hh | hh <;> rw [hh] <;> decide
  have child' : ChildReady t.mem p.B pWorkspace (p.len / 8) (Spec.Dsa.decodeBE p.pb) mi := by
    rw [h.modulus.2.2.2]; exact child
  have plen' : word t.mem p.B 328 = BitVec.ofNat 64 p.len := by
    rw [h.modulus.2.2.2]; exact plen
  exact ⟨mi, hg, child', gh.trans h.base, ep, plen',
    h.hSource.congrK (InScr.of_frm ff bounds) hk,
    h.eSource.congrK (InScr.of_frm ff bounds) hk,
    fun i hi => by rw [hk.wr]; exact h.output i hi⟩

theorem generatorPowerFresh_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorFreshBefore len)) (generatorPowerFresh M.mm len)
      (fun _ _ => True) := by
  unfold generatorPowerFresh
  exact RelCT.seq (two_post
    (two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.modulus) (generatorModulus_ct len hl))
    (fun _ _ h => generatorFresh_ready h)) (generatorPower_ct M)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Load the selected generator candidate from the persistent frame and evaluate it -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Bignum.AArch64 VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.Rsa.AArch64

def GeneratorBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  (∃ W, GeneratorMemory p W s) ∧ p.len = len

theorem generatorInput_ready {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (.block generatorInput) s (GeneratorFreshBefore len p) := by
  obtain ⟨W, hm⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (generatorInput_ok hm.layout R hm.base hm.input (hm.parent.st (d := 272) (by decide)))
    fun t ⟨hd, hp, hf, hk⟩ => ?_
  have ff : Frm p.B [(272, 8)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(272, 8)], r.1 + r.2 ≤ activeBytes := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide
  exact ⟨⟨hm.parent.congr hk.wr, hd,
      hm.pParent.congrK (InScr.of_frm ff bound) hk, h.2⟩, hp,
    hm.hParent.congrK (InScr.of_frm ff bound) hk,
    hm.eParent.congrK (InScr.of_frm ff bound) hk,
    fun i hi => by rw [hk.wr]; exact hm.gWrite i hi⟩

theorem generatorInput_ct (len : Nat) :
    RelCT isa (Two (GeneratorBefore len)) (.block generatorInput)
      (Two (GeneratorFreshBefore len)) := by
  unfold generatorInput
  apply RelCT.block_append (M := isa) (l₁ := [.ldrSp .x0 40, .ldrSp .x3 168])
    (l₂ := [.str .x .x3 .x0 Field.g.offset])
  apply pin_ct [] [.x0] (fun p : GeneratorPlan => fun _ => p.B)
    (by intro _ _ _ _ _ _ h; cases h) (by taint_decide) ?_ (by taint_decide) ?_
  · intro p s h
    obtain ⟨W, hm⟩ := h.1
    obtain ⟨V, R⟩ := hm.rep
    have hv : s.mem.readW (p.F + BitVec.ofNat 64 40) 64 = p.B := (R.fr 5 (by decide)).trans hm.base
    have step : WP isa (.block [.ldrSp .x0 40, .ldrSp .x3 168]) s (fun t => t.gpr .x0 = p.B) := by
      brun [exec_ldrSp (off := 40) (by decide), exec_ldrSp (off := 168) (by decide),
        hm.layout.sp, hm.layout.ld (d := 40) (n := 8) (by decide),
        hm.layout.ld (d := 168) (n := 8) (by decide), hv]
    exact WP.mono step fun t ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ht
  · intro p s h
    apply WP.seq_iff.mpr
    exact (WP.block_append_iff (M := isa)
      (l₁ := [.ldrSp .x0 40, .ldrSp .x3 168])
      (l₂ := [.str .x .x3 .x0 Field.g.offset])).mp (generatorInput_ready h)

theorem generatorEvaluate_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorEvaluate M.mm len)
      (fun _ _ => True) := by
  unfold generatorEvaluate
  exact RelCT.seq (generatorInput_ct len) (generatorPowerFresh_ct M len hl)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Instantiate range timing with the exact generator inputs and computed output -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.AArch64

def GeneratorPlan.rangeWorkspace (p : GeneratorPlan) (xb : List Byte) (hx : xb.length = p.len) :
    GeneratorWorkspacePublic where
  frame := {
    B := p.A, F := p.F, arena := p.B, hp := p.hp, Z := p.Z, w := p.len / 8
    width := by rcases p.width with h | h | h <;> omega_using [h]
    pb := p.pb, xb := xb
    pLength := by rw [p.pLength]; rcases p.width with h | h | h <;> rw [h] <;> decide
    xLength := hx.trans p.pLength.symm
    separate := p.frameHeaders }
  base := p.arithmeticBase.symm
  room := p.workspaceRoom
  lower := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  upper := by dsimp only; rcases p.width with h | h | h <;> rw [h] <;> decide
  outside := p.frameOutside

theorem generatorRange_plan {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    {xb : List Byte} (hx : xb.length = p.len) (result : Bool)
    (h : GeneratorMemory p W s)
    (src : Src s p.A p.Z (if result then VG.Proof.Bignum.off p.B g else p.hp) xb) :
    GeneratorWorkspaceBefore (p.len / 8) p.len result (p.rangeWorkspace xb hx) s := by
  obtain ⟨V, R⟩ := h.rep
  exact ⟨⟨h.layout.sp, fun k hk => h.layout.ld (d := 8 * k) (n := 8) (by unfold frameBytes; omega_using [hk]),
    (R.fr 5 (by decide)).trans h.base, (R.fr 21 (by decide)).trans h.input,
    h.pArithmetic, src, fun _ => p.pOdd⟩, h.arithmetic, rfl, p.pLength⟩

theorem generatorInputRange_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (Impl.Dsa.AArch64.Generation.generatorRangeFromFrame len false)
      (fun _ _ => True) := by
  apply two_map (fun p : GeneratorPlan => p.rangeWorkspace p.hb p.hLength) ?_
    (generatorRangeFromFrame_ct len false hl)
  intro p s ⟨⟨W, h⟩, he⟩
  have ready := generatorRange_plan p.hLength false h h.hArithmetic
  subst len
  exact ready

def GeneratorOutputBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value

theorem generatorOutput_source {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s)
    (hg : Spec.Rsa.bytesAt s.mem (VG.Proof.Bignum.off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) :
    Src s p.A p.Z (VG.Proof.Bignum.off p.B g) (Spec.Dsa.encodeBE p.len p.value) := by
  have hlen := VG.Proof.Dsa.encodeBE_length p.len p.value
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => p.gArithmeticOutside i (hlen ▸ hi)⟩
  · obtain ⟨r, hr, hc⟩ := h.gWrite i (hlen ▸ hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have eq := congrArg (fun bs : List Byte => bs[i]?) hg
    simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
      show i < p.len from hlen ▸ hi, ↓reduceIte, Option.map_some, List.getElem?_eq_getElem hi,
      Option.some.injEq] using eq

theorem generatorOutputRange_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorOutputBefore len)) (Impl.Dsa.AArch64.Generation.generatorRangeFromFrame len true)
      (fun _ _ => True) := by
  apply two_map (fun p : GeneratorPlan => p.rangeWorkspace (Spec.Dsa.encodeBE p.len p.value)
    (VG.Proof.Dsa.encodeBE_length p.len p.value)) ?_ (generatorRangeFromFrame_ct len true hl)
  intro p s ⟨⟨⟨W, h⟩, he⟩, hg⟩
  have ready := generatorRange_plan (VG.Proof.Dsa.encodeBE_length p.len p.value) true h
    (generatorOutput_source h hg)
  subst len
  exact ready

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Generator decisions branch on masks determined by public generation inputs -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation

def GeneratorMasked (len : Nat) (valid : GeneratorPlan → Bool) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ s.gpr .x3 = mask (valid p)

theorem generatorStatus_ct (len : Nat) (status : Nat) (hs : status = 1 ∨ status = 3) :
    RelCT isa (Two (GeneratorBefore len)) (.block (stackStatus status)) (fun _ _ => True) := by
  rcases hs with rfl | rfl <;>
    exact two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide)

def GeneratorPlan.inputValid (p : GeneratorPlan) : Bool :=
  decide (1 < Spec.Dsa.decodeBE p.hb ∧ Spec.Dsa.decodeBE p.hb < Spec.Dsa.decodeBE p.pb - 1)

def GeneratorPlan.outputValid (p : GeneratorPlan) : Bool := decide (1 < p.value)

theorem generatorInputRange_mask {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (generatorRangeFromFrame len false) s (GeneratorMasked len GeneratorPlan.inputValid p) := by
  obtain ⟨⟨W, h⟩, he⟩ := h
  have step := generatorInputRange_ok h
  rw [he] at step
  exact WP.mono step fun t ⟨hr, ht, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, hr⟩

theorem generatorOutputRange_mask {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorOutputBefore len p s) :
    WP isa (generatorRangeFromFrame len true) s (GeneratorMasked len GeneratorPlan.outputValid p) := by
  obtain ⟨⟨⟨W, h⟩, he⟩, hg⟩ := h
  have step := generatorOutputRange_ok h hg
  rw [he] at step
  exact WP.mono step fun t ⟨hr, ht, _, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, hr⟩

theorem generatorEvaluate_ready (M : Mont)  {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (generatorEvaluate M.mm len) s (GeneratorOutputBefore len p) := by
  obtain ⟨⟨W, h⟩, he⟩ := h
  have step := generatorEvaluateStage_ok M h
  rw [he] at step
  exact WP.mono step fun t ⟨hg, ht, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, by simpa only [he] using hg⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.GeneratorSearchCTState`, which this module and modules that import it used -/

section

/-! # Public cursor and exact chunk state of the generator search -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

structure GeneratorSearchPublic where
  plan : GeneratorSearchPlan
  used : Nat
  bound : used ≤ plan.tape.length

def GeneratorSearchBefore (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧ W 20 = BitVec.ofNat 64 p.used) ∧ p.plan.core.len = len

def GeneratorSearchPublic.exhausted (p : GeneratorSearchPublic) : Bool :=
  decide (p.plan.tape.length - p.used < p.plan.core.len)

def GeneratorSearchChecked (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ isa.eval (.nonzero .x .x0) s = some p.exhausted

def GeneratorSearchAvailable (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

def GeneratorSearchTaken (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧
    W 20 = BitVec.ofNat 64 (p.used + p.plan.core.len) ∧ W 21 = VG.Proof.Bignum.off p.plan.tapePtr p.used) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_check {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchBefore len p s) :
    WP isa (.block (chunkCheck generatorTape len)) s (GeneratorSearchChecked len p) := by
  obtain ⟨⟨W, hm, hu⟩, he⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : len < 65536 := by rcases p.plan.core.width with hh | hh | hh <;> omega
  refine WP.mono (chunkCheck_frame_ok hm.layout R generatorTape (by decide) (by decide)
    hl hu hm.tapeLength p.bound p.plan.tapeFits) fun t ⟨hc, hmem, hk⟩ => ?_
  exact ⟨⟨⟨W, generatorMemory_congr hm hmem (hk.mono (by decide)), hu⟩, he⟩,
    by
      simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hc, GeneratorSearchPublic.exhausted, he]
      by_cases room : len ≤ p.plan.tape.length - p.used
      · simp only [ite_eq_left room, decide_eq_false (show ¬ p.plan.tape.length - p.used < len by omega_using [room])]; rfl
      · simp only [ite_eq_right room, decide_eq_true (show p.plan.tape.length - p.used < len by omega_using [room])]; rfl⟩

theorem generatorSearch_available {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchChecked len p s) (hb : isa.eval (.nonzero .x .x0) s = some false) :
    GeneratorSearchAvailable len p s := by
  have he : p.exhausted = false := Option.some.inj (h.2.symm.trans hb)
  have hn := of_decide_eq_false he
  exact ⟨h.1, by have hb := p.bound; omega_using [hn, hb]⟩

theorem generatorSearch_take {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchAvailable len p s) :
    WP isa (.block (tapeTake generatorTape len)) s (GeneratorSearchTaken len p) := by
  obtain ⟨⟨⟨W, hm, hu⟩, he⟩, room⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : len < 65536 := by rcases p.plan.core.width with hh | hh | hh <;> omega
  refine WP.mono (chunkTake_ok hm.layout R generatorTape (by decide) (by decide)
    (by decide) (by decide) (by decide) hl hu) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.plan.core.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff kt.rd kt.wr
  refine ⟨⟨_, ht, ?_, ?_⟩, he, room⟩
  · simp only [generatorTape, upd, ↓reduceIte, he]
  · simp [generatorTape, upd, hm.tapeBase]

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! ### `Dsa.AArch64.Generation.GeneratorStepCT`, which only this module used -/

section

/-! # Timing of a complete generator attempt, including both retry decisions -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Impl.Bignum.AArch64

theorem generatorStep_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorStep M.mm len) (fun _ _ => True) := by
  unfold generatorStep
  refine RelCT.seq (two_post (generatorInputRange_ct len hl)
    (fun _ _ h => generatorInputRange_mask h))
    ?_
  refine two_ite (fun _ _ _ hs ht => (generatorTest_ok hs.2).trans (generatorTest_ok ht.2).symm) ?_ ?_
  · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
      (generatorStatus_ct len 3 (Or.inr rfl))
  · have body : RelCT isa (Two (GeneratorBefore len))
        (seqs [generatorEvaluate M.mm len, generatorRangeFromFrame len true,
          .ite (.zero .x .x3) (.block (stackStatus 3)) (.block (stackStatus 1))]) (fun _ _ => True) := by
      simp only [seqs]
      refine RelCT.seq (two_post (generatorEvaluate_ct M len hl)
        (fun _ _ h => generatorEvaluate_ready M h))
        (RelCT.seq (two_post (generatorOutputRange_ct len hl)
          (fun _ _ h => generatorOutputRange_mask h))
          ?_)
      refine two_ite (fun _ _ _ hs ht => (generatorTest_ok hs.2).trans (generatorTest_ok ht.2).symm) ?_ ?_
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 3 (Or.inr rfl))
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 1 (Or.inl rfl))
    exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1) body

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Public retry condition and strictly advancing generator tape cursor -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/Generation/GeneratorSearchBodyCT.lean`, which only this module imported.
section

/-! # A complete generator attempt preserves the tape and returns a public status -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def GeneratorSearchPublic.accepted (p : GeneratorSearchPublic) : Bool :=
  if room : p.used + p.plan.core.len ≤ p.plan.tape.length then decide (p.plan.chunk p.used room).accepts else false

def GeneratorSearchBodyAfter (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧
    W 20 = BitVec.ofNat 64 (p.used + p.plan.core.len) ∧ W 19 = if p.accepted then 1 else 3) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_body_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchTaken len)) (generatorStep M.mm len) (fun _ _ => True) := by
  apply (generatorStep_ct M len hl).mono
  · rintro s t ⟨p, ⟨⟨Ws, hs, _, ps⟩, he, room⟩, ⟨⟨Wt, ht, _, pt⟩, _, _⟩, hsp⟩
    exact ⟨p.plan.chunk p.used room, ⟨⟨Ws, hs.chunk room ps⟩, he⟩, ⟨⟨Wt, ht.chunk room pt⟩, he⟩, hsp⟩
  · exact fun _ _ h => h

theorem generatorSearch_body_ready (M : Mont)  {len : Nat}
    {p : GeneratorSearchPublic} {s : State} (h : GeneratorSearchTaken len p s) :
    WP isa (generatorStep M.mm len) s (GeneratorSearchBodyAfter len p) := by
  obtain ⟨⟨W, hm, hu, hp⟩, he, room⟩ := h
  have hc := hm.chunk room hp
  have step := generatorStep_ok M hc
  change WP isa (generatorStep M.mm p.plan.core.len) s _ at step
  rw [he] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have memory := hm.frame ht.layout ht.rep (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff hk.rd hk.wr
  refine ⟨⟨_, memory, ?_, ?_⟩, he, room⟩
  · simpa [upd] using hu
  · simp [upd, GeneratorSearchPublic.accepted, room]

end VG.Proof.Dsa.AArch64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def GeneratorSearchPublic.continues (p : GeneratorSearchPublic) : Bool := !p.exhausted && !p.accepted

def GeneratorSearchPublic.next (p : GeneratorSearchPublic) (hc : p.continues = true) : GeneratorSearchPublic where
  plan := p.plan
  used := p.used + p.plan.core.len
  bound := by
    have hn : p.exhausted = false := by
      cases he : p.exhausted <;> simp_all [continues]
    have hb := p.bound
    have h := of_decide_eq_false hn
    omega_using [hb, h]

def GeneratorSearchIterationAfter (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  isa.eval (.zero .x .x0) s = some p.continues ∧
    ∀ hc : p.continues = true, GeneratorSearchBefore len (p.next hc) s

theorem generatorSearch_status {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchBodyAfter len p s) :
    WP isa (.block tapeStatus) s (GeneratorSearchIterationAfter len p) := by
  obtain ⟨⟨W, hm, hu, hs⟩, he, room⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = false := by
    apply decide_eq_false
    omega_using [room]
  refine WP.mono (tapeStatus_ok hm.layout R) fun t ⟨hz, hmem, hk⟩ => ?_
  refine ⟨?_, fun hc => ⟨⟨W, generatorMemory_congr hm hmem (hk.mono (by decide)), hu⟩, he⟩⟩
  change eval (.zero .x .x0) t = some p.continues
  rw [hz]
  simp only [hs, GeneratorSearchPublic.continues, exhausted, Bool.not_false, Bool.true_and]
  cases p.accepted <;> rfl

theorem generatorSearch_exhausted {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchChecked len p s) (hb : isa.eval (.nonzero .x .x0) s = some true) :
    WP isa (.block ([VG.Impl.Bignum.AArch64.movi .x0 3] ++ Impl.Dsa.AArch64.Random.store 152 .x0 ++ [VG.Impl.Bignum.AArch64.movi .x0 1])) s
      (GeneratorSearchIterationAfter len p) := by
  obtain ⟨⟨W, hm, _⟩, _⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = true := Option.some.inj (h.2.symm.trans hb)
  have cont : p.continues = false := by simp [GeneratorSearchPublic.continues, exhausted]
  refine WP.mono (tapeExhausted_ok hm.layout R) fun t ⟨hz, _⟩ => ?_
  exact ⟨by simpa only [cont] using hz, fun hc => by rw [cont] at hc; contradiction⟩

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! A complete generator-tape iteration has a public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem generatorIteration_ct_of (M : Mont) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs []) (.block (chunkCheck generatorTape len)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs []) (.block (tapeTake generatorTape len)) hc₂).isSome = true) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  unfold tapeIteration
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht₁)
    (fun _ _ h => generatorSearch_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
      (fun _ _ h => generatorSearch_exhausted h.1 h.2)
  · have tail : RelCT isa (Two (GeneratorSearchAvailable len))
        (.seq (.block (tapeTake generatorTape len))
          (.seq (generatorStep M.mm len) (.block tapeStatus)))
        (Two (GeneratorSearchIterationAfter len)) := by
      refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) ht₂)
        (fun _ _ h => generatorSearch_take h))
        (RelCT.seq (two_post (generatorSearch_body_ct M len hl)
          (fun _ _ h => generatorSearch_body_ready M h)) ?_)
      exact two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
        (fun _ _ h => generatorSearch_status h)
    exact two_map (fun p : GeneratorSearchPublic => p)
      (fun _ _ h => generatorSearch_available h.1 h.2) tail

theorem generatorIteration_ct (M : Mont) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  rcases hl with rfl | rfl | rfl
  all_goals exact generatorIteration_ct_of M _ (by omega_using []) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Timing and termination of the complete generator tape search loop -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64.Generation

theorem generatorIteration_ready (M : Mont)  {len : Nat}
    {p : GeneratorSearchPublic} {s : State} (h : GeneratorSearchBefore len p s) :
    WP isa (tapeIteration generatorTape len (generatorStep M.mm len)) s
      (GeneratorSearchIterationAfter len p) := by
  unfold tapeIteration
  refine WP.seq (WP.mono (generatorSearch_check h) fun t ht => ?_)
  refine WP.ite p.exhausted ht.2 (fun he => generatorSearch_exhausted ht (ht.2.trans (congrArg some he))) ?_
  intro he
  have available := generatorSearch_available ht (ht.2.trans (congrArg some he))
  exact WP.seq (WP.mono (generatorSearch_take available) fun _ hv =>
    WP.seq (WP.mono (generatorSearch_body_ready M hv) fun _ hw => generatorSearch_status hw))

private def generatorLoopInv (len remaining : Nat) : State → State → Prop :=
  Two fun p s => p.plan.tape.length - p.used + 1 = remaining ∧ GeneratorSearchBefore len p s

private theorem generatorLoop_step (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (remaining : Nat) :
    RelCT isa (generatorLoopInv len remaining)
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (fun s t => isa.eval (.zero .x .x0) s = isa.eval (.zero .x .x0) t ∧ (isa.eval (.zero .x .x0) s = some false → True) ∧
        (isa.eval (.zero .x .x0) s = some true → ∃ next < remaining, generatorLoopInv len next s t)) := by
  have step : RelCT isa (generatorLoopInv len remaining)
      (tapeIteration generatorTape len (generatorStep M.mm len))
      (Two fun p s => p.plan.tape.length - p.used + 1 = remaining ∧ GeneratorSearchIterationAfter len p s) := by
    refine two_post ((generatorIteration_ct M len hl).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (generatorIteration_ready M h.2) fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩, hsp⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have room := (p.next cont).bound
  have positive : 0 < p.plan.core.len := by rcases p.plan.core.width with hh | hh | hh <;> omega_using [hh]
  refine ⟨p.plan.tape.length - (p.used + p.plan.core.len) + 1, ?_, p.next cont,
    ⟨rfl, hs.2 cont⟩, ⟨rfl, ht.2 cont⟩, hsp⟩
  change p.used + p.plan.core.len ≤ p.plan.tape.length at room
  omega_using [hr, positive, room]

theorem generatorLoop_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (.loop (tapeIteration generatorTape len (generatorStep M.mm len)) (.zero .x .x0)) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht, hsp⟩ es et
  exact RelCT.loop (generatorLoopInv len) (generatorLoop_step M len hl)
    (p.plan.tape.length - p.used + 1) s t a b s' t' ⟨p, ⟨rfl, hs⟩, ⟨rfl, ht⟩, hsp⟩ es et

end VG.Proof.Dsa.AArch64.Generation

end

end

/-! # Timing of complete native generator selection from an input tape -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.Generation VG.Proof.RsaOaep.AArch64 VG.Impl.RsaOaep.AArch64

def GeneratorSearchStart (len : Nat) (p : GeneratorSearchPlan) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p W s) ∧ p.core.len = len

def GeneratorSearchPlan.start (p : GeneratorSearchPlan) : GeneratorSearchPublic := ⟨p, 0, Nat.zero_le _⟩

theorem generatorSearch_reset {len : Nat} {p : GeneratorSearchPlan} {s : State}
    (h : GeneratorSearchStart len p s) :
    WP isa (.block (tapeReset generatorTape)) s (GeneratorSearchBefore len p.start) := by
  obtain ⟨⟨W, hm⟩, he⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (tapeReset_frame_ok hm.layout R generatorTape (by decide) (by decide))
    fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.core.changed s.mem t.mem := by
    intro a ha
    apply ft a
    right
    have hn := ha ⟨p.core.F, frameBytes⟩ (by simp [GeneratorPlan.changed])
    change ¬ ofs p.core.F a < frameBytes at hn
    change 168 ≤ ofs p.core.F a
    unfold frameBytes at hn
    omega_using [hn]
  refine ⟨⟨upd W 20 0, hm.frame Lt ⟨V, Rt⟩ ?_ ff kt.rd kt.wr, by simp [upd, GeneratorSearchPlan.start]⟩, he⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nativeGenerator_ct (M : Mont)  (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchStart len)) (generatorSearch M.mm len) (fun _ _ => True) := by
  unfold generatorSearch tapeLoop
  refine RelCT.seq (two_post (two_taint [] (by intro _ _ _ _ _ _ h; cases h) (by taint_decide))
    (fun _ _ h => generatorSearch_reset h)) ?_
  exact two_map GeneratorSearchPlan.start (fun _ _ h => h) (generatorLoop_ct M len hl)

end VG.Proof.Dsa.AArch64.Generation
