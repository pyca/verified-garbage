module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSearchPlanCT
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextGenerator
import VerifiedGarbage.Proof.Framework.Omega
public import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorSearch
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeIteration
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorSearch
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeIteration
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInvariant
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorSearchMemory
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorStep
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
public import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Parent
public import VerifiedGarbage.Proof.Dsa.X86_64.PublicFinishCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.X86_64.PublicFinishCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorPower
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CheckPrime
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
meta import VerifiedGarbage.Proof.Dsa.X86_64.RangeMask
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorRange
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedSearchPlanCT
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.GeneratorRange
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.CandidateArithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ArgumentBlocksCT
meta import VerifiedGarbage.Proof.RsaKeyGen.Table
meta import VerifiedGarbage.Proof.Dsa.Encoding
meta import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.GeneratorInvariant
meta import VerifiedGarbage.Impl.Dsa.X86_64.Generation.TapeLoop

/-! ### `Dsa.X86_64.Generation.NativeGeneratorCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorLoopCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorIterationCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorSearchTailCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorDecisionCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorRangePlanCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorWorkspaceCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorFrameCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorRangeCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorLoadsCT`, which this module and modules that import it used -/

section

/-! # Public-address loads for generator range checks -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

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
      left; simp only [slot, hdrBytes]; omega_using [hd]
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
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.X86_64.Generation.generatorLoadPair
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.generatorLoadPair
  refine RelCT.seq (two_post ?_ (fun _ _ h => generatorFirst_ready h)) ?_
  · exact two_map GeneratorLoadPublic.modulus (fun _ _ h => h.1)
      (loadCandidate_ct (by decide : 0 < 16) (by decide : 16 < 32)
        (by decide : 17 < 32) (by taint_decide) (by taint_decide))
  · exact two_map GeneratorLoadPublic.second (fun _ _ h => h)
      (loadCandidate_ct (by decide : 1 < 16) (by decide : 18 < 32)
        (by decide : 19 < 32) (by taint_decide) (by taint_decide))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of generator-input and generator-output range filtering -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

def GeneratorRangeBefore (p : GeneratorLoadPublic) (s : State) : Prop :=
  GeneratorLoadBefore p s ∧ Spec.Rsa.os2ip p.modulus.bytes % 2 = 1

def GeneratorRangeLoaded (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.Ws s p.B p.Z p.w ∧ wv s.mem p.B (slot p.w 0) p.w % 2 = 1

def GeneratorRangeWorkspace (p : LoadPublic) (s : State) : Prop :=
  VG.Proof.Rsa.X86_64.Ws s p.B p.Z p.w

theorem generatorRangeWorkspace_ct :
    RelCT isa (Two GeneratorRangeWorkspace) (Impl.Dsa.X86_64.Checks.rangeMask true)
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Checks.rangeMask seqs
  let addresses (p : LoadPublic) (s : State) : Prop :=
    s.gpr .r12 = BitVec.ofNat 64 p.w ∧
    s.gpr .rbx = off p.B (slot p.w Public.aX) ∧
    s.gpr .r10 = off p.B (slot p.w Public.aN)
  refine RelCT.seq (two_piece (Ψ := addresses) [.rdi] ?_ (by taint_decide) ?_) ?_
  · intro p s t hs ht r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact hs.rdi.trans ht.rdi.symm
  · intro p s h
    exact WP.mono (VG.Proof.Dsa.X86_64.rangeHead_ok h.good.1 h.good.2)
      fun _ ht => ⟨ht.1, ht.2.1, ht.2.2.1⟩
  · exact two_taint [.r12, .rbx, .r10] (fun p s t hs ht r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hs.1.trans ht.1.symm
      · exact hs.2.1.trans ht.2.1.symm
      · exact hs.2.2.trans ht.2.2.symm) (by taint_decide)

theorem generatorLoadPair_ready {p : GeneratorLoadPublic} {s : State}
    (h : GeneratorLoadBefore p s) :
    WP isa Impl.Dsa.X86_64.Generation.generatorLoadPair s fun t =>
      VG.Proof.Rsa.X86_64.Ws t p.modulus.B p.modulus.Z p.modulus.w ∧
      wv t.mem p.modulus.B (slot p.modulus.w 0) p.modulus.w = Spec.Rsa.os2ip p.modulus.bytes :=
  WP.mono (generatorLoadPair_ok h.1.ws h.1.pointer h.1.length h.2.pointer h.2.length
    h.1.source h.2.source h.1.positive h.1.fits h.2.positive h.2.fits)
    (fun _ h => ⟨h.1, h.2.1⟩)

theorem generatorDecrement_ct :
    RelCT isa (Two GeneratorRangeLoaded) (.block (decA 0))
      (Two GeneratorRangeWorkspace) := by
  unfold decA
  simp only [List.append_assoc]
  exact ws_block_ct LoadPublic.B LoadPublic.Z LoadPublic.w (fun _ _ h => h.1)
    (by taint_decide) (fun _ _ h => WP.mono
      (decrementOdd_ok h.1 (by decide : 0 < 16) h.2) fun _ ht => ht.1)

theorem generatorRange_ct :
    RelCT isa (Two GeneratorRangeBefore) Impl.Dsa.X86_64.Generation.generatorRange
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.generatorRange
  refine RelCT.seq (two_post (generatorLoadPair_ct.mono
    (fun _ _ ⟨p, hs, ht⟩ => ⟨p, hs.1, ht.1⟩) (fun _ _ h => h))
    (fun p s h => WP.mono (generatorLoadPair_ready h.1) fun t ht =>
      show GeneratorRangeLoaded p.modulus t from ⟨ht.1, ht.2 ▸ h.2⟩)) ?_
  exact RelCT.seq (two_map GeneratorLoadPublic.modulus (fun _ _ h => h) generatorDecrement_ct)
    generatorRangeWorkspace_ct

theorem generatorResult_ct :
    RelCT isa (Two GeneratorLoadBefore) Impl.Dsa.X86_64.Generation.generatorResult
      (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.generatorResult
  refine RelCT.seq (two_post generatorLoadPair_ct
    (fun p s h => WP.mono (generatorLoadPair_ready h) fun _ ht =>
      show GeneratorRangeWorkspace p.modulus _ from ht.1)) ?_
  exact two_map GeneratorLoadPublic.modulus
    (fun _ _ h => h) generatorRangeWorkspace_ct

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Bind public generator inputs through the persistent frame -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.Generation.Layout

structure GeneratorFramePublic where
  B : Addr
  F : Addr
  arena : Addr
  hp : Addr
  Z : Nat
  w : Nat
  pb : List Byte
  xb : List Byte
  pLength : pb.length = 8 * w
  xLength : xb.length = pb.length
  separate : ∀ k < 37, ∀ j < 32, Mem.Sep (off F (8 * k)) 8 (off B (8 * j)) 8

def GeneratorFramePublic.loads (c : GeneratorFramePublic) (result : Bool) : GeneratorLoadPublic :=
  ⟨⟨c.B, c.Z, c.w, off c.arena p, c.pb⟩, if result then off c.arena g else c.hp, c.xb⟩

def GeneratorFramePublic.pointers (c : GeneratorFramePublic) : ArgumentPointers := ⟨c.B, c.F⟩

structure GeneratorFrameInputs (result : Bool) (c : GeneratorFramePublic) (s : State) : Prop where
  stack : s.gpr .rsp = c.F
  read : ∀ k < 37, InRegions (s.rd ++ s.wr) (off c.F (8 * k)) 8
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
  have hl : len < 2 ^ 31 := by omega_using [h.2.1.w2, c.pLength, h.2.2]
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
    {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (generatorRangeArguments len result))) hc).isSome = true) :
    RelCT isa (Two (GeneratorFrameBefore len result))
      (.seq (.block (headerArguments (generatorRangeArguments len result)))
        (if result then generatorResult else generatorRange)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map GeneratorFramePublic.pointers
    (fun _ _ h => ⟨h.2.1.rdi, h.1.stack⟩)
    (two_taint [.rdi, .rsp] argumentRegisters_pins ht))
    (fun _ _ h => generatorFrame_ready h)) ?_
  cases result
  · exact two_map (fun c : GeneratorFramePublic => c.loads false)
      (fun _ _ h => ⟨h.1, h.2 rfl⟩) generatorRange_ct
  · exact two_map (fun c : GeneratorFramePublic => c.loads true)
      (fun _ _ h => h.1) generatorResult_ct

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Initialize generator range-check scratch while retaining source bytes and frame arguments -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Rsa VG.Proof.Rsa.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Dsa.Generation.Layout

structure GeneratorWorkspacePublic where
  frame : GeneratorFramePublic
  base : frame.B = off frame.arena arithmetic
  room : slot frame.w 16 ≤ frame.Z
  lower : 2 ≤ frame.w
  upper : frame.w < 2 ^ 24
  outside : ∀ k < 37, ∀ i < 8, frame.Z ≤ ofs frame.B (off (off frame.F (8 * k)) i)

def GeneratorWorkspaceBefore (w len : Nat) (result : Bool) (c : GeneratorWorkspacePublic) (s : State) : Prop :=
  GeneratorFrameInputs result c.frame s ∧ Scr s c.frame.B c.frame.Z ∧
    c.frame.w = w ∧ c.frame.pb.length = len

def GeneratorWorkspaceBase (w len : Nat) (result : Bool) (c : GeneratorWorkspacePublic) (s : State) : Prop :=
  GeneratorWorkspaceBefore w len result c s ∧ s.gpr .rdi = c.frame.B

theorem generatorWorkspace_base {w len : Nat} {result : Bool} {c : GeneratorWorkspacePublic} {s : State}
    (h : GeneratorWorkspaceBefore w len result c s) :
    WP isa (.block workspaceBase) s (GeneratorWorkspaceBase w len result c) := by
  have ld := h.1.read 5 (by decide)
  have hv : s.mem.readW (off c.frame.F 40) 64 = c.frame.arena := h.1.arena
  have step : WP isa (.block workspaceBase) s fun t => t.gpr .rdi = c.frame.B ∧ t.mem = s.mem := by
    xrun [workspaceBase, VG.Proof.RsaOaep.X86_64.ea_sp, h.1.stack, ld, hv,
      sx_ofNat (by decide : arithmetic < 2 ^ 31)]
    exact c.base.symm
  refine WP.mono (WP.keep [.rdi] step rfl) fun t ⟨⟨hb, hm⟩, hk⟩ => ?_
  refine ⟨⟨?_, h.2.1.congr hk.2.2, h.2.2⟩, hb⟩
  exact ⟨(hk.gpr (by decide)).trans h.1.stack,
    (fun k hk' => by rw [hk.2.1, hk.2.2]; exact h.1.read k hk'),
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
  have bound : ∀ r ∈ [(48, 80), (224, 8)], r.1 + r.2 ≤ c.frame.Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only <;> omega_using [hz]
  have ht' : Ws t c.frame.B c.frame.Z c.frame.w := by rw [h.1.2.2.1]; exact ht
  refine ⟨?_, ht', h.1.2.2.2⟩
  refine ⟨(hk.gpr (by decide)).trans h.1.1.stack, ?_, ?_, ?_,
    h.1.1.modulus.congrK (InScr.of_frm ff bound) hk, h.1.1.source.congrK (InScr.of_frm ff bound) hk, h.1.1.odd⟩
  · intro k hk'; rw [hk.2.1, hk.2.2]; exact h.1.1.read k hk'
  · exact (frame_word_of_workspace ff bound (c.outside 5 (by decide))).trans h.1.1.arena
  · exact (frame_word_of_workspace ff bound (c.outside 21 (by decide))).trans h.1.1.candidate

theorem generatorRangeFromFrame_ct_of (w len : Nat) (result : Bool) {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rdi]) (workspace w) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rdi, .rsp])
      (.block (headerArguments (generatorRangeArguments len result))) hc₂).isSome = true) :
    RelCT isa (Two (GeneratorWorkspaceBefore w len result))
      (seqs [.block workspaceBase, workspace w, (.seq (.block (headerArguments (generatorRangeArguments len result)))
        (if result then generatorResult else generatorRange))]) (fun _ _ => True) := by
  simp only [seqs]
  refine RelCT.seq (two_post (two_taint [.rsp] ?_ (by taint_decide))
    (fun _ _ h => generatorWorkspace_base h))
    (RelCT.seq (two_post (two_taint [.rdi] ?_ ht₁)
      (fun _ _ h => generatorWorkspace_ready h)) ?_)
  · intro c s t hs ht r hr
    simp only [List.mem_singleton] at hr; subst r
    exact hs.1.stack.trans ht.1.stack.symm
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

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorEvaluateCT`, which this module and modules that import it used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorFreshCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorModulusCT`, which only this module used -/

section

/-! ### `Dsa.X86_64.Generation.GeneratorPowerCT`, which only this module used -/

section

/-! # Generator exponentiation reuses the verified public-power timing proof -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64

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
  have ls : (word s.mem (off p.B pWorkspace) (slot (p.len / 8) Public.aN)).toNat =
      Spec.Dsa.decodeBE p.pb % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.len / 8) _ _ _ positive, hs.child.modulus]
  have lt : (word t.mem (off p.B pWorkspace) (slot (p.len / 8) Public.aN)).toNat =
      Spec.Dsa.decodeBE p.pb % 2 ^ 64 := by
    rw [← wv_mod64 (n := p.len / 8) _ _ _ positive, ht.child.modulus]
  have hi := hs.child.inverse
  have hj := ht.child.inverse
  rw [ls] at hi
  rw [lt] at hj
  exact minv_unique (by rw [Nat.mod_mod_of_dvd _ (by decide)]; exact p.pOdd) hi hj

theorem generatorPower_ct (M : Mont) (Sq : MontS) :
    RelCT isa (Two GeneratorPowerBefore) (Impl.Dsa.X86_64.Generation.generatorPower Sq.mm M.mm)
      (fun _ _ => True) := by
  apply (PublicPower.corePublicPow_ct M Sq (a := ⟨.input .g, .pLen⟩)
    (b := ⟨.input .x, .pLen⟩) (output := ⟨.local VG.Impl.Dsa.Generation.Layout.g, .pLen⟩)
    (o := pWorkspace) (by trivial) (by trivial) (by change VG.Impl.Dsa.Generation.Layout.g < 2 ^ 31; decide) (by taint_decide)).mono
  · intro s t ⟨p, ⟨mi, hs⟩, ⟨mj, ht⟩⟩
    have eq := generatorPower_inverse hs ht
    subst mj
    exact ⟨(p.powerCall mi, p.eb), ⟨generatorPower_call hs, rfl⟩, ⟨generatorPower_call ht, rfl⟩⟩
  · exact fun _ _ h => h

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of fresh generator modulus setup -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.Generation

def GeneratorModulusBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  Scr s p.B activeBytes ∧ s.gpr .rdi = p.B ∧
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
  have hl : len < 2 ^ 32 := by have he := h.2.2; rcases p.width with hh | hh | hh <;> omega
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
  refine RelCT.seq (two_post (two_map GeneratorPlan.B (fun _ _ h => h.2.1) parent_ct)
    (fun _ _ h => generatorModulus_parent h)) ?_
  have fields : RelCT isa (Two (GeneratorModulusParent len)) (.block (generatorFields len))
      (fun _ _ => True) := by
    apply two_map (Φ' := BasePublic) GeneratorPlan.B (fun _ _ h => h.1.rdi)
    rcases hl with rfl | rfl | rfl
    all_goals exact two_taint [.rdi] pins_base (by taint_decide)
  refine RelCT.seq (two_post fields (fun _ _ h => generatorModulus_fields h)) ?_
  exact two_map GeneratorPlan.childCall (fun _ _ h => ⟨h, rfl⟩)
    (child_ct ⟨.input .p, .pLen⟩ (by trivial) pWorkspace (by taint_decide))

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Compose fresh workspace initialization with generator exponentiation -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.Generation

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
    fun i hi => by rw [hk.2.2]; exact h.output i hi⟩

theorem generatorPowerFresh_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorFreshBefore len)) (generatorPowerFresh Sq.mm M.mm len)
      (fun _ _ => True) := by
  unfold generatorPowerFresh
  exact RelCT.seq (two_post
    (two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.modulus) (generatorModulus_ct len hl))
    (fun _ _ h => generatorFresh_ready h)) (generatorPower_ct M Sq)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Load the selected generator candidate from the persistent frame and evaluate it -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.Rsa.X86_64

def GeneratorBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  (∃ W, GeneratorMemory p W s) ∧ p.len = len

theorem generatorInput_ready {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (.block generatorInput) s (GeneratorFreshBefore len p) := by
  obtain ⟨W, hm⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (generatorInput_ok hm.layout R hm.base hm.input (hm.parent.st (by decide)))
    fun t ⟨hd, hp, hf, hk⟩ => ?_
  have ff : Frm p.B [(272, 8)] s.mem t.mem := Frm.of_outside hf (by simp)
  have bound : ∀ r ∈ [(272, 8)], r.1 + r.2 ≤ activeBytes := by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; decide
  exact ⟨⟨hm.parent.congr hk.2.2, hd,
      hm.pParent.congrK (InScr.of_frm ff bound) hk, h.2⟩, hp,
    hm.hParent.congrK (InScr.of_frm ff bound) hk,
    hm.eParent.congrK (InScr.of_frm ff bound) hk,
    fun i hi => by rw [hk.2.2]; exact hm.gWrite i hi⟩

theorem generatorInput_ct (len : Nat) :
    RelCT isa (Two (GeneratorBefore len)) (.block generatorInput)
      (Two (GeneratorFreshBefore len)) := by
  unfold generatorInput
  apply RelCT.block_append (M := isa) (l₁ := [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 40)), .mov .rax (.mem (Impl.Mgf1.X86_64.sp 168))])
    (l₂ := [.store (Core.field .g) .rax])
  apply pin_ct [.rsp] [.rdi] (fun p _ => p.B) ?_ (by taint_decide) ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain ⟨Ws, hs⟩ := hs.1
    obtain ⟨Wt, ht⟩ := ht.1
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · intro p s h
    obtain ⟨W, hm⟩ := h.1
    obtain ⟨V, R⟩ := hm.rep
    have ld := hm.layout.ld (d := 40) (by decide)
    have ld168 := hm.layout.ld (d := 168) (by decide)
    have hv := R.slot (d := 40) (k := 5) rfl (by decide) hm.base
    have step : WP isa (.block [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 40)), .mov .rax (.mem (Impl.Mgf1.X86_64.sp 168))]) s
        (fun t => t.gpr .rdi = p.B) := by
      xrun [VG.Proof.RsaOaep.X86_64.ea_sp, hm.layout.rsp, ld, ld168, hv]
    exact WP.mono step fun t ht r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact ht
  · intro p s h
    apply WP.seq_iff.mpr
    exact (WP.block_append_iff (M := isa)
      (l₁ := [.mov .rdi (.mem (Impl.Mgf1.X86_64.sp 40)), .mov .rax (.mem (Impl.Mgf1.X86_64.sp 168))])
      (l₂ := [.store (Core.field .g) .rax])).mp (generatorInput_ready h)

theorem generatorEvaluate_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorEvaluate Sq.mm M.mm len)
      (fun _ _ => True) := by
  unfold generatorEvaluate
  exact RelCT.seq (generatorInput_ct len) (generatorPowerFresh_ct M Sq len hl)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Instantiate range timing with the exact generator inputs and computed output -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.Generation.Layout VG.Impl.RsaOaep.X86_64

def GeneratorPlan.rangeWorkspace (p : GeneratorPlan) (xb : List Byte) (hx : xb.length = p.len) :
    GeneratorWorkspacePublic where
  frame := {
    B := p.A, F := p.F, arena := p.B, hp := p.hp, Z := p.Z, w := p.len / 8
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
    (src : Src s p.A p.Z (if result then off p.B g else p.hp) xb) :
    GeneratorWorkspaceBefore (p.len / 8) p.len result (p.rangeWorkspace xb hx) s := by
  obtain ⟨V, R⟩ := h.rep
  exact ⟨⟨h.layout.rsp, fun k hk => h.layout.ld (by unfold frameBytes; omega_using [hk]),
    (R.fr 5 (by decide)).trans h.base, (R.fr 21 (by decide)).trans h.input,
    h.pArithmetic, src, fun _ => p.pOdd⟩, h.arithmetic, rfl, p.pLength⟩

theorem generatorInputRange_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame len false)
      (fun _ _ => True) := by
  apply two_map (fun p : GeneratorPlan => p.rangeWorkspace p.hb p.hLength) ?_
    (generatorRangeFromFrame_ct len false hl)
  intro p s ⟨⟨W, h⟩, he⟩
  have ready := generatorRange_plan p.hLength false h h.hArithmetic
  subst len
  exact ready

def GeneratorOutputBefore (len : Nat) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ Spec.Rsa.bytesAt s.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value

theorem generatorOutput_source {p : GeneratorPlan} {W : Nat → BitVec 64} {s : State}
    (h : GeneratorMemory p W s)
    (hg : Spec.Rsa.bytesAt s.mem (off p.B g) p.len = Spec.Dsa.encodeBE p.len p.value) :
    Src s p.A p.Z (off p.B g) (Spec.Dsa.encodeBE p.len p.value) := by
  have hlen := VG.Proof.Dsa.encodeBE_length p.len p.value
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => p.gArithmeticOutside i (hlen ▸ hi)⟩
  · obtain ⟨r, hr, hc⟩ := h.gWrite i (hlen ▸ hi)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · have eq := congrArg (fun bs : List Byte => bs[i]?) hg
    simpa only [Spec.Rsa.bytesAt, List.getElem?_map, List.getElem?_range,
      show i < p.len from hlen ▸ hi, ↓reduceIte, Option.map_some, List.getElem?_eq_getElem hi,
      Option.some.injEq] using eq

theorem generatorOutputRange_ct (len : Nat) (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorOutputBefore len)) (Impl.Dsa.X86_64.Generation.generatorRangeFromFrame len true)
      (fun _ _ => True) := by
  apply two_map (fun p : GeneratorPlan => p.rangeWorkspace (Spec.Dsa.encodeBE p.len p.value)
    (VG.Proof.Dsa.encodeBE_length p.len p.value)) ?_ (generatorRangeFromFrame_ct len true hl)
  intro p s ⟨⟨⟨W, h⟩, he⟩, hg⟩
  have ready := generatorRange_plan (VG.Proof.Dsa.encodeBE_length p.len p.value) true h
    (generatorOutput_source h hg)
  subst len
  exact ready

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Generator decisions branch on masks determined by public generation inputs -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation

def GeneratorMasked (len : Nat) (valid : GeneratorPlan → Bool) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ s.gpr .rax = mask (valid p)

def GeneratorDecided (len : Nat) (valid : GeneratorPlan → Bool) (p : GeneratorPlan) (s : State) : Prop :=
  GeneratorBefore len p s ∧ isa.eval .e s = !(valid p)

theorem generatorTest_ct (len : Nat) (valid : GeneratorPlan → Bool) :
    RelCT isa (Two (GeneratorMasked len valid)) (.block [.alu .test .rax (.reg .rax)])
      (Two (GeneratorDecided len valid)) := by
  refine two_piece [.rax] ?_ (by taint_decide) ?_
  · intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.2.trans ht.2.symm
  · intro p s ⟨⟨⟨W, h⟩, he⟩, hr⟩
    refine WP.mono (generatorTest_ok h hr) fun t ⟨hz, ht, _, _⟩ => ?_
    exact ⟨⟨⟨W, ht⟩, he⟩, by simp only [eval, hz]⟩

theorem generatorStatus_ct (len : Nat) (status : Nat) (hs : status = 1 ∨ status = 3) :
    RelCT isa (Two (GeneratorBefore len)) (.block (stackStatus status)) (fun _ _ => True) := by
  have pins : Pins (GeneratorBefore len) [.rsp] := by
    intro p s t ⟨⟨Ws, hs⟩, _⟩ ⟨⟨Wt, ht⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  rcases hs with rfl | rfl <;> exact two_taint [.rsp] pins (by taint_decide)

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

theorem generatorEvaluate_ready (M : Mont) (Sq : MontS) {len : Nat} {p : GeneratorPlan} {s : State}
    (h : GeneratorBefore len p s) :
    WP isa (generatorEvaluate Sq.mm M.mm len) s (GeneratorOutputBefore len p) := by
  obtain ⟨⟨W, h⟩, he⟩ := h
  have step := generatorEvaluateStage_ok M Sq h
  rw [he] at step
  exact WP.mono step fun t ⟨hg, ht, _, _⟩ => ⟨⟨⟨W, ht⟩, he⟩, by simpa only [he] using hg⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! ### `Dsa.X86_64.Generation.GeneratorSearchCTState`, which this module and modules that import it used -/

section

/-! # Public cursor and exact chunk state of the generator search -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

structure GeneratorSearchPublic where
  plan : GeneratorSearchPlan
  used : Nat
  bound : used ≤ plan.tape.length

def GeneratorSearchBefore (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧ W 20 = BitVec.ofNat 64 p.used) ∧ p.plan.core.len = len

def GeneratorSearchPublic.exhausted (p : GeneratorSearchPublic) : Bool :=
  decide (p.plan.tape.length - p.used < p.plan.core.len)

def GeneratorSearchChecked (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ isa.eval .b s = some p.exhausted

def GeneratorSearchAvailable (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  GeneratorSearchBefore len p s ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

def GeneratorSearchTaken (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧
    W 20 = BitVec.ofNat 64 (p.used + p.plan.core.len) ∧ W 21 = off p.plan.tapePtr p.used) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_check {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchBefore len p s) :
    WP isa (.block (chunkCheck generatorTape len)) s (GeneratorSearchChecked len p) := by
  obtain ⟨⟨W, hm, hu⟩, he⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : len < 2 ^ 31 := by rcases p.plan.core.width with hh | hh | hh <;> omega
  refine WP.mono (chunkCheck_ok hm.layout R generatorTape (by decide) (by decide)
    hl hu hm.tapeLength p.bound p.plan.tapeFits) fun t ⟨hc, hmem, hk⟩ => ?_
  exact ⟨⟨⟨W, generatorMemory_congr hm hmem hk, hu⟩, he⟩,
    by simp only [eval, hc, GeneratorSearchPublic.exhausted, he]⟩

theorem generatorSearch_available {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchChecked len p s) (hb : isa.eval .b s = some false) :
    GeneratorSearchAvailable len p s := by
  have he : p.exhausted = false := Option.some.inj (h.2.symm.trans hb)
  have hn := of_decide_eq_false he
  exact ⟨h.1, by have hb := p.bound; omega_using [hn, hb]⟩

theorem generatorSearch_take {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchAvailable len p s) :
    WP isa (.block (tapeTake generatorTape len)) s (GeneratorSearchTaken len p) := by
  obtain ⟨⟨⟨W, hm, hu⟩, he⟩, room⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  have hl : len < 2 ^ 31 := by rcases p.plan.core.width with hh | hh | hh <;> omega
  refine WP.mono (chunkTake_ok hm.layout R generatorTape (by decide) (by decide)
    (by decide) (by decide) (by decide) hl hu) fun t ⟨Lt, Rt, ft, kt⟩ => ?_
  have ff : Frame p.plan.core.changed s.mem t.mem := ft.mono (by
    intro r hr; rcases List.mem_singleton.mp hr with rfl; simp [GeneratorPlan.changed])
  have ht := hm.frame Lt ⟨V, Rt⟩ (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff kt.2.1 kt.2.2
  refine ⟨⟨_, ht, ?_, ?_⟩, he, room⟩
  · simp only [generatorTape, upd, ↓reduceIte, he]
  · simp [generatorTape, upd, hm.tapeBase]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Public retry condition and strictly advancing generator tape cursor -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorStepCT.lean`, which only this module imported.
section

/-! # Timing of a complete generator attempt, including both retry decisions -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Impl.Bignum.X86_64

theorem generatorStep_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorBefore len)) (generatorStep Sq.mm M.mm len) (fun _ _ => True) := by
  unfold generatorStep
  refine RelCT.seq (two_post (generatorInputRange_ct len hl)
    (fun _ _ h => generatorInputRange_mask h))
    (RelCT.seq (generatorTest_ct len GeneratorPlan.inputValid) ?_)
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
      (generatorStatus_ct len 3 (Or.inr rfl))
  · have body : RelCT isa (Two (GeneratorBefore len))
        (seqs [generatorEvaluate Sq.mm M.mm len, generatorRangeFromFrame len true,
          .block [.alu .test .rax (.reg .rax)],
          .ite .e (.block (stackStatus 3)) (.block (stackStatus 1))]) (fun _ _ => True) := by
      simp only [seqs]
      refine RelCT.seq (two_post (generatorEvaluate_ct M Sq len hl)
        (fun _ _ h => generatorEvaluate_ready M Sq h))
        (RelCT.seq (two_post (generatorOutputRange_ct len hl)
          (fun _ _ h => generatorOutputRange_mask h))
          (RelCT.seq (generatorTest_ct len GeneratorPlan.outputValid) ?_))
      refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 3 (Or.inr rfl))
      · exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1)
          (generatorStatus_ct len 1 (Or.inl rfl))
    exact two_map (fun p : GeneratorPlan => p) (fun _ _ h => h.1.1) body

end VG.Proof.Dsa.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/GeneratorSearchBodyCT.lean`, which only this module imported.
section

/-! # A complete generator attempt preserves the tape and returns a public status -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def GeneratorSearchPublic.accepted (p : GeneratorSearchPublic) : Bool :=
  if room : p.used + p.plan.core.len ≤ p.plan.tape.length then decide (p.plan.chunk p.used room).accepts else false

def GeneratorSearchBodyAfter (len : Nat) (p : GeneratorSearchPublic) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p.plan W s ∧
    W 20 = BitVec.ofNat 64 (p.used + p.plan.core.len) ∧ W 19 = if p.accepted then 1 else 3) ∧
    p.plan.core.len = len ∧ p.used + p.plan.core.len ≤ p.plan.tape.length

theorem generatorSearch_body_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchTaken len)) (generatorStep Sq.mm M.mm len) (fun _ _ => True) := by
  apply (generatorStep_ct M Sq len hl).mono
  · rintro s t ⟨p, ⟨⟨Ws, hs, _, ps⟩, he, room⟩, ⟨⟨Wt, ht, _, pt⟩, _, _⟩⟩
    exact ⟨p.plan.chunk p.used room, ⟨⟨Ws, hs.chunk room ps⟩, he⟩, ⟨⟨Wt, ht.chunk room pt⟩, he⟩⟩
  · exact fun _ _ h => h

theorem generatorSearch_body_ready (M : Mont) (Sq : MontS) {len : Nat}
    {p : GeneratorSearchPublic} {s : State} (h : GeneratorSearchTaken len p s) :
    WP isa (generatorStep Sq.mm M.mm len) s (GeneratorSearchBodyAfter len p) := by
  obtain ⟨⟨W, hm, hu, hp⟩, he, room⟩ := h
  have hc := hm.chunk room hp
  have step := generatorStep_ok M Sq hc
  change WP isa (generatorStep Sq.mm M.mm p.plan.core.len) s _ at step
  rw [he] at step
  refine WP.mono step fun t ⟨ht, _, ff, hk⟩ => ?_
  have memory := hm.frame ht.layout ht.rep (by
    intro k hk
    simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    ff hk.2.1 hk.2.2
  refine ⟨⟨_, memory, ?_, ?_⟩, he, room⟩
  · simpa [upd] using hu
  · simp [upd, GeneratorSearchPublic.accepted, room]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

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
  isa.eval .e s = some p.continues ∧
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
  simp only [eval, hz, hs, GeneratorSearchPublic.continues, exhausted, Bool.not_false, Bool.true_and]
  cases p.accepted <;> rfl

theorem generatorSearch_exhausted {len : Nat} {p : GeneratorSearchPublic} {s : State}
    (h : GeneratorSearchChecked len p s) (hb : isa.eval .b s = some true) :
    WP isa (.block (stackStatus 3 ++ ([.mov32 .rax (.imm 1), .alu .test .rax (.reg .rax)] : List Instr))) s
      (GeneratorSearchIterationAfter len p) := by
  obtain ⟨⟨W, hm, _⟩, _⟩ := h.1
  obtain ⟨V, R⟩ := hm.rep
  have exhausted : p.exhausted = true := Option.some.inj (h.2.symm.trans hb)
  have cont : p.continues = false := by simp [GeneratorSearchPublic.continues, exhausted]
  refine WP.mono (tapeExhausted_ok hm.layout R) fun t ⟨hz, _⟩ => ?_
  exact ⟨by simp only [eval, hz, cont], fun hc => by rw [cont] at hc; contradiction⟩

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of a complete generator tape iteration -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem generatorSearch_before_pins (len : Nat) : Pins (GeneratorSearchBefore len) [.rsp] := by
  intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
  obtain rfl := List.mem_singleton.mp hr
  exact hs.layout.rsp.trans ht.layout.rsp.symm

theorem generatorIteration_ct_of (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.rsp]) (.block (chunkCheck generatorTape len)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.rsp]) (.block (tapeTake generatorTape len)) hc₂).isSome = true) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  unfold tapeIteration
  refine RelCT.seq (two_piece [.rsp] (generatorSearch_before_pins len) ht₁
    (fun _ _ h => generatorSearch_check h)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => generatorSearch_exhausted h.1 h.2)
    intro p s t hs ht r hr
    exact generatorSearch_before_pins len p s t hs.1.1 ht.1.1 r hr
  · have tail : RelCT isa (Two (GeneratorSearchAvailable len))
        (.seq (.block (tapeTake generatorTape len))
          (.seq (generatorStep Sq.mm M.mm len) (.block tapeStatus)))
        (Two (GeneratorSearchIterationAfter len)) := by
      refine RelCT.seq (two_piece [.rsp] ?_ ht₂ (fun _ _ h => generatorSearch_take h))
        (RelCT.seq (two_post (generatorSearch_body_ct M Sq len hl)
          (fun _ _ h => generatorSearch_body_ready M Sq h)) ?_)
      · intro p s t hs ht r hr
        exact generatorSearch_before_pins len p s t hs.1 ht.1 r hr
      · refine two_piece [.rsp] ?_ (by taint_decide) (fun _ _ h => generatorSearch_status h)
        intro p s t ⟨⟨Ws, hs, _⟩, _⟩ ⟨⟨Wt, ht, _⟩, _⟩ r hr
        obtain rfl := List.mem_singleton.mp hr
        exact hs.layout.rsp.trans ht.layout.rsp.symm
    exact two_map (fun p : GeneratorSearchPublic => p)
      (fun _ _ h => generatorSearch_available h.1 h.2) tail

theorem generatorIteration_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len))
      (Two (GeneratorSearchIterationAfter len)) := by
  rcases hl with rfl | rfl | rfl
  all_goals
    exact generatorIteration_ct_of M Sq _ (by omega_using []) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing and termination of the complete generator tape search loop -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.X86_64.Generation

theorem generatorIteration_ready (M : Mont) (Sq : MontS) {len : Nat}
    {p : GeneratorSearchPublic} {s : State} (h : GeneratorSearchBefore len p s) :
    WP isa (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len)) s
      (GeneratorSearchIterationAfter len p) := by
  unfold tapeIteration
  refine WP.seq (WP.mono (generatorSearch_check h) fun t ht => ?_)
  refine WP.ite p.exhausted ht.2 (fun he => generatorSearch_exhausted ht (ht.2.trans (congrArg some he))) ?_
  intro he
  have available := generatorSearch_available ht (ht.2.trans (congrArg some he))
  exact WP.seq (WP.mono (generatorSearch_take available) fun _ hv =>
    WP.seq (WP.mono (generatorSearch_body_ready M Sq hv) fun _ hw => generatorSearch_status hw))

private def generatorLoopInv (len remaining : Nat) : State → State → Prop :=
  Two fun p s => p.plan.tape.length - p.used + 1 = remaining ∧ GeneratorSearchBefore len p s

private theorem generatorLoop_step (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) (remaining : Nat) :
    RelCT isa (generatorLoopInv len remaining)
      (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len))
      (fun s t => isa.eval .e s = isa.eval .e t ∧ (isa.eval .e s = some false → True) ∧
        (isa.eval .e s = some true → ∃ next < remaining, generatorLoopInv len next s t)) := by
  have step : RelCT isa (generatorLoopInv len remaining)
      (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len))
      (Two fun p s => p.plan.tape.length - p.used + 1 = remaining ∧ GeneratorSearchIterationAfter len p s) := by
    refine two_post ((generatorIteration_ct M Sq len hl).mono
      (fun _ _ => two_mono fun _ _ h => h.2) (fun _ _ _ => True.intro)) ?_
    intro p s h
    exact WP.mono (generatorIteration_ready M Sq h.2) fun _ ht => ⟨h.1, ht⟩
  refine step.mono (fun _ _ h => h) ?_
  rintro s t ⟨p, ⟨hr, hs⟩, ⟨_, ht⟩⟩
  refine ⟨hs.1.trans ht.1.symm, fun _ => True.intro, fun he => ?_⟩
  have cont : p.continues = true := Option.some.inj (hs.1.symm.trans he)
  have room := (p.next cont).bound
  have positive : 0 < p.plan.core.len := by rcases p.plan.core.width with hh | hh | hh <;> omega_using [hh]
  refine ⟨p.plan.tape.length - (p.used + p.plan.core.len) + 1, ?_, p.next cont,
    ⟨rfl, hs.2 cont⟩, rfl, ht.2 cont⟩
  change p.used + p.plan.core.len ≤ p.plan.tape.length at room
  omega_using [hr, positive, room]

theorem generatorLoop_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchBefore len))
      (.loop (tapeIteration generatorTape len (generatorStep Sq.mm M.mm len)) .e) (fun _ _ => True) := by
  rintro s t a b s' t' ⟨p, hs, ht⟩ es et
  exact RelCT.loop (generatorLoopInv len) (generatorLoop_step M Sq len hl)
    (p.plan.tape.length - p.used + 1) s t a b s' t' ⟨p, ⟨rfl, hs⟩, rfl, ht⟩ es et

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Timing of complete native generator selection from an input tape -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64.Generation VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64

def GeneratorSearchStart (len : Nat) (p : GeneratorSearchPlan) (s : State) : Prop :=
  (∃ W, GeneratorSearchMemory p W s) ∧ p.core.len = len

def GeneratorSearchPlan.start (p : GeneratorSearchPlan) : GeneratorSearchPublic := ⟨p, 0, Nat.zero_le _⟩

theorem generatorSearch_reset {len : Nat} {p : GeneratorSearchPlan} {s : State}
    (h : GeneratorSearchStart len p s) :
    WP isa (.block (tapeReset generatorTape)) s (GeneratorSearchBefore len p.start) := by
  obtain ⟨⟨W, hm⟩, he⟩ := h
  obtain ⟨V, R⟩ := hm.rep
  refine WP.mono (tapeReset_ok hm.layout R generatorTape (by decide) (by decide))
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
  refine ⟨⟨upd W 20 0, hm.frame Lt ⟨V, Rt⟩ ?_ ff kt.2.1 kt.2.2, by simp [upd, GeneratorSearchPlan.start]⟩, he⟩
  intro k hk
  simp only [generatorSlots, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nativeGenerator_ct (M : Mont) (Sq : MontS) (len : Nat)
    (hl : len = 128 ∨ len = 256 ∨ len = 384) :
    RelCT isa (Two (GeneratorSearchStart len)) (generatorSearch Sq.mm M.mm len) (fun _ _ => True) := by
  unfold generatorSearch tapeLoop
  refine RelCT.seq (two_piece [.rsp] ?_ (by taint_decide)
    (fun _ _ h => generatorSearch_reset h)) ?_
  · intro p s t ⟨⟨Ws, hs⟩, _⟩ ⟨⟨Wt, ht⟩, _⟩ r hr
    obtain rfl := List.mem_singleton.mp hr
    exact hs.layout.rsp.trans ht.layout.rsp.symm
  · exact two_map GeneratorSearchPlan.start (fun _ _ h => h) (generatorLoop_ct M Sq len hl)

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # Public accepted primes determine the generator-search plan -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout

structure SeedGeneratorPublic where
  seed : SeedPublic
  value : Nat
  domain : VG.Proof.Dsa.Generation.PDomain seed.context.geo.pLen value

def SeedGeneratorPublic.qValue (p : SeedGeneratorPublic) : Nat :=
  Spec.Dsa.qCandidate (8 * p.seed.context.geo.qLen) p.seed.seed.bytes

def SeedGeneratorPublic.plan (p : SeedGeneratorPublic) : GeneratorSearchPlan := by
  have fit : p.value < 256 ^ p.seed.context.geo.pLen := by
    simpa only [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_mul] using p.domain.upper
  have decode := VG.Proof.Dsa.decodeBE_encodeBE fit
  have expFit : (p.value - 1) / p.qValue < 256 ^ p.seed.context.geo.pLen :=
    Nat.lt_of_le_of_lt (Nat.le_trans (Nat.div_le_self _ _) (Nat.sub_le _ _)) fit
  exact p.seed.context.generatorPlan (upd p.seed.words 16 (BitVec.ofNat 64 p.seed.used))
    (Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value)
    (Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue))
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _)
    (by rw [decode]; omega_using [p.domain.large])
    (by rw [decode]; exact p.domain.odd) p.qValue
    (by rw [decode, VG.Proof.Dsa.decodeBE_encodeBE expFit])

def SeedGeneratorBefore (n pLen qLen : Nat) (p : SeedGeneratorPublic) (s : State) : Prop :=
  SeedPrimeBefore n pLen qLen p.seed s ∧
  Spec.Rsa.bytesAt s.mem (off p.seed.context.geo.B VG.Impl.Dsa.Generation.Layout.p) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen p.value ∧
  Spec.Rsa.bytesAt s.mem (off p.seed.context.geo.B exponent) p.seed.context.geo.pLen =
    Spec.Dsa.encodeBE p.seed.context.geo.pLen ((p.value - 1) / p.qValue)

theorem seedGenerator_start {n pLen qLen : Nat} {p : SeedGeneratorPublic} {s : State}
    (h : SeedGeneratorBefore n pLen qLen p s) : GeneratorSearchStart pLen p.plan s := by
  obtain ⟨⟨⟨⟨W, hm, h1, h16, h10⟩, _, _, _, _⟩, hp, _⟩, bp, be⟩ := h
  have state := hm.generatorState p.plan.core.pb p.plan.core.eb p.plan.core.pLength p.plan.core.eLength
    p.plan.core.pPositive p.plan.core.pOdd p.qValue p.plan.exponentValue bp be
  refine ⟨⟨W, { state with slots := ?_ }⟩, hp⟩
  intro k hk
  change W k = upd p.seed.words 16 (BitVec.ofNat 64 p.seed.used) k
  by_cases h16k : k = 16
  · subst k; simpa [upd] using h16
  by_cases h1k : k = 1
  · subst k; simpa [upd, SeedPublic.words] using h1
  by_cases h10k : k = 10
  · subst k; simpa [upd, SeedPublic.words] using h10
  have member : k ∈ generationSlots := by
    simp only [generatorSlots, generationSlots, List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
    omega_using [h16k, h1k, h10k, hk]
  simpa [upd, SeedPublic.words, h16k, h1k, h10k] using hm.slots k member

end VG.Proof.Dsa.X86_64.Generation
