module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateBranch
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Ptr
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.TCB.X86.Isa
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestCoreTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePrepareInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.MrExponentRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
import VerifiedGarbage.Proof.RsaKeyGen.X86.MrExponentRt.Prepared
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.R2Timing
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.RsaKeyGen.X86.SigMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.HeaderStore
import VerifiedGarbage.Proof.MillerRabin.X86.TimingCopy
import VerifiedGarbage.Proof.MillerRabin.X86.TimingPointers
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBase
public import VerifiedGarbage.Proof.Mont.X86.WordOps
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
import VerifiedGarbage.Proof.RsaKeyGen.X86.WorkspaceDisjoint
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateStack
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ConstantsTiming
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.R2
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedCopy
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.MillerRabin.X86.TimingMultiply
import VerifiedGarbage.Proof.MillerRabin.X86.Multiply
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Loop
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessFrame
import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportLoop
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
import VerifiedGarbage.Proof.Mont.RegionOutside
public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessRt
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.MillerRabin.X86.Context
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ImportContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinStep
public import VerifiedGarbage.Proof.MillerRabin.X86.Caller
public import VerifiedGarbage.Proof.MillerRabin.Contract
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateShape
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.RsaKeyGen.RandMemory
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateArrays
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Code
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentRt
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Array
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64
public import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
public import VerifiedGarbage.Proof.Mont.X86.ExponentTiming
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Word
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Result
import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Setup
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
public import VerifiedGarbage.Impl.Bignum.X86.PublicContext

/-! ### `RsaKeyGen.X86.CandidateTestTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateTimingInput`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.CandidateExponentInitial`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.ExponentTimingInput`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.ExponentRt.FastTiming`, which this module and modules that import it used -/

section

/-! ### `RsaKeyGen.X86.ExponentRt.SaveTiming`, which this module and modules that import it used -/

section

/-! # Saving and restoring the candidate at a run-time width have public loop bounds

The pointers and the count of the copies are computed from the length in
the header, which the taint analysis takes for secret: each run computes
them from the same length, so they agree once correctness gives their
values (`publish`), and the loops are then checked with them public.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt

/-- Runs from states agreeing on `rs` leak the same trace (`raw`); by
correctness each run leaves the same values `f r` in the registers `qs`,
which therefore agree afterwards. -/
theorem publish {X Y : State → Prop} {c : Prog isa} {rs : List Reg} (qs : List Reg) (f : Reg → BitVec 32)
    (agree : ∀ s t, X s → X t → VG.X86.Taint.Agree (τr rs) s t)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr rs)) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s (fun u => Y u ∧ ∀ r ∈ qs, u.gpr r = f r)) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => (Y u ∧ Y z) ∧ VG.X86.Taint.Agree (τr qs) u z) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  obtain ⟨Yu, Fu⟩ := wp_result (run s S) E
  obtain ⟨Yz, Fz⟩ := wp_result (run t T) G
  exact ⟨(raw _ _ _ _ _ _ (agree s t S T) E G).1, ⟨Yu, Yz⟩, agree_regs fun r mem => (Fu r mem).trans (Fz r mem).symm⟩

/-- Runs leaking the same trace (`raw`) whose final states each satisfy `Y`
by correctness. -/
theorem checked {X Y : State → Prop} {P Q : State → State → Prop} {c : Prog isa}
    (raw : RelCT isa P c Q) (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => (X s ∧ X t) ∧ P s t) c (fun u z => (Y u ∧ Y z) ∧ Q u z) := by
  intro s t tr ur u z ⟨⟨S, T⟩, H⟩ E G
  obtain ⟨trace, post⟩ := raw _ _ _ _ _ _ H E G
  exact ⟨trace, ⟨wp_result (run s S) E, wp_result (run t T) G⟩, post⟩

/-- The working space, the stack and the length `8 w` in the header. -/
structure Space (workspace p : BitVec 32) (size w : Nat) (s : State) : Prop where
  scratch : Scr s (workspace.setWidth 64) size
  stack : s.gpr .esp = p
  width : 4 ≤ w
  widthBound : w ≤ 64
  space : slot w 5 + 8 * w ≤ size
  len : s.mem.readW (off (workspace.setWidth 64) 4) 32 = BitVec.ofNat 32 (8 * w)

theorem Space.workspace {workspace p : BitVec 32} {size w : Nat} {s : State}
    (S : Space workspace p size w s) : s.gpr .edi = workspace := by
  apply BitVec.eq_of_toNat_eq
  rw [S.scratch.edi_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans workspace.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem Space.keep {workspace p : BitVec 32} {size w : Nat} {s t : State} (S : Space workspace p size w s)
    {rs : List Reg} (K : Keeps rs s t) (edi : .edi ∉ rs) (esp : .esp ∉ rs)
    (L : t.mem.readW (off (workspace.setWidth 64) 4) 32 = s.mem.readW (off (workspace.setWidth 64) 4) 32) :
    Space workspace p size w t :=
  ⟨S.scratch.of_keeps K edi esp, (K.1 .esp esp).trans S.stack, S.width, S.widthBound, S.space, L.trans S.len⟩

theorem Space.agree {workspace p : BitVec 32} {size w : Nat} {s t : State}
    (S : Space workspace p size w s) (T : Space workspace p size w t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.stack.trans T.stack.symm
  · exact S.workspace.trans T.workspace.symm

theorem Space.header {workspace p : BitVec 32} {size w : Nat} {s : State}
    (S : Space workspace p size w s) : 256 + 8 * w ≤ slot w 5 ∧ slot w 5 + 8 * w ≤ size :=
  ⟨slot5_ge w, S.space⟩

/-- The registers of a copy: its source and destination, at `x` and `y`. -/
def copyRegs (workspace p : BitVec 32) (w src dst : Nat) : Reg → BitVec 32
  | .esp => p
  | .edi => workspace
  | .ebp => workspace + BitVec.ofNat 32 src
  | .ebx => workspace + BitVec.ofNat 32 dst
  | .esi => BitVec.ofNat 32 (2 * w)
  | .ecx => BitVec.allOnes 32
  | _ => 0

/-- A copy about to run: the working space and its pointers. -/
structure CopyIn (workspace p : BitVec 32) (size w src dst : Nat) (s : State) : Prop where
  space : Space workspace p size w s
  regs : ∀ r ∈ [Reg.esp, .edi, .ebp, .ebx, .esi, .ecx], s.gpr r = copyRegs workspace p w src dst r

theorem copy_trace {workspace p : BitVec 32} {size w src dst : Nat}
    (fits : slot w 5 + 8 * w ≤ size → src + 8 * w ≤ size ∧ dst + 8 * w ≤ size ∧
      (dst + 8 * w ≤ src ∨ src + 8 * w ≤ dst) ∧ 8 ≤ dst) :
    RelCT isa (fun s t => (CopyIn workspace p size w src dst s ∧ CopyIn workspace p size w src dst t) ∧
        VG.X86.Taint.Agree (τr [.esp, .edi, .ebp, .ebx, .esi, .ecx]) s t) copyLoop
      (fun u z => (Space workspace p size w u ∧ Space workspace p size w z) ∧
        VG.X86.Taint.Agree (τr [.esp, .edi]) u z) := by
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp, .ebx, .esi, .ecx])) copyLoop
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT copyLoop copyLoop
      (VG.Taint.hintOf taint (τr [.esp, .edi, .ebp, .ebx, .esi, .ecx]) (Code.erase copyLoop))
      (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)
  refine checked raw fun s S => ?_
  obtain ⟨fit, dstFit, apart, headerApart⟩ := fits S.space.space
  have nowrap := S.space.scratch.nowrap
  have hws : Ws s (workspace.setWidth 64) size := ⟨S.space.scratch.wr, nowrap⟩
  have edi : s.gpr .edi = workspace := S.space.workspace
  refine WP.mono (copyLoop_ok hws (x := dst) (y := src) (N := 2 * w) (by have := S.space.width; omega_using [this]) (by omega_using [dstFit])
    (by omega_using [fit]) (by omega_using [apart])
    (ptrAt_edi S.space.scratch (by rw [S.regs .ebx (by simp), edi]; rfl))
    (ptrAt_edi S.space.scratch (by rw [S.regs .ebp (by simp), edi]; rfl))
    (by rw [S.regs .esi (by simp)]; change (BitVec.ofNat 32 (2 * w)).toNat = 2 * w
        rw [BitVec.toNat_ofNat]; have := S.space.widthBound; omega_using [this])
    (S.regs .ecx (by simp))) fun u ⟨O, _, K⟩ => ?_
  exact S.space.keep K (by decide) (by decide)
    (BitVec.eq_of_toNat_eq (O.w32 (d := 4) (Or.inl (by omega_using [headerApart])) (by omega_using [])))

theorem save_trace {workspace p : BitVec 32} {size w : Nat} :
    RelCT isa (fun s t => Space workspace p size w s ∧ Space workspace p size w t) save
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  unfold save
  have setupRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block saveSetup)
      (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have setup := publish (X := Space workspace p size w) (Y := CopyIn workspace p size w 256 (slot w 5))
    [.esp, .edi, .ebp, .ebx, .esi, .ecx] (copyRegs workspace p w 256 (slot w 5)) (fun _ _ S T => S.agree T)
    setupRaw (fun s S => ?_)
  rotate_left
  · have header := S.header
    refine WP.mono (saveSetup_ok S.scratch S.widthBound (by omega_using [header]) S.len) fun d ⟨K, M, ebp, ebx, esi, ecx⟩ => ?_
    have Sd : Space workspace p size w d := S.keep K (by decide) (by decide) (by rw [M])
    have regs : ∀ r ∈ [Reg.esp, .edi, .ebp, .ebx, .esi, .ecx], d.gpr r = copyRegs workspace p w 256 (slot w 5) r := by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Sd.stack
      · exact Sd.workspace
      · rw [ebp, S.workspace]; rfl
      · rw [ebx, S.workspace]; rfl
      · apply BitVec.eq_of_toNat_eq; rw [esi]; change 2 * w = (BitVec.ofNat 32 (2 * w)).toNat
        rw [BitVec.toNat_ofNat]; have := S.widthBound; omega_using [esi]
      · exact ecx
    exact ⟨⟨Sd, regs⟩, regs⟩
  have loop := copy_trace (workspace := workspace) (p := p) (size := size) (w := w) (src := 256) (dst := slot w 5)
    fun h => by have := slot5_ge w; exact ⟨by omega_using [h, this], h, Or.inr (by omega_using [this]), by omega_using [this]⟩
  have ptrRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (savedPtr .ebx .edx)) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have ptr := publish (X := Space workspace p size w) (Y := fun _ => True) [.esp, .edi, .ebx]
    (copyRegs workspace p w 256 (slot w 5)) (fun _ _ S T => S.agree T) ptrRaw (fun s S => ?_)
  rotate_left
  · refine WP.mono (savedPtr_block_ok S.scratch (by have := S.header; omega_using [this]) S.len (by decide) (by decide)
      (by decide)) fun d ⟨K, _, ebx⟩ => ⟨trivial, ?_⟩
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · rw [K.1 .esp (by decide)]; exact S.stack
    · rw [K.1 .edi (by decide)]; exact S.workspace
    · rw [ebx, S.workspace]; rfl
  have dec : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebx])) (.block decrementAt)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel)
  exact RelCT.seq setup (RelCT.seq loop (RelCT.seq (ptr.mono (fun _ _ H => H.1) (fun _ _ H => H.2)) dec))

end VG.Proof.RsaKeyGen.X86.ExponentRt

end

end

/-! # The 65537 filter at a run-time width reads the same words in every run -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/FermatTiming.lean`, which only this module imported.
section

/-! # Coprimality with 65537 uses only public frame and candidate addresses -/

section
namespace VG.Proof.RsaKeyGen.X86.FermatExponent
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.FermatExponent VG.Proof.RsaKeyGen.X86.Sieve

theorem init_control {g : Geometry} {s : State} (S : ReadControl g 0 s) :
    WP isa (.block init) s (ReadControl g 0) := by
  unfold init
  refine wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => wp_movS rfl fun t T _ => WP.block_nil ?_
  have K : Keeps [.ebx, .esi, .ebp] s t := ((A.keeps.mono (by decide)).widen B.keeps).widen T.keeps
  exact ⟨S.stack.keep K (by decide),
    fun i index => by rw [K.2.1, K.2.2]; exact S.candidateRead i index,
    by rw [T.mem, B.mem, A.mem]; exact S.ending,
    (K.1 .edi (by decide)).trans S.pointer⟩

theorem init_trace {g : Geometry} :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) (.block init)
      (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have trace := ((checkedBlockInvariant (τ := τr [.esp, .edi]) (code := init) rfl rfl)
    _ _ _ _ _ _ (S.agree T) E G).1
  exact ⟨trace, wp_result (init_control S) E, wp_result (init_control T) G⟩

theorem code_trace_bounded {g : Geometry} (positive : 0 < g.w) (widthBound : g.w ≤ 128)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) (code 4)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq init_trace (RelCT.seq (divisor_trace_bounded positive widthBound candidateFit) (checkedBlockInvariant rfl rfl))

end VG.Proof.RsaKeyGen.X86.FermatExponent
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt
open VG.Impl.Mont.X86 (at_)

/-- The working space, and the stack below it for a frame of 20 bytes. -/
structure Framed (workspace p : BitVec 32) (size w : Nat) (s : State) : Prop where
  space : Space workspace p size w s
  fit : 40 ≤ p.toNat
  separate : p.toNat ≤ (workspace.setWidth 64).toNat ∨ (workspace.setWidth 64).toNat + size + 40 ≤ p.toNat

theorem Framed.scratch {workspace p : BitVec 32} {size w : Nat} {s : State} (S : Framed workspace p size w s) :
    Scr (allocFrame 20 s) (workspace.setWidth 64) size :=
  VG.Proof.RsaKeyGen.X86.FilterStack.allocated_scratch S.space.scratch (by rw [S.space.stack]; exact S.fit)
    (by rw [S.space.stack]; exact S.separate)

/-- The trial frame of the 65537 filter over array 5. -/
def fastGeometry (workspace p : BitVec 32) (w : Nat) : Sieve.Geometry :=
  ⟨p - 20#32, workspace + BitVec.ofNat 32 (slot w 5), 0, w, 1⟩

theorem fastArgs_control {workspace p : BitVec 32} {size w : Nat} {s : State}
    (S : Framed workspace p size w s) :
    WP isa (.block fastArgs) (allocFrame 20 s) (Sieve.ReadControl (fastGeometry workspace p w) 0) := by
  have fit : 20 ≤ (s.gpr .esp).toNat := by rw [S.space.stack]; have := S.fit; omega_using [this]
  have C : Sieve.StackContext (p - 20#32) (allocFrame 20 s) := by
    rw [← S.space.stack]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context fit
  have Si := S.scratch
  have width := S.space.width
  have space := S.space.space
  have nowrap := Si.nowrap
  have header := slot5_ge w
  refine WP.mono (fastArgs_ok (w := w) C Si (by omega_using [width, space]) (by rw [allocFrame_mem]; exact S.space.len))
    fun t ⟨ptr, ending, _, _, K⟩ => ?_
  have edi : (allocFrame 20 s).gpr .edi = workspace := by
    rw [allocFrame_gpr _ _ (by decide)]; exact S.space.workspace
  have pbase : (workspace + BitVec.ofNat 32 (slot w 5)).setWidth 64 = off (workspace.setWidth 64) (slot w 5) := by
    have h := Si.ea (d := slot w 5) (by omega_using [width, space])
    change ((allocFrame 20 s).gpr .edi + BitVec.ofNat 32 (slot w 5)).setWidth 64 = _ at h
    rw [edi] at h
    exact h
  refine ⟨C.keep K (by decide), ?_, ?_, ?_⟩
  · intro i index
    change i < 2 * w at index
    rw [K.2.1, K.2.2]
    change InRegions _ (off ((workspace + BitVec.ofNat 32 (slot w 5)).setWidth 64) (4 * i)) 4
    rw [pbase]
    simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add] using Si.read (d := slot w 5 + 4 * i) (n := 4) (by omega_using [space, index])
  · change t.mem.readW (off ((p - 20#32).setWidth 64) 4) 32 =
      workspace + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (8 * w)
    rw [ending, edi]
  · change t.gpr .edi = workspace + BitVec.ofNat 32 (slot w 5) + BitVec.ofNat 32 (4 * 0)
    rw [ptr, edi, show BitVec.ofNat 32 (4 * 0) = 0#32 from rfl, BitVec.add_zero]

theorem fast_trace {workspace p : BitVec 32} {size w : Nat} :
    RelCT isa (fun s t => Framed workspace p size w s ∧ Framed workspace p size w t) fast (fun _ _ => True) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have nowrap := S.space.scratch.nowrap
  have space := S.space.space
  have width := S.space.width
  have widthBound := S.space.widthBound
  have header := slot5_ge w
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block fastArgs) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have args : RelCT isa (fun a b => ∃ s₁ s₂, (Framed workspace p size w s₁ ∧ Framed workspace p size w s₂) ∧
      a = allocFrame 20 s₁ ∧ b = allocFrame 20 s₂) (.block fastArgs)
      (fun a b => Sieve.ReadControl (fastGeometry workspace p w) 0 a ∧
        Sieve.ReadControl (fastGeometry workspace p w) 0 b) := by
    rintro _ _ tr ur a b ⟨s₁, s₂, ⟨S₁, S₂⟩, rfl, rfl⟩ E₁ E₂
    have agree : VG.X86.Taint.Agree (τr [.esp, .edi]) (allocFrame 20 s₁) (allocFrame 20 s₂) := by
      apply agree_regs
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, allocFrame_esp, S₁.space.stack, S₂.space.stack]
      · rw [allocFrame_gpr _ _ (by decide), allocFrame_gpr _ _ (by decide), S₁.space.workspace,
          S₂.space.workspace]
    exact ⟨(raw _ _ _ _ _ _ agree E₁ E₂).1, wp_result (fastArgs_control S₁) E₁, wp_result (fastArgs_control S₂) E₂⟩
  have fit : (workspace + BitVec.ofNat 32 (slot w 5)).toNat + 8 * w ≤ 2 ^ 32 := by
    have edi := S.space.scratch.edi_toNat
    rw [S.space.workspace] at edi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := slot w 5) (by omega_using [nowrap, space, width]), edi,
      Nat.mod_eq_of_lt (by omega_using [nowrap, space, width])]
    omega_using [nowrap, space]
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .edi (.mem (at_ .esp 0))]) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have body := RelCT.seq args (RelCT.seq (VG.Proof.RsaKeyGen.X86.FermatExponent.code_trace_bounded
    (g := fastGeometry workspace p w) (by change 0 < w; omega_using [width]) (by change w ≤ 128; omega_using [widthBound]) fit) restore)
  exact RelCT.frameAlloc body _ _ _ _ _ _ ⟨S, T⟩ E G

end VG.Proof.RsaKeyGen.X86.ExponentRt

end

end

/-! ### `RsaKeyGen.X86.ExponentRt.GeneralTiming`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.Gcd64Timing`, which only this module used -/

section

/-! # The fixed native 64-bit GCD schedule has no input-dependent branches or addresses -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Gcd64

theorem bankStep_public (a b : Nat) : KeyPublic (bankStep a b) := by
  unfold bankStep
  apply KeyPublic.seqs
  intro c mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact bitOf_public .. | exact sub3_public .. | exact sel_public .. |
      exact masks_public | exact zeroCarry_public | exact half_public ..

theorem code_check : ∃ hint, VG.Taint.check taint (workspaceTaint false) code hint = some counterEndTaint := by
  obtain ⟨h1, o1, c1, l1⟩ := bankStep_public 0 4
  obtain ⟨h2, o2, c2, l2⟩ := bankStep_public 4 0
  let bodyHint : VG.Taint.Hint VG.X86.Taint.T :=
    .seq (workspaceTaint true) h1 (.seq (workspaceTaint true) h2 (.block []))
  have checkedBody : VG.Taint.check taint (workspaceTaint true) body bodyHint = some counterEndTaint :=
    exponent_check_seq taint c1 l1 (exponent_check_seq taint c2 l2 (by rfl))
  have checkedLoop : VG.Taint.check taint (workspaceTaint true) (.loop body .ne)
      (.loop (workspaceTaint true) bodyHint) = some counterEndTaint := by
    change (if taint.le (workspaceTaint true) (workspaceTaint true) then
      (VG.Taint.check taint (workspaceTaint true) body bodyHint).bind
        (fun t => if taint.le (workspaceTaint true) t && taint.condPub t .ne then some t else none)
      else none) = _
    rw [checkedBody]
    rfl
  refine ⟨.seq (workspaceTaint true) (.block []) (.loop (workspaceTaint true) bodyHint), ?_⟩
  exact exponent_check_seq taint (u := workspaceTaint true) (by rfl) (by rfl) checkedLoop

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) code
    (VG.X86.Taint.Agree (workspaceTaint false)) := by
  obtain ⟨hint, checked⟩ := code_check
  exact checkedProgramChange checked rfl

end VG.Proof.RsaKeyGen.X86.Gcd64

end

end

/-! ### `RsaKeyGen.X86.Mod64ArrayLoadTiming`, which only this module used -/

section

/-! # Republish the public descending pointer before loading secret candidate data -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem ArrayState.agree {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} {s t : State}
    (S : ArrayState g candidate exponent i s) (T : ArrayState g other otherExponent i t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.context.stack.sp.trans T.context.stack.sp.symm
  · exact S.context.workspace.trans T.context.workspace.symm

theorem pointerLoad_ok {g : ArrayGeometry} {candidate exponent i : Nat} {s : State}
    (S : ArrayState g candidate exponent i s) :
    WP isa (.block [.mov .eax (.mem (stack 0))]) s fun t =>
      t.gpr .eax = g.pointer i ∧ t.gpr .esp = g.sp ∧ t.gpr .edi = g.workspace := by
  refine wp_movS (S.context.stack.read 0 (by decide)) fun t T _ => WP.block_nil ?_
  exact ⟨T.gpr.trans S.pointer, (T.other .esp (by decide)).trans S.context.stack.sp,
    (T.other .edi (by decide)).trans S.context.workspace⟩

theorem pointerLoad_trace {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent i s ∧ ArrayState g other otherExponent i t)
      (.block [.mov .eax (.mem (stack 0))]) (VG.X86.Taint.Agree (τr [.esp, .edi, .eax])) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have trace := ((checkedBlockInvariant (τ := τr [.esp, .edi]) (code := [.mov .eax (.mem (stack 0))]) rfl rfl)
    _ _ _ _ _ _ (S.agree T) E G).1
  obtain ⟨Au, Su, Wu⟩ := wp_result (pointerLoad_ok S) E
  obtain ⟨Az, Sz, Wz⟩ := wp_result (pointerLoad_ok T) G
  refine ⟨trace, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact Su.trans Sz.symm
  · exact Wu.trans Wz.symm
  · exact Au.trans Az.symm

theorem loadWord_trace {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent i s ∧ ArrayState g other otherExponent i t)
      (.block loadWord) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  change RelCT isa _ (.block ([.mov .eax (.mem (stack 0))] ++ [.mov .esi (.mem ⟨.eax, 0⟩)])) _
  exact RelCT.block_append (RelCT.seq pointerLoad_trace
    (checkedProgramChange (τ' := τr [.esp, .edi, .eax]) (hint := .block []) rfl rfl))

end VG.Proof.RsaKeyGen.X86.Mod64

end

end

/-! # The general public exponent at a run-time width: the remainder, the gcd and the restored candidate -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64Timing.lean`, which only this module imported.
section

/-! # A public-exponent reduction bit keeps every candidate bit secret -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem bit_trace (exponent : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (bit exponent))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (bit exponent)) (.block (bit 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64WordTiming.lean`, which only this module imported.
section

/-! # A whole native-word reduction has a fixed secret-independent trace -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem steps_trace (exponent count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (steps exponent count))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  blockFlatMap_relCT (List.range count) (fun _ => bit exponent) (fun _ => bit_trace exponent)

theorem word_trace (exponent : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (VG.Impl.RsaKeyGen.X86.Mod64.word exponent))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := steps_trace exponent 32

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayStepTiming.lean`, which only this module imported.
section

/-! # A complete word iteration has only public-address stack and workspace accesses -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem advance_trace : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block advance)
    (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl

theorem arrayStep_trace {g : ArrayGeometry} {candidate exponent other otherExponent i : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent i s ∧ ArrayState g other otherExponent i t)
      (arrayStep g.exponent) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq loadWord_trace (RelCT.seq (word_trace g.exponent) advance_trace)

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayLoopTiming.lean`, which only this module imported.
section

/-! # Candidate size alone controls the modular reduction's word loop -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Mod64

theorem loop_trace {g : ArrayGeometry} (v : g.Valid) {candidate exponent other otherExponent : Nat} :
    RelCT isa (fun s t => ArrayState g candidate exponent 0 s ∧ ArrayState g other otherExponent 0 t)
      (.loop (arrayStep g.exponent) .ne) (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  refine (RelCT.loop (M := isa) (body := arrayStep g.exponent) (c := .ne)
    (I := fun q s t => ∃ i, i < g.n ∧ q = g.n - i ∧ ArrayState g candidate exponent i s ∧
      ArrayState g other otherExponent i t) (Q := VG.X86.Taint.Agree (τr [.esp, .edi])) ?_ g.n).mono
    (fun _ _ H => ⟨0, v.positive, rfl, H⟩) (fun _ _ H => H)
  rintro q s t tr ur u z ⟨i, index, rfl, S, T⟩ E G
  have trace := (arrayStep_trace _ _ _ _ _ _ ⟨S, T⟩ E G).1
  obtain ⟨U, Zu, _, _⟩ := wp_result (S.step v index) E
  obtain ⟨Z, Zz, _, _⟩ := wp_result (T.step v index) G
  have eu : isa.eval .ne u = some (!decide (i + 1 = g.n)) := by
    change u.zf.map Bool.not = _
    rw [Zu]
    rfl
  have ez : isa.eval .ne z = some (!decide (i + 1 = g.n)) := by
    change z.zf.map Bool.not = _
    rw [Zz]
    rfl
  refine ⟨trace, eu.trans ez.symm, fun _ => U.agree Z, ?_⟩
  intro next
  have more : i + 1 ≠ g.n := by
    intro done
    rw [eu, decide_eq_true done] at next
    cases next
  exact ⟨g.n - (i + 1), by omega, i + 1, by omega, rfl, U, Z⟩

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Mod64ArrayTiming.lean`, which only this module imported.
section

/-! # Two runs of the reduction agree on its public pointers -/

section
namespace VG.Proof.RsaKeyGen.X86.Mod64
open VG VG.X86

theorem ArrayContext.agree {g : ArrayGeometry} {candidate exponent other otherExponent : Nat} {s t : State}
    (S : ArrayContext g candidate exponent s) (T : ArrayContext g other otherExponent t) :
    VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.stack.sp.trans T.stack.sp.symm
  · exact S.workspace.trans T.workspace.symm

end VG.Proof.RsaKeyGen.X86.Mod64
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Gcd64CheckTiming.lean`, which only this module imported.
section

/-! # Complete native coprimality executes independently of the remainder's value -/

section
namespace VG.Proof.RsaKeyGen.X86.Gcd64
open VG VG.X86 VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Gcd64

theorem setup_trace (offset : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block (setup offset))
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  erased_relCT (.block (setup offset)) (.block (setup 0)) (.block []) rfl rfl rfl (by decide +kernel)

theorem result_trace : RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (.block result)
    (VG.X86.Taint.Agree (workspaceTaint false)) := checkedBlockInvariant rfl rfl

end VG.Proof.RsaKeyGen.X86.Gcd64
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.RsaKeyGen.X86.ExponentRt
open VG.Proof.RsaKeyGen.X86.Mod64 (ArrayContext ArrayState)

/-- The general path's inputs: the saved candidate minus one and an odd `e`. -/
structure GeneralIn (workspace p : BitVec 32) (size w candidate exponent : Nat) (s : State) : Prop where
  framed : Framed workspace p size w s
  saved : val32 s.mem (workspace.setWidth 64) (slot w 5) (2 * w) = candidate - 1
  eValue : Mod64.exponentValue s.mem (workspace.setWidth 64) 128 = exponent
  eOdd : exponent % 2 = 1

theorem GeneralIn.context {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : GeneralIn workspace p size w candidate exponent s) :
    (geometry (p - 20#32) workspace size w).Valid ∧
      ArrayContext (geometry (p - 20#32) workspace size w) (candidate - 1) exponent (allocFrame 20 s) := by
  have F := S.framed
  have H := framed_context F.space.scratch F.space.width F.space.space S.saved S.eValue
    (by rw [F.space.stack]; exact F.fit) (by rw [F.space.stack]; exact F.separate)
  rw [F.space.stack, F.space.workspace] at H
  exact H

theorem GeneralIn.len {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : GeneralIn workspace p size w candidate exponent s) :
    (allocFrame 20 s).mem.readW (off (geometry (p - 20#32) workspace size w).base 4) 32 =
      BitVec.ofNat 32 (8 * w) := S.framed.space.len

theorem array_framed_trace {workspace p : BitVec 32} {size w c d exponent : Nat} :
    RelCT isa (fun s t => GeneralIn workspace p size w c exponent s ∧ GeneralIn workspace p size w d exponent t)
      (.frame (.alloc 20) array (.free 20))
      (fun u z => (Space workspace p size w u ∧ Mod64.exponentValue u.mem (workspace.setWidth 64) 128 = exponent) ∧
        (Space workspace p size w z ∧ Mod64.exponentValue z.mem (workspace.setWidth 64) 128 = exponent)) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have v := S.context.1
  have positive : 0 < exponent := by have := S.eOdd; omega_using [this]
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block arrayInit) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have init : RelCT isa (fun a b => ∃ s₁ s₂, (GeneralIn workspace p size w c exponent s₁ ∧
        GeneralIn workspace p size w d exponent s₂) ∧ a = allocFrame 20 s₁ ∧ b = allocFrame 20 s₂)
      (.block arrayInit) (fun a b => ArrayState (geometry (p - 20#32) workspace size w) (c - 1) exponent 0 a ∧
        ArrayState (geometry (p - 20#32) workspace size w) (d - 1) exponent 0 b) := by
    rintro _ _ tr₁ tr₂ a b ⟨s₁, s₂, ⟨S₁, S₂⟩, rfl, rfl⟩ E₁ E₂
    have C₁ := S₁.context.2
    have C₂ := S₂.context.2
    exact ⟨(raw _ _ _ _ _ _ (VG.Proof.RsaKeyGen.X86.Mod64.ArrayContext.agree C₁ C₂) E₁ E₂).1,
      (wp_result (init_ok v C₁ positive S₁.framed.space.widthBound S₁.len) E₁).1,
      (wp_result (init_ok v C₂ positive S₂.framed.space.widthBound S₂.len) E₂).1⟩
  have body := RelCT.seq init (VG.Proof.RsaKeyGen.X86.Mod64.loop_trace v)
  refine ⟨(RelCT.frameAlloc body _ _ _ _ _ _ ⟨S, T⟩ E G).1, ?_, ?_⟩
  all_goals first
    | (obtain ⟨Sx, -, -, eA, Fx, Kx⟩ := wp_result (framed_ok S.framed.space.scratch S.framed.space.width
          S.framed.space.widthBound S.framed.space.space S.framed.space.len rfl S.eValue positive
          (by rw [S.framed.space.stack]; exact S.framed.fit) (by rw [S.framed.space.stack]; exact S.framed.separate)) E
       exact ⟨⟨Sx, (Kx.1 .esp (by decide)).trans S.framed.space.stack, S.framed.space.width,
         S.framed.space.widthBound, S.framed.space.space,
         (Fx.readW (r := ⟨workspace.setWidth 64, size⟩)
           (Offset.contains_base _ (by have := slot5_lo w; have := S.framed.space.space; omega_arith)
             (by have := S.framed.space.scratch.nowrap; omega_using []))
           (by
             intro r mem; obtain rfl := List.mem_singleton.mp mem
             exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by have := S.framed.fit; rw [S.framed.space.stack]; omega_using [this])
               S.framed.space.scratch.nowrap (by
                 rw [S.framed.space.stack]
                 rcases S.framed.separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h])))
           (by decide)).trans S.framed.space.len⟩, eA⟩)
    | (obtain ⟨Sx, -, -, eA, Fx, Kx⟩ := wp_result (framed_ok T.framed.space.scratch T.framed.space.width
          T.framed.space.widthBound T.framed.space.space T.framed.space.len rfl T.eValue positive
          (by rw [T.framed.space.stack]; exact T.framed.fit) (by rw [T.framed.space.stack]; exact T.framed.separate)) G
       exact ⟨⟨Sx, (Kx.1 .esp (by decide)).trans T.framed.space.stack, T.framed.space.width,
         T.framed.space.widthBound, T.framed.space.space,
         (Fx.readW (r := ⟨workspace.setWidth 64, size⟩)
           (Offset.contains_base _ (by have := slot5_lo w; have := T.framed.space.space; omega_arith)
             (by have := T.framed.space.scratch.nowrap; omega_using []))
           (by
             intro r mem; obtain rfl := List.mem_singleton.mp mem
             exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by have := T.framed.fit; rw [T.framed.space.stack]; omega_using [this])
               T.framed.space.scratch.nowrap (by
                 rw [T.framed.space.stack]
                 rcases T.framed.separate with h | h; exact Or.inl h; exact Or.inr (by omega_using [h])))
           (by decide)).trans T.framed.space.len⟩, eA⟩)

theorem gcd_trace {workspace p : BitVec 32} {size w exponent : Nat} (odd : exponent % 2 = 1) :
    RelCT isa (fun s t => (Space workspace p size w s ∧ Mod64.exponentValue s.mem (workspace.setWidth 64) 128 = exponent) ∧
        (Space workspace p size w t ∧ Mod64.exponentValue t.mem (workspace.setWidth 64) 128 = exponent))
      (.seq (.block (VG.Impl.RsaKeyGen.X86.Gcd64.setup 128)) VG.Impl.RsaKeyGen.X86.Gcd64.code)
      (fun u z => Space workspace p size w u ∧ Space workspace p size w z) := by
  have raw := RelCT.seq (VG.Proof.RsaKeyGen.X86.Gcd64.setup_trace 128) VG.Proof.RsaKeyGen.X86.Gcd64.code_trace
  intro s t tr ur u z ⟨⟨S, eS⟩, ⟨T, eT⟩⟩ E G
  have agree : VG.X86.Taint.Agree (VG.Proof.Mont.X86.Dynamic.workspaceTaint false) s t :=
    agree_regs (rs := [.edi]) fun r mem => by
      obtain rfl := List.mem_singleton.mp mem; exact S.workspace.trans T.workspace.symm
  have keep {x y : State} {tr : List Leak} (X : Space workspace p size w x)
      (ex : Mod64.exponentValue x.mem (workspace.setWidth 64) 128 = exponent)
      (EX : Exec isa (.seq (.block (VG.Impl.RsaKeyGen.X86.Gcd64.setup 128)) VG.Impl.RsaKeyGen.X86.Gcd64.code) x tr y) :
      Space workspace p size w y := by
    obtain ⟨Sy, L, K⟩ := wp_result (gcd_keep_ok X.scratch X.width X.space (by rw [ex]; exact odd)) EX
    exact X.keep K (by decide) (by decide) L
  exact ⟨(raw _ _ _ _ _ _ agree E G).1, keep S eS E, keep T eT G⟩

theorem restore_trace {workspace p : BitVec 32} {size w : Nat} :
    RelCT isa (fun s t => Space workspace p size w s ∧ Space workspace p size w t) restore
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := by
  unfold restore
  have setupRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block restoreSetup)
      (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have setup := publish (X := Space workspace p size w) (Y := CopyIn workspace p size w (slot w 5) 256)
    [.esp, .edi, .ebp, .ebx, .esi, .ecx] (copyRegs workspace p w (slot w 5) 256) (fun _ _ S T => S.agree T)
    setupRaw (fun s S => ?_)
  rotate_left
  · have header := S.header
    refine WP.mono (restoreSetup_ok S.scratch S.widthBound (by omega_using [header]) S.len) fun d ⟨K, M, ebx, ebp, esi, ecx⟩ => ?_
    have Sd : Space workspace p size w d := S.keep K (by decide) (by decide) (by rw [M])
    have regs : ∀ r ∈ [Reg.esp, .edi, .ebp, .ebx, .esi, .ecx], d.gpr r = copyRegs workspace p w (slot w 5) 256 r := by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Sd.stack
      · exact Sd.workspace
      · rw [ebp, S.workspace]; rfl
      · rw [ebx, S.workspace]; rfl
      · apply BitVec.eq_of_toNat_eq; rw [esi]; change 2 * w = (BitVec.ofNat 32 (2 * w)).toNat
        rw [BitVec.toNat_ofNat]; have := S.widthBound; omega_using [esi]
      · exact ecx
    exact ⟨⟨Sd, regs⟩, regs⟩
  have loop := copy_trace (workspace := workspace) (p := p) (size := size) (w := w) (src := slot w 5) (dst := 256)
    fun h => by have := slot5_ge w; exact ⟨h, by omega_using [h, this], Or.inl (by omega_using [this]), by omega_using []⟩
  have inc : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (VG.Impl.RsaKeyGen.X86.LowWord.increment 256)) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel)
  exact RelCT.seq setup (RelCT.seq loop (inc.mono (fun _ _ H => H.2) (fun _ _ H => H)))

theorem general_trace {workspace p : BitVec 32} {size w c d exponent : Nat} (odd : exponent % 2 = 1) :
    RelCT isa (fun s t => GeneralIn workspace p size w c exponent s ∧ GeneralIn workspace p size w d exponent t)
      general (fun _ _ => True) := by
  unfold general
  have result : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block VG.Impl.RsaKeyGen.X86.Gcd64.result)
      (fun _ _ => True) :=
    (VG.Proof.RsaKeyGen.X86.Gcd64.result_trace.mono (fun _ _ H => VG.X86.Taint.le_sound (by decide) H)
      (fun _ _ _ => trivial))
  exact RelCT.seq array_framed_trace (RelCT.assoc (RelCT.seq (gcd_trace odd) (RelCT.seq restore_trace result)))

end VG.Proof.RsaKeyGen.X86.ExponentRt

end

end


/-! # Both exponent paths derive their public geometry from the same candidate input -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

structure TimingInput (workspace p : BitVec 32) (size w candidate exponent : Nat) (s : State) : Prop where
  input : Input (workspace.setWidth 64) size w candidate exponent s
  stack : s.gpr .esp = p
  len : s.mem.readW (off (workspace.setWidth 64) 4) 32 = BitVec.ofNat 32 (8 * w)

theorem TimingInput.workspace {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) : s.gpr .edi = workspace := by
  apply BitVec.eq_of_toNat_eq
  rw [S.input.scratch.edi_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans workspace.isLt (by decide : 2 ^ 32 < 2 ^ 64))]

theorem TimingInput.keepReadonly {workspace p : BitVec 32} {size w candidate exponent : Nat} {s t : State}
    (S : TimingInput workspace p size w candidate exponent s) (M : t.mem = s.mem) (K : Keeps [.eax] s t) :
    TimingInput workspace p size w candidate exponent t :=
  ⟨S.input.keepReadonly M K, (K.1 .esp (by decide)).trans S.stack, by rw [M]; exact S.len⟩

theorem TimingInput.framed {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) : ExponentRt.Framed workspace p size w s :=
  ⟨⟨S.input.scratch, S.stack, S.input.width, S.input.widthBound, S.input.space, S.len⟩,
    by rw [← S.stack]; exact S.input.fit, by rw [← S.stack]; exact S.input.separate⟩

theorem TimingInput.general {workspace p : BitVec 32} {size w candidate exponent : Nat} {s : State}
    (S : TimingInput workspace p size w candidate exponent s) (odd : exponent % 2 = 1) :
    ExponentRt.GeneralIn workspace p size w candidate exponent s :=
  ⟨S.framed, S.input.saved, S.input.exponentEq, odd⟩

end VG.Proof.RsaKeyGen.X86.ExponentFilter

end

end

/-! # Public exponent bytes enter filtering with one shared native value -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.CandidateExponent
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PublicContext

structure Initial (workspace p e : BitVec 32) (size w candidate len exponent : Nat) (s : State) : Prop where
  scratch : Scr s (workspace.setWidth 64) size
  stack : s.gpr .esp = p
  width : 4 ≤ w
  widthBound : w ≤ 64
  space : slot w 5 + 8 * w ≤ size
  candidateEq : val32 s.mem (workspace.setWidth 64) (slot w 0) (2 * w) = candidate
  large : 1 < candidate
  odd : candidate % 2 = 1
  pointer : s.mem.readW (off (workspace.setWidth 64) 12) 32 = e
  length : w32 s.mem (workspace.setWidth 64) 16 = len
  ePositive : 0 < len
  eBound : len ≤ 8
  eFit : e.toNat + len ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (e.setWidth 64) len
  separateE : (⟨e.setWidth 64, len⟩ : Region).Disjoint ⟨workspace.setWidth 64, size⟩
  exponentEq : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (e.setWidth 64) len) = exponent
  fit : 40 ≤ p.toNat
  separateStack : p.toNat ≤ (workspace.setWidth 64).toNat ∨ (workspace.setWidth 64).toNat + size + 40 ≤ p.toNat
  outLen : s.mem.readW (off (workspace.setWidth 64) 4) 32 = BitVec.ofNat 32 (8 * w)

theorem Initial.header {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) : 256 ≤ size := by
  have space := S.space
  have width := S.width
  unfold slot stride VG.Impl.Bignum.hdrBytes at space
  omega_using [space]

theorem Initial.savedLo {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) : 400 ≤ slot w 5 := by
  have width := S.width
  unfold slot stride VG.Impl.Bignum.hdrBytes
  omega_using [width]

theorem Initial.spaceRt {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) : ExponentRt.Space workspace p size w s :=
  ⟨S.scratch, S.stack, S.width, S.widthBound, S.space, S.outLen⟩

theorem Initial.save_ok {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) :
    WP isa VG.Impl.RsaKeyGen.X86.ExponentRt.save s fun t =>
      Scr t (workspace.setWidth 64) size ∧ Outside (workspace.setWidth 64) (slot w 5) (8 * w) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (ExponentRt.save_ok S.scratch S.width S.widthBound S.space S.outLen
    (by rw [S.candidateEq]; exact S.odd)) fun t ⟨_, O, K⟩ => ?_
  exact ⟨S.scratch.of_keeps K (by decide), O, K⟩

theorem Initial.prepare_ok {workspace p e : BitVec 32} {size w candidate len exponent : Nat} {s : State}
    (S : Initial workspace p e size w candidate len exponent s) :
    WP isa (.seq VG.Impl.RsaKeyGen.X86.ExponentRt.save VG.Impl.RsaKeyGen.X86.ExponentImport.code) s
      (ExponentFilter.TimingInput workspace p size w candidate exponent) := by
  refine WP.mono (ExponentRt.prepare_ok S.scratch S.width S.widthBound S.space S.candidateEq S.large S.odd
    S.pointer S.length S.ePositive S.eBound S.eFit S.readable S.separateE
    (by rw [S.stack]; exact S.fit) (by rw [S.stack]; exact S.separateStack) S.outLen) fun t ⟨I, _, _, K, L⟩ => ?_
  rw [S.exponentEq] at I
  exact ⟨I, (K.1 .esp (by decide)).trans S.stack, L⟩

end VG.Proof.RsaKeyGen.X86.CandidateExponent

end

end

/-! # Native candidate timing shares public pointers and exponent bytes across secret inputs -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86

structure InputPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop where
  left : Input E eBytes pBytes rBytes s
  right : Input E eBytes qBytes sBytes t

structure DrawnPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop where
  left : Drawn E eBytes pBytes rBytes s
  right : Drawn E eBytes qBytes sBytes t

theorem InputPair.agree {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte} {s t : State}
    (P : InputPair E eBytes pBytes qBytes rBytes sBytes s t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact P.left.stack.trans P.right.stack.symm
  · exact BitVec.eq_of_toNat_eq (P.left.scratch.edi_toNat.trans P.right.scratch.edi_toNat.symm)

theorem DrawnPair.inputs {E : Environment} {eBytes pBytes qBytes rBytes sBytes : List Byte} {s t : State}
    (P : DrawnPair E eBytes pBytes qBytes rBytes sBytes s t) : InputPair E eBytes pBytes qBytes rBytes sBytes s t :=
  ⟨P.left.input, P.right.input⟩

theorem Drawn.exponentInitial {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s : State}
    (D : Drawn E eBytes pBytes entropy s) :
    CandidateExponent.Initial E.workspace E.p E.exponent E.size E.width (candidateValue E entropy)
      E.exponentLength (Spec.Rsa.os2ip eBytes) s := by
  refine ⟨D.input.scratch, D.input.stack, v.width_bounds.1, v.width_bounds.2, v.slotFit (by decide), D.candidate,
    by have := candidate_large v entropy; omega_using [this], candidate_odd v entropy, D.input.exponent_eq,
    D.input.exponentLength_eq v, by have := v.exponentLength.1; omega_using [this], v.exponentLength.2, v.exponentFit,
    D.input.memory.exponentRead, v.readWorkspace List.mem_cons_self, ?_, by have := v.low; omega_using [this], ?_, ?_⟩
  · rw [D.input.memory.exponentBytes]
  · change E.p.toNat ≤ E.base.toNat ∨ E.base.toNat + E.size + 40 ≤ E.p.toNat
    rcases v.workspaceStack with h | h
    · exact Or.inl h
    · exact Or.inr (by omega_using [h])
  · change s.mem.readW (off E.base (4 * 1)) 32 = _
    rw [D.input.header 1 (by decide), v.length_eq]; rfl

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.MrExponentRt.Timing`, which only this module used -/

section

/-! # Miller–Rabin's exponent at the run-time width reads the same addresses in every run

The pointers and counts come from the prepared header, which the taint
analysis takes for secret: each run computes them from the same header, so
they agree once correctness gives their values, and the loops are then
checked with them public.
-/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.MrExponentRt
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- Prepared, for some candidate. -/
def Prepared (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s

/-- The workspace pointer, from the header's base. -/
theorem edi_value {g : Geometry} {s : State} (C : Context g s) : s.gpr .edi = BitVec.ofNat 32 g.W.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [C.base, BitVec.toNat_ofNat, Nat.add_zero]

theorem prepared_pair {g : Geometry} {capacity : Nat} {p : BitVec 32} {s t : State}
    (S : Prepared g capacity p s) (T : Prepared g capacity p t) : Pair g [.edi] s t := by
  obtain ⟨_, S⟩ := S
  obtain ⟨_, T⟩ := T
  refine ⟨S.context, T.context, agree_regs fun r mem => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.caller.sp.trans T.caller.sp.symm
  · exact (edi_value S.context).trans (edi_value T.context).symm

/-- In the scan's frame. -/
def Framed (g : Geometry) (capacity : Nat) (p : BitVec 32) (a : State) : Prop :=
  ∃ s, Prepared g capacity p s ∧ a = allocFrame 20 s

/-- Ready to scan: `ebp` at array 5 and `edi` its pairs. -/
structure Scanning (g : Geometry) (p : BitVec 32) (a : State) : Prop where
  ws : Ws a g.W g.L
  stack : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) a
  ebp : PtrAt a g.W .ebp (g.array 5)
  count : (a.gpr .edi).toNat = g.w

theorem scan_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) scan
      (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) := by
  refine withRuns (R := fun _ _ => True) ?_ fun s ⟨c, S⟩ => WP.mono (scan_ok v S) fun t ⟨_, F, K⟩ =>
    ⟨c, (Ready.keepStack v S K (by decide) (by decide) F).1⟩
  unfold scan
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  obtain setupRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block scanSetup) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  obtain setup := seg (X := Framed g capacity p) (Y := Scanning g p) [.esp, .edi]
    (fun r => if r = .esp then p - 20#32 else BitVec.ofNat 32 g.W.toNat) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, S.caller.sp]; rfl
      · rw [allocFrame_gpr _ _ (by decide)]; exact edi_value S.context) setupRaw (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      have sp := S.caller.sp
      obtain St : VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) (allocFrame 20 s) := by
        rw [← sp]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; have := S.caller.low; omega_using [this])
      have C := S.context
      obtain Ci : Context g (allocFrame 20 s) :=
        ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
          C.width, C.stride, C.pointers⟩
      exact WP.mono (scanSetup_ok v Ci St) fun a ⟨_, _, P, count, _, _, K⟩ =>
        ⟨Ci.ws.of_keeps K, St.keep K (by decide), P, count⟩)
  obtain loopRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .edi])) (.loop (.block pairStep) .ne)
      (fun _ _ => True) :=
    (erased_relCT (.loop (.block pairStep) .ne) (.loop (.block pairStep) .ne)
      (VG.Taint.hintOf taint (τr [.esp, .ebp, .edi]) (Code.erase (.loop (.block pairStep) .ne)))
      (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .ebp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have positive := v.minWidth
  have maxWidth := v.maxWidth
  obtain fit := v.arrayFit (j := 5) (by decide)
  unfold Geometry.words at fit
  obtain loop := seg (X := Scanning g p) (Y := fun a => VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) a)
    [.esp, .ebp, .edi]
    (fun r => if r = .esp then p - 20#32 else if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 5)
      else BitVec.ofNat 32 g.w) (fun a A => by
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact A.stack.sp
      · exact ptr_value A.ebp
      · change a.gpr .edi = BitVec.ofNat 32 g.w
        apply BitVec.eq_of_toNat_eq
        rw [A.count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [maxWidth])]) loopRaw
    (fun a A => WP.mono (scanLoop_ok A.ws (by omega_using [positive]) (by omega_using [fit]) A.ebp A.count) fun _ ⟨_, _, K⟩ =>
      A.stack.keep K (by decide))
  obtain restoreRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edi (.mem (VG.Impl.Mont.X86.at_ .esp 0))])
      (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  obtain restore := seg (X := fun a => VG.Proof.RsaKeyGen.X86.Sieve.StackContext (p - 20#32) a)
    (Y := fun _ => True) [.esp] (fun _ => p - 20#32) (fun a A r mem => by
      obtain rfl := List.mem_singleton.mp mem
      exact A.sp) restoreRaw (fun a A => wp_movS (A.read 0 (by decide)) fun _ _ _ => WP.block_nil trivial)
  exact (RelCT.seq setup (RelCT.seq loop restore)).mono
    (fun a b ⟨s₁, s₂, ⟨S₁, S₂⟩, e₁, e₂⟩ => ⟨⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩) (fun _ _ _ => trivial)

/-- Before a pass: its top word zero and a mask in `ecx`. -/
def Halving (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ w32 s.mem g.W (g.array 27 + 4 * g.words) = 0 ∧ ∃ choice, s.gpr .ecx = cmask choice

/-- After a pass: `ebp` past array 27. -/
def Halved (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ w32 s.mem g.W (g.array 27 + 4 * g.words) = 0 ∧
    PtrAt s g.W .ebp (g.array 27 + 4 * g.words)

/-- The stack pointer and the workspace pointer, the same in every run. -/
def baseRegs (g : Geometry) (p : BitVec 32) (extra : Reg → BitVec 32) : Reg → BitVec 32
  | .esp => p
  | .edi => BitVec.ofNat 32 g.W.toNat
  | r => extra r

theorem base_vals {g : Geometry} {c capacity : Nat} {p : BitVec 32} {s : State} (S : Ready g c capacity p s)
    (extra : Reg → BitVec 32) : ∀ r ∈ [Reg.esp, .edi], s.gpr r = baseRegs g p extra r := by
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact S.caller.sp
  · exact edi_value S.context

theorem markerBlock_keep {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {s : State}
    (S : Prepared g capacity p s) :
    WP isa (.block (VG.Impl.RsaKeyGen.X86.LowBit.code ++ VG.Impl.RsaKeyGen.X86.Exponent.saveMarker)) s
      (Prepared g capacity p) := by
  obtain ⟨c, S⟩ := S
  refine WP.block_append (WP.mono (VG.Proof.RsaKeyGen.X86.LowBit.code_ok s) fun a ⟨_, Ma, Ka⟩ => ?_)
  obtain Ksa : Keeps VG.Proof.RsaKeyGen.X86.Exponent.clob s a := Ka.mono (by decide)
  have head := v.headerFit
  refine WP.mono (VG.Proof.RsaKeyGen.X86.Header.storePair_ok (S.scratch.of_keeps Ksa (by decide)) (offset := 136)
    (by omega_using [head])) fun t ⟨_, Ot, Kt⟩ => ?_
  obtain O : Outside g.W 136 8 s.mem t.mem := by rw [← Ma]; exact Ot
  exact ⟨c, VG.Proof.RsaKeyGen.X86.Exponent.ready_keep v S (outs_prepared O ⟨(136, 8), by
    unfold VG.Proof.RsaKeyGen.X86.Exponent.preparedRanges VG.Proof.RsaKeyGen.X86.Exponent.ranges
    exact List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩) (Ksa.trans (Kt.mono (by decide)))⟩

theorem marker_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) marker
      (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) := by
  unfold marker
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (VG.Impl.RsaKeyGen.X86.LowBit.code ++ VG.Impl.RsaKeyGen.X86.Exponent.saveMarker)) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  exact RelCT.seq (scan_trace v) (seg [.esp, .edi] (baseRegs g p fun _ => 0) (fun _ ⟨_, S⟩ => base_vals S _) raw
    fun _ S => markerBlock_keep v S)

theorem copyTops_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) copyTops
      (fun s t => Halving g capacity p s ∧ Halving g capacity p t) := by
  obtain topsRaw : RelCT isa (VG.X86.Taint.Agree (roundTaint copyRegisters))
      (.block [.mov .eax (.imm 0), .store (VG.Impl.Mont.X86.at_ .ebx 0) .eax, .store (VG.Impl.Mont.X86.at_ .ebp 0) .eax,
        .mov .ecx (.imm (BitVec.allOnes 32))]) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (roundTaint copyRegisters)) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  refine withRuns (R := fun _ _ => True) ?_ fun s ⟨c, S⟩ => WP.mono (copyTops_ok v S)
    fun t ⟨T, _, top, mask, _, _, _⟩ => ⟨c, T, top, true, mask⟩
  unfold copyTops
  exact RelCT.seq ((copy_trace v _ 0 (by decide) (by decide)).mono (fun _ _ ⟨S, T⟩ => prepared_pair S T)
    (fun _ _ H => H)) topsRaw

theorem half_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Halving g capacity p s ∧ Halving g capacity p t) half
      (fun s t => Halved g capacity p s ∧ Halved g capacity p t) := by
  obtain loopRaw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.esi, .ebp, .edi])) (.loop (.block halfStep) .ne)
      (fun _ _ => True) :=
    (erased_relCT (.loop (.block halfStep) .ne) (.loop (.block halfStep) .ne)
      (VG.Taint.hintOf taint (roundTaint [.esi, .ebp, .edi]) (Code.erase (.loop (.block halfStep) .ne)))
      (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (roundTaint [.esi, .ebp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  refine withRuns (R := fun _ _ => True) ?_ fun s ⟨c, S, top, choice, mask⟩ =>
    WP.mono (halfStage_ok v S top mask) fun t ⟨T, _, topT, _, P, _, _⟩ => ⟨c, T, topT, P⟩
  unfold half
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    ((pointer_pair_relCT v .ebp 27 (by decide) (by decide) [.edi] (by decide)).mono
      (fun _ _ ⟨⟨c₁, S, _⟩, ⟨c₂, T, _⟩⟩ => prepared_pair ⟨c₁, S⟩ ⟨c₂, T⟩) (fun _ _ H => H))
    (words_pair_relCT v [.ebp, .edi] (by decide)))) ?_
  exact loopRaw.mono (fun _ _ H => H.2.2) (fun _ _ H => H)

theorem halfIf_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} (j : Nat) :
    RelCT isa (fun s t => Halved g capacity p s ∧ Halved g capacity p t) (halfIf j)
      (fun s t => Halved g capacity p s ∧ Halved g capacity p t) := by
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (VG.Impl.RsaKeyGen.X86.SigMask.code VG.Impl.RsaKeyGen.X86.Exponent.markerOffset j))
      (fun _ _ => True) :=
    (erased_relCT (.block (VG.Impl.RsaKeyGen.X86.SigMask.code VG.Impl.RsaKeyGen.X86.Exponent.markerOffset j))
      (.block (VG.Impl.RsaKeyGen.X86.SigMask.code 136 1)) (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp, .edi]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have head := v.headerFit
  obtain sig := seg (X := Halved g capacity p) (Y := Halving g capacity p) [.esp, .edi] (baseRegs g p fun _ => 0)
    (fun _ ⟨_, S, _⟩ => base_vals S _) raw fun s ⟨c, S, top, _⟩ => by
      refine WP.mono (VG.Proof.RsaKeyGen.X86.SigMask.code_ok S.scratch
        (by unfold VG.Impl.RsaKeyGen.X86.Exponent.markerOffset; omega_using [head])) fun t ⟨mask, M, K⟩ => ?_
      obtain outs : Outs g.W (VG.Proof.RsaKeyGen.X86.Exponent.preparedRanges g) s.mem t.mem := by
        rw [M]; exact Outs.refl _ _ _
      exact ⟨c, VG.Proof.RsaKeyGen.X86.Exponent.ready_keep v S outs (K.mono (by decide)), by rw [M]; exact top, _, mask⟩
  unfold halfIf
  exact RelCT.seq sig (half_trace v)

theorem finish_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Halved g capacity p s ∧ Halved g capacity p t) (.block finish) (fun _ _ => True) := by
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp])) (.block finish) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  refine (seg (X := Halved g capacity p) (Y := fun _ => True) [.esp, .edi, .ebp]
    (baseRegs g p fun _ => BitVec.ofNat 32 (g.W.toNat + (g.array 27 + 4 * g.words))) (fun s ⟨_, S, _, P⟩ => ?_) raw
    fun s ⟨_, S, _, P⟩ => WP.mono (finish_ok v S.scratch P) fun _ _ => trivial).mono (fun _ _ H => H) fun _ _ _ => trivial
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact S.caller.sp
  · exact edi_value S.context
  · exact ptr_value P

/-- Miller–Rabin's exponent at the run-time width leaks no more than the
prepared header. -/
theorem code_trace {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} :
    RelCT isa (fun s t => Prepared g capacity p s ∧ Prepared g capacity p t) code (fun _ _ => True) := by
  unfold code
  exact RelCT.seq (marker_trace v) (RelCT.seq (copyTops_trace v) (RelCT.seq (half_trace v)
    (RelCT.seq (halfIf_trace v 1) (RelCT.seq (halfIf_trace v 2) (RelCT.seq (halfIf_trace v 3) (finish_trace v))))))

end VG.Proof.RsaKeyGen.X86.MrExponentRt

end

end

/-! ### `RsaKeyGen.X86.PrepareRt.ConstantsTiming`, which only this module used -/

section

/-! # Montgomery one and minus one at the run-time width read the same addresses in every run -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.PrepareRt
open VG.Proof.RsaKeyGen.X86 (seg withRuns rawBlock ptr_value)
open VG.Proof.RsaKeyGen.X86.Sieve (StackContext)
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready)

/-- About to subtract: `ebp` at the candidate, `ebx` at array 9, `edi` at array 10, `edx` their octets. -/
structure Subtracting (g : Geometry) (q : BitVec 32) (s : State) : Prop where
  ws : Ws s g.W g.L
  stack : StackContext q s
  ebp : PtrAt s g.W .ebp (g.array 0)
  ebx : PtrAt s g.W .ebx (g.array 9)
  edi : PtrAt s g.W .edi (g.array 10)
  edx : (s.gpr .edx).toNat = 4 * g.words
  ecx : s.gpr .ecx = cmask false

theorem subtractArgs_ok {g : Geometry} (v : g.Valid) {a : State} {q : BitVec 32} (C : Context g a)
    (St : StackContext q a) (apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨q.setWidth 64, 20⟩) :
    WP isa (.block subtractArgs) a (Subtracting g q) := by
  obtain ⟨-, -, -, words⟩ := WitnessRt.fits v
  have bound := v.maxWidth
  unfold subtractArgs
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (St.store 0 (by decide) .edi) fun e ⟨_, Oe, Ke, Se⟩ => ?_)
  obtain ⟨_, We⟩ := frame_workspace C.ws.nowrap apart (by decide) Oe
  obtain Ce := Context.keepWork v C Ke (by decide) We fun _ mem => nomatch mem
  refine WP.block_append (WP.mono (WitnessRt.ptr_short v Ce 0 (by decide) .ebp) fun f1 ⟨Q1, N1, L1⟩ => ?_)
  obtain Cf1 := Ce.keepMem L1 (by decide) N1
  refine WP.block_append (WP.mono (Cf1.ptr v 9 (by decide) .ebx (by decide) (by decide)) fun f2 ⟨Q2, N2, L2⟩ => ?_)
  obtain Cf2 := Cf1.keepMem L2 (by decide) N2
  refine WP.block_append (WP.mono (Cf2.ptr v 10 (by decide) .eax (by decide) (by decide)) fun f3 ⟨Q3, N3, L3⟩ => ?_)
  obtain Cf3 := Cf2.keepMem L3 (by decide) N3
  refine WP.block_append (WP.mono (WitnessRt.draw_ok v Cf3) fun f4 ⟨D4, N4, L4⟩ => ?_)
  refine wp_movS rfl fun f5 F5 _ => wp_movS rfl fun f F _ => WP.block_nil ?_
  obtain Lf : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] e f :=
    (((((L1.mono (by decide)).widen L2).widen L3).widen L4).widen F5.keeps).widen F.keeps
  refine ⟨Ce.ws.of_keeps Lf, Se.keep Lf (by decide), ?_, ?_, ?_, ?_, F.gpr⟩
  · rw [PtrAt, F.other .ebp (by decide), F5.other .ebp (by decide), L4.1 .ebp (by decide), L3.1 .ebp (by decide),
      L2.1 .ebp (by decide)]; exact Q1
  · rw [PtrAt, F.other .ebx (by decide), F5.other .ebx (by decide), L4.1 .ebx (by decide), L3.1 .ebx (by decide)]
    exact Q2
  · rw [PtrAt, F.other .edi (by decide), F5.gpr, L4.1 .eax (by decide)]; exact Q3
  · rw [F.other .edx (by decide), F5.other .edx (by decide), D4, BitVec.toNat_ofNat]; omega_using [words, bound]

section
variable {g : Geometry} {capacity : Nat} {p : BitVec 32}

theorem subtract_trace (v : g.Valid) :
    RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) subtract (fun _ _ => True) := by
  obtain ⟨-, -, many, -⟩ := WitnessRt.fits v
  obtain fit0 := v.arrayFit (j := 0) (by decide)
  obtain fit9 := v.arrayFit (j := 9) (by decide)
  obtain fit10 := v.arrayFit (j := 10) (by decide)
  unfold subtract
  refine RelCT.frameAlloc (R := fun _ _ => True) ?_
  intro a b tr ur u z H E G
  obtain ⟨s₁, s₂, ⟨S₁, S₂⟩, e₁, e₂⟩ := H
  obtain apart : (⟨g.W, g.L⟩ : Region).Disjoint ⟨(p - 20#32).setWidth 64, 20⟩ := by
    obtain ⟨_, S⟩ := S₁
    exact S.caller.stackFar.sub_right (below_sub (a := 20) (by decide) S.caller.low)
  obtain setup := seg (X := Framed g capacity p) (Y := Subtracting g (p - 20#32)) (c := .block subtractArgs)
    [.esp, .edi] (fun r => if r = .esp then p - 20#32 else BitVec.ofNat 32 g.W.toNat) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · rw [allocFrame_esp, S.caller.sp]; rfl
      · rw [allocFrame_gpr (q := .edi) _ _ (by decide)]; exact edi_at S.context)
    (rawBlock (by decide +kernel)) (fun a ⟨s, ⟨_, S⟩, eq⟩ => by
      subst eq
      have sp := S.caller.sp
      obtain St : StackContext (p - 20#32) (allocFrame 20 s) := by
        rw [← sp]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context (by rw [sp]; have := S.caller.low; omega_using [this])
      have C := S.context
      obtain Ci : Context g (allocFrame 20 s) :=
        ⟨⟨List.mem_cons_of_mem _ C.ws.wr, C.ws.nowrap⟩, by rw [PtrAt, allocFrame_gpr _ _ (by decide)]; exact C.base,
          C.width, C.stride, C.pointers⟩
      exact subtractArgs_ok v Ci St apart)
  obtain loop := seg (X := Subtracting g (p - 20#32)) (Y := StackContext (p - 20#32)) [.ebp, .ebx, .edi, .edx]
    (fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 0)
      else if r = .ebx then BitVec.ofNat 32 (g.W.toNat + g.array 9)
      else if r = .edi then BitVec.ofNat 32 (g.W.toNat + g.array 10) else BitVec.ofNat 32 (4 * g.words))
    (fun s S r mem => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl
      · exact ptr_value S.ebp
      · exact ptr_value S.ebx
      · exact ptr_value S.edi
      · exact nat_at S.edx) reduceLoop_raw (fun s S =>
      WP.mono (VG.Proof.Bignum.X86.PublicRt.reduceLoop_ok S.ws (a := g.array 0) (m := g.array 9) (d := g.array 10)
        (N := g.words) (by omega_using [many]) fit0 fit9 fit10 (Or.inr (g.arrayBefore (by decide)))
        (Or.inr (g.arrayBefore (by decide))) S.ebp S.ebx S.edi S.edx S.ecx) fun _ ⟨_, _, _, K⟩ =>
        S.stack.keep K (by decide))
  obtain restore := seg (X := StackContext (p - 20#32)) (Y := fun _ => True) (c := .block [.mov .edi (.mem (VG.Impl.Mont.X86.at_ .esp 0))])
    [.esp] (fun _ => p - 20#32) (fun a A r mem => by obtain rfl := List.mem_singleton.mp mem; exact A.sp)
    (rawBlock (by decide +kernel)) (fun a A => wp_movS (A.read 0 (by decide)) fun _ _ _ => WP.block_nil trivial)
  exact ⟨(RelCT.seq setup (RelCT.seq loop restore) _ _ _ _ _ _ ⟨⟨s₁, S₁, e₁⟩, ⟨s₂, S₂, e₂⟩⟩ E G).1, trivial⟩

/-- About to multiply one by R² (array 4). -/
def OneSet (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  ∃ c, Ready g c capacity p s ∧ c % 2 = 1 ∧ val32 s.mem g.W (g.array 4) g.words < c

theorem constants_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56) (v : g.Valid) (length : g.L = 8 * capacity) :
    RelCT isa (fun s t => Constants.Input g capacity p s ∧ Constants.Input g capacity p t) (constants name mont)
      (fun _ _ => True) := by
  obtain fit4 := v.arrayFit (j := 4) (by decide)
  unfold constants
  obtain oneT : RelCT isa (fun s t => Constants.Input g capacity p s ∧ Constants.Input g capacity p t) one
      (fun u z => OneSet g capacity p u ∧ OneSet g capacity p z) :=
    withRuns ((one_trace v).mono (fun _ _ ⟨⟨c, S, _⟩, ⟨d, T, _⟩⟩ => ⟨⟨c, S⟩, ⟨d, T⟩⟩) (fun _ _ H => H))
      fun s ⟨c, S, odd, positive, r2⟩ => WP.mono (one_ok v S) fun _ ⟨T, _, O, _⟩ =>
        ⟨c, T, odd, by
          rw [O.val32 (Or.inl (g.arrayBefore (by decide))) (by have := S.scratch.nowrap; omega_using [fit4, this]), r2]
          exact Nat.mod_lt _ positive⟩
  obtain mulT : RelCT isa (fun s t => OneSet g capacity p s ∧ OneSet g capacity p t) (VG.Impl.MillerRabin.X86.mulY name mont 4)
      (fun u z => Held g capacity p u ∧ Held g capacity p z) :=
    withRuns ((mulY_relCT (p := p) (b := 4) verified noSp stack v length (by unfold Proof.Rsa.Mont.Operand; decide)).mono
      (fun s t ⟨⟨c, S, odd, lt⟩, ⟨d, T, odd', lt'⟩⟩ => ⟨held_pair ⟨c, S⟩ ⟨d, T⟩,
        ⟨S.context, ⟨c, S.modulus, odd, lt⟩, S.caller⟩, ⟨T.context, ⟨d, T.modulus, odd', lt'⟩, T.caller⟩⟩)
      (fun _ _ H => H))
      fun s ⟨c, S, odd, lt⟩ => WP.mono (mulY_ok verified noSp stack v S.context length S.modulus
        (by unfold Proof.Rsa.Mont.Operand; decide) odd lt S.caller.readLen (by rw [S.caller.sp]; exact S.caller.low)
        (by rw [S.caller.sp]; exact S.caller.stackFar)) fun b ⟨_, _, Kb, Cb, Mb, Fb⟩ => by
          rw [S.caller.sp] at Fb
          exact ⟨c, Cb, Mb, S.caller.keepFrame Kb (by decide) Fb, S.scratch.of_keeps Kb (by decide)⟩
  obtain copyT : RelCT isa (fun s t => Held g capacity p s ∧ Held g capacity p t) (VG.Impl.MillerRabin.X86.copy 9 6)
      (fun u z => Held g capacity p u ∧ Held g capacity p z) :=
    withRuns ((copy_relCT v 9 6 (by decide) (by decide)).mono (fun s t ⟨S, T⟩ => held_pair S T) (fun _ _ H => H))
      fun s ⟨c, S⟩ => WP.mono (Prepared.copy_ready v S 9 6 (by decide) (by decide) (by decide))
        fun _ ⟨T, _⟩ => ⟨c, T⟩
  exact RelCT.seq oneT (RelCT.seq mulT (RelCT.seq copyT (subtract_trace v)))

end

end VG.Proof.RsaKeyGen.X86.PrepareRt

end

end

/-! ### `RsaKeyGen.X86.WitnessRt.Timing`, which only this module used -/

section

/-! ### `RsaKeyGen.X86.WitnessRt.SampleTiming`, which only this module used -/

section

/-! # A witness drawn and sampled at the run-time width reads the same addresses in every run

The taint analysis takes what code reads from the workspace for secret, the
header's pointers too: the draw is checked in segments, each run holding the
same pointers and counts at a segment's start, which correctness gives
(`seg`). -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.WitnessRt
open VG.Proof.RsaKeyGen.X86.WitnessRound (Work)

/-- The public registers' values: `esp` at `p`, `edi` at the workspace, and
those `extra` gives. -/
def regs (g : Geometry) (p : BitVec 32) (extra : Reg → BitVec 32) (r : Reg) : BitVec 32 :=
  if r = .esp then p else if r = .edi then BitVec.ofNat 32 g.W.toNat else extra r

theorem edi_value {g : Geometry} {s : State} (C : Context g s) : s.gpr .edi = BitVec.ofNat 32 g.W.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [C.base, BitVec.toNat_ofNat, Nat.add_zero]

theorem toNat_value {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)]

section
variable {g : Geometry} {capacity : Nat} {p : BitVec 32}

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.context {s : State} (S : Work g capacity p s) : Context g s := by
  obtain ⟨_, D, _⟩ := S
  exact D.ready.context

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.sp {s : State} (S : Work g capacity p s) : s.gpr .esp = p := by
  obtain ⟨_, D, _⟩ := S
  exact D.ready.caller.sp

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.keep (v : g.Valid) {s t : State} (S : Work g capacity p s) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) (O : Outside g.W (g.array 6) (4 * g.words) s.mem t.mem) :
    Work g capacity p t := by
  obtain ⟨c, D, odd, large⟩ := S
  exact ⟨c, WitnessMont.data_outside v D O K edi esp, odd, large⟩

theorem _root_.VG.Proof.RsaKeyGen.X86.WitnessRound.Work.keepMem (v : g.Valid) {s t : State} (S : Work g capacity p s) {rs : List Reg} (K : Keeps rs s t)
    (edi : .edi ∉ rs) (esp : .esp ∉ rs) (M : t.mem = s.mem) : Work g capacity p t :=
  S.keep v K edi esp (by rw [M]; exact Outside.refl _ _ _ _)

/-- Every run holds the same `esp`, `edi` and, in `r`, the pointer at `x`. -/
theorem ptrSeg {X Y : State → Prop} {c : Prog isa} (r : Reg) (x : Nat) (notSp : r ≠ .esp) (notBase : r ≠ .edi)
    (work : ∀ s, X s → Work g capacity p s) (ptr : ∀ s, X s → PtrAt s g.W r x)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, r])) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  refine seg [.esp, .edi, r] (regs g p fun _ => BitVec.ofNat 32 (g.W.toNat + x)) (fun s S r' mem => ?_) raw run
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact (work s S).sp
  · exact edi_value (work s S).context
  · simp only [regs, notSp, notBase, ↓reduceIte]
    exact ptr_value (ptr s S)

/-- Every run holds the same `esp` and `edi`. -/
theorem baseSeg {X Y : State → Prop} {c : Prog isa} (work : ∀ s, X s → Work g capacity p s)
    (raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) c (fun _ _ => True))
    (run : ∀ s, X s → WP isa c s Y) :
    RelCT isa (fun s t => X s ∧ X t) c (fun u z => Y u ∧ Y z) := by
  refine seg [.esp, .edi] (regs g p fun _ => 0) (fun s S r mem => ?_) raw run
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact (work s S).sp
  · exact edi_value (work s S).context

/-- Prepared, with a pointer at `x` in `r`. -/
def At (g : Geometry) (capacity : Nat) (p : BitVec 32) (r : Reg) (x : Nat) (s : State) : Prop :=
  Work g capacity p s ∧ PtrAt s g.W r x

theorem ptr6_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block (VG.Impl.MillerRabin.X86.ptr .ebp 6))
      (fun u z => At g capacity p .ebp (g.array 6) u ∧ At g capacity p .ebp (g.array 6) z) :=
  baseSeg (fun _ S => S) (rawBlock (by decide +kernel)) fun s S =>
    WP.mono (ptr_short v S.context 6 (by decide) .ebp) fun _ ⟨P, M, K⟩ =>
      ⟨S.keepMem v K (by decide) (by decide) M, P⟩

/-! ## Frames of the blocks whose results the trace does not need -/

theorem lowerAt_frame {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x) (fit : x + 4 ≤ L) :
    WP isa (.block lowerAt) s fun t => t.mem = s.mem ∧ Keeps [.eax, .ebx] s t := by
  unfold lowerAt
  refine wp_movS (readSrc_ptr hw P (d := 0) (by omega_using [fit])) fun b B _ => wp_orS rfl fun c Cc =>
    wp_logicS (.inr rfl) rfl fun d D => wp_orS rfl fun e E => ?_
  refine wp_cmpi fun f F cf _ => wp_sbb_self cf fun h H => wp_logicS (.inr rfl) rfl fun i I =>
    wp_movS rfl fun j J _ => wp_logicS (.inl rfl) rfl fun t T => WP.block_nil ?_
  exact ⟨by rw [T.mem, J.mem, I.mem, H.mem, F.mem, E.mem, D.mem, Cc.mem, B.mem],
    (((((((((B.keeps.mono (by decide)).widen Cc.keeps).widen D.keeps).widen E.keeps).trans
      (F.keeps _)).widen H.keeps).widen I.keeps).widen J.keeps).widen T.keeps)⟩

theorem fallbackLow_frame {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebp x)
    (fit : x + 4 ≤ L) :
    WP isa (.block fallbackLow) s fun t => Outside W x 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold fallbackLow
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B => wp_logicS (.inl rfl) rfl fun c C => ?_
  obtain Kc : Keeps [.ecx] s c := (A.keeps.widen B.keeps).widen C.keeps
  obtain Pc : PtrAt c W .ebp x := by rw [PtrAt, Kc.1 .ebp (by decide)]; exact P
  refine wp_orS (readSrc_ptr (hw.of_keeps Kc) Pc (d := 0) (by omega_using [fit])) fun d D => ?_
  obtain Kd : Keeps [.ecx] s d := Kc.widen D.keeps
  obtain wd := hw.of_keeps Kd
  obtain Pd : PtrAt d W .ebp x := by rw [PtrAt, Kd.1 .ebp (by decide)]; exact P
  refine wp_storeS (ea_ptr wd Pd (d := 0) (by omega_using [fit])) (ws_write wd (y := x + 0) (n := 4) (by omega_using [fit]))
    fun t T => WP.block_nil ⟨?_, Kd.widen (T.keeps [])⟩
  rw [T.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
  exact writeW32_outside _ _ _ (by have := hw.nowrap; omega_using [fit, this])

theorem fallbackHigh_frame {s : State} {W : Addr} {L x : Nat} (hw : Ws s W L) (P : PtrAt s W .ebx x)
    (fit : x + 4 ≤ L) :
    WP isa (.block fallbackHigh) s fun t => Outside W x 4 s.mem t.mem ∧ Keeps [.ecx] s t := by
  unfold fallbackHigh
  refine wp_movS rfl fun a A _ => wp_logicS (.inr rfl) rfl fun b B =>
    wp_logicS (.inl rfl) rfl fun c C => wp_logicS (.inr rfl) rfl fun d D => ?_
  obtain Kd : Keeps [.ecx] s d := ((A.keeps.widen B.keeps).widen C.keeps).widen D.keeps
  obtain Pd : PtrAt d W .ebx x := by rw [PtrAt, Kd.1 .ebx (by decide)]; exact P
  refine wp_logicS (.inl rfl) (readSrc_ptr (hw.of_keeps Kd) Pd (d := 0) (by omega_using [fit])) fun e E => ?_
  obtain Ke : Keeps [.ecx] s e := Kd.widen E.keeps
  obtain we := hw.of_keeps Ke
  obtain Pe : PtrAt e W .ebx x := by rw [PtrAt, Ke.1 .ebx (by decide)]; exact P
  refine wp_storeS (ea_ptr we Pe (d := 0) (by omega_using [fit])) (ws_write we (y := x + 0) (n := 4) (by omega_using [fit]))
    fun t T => WP.block_nil ⟨?_, Ke.widen (T.keeps [])⟩
  rw [T.mem, E.mem, D.mem, C.mem, B.mem, A.mem, Nat.add_zero]
  exact writeW32_outside _ _ _ (by have := hw.nowrap; omega_using [fit, this])

/-! ## The sampler's segments -/

theorem mark_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block mark)
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold mark
  exact RelCT.block_append (RelCT.seq (ptr6_trace v)
    (ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (markAt_ok S.1.context.ws S.2 (n := g.words) (by omega_using [many]) fit) fun _ ⟨_, _, O, K⟩ =>
        S.1.keep v K (by decide) (by decide) (O.mono (by omega_using []) (by omega_using [many]))))

/-- About to compare the witness with the candidate. -/
def Comparing (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Work g capacity p s ∧ PtrAt s g.W .esi (g.array 6) ∧ PtrAt s g.W .ebp (g.array 0) ∧
    (s.gpr .edx).toNat = 4 * g.words ∧ s.gpr .ecx = cmask false

theorem lessLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .esi, .ebp, .edx])) lessLoop
    (fun _ _ => True) :=
  (erased_relCT (σ := τr []) lessLoop lessLoop
    (VG.Taint.hintOf taint (τr [.esp, .edi, .esi, .ebp, .edx]) (Code.erase lessLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem less_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) less
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, below, many, words⟩ := fits v
  have bound := v.maxWidth
  have nowrap := v.headerFit
  unfold less
  refine RelCT.seq (R := fun u z => Comparing g capacity p u ∧ Comparing g capacity p z)
    (baseSeg (fun _ S => S) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (lessArgs_ok v S.context) fun _ ⟨esi, ebp, edx, ecx, M, K⟩ =>
        ⟨S.keepMem v K (by decide) (by decide) M, esi, ebp, edx, ecx⟩) ?_
  refine seg [.esp, .edi, .esi, .ebp, .edx] (regs g p fun r => if r = .esi then BitVec.ofNat 32 (g.W.toNat + g.array 6)
    else if r = .ebp then BitVec.ofNat 32 (g.W.toNat + g.array 0) else BitVec.ofNat 32 (4 * g.words))
    (fun s S r mem => ?_) lessLoop_raw fun s S => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact S.1.sp
    · exact edi_value S.1.context
    · exact ptr_value S.2.1
    · exact ptr_value S.2.2.1
    · exact toNat_value S.2.2.2.1
  · exact WP.mono (VG.Proof.Bignum.X86.PublicRt.compareLoop_ok S.1.context.ws (x := g.array 6) (y := g.array 0)
      (N := g.words) (by omega_using [many]) (by omega_using [fit]) (by omega_using [fit, below]) S.2.1 S.2.2.1 S.2.2.2.1 S.2.2.2.2) fun _ ⟨M, _, K⟩ =>
        S.1.keepMem v K (by decide) (by decide) M

theorem restore_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block restore)
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold restore
  exact RelCT.block_append (RelCT.seq (ptr6_trace v)
    (ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (restoreAt_ok S.1.context.ws S.2 (by omega_using [fit, many])) fun _ ⟨_, O, _, K⟩ =>
        S.1.keep v K (by decide) (by decide) (O.mono (by omega_using []) (by omega_using [many]))))

/-- About to scan the witness's words above its lowest. -/
def Scanning (g : Geometry) (capacity : Nat) (p : BitVec 32) (s : State) : Prop :=
  Work g capacity p s ∧ PtrAt s g.W .ebp (g.array 6 + 4) ∧ (s.gpr .ecx).toNat = g.words - 1 ∧ s.gpr .ebx = 0#32

theorem orLoop_raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi, .ebp, .ecx])) orLoop (fun _ _ => True) :=
  (erased_relCT (σ := τr []) orLoop orLoop (VG.Taint.hintOf taint (τr [.esp, .edi, .ebp, .ecx]) (Code.erase orLoop))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

theorem scan_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) scan
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, words⟩ := fits v
  unfold scan
  refine RelCT.seq (R := fun u z => Scanning g capacity p u ∧ Scanning g capacity p z)
    (baseSeg (fun _ S => S) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (scanArgs_ok v S.context) fun _ ⟨P, count, zero, M, K⟩ =>
        ⟨S.keepMem v K (by decide) (by decide) M, P, count, zero⟩) ?_
  refine seg [.esp, .edi, .ebp, .ecx] (regs g p fun r => if r = .ebp then BitVec.ofNat 32 (g.W.toNat + (g.array 6 + 4))
    else BitVec.ofNat 32 (g.words - 1)) (fun s S r mem => ?_) orLoop_raw fun s S => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl
    · exact S.1.sp
    · exact edi_value S.1.context
    · exact ptr_value S.2.1
    · exact toNat_value S.2.2.1
  · exact WP.mono (FrontRt.orLoop_ok S.1.context.ws (by omega_using [many]) (by omega_using [fit, many]) S.2.1 S.2.2.1 S.2.2.2) fun _ ⟨_, M, _, K⟩ =>
      S.1.keepMem v K (by decide) (by decide) M

theorem finish_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) (.block (lower ++ fallback))
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, words⟩ := fits v
  unfold lower fallback
  simp only [List.append_assoc]
  obtain lowerT : RelCT isa (fun s t => At g capacity p .ebp (g.array 6) s ∧ At g capacity p .ebp (g.array 6) t)
      (.block lowerAt) (fun u z => Work g capacity p u ∧ Work g capacity p z) :=
    ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (lowerAt_frame S.1.context.ws S.2 (by omega_using [fit, many])) fun _ ⟨M, K⟩ =>
        S.1.keepMem v K (by decide) (by decide) M
  obtain lowT : RelCT isa (fun s t => At g capacity p .ebp (g.array 6) s ∧ At g capacity p .ebp (g.array 6) t)
      (.block fallbackLow) (fun u z => At g capacity p .ebp (g.array 6) u ∧ At g capacity p .ebp (g.array 6) z) :=
    ptrSeg .ebp (g.array 6) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2) (rawBlock (by decide +kernel))
      fun s S => WP.mono (fallbackLow_frame S.1.context.ws S.2 (by omega_using [fit, many])) fun _ ⟨O, K⟩ =>
        ⟨S.1.keep v K (by decide) (by decide) (O.mono (by omega_using []) (by omega_using [many])), by
          rw [PtrAt, K.1 .ebp (by decide)]; exact S.2⟩
  obtain topT : RelCT isa (fun s t => At g capacity p .ebp (g.array 6) s ∧ At g capacity p .ebp (g.array 6) t)
      (.block fallbackTop) (fun u z => At g capacity p .ebx (g.array 6 + 4 * g.words - 4) u ∧
        At g capacity p .ebx (g.array 6 + 4 * g.words - 4) z) :=
    baseSeg (fun _ S => S.1) (rawBlock (by decide +kernel)) fun s S =>
      WP.mono (fallbackTop_ok v S.1.context S.2) fun _ ⟨P, M, K⟩ => ⟨S.1.keepMem v K (by decide) (by decide) M, P⟩
  obtain highT : RelCT isa (fun s t => At g capacity p .ebx (g.array 6 + 4 * g.words - 4) s ∧
      At g capacity p .ebx (g.array 6 + 4 * g.words - 4) t)
      (.block fallbackHigh) (fun u z => Work g capacity p u ∧ Work g capacity p z) :=
    ptrSeg .ebx (g.array 6 + 4 * g.words - 4) (by decide) (by decide) (fun _ S => S.1) (fun _ S => S.2)
      (rawBlock (by decide +kernel)) fun s S => WP.mono (fallbackHigh_frame S.1.context.ws S.2 (by omega_using [fit, many]))
        fun _ ⟨O, K⟩ => S.1.keep v K (by decide) (by decide) (O.mono (by omega_using [many]) (by omega_using [many]))
  exact RelCT.block_append (RelCT.seq (ptr6_trace v) (RelCT.block_append (RelCT.seq lowerT
    (RelCT.block_append (RelCT.seq (ptr6_trace v) (RelCT.block_append (RelCT.seq lowT
      (RelCT.block_append (RelCT.seq topT highT)))))))))

theorem sample_trace (v : g.Valid) :
    RelCT isa (fun s t => Work g capacity p s ∧ Work g capacity p t) sample
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  unfold sample
  exact RelCT.seq (mark_trace v) (RelCT.seq (less_trace v) (RelCT.seq (restore_trace v)
    (RelCT.seq (scan_trace v) (finish_trace v))))

/-! ## The witness's draw -/

/-- `Import.code`'s arguments set for the draw `input`. -/
def Importing (g : Geometry) (capacity : Nat) (p : BitVec 32) (input : Import.Geometry) (s : State) : Prop :=
  Work g capacity p s ∧ Import.Context input s ∧ s.gpr .esi = input.sourcePtr 0 ∧
    s.gpr .ebx = input.destPtr 0 ∧ s.gpr .ecx = BitVec.ofNat 32 input.count ∧
    input.dst.setWidth 64 = off g.W (g.array 6)

theorem load_trace (v : g.Valid) {input : Import.Geometry} (count : input.count = g.words) :
    RelCT isa (fun s t => WitnessRound.Initial g capacity p input s ∧ WitnessRound.Initial g capacity p input t) load
      (fun u z => Work g capacity p u ∧ Work g capacity p z) := by
  obtain ⟨fit, -, many, -⟩ := fits v
  unfold load
  refine RelCT.seq (R := fun u z => Importing g capacity p input u ∧ Importing g capacity p input z)
    (baseSeg (fun _ ⟨c, D, odd, large, _⟩ => ⟨c, D, odd, large⟩) (rawBlock (by decide +kernel))
      fun s ⟨c, D, odd, large, _, I, source, destination⟩ =>
        WP.mono (importArgs_ok v D.ready.context count source destination) fun t ⟨M, K, Ps, Pd, Pc⟩ =>
          ⟨(show Work g capacity p s from ⟨c, D, odd, large⟩).keepMem v K (by decide) (by decide) M,
            ⟨I.positive, I.sourceFit, I.destFit, fun i index => by rw [K.2.1, K.2.2]; exact I.readable i index,
              fun i index => by rw [K.2.2]; exact I.writable i index, I.separate⟩, Ps, Pd, Pc,
            by rw [← destination]; exact D.ready.scratch.ea (d := g.array 6) (by omega_using [fit, many])⟩) ?_
  refine seg [.esp, .edi, .esi, .ebx, .ecx] (regs g p fun r => if r = .esi then input.sourcePtr 0
    else if r = .ebx then input.destPtr 0 else BitVec.ofNat 32 input.count) (fun s S r mem => ?_)
    (VG.Proof.RsaKeyGen.X86.Import.code_trace.mono (fun _ _ h => h) (fun _ _ _ => trivial)) fun s S => ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl
    · exact S.1.sp
    · exact edi_value S.1.context
    · exact S.2.2.1
    · exact S.2.2.2.1
    · exact S.2.2.2.2.1
  · obtain ⟨Sw, I, Ps, Pd, Pc, dstAddr⟩ := S
    have C := Sw.context
    have nowrap := C.ws.nowrap
    refine WP.mono (VG.Proof.RsaKeyGen.X86.Import.code_ok I Ps Pd Pc) fun t T => ?_
    have F := T.frame
    obtain region : input.destRegion = ⟨off g.W (g.array 6), 4 * input.count⟩ := by
      unfold Import.Geometry.destRegion
      rw [dstAddr]
    rw [region, count] at F
    exact Sw.keep v T.keeps (by decide) (by decide) (frame_outside F (by omega_using [fit, nowrap]))

end

end VG.Proof.RsaKeyGen.X86.WitnessRt

end

end


/-! # The witness loop at the run-time width reveals only its consumed entropy length

`MillerRabinLoop.code_trace` for the run-time loop: each witness's draw is
checked in segments (`drawn_pair`), the rest as for a fixed width. -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen VG.Proof.Dsa.X86
open VG.Proof.RsaKeyGen.X86.MillerRabinLoop
open VG.Proof.RsaKeyGen.X86.WitnessRound (Work WorkPair)
open VG.Impl.RsaKeyGen.X86.MillerRabinLoop (exhausted again)
open VG.Impl.RsaKeyGen.X86.WitnessRt (drawn advance available checks)

theorem drawn_pair {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {input : Import.Geometry}
    (count : input.count = g.words) :
    RelCT isa (WitnessRound.InitialPair g capacity p input) drawn (WorkPair g capacity p) := by
  refine (RelCT.seq (load_trace v count) (sample_trace v)).mono (fun _ _ H => ⟨H.2.1, H.2.2⟩)
    fun u z ⟨U, Z⟩ => ⟨⟨U.context, Z.context, agree_regs fun r mem => ?_⟩, U, Z⟩
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact U.sp.trans Z.sp.symm
  · exact (edi_value U.context).trans (edi_value Z.context).symm

theorem advance_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block advance)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block advance) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem available_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block available)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block available) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem checks_raw : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block checks)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT _ (.block checks) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

theorem availableRt_ok {P : Parameters} (v : P.Valid) (Fx : Fixed P) {s : State} {k n : Nat}
    (S : StateAt P k n s) :
    WP isa (.block available) s fun t =>
      StateAt P k n t ∧ isa.eval .b t = some (decide (P.randLen - (P.start + P.bytes * k) < P.bytes)) := by
  obtain usedBound : P.start + P.bytes * k ≤ P.randLen := by
    have := S.atLoop.used; rw [v.entropyLength] at this; exact this
  refine WP.mono (available_ok v.geometry S.prepared.ready.scratch S.prepared.ready.context S.randLength S.used
    usedBound) fun t ⟨CF, mem, K⟩ => ?_
  refine ⟨S.keepMem v mem K (by decide) (by decide), ?_⟩
  rw [← Fx.bytes] at CF
  exact CF

theorem availableRt_pair {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat}
    {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.block available) (AvailablePair P other entropy k n) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := available_raw _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨U, Cu⟩ := wp_result (availableRt_ok v Fx H.2.1) E
  obtain ⟨Z, Cz⟩ := wp_result (availableRt_ok w ⟨Fx.bytes, Fx.words, Fx.checks⟩ H.2.2) G
  exact ⟨trace, ⟨⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩, Cu, Cz⟩

theorem round_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity : Nat} {p : BitVec 32} {input : Import.Geometry}
    (count : input.count = g.words) (length : g.L = 8 * capacity) (fit : 108 ≤ p.toNat)
    (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (WitnessRound.InitialPair g capacity p input) (VG.Impl.RsaKeyGen.X86.WitnessRt.round montName mont roundName round)
      (Pair g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.round
  exact RelCT.seq (drawn_pair v count) (RelCT.seq (WitnessRound.store_pair v)
    (RelCT.seq (WitnessRound.convert_pair montVerified montNoSp montStack v length)
      (RoundCall.code_trace roundVerified roundNoSp roundStack v length fit far lengthFar)))

theorem advance_pair {g : Geometry} (v : g.Valid) {capacity used randLen : Nat} {p rand : BitVec 32}
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + 8 * g.w ≤ randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩) :
    RelCT isa (WitnessStep.InitialPair g capacity p rand used randLen) (.block advance)
      (WitnessRound.InitialPair g capacity p (WitnessInput.geometryAt g rand used g.words)) := by
  have positive := v.minWidth
  have bound := v.maxWidth
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := advance_raw _ _ _ _ _ _ H.1.2.2 E G
  have post {a : State} (I : WitnessStep.Initial g capacity p rand used randLen a) :
      WP isa (.block advance) a fun b =>
        WitnessRound.Initial g capacity p (WitnessInput.geometryAt g rand used g.words) b ∧
        b.gpr .esi = rand + BitVec.ofNat 32 used := by
    obtain ⟨c, S, source, consumed, odd, large, shape, _, _, readable⟩ := I
    refine WP.mono (advance_ok v S source consumed (by omega_using [randLenFit, enough]))
      fun b ⟨B, ptr, _, _, K⟩ => ?_
    obtain readB : InRegions (b.rd ++ b.wr) (rand.setWidth 64) randLen := by
      rw [K.2.1, K.2.2]; exact readable
    exact ⟨⟨c, B, odd, large, shape, WitnessInput.context_okAt (used := used) (count := g.words) v B.ready.scratch
      randFit (by unfold Geometry.words; omega_using [positive]) (by unfold Geometry.words; omega_using []) (by unfold Geometry.words; omega_using [enough])
      readB separate,
      ptr, (WitnessInput.destination_pointer v B.ready.scratch).symm⟩, ptr⟩
  obtain ⟨U, sourceU⟩ := wp_result (post H.2.1) E
  obtain ⟨Z, sourceZ⟩ := wp_result (post H.2.2) G
  obtain ⟨cu, Du, ou, lu, hu, Cu, su, du⟩ := U
  obtain ⟨cz, Dz, oz, lz, hz, Cz, sz, dz⟩ := Z
  obtain registers : ∀ r ∈ ([.edi, .esi] : List Reg), u.gpr r = z.gpr r := by
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact round_regs agree (by decide)
    · rw [sourceU, sourceZ]
  exact ⟨trace, ⟨Du.ready.context, Dz.ready.context, round_add_regs (round_forget agree) registers⟩,
    ⟨cu, Du, ou, lu, hu, Cu, su, du⟩, ⟨cz, Dz, oz, lz, hz, Cz, sz, dz⟩⟩

theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {g : Geometry} (v : g.Valid) {capacity used randLen : Nat} {p rand : BitVec 32}
    (length : g.L = 8 * capacity)
    (randFit : rand.toNat + randLen ≤ 2 ^ 32) (randLenFit : randLen < 2 ^ 32)
    (enough : used + 8 * g.w ≤ randLen)
    (separate : (⟨rand.setWidth 64, randLen⟩ : Region).Disjoint ⟨g.W, g.L⟩)
    (fit : 108 ≤ p.toNat) (far : (⟨g.W, g.L⟩ : Region).Disjoint (below p 108))
    (lengthFar : (lengthRegion p).Disjoint (below p 108)) :
    RelCT isa (WitnessStep.InitialPair g capacity p rand used randLen)
      (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) (Pair g [.edi]) := by
  obtain raw : RelCT isa (WitnessStep.InitialPair g capacity p rand used randLen)
      (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
    unfold VG.Impl.RsaKeyGen.X86.WitnessRt.body
    refine RelCT.seq (advance_pair v randFit randLenFit enough separate) (RelCT.seq
      (round_trace (input := WitnessInput.geometryAt g rand used g.words) montVerified montNoSp
        montStack roundVerified roundNoSp roundStack v rfl length fit far lengthFar) ?_)
    exact WitnessCount.code_trace.mono (fun _ _ H => H.2.2) (fun _ _ H => H)
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := raw _ _ _ _ _ _ H E G
  have post {a : State} (I : WitnessStep.Initial g capacity p rand used randLen a) :
      WP isa (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round) a (Context g) := by
    obtain ⟨c, S, source, consumed, odd, large, shape, roundsFit, uniformFit, readable⟩ := I
    exact WP.mono (body_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      length S source consumed randFit randLenFit enough readable separate odd large (by rw [shape]; omega_using []) roundsFit
      uniformFit fit far lengthFar) fun _ R => R.1.ready.context
  exact ⟨trace, wp_result (post H.2.1) E, wp_result (post H.2.2) G, agree⟩

theorem branchRt_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (AvailablePair P other entropy k n)
      (.ite .b (.block exhausted) (VG.Impl.RsaKeyGen.X86.WitnessRt.body montName mont roundName round))
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  refine VG.RelCT.ite (fun _ _ H => H.2.1.trans H.2.2.symm)
    (exhausted_raw.mono (fun _ _ H => H.1.1.1.2.2) (fun _ _ H => H)) ?_
  intro s t tr ur u z H E G
  obtain enough : P.start + P.bytes * k + P.bytes ≤ P.randLen := by
    by_contra short
    have bound := H.1.1.2.1.atLoop.used
    rw [v.entropyLength] at bound
    obtain small : P.randLen - (P.start + P.bytes * k) < P.bytes := by omega_using [short, bound]
    have condition := H.1.2.1
    rw [H.2, decide_eq_true small] at condition
    cases condition
  obtain pre : WitnessStep.InitialPair P.g P.capacity P.p P.rand (P.start + P.bytes * k) P.randLen s t :=
    ⟨H.1.1.1, Fx.words ▸ H.1.1.2.1.stepInitial v, Fx.words ▸ H.1.1.2.2.stepInitial w⟩
  obtain ⟨trace, pair⟩ := body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v.geometry v.length v.randFit v.randLenFit (by rw [← Fx.bytes]; exact enough) v.randSeparate v.low v.stackFar
    v.lengthFar _ _ _ _ _ _ pre E G
  exact ⟨trace, pair.2.2⟩

theorem stepRt_raw {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round)
      (VG.X86.Taint.Agree (roundTaint [.edi])) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.step
  exact RelCT.seq (availableRt_pair v Fx w k n)
    (RelCT.seq (branchRt_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w k n) again_raw)

theorem stepRt_pair {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round)
      (fun s t => Pair P.g [.edi] s t ∧ Outcome P k n s ∧ Outcome (P.withSecret other entropy) k n t) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := stepRt_raw montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w k n _ _ _ _ _ _ H E G
  obtain ⟨U, Ou, _, _, _⟩ := wp_result
    (stepRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx H.2.1) E
  obtain ⟨Z, Oz, _, _, _⟩ := wp_result
    (stepRt_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack w ⟨Fx.bytes, Fx.words, Fx.checks⟩ H.2.2) G
  exact ⟨trace, ⟨U.ready.context, Z.ready.context, agree⟩, Ou, Oz⟩

theorem loopRt_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (k n : Nat) :
    RelCT isa (LoopPair P other entropy k n) (.loop (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) .e) (Pair P.g [.edi]) := by
  let Inv : Nat → State → State → Prop := fun q s t => ∃ k n, q = n + 1 ∧ LoopPair P other entropy k n s t
  obtain run : RelCT isa (Inv (n + 1)) (.loop (VG.Impl.RsaKeyGen.X86.WitnessRt.step montName mont roundName round) .e) (Pair P.g [.edi]) := by
    refine RelCT.loop (M := isa) Inv ?_ (n + 1)
    rintro q s t tr ur u z ⟨i, j, rfl, H⟩ E G
    obtain ⟨trace, pair, Ou, Oz⟩ := stepRt_pair montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w i j _ _ _ _ _ _ H E G
    rcases Ou with ⟨Eu, zeroU, _⟩ | ⟨Eu, positiveU, U⟩ <;>
      rcases Oz with ⟨Ez, zeroZ, _⟩ | ⟨Ez, positiveZ, Z⟩
    · refine ⟨trace, Eu.trans Ez.symm, fun _ => pair, ?_⟩
      intro continuing
      rw [Eu] at continuing
      cases continuing
    · omega
    · omega
    · refine ⟨trace, Eu.trans Ez.symm, ?_, ?_⟩
      · intro done
        rw [Eu] at done
        cases done
      · intro _
        exact ⟨j, by omega_using [], i + 1, j - 1, by omega_using [positiveU], pair, U, Z⟩
  exact run.mono (fun _ _ H => ⟨k, n, rfl, H⟩) (fun _ _ H => H)

theorem initRt_pair {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (.block VG.Impl.RsaKeyGen.X86.WitnessRt.checks)
      (LoopPair P other entropy 0 P.iterations) := by
  intro s t tr ur u z H E G
  obtain ⟨trace, agree⟩ := checks_raw _ _ _ _ _ _ H.1.2.2 E G
  obtain ⟨S, readS, bytesS, ptrS, lenS, usedS⟩ := H.2.1
  obtain ⟨T, readT, bytesT, ptrT, lenT, usedT⟩ := H.2.2.1
  obtain ⟨U, _, _, _⟩ := wp_result (initRt_ok v Fx S readS bytesS ptrS lenS usedS enough) E
  obtain ⟨Z, _, _, _⟩ := wp_result (initRt_ok w ⟨Fx.bytes, Fx.words, Fx.checks⟩ T readT bytesT ptrT lenT usedT enough) G
  have iters := H.2.2.2
  change P.iterations = (P.withSecret other entropy).iterations at iters
  change StateAt (P.withSecret other entropy) 0 (P.withSecret other entropy).iterations z at Z
  rw [← iters] at Z
  exact ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree⟩, U, Z⟩

theorem codeRt_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : Parameters} (v : P.Valid) (Fx : Fixed P) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) (enough : P.start ≤ P.randLen) :
    RelCT isa (InitialPair P other entropy) (VG.Impl.RsaKeyGen.X86.WitnessRt.code montName mont roundName round) (Pair P.g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.WitnessRt.code
  exact RelCT.seq (initRt_pair v Fx w enough)
    (loopRt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v Fx w 0 P.iterations)

end VG.Proof.RsaKeyGen.X86.WitnessRt

end

end

/-! # All prepared witnesses share one public private frame and one released iteration count -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/MrExponentRt/TestTiming.lean`, which only this module imported.
section

/-! # Preparation with the run-time exponent, then the witnesses, leak only the iteration count -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MrExponentRt
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.MillerRabin.X86
open VG.Proof.RsaKeyGen VG.Proof.Dsa.X86

/-- The candidate's length `8 w` at header byte 4. -/
def Len (P : MillerRabinLoop.Parameters) (s : State) : Prop :=
  s.mem.readW (off P.g.W 4) 32 = BitVec.ofNat 32 (8 * P.g.w)

/-- Each run's inputs to preparation. -/
def InputsPair (P : MillerRabinLoop.Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  (CandidatePrepare.Input P s ∧ Len P s) ∧ (CandidatePrepare.Input (P.withSecret other entropy) t ∧ Len P t)

theorem inputs_agree {P : MillerRabinLoop.Parameters} {other : Nat} {entropy : Spec.RsaKeyGen.Rand} {s t : State}
    (H : InputsPair P other entropy s t) : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
  apply agree_regs
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact H.1.1.prepare.caller.sp.trans H.2.1.prepare.caller.sp.symm
  · exact BitVec.eq_of_toNat_eq (H.1.1.prepare.scratch.edi_toNat.trans H.2.1.prepare.scratch.edi_toNat.symm)

/-- After the header, for the run's original inputs `s0`: what `head_ok` needs. -/
def Headed (P : MillerRabinLoop.Parameters) (s : State) : Prop :=
  ∃ s0, Prepare.Input P.g P.candidate P.capacity P.p s0 ∧ PreparedR2.Ready P.g P.candidate P.capacity P.p s ∧
    Outs P.g.W PrepareHeader.ranges s0.mem s.mem ∧ Keeps PrepareHeader.clob s0 s ∧
    word s.mem P.g.W 224 = BitVec.ofNat 64 (8 * (P.g.w + 2)) ∧ Len P s

def HeadedPair (P : MillerRabinLoop.Parameters) (other : Nat) (entropy : Spec.RsaKeyGen.Rand) (s t : State) : Prop :=
  Headed P s ∧ Headed (P.withSecret other entropy) t

/-- Header byte 4 is outside what the header writes. -/
theorem len_header {P : MillerRabinLoop.Parameters} {s t : State} (O : Outs P.g.W PrepareHeader.ranges s.mem t.mem)
    (len : Len P s) : Len P t := by
  obtain same := O.val32 (d := 4) (k := 1) (fun r mem => by
    simp only [PrepareHeader.ranges, Header.ranges, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at mem
    rcases mem with (rfl | rfl | rfl) | rfl <;> left <;> decide) (by decide)
  simp only [val32, Nat.mul_zero, Nat.add_zero] at same
  unfold Len at *
  rw [← len]
  exact BitVec.eq_of_toNat_eq same

theorem headed_ok {Q : MillerRabinLoop.Parameters} (G : Q.g.Valid) (length : Q.g.L = 8 * Q.capacity)
    (seed : Q.seed = 64 * Q.g.w - 1) {s : State} (I : CandidatePrepare.Input Q s) (len : Len Q s) :
    WP isa VG.Impl.RsaKeyGen.X86.HeaderRt.prepare s (Headed Q) := by
  obtain Ip : Prepare.Input Q.g Q.candidate Q.capacity Q.p s := by
    have := I.prepare
    rw [seed] at this
    exact this
  exact WP.mono (PrepareHeader.prepareRt_ok G Ip.scratch Ip.caller length Ip.candidate Ip.odd len)
    fun _ ⟨R, O, K, stride⟩ => ⟨s, Ip, R, O, K, stride, len_header O len⟩

theorem header_trace {P : MillerRabinLoop.Parameters} (v : P.Valid) (seed : P.seed = 64 * P.g.w - 1)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (InputsPair P other entropy) VG.Impl.RsaKeyGen.X86.HeaderRt.prepare (HeadedPair P other entropy) := by
  intro s t tr ur u z H E F
  exact ⟨(PrepareHeader.prepareRt_trace _ _ _ _ _ _ (inputs_agree H) E F).1,
    wp_result (headed_ok v.geometry v.length seed H.1.1 H.1.2) E,
    wp_result (headed_ok (Q := P.withSecret other entropy) v.geometry v.length seed H.2.1 H.2.2) F⟩

theorem head_trace {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (HeadedPair P other entropy) (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead name mont)
      (fun u z => Prepared P.g P.capacity P.p u ∧ Prepared P.g P.capacity P.p z) := by
  have G := v.geometry
  obtain raw : RelCT isa (fun s t => PreparedR2.Input P.g P.capacity P.p s ∧ PreparedR2.Input P.g P.capacity P.p t)
      (VG.Impl.RsaKeyGen.X86.Candidate.prepareHead name mont) (fun _ _ => True) := by
    unfold VG.Impl.RsaKeyGen.X86.Candidate.prepareHead
    exact RelCT.seq (PrepareRt.r2_trace verified noSp stack G v.length)
      (PrepareRt.constants_trace verified noSp stack G v.length)
  intro s t tr ur u z H E F
  obtain ⟨⟨s0, Is, Rs, Os, Ks, strides, _⟩, ⟨t0, It, Rt, Ot, Kt, stridet, _⟩⟩ := H
  refine ⟨(raw _ _ _ _ _ _ ⟨⟨_, Rs, Is.odd, Is.top⟩, ⟨_, Rt, It.odd, It.top⟩⟩ E F).1, ?_, ?_⟩
  · exact ⟨_, (wp_result (head_ok verified noSp stack G v.length Is Rs Os Ks strides) E).1⟩
  · exact ⟨_, (wp_result (head_ok verified noSp stack G v.length It Rt Ot Kt stridet) F).1⟩

theorem prepared_raw {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid)
    (seed : P.seed = 64 * P.g.w - 1) {other : Nat} {entropy : Spec.RsaKeyGen.Rand} :
    RelCT isa (InputsPair P other entropy) (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.prepared
  exact RelCT.seq (header_trace v seed) (RelCT.seq (head_trace verified noSp stack v)
    (MrExponentRt.code_trace v.geometry))

/-- Preparation with the run-time exponent: `CandidateTest.prepare_pair`. -/
theorem preparedRun_pair {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) {other : Nat} {entropy : Spec.RsaKeyGen.Rand}
    (w : (P.withSecret other entropy).Valid) :
    RelCT isa (fun s t => InputsPair P other entropy s t ∧ P.iterations = (P.withSecret other entropy).iterations)
      (VG.Impl.RsaKeyGen.X86.Candidate.prepared name mont) (MillerRabinLoop.InitialPair P other entropy) := by
  intro s t tr ur u z ⟨H, iterations⟩ E G
  obtain trace := (prepared_raw verified noSp stack v seed _ _ _ _ _ _ H E G).1
  obtain ⟨U, _, _, _⟩ := wp_result (prepared_ok verified noSp stack v width bound seed H.1.1 H.1.2) E
  obtain ⟨Z, _, _, _⟩ := wp_result (prepared_ok verified noSp stack w width bound seed H.2.1 H.2.2) G
  refine ⟨trace, ⟨U.prepared.ready.context, Z.prepared.ready.context, agree_regs fun r mem => ?_⟩,
    ⟨U.prepared, U.readable, U.entropy, U.randPtr, U.randLength, U.used⟩,
    ⟨Z.prepared, Z.readable, Z.entropy, Z.randPtr, Z.randLength, Z.used⟩, iterations⟩
  change r ∈ [.esp, .edi] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact U.prepared.ready.caller.sp.trans Z.prepared.ready.caller.sp.symm
  · exact (edi_value U.prepared.ready.context).trans (edi_value Z.prepared.ready.context).symm

/-- Preparation and the witnesses: `CandidateTest.core_trace` with the
exponent at the run-time width. -/
theorem body_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {P : MillerRabinLoop.Parameters} (v : P.Valid) (width : 4 ≤ P.g.w) (bound : P.g.w ≤ 64)
    (seed : P.seed = 64 * P.g.w - 1) (checks : P.checks = VG.Impl.RsaKeyGen.X86.WitnessChecks.checks P.g.w)
    (bytes : P.bytes = 8 * P.g.w) (words : P.words = 2 * P.g.w)
    {other : Nat} {entropy : Spec.RsaKeyGen.Rand} (w : (P.withSecret other entropy).Valid)
    (enough : P.start ≤ P.randLen) :
    RelCT isa (fun s t => InputsPair P other entropy s t ∧ P.iterations = (P.withSecret other entropy).iterations)
      (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round) (Pair P.g [.edi]) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.testBody
  exact RelCT.seq (preparedRun_pair montVerified montNoSp montStack v width bound seed w)
    (WitnessRt.codeRt_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
      ⟨bytes, words, checks⟩ w enough)

end VG.Proof.RsaKeyGen.X86.MrExponentRt
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePrivateInput.lean`, which only this module imported.
section

/-! # The single private call frame establishes every prepared-loop input -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem private_input {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s)
    (minusOne : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E entropy - 1)
    (S : Scr t E.base E.size) (C : Caller E.geometry E.capacity (E.p - 28#32) t)
    (F : Frame [below E.p 28] s.mem t.mem) (K : Keeps [.edx] (allocFrame 28 s) t) :
    CandidatePrepare.Input (E.parameters entropy) t := by
  obtain workspaceFar : E.workspaceRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  obtain randFar : E.randRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.randRegion (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  obtain W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  obtain top : 2 ^ (64 * E.width - 1) ≤ candidateValue E entropy := by
    obtain lower := (candidate_shape v entropy).2.1
    have width := v.width_bounds.1
    obtain eqPower : 2 ^ (64 * E.width - 1) = 2 ^ (64 * E.width - 2) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega_using [width]
    rw [eqPower]
    omega_using [lower]
  refine ⟨⟨S, C, ?_, ?_, candidate_odd v entropy, by change 1 < candidateValue E entropy; have := candidate_large v entropy; omega_using [this], top⟩, ?_, ?_, ?_, ?_, ?_⟩
  · have value := W.val32 (v.geometry.arrayFit (j := 0) (by decide)) (by intro r mem; cases mem)
    rw [← Prepared.slot_eq] at value
    exact value.trans D.candidate
  · have value := W.val32 (v.geometry.arrayFit (j := 5) (by decide)) (by intro r mem; cases mem)
    rw [← Prepared.slot_eq] at value
    exact value.trans minusOne
  · rw [K.2.1, K.2.2]
    obtain ⟨r, mem, contains⟩ := D.input.memory.randRead
    refine ⟨r, ?_, contains⟩
    change r ∈ s.rd ++ (⟨(s.gpr .esp - 28#32).setWidth 64, 28⟩ :: s.wr)
    exact (List.mem_append.mp mem).elim (List.mem_append_left _) (fun known => List.mem_append_right _ (List.mem_cons_of_mem _ known))
  · change Spec.Rsa.bytesAt t.mem (E.rand.setWidth 64) E.randLength = entropy
    rw [VG.Proof.RsaKeyGen.frame_bytesAt F
      (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact randFar) (by have := v.randLengthFit; omega_using [this])]
    exact D.input.memory.entropy
  · exact (W.read32 (d := 28) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 28 + 4 ≤ E.size; omega_using [H])
      (by intro r mem; cases mem)).trans D.input.rand_eq
  · have word := W.read32 (d := 32) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 32 + 4 ≤ E.size; omega_using [H])
      (by intro r mem; cases mem)
    exact (congrArg BitVec.toNat word).trans (D.input.randLength_eq v)
  · have word := W.read32 (d := 152) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 152 + 4 ≤ E.size; omega_using [H])
      (by intro r mem; cases mem)
    change (t.mem.readW (off E.base 152) 32).toNat = 8 * E.width
    rw [v.length_eq]
    exact (congrArg BitVec.toNat word).trans D.used

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86
open VG.Impl.Bignum.X86.PublicContext VG.Impl.Mont.X86

structure TestPair (E : Environment) (eBytes pBytes qBytes rBytes sBytes : List Byte) (s t : State) : Prop
    extends DrawnPair E eBytes pBytes qBytes rBytes sBytes s t where
  savedLeft : val32 s.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E rBytes - 1
  savedRight : val32 t.mem E.base (slot E.width 5) (2 * E.width) = candidateValue E sBytes - 1

theorem capacity_ok {s : State} {base : Addr} {size : Nat} (S : Scr s base size) (space : 44 ≤ size) :
    WP isa (.block [.mov .edx (.mem (sc 40))]) s fun t => Upd s t .edx (s.mem.readW (off base 40) 32) :=
  wp_movS (readSrc_sc S space) fun _ U _ => WP.block_nil U

/-- The candidate's length, kept inside the private frame. -/
theorem private_len {E : Environment} (v : E.Valid) {eBytes pBytes entropy : List Byte} {s t : State}
    (D : Drawn E eBytes pBytes entropy s) (F : Frame [below E.p 28] s.mem t.mem) (other : List Byte) :
    MrExponentRt.Len (E.parameters other) t := by
  obtain workspaceFar : E.workspaceRegion.Disjoint (below E.p 28) :=
    (v.stackFar E.workspaceRegion (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))).sub_right
      (below_sub (by decide) v.low)
  obtain W : WorkspaceFrame E.geometry [] s.mem t.mem := workspace_of_frame F D.input.scratch.nowrap
    (by intro r mem; obtain rfl := List.mem_singleton.mp mem; exact workspaceFar)
  change t.mem.readW (off E.geometry.W 4) 32 = BitVec.ofNat 32 (8 * E.width)
  rw [W.read32 (d := 4) (by have H : 256 ≤ E.size := v.geometry.headerFit; change 4 + 4 ≤ E.size; omega_using [H])
    (by intro r mem; cases mem)]
  change s.mem.readW (off E.base (4 * 1)) 32 = _
  rw [D.input.header 1 (by decide)]
  change BitVec.ofNat 32 E.length = _
  rw [v.length_eq]

theorem test_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (iterations : (E.parameters rBytes).iterations = (E.parameters sBytes).iterations)
    (enough : E.length ≤ E.randLength) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
        (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round)) (fun _ _ => True) := by
  intro s t tr ur u z H A B
  have space : 256 ≤ E.size := v.geometry.headerFit
  obtain raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block [.mov .edx (.mem (sc 40))])
      (VG.X86.Taint.Agree (τr [.esp, .edi])) := checkedBlockInvariant rfl rfl
  cases A with
  | seq argsA frameA =>
    cases B with
    | seq argsB frameB =>
      obtain argsTrace := (raw _ _ _ _ _ _ H.toDrawnPair.inputs.agree argsA argsB).1
      obtain Ua := wp_result (capacity_ok H.left.input.scratch (by omega_using [space])) argsA
      obtain Ub := wp_result (capacity_ok H.right.input.scratch (by omega_using [space])) argsB
      obtain Da := H.left.keepMem v Ua.mem Ua.keeps (by decide) (by decide) Ua.syms
      obtain Db := H.right.keepMem v Ub.mem Ub.keeps (by decide) (by decide) Ub.syms
      obtain capA : _ := Ua.gpr.trans (H.left.input.header 10 (by decide))
      obtain capB : _ := Ub.gpr.trans (H.right.input.header 10 (by decide))
      cases frameA with
      | frame pushA bodyA popA =>
        cases frameB with
        | frame pushB bodyB popB =>
          obtain ea := alloc_some pushA
          obtain eb := alloc_some pushB
          subst ea eb
          cases bodyA with
          | seq storeA coreA =>
            cases bodyB with
            | seq storeB coreB =>
              obtain slotA := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity) Da.input.scratch (by rw [Da.input.stack]; exact v.low)
                (by rw [Da.input.stack]; exact v.workspaceStack) capA) storeA
              obtain slotB := wp_result (CandidateFrame.slot_ok (g := E.geometry) (capacity := E.capacity) Db.input.scratch (by rw [Db.input.stack]; exact v.low)
                (by rw [Db.input.stack]; exact v.workspaceStack) capB) storeB
              obtain ⟨Sa, Ca, _, Fa, Ka⟩ := slotA
              obtain ⟨Sb, Cb, _, Fb, Kb⟩ := slotB
              rw [CandidateFrame.privateSp, Da.input.stack] at Ca
              rw [CandidateFrame.privateSp, Db.input.stack] at Cb
              rw [Da.input.stack] at Fa
              rw [Db.input.stack] at Fb
              obtain Ia := private_input v Da (by rw [Ua.mem]; exact H.savedLeft) Sa Ca Fa (Ka.mono (by decide))
              obtain Ib := private_input v Db (by rw [Ub.mem]; exact H.savedRight) Sb Cb Fb (Kb.mono (by decide))
              obtain initial : MrExponentRt.InputsPair (E.parameters rBytes) (candidateValue E sBytes) sBytes _ _ ∧
                  (E.parameters rBytes).iterations = ((E.parameters rBytes).withSecret (candidateValue E sBytes) sBytes).iterations :=
                ⟨⟨⟨Ia, private_len v Da Fa _⟩, ⟨Ib, private_len v Db Fb _⟩⟩, iterations⟩
              obtain coreTrace := (MrExponentRt.body_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack
                (v.parameters_valid rBytes H.left.input.memory.entropyLength) v.width_bounds.1 v.width_bounds.2
                rfl rfl rfl rfl
                (v.parameters_valid sBytes H.right.input.memory.entropyLength) (by change 8 * E.width ≤ E.randLength; rw [v.length_eq]; exact enough)
                _ _ _ _ _ _ initial coreA coreB).1
              obtain storeRaw : RelCT isa (VG.X86.Taint.Agree (τr [.esp])) (.block [.store (at_ .esp 24) .edx])
                  (VG.X86.Taint.Agree (τr [.esp])) := checkedBlockInvariant rfl rfl
              obtain storeTrace := (storeRaw _ _ _ _ _ _ (by
                apply agree_regs
                intro r mem
                obtain rfl := List.mem_singleton.mp mem
                rw [allocFrame_esp, allocFrame_esp, Da.input.stack, Db.input.stack]) storeA storeB).1
              refine ⟨?_, trivial⟩
              change _ ++ ([] ++ (_ ++ _) ++ []) = _ ++ ([] ++ (_ ++ _) ++ [])
              rw [argsTrace, storeTrace, coreTrace]

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! ### `RsaKeyGen.X86.CandidateDispatchTiming`, which this module and modules that import it used -/

section

/-! # Branches on public values and the width dispatch leak only the branch taken -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

def WithFlag (P : State → State → Prop) (bit : Bool) (s t : State) : Prop :=
  P s t ∧ s.gpr .eax = BitVec.ofNat 32 bit.toNat ∧ t.gpr .eax = BitVec.ofNat 32 bit.toNat

def WithCondition (P : State → State → Prop) (c : Cond) (bit : Bool) (s t : State) : Prop :=
  P s t ∧ isa.eval c s = some bit ∧ isa.eval c t = some bit

theorem cmp_flag_trace {P : State → State → Prop} (bit : Bool)
    (keep : ∀ s t u z, P s t → Fupd s u → Fupd t z → P u z) :
    RelCT isa (WithFlag P bit) (.block [.alu .cmp .eax (.imm 0)])
      (fun s t => WithCondition P .e (!bit) s t ∧ WithCondition P .ne bit s t) := by
  intro s t tr ur u z ⟨H, flagS, flagT⟩ A B
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [])) (.block [.alu .cmp .eax (.imm 0)])
      (VG.X86.Taint.Agree (τr [])) := checkedBlockInvariant rfl rfl
  have empty : VG.X86.Taint.Agree (τr []) s t := agree_regs (by intro r mem; cases mem)
  obtain ⟨U, eqU, neU⟩ := wp_result (cmp_bool flagS) A
  obtain ⟨Z, eqZ, neZ⟩ := wp_result (cmp_bool flagT) B
  exact ⟨(raw _ _ _ _ _ _ empty A B).1, ⟨keep _ _ _ _ H U Z, eqU, eqZ⟩, ⟨keep _ _ _ _ H U Z, neU, neZ⟩⟩

theorem branch_true {P Q : State → State → Prop} {c : Cond} {th el : Prog isa}
    (H : RelCT isa P th Q) :
    RelCT isa (WithCondition P c true) (.ite c th el) Q := by
  apply VG.RelCT.ite (fun _ _ P => P.2.1.trans P.2.2.symm)
  · exact H.mono (fun _ _ P => P.1.1) (fun _ _ P => P)
  · intro s t tr ur u z P _ _
    have impossible := P.1.2.1.symm.trans P.2
    cases impossible

theorem branch_false {P Q : State → State → Prop} {c : Cond} {th el : Prog isa}
    (H : RelCT isa P el Q) :
    RelCT isa (WithCondition P c false) (.ite c th el) Q := by
  apply VG.RelCT.ite (fun _ _ P => P.2.1.trans P.2.2.symm)
  · intro s t tr ur u z P _ _
    have impossible := P.1.2.1.symm.trans P.2
    cases impossible
  · exact H.mono (fun _ _ P => P.1.1) (fun _ _ P => P)

theorem compare_value_ok {s : State} (value : BitVec 32) :
    WP isa (.block [.alu .cmp .eax (.imm value)]) s fun t =>
      Fupd s t ∧ isa.eval .e t = some (s.gpr .eax - value == 0#32) := by
  refine wp_cmpS rfl fun _ T Z => WP.block_nil ⟨T, ?_⟩
  exact Z

end VG.Proof.RsaKeyGen.X86.Candidate

end

end

/-! # Boolean status branches compose without publishing candidate arithmetic -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Proof.Dsa.X86

theorem DrawnPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : DrawnPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    DrawnPair E eBytes pBytes qBytes rBytes sBytes u z :=
  ⟨P.left.keepMem v U.mem (U.keeps []) (by decide) (by decide) U.syms,
    P.right.keepMem v Z.mem (Z.keeps []) (by decide) (by decide) Z.syms⟩

theorem TestPair.keepFlags {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : TestPair E eBytes pBytes qBytes rBytes sBytes s t) (U : Fupd s u) (Z : Fupd t z) :
    TestPair E eBytes pBytes qBytes rBytes sBytes u z := by
  refine ⟨P.toDrawnPair.keepFlags v U Z, ?_, ?_⟩
  · rw [U.mem]; exact P.savedLeft
  · rw [Z.mem]; exact P.savedRight

end VG.Proof.RsaKeyGen.X86.Candidate
