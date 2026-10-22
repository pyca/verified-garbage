module

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentFastSetup
import VerifiedGarbage.Proof.RsaKeyGen.X86.FermatTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentFilter
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStack
public import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialReadControl

/-! # The usual public exponent scans the same candidate words in every execution -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentFilter
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Mont.X86 VG.Impl.RsaKeyGen.X86.ExponentFilter VG.Impl.Bignum.X86.PublicContext

structure FastInitial (g : Sieve.Geometry) (workspace : BitVec 32) (s : State) : Prop where
  stack : Sieve.StackContext g.sp s
  workspaceEq : s.gpr .edi = workspace
  readable : ∀ i < 2 * g.w, InRegions (s.rd ++ s.wr) (off (g.candidate.setWidth 64) (4 * i)) 4

theorem fastArgs_control {g : Sieve.Geometry} {workspace : BitVec 32}
    (pointer : workspace + BitVec.ofNat 32 (slot g.w 5) = g.candidate)
    {s : State} (S : FastInitial g workspace s) :
    WP isa (.block (.store (at_ .esp 0) .edi :: fastArgs g.w)) s (Sieve.ReadControl g 0) := by
  refine WP.mono (fastArgs_ok S.stack) fun t ⟨ptr, ending, _, _, K⟩ => ?_
  refine ⟨S.stack.keep K (by decide), ?_, ?_, ?_⟩
  · intro i index
    rw [K.2.1, K.2.2]; exact S.readable i index
  · rw [ending, S.workspaceEq, pointer]; rfl
  · simpa only [S.workspaceEq, pointer, Nat.mul_zero, show BitVec.ofNat 32 0 = 0#32 from rfl, BitVec.add_zero] using ptr

theorem fastArgs_trace {g : Sieve.Geometry} {workspace : BitVec 32}
    (pointer : workspace + BitVec.ofNat 32 (slot g.w 5) = g.candidate) :
    RelCT isa (fun s t => FastInitial g workspace s ∧ FastInitial g workspace t)
      (.block (.store (at_ .esp 0) .edi :: fastArgs g.w))
      (fun s t => Sieve.ReadControl g 0 s ∧ Sieve.ReadControl g 0 t) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have A : VG.X86.Taint.Agree (τr [.esp, .edi]) s t := by
    apply agree_regs
    intro r mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact S.stack.sp.trans T.stack.sp.symm
    · exact S.workspaceEq.trans T.workspaceEq.symm
  have raw : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block (.store (at_ .esp 0) .edi :: fastArgs g.w)) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
    erased_relCT _ (.block (.store (at_ .esp 0) .edi :: fastArgs 0)) (.block []) rfl rfl rfl (by decide +kernel)
  exact ⟨(raw _ _ _ _ _ _ A E G).1,
    wp_result (fastArgs_control pointer S) E, wp_result (fastArgs_control pointer T) G⟩

theorem fast_body_trace_bounded {g : Sieve.Geometry} (positive : 0 < g.w) (widthBound : g.w ≤ 128)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) {workspace : BitVec 32}
    (pointer : workspace + BitVec.ofNat 32 (slot g.w 5) = g.candidate) :
    RelCT isa (fun s t => FastInitial g workspace s ∧ FastInitial g workspace t)
      (.seq (.block (.store (at_ .esp 0) .edi :: fastArgs g.w))
        (.seq (VG.Impl.RsaKeyGen.X86.FermatExponent.code 4) (.block [.mov .edi (.mem (at_ .esp 0))])))
      (fun _ _ => True) := by
  refine RelCT.seq (fastArgs_trace pointer) (RelCT.seq (FermatExponent.code_trace_bounded positive widthBound candidateFit) ?_)
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .edi (.mem (at_ .esp 0))]) (VG.X86.Taint.Agree (τr [.esp])) :=
    erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel)
  exact restore.mono (fun _ _ H => H) (fun _ _ _ => trivial)

theorem fast_body_trace {g : Sieve.Geometry} (v : g.Valid) {workspace : BitVec 32}
    (pointer : workspace + BitVec.ofNat 32 (slot g.w 5) = g.candidate) :
    RelCT isa (fun s t => FastInitial g workspace s ∧ FastInitial g workspace t)
      (.seq (.block (.store (at_ .esp 0) .edi :: fastArgs g.w))
        (.seq (VG.Impl.RsaKeyGen.X86.FermatExponent.code 4) (.block [.mov .edi (.mem (at_ .esp 0))])))
      (fun _ _ => True) :=
  fast_body_trace_bounded v.positive v.widthBound v.candidateFit pointer

structure FastEntry (g : Sieve.Geometry) (workspace : BitVec 32) (s : State) : Prop where
  fit : 20 ≤ (s.gpr .esp).toNat
  stackEq : s.gpr .esp - 20#32 = g.sp
  workspaceEq : s.gpr .edi = workspace
  readable : ∀ i < 2 * g.w, InRegions (s.rd ++ s.wr) (off (g.candidate.setWidth 64) (4 * i)) 4

theorem FastEntry.initial {g : Sieve.Geometry} {workspace : BitVec 32} {s : State}
    (S : FastEntry g workspace s) : FastInitial g workspace (allocFrame 20 s) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← S.stackEq]; exact FilterStack.allocated_context S.fit
  · rw [allocFrame_gpr _ _ (by decide)]; exact S.workspaceEq
  · intro i index
    obtain ⟨r, mem, contains⟩ := S.readable i index
    refine ⟨r, ?_, contains⟩
    rcases List.mem_append.mp mem with mem | mem
    · exact List.mem_append_left _ mem
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ mem)

theorem fast_trace_bounded {g : Sieve.Geometry} (positive : 0 < g.w) (widthBound : g.w ≤ 128)
    (candidateFit : g.candidate.toNat + 8 * g.w ≤ 2 ^ 32) {workspace : BitVec 32}
    (pointer : workspace + BitVec.ofNat 32 (slot g.w 5) = g.candidate) :
    RelCT isa (fun s t => FastEntry g workspace s ∧ FastEntry g workspace t)
      (fast g.w) (fun _ _ => True) := by
  unfold fast
  apply RelCT.frameAlloc
  refine (fast_body_trace_bounded positive widthBound candidateFit pointer).mono ?_ (fun _ _ _ => trivial)
  rintro _ _ ⟨s, t, ⟨S, T⟩, rfl, rfl⟩
  exact ⟨S.initial, T.initial⟩

theorem fast_trace {g : Sieve.Geometry} (v : g.Valid) {workspace : BitVec 32}
    (pointer : workspace + BitVec.ofNat 32 (slot g.w 5) = g.candidate) :
    RelCT isa (fun s t => FastEntry g workspace s ∧ FastEntry g workspace t)
      (fast g.w) (fun _ _ => True) :=
  fast_trace_bounded v.positive v.widthBound v.candidateFit pointer

end VG.Proof.RsaKeyGen.X86.ExponentFilter
