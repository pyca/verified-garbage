module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.SaveTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialReadControl
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Fast
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Impl.RsaKeyGen.X86.FermatExponent
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
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

theorem code_trace {g : Geometry} (v : g.Valid) :
    RelCT isa (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) (code 4)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq init_trace (RelCT.seq (divisor_trace v) (checkedBlockInvariant rfl rfl))

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
  have fit : 20 ≤ (s.gpr .esp).toNat := by rw [S.space.stack]; have := S.fit; omega
  have C : Sieve.StackContext (p - 20#32) (allocFrame 20 s) := by
    rw [← S.space.stack]; exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_context fit
  have Si := S.scratch
  have width := S.space.width
  have space := S.space.space
  have nowrap := Si.nowrap
  have header := slot5_ge w
  refine WP.mono (fastArgs_ok (w := w) C Si (by omega) (by rw [allocFrame_mem]; exact S.space.len))
    fun t ⟨ptr, ending, _, _, K⟩ => ?_
  have edi : (allocFrame 20 s).gpr .edi = workspace := by
    rw [allocFrame_gpr _ _ (by decide)]; exact S.space.workspace
  have pbase : (workspace + BitVec.ofNat 32 (slot w 5)).setWidth 64 = off (workspace.setWidth 64) (slot w 5) := by
    have h := Si.ea (d := slot w 5) (by omega)
    change ((allocFrame 20 s).gpr .edi + BitVec.ofNat 32 (slot w 5)).setWidth 64 = _ at h
    rw [edi] at h
    exact h
  refine ⟨C.keep K (by decide), ?_, ?_, ?_⟩
  · intro i index
    change i < 2 * w at index
    rw [K.2.1, K.2.2]
    change InRegions _ (off ((workspace + BitVec.ofNat 32 (slot w 5)).setWidth 64) (4 * i)) 4
    rw [pbase]
    simpa only [off, BitVec.add_assoc, ← BitVec.ofNat_add] using Si.read (d := slot w 5 + 4 * i) (n := 4) (by omega)
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
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := slot w 5) (by omega), edi,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have restore : RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi]))
      (.block [.mov .edi (.mem (at_ .esp 0))]) (fun _ _ => True) :=
    (erased_relCT _ _ (.block []) rfl rfl rfl (by decide +kernel) :
      RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) _ (VG.X86.Taint.Agree (τr [.esp]))).mono
      (fun _ _ H => H) (fun _ _ _ => trivial)
  have body := RelCT.seq args (RelCT.seq (VG.Proof.RsaKeyGen.X86.FermatExponent.code_trace_bounded
    (g := fastGeometry workspace p w) (by change 0 < w; omega) (by change w ≤ 128; omega) fit) restore)
  exact RelCT.frameAlloc body _ _ _ _ _ _ ⟨S, T⟩ E G

end VG.Proof.RsaKeyGen.X86.ExponentRt
