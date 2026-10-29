module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.FastTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64
public import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Array

import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.General
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86.Gcd64Timing
import VerifiedGarbage.Proof.RsaKeyGen.X86.FilterStack
import VerifiedGarbage.Proof.Mont.X86.DynamicTiming
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.ExponentRt.Pointer
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64
import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Word
import VerifiedGarbage.Impl.RsaKeyGen.X86.Mod64Array
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayLoadTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.Mod64ArrayStep
import VerifiedGarbage.Impl.RsaKeyGen.X86.Gcd64Check
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86.Taint
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

theorem check_trace (offset : Nat) :
    RelCT isa (VG.X86.Taint.Agree (workspaceTaint false)) (check offset)
      (VG.X86.Taint.Agree (workspaceTaint false)) :=
  RelCT.seq (setup_trace offset) (RelCT.seq code_trace result_trace)

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
  have positive : 0 < exponent := by have := S.eOdd; omega
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
           (Offset.contains_base _ (by have := slot5_lo w; have := S.framed.space.space; omega)
             (by have := S.framed.space.scratch.nowrap; omega))
           (by
             intro r mem; obtain rfl := List.mem_singleton.mp mem
             exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by have := S.framed.fit; rw [S.framed.space.stack]; omega)
               S.framed.space.scratch.nowrap (by
                 rw [S.framed.space.stack]
                 rcases S.framed.separate with h | h; exact Or.inl h; exact Or.inr (by omega)))
           (by decide)).trans S.framed.space.len⟩, eA⟩)
    | (obtain ⟨Sx, -, -, eA, Fx, Kx⟩ := wp_result (framed_ok T.framed.space.scratch T.framed.space.width
          T.framed.space.widthBound T.framed.space.space T.framed.space.len rfl T.eValue positive
          (by rw [T.framed.space.stack]; exact T.framed.fit) (by rw [T.framed.space.stack]; exact T.framed.separate)) G
       exact ⟨⟨Sx, (Kx.1 .esp (by decide)).trans T.framed.space.stack, T.framed.space.width,
         T.framed.space.widthBound, T.framed.space.space,
         (Fx.readW (r := ⟨workspace.setWidth 64, size⟩)
           (Offset.contains_base _ (by have := slot5_lo w; have := T.framed.space.space; omega)
             (by have := T.framed.space.scratch.nowrap; omega))
           (by
             intro r mem; obtain rfl := List.mem_singleton.mp mem
             exact VG.Proof.RsaKeyGen.X86.FilterStack.allocated_apart (by have := T.framed.fit; rw [T.framed.space.stack]; omega)
               T.framed.space.scratch.nowrap (by
                 rw [T.framed.space.stack]
                 rcases T.framed.separate with h | h; exact Or.inl h; exact Or.inr (by omega)))
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
    refine WP.mono (restoreSetup_ok S.scratch S.widthBound (by omega) S.len) fun d ⟨K, M, ebx, ebp, esi, ecx⟩ => ?_
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
        rw [BitVec.toNat_ofNat]; have := S.widthBound; omega
      · exact ecx
    exact ⟨⟨Sd, regs⟩, regs⟩
  have loop := copy_trace (workspace := workspace) (p := p) (size := size) (w := w) (src := slot w 5) (dst := 256)
    fun h => by have := slot5_ge w; exact ⟨h, by omega, Or.inl (by omega), by omega⟩
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
