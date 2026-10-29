module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveStep
public import VerifiedGarbage.Proof.Framework.X86.RelCT

import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialReadControl
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialLoopTiming
/-! # The sieve leaks only the divisor pattern of a rejected candidate

Passing candidates have the all-false pattern, so their values remain secret.
Equal rejected candidates have the same pattern; the candidate contract can
therefore release the rejected candidate rather than impose a full-table pass.
-/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveLoadState.lean`, which only this module imported.
section

/-! # Loading a divisor preserves every candidate and table invariant -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem StateAt.load {g : Geometry} (v : g.Valid) {c i q : Nat} {s : State}
    (H : StateAt g c i q s) (index : i < 1024) :
    WP isa (.block (loadPrime stackSlots)) s fun t => StateAt g c i q t ∧ t.gpr .edi = g.candidate := by
  have readTable : s.mem.readW ((g.cursor i).setWidth 64) 64 = BitVec.ofNat 64 (TrialTable32.entry i) := by
    rw [v.cursor_addr index]
    exact H.context.tableWords i index
  refine WP.mono (loadPrime_ok H.context.stack index (v.cursor_fit index) H.cursor H.candidate
    (H.context.tableRead i index 0 (by decide)) (H.context.tableRead i index 4 (by decide)) readTable)
    fun t ⟨_, _, ptr, _, M, K, _⟩ => ?_
  refine ⟨⟨H.context.keep v K (by decide) ?_, ?_, ?_, ?_, ?_⟩, ptr⟩
  · rw [M]; exact Frame.refl _ _
  · rw [M]; exact H.candidate
  · rw [M]; exact H.ending
  · rw [M]; exact H.cursor
  · rw [M]; exact H.count

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveLoadTiming.lean`, which only this module imported.
section

/-! # Static-table loads depend only on the public table index -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.RsaKeyGen.X86.Sieve

theorem StateAt.cursorLoad {g : Geometry} {c i q : Nat} {s : State} (S : StateAt g c i q s) :
    WP isa (.block [.mov .edx (.mem (slot 8))]) s fun t =>
      t.gpr .edx = g.cursor i ∧ t.gpr .esp = g.sp := by
  refine wp_movS (S.context.stack.read 8 (by decide)) fun t T _ => WP.block_nil ?_
  exact ⟨T.gpr.trans S.cursor, (T.other .esp (by decide)).trans S.context.stack.sp⟩

theorem cursorLoad_trace {g : Geometry} {c d i q : Nat} :
    RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (.block [.mov .edx (.mem (slot 8))]) (VG.X86.Taint.Agree (τr [.esp, .edx])) := by
  intro s t tr ur u z ⟨S, T⟩ E G
  have before : VG.X86.Taint.Agree (τr [.esp]) s t := agree_regs (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact S.context.stack.sp.trans T.context.stack.sp.symm)
  have trace := ((checkedBlockInvariant rfl rfl : RelCT isa
    (VG.X86.Taint.Agree (τr [.esp])) (.block [.mov .edx (.mem (slot 8))])
    (VG.X86.Taint.Agree (τr [.esp]))) _ _ _ _ _ _ before E G).1
  obtain ⟨Du, Pu⟩ := wp_result S.cursorLoad E
  obtain ⟨Dz, Pz⟩ := wp_result T.cursorLoad G
  refine ⟨trace, agree_regs ?_⟩
  intro r mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact Pu.trans Pz.symm
  · exact Du.trans Dz.symm

theorem loadPrime_trace {g : Geometry} (v : g.Valid) {c d i q : Nat} (index : i < 1024) :
    RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (.block (loadPrime stackSlots)) (fun s t => ReadControl g 0 s ∧ ReadControl g 0 t) := by
  have raw : RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (.block (loadPrime stackSlots)) (VG.X86.Taint.Agree (τr [.esp])) := by
    change RelCT isa _ (.block ([.mov .edx (.mem (slot 8))] ++ [.mov .ebx (.mem ⟨.edx, 0⟩),
      .mov .esi (.mem ⟨.edx, 4⟩), .mov .edi (.mem (slot 0)), .mov .ebp (.imm 0)])) _
    exact RelCT.block_append (RelCT.seq cursorLoad_trace
      (checkedProgramChange (hint := .block []) (τ' := τr [.esp, .edx, .ebp]) rfl rfl))
  intro s t tr ur u z ⟨S, T⟩ E G
  have trace := (raw _ _ _ _ _ _ ⟨S, T⟩ E G).1
  obtain ⟨U, Pu⟩ := wp_result (S.load v index) E
  obtain ⟨Z, Pz⟩ := wp_result (T.load v index) G
  exact ⟨trace, U.readControl Pu, Z.readControl Pz⟩

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/SieveStepTiming.lean`, which only this module imported.
section

/-! # One divisor's trace has no candidate-dependent memory address -/

section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Sieve

theorem step_trace {g : Geometry} (v : g.Valid) {c d i q : Nat} (index : i < 1024) :
    RelCT isa (fun s t => StateAt g c i q s ∧ StateAt g d i q t)
      (step stackSlots) (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  RelCT.seq (loadPrime_trace v index) (RelCT.seq (divisor_trace v) (checkedBlockInvariant rfl rfl))

end VG.Proof.RsaKeyGen.X86.Sieve
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Sieve

def SamePattern (g : Geometry) (c d : Nat) : Prop := ∀ i < g.limit, dividesAt c i = dividesAt d i

theorem loop_trace {g : Geometry} (v : g.Valid) {c d : Nat} (pattern : SamePattern g c d) :
    RelCT isa (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t)
      (loop stackSlots) (VG.X86.Taint.Agree (τr [.esp])) := by
  have raw : RelCT isa (fun s t => StateAt g c 0 g.limit s ∧ StateAt g d 0 g.limit t)
      (.loop (step stackSlots) .ne) (VG.X86.Taint.Agree (τr [.esp])) := by
    refine (RelCT.loop (M := isa) (body := step stackSlots) (c := .ne)
      (I := fun q s t => ∃ i, i < g.limit ∧ q = g.limit - i ∧ StateAt g c i q s ∧ StateAt g d i q t)
      (Q := VG.X86.Taint.Agree (τr [.esp])) ?_ g.limit).mono
      (fun _ _ H => ⟨0, v.limitPositive, rfl, H⟩) (fun _ _ H => H)
    rintro q s t tr ur u z ⟨i, index, rfl, S, T⟩ E G
    have positive : 0 < g.limit - i := by omega
    have bound : g.limit - i < 2 ^ 32 := by have := v.limitBound; omega
    have hitEq := pattern i index
    have trace := (step_trace v (by have := v.limitBound; omega) _ _ _ _ _ _ ⟨S, T⟩ E G).1
    obtain ⟨U, _, Zu, _, _⟩ := wp_result (S.step v (by have := v.limitBound; omega) positive bound) E
    obtain ⟨Z, _, Zz, _, _⟩ := wp_result (T.step v (by have := v.limitBound; omega) positive bound) G
    rw [← hitEq] at Z Zz
    have nextBound : nextCount (g.limit - i) (dividesAt c i) < 2 ^ 32 := Nat.lt_trans (nextCount_lt positive _) bound
    have eu : isa.eval .ne u = some (!decide (nextCount (g.limit - i) (dividesAt c i) = 0)) := by
      change u.zf.map Bool.not = _
      rw [Zu, countWord_zero nextBound]
      rfl
    have ez : isa.eval .ne z = some (!decide (nextCount (g.limit - i) (dividesAt c i) = 0)) := by
      change z.zf.map Bool.not = _
      rw [Zz, countWord_zero nextBound]
      rfl
    refine ⟨trace, eu.trans ez.symm, ?_, ?_⟩
    · intro _
      exact agree_regs (by
        intro r mem
        obtain rfl := List.mem_singleton.mp mem
        exact U.context.stack.sp.trans Z.context.stack.sp.symm)
    · intro next
      have nz : nextCount (g.limit - i) (dividesAt c i) ≠ 0 := by
        intro zero
        rw [eu, decide_eq_true zero] at next
        cases next
      have missed : dividesAt c i = false := by
        by_cases hit : dividesAt c i = true
        · apply False.elim
          apply nz
          rw [hit]
          rfl
        · exact Bool.eq_false_iff.mpr hit
      have count : nextCount (g.limit - i) (dividesAt c i) = g.limit - (i + 1) := by
        rw [missed]
        change g.limit - i - 1 = g.limit - (i + 1)
        omega
      exact ⟨nextCount (g.limit - i) (dividesAt c i), nextCount_lt positive _, i + 1,
        by omega, count, U, Z⟩
  exact RelCT.seq raw (checkedBlockInvariant rfl rfl)

end VG.Proof.RsaKeyGen.X86.Sieve
