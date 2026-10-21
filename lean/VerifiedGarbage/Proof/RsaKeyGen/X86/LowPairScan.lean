module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairStep
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The fixed paired-word scan returns the first nonzero word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowPair
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86 VG.Impl.RsaKeyGen.X86.LowPair

def first (m : Mem) (base : Addr) (src : Nat) :
    (BitVec 32 × BitVec 32) → Nat → Nat → BitVec 32 × BitVec 32
  | before, _, 0 => before
  | before, start, count + 1 => first m base src (select before (pairAt m base (src + 8 * start))) (start + 1) count

theorem steps_ok {s : State} {base : Addr} {size src start count : Nat} (scratch : Scr s base size)
    (fit : src + 8 * (start + count) ≤ size) :
    WP isa (steps src start count) s fun t =>
      (t.gpr .ebx, t.gpr .esi) = first s.mem base src (s.gpr .ebx, s.gpr .esi) start count ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  induction count generalizing s start with
  | zero => exact WP.block_nil ⟨rfl, rfl, Keeps.refl _ _⟩
  | succ count ih =>
    refine WP.seq (WP.mono (step_ok scratch (by omega)) fun a ⟨V, M, K⟩ => ?_)
    refine WP.mono (ih (scratch.of_keeps K (by decide)) (by omega)) fun t ⟨Vt, Mt, Kt⟩ => ?_
    exact ⟨by rw [Vt, M, V]; rfl, Mt.trans M, K.trans Kt⟩

theorem scan_ok {s : State} {base : Addr} {size src count : Nat} (scratch : Scr s base size)
    (fit : src + 8 * count ≤ size) :
    WP isa (scan src count) s fun t =>
      (t.gpr .ebx, t.gpr .esi) = first s.mem base src (0#32, 0#32) 0 count ∧
      t.mem = s.mem ∧ Keeps [.eax, .ecx, .edx, .ebx, .esi] s t := by
  refine WP.seq (wp_movS rfl fun a A _ => wp_movS rfl fun b B _ => WP.block_nil ?_)
  have K : Keeps [.ebx, .esi] s b := (A.keeps.mono (by decide)).widen B.keeps
  refine WP.mono (steps_ok (scratch.of_keeps K (by decide)) (by omega)) fun t ⟨V, M, Kt⟩ => ?_
  rw [B.mem, A.mem, B.gpr, B.other .ebx (by decide), A.gpr] at V
  exact ⟨V, M.trans (B.mem.trans A.mem), (K.mono (by decide)).trans Kt⟩

end VG.Proof.RsaKeyGen.X86.LowPair
