module

public import VerifiedGarbage.Proof.MillerRabin.X86.SquareFrame
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

/-! # Repeated squaring follows the shared Montgomery Miller–Rabin run -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.MillerRabin.X86
open VG.Spec.Rsa.Mont (arrAt numAt)

abbrev squareRun (σ ρ : State) (base : Addr) (w q0 r : Nat) (F : Bool) (n : Nat) : Nat × Bool :=
  VG.Proof.MillerRabin.Math.msqs (val32 σ.mem base 256 (2 * w)) w
    (numAt ρ.mem base w 8) r q0 (numAt ρ.mem base w 6, F) n

structure SquareState (σ ρ : State) (base : Addr) (bytes w q0 r : Nat) (F : Bool) (n : Nat) (s : State) : Prop where
  stage : Stage base bytes w σ s
  count : w32 s.mem base sQ = q0 - n
  value : numAt s.mem base w 6 = (squareRun σ ρ base w q0 r F n).1
  flag : w32 s.mem base sF = (squareRun σ ρ base w q0 r F n).2.toNat
  reduced : numAt s.mem base w 6 < val32 σ.mem base 256 (2 * w)
  frame : Frame (squareAreas base w (ρ.gpr .esp)) ρ.mem s.mem

theorem square_state_step {σ ρ s : State} {base : Addr} {bytes w q0 r n : Nat} {F : Bool}
    (facts : RoundFacts σ base bytes w) (initial : Stage base bytes w σ ρ)
    (hq : q0 < 2 ^ 31) (hr : r < 2 ^ 31) (hn : n < q0)
    (threshold : ρ.mem.readW (off base sR) 32 = BitVec.ofNat 32 r)
    (h : SquareState σ ρ base bytes w q0 r F n s) :
    WP isa sqStep s fun t => SquareState σ ρ base bytes w q0 r F (n + 1) t ∧
      t.zf = some (decide (n + 1 = q0)) := by
  have sameM := square_frame_num initial.context initial.room facts.fit
    (show 5 ≤ 8 ∧ 8 < 28 by decide) (by decide) h.frame
  have sameR := square_frame_header initial.context initial.room facts.fit (by decide : sR + 4 ≤ 256)
    (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl <;> decide) h.frame
  have count := readW_of_w32 (by omega : q0 - n < 2 ^ 32) h.count
  have boolSmall (b : Bool) : b.toNat < 2 ^ 32 := by cases b <;> decide
  have flag := readW_of_w32 (boolSmall _) h.flag
  refine WP.mono (square_step facts h.stage ⟨by omega, by omega⟩ hr count
    (sameR.trans threshold) flag h.reduced) ?_
  rintro t ⟨ht, countT, zero, valueT, flagT, frameT⟩
  have sp : s.gpr .esp = ρ.gpr .esp := h.stage.stack.trans initial.stack.symm
  rw [sp] at frameT
  have valueNext : numAt t.mem base w 6 = (squareRun σ ρ base w q0 r F (n + 1)).1 := by
    rw [h.value] at valueT
    exact valueT
  have flagNext : w32 t.mem base sF = (squareRun σ ρ base w q0 r F (n + 1)).2.toNat := by
    rw [h.value, sameM] at flagT
    exact flagT
  have pos : 0 < val32 σ.mem base 256 (2 * w) := by have := facts.odd; omega
  refine ⟨⟨ht, ?_, valueNext, flagNext, ?_, h.frame.trans frameT⟩, ?_⟩
  · simpa only [show q0 - n - 1 = q0 - (n + 1) by omega] using countT
  · rw [valueT]
    exact VG.Proof.MillerRabin.Math.mm_lt pos
  · rw [zero]
    congr 1
    exact decide_eq_decide.mpr (by omega)

theorem square_loop {σ ρ : State} {base : Addr} {bytes w q0 r : Nat} {F : Bool}
    (facts : RoundFacts σ base bytes w) (initial : Stage base bytes w σ ρ)
    (hq : 0 < q0 ∧ q0 < 2 ^ 31) (hr : r < 2 ^ 31)
    (count : w32 ρ.mem base sQ = q0)
    (threshold : ρ.mem.readW (off base sR) 32 = BitVec.ofNat 32 r)
    (flag : w32 ρ.mem base sF = F.toNat)
    (reduced : numAt ρ.mem base w 6 < val32 σ.mem base 256 (2 * w)) :
    WP isa sqLoop ρ (SquareState σ ρ base bytes w q0 r F q0) := by
  exact VG.Proof.Bignum.X86.PublicRt.countLoop hq.1 (SquareState σ ρ base bytes w q0 r F)
    (fun _ _ hn hi => square_state_step facts initial hq.2 hr hn threshold hi)
    ⟨initial, count, rfl, flag, reduced, Frame.refl _ _⟩

end VG.Proof.MillerRabin.X86
