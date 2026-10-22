module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoopShort
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoopDraw
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeCheck

/-! The tape check selects a complete draw or the exact shared failure result. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem loop_step (v : RoundImpl) {s₀ s : State} {base : Addr}
    {bytes n len candidate checks startLen measure drawBytes : Nat} {result : Option (Bool × List Byte)}
    {r : List Byte} {ptr : BitVec 32} {i uniform : Nat}
    (R : LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s)
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (stack : RoundRoom (s.gpr .esp) base bytes)
    (positive : 0 < n) (upper : n ≤ 48) (lower : 4 ≤ len)
    (length : len ≤ 8 * n) (aligned : len % 4 = 0) (padded : len ≤ drawBytes)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (width : Spec.RsaKeyGen.witnessBytes candidate = drawBytes)
    (drawBound : drawBytes < 2 ^ 32) (checksBound : checks < 2 ^ 32) (startBound : startLen < 2 ^ 32) :
    WP isa (primeIteration (testedDraw v.name v.code n len drawBytes checks) drawBytes) s
      (LoopStepPost s₀ base bytes n len candidate checks startLen result measure) := by
  have bound : r.length < 2 ^ 32 := Nat.lt_of_le_of_lt R.left startBound
  unfold primeIteration
  refine WP.seq (WP.mono (tape_check scr capacity bound drawBound R.remaining)
    fun a ⟨carry, memory, K⟩ => ?_)
  have A := R.of_keeps (K.mono (by decide)) memory
  have Sa := scr.of_keeps K (by decide)
  have stackA : RoundRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact stack
  refine WP.seq (WP.ite (decide (r.length < drawBytes)) carry ?_ ?_)
  · intro h
    exact loop_short A Sa capacity (by omega) width (by omega) (of_decide_eq_true h)
  · intro h
    exact loop_draw v A Sa capacity stackA positive upper lower length aligned padded bits width
      checksBound startBound (by have := of_decide_eq_false h; omega)

theorem witness_loop (v : RoundImpl) {s₀ s : State} {base : Addr}
    {bytes n len candidate checks startLen measure drawBytes : Nat} {result : Option (Bool × List Byte)}
    (scr : Scr s₀ base bytes) (capacity : 40960 ≤ bytes) (stack : RoundRoom (s₀.gpr .esp) base bytes)
    (positive : 0 < n) (upper : n ≤ 48) (lower : 4 ≤ len)
    (length : len ≤ 8 * n) (aligned : len % 4 = 0) (padded : len ≤ drawBytes)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (width : Spec.RsaKeyGen.witnessBytes candidate = drawBytes)
    (drawBound : drawBytes < 2 ^ 32) (checksBound : checks < 2 ^ 32) (startBound : startLen < 2 ^ 32)
    (ready : LoopInvariant s₀ base bytes n len candidate checks startLen result measure s) :
    WP isa (.loop (primeIteration (testedDraw v.name v.code n len drawBytes checks) drawBytes) .e) s
      fun t => ∃ r ptr, LoopResult s₀ base bytes n len candidate result r ptr t := by
  refine WP.loop (M := isa) (body := primeIteration (testedDraw v.name v.code n len drawBytes checks) drawBytes)
    (c := .e) (Q := fun t => ∃ r ptr, LoopResult s₀ base bytes n len candidate result r ptr t)
    (LoopInvariant s₀ base bytes n len candidate checks startLen result)
    (fun measure a invariant => ?_) measure s ready
  obtain ⟨r, ptr, i, uniform, R⟩ := invariant
  have Sa := scr.of_keeps R.regs (by decide)
  have stackA : RoundRoom (a.gpr .esp) base bytes := by rw [R.regs.1 .esp (by decide)]; exact stack
  exact loop_step v R Sa capacity stackA positive upper lower length aligned padded bits width drawBound checksBound startBound

end VG.Proof.Dsa.X86.Generation
