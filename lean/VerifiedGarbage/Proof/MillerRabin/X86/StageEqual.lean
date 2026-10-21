module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
import VerifiedGarbage.Proof.MillerRabin.X86.DataEqual
import VerifiedGarbage.Proof.MillerRabin.X86.ModulusKeep

/-! # Equality records a flag while retaining the prepared call invariants -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.equal {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (d a b : Nat) (scratch : scratchWord d) (aKnown : a ∈ Js) (bKnown : b ∈ Js) :
    WP isa (equal d a b) s fun t =>
      Stage g capacity c p A Js (setAt V d (BitVec.ofNat 32 (decide (A a = A b)).toNat)) (d :: Ds) t ∧
      Outside g.W d 4 s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.equal v d a b scratch aKnown bKnown) fun t ⟨D, O, K⟩ => ?_
  refine ⟨⟨D, S.modulus.keepScalar v S.data.context.ws.nowrap scratch O, ?_, S.noScratch⟩, O, K⟩
  exact S.caller.keepOuts K (by decide) (Outs.of_outside O (List.mem_singleton_self _)) (by
    intro r mem
    obtain rfl := List.mem_singleton.mp mem
    exact Nat.le_trans (scratch_fit scratch) v.headerFit)

end VG.Proof.MillerRabin.X86
