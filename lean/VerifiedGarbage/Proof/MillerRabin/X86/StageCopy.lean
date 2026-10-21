module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
import VerifiedGarbage.Proof.MillerRabin.X86.DataCopy
import VerifiedGarbage.Proof.MillerRabin.X86.ModulusKeep

/-! # Array copies preserve all invariants needed by the next prepared product -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.copy {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (dst src : Nat) (index : dst < 28) (notMod : 0 < dst) (notScratch : dst ≠ 2 ∧ dst ≠ 3)
    (source : src ∈ Js) :
    WP isa (copy dst src) s fun t =>
      Stage g capacity c p (setAt A dst (A src)) (dst :: Js) V Ds t ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧
      Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.copy v dst src index source) fun t ⟨D, O, K⟩ => ?_
  refine ⟨⟨D, S.modulus.keepArray v S.data.context.ws.nowrap notMod O, ?_, ?_⟩, O, K⟩
  · exact S.caller.keepOuts K (by decide) (Outs.of_outside O (List.mem_singleton_self _)) (by
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      exact v.arrayFit index)
  · intro j mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact notScratch
    · exact S.noScratch j mem

end VG.Proof.MillerRabin.X86
