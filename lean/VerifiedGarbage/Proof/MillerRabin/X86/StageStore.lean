module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Scalar
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # Record a known register value in one permitted scratch word -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.storeRegister {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d : Nat) (scratch : scratchWord d) (r : Reg)
    (value : BitVec 32) (regValue : s.gpr r = value) :
    WP isa (.block [.store (slot d) r]) s fun t =>
      Stage g capacity c p A Js (setAt V d value) (d :: Ds) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [] s t := by
  refine WP.mono (scalarStore_ok v S.data.context d scratch r) fun t ⟨Value, O, K, C⟩ => ?_
  rw [regValue] at Value
  have D := S.data.afterScalar v C d scratch value O Value
  have scratchList : ∀ e ∈ [d], scratchWord e := by
    intro e mem
    obtain rfl := List.mem_singleton.mp mem
    exact scratch
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] scratchList outs K (by decide),
    scalar_roundFrame S.data.context.ws.nowrap scratchList outs, K⟩

end VG.Proof.MillerRabin.X86
