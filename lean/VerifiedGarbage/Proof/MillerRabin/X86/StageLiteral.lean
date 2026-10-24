module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # Initialize a public counter without disturbing prepared round data -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.X86.Wp VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem Stage.literal {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d : Nat) (scratch : scratchWord d) (value : BitVec 32) :
    WP isa (.block [.mov .eax (.imm value), .store (slot d) .eax]) s fun t =>
      Stage g capacity c p A Js (setAt V d value) (d :: Ds) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax] s t := by
  have fit : d + 4 ≤ g.L := Nat.le_trans (scratch_fit scratch) v.headerFit
  refine wp_movS rfl fun a A₁ _ => ?_
  have Ca := S.data.context.keepMem A₁.keeps (by decide) A₁.mem
  refine wp_storeS (ea_ptr Ca.ws Ca.base (d := d) (by omega))
    (ws_write Ca.ws (y := 0 + d) (n := 4) (by omega)) fun t T => WP.block_nil ?_
  have O : Outside g.W d 4 s.mem t.mem := by
    rw [T.mem, Nat.zero_add, A₁.mem]
    exact writeW32_outside _ _ _ (by have := S.data.context.ws.nowrap; omega)
  have K : Keeps [.eax] s t := A₁.keeps.widen (T.keeps [])
  have C := S.data.context.keepScalar K (by decide) O scratch
  have stored : t.mem.readW (off g.W d) 32 = value := by
    rw [T.mem, Nat.zero_add, Mem.readW_writeW_self32, A₁.gpr]
  have D := S.data.afterScalar v C d scratch value O stored
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] (by intro e mem; obtain rfl := List.mem_singleton.mp mem; exact scratch)
    outs K (by decide), scalar_roundFrame S.data.context.ws.nowrap (rs := [d])
      (by intro e mem; obtain rfl := List.mem_singleton.mp mem; exact scratch) outs, K⟩

end VG.Proof.MillerRabin.X86
