module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.Counter
import VerifiedGarbage.Proof.MillerRabin.X86.DataScalar
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
public import VerifiedGarbage.Impl.MillerRabin.X86.Layout

/-! # A public countdown is a prepared-stage transition -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.counterDown {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) (d q : Nat) (scratch : scratchWord d) (known : d ∈ Ds)
    (positive : 0 < q) (bound : q < 2 ^ 32) (count : V d = BitVec.ofNat 32 q) :
    WP isa (.block [.mov .eax (.mem (slot d)), .alu .sub .eax (.imm 1), .store (slot d) .eax]) s fun t =>
      Stage g capacity c p A Js (setAt V d (BitVec.ofNat 32 (q - 1))) (d :: Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax] s t := by
  have read := (S.data.slotValues d known).2.trans count
  refine WP.mono (counterDown_ok v S.data.context d q scratch positive bound read)
    fun t ⟨Count, Z, O, K, C⟩ => ?_
  have stored : t.mem.readW (off g.W d) 32 = BitVec.ofNat 32 (q - 1) := by
    apply BitVec.eq_of_toNat_eq
    change w32 t.mem g.W d = _
    rw [Count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have D := S.data.afterScalar v C d scratch _ O stored
  have scratchList : ∀ e ∈ [d], scratchWord e := by
    intro e mem
    obtain rfl := List.mem_singleton.mp mem
    exact scratch
  have outs := Outs.of_outside O (rs := slotWrites [d]) (List.mem_singleton_self _)
  exact ⟨S.afterSlots v D [d] scratchList outs K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratchList outs, K⟩

end VG.Proof.MillerRabin.X86
