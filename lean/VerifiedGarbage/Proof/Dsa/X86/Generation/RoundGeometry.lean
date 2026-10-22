module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Subspace
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundArguments
public import VerifiedGarbage.Proof.MillerRabin.X86.CallPre
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset

/-! The generic round uses eight argument bytes and its existing verified stack bound. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

structure RoundRoom (sp : BitVec 32) (base : Addr) (bytes : Nat) : Prop where
  low : 1184 ≤ sp.toNat
  apart : Region.Disjoint (below sp 1184) ⟨base, bytes⟩

abbrev roundCallee (g : State) (base : Addr) : State :=
  g.callEntry.withRegions [⟨argAddr g.callEntry 0, 8⟩] [⟨off base Layout.arithmetic, 12288⟩]

theorem round_compact_fit {bytes : Nat} (capacity : 40960 ≤ bytes) :
    Layout.arithmetic + 12288 ≤ bytes := by
  unfold Layout.arithmetic; omega

theorem round_args_address {base : Addr} {s g : State} (stack : g.gpr .esp = s.gpr .esp - 8#32) :
    argAddr (roundCallee g base) 0 = (below (s.gpr .esp) 8).base := by
  change argAddr g.callEntry 0 = _
  rw [argAddr_callEntry, BitVec.add_zero, stack]

theorem round_entry_frame {s g : State} {base : Addr} {bytes : Nat}
    (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : g.gpr .esp = s.gpr .esp - 8#32)
    (F : Frame [below (s.gpr .esp) 8] s.mem g.mem) :
    Frame [below (s.gpr .esp) 12] s.mem (roundCallee g base).mem := by
  change Frame _ _ g.callEntry.mem
  rw [State.callEntry_mem]
  have first := F.sub (rs' := [below (s.gpr .esp) 12]) (by
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact ⟨_, List.mem_singleton_self _, below_sub (by decide) (by have := room.low; omega)⟩)
  apply first.writeW (List.mem_singleton_self _)
  rw [stack]
  change (below (s.gpr .esp) 12).Contains ((s.gpr .esp - 8#32 - 4#32).setWidth 64) 4
  rw [show s.gpr .esp - 8#32 - 4#32 = s.gpr .esp - 12#32 by
    rw [BitVec.sub_sub]; rfl]
  exact below_top (by decide) (by have := room.low; omega) (by decide)

theorem round_workspace_same {s g : State} {base : Addr} {bytes : Nat}
    (room : RoundRoom (s.gpr .esp) base bytes) (capacity : 40960 ≤ bytes)
    (stack : g.gpr .esp = s.gpr .esp - 8#32)
    (F : Frame [below (s.gpr .esp) 8] s.mem g.mem) :
    ∀ i < 12288, (roundCallee g base).mem (off (off base Layout.arithmetic) i) =
      s.mem (off (off base Layout.arithmetic) i) := by
  intro i hi
  exact (round_entry_frame room stack F).bytes (R := ⟨off base Layout.arithmetic, 12288⟩)
    (by
      intro r hr
      rw [List.mem_singleton.mp hr]
      exact ((room.apart.sub_left (below_sub (by decide) room.low)).sub_right
        (Offset.sub_base base (round_compact_fit capacity))).symm)
    (by change 12288 ≤ 2 ^ 64; decide) hi

end VG.Proof.Dsa.X86.Generation
