module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem

/-! The small cdecl frame used by the reused runtime RSA arithmetic. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Proof.Mont.X86

theorem arithmetic_arguments {f : State}
    (low : (f.gpr .esp).toNat + 16 ≤ 2 ^ 32)
    (fr : (⟨(f.gpr .esp).setWidth 64, 16⟩ : Region) ∈ f.wr) :
    WP isa (.block arithmeticArgs) f fun t =>
      Keeps [.eax] f t ∧ Frame [⟨(f.gpr .esp).setWidth 64, 16⟩] f.mem t.mem ∧
      t.mem.readW ((f.gpr .esp).setWidth 64 + 4#64) 32 = (0 : BitVec 32) ∧
      t.mem.readW ((f.gpr .esp).setWidth 64 + 8#64) 32 = f.gpr .edi ∧
      t.mem.readW ((f.gpr .esp).setWidth 64 + 12#64) 32 = f.gpr .esi := by
  let P := (f.gpr .esp).setWidth 64
  have access {s : State} (K : Keeps [.eax] f s) {d : Nat} (hd : d + 4 ≤ 16) :
      s.ea (VG.Impl.Mont.X86.at_ .esp d) = P + BitVec.ofNat 64 d ∧
        InRegions s.wr (P + BitVec.ofNat 64 d) 4 := by
    refine ⟨?_, ⟨⟨P, 16⟩, by rw [K.2.2]; exact fr,
      Offset.contains_base _ hd (by omega)⟩⟩
    rw [VG.Impl.Mont.X86.at_, ea_mk, K.1 .esp (by decide), addr_eq (by omega)]
  unfold arithmeticArgs
  refine wp_movS rfl fun a U _ => ?_
  have A := access U.keeps (d := 4) (by decide)
  refine wp_storeS A.1 A.2 fun b B => ?_
  have Kb := U.keeps.trans (B.keeps [.eax])
  have AB := access Kb (d := 8) (by decide)
  refine wp_storeS AB.1 AB.2 fun c C => ?_
  have Kc := Kb.trans (C.keeps [.eax])
  have AC := access Kc (d := 12) (by decide)
  refine wp_storeS AC.1 AC.2 fun t T => WP.block_nil ?_
  have memory : t.mem = ((f.mem.writeW (P + 4#64) (0 : BitVec 32)).writeW (P + 8#64) (f.gpr .edi)).writeW
      (P + 12#64) (f.gpr .esi) := by
    rw [T.mem, C.mem, B.mem, U.mem, U.gpr, Kb.1 .edi (by decide), Kc.1 .esi (by decide)]
  refine ⟨Kc.trans (T.keeps [.eax]), ?_, ?_, ?_, ?_⟩
  · rw [memory]
    have store {m : Mem} (d : Nat) (v : BitVec 32) (hd : d + 4 ≤ 16)
        (F : Frame [⟨P, 16⟩] f.mem m) : Frame [⟨P, 16⟩] f.mem (m.writeW (P + BitVec.ofNat 64 d) v) :=
      F.writeW (List.mem_singleton_self _) v (Offset.contains_base _ hd (by omega))
    exact store 12 _ (by decide) (store 8 _ (by decide) (store 4 _ (by decide) (Frame.refl _ _)))
  all_goals rw [memory]
  · rw [Mem.readW_writeW_sep (w := 32) (w' := 32) (Offset.sep P (by decide : 4 + 4 ≤ 12 ∨ 12 + 4 ≤ 4) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (w := 32) (w' := 32) (Offset.sep P (by decide : 4 + 4 ≤ 8 ∨ 8 + 4 ≤ 4) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (w := 32) (w' := 32) (Offset.sep P (by decide : 8 + 4 ≤ 12 ∨ 12 + 4 ≤ 8) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32]
  · exact Mem.readW_writeW_self32 _ _ _

end VG.Proof.Dsa.X86.Generation
