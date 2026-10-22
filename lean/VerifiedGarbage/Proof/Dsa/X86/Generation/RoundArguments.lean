module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.RoundCall
public import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! Store the compact workspace pointer and size in the cdecl argument frame. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86

theorem round_arguments {s : State}
    (fit : (s.gpr .esp).toNat + 8 ≤ 2 ^ 32)
    (fr : (⟨(s.gpr .esp).setWidth 64, 8⟩ : Region) ∈ s.wr) :
    WP isa (.block roundArguments) s fun t =>
      Keeps [.eax] s t ∧ Frame [⟨(s.gpr .esp).setWidth 64, 8⟩] s.mem t.mem ∧
      t.mem.readW ((s.gpr .esp).setWidth 64) 32 =
        s.gpr .edi + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic ∧
      t.mem.readW ((s.gpr .esp).setWidth 64 + 4#64) 32 = 1536#32 := by
  have store : ∀ (t : State), Keeps [.eax] s t → ∀ k, k + 4 ≤ 8 →
      t.ea (at_ .esp k) = (s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k ∧
      InRegions t.wr ((s.gpr .esp).setWidth 64 + BitVec.ofNat 64 k) 4 := by
    intro t K k hk
    refine ⟨?_, ⟨_, by rw [K.2.2]; exact fr, Offset.contains_base _ hk (by omega)⟩⟩
    rw [at_, ea_mk, addr_eq (by rw [K.1 .esp (by decide)]; omega), K.1 .esp (by decide)]
  unfold roundArguments
  refine wp_movS rfl fun a A _ => wp_addS rfl fun b B _ => ?_
  have Kb : Keeps [.eax] s b := A.keeps.trans B.keeps
  obtain ⟨ea0, wr0⟩ := store b Kb 0 (by decide)
  simp only [BitVec.add_zero] at ea0 wr0
  refine wp_storeS ea0 wr0 fun c C => wp_movS rfl fun d D _ => ?_
  have Kd := (Kb.trans (C.keeps _)).trans D.keeps
  obtain ⟨ea4, wr4⟩ := store d Kd 4 (by decide)
  refine wp_storeS ea4 wr4 fun t T => WP.block_nil ?_
  refine ⟨Kd.trans (T.keeps _), ?_, ?_, ?_⟩
  · rw [T.mem, D.mem, C.mem, B.mem, A.mem]
    have first : (⟨(s.gpr .esp).setWidth 64, 8⟩ : Region).Contains ((s.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using Offset.contains_base ((s.gpr .esp).setWidth 64)
        (d := 0) (n := 4) (k := 8) (by decide) (by decide)
    exact ((Frame.refl [⟨(s.gpr .esp).setWidth 64, 8⟩] s.mem).writeW
      (List.mem_singleton_self _) _ first).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (d := 4) (n := 4) (k := 8) (by decide) (by decide))
  · rw [T.mem, Mem.readW_writeW_sep (Offset.sep_base _ (by decide : 4 ≤ 4)
      (by decide : 4 + 4 ≤ 2 ^ 64)) (by decide), D.mem, C.mem,
      Mem.readW_writeW_self32, B.gpr, A.gpr]
  · rw [T.mem, Mem.readW_writeW_self32, D.gpr]
    rfl

end VG.Proof.Dsa.X86.Generation
