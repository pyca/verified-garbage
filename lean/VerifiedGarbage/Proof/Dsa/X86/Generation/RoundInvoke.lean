module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundPre
public import VerifiedGarbage.Proof.MillerRabin.X86.Backend
import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Offset

/-! Invoke every prepared-round variant through its existing verified contract. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86

theorem round_invoke (v : RoundImpl) {s g : State} {base : Addr} {bytes : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : g.gpr .esp = s.gpr .esp - 8#32)
    (F : Frame [below (s.gpr .esp) 8] s.mem g.mem)
    (first : g.mem.readW ((g.gpr .esp).setWidth 64) 32 =
      s.gpr .edi + BitVec.ofNat 32 Layout.arithmetic)
    (second : g.mem.readW ((g.gpr .esp).setWidth 64 + 4#64) 32 = 1536#32)
    (frame : below (s.gpr .esp) 8 ∈ g.wr) (work : ⟨base, bytes⟩ ∈ g.wr)
    (L : Spec.MillerRabin.Layout Spec.MillerRabin.compact s.mem (off base Layout.arithmetic) 1536)
    (P : Spec.MillerRabin.Prepared Spec.MillerRabin.compact s.mem (off base Layout.arithmetic)) :
    WP isa (.call v.name v.code) g fun t =>
      t.rd = g.rd ∧ t.wr = g.wr ∧ (∀ r ∈ calleeSaved, t.gpr r = g.gpr r) ∧
      Frame [⟨off base Layout.arithmetic, 12288⟩, below (s.gpr .esp) 1184] g.mem t.mem ∧
      ∃ u : State, u.mem = t.mem ∧ (∀ r, r ≠ .esp → u.gpr r = t.gpr r) ∧
        (Spec.MillerRabin.roundContract abi Spec.MillerRabin.compact stackBytes).post
          (roundCallee g base) u := by
  have arguments : Covers [⟨argAddr g.callEntry 0, 8⟩] g.wr := by
    apply Covers.of_mem
    intro r hr
    rw [List.mem_singleton.mp hr]
    change (⟨argAddr (roundCallee g base) 0, 8⟩ : Region) ∈ g.wr
    rw [round_args_address stack]
    exact frame
  have workspace : Covers [⟨off base Layout.arithmetic, 12288⟩] g.wr := by
    apply Covers.of_sub
    intro r hr
    rw [List.mem_singleton.mp hr]
    exact ⟨_, work, Layout.arithmetic, rfl, round_compact_fit capacity⟩
  have depth := v.stack
  have gn : (g.gpr .esp).toNat = (s.gpr .esp).toNat - 8 := by
    rw [stack, VG.X86.sub_toNat (by have := room.low; omega)]
  refine WP.call (rd := [⟨argAddr g.callEntry 0, 8⟩])
    (wr := [⟨off base Layout.arithmetic, 12288⟩])
    v.verified.1 v.noSp (by have := room.low; change stackUse v.code ≤ 1172 at depth; omega)
    (round_pre_of (round_callee_abi scr capacity room stack F first second L P))
    ((arguments.append_left workspace).right) workspace fun t rd wr saved Ft _ post => ?_
  refine ⟨rd, wr, saved, Ft.sub ?_, post⟩
  intro r hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨below (s.gpr .esp) 1184, by simp, by
      rw [stack]
      exact below_inner (by change stackUse v.code + 4 + 8 ≤ 1184; change stackUse v.code ≤ 1172 at depth; omega)
        room.low⟩

end VG.Proof.Dsa.X86.Generation
