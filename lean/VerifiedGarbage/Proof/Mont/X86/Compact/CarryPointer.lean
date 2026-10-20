module

public import VerifiedGarbage.Proof.Mont.X86.Compact.TimingContext
import VerifiedGarbage.Proof.Mont.X86.Compact.CarryFrame
import VerifiedGarbage.Proof.Mont.X86.Compact.Length
import VerifiedGarbage.Proof.Mont.X86.OutsZ

/-! # Carry propagation restores the row's product pointer without value assumptions -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

theorem carryUp_pointer {g : Geometry} (v : g.Valid) {s : State} (C : Context g s) (w : Nat)
    (low : g.S ≤ w) (high : w + 4 * g.N + 8 ≤ g.S + 8 * g.N + 28)
    (bp : PtrAt s g.W .ebp (w + 4 * g.N)) :
    WP isa (.block Compact.carryUp) s fun t => PtrAt t g.W .ebp w ∧
      Outs g.W g.writes s.mem t.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  have fit := v.lay.scr
  unfold Compact.carryUp
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (carryWords_frame C.ws bp (by omega)) fun a ⟨O, K⟩ => ?_)
  have writes : Outs g.W g.writes s.mem a.mem :=
    Outs.widen (Outs.of_outside O (List.mem_singleton_self _)) fun x hx r hr => by
      have outside := hx _ (List.mem_cons_self ..)
      simp only [List.mem_singleton] at hr
      subst hr
      dsimp only at *
      omega
  have Ca := C.keepK v K (by decide) writes
  refine WP.block_append (WP.mono (lenTimes_ok Ca.ws Ca.args v.base
    (by have := v.lay.header; omega) 0) fun b ⟨len, M, Kb⟩ => ?_)
  refine wp_subS rfl fun t T _ => WP.block_nil ?_
  have value : (b.gpr .eax).toNat = 4 * g.N := by
    rw [len, show 2 ^ (3 + 0) = 8 from rfl, Ca.metadata.width, Nat.mod_eq_of_lt v.n32]
  have bpB : PtrAt b g.W .ebp (w + 4 * g.N) := by
    rw [PtrAt, Kb.1 .ebp (by decide), K.1 .ebp (by decide)]; exact bp
  refine ⟨?_, ?_, ((K.mono (by decide)).trans (Kb.mono (by decide))).trans (T.keeps.mono (by decide))⟩
  · rw [PtrAt, T.gpr, ptr_sub bpB _ (by rw [value]; omega), value]
    congr 2; omega
  · rw [T.mem, M]; exact writes

end VG.Proof.Mont.X86.Compact
