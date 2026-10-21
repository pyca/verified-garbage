module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoad

/-! # Loading a divisor preserves every candidate and table invariant -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem StateAt.load {g : Geometry} (v : g.Valid) {c i q : Nat} {s : State}
    (H : StateAt g c i q s) (index : i < 1024) :
    WP isa (.block (loadPrime stackSlots)) s fun t => StateAt g c i q t ∧ t.gpr .edi = g.candidate := by
  have readTable : s.mem.readW ((g.cursor i).setWidth 64) 64 = BitVec.ofNat 64 (TrialTable32.entry i) := by
    rw [v.cursor_addr index]
    exact H.context.tableWords i index
  refine WP.mono (loadPrime_ok H.context.stack index (v.cursor_fit index) H.cursor H.candidate
    (H.context.tableRead i index 0 (by decide)) (H.context.tableRead i index 4 (by decide)) readTable)
    fun t ⟨_, _, ptr, _, M, K, _⟩ => ?_
  refine ⟨⟨H.context.keep v K (by decide) ?_, ?_, ?_, ?_, ?_⟩, ptr⟩
  · rw [M]; exact Frame.refl _ _
  · rw [M]; exact H.candidate
  · rw [M]; exact H.ending
  · rw [M]; exact H.cursor
  · rw [M]; exact H.count

end VG.Proof.RsaKeyGen.X86.Sieve
