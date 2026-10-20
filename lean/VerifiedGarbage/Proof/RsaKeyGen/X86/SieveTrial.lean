module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveContext
import VerifiedGarbage.Proof.RsaKeyGen.X86.SieveLoad
import VerifiedGarbage.Proof.RsaKeyGen.X86.TrialDivisor
import VerifiedGarbage.Proof.RsaKeyGen.TrialTable32

/-! # One static table entry tests the unchanged candidate exactly -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Sieve
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.RsaKeyGen VG.Impl.RsaKeyGen.X86.Sieve

theorem StateAt.trial {g : Geometry} (v : g.Valid) {c i q : Nat} {s : State}
    (H : StateAt g c i q s) (index : i < 1024) :
    WP isa (.seq (.block (loadPrime stackSlots)) (VG.Impl.RsaKeyGen.X86.Trial.divisor 4)) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (decide (c % tabEntry i = 0)).toNat ∧
      t.mem = s.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi] s t ∧ StackContext g.sp t := by
  have readTable : s.mem.readW ((g.cursor i).setWidth 64) 64 = BitVec.ofNat 64 (TrialTable32.entry i) := by
    rw [v.cursor_addr index]
    exact H.context.tableWords i index
  refine WP.seq (WP.mono (loadPrime_ok H.context.stack index (v.cursor_fit index) H.cursor H.candidate
    (H.context.tableRead i index 0 (by decide)) (H.context.tableRead i index 4 (by decide)) readTable)
    fun a ⟨prime, inv, ptr, zero, M, K, Ca⟩ => ?_)
  have facts := VG.Proof.RsaKeyGen.tabEntry_facts index
  have primeVal : (a.gpr .ebx).toNat = tabEntry i := by
    rw [prime, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have endValue : a.mem.readW (addr (a.gpr .esp) 4) 32 = g.candidate + BitVec.ofNat 32 (4 * (2 * g.w)) := by
    change a.mem.readW (a.ea (slot 4)) 32 = _
    rw [Ca.address 4 (by decide), M, H.ending]
    unfold Geometry.ending
    rw [show 8 * g.w = 4 * (2 * g.w) by omega]
  refine WP.mono (Trial.divisor_ok a g.candidate g.w 4 v.positive (by have := v.widthBound; omega)
    (by have := v.candidateFit; omega) (by
      intro j bound
      rw [K.2.1, K.2.2]
      exact H.context.candidateRead j bound)
    (Ca.access 4 (by decide)) endValue ptr zero
    (by rw [primeVal]; exact facts.2.1) (by rw [primeVal]; have := facts.2.2; omega)
    (by rw [primeVal]; exact facts.1) (by
      rw [primeVal, inv]
      exact VG.Proof.RsaKeyGen.TrialTable32.inverse_entry index)) fun t ⟨V, Mt, Kt⟩ => ?_
  refine ⟨?_, Mt.trans M, (K.mono (by decide)).widen Kt, Ca.keep Kt (by decide)⟩
  rw [V, M, primeVal]
  change BitVec.ofNat 32 (decide (val32 s.mem (g.candidate.setWidth 64) 0 (2 * g.w) % tabEntry i = 0)).toNat = _
  rw [H.context.candidateValue]

end VG.Proof.RsaKeyGen.X86.Sieve
