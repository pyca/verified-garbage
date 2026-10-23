module

public import VerifiedGarbage.Proof.Dsa.X86.PowEntry
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
public import VerifiedGarbage.Proof.Dsa.X86.PowCore
import VerifiedGarbage.Proof.Framework.Omega

/-! # IA-32 DSA exponentiation with its callee-saved registers restored -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Pow
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86.Pow

theorem core_saved {s t : State} {base : Addr} {sp : BitVec 32} {size n : Nat} {g : Reg → BitVec 32}
    (O : OutsS base sp (coreRanges n) s.mem t.mem) (R : CallRoom sp base size) (nw : base.toNat + size ≤ 2 ^ 32)
    (hz : 24 ≤ size) (H : Saved s.mem (off base) g slots) : Saved t.mem (off base) g slots := by
  intro p hp
  have hp' : 8 ≤ p.2 ∧ p.2 + 4 ≤ 24 := by
    simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> decide
  rw [O.readW32 R nw (fun r hr => by
      simp only [coreRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [slot_lin] <;> omega) (by omega)]
  exact H p hp

theorem body_ok {s : State} {base : Addr} {size n e m : Nat}
    (E : Entry s base size) (R : CallRoom (s.gpr .esp) base size) (hz : contextBytes n ≤ size)
    (hn : 2 ≤ n) (hn48 : n ≤ 48) (he : 1 < e) (hen : e ≤ 2 * n)
    (hv : wordsVal s.mem base (slot n 0) n = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body n e) s fun t =>
      wordsVal t.mem base (slot n 6) n =
        wordsVal s.mem base (slot n 5) n ^ val32 s.mem base (slot n 8) e % m ∧
      OutsS base (s.gpr .esp) (scratch n) s.mem t.mem ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have nw := E.nowrap
  have hz24 : 24 ≤ size := by simp only [contextBytes, slot, stride] at hz; omega
  unfold body
  refine WP.seq (WP.mono (save_ok E hz24) fun u ⟨Su, Saved, Ou, Ku⟩ => ?_)
  have uesp : u.gpr .esp = s.gpr .esp := Ku.1 _ (by decide)
  have vals : ∀ {d k : Nat}, 24 ≤ d → d + 4 * k ≤ 2 ^ 64 →
      val32 u.mem base d k = val32 s.mem base d k :=
    fun hd hk => Ou.val32 (by omega) hk
  have V : wordsVal u.mem base (slot n 0) n = m := by
    rw [wordsVal_eq_val32, vals (by simp only [slot]; omega) (by simp only [slot, stride]; omega),
      ← wordsVal_eq_val32, hv]
  refine WP.seq (WP.mono (core_ok Su (by rw [uesp]; exact R) hz hn hn48 he hen V hm1 hodd)
    fun v ⟨Vv, Ov, Kv⟩ => ?_)
  rw [uesp] at Ov
  refine WP.mono (restore_ok (Su.of_keeps Kv (by decide)) hz24 (core_saved Ov R nw hz24 Saved))
    fun t R' => ⟨?_, ?_, R'.abi (by decide) (by decide) ?_, ?_, ?_⟩
  · rw [R'.mem, Vv, wordsVal_eq_val32, vals (by simp only [slot]; omega)
      (by simp only [slot, stride]; omega), vals (by simp only [slot]; omega)
      (by simp only [slot, stride]; omega), ← wordsVal_eq_val32]
  · rw [R'.mem]
    refine (OutsS.of_outs (Outs.of_outside (Ou.mono (by decide) (by decide)) (List.mem_cons_self ..))).trans ?_
    refine Ov.widen fun y hy r hr => ?_
    simp only [coreRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h0 := hy (0, 64) (List.mem_cons_self ..)
    have h1 := hy _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    rcases hr with rfl | rfl <;> dsimp only at * <;> omega
  · exact (Kv.1 _ (by decide)).trans (Ku.1 _ (by decide))
  · rw [R'.rd, Kv.2.1, Ku.2.1]
  · rw [R'.wr, Kv.2.2, Ku.2.2]

end VG.Proof.Dsa.X86.Pow
