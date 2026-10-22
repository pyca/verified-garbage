module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomerySetup
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryOne
public import VerifiedGarbage.Proof.Dsa.X86.Generation.MontgomeryMinusOne
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! The reusable context holds R-squared, Montgomery one and minus one. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem montgomery_constants {s : State} {base : Addr} {n m bits : Nat}
    (scr : Scr s base montgomeryBytes) (room : CallRoom (s.gpr .esp) base montgomeryBytes)
    (hn : 0 < n) (hn' : n ≤ 48) (modulus : wordsVal s.mem base (slot n 0) n = m)
    (gt : 1 < m) (odd : m % 2 = 1)
    (bitsLow : 2 ≤ bits) (bitsHigh : bits ≤ 64 * n) (top : 2 ^ (bits - 1) ≤ m) :
    WP isa (montgomeryConstants n bits) s fun t =>
      Context n m base montgomeryBytes t ∧
      wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (64 * n) * 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 6) n = 2 ^ (64 * n) % m ∧
      wordsVal t.mem base (slot n 7) n = m - 2 ^ (64 * n) % m ∧
      MontgomerySetupFrame base (s.gpr .esp) n s t ∧ Keeps powerClob s t := by
  unfold montgomeryConstants
  refine WP.seq (WP.mono (montgomery_setup scr room hn hn' modulus gt odd bitsLow bitsHigh top)
    fun u ⟨Cu, one, square, Fsu, Ksu⟩ => ?_)
  have roomU : CallRoom (u.gpr .esp) base montgomeryBytes := by
    rw [Ksu.1 .esp (by decide)]; exact room
  refine WP.seq (WP.mono (montgomery_one Cu roomU hn hn' odd one square)
    fun v ⟨Cv, encoded, squareV, Fuv, cs, rd, wr⟩ => ?_)
  have K_uv : Keeps powerClob u v := ⟨fun r hr => cs r (by
    cases r <;> simp_all [powerClob, calleeSaved]), rd, wr⟩
  refine WP.mono (montgomery_minus_one (r := 2 ^ (64 * n) % m) Cv hn (by rw [← wordsVal_eq_val32]; exact encoded)
    (Nat.mod_lt _ (by omega))) fun t ⟨Ct, minus, Fvt, Kvt⟩ => ?_
  have b4 := slot_bound (n := n) (i := 4) (by decide)
  have b3 := slot_bound (n := n) (i := 3) (by decide)
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have s47 := slot_le (n := n) (i := 4) (j := 7) (by decide)
  have s37 := slot_le (n := n) (i := 3) (j := 7) (by decide)
  have s67 := slot_le (n := n) (i := 6) (j := 7) (by decide)
  have hz := Cv.size_le
  have nw := Cv.scr.nowrap
  refine ⟨Ct, ?_, ?_, ?_, ?_, ?_, Ksu.trans (K_uv.trans (Kvt.mono (by decide)))⟩
  · rw [wordsVal_eq_val32, Fvt.val32 (.inl (by unfold stride at s37; omega))
      (by unfold stride at b3; omega), montgomery_slot_keep Cu.scr roomU Fuv hn hn'
        (show 6 < 9 by decide) (by decide) (show 3 < 9 by decide) (by decide), ← wordsVal_eq_val32]
    exact one
  · rw [wordsVal_eq_val32, Fvt.val32 (.inl (by unfold stride at s47; omega))
      (by unfold stride at b4; omega), ← wordsVal_eq_val32]
    exact squareV
  · rw [wordsVal_eq_val32, Fvt.val32 (.inl (by unfold stride at s67; omega))
      (by unfold stride at b6; omega), ← wordsVal_eq_val32]
    exact encoded
  · rw [wordsVal_eq_val32]; exact minus
  · have Fuv' := Fuv.context (show 6 < 9 by decide)
    rw [Ksu.1 .esp (by decide)] at Fuv'
    have Fvt' : Frame [⟨base, contextBytes n⟩] v.mem t.mem :=
      (Outs.of_outside Fvt (List.mem_singleton_self _)).frame (by
        intro r hr
        rw [List.mem_singleton.mp hr]
        unfold stride at b7
        exact Nat.le_trans (by omega) b7)
    exact (Fsu.trans Fuv').trans (Fvt'.sub (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨_, by simp, fun _ h => h⟩))

end VG.Proof.Dsa.X86.Generation
