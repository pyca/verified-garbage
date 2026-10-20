module

public import VerifiedGarbage.Impl.Bignum.X86.PreparePrime
import VerifiedGarbage.Proof.Bignum.X86.SanitizeModulus
public import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Preparation always establishes a safe odd Montgomery modulus -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic

def primeSetupRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 7, 8 * n), (slot n 0, 8 * n)] ++ setupRanges n

theorem preparePrime_ok {s : State} {base : Addr} {bytes n m : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32)
    (hz : contextBytes n ≤ bytes) (hm : wordsVal s.mem base (slot n 0) n = m)
    (valid : Bool) (mask : s.gpr .ecx = if valid then BitVec.allOnes 32 else 0)
    (accepted : valid = true → 1 < m ∧ m % 2 = 1) :
    WP isa (preparePrime n) s fun t =>
      Context n (if valid then m else 3) base bytes t ∧
      wordsVal t.mem base (slot n 3) n = 1 ∧
      wordsVal t.mem base (slot n 4) n = 2 ^ (128 * n) % (if valid then m else 3) ∧
      Outs base (primeSetupRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 7) (by decide)
  unfold preparePrime
  refine WP.seq (WP.mono (sanitizeModulus_ok hs hn
    (by unfold stride at b0; omega) (by unfold stride at b7; omega)
    (by unfold stride at sep; omega) valid mask) fun u ⟨V, O, K⟩ => ?_)
  have gt : 1 < (if valid then m else 3) := by
    cases valid with
    | false => simp
    | true => exact (accepted rfl).1
  have odd : (if valid then m else 3) % 2 = 1 := by
    cases valid with
    | false => simp
    | true => exact (accepted rfl).2
  refine WP.mono (contextSetup_ok (hs.of_keeps K (by decide)) hn hn32 hz
    (by rw [V, hm]) gt odd) fun t ⟨C, One, R, Ot, Kt⟩ => ?_
  exact ⟨C, One, R, (O.mono (by intro r hr; exact List.mem_append_left _ hr)).trans
    (Ot.mono (by intro r hr; exact List.mem_append_right _ hr)), (K.mono (by decide)).trans Kt⟩

end VG.Proof.Bignum.X86
