module

public import VerifiedGarbage.Proof.Bignum.X86.CrtLoadPower
public import VerifiedGarbage.Proof.Bignum.X86.CopyPadded

/-! # A factor phase computes and saves its residue without losing the imported key -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

def factorRanges (n output : Nat) : List (Nat × Nat) := arithmeticRanges n ++ [(slot n output, 16 * n)]

theorem factorPower_ok {s : State} {base : Addr} {bytes n prime exponent output : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (hp : 9 ≤ prime) (hp' : prime < 16) (he : 9 ≤ exponent) (he' : exponent < 16)
    (ho : 16 ≤ output) (ho' : output < 20) :
    WP isa (factorPower n prime exponent output) s fun t =>
      let result := wordsVal s.mem base (slot n inputSlot) n ^ wordsVal s.mem base (slot n exponent) n %
        safePrime (wordsVal s.mem base (slot n prime) n)
      wordsVal t.mem base (slot n output) n = result ∧ wordsVal t.mem base (slot n output) (2 * n) = result ∧
      Outs base (factorRanges n output) s.mem t.mem ∧ Keeps powerClob s t := by
  unfold factorPower
  refine WP.seq (WP.mono (loadPower_ok hs hn hz hp hp' he he') fun u ⟨P, X, E, O, K⟩ => ?_)
  refine WP.seq (WP.mono (checkedPrimePower_ok (hs.of_keeps K (by decide)) hn hn32
    (Nat.le_trans (context_fits n) hz)) fun v ⟨C, V, Ov, Kv⟩ => ?_)
  have Ksv : Keeps powerClob s v := (K.mono (by decide)).trans Kv
  have b6 := VG.Proof.Mont.X86.Dynamic.slot_bound (n := n) (i := 6) (by decide)
  have bout := slot_bound (n := n) ho'
  have sep := VG.Proof.Mont.X86.Dynamic.slot_le (n := n) (i := 6) (j := output) (by omega)
  refine WP.mono (copyPadded_ok (hs.of_keeps Ksv (by decide)) hn
    (by have := context_fits n; unfold stride at b6; omega) (by unfold stride at bout; omega)
    (by unfold stride at sep; omega)) fun t ⟨N, W, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, ?_, Ksv.trans (Kt.mono (by decide))⟩
  · rw [N, V, X, E, P]
  · rw [W, V, X, E, P]
  · exact ((O.trans (prime_arithmetic_frame Ov)).mono (by intro r hr; exact List.mem_append_left _ hr)).trans
      (Outs.of_outside Ot (by simp [factorRanges]))

end VG.Proof.Bignum.X86.Crt
