module

public import VerifiedGarbage.Proof.Bignum.X86.CrtBothPowers
public import VerifiedGarbage.Proof.Bignum.X86.CrtCoefficientStage
public import VerifiedGarbage.Proof.Bignum.X86.CrtRecombineStage
public import VerifiedGarbage.Proof.Bignum.X86.SafePrime

/-! # Complete private arithmetic for both accepted and rejected CRT components -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt

def residueValue (x d p : Nat) : Nat := x ^ d % safePrime p

def coefficientValue (p mp mq qi : Nat) : Nat :=
  ((mp + safePrime p - mq % safePrime p) % safePrime p * qi) % safePrime p

def resultValue (p q dp dq qi x : Nat) : Nat :=
  q * coefficientValue p (residueValue x dp p) (residueValue x dq q) qi + residueValue x dq q

def computeRanges (n : Nat) : List (Nat × Nat) := powersRanges n ++ recombineRanges n

theorem compute_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hn32 : 128 * n < 2 ^ 32) (hz : size n ≤ bytes)
    (args : PowerArgs base bytes n s) :
    WP isa (compute n) s fun t =>
      wordsVal t.mem base (slot n resultSlot) (2 * n) =
        resultValue (wordsVal s.mem base (slot n pSlot) n) (wordsVal s.mem base (slot n qSlot) n)
          (wordsVal s.mem base (slot n dpSlot) n) (wordsVal s.mem base (slot n dqSlot) n)
          (wordsVal s.mem base (slot n inverseSlot) n) (wordsVal s.mem base (slot n inputSlot) n) % 2 ^ (128 * n) ∧
      Outs base (computeRanges n) s.mem t.mem ∧ Keeps powerClob s t := by
  have fit : size n ≤ 2 ^ 64 := by have := hs.nowrap; omega
  unfold compute
  refine WP.seq (WP.mono (powers_ok hs hn hn32 hz args) fun u ⟨P, _, Q, Qw, Pu, Qu, O, K⟩ => ?_)
  have QIu := powers_value O (i := inverseSlot) (k := n) (by decide) (by omega) fit
  have reduced : wordsVal u.mem base (slot n mpSlot) n < safePrime (wordsVal u.mem base (slot n pSlot) n) := by
    rw [P, Pu]
    exact Nat.mod_lt _ (by have := safePrime_gt_one (wordsVal s.mem base (slot n pSlot) n); omega)
  refine WP.seq (WP.mono (coefficient_ok (hs.of_keeps K (by decide)) hn hn32 hz reduced)
    fun v ⟨H, Ov, Kv⟩ => ?_)
  have Ksv := K.trans Kv
  have Qv := arithmetic_value Ov (i := qSlot) (k := n) (by decide) (by decide) (by omega) fit
  have MQv := arithmetic_value Ov (i := mqSlot) (k := 2 * n) (by decide) (by decide) (by omega) fit
  refine WP.mono (recombine_ok (hs.of_keeps Ksv (by decide)) hn hz) fun t ⟨V, Ot, Kt⟩ => ?_
  refine ⟨?_, ?_, Ksv.trans (Kt.mono (by decide))⟩
  · rw [V, H, Qv, MQv, Qw, P, Q, Pu, QIu, Qu]
    rfl
  · have Ov' : Outs base (powersRanges n) u.mem v.mem := Ov.mono (by
      intro r hr; exact List.mem_append_left _ hr)
    exact ((O.trans Ov').mono (by intro r hr; exact List.mem_append_left _ hr)).trans
      (Ot.mono (by intro r hr; exact List.mem_append_right _ hr))

end VG.Proof.Bignum.X86.Crt
