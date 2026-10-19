module

public import VerifiedGarbage.Impl.Bignum.X86.CrtRecombine
public import VerifiedGarbage.Proof.Bignum.X86.WideProductWords

/-! # The full-width recombination adds the q residue without truncating a valid result -/

@[expose] public section
namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem crtRecombine_ok {s : State} {base : Addr} {bytes n product q h residue out mult : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (L : WideLayout (2 * n) bytes product q h mult)
    (hr : residue + 16 * n ≤ bytes) (ho : out + 16 * n ≤ bytes)
    (rp : residue + 16 * n ≤ product ∨ product + 4 * (4 * n + 1) ≤ residue)
    (rm : residue + 16 * n ≤ mult ∨ mult + 4 ≤ residue)
    (op : out + 16 * n ≤ product ∨ product + 16 * n ≤ out)
    (orr : out + 16 * n ≤ residue ∨ residue + 16 * n ≤ out) :
    WP isa (crtRecombine n product q h residue out mult) s fun t =>
      wordsVal t.mem base out (2 * n) =
        (wordsVal s.mem base q n * wordsVal s.mem base h n + wordsVal s.mem base residue (2 * n)) % 2 ^ (128 * n) ∧
      Outs base [(product, 4 * (2 * (2 * n) + 1)), (mult, 4), (out, 16 * n)] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  unfold crtRecombine
  refine WP.seq (WP.mono (wideProductWords_ok hs hn L) fun u ⟨V, O, K⟩ => ?_)
  have R : wordsVal u.mem base residue (2 * n) = wordsVal s.mem base residue (2 * n) := by
    rw [wordsVal_eq_val32, wordsVal_eq_val32]
    apply O.val32
    · intro r mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> omega
    · have := hs.nowrap; omega
  refine WP.mono (chainAddW_ok (hs.of_keeps K (by decide)) (k := 4 * n)
    (by omega) (by omega) (by have := L.outBound; omega) (by omega) (by omega) (by omega))
    fun t ⟨Ot, ⟨c, _, Sum⟩, Kt⟩ => ?_
  have Ot' : Outside base out (16 * n) u.mem t.mem := by
    simpa only [show 4 * (4 * n) = 16 * n by omega] using Ot
  refine ⟨?_, (O.mono (by intro r mem; simp only [List.mem_cons, List.not_mem_nil, or_false] at mem ⊢; exact mem.elim Or.inl (fun h => Or.inr (Or.inl h)))).trans
    (Outs.of_outside Ot' (by simp)), K.trans (Kt.mono (by decide))⟩
  have SumMod := congrArg (· % 2 ^ (32 * (4 * n))) Sum
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod,
    Nat.mod_eq_of_lt (val32_lt t.mem base out (4 * n))] at SumMod
  rw [wordsVal_eq_val32, wordsVal_eq_val32] at V R
  rw [show 2 * (2 * n) = 4 * n by omega] at V R
  rw [V, R] at SumMod
  simpa only [wordsVal_eq_val32, Nat.add_mod, Nat.mod_mod, show 2 * (2 * n) = 4 * n by omega,
    show 32 * (4 * n) = 128 * n by omega] using SumMod

end VG.Proof.Bignum.X86
