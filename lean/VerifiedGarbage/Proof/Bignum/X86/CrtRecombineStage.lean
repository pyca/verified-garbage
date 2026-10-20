module
public import VerifiedGarbage.Impl.Bignum.X86.CrtLayout
public import VerifiedGarbage.Impl.Bignum.X86.CrtRecombine
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Bignum.X86.CrtProductLayout
import VerifiedGarbage.Proof.Bignum.X86.CrtRecombine
import VerifiedGarbage.Proof.Bignum.X86.CrtLayout
import VerifiedGarbage.Proof.Mont.X86.ContextLayout

/-! # Recombine from the saved q residue into the private result slot -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont.X86.Dynamic
open VG.Impl.Bignum.X86.Crt VG.Impl.Bignum.X86

def recombineRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n productSlot, 4 * (2 * (2 * n) + 1)), (multiplierOffset, 4), (slot n resultSlot, 16 * n)]

theorem recombine_ok {s : State} {base : Addr} {bytes n : Nat}
    (hs : Scr s base bytes) (hn : 0 < n) (hz : size n ≤ bytes) :
    WP isa (crtRecombine n (slot n productSlot) (slot n qSlot) (slot n 7)
      (slot n mqSlot) (slot n resultSlot) multiplierOffset) s fun t =>
      wordsVal t.mem base (slot n resultSlot) (2 * n) =
        (wordsVal s.mem base (slot n qSlot) n * wordsVal s.mem base (slot n 7) n +
          wordsVal s.mem base (slot n mqSlot) (2 * n)) % 2 ^ (128 * n) ∧
      Outs base (recombineRanges n) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t := by
  have br := slot_bound (n := n) (i := mqSlot) (by decide)
  have bo := slot_bound (n := n) (i := resultSlot) (by decide)
  have rp := slot_le (n := n) (i := mqSlot) (j := productSlot) (by decide)
  have po := slot_le (n := n) (i := productSlot) (j := resultSlot) (by decide)
  have ro := slot_le (n := n) (i := mqSlot) (j := resultSlot) (by decide)
  have head := slot_header n mqSlot
  simp only [stride] at br bo rp po ro
  exact crtRecombine_ok hs hn (product_layout hz (by decide) (by decide) (by decide) (by decide))
    (by omega) (by omega) (by omega) (by unfold multiplierOffset; omega) (by omega) (by omega)

end VG.Proof.Bignum.X86.Crt
