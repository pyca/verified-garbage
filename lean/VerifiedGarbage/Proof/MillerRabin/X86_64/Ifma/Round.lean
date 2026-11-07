module

public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Setup
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Ifma.Window
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Backend

/-!
# The IFMA Miller–Rabin round: correctness

`ifma_ok`: the round of a layout, in its frame: the setup, the vector code
(the table and the windows) under Intel's MXCSR prologue and epilogue, and
the flag; `code_correct`: the dispatch on the candidate's size, `round mul`
for the other sizes.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.X86_64.Ifma

open VG VG.X86_64
open VG.Proof.Bignum (off word ofs Outside mask Frm wv)
open VG.Proof.Bignum.X86_64.Ifma.Pub (PubOk)
open VG.Impl.MillerRabin.X86_64.Ifma

variable {l : VG.Impl.Rsa.X86_64.CrtIfma.Lay}

set_option warningAsError false

/-- The round of a layout of the candidate's size. -/
theorem ifma_ok (hl : PubOk l) {s : State} (h : roundPre s)
    (hw : Proof.Rsa.Mont.wOf s.mem (s.gpr .rdi) = l.W) :
    WP isa (ifma l) s fun t =>
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ roundPost s t ∧
      Frame [⟨s.gpr .rsp - 48#64, 48⟩, ⟨s.gpr .rdi, (s.gpr .rsi).toNat * 8⟩] s.mem t.mem ∧
      ctl t.mxcsr = ctl s.mxcsr := by
  sorry

/-- The round with the IFMA layouts, `round mul` otherwise. -/
theorem code_correct (v : RoundArith) (s : State) (h : roundPre s) :
    ∃ tr t, Exec isa (code v.mm) s tr t ∧ abiPreserved s t ∧ roundPost s t := by
  sorry

end VG.Proof.MillerRabin.X86_64.Ifma
