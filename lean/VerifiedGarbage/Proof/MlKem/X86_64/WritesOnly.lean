import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# ML-KEM on x86-64: `writesOnly` in the form of `writesIn`

`writesOnly rs c` is `c.allInstrs (writesIn rs)` (`Wp.lean`), which asks of each
instruction only whether the registers it writes are in `rs`; `writesOnly_of`
states it for the proofs that ask for that form.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

theorem writesOnly_of {rs : List Reg} {c : Prog isa} (h : c.allInstrs (writesIn rs) = true) :
    writesOnly rs c = true := h

end VG.Proof.MlKem.X86_64
