import VerifiedGarbage.Proof.MlKem.X86_64.Wp

/-!
# ML-KEM on x86-64: `writesOnly` of code checked through its literal

`writesOnly rs c` is `c.allInstrs (writesIn rs)`; `writesOnly_of` states it
in that form, which `lit_decide` evaluates on the literal of `c`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

theorem writesOnly_of {rs : List Reg} {c : Prog isa} (h : c.allInstrs (writesIn rs) = true) :
    writesOnly rs c = true := h

end VG.Proof.MlKem.X86_64
