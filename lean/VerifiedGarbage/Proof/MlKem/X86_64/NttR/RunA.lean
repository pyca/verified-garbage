module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.Run
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit

/-!
# ML-KEM on x86-64: the NTT on registers, the run of pass A

The state of `Sym.run` after pass A as a literal (`stA.lit`), which the
kernel checks once (`stA.lit_eq`); the runs of pass B start from it.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stA

end VG.Proof.MlKem.X86_64.NttR
