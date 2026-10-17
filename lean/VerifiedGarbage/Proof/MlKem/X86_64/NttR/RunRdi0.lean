module

public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.RunA
public import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit
public meta import VerifiedGarbage.Proof.MlKem.X86_64.NttR.StLit

/-!
# ML-KEM on x86-64: the NTT on registers, the first half of pass B to `rdi`

The state after half 0 of pass B storing to `rdi`, for `vg_mlkem_ntt_avx2`, as a
literal, from that after pass A.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64.NttR

open VG.Impl.MlKem.X86_64.NttR

materialize_value stRdi0

end VG.Proof.MlKem.X86_64.NttR
