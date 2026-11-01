module

public import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
public import VerifiedGarbage.Impl.Rsa.X86_64.Keys
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Impl.Rsa.X86_64.Keys

@[expose] public section

namespace VG.Proof.Rsa.X86_64.InvB
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.Keys

theorem tst {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (_ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block ([.mov .r13 (.reg .r12)] : List Instr))
      (inverseN 4 5 6 7)) hc).isSome = true) : True := trivial

theorem tst2 : True := tst (by taint_decide)

end VG.Proof.Rsa.X86_64.InvB
