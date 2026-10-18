module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.CT
public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Instrs
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# Deterministic ECDSA on x86-64: `sign` of one hash function

For any hash function `P`, from a body's entry (`BodyIn`, in which the
streaming functions at the addresses in `r9`, `r10` and `r11` meet their
contracts), `sign` of its configuration runs to the postcondition of
`rfcX86_64` and keeps what the calling convention keeps (`sign_x86`: the
callee-saved registers and the return address by `sign_ok`, MXCSR's control
bits by `Instrs.cfgOf_fine`); and it writes `rsp` only in its frame's push and pop
(`sign_spSafe`). Constant time up to the number of candidates: `sign_ct`.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64

variable (P : RfcHash)

theorem sign_spSafe : (cfgOf P).sign.all (fun i => !isa.writesSp i) = true := (Instrs.cfgOf_fine P).2

theorem sign_x86 {E s : State} {X : List Region} (h : (rfcX86_64 P.R.E.combConsts P.I 408 X).pre s)
    (hb : BodyIn P.R.E.combConsts P.T E s) :
    ∃ t s', Exec isa (cfgOf P).sign s t s' ∧ abiPreserved s s' ∧
      (rfcX86_64 P.R.E.combConsts P.I 408 X).post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := sign_ok (P := P) h hb
  exact ⟨t, s', he, abiPreserved_of_ctl (ctlOk_of_ctlC (Instrs.cfgOf_fine P).1) he hg, hp⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
