module

public import VerifiedGarbage.Impl.RsaPss.X86_64

/-!
# RSASSA-PSS signing with precomputed values on x86-64

`signPc(out, out_len, n, n_len, e, e_len, p, p_len, q, q_len, dp, dp_len,
dq, dq_len, qinv, qinv_len, digest, salt, salt_len, scratch, scratch_len,
pre, pre_len)`, the last seventeen on the stack: `sign`, calling
`vg_rsa_private_checked_precomputed` with `pre` as its last two stack
arguments, in the frame's words 14 and 15 (`privArgsPc`), which `sign`
leaves unused.
-/

@[expose] public section

namespace VG.Impl.RsaPss.X86_64

open VG.X86_64

/-- The arguments of `vg_rsa_private_checked_precomputed`: those of
`vg_rsa_private_checked` (`privArgs`), and `pre` and `pre_len`. -/
def privArgsPc : List Instr :=
  privArgs ++ ([.mov .rax (.mem (arg 15)), .store (sp 112) .rax, .mov .rax (.mem (arg 16)), .store (sp 120) .rax] :
    List Instr)

variable (H : Pbkdf2.Md.X86_64.Hash) (privN : String) (privC : Prog isa)

/-- After the checks: the encoding, and the private-key operation. -/
def signMainPc : Prog isa := seqs [signEnc H, .block privArgsPc, .call privN privC]

/-- The checks, then `signMainPc`. -/
def signBodyPc : Prog isa :=
  seqs [.block (signPrologue ++ n0),
    .ite .e signFail (seqs [.block smear, emLen H,
      .ite .b signFail (seqs [.block (([.mov .rdx (.mem (sp sSaltLen))] : List Instr) ++ saltFits H),
        .ite .b signFail (signMainPc H privN privC)])]),
    .block restoreRegs]

/-- `vg_rsa_pss_<H>_mgf1_<H>_sign_precomputed`. -/
def signPc : Prog isa := .frame (.alloc frameBytes) (signBodyPc H privN privC) (.free frameBytes)

end VG.Impl.RsaPss.X86_64
