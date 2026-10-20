module
public import VerifiedGarbage.Impl.Bignum.X86_64


/-! # FFDH parameter candidates on x86-64: load p or q into the shared workspace -/

@[expose] public section

namespace VG.Impl.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

/-- Load the big-endian bytes at rsi (rcx bytes) into the selected base array. The source may
have one leading zero byte when q needs one fewer word than p. -/
def loadNumber (a : Nat) : Prog isa := .seq (.block [.mov .rbx (.mem (hdr (sArr a)))]) loadBE

/-- Load either modulus into its candidate array. -/
def loadCandidate : Prog isa := loadNumber aN

end VG.Impl.Ffdh.X86_64.ParameterCandidate
