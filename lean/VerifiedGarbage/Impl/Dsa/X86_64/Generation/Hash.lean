module

public import VerifiedGarbage.Impl.RsaOaep.X86_64
public import VerifiedGarbage.Impl.ICall

/-! # Seed hashing for DSA parameter generation

Reuse the verified streaming-hash sequence and its workspace layout. The
seed pointer and length occupy the hash sequence's label slots. Each seed
is 20 bytes for SHA-1 or 32 bytes for SHA-256, including the wrapped seeds
used when constructing p. The digest is written at oDig.

The search is one function for every implementation of the hash and of the
prime test: it calls the hash's `update` and `finalize` and the test by
their addresses, which its caller leaves in `rax`, `r10` and `r11` and its
entry keeps in frame words 29, 30 and 31 (`updSlot`, `finSlot`,
`primeSlot`), as `mov rax, [rsp + d]; call rax` (`viaSlot`), an indirect call
of the one function `n` (`Code.icalls`), whose printed code does not name it.
`init` is the same function for every implementation, and called directly.
-/

@[expose] public section
namespace VG.Impl.Dsa.X86_64.Generation
open VG VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

/-- The frame words holding the addresses of the hash's `update` and
`finalize` and of the prime test, at these offsets from `rsp`. -/
def updSlot : Nat := 232
def finSlot : Nat := 240
def primeSlot : Nat := 248

/-- The call of `n`, whose code is `c`, by the address in the frame word at
`rsp + d`. -/
def viaSlot (d : Nat) (n : String) (c : Prog isa) : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp d))]) (Code.icalls (.callr .rax) [(n, c)])

/-- `hashLabel H o`, with `update` and `finalize` called by the addresses in
their slots. -/
def hashLabelI (H : Stream) (o : Nat) : Prog isa :=
  Impl.Mgf1.X86_64.seqs [.block (scr .rdi oSt), .call H.initN H.initC,
    .block (scr .rdi oSt ++ [.mov32 .rsi (.imm 0), .mov .rdx (.mem (sp sLab)), .mov .rcx (.mem (sp sLabLen))] ++
      scr .r8 oW),
    viaSlot updSlot H.updN H.updC,
    .block (scr .rdi oSt ++ [.mov .rsi (.mem (sp sLabLen))] ++ scr .rdx o ++ scr .rcx oW),
    viaSlot finSlot H.finN H.finC]

/-- The generator's reviewed width determines its hash before emission. -/
def seedHashAt (sha1 sha256 : Stream) (len : Nat) : Prog isa :=
  hashLabelI (if len = 20 then sha1 else sha256) oDig

end VG.Impl.Dsa.X86_64.Generation
