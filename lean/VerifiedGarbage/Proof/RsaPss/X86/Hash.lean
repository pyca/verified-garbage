module

public import VerifiedGarbage.Impl.RsaPss.X86
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Spec.Mgf1

/-!
# RSASSA-PSS on x86: what the proofs need of the hash function

The proofs are generic over a `PssHash`: the code of a Merkle–Damgård hash
function (`Impl.Pbkdf2.Md.X86.Hash`: its streaming functions, its
compression function and its digest code), what the proofs know of it
(`Proof.Pbkdf2.Md.X86.MdOk`, with which HMAC and PBKDF2 call its
compression function), the hash function as RSA's padding takes it (`G`),
that the length field `Impl.MdStream.X86.len64Of` writes in the last 8
bytes of a block is the end of its own (`lenBytes`, after zeros), that
MGF1's message `H ‖ C` and its padding fit one block, and the taint checks
of the pieces of code whose immediates depend on the hash function's sizes
(`Certs`), evaluated once for each hash function.
-/

@[expose] public section

namespace VG.Proof.RsaPss.X86

open VG VG.X86 VG.Impl.RsaPss.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Impl.RsaPkcs1Sig.X86 (argOff)

/-- The taint analysis proves `c` constant time from states that agree on `rs`. -/
abbrev TaintOk (rs : List Reg) (c : Prog isa) : Prop :=
  ∃ hc, (VG.Taint.check VG.X86.taint (τr rs) c hc).isSome = true

/-- The taint checks of the pieces whose immediates depend on the hash
function: the blocks from states where only `esp` and `ebp` are known to
agree, and the padding loop's body. -/
structure Certs (H : Hash) : Prop where
  lenSet : TaintOk [.esp, .ebp] (.block (lenSet H))
  clrB : TaintOk [.esp, .ebp] (.block (clrArgs oLen H.B))
  clrY : TaintOk [.esp, .ebp] (.block (clrArgs oY H.B))
  padArgs : TaintOk [.esp, .ebp] (.block (padArgs H))
  padBody : TaintOk [.esp, .ebp, .esi, .edi, .ebx] (.block (padBody H))
  blkSet : TaintOk [.esp, .ebp] (.block (blkSet H))
  cmpSet : TaintOk [.esp, .ebp] (.block (cmpSet H))
  selSet : TaintOk [.esp, .ebp] (.block (selSet H))
  outPart : TaintOk [.esp, .ebp] (outPart H)
  mgfSeed : TaintOk [.esp, .ebp] (.block (mgfSeed H))
  ctrSet : TaintOk [.esp, .ebp] (.block (ctrSet H))
  xorSet : TaintOk [.esp, .ebp] (.block (xorSet H))
  mgfNext : TaintOk [.esp, .ebp] (.block (mgfNext H))
  params : TaintOk [.esp, .ebp, .esi, .ecx, .edx] (.block (params H))
  cpDig16 : TaintOk [.esp, .ebp] (.block (cpDig H 16))
  cpDig4 : TaintOk [.esp, .ebp] (.block (cpDig H 4))
  lenArgs18 : TaintOk [.esp, .ebp] (.block (lenArgs H 18))
  lenArgs7 : TaintOk [.esp, .ebp] (.block (lenArgs H 7))
  cpSalt : TaintOk [.esp, .ebp] (.block (cpSalt H))
  putH : TaintOk [.esp, .ebp] (.block (putH H))
  fxSalt : TaintOk [.esp, .ebp] (.block (fxSalt H))
  cpDb : TaintOk [.esp, .ebp] (.block (cpDb H))
  passSet : TaintOk [.esp, .ebp] (.block (passSet H))
  anyLen : TaintOk [.esp, .ebp] (.block (anyLen H))
  cmpArgs : TaintOk [.esp, .ebp] (.block (cmpArgs H))

/-- What the pieces of code `Certs` checks read of a hash function: its
sizes and its digest code. The taint checks need closed code, so they are
evaluated at a hash function's shape, which is the same for all its
implementations (`Certs.of_shape`). -/
def shapeOf (H : Hash) : Hash :=
  ⟨⟨H.B, 0, H.D, 0, 0, "", .block [], "", .block [], "", .block []⟩, H.N, H.L, H.be, 0, "", .block [], H.out⟩

theorem Certs.of_shape {H : Hash} (h : Certs (shapeOf H)) : Certs H :=
  ⟨h.lenSet, h.clrB, h.clrY, h.padArgs, h.padBody, h.blkSet, h.cmpSet, h.selSet, h.outPart, h.mgfSeed,
    h.ctrSet, h.xorSet, h.mgfNext, h.params, h.cpDig16, h.cpDig4, h.lenArgs18, h.lenArgs7, h.cpSalt, h.putH,
    h.fxSalt, h.cpDb, h.passSet, h.anyLen, h.cmpArgs⟩

/-- A hash function, as RSASSA-PSS on x86 uses it. -/
structure PssHash where
  /-- Its code. -/
  H : Hash
  /-- What the proofs know of its code as a Merkle–Damgård hash function. -/
  ok : Proof.Pbkdf2.Md.X86.MdOk H
  /-- The length field of `n` bytes: zeros, then the 64-bit bit count that
  `len64Of` writes. -/
  len : ∀ n, n < 2 ^ 29 →
    ok.md.lenBytes n = List.replicate (H.L - 8) 0 ++ Proof.MdStream.bytes64 H.be (BitVec.ofNat 64 (8 * n))
  L8 : 8 ≤ H.L
  L16 : H.L ≤ 16
  NLB : H.N + H.L ≤ H.B
  /-- The hash function as RSA's padding takes it. -/
  G : Spec.Mgf1.Hash
  hash : ∀ x, G.hash x = ok.hH.SH.H.hash x
  glen : G.len = H.D
  /-- MGF1's message `H ‖ C`, `0x80` and the length field fit one block. -/
  one : H.D + 5 + H.L ≤ H.B
  /-- The taint checks. -/
  certs : Certs H

end VG.Proof.RsaPss.X86
