module
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start

import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MainCT
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Start
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.MainCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.SetupCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.FrontCT
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! # FFDH key generation on x86-64: public entry and modulus validation -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Rsa.X86_64.Crt (stk ws)

def loads : List Instr :=
  [.mov .rax (.mem (stk 4)), .mov .r10 (.mem (stk 1)), .mov .r11 (.mem (stk 2))]

def entryTail : List Instr := save .rax ++
  [.store (ws .rax sX) .rdi, .store (ws .rax sY) .rdx, .store (ws .rax sDom) .r8,
    .store (ws .rax sDomLen) .r9, .store (ws .rax sK) .r10, .store (ws .rax sRand) .r11, .mov .rdi (.reg .rax)]

theorem loads_ok (s : State) (c : GkCtx s) : WP isa (.block loads) s
    fun t => t.gpr .rax = stackArg s 3 := by
  have h3 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 32) 8 := c.ha 3 (by decide)
  have h0 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 8) 8 := c.ha 0 (by decide)
  have h1 : InRegions (s.rd ++ s.wr) (off (s.gpr .rsp) 16) 8 := c.ha 1 (by decide)
  unfold loads stk
  xrun [State.ea, hdrOff, h3, h0, h1]
  rfl

end VG.Proof.Ffdh.X86_64.GenerateKey
