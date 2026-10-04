import VerifiedGarbage.Impl.Ed448.X86_64.Verify
import VerifiedGarbage.Impl.Ed448.X86_64.ScalarBase

/-!
# Ed448 signing with a cached public key on x86-64

`vg_ed448_sign_cached(out = rdi, seed = rsi, pk = rdx, context = rcx,
ctxlen = r8, message = r9, len = [rsp + 8], scratch = [rsp + 16])`: RFC 8032
§5.2.6, with the public key `A` given (and `ctxlen ≤ 255`).

It pushes a frame of 56 words, which hold, from `rsp`: the first ten bytes
of `dom4(0, context)` (in two words), a 114-byte hash, `seed`, the other
arguments (at the offsets of `vg_ed448_verify`'s, which `out` takes the
signature's), then the challenge `k`, the pruned scalar `s` and the nonce `r`
(eight words each). Then:

* `SHAKE256(seed, 114)` into the frame, whose first 57 bytes, pruned, are
  `s` (`prune`) and whose last 57 are the prefix;
* `r`, `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)` reduced modulo `L`
  (`vg_ed448_scalar_reduce`);
* `R = [r]B`, into the first half of `out` (`vg_ed448_scalar_base`);
* `k`, `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)` reduced modulo `L`;
* `S = (r + k s) mod L`, into the second half of `out`
  (`vg_ed448_scalar_mul_add`);
* `s` and `r` cleared from the frame.

The hashes use the sponge functions as `vg_ed448_verify` does, with the
Keccak state at `scratch` and their working space at `scratch + 256`. Every
address and branch depends only on the pointers and the lengths.
-/

namespace VG.Impl.Ed448.X86_64.SignCached

open VG.X86_64
open VG.Impl.Ed448.X86_64.Verify (stk Arg callA hdr zeroSt kabs kpad ksqz fHdr fH fPk fCtx fCtxLen fMsg fLen
  fScr)

/-! ## The frame -/

/-- The slots of the frame beyond those of `vg_ed448_verify`'s, from `rsp`:
`seed`, `out` (where `vg_ed448_verify` keeps the signature), `k`, `s` and
`r`. -/
def fSeed : Nat := 136
def fOut : Nat := 240
def fK : Nat := 256
def fS : Nat := 320
def fR : Nat := 384

/-- The registers pushed (the first at `rsp + 440`): 0 for `r`, `s` and `k`,
`scratch` in `r11`, `out`, `len` in `r10`, `msg`, `ctx_len`, `ctx`, `pk`, 0,
`seed`, and 0 for the hash and the header. -/
def regs : List Reg :=
  List.replicate 24 .rax ++ [.r11, .rdi, .r10, .r9, .r8, .rcx, .rdx] ++ List.replicate 7 .rax ++ [.rsi] ++
    List.replicate 17 .rax

/-! ## `s` -/

/-- The first seven words of the hash into `r8`–`r11`, `rax`, `rcx` and `rsi`. -/
def loads : List Instr :=
  [.mov .r8 (.mem (stk (fH + 0))), .mov .r9 (.mem (stk (fH + 8))), .mov .r10 (.mem (stk (fH + 16))),
    .mov .r11 (.mem (stk (fH + 24))), .mov .rax (.mem (stk (fH + 32))), .mov .rcx (.mem (stk (fH + 40))),
    .mov .rsi (.mem (stk (fH + 48)))]

/-- Pruning (`Spec.Ed448.prune`): bits 0–1 cleared, bit 447 (the top of word
6) set, and the eighth word, whose low byte is the 57th, 0 in `rdi`. -/
def mods : List Instr :=
  [.alu .and .r8 (.imm (BitVec.ofInt 32 (-4))), .movImm64 .rdi (BitVec.ofNat 64 (2 ^ 63)),
    .alu .or .rsi (.reg .rdi), .mov32 .rdi (.imm 0)]

/-- The registers that hold the words of `s` on their way to the frame. -/
def sRegs : List Reg := [.r8, .r9, .r10, .r11, .rax, .rcx, .rsi, .rdi]

/-- The eight registers into the frame at `fS`. -/
def stores : List Instr := (List.range 8).map fun k => .store (stk (fS + 8 * k)) (sRegs.getD k .r8)

/-- The first 57 bytes of the hash, pruned, into the frame at `fS`. -/
def prune : List Instr := loads ++ (mods ++ stores)

/-! ## The hashes -/

/-- `SHAKE256(seed, 114)` into the frame at `fH`. -/
def seedHash : Prog isa :=
  .seq zeroSt <| .seq (kabs (.slot fSeed) (.imm 57) (.imm 0)) <| .seq (kpad (.imm 57)) ksqz

/-- `SHAKE256(dom4(0, C) ‖ prefix ‖ M, 114)`, the prefix the last 57 bytes of
the hash at `fH`, into the frame at `fH`. -/
def nonceHash : Prog isa :=
  .seq zeroSt <| .seq (kabs (.sp fHdr) (.imm 10) (.imm 0)) <| .seq (kabs (.slot fCtx) (.slot fCtxLen) .ret) <|
    .seq (kabs (.sp (fH + 57)) (.imm 57) .ret) <| .seq (kabs (.slot fMsg) (.slot fLen) .ret) <|
    .seq (kpad .ret) ksqz

/-- `SHAKE256(dom4(0, C) ‖ R ‖ A ‖ M, 114)`, `R` the first half of `out`,
into the frame at `fH`. -/
def chalHash : Prog isa :=
  .seq zeroSt <| .seq (kabs (.sp fHdr) (.imm 10) (.imm 0)) <| .seq (kabs (.slot fCtx) (.slot fCtxLen) .ret) <|
    .seq (kabs (.slot fOut) (.imm 57) .ret) <| .seq (kabs (.slot fPk) (.imm 57) .ret) <|
    .seq (kabs (.slot fMsg) (.slot fLen) .ret) <| .seq (kpad .ret) ksqz

/-! ## The function -/

/-- `s` and `r` cleared. -/
def wipe : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range 16).map fun k => .store (stk (fS + 8 * k)) .rax

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block hdr) <| .seq seedHash <| .seq (.block prune) <| .seq nonceHash <|
    .seq (callA "vg_ed448_scalar_reduce" scalarReduce [.sp fR, .sp fH, .slot fScr]) <|
    .seq (callA "vg_ed448_scalar_base" scalarBase [.slot fOut, .sp fR, .slot fScr]) <|
    .seq chalHash <|
    .seq (callA "vg_ed448_scalar_reduce" scalarReduce [.sp fK, .sp fH, .slot fScr]) <|
    .seq (callA "vg_ed448_scalar_mul_add" scalarMulAdd [.slotOff fOut 57, .sp fR, .sp fK, .sp fS, .slot fScr])
      (.block wipe)

/-- `vg_ed448_sign_cached`. -/
def signCached : Prog isa :=
  .seq (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)])
    (.frame (.push regs) body (.pop .r11 56))

end VG.Impl.Ed448.X86_64.SignCached
