import VerifiedGarbage.Impl.Pbkdf2.Md.X86_64

/-!
# MGF1 (RFC 8017 Appendix B.2.1) on x86-64

`mgfXor`: `dst ⊕= MGF1(src, dstLen)` with a Merkle–Damgård hash function's
streaming functions (an `Impl.Pbkdf2.Md.X86_64.Stream`: `init`, `update`,
`finalize`), for a caller with a frame: the addresses and lengths are in
the caller's frame slots, and the hash function's state, the counter, the
digest and the working space of `update` and `finalize` in its working
space (`scratch`, whose address is in a slot), at the offsets of a
`Layout`. Every length is public, so this is code for any caller whose
seed and mask lengths are public (RSAES-OAEP's, RSASSA-PSS's signing).

For each counter `c` from 0, while `done = c hLen` is below `dstLen`: the
state is set by `init`, `update` absorbs `src` (`srcLen` bytes, from the
slots) and `I2OSP(c, 4)` (written big-endian to `scratch + oCtr`),
`finalize` writes the digest to `scratch + oDig`, and its first
`min(hLen, dstLen - done)` bytes are XORed into `dst + done`.

The code keeps nothing in registers across its calls (only caller-saved
registers are used); the slots `sCtr` and `sDone` hold the counter and
`done`.
-/

namespace VG.Impl.Mgf1.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)

/-! ## Operands and control -/

/-- `c₁; c₂; …`. -/
def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- `[rsp + d]`. -/
def sp (d : Nat) : MemOp := { base := .rsp, disp := (d : Int) }

/-- `[b + i + d]`. -/
def ix (b i : Reg) (d : Nat := 0) : MemOp := { base := b, index := some i, disp := (d : Int) }

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat := 0) : MemOp := { base := b, disp := (d : Int) }

/-- `add r8, 1; cmp r8, n`: the counter of a byte loop. -/
def step (n : Src) : List Instr := [.alu .add .r8 (.imm 1), .alu .cmp .r8 n]

/-- A loop over `r8` while it differs from `n` after the step. -/
def byteLoop (body : List Instr) (n : Src) : Prog isa := .loop (.block (body ++ step n)) .ne

/-! ## The layout -/

/-- Where the caller keeps what `mgfXor` uses: the frame slots (offsets
from `rsp`) of `scratch`, `src`, `srcLen`, `dst`, `dstLen`, the counter and
`done`; and the offsets in `scratch` of the hash function's streaming state,
the counter's four bytes, the digest, and the working space of `update` and
`finalize`. -/
structure Layout where
  sScr : Nat
  sSrc : Nat
  sSrcLen : Nat
  sDst : Nat
  sDstLen : Nat
  sCtr : Nat
  sDone : Nat
  oSt : Nat
  oCtr : Nat
  oDig : Nat
  oW : Nat

variable (L : Layout) (G : Stream)

/-- `d ← [scratch] + o`. -/
def scr (d : Reg) (o : Nat) : List Instr :=
  [.mov d (.mem (sp L.sScr)), .alu .add d (.imm (BitVec.ofNat 32 o))]

/-! ## One block of the mask -/

/-- `init` on the state. -/
def initArgs : List Instr := scr L .rdi L.oSt

/-- `update` of the state with `src`, after nothing. -/
def updSrcArgs : List Instr :=
  scr L .rdi L.oSt ++ [.mov32 .rsi (.imm 0), .mov .rdx (.mem (sp L.sSrc)), .mov .rcx (.mem (sp L.sSrcLen))] ++
    scr L .r8 L.oW

/-- The counter, big-endian, to `scratch + oCtr`; then `update` of the
state with those four bytes, after `src`. -/
def updCtrArgs : List Instr :=
  scr L .rdx L.oCtr ++ [.mov .rax (.mem (sp L.sCtr)), .store8 (at_ .rdx 3) .rax, .shift .shr .rax 8,
    .store8 (at_ .rdx 2) .rax, .shift .shr .rax 8, .store8 (at_ .rdx 1) .rax, .shift .shr .rax 8,
    .store8 (at_ .rdx) .rax] ++
    scr L .rdi L.oSt ++ [.mov .rsi (.mem (sp L.sSrcLen)), .mov32 .rcx (.imm 4)] ++ scr L .r8 L.oW

/-- `finalize` of the state, after `srcLen + 4` bytes, to `scratch + oDig`. -/
def finArgs : List Instr :=
  scr L .rdi L.oSt ++ [.mov .rsi (.mem (sp L.sSrcLen)), .alu .add .rsi (.imm 4)] ++ scr L .rdx L.oDig ++
    scr L .rcx L.oW

/-- `rcx` = the digest, `rdi` = `dst + done`, `r10` = `hLen`, `rax` =
`dstLen - done`, and CF set if `dstLen - done < hLen`. -/
def xorHead : List Instr :=
  scr L .rcx L.oDig ++ [.mov .rdx (.mem (sp L.sDone)), .mov .rdi (.mem (sp L.sDst)), .alu .add .rdi (.reg .rdx),
    .mov .rax (.mem (sp L.sDstLen)), .alu .sub .rax (.reg .rdx),
    .mov32 .r10 (.imm (BitVec.ofNat 32 G.D)), .alu .cmp .rax (.reg .r10)]

/-- The first `min(hLen, dstLen - done)` bytes of the digest XORed into
`dst + done`. -/
def xorOut : Prog isa :=
  seqs [.block (xorHead L G), .ite .b (.block [.mov .r10 (.reg .rax)]) (.block []), .block [.mov32 .r8 (.imm 0)],
    byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdx (ix .rdi .r8), .alu .xor .rdx (.reg .rax),
      .store8 (ix .rdi .r8) .rdx] (.reg .r10)]

/-- The next counter and `done`, and CF set while `done < dstLen`. -/
def nextCtr : List Instr :=
  [.mov .rax (.mem (sp L.sCtr)), .alu .add .rax (.imm 1), .store (sp L.sCtr) .rax, .mov .rax (.mem (sp L.sDone)),
    .alu .add .rax (.imm (BitVec.ofNat 32 G.D)), .store (sp L.sDone) .rax, .alu .cmp .rax (.mem (sp L.sDstLen))]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`. -/
def round : Prog isa :=
  seqs [.block (initArgs L), .call G.initN G.initC, .block (updSrcArgs L), .call G.updN G.updC,
    .block (updCtrArgs L), .call G.updN G.updC, .block (finArgs L), .call G.finN G.finC, xorOut L G,
    .block (nextCtr L G)]

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`. -/
def mgfXor : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (sp L.sCtr) .rax, .store (sp L.sDone) .rax]) (.loop (round L G) .b)

end VG.Impl.Mgf1.X86_64
