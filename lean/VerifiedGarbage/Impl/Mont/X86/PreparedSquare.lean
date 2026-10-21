module

public import VerifiedGarbage.Impl.Mont.X86.Compact

/-! # Symmetric column squares in the prepared RSA workspace

Four public values replace repeated prepared-header reads inside the square:
the working-space pointer, width, input pointer and modulus pointer. The
callee's four preserved registers occupy the first sixteen scratch bytes;
the public values occupy its sixteen-byte stack frame. Columns accumulate
the low and high halves of scalar products independently with SSE2, sharing
each off-diagonal product between the two symmetric terms.
-/

@[expose] public section
namespace VG.Impl.Mont.X86.PreparedSquare
open VG VG.X86 VG.Impl.Mont.X86

def seqs : List (Prog isa) → Prog isa
  | [] => .block []
  | [c] => c
  | c :: cs => .seq c (seqs cs)

def cache : List Instr := [
  .mov .eax (.mem (at_ .esp 4)), .mov .ecx (.mem (at_ .eax 80)),
  .store (at_ .ecx 0) .ebx, .store (at_ .ecx 4) .esi,
  .store (at_ .ecx 8) .ebp, .store (at_ .ecx 12) .edi,
  .mov .edx (.mem (at_ .esp 16)),
  .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx), .alu .add .edx (.reg .edx),
  .alu .add .edx (.reg .eax), .mov .esi (.mem (at_ .edx 64)),
  .mov .ebx (.mem (at_ .eax 48)), .mov .ebp (.mem (at_ .eax 64)),
  .mov .edi (.reg .ecx)]

def lenTimes (r : Reg) (k : Nat) : List Instr :=
  [.mov r (.mem (at_ .esp 12))] ++ List.replicate (3 + k) (.alu .add r (.reg r))

def crossBody : Prog isa := seqs [
  .block (lenTimes .eax 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .eax)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.mem (at_ .esp 8)), .mov .ebp (.reg .ecx),
    .alu .add .ecx (.reg .edx), .alu .add .ebp (.reg .esi),
    .alu .sub .ebp (.reg .edx), .alu .cmp .ecx (.reg .ebp)],
  .ite .b Rt.Square.pairLoop (.block []),
  .block [.xop (.shift .psllq .xmm0 1), .xop (.shift .psllq .xmm1 1),
    .mov .eax (.reg .esi), .alu .and .eax (.imm 4)],
  .ite .e
    (.block (([.mov .ecx (.mem (at_ .esp 8)), .mov .eax (.reg .esi), .shift .shr .eax 1,
      .alu .add .eax (.reg .ecx), .mov .eax (.mem (at_ .eax 0)), .mul .eax] : List Instr) ++ Rt.Square.accum))
    (.block [])]

def cross : Prog isa := .seq
  (.block (lenTimes .eax 1 ++ [.alu .sub .eax (.imm 4), .alu .cmp .esi (.reg .eax)]))
  (.ite .b crossBody (.block []))

def reduction : Prog isa := seqs [
  .block (lenTimes .ebx 0 ++ [.mov .edx (.reg .esi), .alu .add .edx (.imm 4), .alu .sub .edx (.reg .ebx)]),
  .ite .b (.block [.mov .edx (.imm 0)]) (.block []),
  .block [.mov .ecx (.reg .edi), .alu .add .ecx (.imm 24), .alu .add .ecx (.reg .edx),
    .mov .ebp (.mem (at_ .esp 4)), .alu .add .ebp (.reg .esi), .alu .sub .ebp (.reg .edx),
    .alu .cmp .esi (.reg .ebx)],
  .ite .b (.block [.mov .ebx (.reg .esi)]) (.block []),
  .block [.alu .add .ebx (.reg .edi), .alu .add .ebx (.imm 24), .alu .cmp .ecx (.reg .ebx)],
  .ite .b Rt.Square.redLoop (.block []),
  .block ([.movqStore (sc 16) .xmm0] ++ lenTimes .eax 0 ++ [.alu .cmp .esi (.reg .eax)]),
  .ite .b
    (.block (([.mov .edx (.mem (at_ .esp 4)), .alu .sub .edx (.imm 200), .mov .edx (.mem (at_ .edx 0)),
      .mov .eax (.mem (sc 16)), .mul .edx,
      .mov .ecx (.reg .edi), .alu .add .ecx (.imm 24), .alu .add .ecx (.reg .esi),
      .store (at_ .ecx 0) .eax, .mov .ebx (.reg .eax),
      .mov .ebp (.mem (at_ .esp 4)), .mov .eax (.mem (at_ .ebp 0)), .mul .ebx] : List Instr) ++ Rt.Square.accum))
    (.block [.mov .eax (.mem (sc 16)), .mov .ecx (.reg .edi),
      .alu .add .ecx (.imm 24), .alu .add .ecx (.reg .esi), .store (at_ .ecx 0) .eax])]

def column : Prog isa := seqs [
  .block [.xop (.bin .pxor .xmm0 (.xmm0)), .xop (.bin .pxor .xmm1 (.xmm1))],
  cross, .block Rt.Square.carryIn, reduction,
  .block ([.xop (.bin .movdqa .xmm3 (.xmm0)), .xop (.shift .psrlq .xmm3 32),
    .xop (.bin .paddq .xmm3 (.xmm1)), .alu .add .esi (.imm 4)] ++
    lenTimes .eax 1 ++ [.alu .cmp .esi (.reg .eax)])]

def columns : Prog isa := seqs [
  .block [.mov .esi (.imm 0), .xop (.bin .pxor .xmm3 (.xmm3)),
    .mov .eax (.imm (-1)), .xop (.movd .xmm7 .eax)],
  .loop column .ne,
  .block ([.mov .ebp (.reg .edi), .alu .add .ebp (.imm 24), .alu .add .ebp (.reg .esi),
    .movqStore (at_ .ebp 0) .xmm3] ++ lenTimes .eax 0 ++ [.alu .sub .ebp (.reg .eax)])]

def core : Prog isa := seqs [columns, Compact.subM, .block Rt.mask, Compact.select]

def restore : List Instr := Compact.scratchPtr ++ [
  .mov .ecx (.reg .edi), .mov .ebx (.mem (at_ .ecx 0)),
  .mov .esi (.mem (at_ .ecx 4)), .mov .ebp (.mem (at_ .ecx 8)), .mov .edi (.mem (at_ .ecx 12))]

def body : Prog isa := .seq (.block cache)
  (.frame (.push [.ebx, .esi, .ebp, .eax]) (.seq core (.block restore)) (.pop .eax 4))

def dispatch : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 16)), .mov .edx (.mem (at_ .esp 20)), .alu .cmp .eax (.reg .edx)])
    (.ite .e body Compact.body)

end VG.Impl.Mont.X86.PreparedSquare
