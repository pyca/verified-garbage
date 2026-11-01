module

import VerifiedGarbage.TCB.X86_64.Print
meta import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.TCB.Rust
meta import VerifiedGarbage.TCB.Rust
import VerifiedGarbage.TCB.AArch64.Print
meta import VerifiedGarbage.TCB.AArch64.Print
import VerifiedGarbage.TCB.X86.Print
meta import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.TCB.Arm.Print
meta import VerifiedGarbage.TCB.Arm.Print
import VerifiedGarbage.TCB.PPC64LE.Print
meta import VerifiedGarbage.TCB.PPC64LE.Print
import VerifiedGarbage.TCB.RISCV64.Print
meta import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Artifacts.Ct.RISCV64
meta import VerifiedGarbage.Artifacts.Ct.RISCV64

/-!
# Golden tests for the trusted printers

The printers are part of the TCB but not verified; these tests pin down their
output for every construct, so that changes to them are deliberate and show
up in review.
-/

namespace VG.Test

/-- The lines of a printed function, a call shown as `<call name>`. -/
def text (ls : List Line) : List String :=
  ls.map fun
    | .text s => s
    | .call n => s!"<call {n}>"
    | .sym s .page n => s!"{s}<page {n}>"
    | .sym s .pageOff n => s!"{s}<pageoff {n}>"
    | .sym s .ripRel n => s!"{s}<riprel {n}>"
    | .sym s .x86PcRel n => s!"{s}<pcrel {n}>"
    | .sym s .armPcRel n => s!"{s}<armpcrel {n}>"
    | .sym s .ppcHa n => s!"{s}<ppcha {n}>"
    | .sym s .ppcLo n => s!"{s}<ppclo {n}>"
    | .sym s .bare n => s!"{s}<sym {n}>"

open X86_64

-- IA-32's position-independent static address is an explicit four-byte
-- frame. The ADD sets flags; releasing its scratch slot preserves them.
#guard text (X86.printer.function
    (.frame (.symPush .edx "VG_TABLE") (.block []) (.free 4) : Prog X86.isa)) ==
  ["call 2f", "2:", "mov edx, DWORD PTR [esp]", ".byte 0x81, 194", ".long <pcrel VG_TABLE>",
    "// lea esp, [esp+4]", ".byte 0x8d,0x64,0x24,0x04", "// ret", ".byte 0xc3"]

#guard Rust.line "call" (.sym ".long " .x86PcRel "VG_TABLE") ==
  "        r\".long {VG_TABLE} - 2b\",\n"

-- Neither a plain block nor an invalid frame can use symPush.
def symState : X86.State :=
  { gpr := fun r => if r = .esp then 4096 else 17
    cf := some true, zf := some false, sf := none, of := some false
    mem := fun _ => 0, rd := [], wr := [], unknowns := fun n => BitVec.ofNat 32 (8192 + n)
    syms := fun _ => 12288 }

#guard (X86.exec (.symPush .eax "VG_TABLE") symState).isNone
#guard (X86.push (.symPush .esp "VG_TABLE") symState).isNone
#guard (X86.push (.symPush .eax "VG_TABLE") (symState.setReg .esp 3)).isNone
#guard match X86.push (.symPush .eax "VG_TABLE") symState with
  | none => false
  | some s => s.gpr .esp == 4092 && s.gpr .eax == 12288 && s.gpr .edx == 17 &&
      s.mem.readW 4092 32 == 8192 && s.unknowns 0 == 8193 &&
      s.cf == some false && s.zf == some false && s.sf == some false && s.of == some false &&
      s.syms "VG_TABLE" == 12288 && s.wr == [⟨4092, 4⟩] &&
      match X86.pop (.free 4) s s with
      | none => false
      | some t => t.gpr .esp == 4096 && t.gpr .eax == 12288 && t.wr.isEmpty &&
          t.mem.readW 4092 32 == 8192

-- The ModR/M /0 encoding follows Intel's register encoding, not an
-- accidental order inferred by the assembler from the instruction text.
#guard ([X86.Reg.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi].map fun r =>
    (X86.Instr.asm (.symPush r "VG_TABLE")).getD 3 "") ==
  [".byte 0x81, 192", ".byte 0x81, 193", ".byte 0x81, 194", ".byte 0x81, 195",
    ".byte 0x81, 196", ".byte 0x81, 197", ".byte 0x81, 198", ".byte 0x81, 199"]

-- A backwards displacement carries; crossing the signed boundary overflows.
#guard match X86.push (.symPush .esi "VG_TABLE") { symState with syms := fun _ => 4096 } with
  | none => false
  | some s => s.gpr .esi == 4096 && s.cf == some true && s.of == some false
#guard match X86.push (.symPush .edi "VG_TABLE")
    { symState with unknowns := fun _ => 0x7fff0000, syms := fun _ => 0x80000000 } with
  | none => false
  | some s => s.gpr .edi == 0x80000000 && s.cf == some false && s.of == some true && s.sf == some true

/-- Every `Code` constructor, nested. -/
def sample : Prog isa :=
  .seq (.block [.alu .xor .rax (.reg .rax)])
    (.ite .ne
      (.loop (.block [.alu .add .rax (.mem { base := .rdi, index := some .rcx, scale := 8, disp := -8 }),
                      .alu .sub .rcx (.imm 1)]) .ne)
      (.block [.store { base := .rsi, disp := 16 } .rax, .mov .rdx (.imm (-1))]))

#guard text (printer.function sample) == [
  "// xor rax, rax", ".byte 0x48,0x31,0xc0",
  "jne 20f",
  "// mov QWORD PTR [rsi+16], rax", ".byte 0x48,0x89,0x46,0x10",
  "// mov rdx, -1", ".byte 0x48,0xc7,0xc2,0xff,0xff,0xff,0xff",
  "jmp 21f",
  "20:",
  "22:",
  "// add rax, QWORD PTR [rdi+rcx*8-8]", ".byte 0x48,0x03,0x44,0xcf,0xf8",
  "// sub rcx, 1", ".byte 0x48,0x83,0xe9,0x01",
  "jne 22b",
  "21:",
  "// ret", ".byte 0xc3"
]

/-! `Rust.badCall`: the first call that is not of the code it runs. -/

/-- The printed code of the functions `f`, `g` and `k`, which calls `g`. -/
def printedFG : String → Option (List Line)
  | "f" => some (printer.function (.block [.mov .rax (.imm 1)]))
  | "g" => some (printer.function (.block [.mov .rax (.imm 2)]))
  | "k" => some (printer.function (.call "g" (.block [.mov .rax (.imm 2)])))
  | _ => none

/-- `Rust.badCall` on `calls`, whose first call of each function is compared
with `printedFG` by printing it (as `Rust.printsAs` does unless it is the same
value as the function's code). -/
def badCallFG (calls : List (String × Prog isa)) : Option (String × Bool) :=
  Rust.badCall printer (fun n => (printedFG n).map fun ls =>
    match calls.find? (·.1 == n) with
    | some (_, b) => printer.function b == ls
    | none => true) calls

-- The same code written twice is two values in memory: the later call of
-- `f` is compared by its printed code.
#guard badCallFG
  [("f", .block [.mov .rax (.imm 1)]), ("g", .block [.mov .rax (.imm 2)]),
   ("f", .block [.mov .rax (.imm 1)])] == none
#guard badCallFG [("h", .block [])] == some ("h", false)
#guard badCallFG
  [("f", .block [.mov .rax (.imm 1)]), ("g", .block [.mov .rax (.imm 1)])] == some ("g", true)
-- A later call of a function whose first call is of its code.
#guard badCallFG
  [("f", .block [.mov .rax (.imm 1)]), ("f", .block [.mov .rax (.imm 2)])] == some ("f", true)
-- Calls nested in a call's code are in `Code.calls`: `k` prints as it should,
-- but the code its call of `g` runs does not.
#guard badCallFG
  (Code.calls (.seq (.call "k" (.call "g" (.block [.mov .rax (.imm 2)])))
    (.call "f" (.block [.mov .rax (.imm 1)])) : Prog isa)) == none
#guard badCallFG
  (Code.calls (.call "k" (.call "g" (.block [.mov .rax (.imm 3)])) : Prog isa)) ==
  some ("g", true)

/-- Every 32-bit instruction form. -/
def sample32 : Prog isa := .block [
  .mov32 .rax (.reg .r8),
  .mov32 .r15 (.imm 0xfffffffe),
  .mov32 .rcx (.mem { base := .rsi, disp := 60 }),
  .store32 { base := .rdi, index := some .rdx, scale := 4 } .r11,
  .alu32 .add .rbp (.imm 0x428a2f98),
  .alu32 .xor .r12 (.reg .rsp),
  .alu32 .and .r13 (.mem { base := .rcx, disp := -4 }),
  .shift32 .ror .rbx 25,
  .shift32 .shr .r9 3,
  .bswap32 .r10
]

#guard text (printer.function sample32) == [
  "// mov eax, r8d", ".byte 0x44,0x89,0xc0",
  "// mov r15d, -2", ".byte 0x41,0xbf,0xfe,0xff,0xff,0xff",
  "// mov ecx, DWORD PTR [rsi+60]", ".byte 0x8b,0x4e,0x3c",
  "// mov DWORD PTR [rdi+rdx*4], r11d", ".byte 0x44,0x89,0x1c,0x97",
  "// add ebp, 1116352408", ".byte 0x81,0xc5,0x98,0x2f,0x8a,0x42",
  "// xor r12d, esp", ".byte 0x41,0x31,0xe4",
  "// and r13d, DWORD PTR [rcx-4]", ".byte 0x44,0x23,0x69,0xfc",
  "// ror ebx, 25", ".byte 0xc1,0xcb,0x19",
  "// shr r9d, 3", ".byte 0x41,0xc1,0xe9,0x03",
  "// bswap r10d", ".byte 0x41,0x0f,0xca",
  "// ret", ".byte 0xc3"
]

/-- The byte instructions, every 8-bit register name, and 64-bit `bswap`. -/
def sample8 : Prog isa := .block ([
  .movzx8 .rax (.mk .rsi (some .rcx) 1 32),
  .movzx8 .r15 { base := .r12 },
  .bswap .rax,
  .bswap .r9] ++
  [Reg.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi,
   .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15].map (.store8 { base := .rdi, disp := -3 }))

#guard text (printer.function sample8) == [
  "// movzx eax, BYTE PTR [rsi+rcx*1+32]", ".byte 0x0f,0xb6,0x44,0x0e,0x20",
  "// movzx r15d, BYTE PTR [r12]", ".byte 0x45,0x0f,0xb6,0x3c,0x24",
  "// bswap rax", ".byte 0x48,0x0f,0xc8",
  "// bswap r9", ".byte 0x49,0x0f,0xc9",
  "// mov BYTE PTR [rdi-3], al", ".byte 0x88,0x47,0xfd",
  "// mov BYTE PTR [rdi-3], cl", ".byte 0x88,0x4f,0xfd",
  "// mov BYTE PTR [rdi-3], dl", ".byte 0x88,0x57,0xfd",
  "// mov BYTE PTR [rdi-3], bl", ".byte 0x88,0x5f,0xfd",
  "// mov BYTE PTR [rdi-3], spl", ".byte 0x40,0x88,0x67,0xfd",
  "// mov BYTE PTR [rdi-3], bpl", ".byte 0x40,0x88,0x6f,0xfd",
  "// mov BYTE PTR [rdi-3], sil", ".byte 0x40,0x88,0x77,0xfd",
  "// mov BYTE PTR [rdi-3], dil", ".byte 0x40,0x88,0x7f,0xfd",
  "// mov BYTE PTR [rdi-3], r8b", ".byte 0x44,0x88,0x47,0xfd",
  "// mov BYTE PTR [rdi-3], r9b", ".byte 0x44,0x88,0x4f,0xfd",
  "// mov BYTE PTR [rdi-3], r10b", ".byte 0x44,0x88,0x57,0xfd",
  "// mov BYTE PTR [rdi-3], r11b", ".byte 0x44,0x88,0x5f,0xfd",
  "// mov BYTE PTR [rdi-3], r12b", ".byte 0x44,0x88,0x67,0xfd",
  "// mov BYTE PTR [rdi-3], r13b", ".byte 0x44,0x88,0x6f,0xfd",
  "// mov BYTE PTR [rdi-3], r14b", ".byte 0x44,0x88,0x77,0xfd",
  "// mov BYTE PTR [rdi-3], r15b", ".byte 0x44,0x88,0x7f,0xfd",
  "// ret", ".byte 0xc3"
]

-- A displacement is encoded in 32 bits, sign-extended: the printer refuses
-- one outside `[-2^31, 2^31)`, for every kind of memory operand, and accepts
-- the bounds.
#guard printer.unencodable (.mov .rax (.mem { base := .rdi, disp := 2147483647 })) == none
#guard printer.unencodable (.store { base := .rdi, index := some .rcx, disp := -2147483648 } .rax) ==
  none
#guard printer.unencodable (.mov .rax (.mem { base := .rdi, disp := 2147483648 })) ==
  some "the displacement of the memory operand [rdi+2147483648] does not fit in 32 bits"
#guard printer.unencodable (.store { base := .rdi, index := some .rcx, disp := -2147483649 } .rax) ==
  some "the displacement of the memory operand [rdi+rcx*1-2147483649] does not fit in 32 bits"
#guard (printer.unencodable (.vmovdqu32Store { base := .rsi, disp := 4294967304 } .xmm0)).isSome
#guard (printer.unencodable (.adox .rax (.mem { base := .rsi, disp := -4294967304 }))).isSome
#guard printer.unencodable (.alu .add .rax (.imm 0x7fffffff)) == none

-- A cold branch (`Code.iteCold`): `je` to its code after the `ret`, which
-- jumps back to the code after the `ite`; the else branch falls through, with
-- no jump, so the code around the `ite` is as long as without `t`.
#guard text (printer.function
    (.seq (Code.iteCold .e (.block [.mov .rax (.imm 1)]) (.block [.mov .rax (.imm 2)]))
      (.block [.mov .rcx (.imm 3)]) : Prog isa)) ==
  ["je 20f", "// mov rax, 2", ".byte 0x48,0xc7,0xc0,0x02,0x00,0x00,0x00", "21:", "// mov rcx, 3", ".byte 0x48,0xc7,0xc1,0x03,0x00,0x00,0x00", "// ret", ".byte 0xc3", "20:", "// mov rax, 1", ".byte 0x48,0xc7,0xc0,0x01,0x00,0x00,0x00", "jmp 21b"]

-- In a loop, and nested: each cold branch's code follows the return, in the
-- order of the branches, the inner one's after the outer one's jump back.
#guard text (printer.function
    (.loop (Code.iteCold .ne
      (Code.iteCold .b (.block [.mov .rax (.imm 1)]) (.block [.mov .rax (.imm 2)]))
      (.block [.mov .rax (.imm 3)])) .ae : Prog isa)) ==
  ["20:", "jne 21f", "// mov rax, 3", ".byte 0x48,0xc7,0xc0,0x03,0x00,0x00,0x00", "22:", "jae 20b", "// ret", ".byte 0xc3",
    "21:", "jb 23f", "// mov rax, 2", ".byte 0x48,0xc7,0xc0,0x02,0x00,0x00,0x00", "24:", "jmp 22b", "23:", "// mov rax, 1", ".byte 0x48,0xc7,0xc0,0x01,0x00,0x00,0x00", "jmp 24b"]

-- An ordinary `ite` and a cold branch in one loop body: the numbers stay
-- distinct (the loop's 20, the `ite`'s 21 and 22, the cold branch's 23 and
-- 24), the `ite`'s references are forward, and the cold code, after the
-- return, jumps backward to its place in the loop.
#guard text (printer.function
    (.loop (.seq (.ite .e (.block [.mov .rax (.imm 1)]) (.block [.mov .rax (.imm 2)]))
      (Code.iteCold .ne (.block [.mov .rcx (.imm 3)]) (.block [.mov .rcx (.imm 4)]))) .ae : Prog isa)) ==
  ["20:", "je 21f", "// mov rax, 2", ".byte 0x48,0xc7,0xc0,0x02,0x00,0x00,0x00", "jmp 22f", "21:", "// mov rax, 1", ".byte 0x48,0xc7,0xc0,0x01,0x00,0x00,0x00", "22:",
    "jne 23f", "// mov rcx, 4", ".byte 0x48,0xc7,0xc1,0x04,0x00,0x00,0x00", "24:", "jae 20b", "// ret", ".byte 0xc3", "23:", "// mov rcx, 3", ".byte 0x48,0xc7,0xc1,0x03,0x00,0x00,0x00", "jmp 24b"]

-- An `ite` whose `then` branch merely starts with one empty block is not cold.
#guard text (printer.function
    (.ite .e (.seq (.block []) (.block [.mov .rax (.imm 1)])) (.block [.mov .rax (.imm 2)]) : Prog isa)) ==
  ["je 20f", "// mov rax, 2", ".byte 0x48,0xc7,0xc0,0x02,0x00,0x00,0x00", "jmp 21f", "20:", "// mov rax, 1", ".byte 0x48,0xc7,0xc0,0x01,0x00,0x00,0x00", "21:", "// ret", ".byte 0xc3"]

/-- The 64-bit shifts and `movabs`, including an immediate ≥ 2⁶³. -/
def sample64 : Prog isa := .block [
  .shift .ror .rax 28,
  .shift .ror .r15 1,
  .shift .shr .rbx 63,
  .shift .shr .r9 7,
  .movImm64 .rcx 0x428a2f98d728ae22,
  .movImm64 .r13 0xb5c0fbcfec4d3b2f,
  .movImm64 .rsi 1
]

#guard text (printer.function sample64) == [
  "// ror rax, 28", ".byte 0x48,0xc1,0xc8,0x1c",
  "// ror r15, 1", ".byte 0x49,0xd1,0xcf",
  "// shr rbx, 63", ".byte 0x48,0xc1,0xeb,0x3f",
  "// shr r9, 7", ".byte 0x49,0xc1,0xe9,0x07",
  "// movabs rcx, 4794697086780616226", ".byte 0x48,0xb9,0x22,0xae,0x28,0xd7,0x98,0x2f,0x8a,0x42",
  "// movabs r13, -5349999486874862801", ".byte 0x49,0xbd,0x2f,0x3b,0x4d,0xec,0xcf,0xfb,0xc0,0xb5",
  "// movabs rsi, 1", ".byte 0x48,0xbe,0x01,0x00,0x00,0x00,0x00,0x00,0x00,0x00",
  "// ret", ".byte 0xc3"
]

/-- Every AArch64 instruction form, and both branch conditions. -/
def sampleA64 : Prog AArch64.isa :=
  .ite (.zero .x .x2) (.block [])
    (.loop (.block [
      .add .w .x4 .x5 .x6, .add .x .x0 .x1 .x30,
      .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1,
      .logic .and .w .x7 .x8 .x9, .logic .orr .w .x7 .x8 .x9, .logic .eor .x .x7 .x8 .x9,
      .ror .w .x13 .x8 25, .lsr .w .x14 .x15 10, .rev32 .x12 .x12,
      .movz .w .x13 0x2f98 0, .movk .w .x13 0x428a 1,
      .ldr .w .x12 .x1 60, .str .w .x12 .x3 4, .ldr .x .x16 .x17 8, .str .x .x20 .x19 16,
      .sub .w .x4 .x5 .x6, .sub .x .x0 .x1 .x30, .rev .x9 .x10,
      .ldrb .x11 .x20 0, .ldrb .x21 .x22 4095, .strb .x23 .x24 7, .strb .x25 .x26 4095,
      .ldrSp .x9 0, .ldrSp .x10 32760, .strSp .x11 0, .strSp .x30 32760])
      (.nonzero .x .x2))

#guard text (AArch64.printer.function sampleA64) == [
  "cbz x2, 20f",
  "22:",
  "// add w4, w5, w6", ".inst 0x0b0600a4",
  "// add x0, x1, x30", ".inst 0x8b1e0020",
  "// add x1, x1, #64", ".inst 0x91010021",
  "// sub x2, x2, #1", ".inst 0xd1000442",
  "// and w7, w8, w9", ".inst 0x0a090107",
  "// orr w7, w8, w9", ".inst 0x2a090107",
  "// eor x7, x8, x9", ".inst 0xca090107",
  "// ror w13, w8, #25", ".inst 0x1388650d",
  "// lsr w14, w15, #10", ".inst 0x530a7dee",
  "// rev w12, w12", ".inst 0x5ac0098c",
  "// movz w13, #12184, lsl #0", ".inst 0x5285f30d",
  "// movk w13, #17034, lsl #16", ".inst 0x72a8514d",
  "// ldr w12, [x1, #60]", ".inst 0xb9403c2c",
  "// str w12, [x3, #4]", ".inst 0xb900046c",
  "// ldr x16, [x17, #8]", ".inst 0xf9400630",
  "// str x20, [x19, #16]", ".inst 0xf9000a74",
  "// sub w4, w5, w6", ".inst 0x4b0600a4",
  "// sub x0, x1, x30", ".inst 0xcb1e0020",
  "// rev x9, x10", ".inst 0xdac00d49",
  "// ldrb w11, [x20, #0]", ".inst 0x3940028b",
  "// ldrb w21, [x22, #4095]", ".inst 0x397ffed5",
  "// strb w23, [x24, #7]", ".inst 0x39001f17",
  "// strb w25, [x26, #4095]", ".inst 0x393fff59",
  "// ldr x9, [sp, #0]", ".inst 0xf94003e9",
  "// ldr x10, [sp, #32760]", ".inst 0xf97fffea",
  "// str x11, [sp, #0]", ".inst 0xf90003eb",
  "// str x30, [sp, #32760]", ".inst 0xf93ffffe",
  "cbnz x2, 22b",
  "b 21f",
  "20:",
  "21:",
  "// ret", ".inst 0xd65f03c0"
]

-- AArch64 alignment padding before a loop's head: `.p2align k`, ahead of
-- the label, and refused for any `k` but 4, 5 and 6; a NOP in the model.
#guard text (AArch64.printer.function
    (.seq (.block [.align 5]) (.loop (.block [.subImm .x .x2 .x2 1]) (.nonzero .x .x2)))) ==
  [".p2align 5", "20:", "// sub x2, x2, #1", ".inst 0xd1000442", "cbnz x2, 20b", "// ret", ".inst 0xd65f03c0"]
#guard AArch64.Instr.asm (.align 4) == [".p2align 4"]
#guard AArch64.Instr.asm (.align 6) == [".p2align 6"]
#guard [4, 5, 6].all fun k => AArch64.printer.unencodable (.align k) == none
#guard AArch64.printer.unencodable (.align 3) == some "`.p2align 3`: only 4, 5 and 6 are allowed"
#guard AArch64.printer.unencodable (.align 7) == some "`.p2align 7`: only 4, 5 and 6 are allowed"
#guard (AArch64.printer.unencodable (.align 0)).isSome
#guard AArch64.isa.requires (.align 5) == []
example (s : AArch64.State) : AArch64.exec (.align 5) s = some s := rfl
example (s : AArch64.State) : AArch64.addrs (.align 5) s = [] := rfl

/-- Every x86 (32-bit) instruction form, every operand form, and both conditions. -/
def sampleX86 : Prog X86.isa :=
  .seq (.block [.mov .eax (.mem { base := .esp, disp := 16 }), .alu .test .ebp (.reg .ebp)])
    (.ite .e (.block [])
      (.loop (.block [
        .mov .ebx (.reg .eax), .mov .ecx (.imm 0xfffffffe), .mov .edx (.mem { base := .esi }),
        .store { base := .eax, disp := 96 } .ebx,
        .alu .add .ecx (.imm 0x428a2f98), .alu .adc .ecx (.reg .edx), .alu .sub .ebp (.imm 1),
        .alu .sbb .ecx (.reg .edx), .alu .and .ebx (.mem { base := .esi, disp := 28 }),
        .alu .or .ebx (.reg .edx), .alu .xor .ebx (.reg .ecx), .alu .cmp .edi (.imm 64),
        .shift .ror .ebx 6, .shift .shr .eax 10, .bswap .eax]) .ne))

#guard text (X86.printer.function sampleX86) == [
  "// mov eax, DWORD PTR [esp+16]", ".byte 0x8b,0x44,0x24,0x10",
  "// test ebp, ebp", ".byte 0x85,0xed",
  "je 20f",
  "22:",
  "// mov ebx, eax", ".byte 0x89,0xc3",
  "// mov ecx, -2", ".byte 0xb9,0xfe,0xff,0xff,0xff",
  "// mov edx, DWORD PTR [esi]", ".byte 0x8b,0x16",
  "// mov DWORD PTR [eax+96], ebx", ".byte 0x89,0x58,0x60",
  "// add ecx, 1116352408", ".byte 0x81,0xc1,0x98,0x2f,0x8a,0x42",
  "// adc ecx, edx", ".byte 0x11,0xd1",
  "// sub ebp, 1", ".byte 0x83,0xed,0x01",
  "// sbb ecx, edx", ".byte 0x19,0xd1",
  "// and ebx, DWORD PTR [esi+28]", ".byte 0x23,0x5e,0x1c",
  "// or ebx, edx", ".byte 0x09,0xd3",
  "// xor ebx, ecx", ".byte 0x31,0xcb",
  "// cmp edi, 64", ".byte 0x83,0xff,0x40",
  "// ror ebx, 6", ".byte 0xc1,0xcb,0x06",
  "// shr eax, 10", ".byte 0xc1,0xe8,0x0a",
  "// bswap eax", ".byte 0x0f,0xc8",
  "jne 22b",
  "jmp 21f",
  "20:",
  "21:",
  "// ret", ".byte 0xc3"
]

/-- The x86 (32-bit) byte instructions, every 8-bit register name, and `jb`/`jae`. -/
def sampleX86Bytes : Prog X86.isa :=
  .seq (.block ([.movzx8 .eax { base := .esi, disp := 32 }, .movzx8 .edi { base := .ebp }] ++
      [X86.Reg8.al, .cl, .dl, .bl].map (.store8 { base := .ebx, disp := 5 })))
    (.seq (.ite .b (.block []) (.block [])) (.ite .ae (.block []) (.block [])))

#guard text (X86.printer.function sampleX86Bytes) == [
  "// movzx eax, BYTE PTR [esi+32]", ".byte 0x0f,0xb6,0x46,0x20",
  "// movzx edi, BYTE PTR [ebp]", ".byte 0x0f,0xb6,0x7d,0x00",
  "// mov BYTE PTR [ebx+5], al", ".byte 0x88,0x43,0x05",
  "// mov BYTE PTR [ebx+5], cl", ".byte 0x88,0x4b,0x05",
  "// mov BYTE PTR [ebx+5], dl", ".byte 0x88,0x53,0x05",
  "// mov BYTE PTR [ebx+5], bl", ".byte 0x88,0x5b,0x05",
  "jb 20f",
  "jmp 21f",
  "20:",
  "21:",
  "jae 22f",
  "jmp 23f",
  "22:",
  "23:",
  "// ret", ".byte 0xc3"
]

/-- Every ARMv7 instruction form, every second-operand form, and both conditions. -/
def sampleArm : Prog Arm.isa :=
  .seq (.block [.cmp .r2 (.imm 0)])
    (.ite .eq (.block [])
      (.loop (.block [
        .mov .r12 (.imm 255), .mov .lr (.reg .r4), .mov .r12 (.shifted .r8 .ror 6),
        .mov .r12 (.shifted .r8 .lsr 10), .mov .r12 (.shifted .r8 .lsl 3),
        .dp .add .r1 .r1 (.imm 64), .dp .sub .r4 .r5 (.reg .r6),
        .dp .and .r7 .r8 (.reg .lr), .dp .orr .r9 .r10 (.reg .r11),
        .dp .eor .r12 .r12 (.shifted .r8 .ror 11),
        .movw .r12 0x2f98, .movt .r12 0x428a, .rev .r12 .r12, .mul .r3 .r4 .r5,
        .mla .r6 .r7 .r8 .r9,
        .ldr .r12 .r1 60, .str .lr .r3 100, .ldrb .r5 .r6 4095, .strb .lr .r7 3, .ldrSp .r4 8,
        .subs .r2 .r2 (.imm 1)]) .ne))

#guard text (Arm.printer.function sampleArm) == [
  "cmp r2, #0",
  "beq 20f",
  "22:",
  "mov r12, #255",
  "mov lr, r4",
  "ror r12, r8, #6",
  "lsr r12, r8, #10",
  "lsl r12, r8, #3",
  "add r1, r1, #64",
  "sub r4, r5, r6",
  "and r7, r8, lr",
  "orr r9, r10, r11",
  "eor r12, r12, r8, ror #11",
  "movw r12, #12184",
  "movt r12, #17034",
  "rev r12, r12",
  "mul r3, r4, r5",
  "mla r6, r7, r8, r9",
  "ldr r12, [r1, #60]",
  "str lr, [r3, #100]",
  "ldrb r5, [r6, #4095]",
  "strb lr, [r7, #3]",
  "ldr r4, [sp, #8]",
  "subs r2, r2, #1",
  "bne 22b",
  "b 21f",
  "20:",
  "21:",
  "bx lr"
]

-- `mla` writes the low 32 bits of `n * m + a` to its register alone, flags
-- unchanged: (2³² − 1)² + 5 = 2⁶⁴ − 2³³ + 6, whose low word is 6.
#guard match Arm.exec (.mla .r0 .r1 .r1 .r2)
    { gpr := fun r => if r = .r1 then 0xffffffff else if r = .r2 then 5 else 17, sp := 4096,
      n := true, z := false, c := true, v := false, mem := fun _ => 0, rd := [], wr := [] } with
  | none => false
  | some s => s.gpr .r0 == 6 && s.gpr .r1 == 0xffffffff && s.gpr .r3 == 17 && s.n && !s.z && s.c && !s.v

/-- Every PPC64LE instruction form, and every condition. -/
def samplePPC : Prog PPC64LE.isa :=
  .seq (.ite (.zero .d .r5) (.block []) (.block []))
  (.ite (.zero .w .r6) (.block [])
    (.loop (.block [
      .add .r3 .r4 .r5, .sub .r6 .r7 .r8, .mul .r3 .r4 .r5, .mulhu .r6 .r7 .r8, .addc .r3 .r4 .r5, .adde .r6 .r7 .r8,
      .addze .r9 .r10, .subc .r3 .r4 .r5, .sube .r6 .r7 .r8, .addi .r4 .r4 64, .subi .r5 .r5 1, .subi .r5 .r5 32768,
      .li .r9 32767, .lis .r10 0x428a, .lis .r10 0xb5c0, .ori .r10 .r10 0x2f98,
      .oris .r11 .r11 0xffff,
      .logic .and .r0 .r2 .r31, .logic .or .r14 .r15 .r16, .logic .xor .r17 .r18 .r19,
      .rotr .w .r12 .r8 25, .rotr .w .r12 .r8 0, .rotr .d .r12 .r8 28, .rotr .d .r12 .r8 0,
      .lsr .w .r20 .r21 10, .lsr .w .r20 .r21 0, .lsr .d .r22 .r23 7, .lsl .r24 .r25 32,
      .load .w .r12 .r4 60, .load .d .r26 .r27 32764, .store .w .r12 .r3 4, .store .d .r28 .r29 8,
      .lbz .r30 .r4 0, .stb .r30 .r3 32767,
      .loadRev .w .r7 .r4 .r8, .loadRev .d .r7 .r4 .r8, .storeRev .w .r7 .r3 .r8,
      .storeRev .d .r7 .r3 .r0,
      .mflr .r0, .mtlr .r0]) (.nonzero .w .r5)))

#guard text (PPC64LE.printer.function samplePPC) == [
  "// cmpldi %cr0, %r5, 0", ".long 0x28250000",
  "beq %cr0, 20f",
  "b 21f",
  "20:",
  "21:",
  "// cmplwi %cr0, %r6, 0", ".long 0x28060000",
  "beq %cr0, 22f",
  "24:",
  "// add %r3, %r4, %r5", ".long 0x7c642a14",
  "// subf %r6, %r8, %r7", ".long 0x7cc83850",
  "// mulld %r3, %r4, %r5", ".long 0x7c6429d2",
  "// mulhdu %r6, %r7, %r8", ".long 0x7cc74012",
  "// addc %r3, %r4, %r5", ".long 0x7c642814",
  "// adde %r6, %r7, %r8", ".long 0x7cc74114",
  "// addze %r9, %r10", ".long 0x7d2a0194",
  "// subfc %r3, %r5, %r4", ".long 0x7c652010",
  "// subfe %r6, %r8, %r7", ".long 0x7cc83910",
  "// addi %r4, %r4, 64", ".long 0x38840040",
  "// addi %r5, %r5, -1", ".long 0x38a5ffff",
  "// addi %r5, %r5, -32768", ".long 0x38a58000",
  "// li %r9, 32767", ".long 0x39207fff",
  "// lis %r10, 17034", ".long 0x3d40428a",
  "// lis %r10, -19008", ".long 0x3d40b5c0",
  "// ori %r10, %r10, 12184", ".long 0x614a2f98",
  "// oris %r11, %r11, 65535", ".long 0x656bffff",
  "// and %r0, %r2, %r31", ".long 0x7c40f838",
  "// or %r14, %r15, %r16", ".long 0x7dee8378",
  "// xor %r17, %r18, %r19", ".long 0x7e519a78",
  "// rlwinm %r12, %r8, 7, 0, 31", ".long 0x550c383e",
  "// rlwinm %r12, %r8, 0, 0, 31", ".long 0x550c003e",
  "// rldicl %r12, %r8, 36, 0", ".long 0x790c2002",
  "// rldicl %r12, %r8, 0, 0", ".long 0x790c0000",
  "// rlwinm %r20, %r21, 22, 10, 31", ".long 0x56b4b2be",
  "// rlwinm %r20, %r21, 0, 0, 31", ".long 0x56b4003e",
  "// rldicl %r22, %r23, 57, 7", ".long 0x7af6c9c2",
  "// rldicr %r24, %r25, 32, 31", ".long 0x7b3807c6",
  "// lwz %r12, 60(%r4)", ".long 0x8184003c",
  "// ld %r26, 32764(%r27)", ".long 0xeb5b7ffc",
  "// stw %r12, 4(%r3)", ".long 0x91830004",
  "// std %r28, 8(%r29)", ".long 0xfb9d0008",
  "// lbz %r30, 0(%r4)", ".long 0x8bc40000",
  "// stb %r30, 32767(%r3)", ".long 0x9bc37fff",
  "// lwbrx %r7, %r4, %r8", ".long 0x7ce4442c",
  "// ldbrx %r7, %r4, %r8", ".long 0x7ce44428",
  "// stwbrx %r7, %r3, %r8", ".long 0x7ce3452c",
  "// stdbrx %r7, %r3, %r0", ".long 0x7ce30528",
  "// mflr %r0", ".long 0x7c0802a6",
  "// mtlr %r0", ".long 0x7c0803a6",
  "// cmplwi %cr0, %r5, 0", ".long 0x28050000",
  "bne %cr0, 24b",
  "b 23f",
  "22:",
  "23:",
  "// blr", ".long 0x4e800020"
]

-- Every register name.
#guard ([PPC64LE.Reg.r0, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15,
    .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].map PPC64LE.Reg.name) ==
  ["%r0", "%r2", "%r3", "%r4", "%r5", "%r6", "%r7", "%r8", "%r9", "%r10", "%r11", "%r12",
   "%r14", "%r15", "%r16", "%r17", "%r18", "%r19", "%r20", "%r21", "%r22", "%r23", "%r24",
   "%r25", "%r26", "%r27", "%r28", "%r29", "%r30", "%r31"]

/-- Every RISC-V instruction form, and every condition. -/
def sampleRV : Prog RISCV64.isa :=
  .seq (.ite (.zero .a5) (.block []) (.block []))
  (.seq (.ite (.eq .a0 .a1) (.block []) (.block []))
  (.seq (.ite (.ne .a2 .a3) (.block []) (.block []))
  (.seq (.ite (.geu .a4 .a5) (.block []) (.block []))
  (.ite (.ltu .t0 .t1) (.block [])
    (.loop (.block [
      .add .a0 .a1 .a2, .sub .a3 .a4 .a5, .addw .a6 .a7 .t0, .subw .t1 .t2 .t3,
      .sltu .t4 .t5 .t6, .mul .a0 .a1 .a2, .mulhu .a3 .a4 .a5, .logic .and .s0 .s1 .s2, .logic .or .s3 .s4 .s5,
      .logic .xor .s6 .s7 .s8, .addi .s9 .s10 2047, .addi .s11 .ra (-2048), .addiw .a0 .a0 (-1),
      .logicImm .and .a1 .a1 255, .logicImm .or .a2 .a2 (-2048), .logicImm .xor .a3 .a3 (-1),
      .li .a4 (-1), .li .a4 2047, .lui .a5 0x6a09e, .lui .a5 0xfffff,
      .shift .sll .d .a6 .a6 63, .shift .srl .d .a6 .a6 1, .shift .sra .d .a6 .a6 0,
      .shift .sll .w .a7 .a7 31, .shift .srl .w .a7 .a7 7, .shift .sra .w .a7 .a7 0,
      .shiftReg .sll .d .a6 .a6 .a5, .shiftReg .srl .d .t0 .t1 .t2, .shiftReg .sra .d .s0 .s1 .s2,
      .shiftReg .sll .w .a7 .a7 .a5, .shiftReg .srl .w .t3 .t4 .t5, .shiftReg .sra .w .s3 .s4 .s5,
      .load .b .t0 .a0 0, .load .h .t0 .a0 2046, .load .w .t1 .a1 4, .load .d .t2 .a2 2040,
      .store .b .t0 .a0 2047, .store .h .t0 .a0 0, .store .w .t1 .a1 4, .store .d .t2 .a2 8,
      .addSp .a0 2047, .lla .s1 "VG_TABLE"]) (.nonzero .t6))))))

#guard text (RISCV64.printer.function sampleRV) == [
  "beqz a5, 20f",
  "j 21f",
  "20:",
  "21:",
  "beq a0, a1, 22f",
  "j 23f",
  "22:",
  "23:",
  "bne a2, a3, 24f",
  "j 25f",
  "24:",
  "25:",
  "bgeu a4, a5, 26f",
  "j 27f",
  "26:",
  "27:",
  "bltu t0, t1, 28f",
  "210:",
  "// add a0, a1, a2", ".insn 4, 0x00c58533",
  "// sub a3, a4, a5", ".insn 4, 0x40f706b3",
  "// addw a6, a7, t0", ".insn 4, 0x0058883b",
  "// subw t1, t2, t3", ".insn 4, 0x41c3833b",
  "// sltu t4, t5, t6", ".insn 4, 0x01ff3eb3",
  "// mul a0, a1, a2", ".insn 4, 0x02c58533",
  "// mulhu a3, a4, a5", ".insn 4, 0x02f736b3",
  "// and s0, s1, s2", ".insn 4, 0x0124f433",
  "// or s3, s4, s5", ".insn 4, 0x015a69b3",
  "// xor s6, s7, s8", ".insn 4, 0x018bcb33",
  "// addi s9, s10, 2047", ".insn 4, 0x7ffd0c93",
  "// addi s11, ra, -2048", ".insn 4, 0x80008d93",
  "// addiw a0, a0, -1", ".insn 2, 0x357d",
  "// andi a1, a1, 255", ".insn 4, 0x0ff5f593",
  "// ori a2, a2, -2048", ".insn 4, 0x80066613",
  "// xori a3, a3, -1", ".insn 4, 0xfff6c693",
  "// addi a4, zero, -1", ".insn 2, 0x577d",
  "// addi a4, zero, 2047", ".insn 4, 0x7ff00713",
  "// lui a5, 434334", ".insn 4, 0x6a09e7b7",
  "// lui a5, 1048575", ".insn 2, 0x77fd",
  "// slli a6, a6, 63", ".insn 2, 0x187e",
  "// srli a6, a6, 1", ".insn 4, 0x00185813",
  "// srai a6, a6, 0", ".insn 4, 0x40085813",
  "// slliw a7, a7, 31", ".insn 4, 0x01f8989b",
  "// srliw a7, a7, 7", ".insn 4, 0x0078d89b",
  "// sraiw a7, a7, 0", ".insn 4, 0x4008d89b",
  "// sll a6, a6, a5", ".insn 4, 0x00f81833",
  "// srl t0, t1, t2", ".insn 4, 0x007352b3",
  "// sra s0, s1, s2", ".insn 4, 0x4124d433",
  "// sllw a7, a7, a5", ".insn 4, 0x00f898bb",
  "// srlw t3, t4, t5", ".insn 4, 0x01eede3b",
  "// sraw s3, s4, s5", ".insn 4, 0x415a59bb",
  "// lbu t0, 0(a0)", ".insn 4, 0x00054283",
  "// lhu t0, 2046(a0)", ".insn 4, 0x7fe55283",
  "// lwu t1, 4(a1)", ".insn 4, 0x0045e303",
  "// ld t2, 2040(a2)", ".insn 4, 0x7f863383",
  "// sb t0, 2047(a0)", ".insn 4, 0x7e550fa3",
  "// sh t0, 0(a0)", ".insn 4, 0x00551023",
  "// sw t1, 4(a1)", ".insn 4, 0x0065a223",
  "// sd t2, 8(a2)", ".insn 4, 0x00763423",
  "// addi a0, sp, 2047", ".insn 4, 0x7ff10513",
  "lla s1, <sym VG_TABLE>",
  "bnez t6, 210b",
  "j 29f",
  "28:",
  "29:",
  "// ret", ".insn 2, 0x8082"
]

-- Each base instruction is its machine code (`Encode.lean`), after its
-- text as a comment: the words in the expected lines above and below are
-- LLVM's encodings of that text (`llvm-mc -triple=riscv64 -mattr=+m,+c
-- -show-encoding`, LLVM 18, which compresses those that have a compressed
-- encoding), not `encode`'s. An operand that does not fit
-- its field has no encoding, which the emitter refuses; `lla` is text.
#guard [RISCV64.Instr.addi .a0 .a0 2048, .addi .a0 .a0 (-2049), .li .a0 4096,
    .addiw .a0 .a0 2048, .logicImm .and .a0 .a0 (-2049), .shift .sll .d .a0 .a0 64,
    .shift .sra .w .a0 .a0 32, .load .d .a0 .a0 2048, .store .b .a0 .a0 2048, .addSp .a0 2048,
    .alloc 4096, .free 4096].all (·.unencodable.isSome)
#guard RISCV64.Instr.unencodable (.lla .a0 "VG_TABLE") == none
#guard RISCV64.Instr.unencodable (.alloc 4064) == none
-- Every target's generated files are in its crate's `src/`, which it compiles.
#guard ["riscv64", "aarch64", "powerpc64le", "x86", "x86_64", "arm"].all fun t =>
  Rust.codeDir t == s!"verified-garbage-asm-{t}/src"
-- Consecutive `.inst` lines are joined, 8 words a line at most; nothing
-- else is.
#guard Rust.template "bl" ((List.range 10).map fun i => .text s!".inst 0x{i}") ==
  "        r\".inst 0x0,0x1,0x2,0x3,0x4,0x5,0x6,0x7\n.inst 0x8,0x9\",\n"
#guard Rust.template "bl" [.text ".inst 0x1", .text "20:", .text ".inst 0x2", .text ".inst 0x3",
    .call "vg_f", .text ".inst 0x4"] ==
  "        r\".inst 0x1\n20:\n.inst 0x2,0x3\nbl {vg_f}\n.inst 0x4\",\n"
-- Each run of consecutive encoded `.byte` lines (x86's) and `.long` lines
-- (PPC64LE's, whose words are little-endian) is one `.base64` line of their
-- bytes; another `.byte` or `.long` line (`symPush`'s) is neither, and ends
-- a run.
#guard Rust.template "call" ((List.range 18).map fun i => .text (X86.byteLine [i])) ==
  "        " ++ Rust.literal ".base64 \"AAECAwQFBgcICQoLDA0ODxAR\"" ++ ",\n"
#guard Rust.template "call" [.text ".byte 0x81, 199", .text (X86.byteLine [1, 2]),
    .text (X86.byteLine [3]), .text ".long 1b - 2b", .text (X86.byteLine [3])] ==
  "        " ++ Rust.literal ".byte 0x81, 199\n.base64 \"AQID\"\n.long 1b - 2b\n.base64 \"Aw==\"" ++
    ",\n"
#guard Rust.template "bl" [.text (PPC64LE.longLine 0x28250000), .text (PPC64LE.longLine 0x7c642a14),
    .text "beq %cr0, 20f"] ==
  "        " ++ Rust.literal ".base64 \"AAAlKBQqZHw=\"\nbeq %cr0, 20f" ++ ",\n"
#guard Rust.byteLine? ".byte 0x81, 199" == none
#guard Rust.byteLine? ".byte 0x81,0xc7" == some [0x81, 0xc7]
#guard Rust.wordLine? ".long 0x28250000,0x00000001" == some [0, 0, 0x25, 0x28, 1, 0, 0, 0]
#guard Rust.wordLine? ".long 0x1" == none
#guard Rust.wordLine? ".long {VG_TABLE} - 2b" == none
-- RFC 4648's padding: none for whole groups of 3 bytes, `==` after 1, `=` after 2.
#guard Rust.base64 [255, 255, 255] == "////"
#guard Rust.base64 [0xfb] == "+w=="
#guard Rust.base64 [0xfb, 0xff] == "+/8="
#guard Rust.base64 [] == ""
-- `.inst` lines are joined, but not other directives.
#guard Rust.template "bl" [.text ".long x", .text ".long y", .text ".inst 0x3"] ==
  "        r\".long x\n.long y\n.inst 0x3\",\n"
#guard Rust.template "bl" [.text ".insn 4, 0x1", .text ".insn 4, 0x2"] ==
  "        r\".insn 4, 0x1\n.insn 4, 0x2\",\n"
-- A comment line is a printer's `// ` line of one line: anything else is
-- assembly.
#guard Rust.commentOf (.text "// add a0, a1, a2") == some "// add a0, a1, a2"
#guard Rust.commentOf (.text "// a\nb") == none
#guard Rust.commentOf (.text "add a0, a1, a2 // a") == none
#guard Rust.commentOf (.call "vg_f") == none

-- Every register name.
#guard ([RISCV64.Reg.ra, .t0, .t1, .t2, .s0, .s1, .a0, .a1, .a2, .a3, .a4, .a5, .a6, .a7, .s2,
    .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .t3, .t4, .t5, .t6].map RISCV64.Reg.name) ==
  ["ra", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7", "s2",
   "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11", "t3", "t4", "t5", "t6"]

-- Frames: the push and pop of one register, and of a buffer, around a call.
#guard text (RISCV64.printer.function
    (.frame (.push .ra) (.frame (.alloc 2032) (.call "vg_f" (.block [])) (.free 2032))
      (.pop .ra) : Prog RISCV64.isa)) == [
  "// addi sp, sp, -16", ".insn 2, 0x1141", "// sd ra, 8(sp)", ".insn 2, 0xe406", "// addi sp, sp, -2032", ".insn 4, 0x81010113", "<call vg_f>",
  "// addi sp, sp, 2032", ".insn 4, 0x7f010113", "// ld ra, 8(sp)", ".insn 2, 0x60a2", "// addi sp, sp, 16", ".insn 2, 0x0141", "// ret", ".insn 2, 0x8082"]
#guard Rust.line RISCV64.printer.call (.call "vg_f") == "        r\"call {vg_f}\",\n"
-- A buffer of 2048 bytes or more: two `addi`s each way, of at most 2032
-- bytes, the largest frame being 4064 bytes; 2047 bytes and less is one.
#guard text (RISCV64.printer.function
    (.frame (.alloc 2048) (.call "vg_f" (.block [])) (.free 2048) : Prog RISCV64.isa)) == [
  "// addi sp, sp, -2032", ".insn 4, 0x81010113", "// addi sp, sp, -16", ".insn 2, 0x1141", "<call vg_f>", "// addi sp, sp, 16", ".insn 2, 0x0141", "// addi sp, sp, 2032", ".insn 4, 0x7f010113", "// ret", ".insn 2, 0x8082"]
#guard text (RISCV64.printer.function
    (.frame (.alloc 4064) (.block [.addSp .a0 0]) (.free 4064) : Prog RISCV64.isa)) == [
  "// addi sp, sp, -2032", ".insn 4, 0x81010113", "// addi sp, sp, -2032", ".insn 4, 0x81010113", "// addi a0, sp, 0", ".insn 2, 0x850a", "// addi sp, sp, 2032", ".insn 4, 0x7f010113", "// addi sp, sp, 2032", ".insn 4, 0x7f010113",
  "// ret", ".insn 2, 0x8082"]
#guard RISCV64.Instr.asm (.alloc 2304) == ["addi sp, sp, -2032", "addi sp, sp, -272"]
#guard RISCV64.Instr.asm (.free 2304) == ["addi sp, sp, 272", "addi sp, sp, 2032"]
#guard RISCV64.Instr.asm (.alloc 2032) == ["addi sp, sp, -2032"]

-- The address of a static (RISC-V): `lla` of its symbol, a `sym` operand,
-- which the assembler expands to `auipc` and `addi`. `asm` gives the text
-- `Rust.line` writes, for reading.
#guard text (RISCV64.printer.function (.block [.lla .a5 "VG_TABLE"] : Prog RISCV64.isa)) == [
  "lla a5, <sym VG_TABLE>", "// ret", ".insn 2, 0x8082"]
#guard Rust.line RISCV64.printer.call (.sym "lla a5, " .bare "VG_TABLE") ==
  "        r\"lla a5, {VG_TABLE}\",\n"
#guard RISCV64.Instr.asm (.lla .a5 "VG_TABLE") == ["lla a5, VG_TABLE"]
-- A template with an `lla` between text lines: the `lla` is a line of the
-- same string literal, and the instructions' comments are not in it, nor in
-- the Rust code, but in the assembly file, in place of their machine code.
#guard Rust.template RISCV64.printer.call
    (RISCV64.printer.function (.block [.li .a0 1, .lla .a5 "VG_TABLE"] : Prog RISCV64.isa)) ==
  "        r\".insn 2, 0x4505\nlla a5, {VG_TABLE}\n.insn 2, 0x8082\",\n"
#guard Rust.assembly RISCV64.printer.call
    (RISCV64.printer.function (.block [.li .a0 1, .lla .a5 "VG_TABLE"] : Prog RISCV64.isa)) ==
  ["addi a0, zero, 1", "lla a5, {VG_TABLE}", "ret"]
-- A comment not followed by a directive, its machine code, is only the text:
-- the line after it is in the assembly file too.
#guard Rust.assembly "call" [.text "// a", .text "b", .text "// c", .text ".byte 0x00", .text ".p2align 6"] ==
  ["a", "b", "c", ".p2align 6"]

-- Every RISC-V function's text enables the M and C extensions for itself alone
-- (`Rust.funcOptions`): `.option push` and `.option arch, +m, +c` are its first
-- lines and `.option pop` its last, after its labels, branches and return
-- (`vg_ct_eq`, the code of `crates/verified-garbage-asm-riscv64/src/ct.rs`). Other targets' functions
-- get no such directives.
#guard Rust.funcOptions RISCV64.target.name ==
  ([".option push", ".option arch, +m, +c"], [".option pop"])
#guard ["x86_64", "x86", "aarch64", "arm", "powerpc64le"].all (Rust.funcOptions · == ([], []))
#guard match Artifacts.Ct.RISCV64.artifacts with
  | [a] => ((Rust.function a (fun _ => "")).splitOn "naked_asm!(\n").getLast! == "        r\".option push
.option arch, +m, +c
.insn 2, 0x4701
.insn 4, 0x40d588b3
beqz a7, 20f
.insn 2, 0x4501
j 21f
20:
.insn 2, 0x4781
beqz a1, 22f
24:
.insn 4, 0x00f502b3
.insn 4, 0x0002c303
.insn 4, 0x00f602b3
.insn 4, 0x0002c383
.insn 4, 0x00734333
.insn 4, 0x00676733
.insn 2, 0x0785
.insn 4, 0x40b788b3
bnez a7, 24b
j 23f
22:
23:
.insn 2, 0x177d
.insn 4, 0x03f75513
21:
.insn 2, 0x8082
.option pop\",
    )
}
"
  | _ => false

#guard Arm.encodable 0xff000000 && Arm.encodable 0x3fc && !Arm.encodable 0x101 && !Arm.encodable 0x1fe00

#guard Rust.escape "ld1 {v0.4s}, [x1] \\ \"q\"" == "ld1 {{v0.4s}}, [x1] \\\\ \\\"q\\\""

/-! ## Calls

A call is its own line, whatever the callee's code; the emitter renders it as
the call instruction with the callee's symbol as a `sym` operand. -/

/-- A call between two blocks, on every target. -/
def callSample : Prog X86_64.isa :=
  .seq (.block [.mov .rdi (.reg .rbx)]) (.seq (.call "vg_f" (.block [.alu .add .rax (.imm 1)]))
    (.block [.mov .rax (.reg .rdx)]))

#guard printer.function callSample == [
  .text "// mov rdi, rbx", .text ".byte 0x48,0x89,0xdf", .call "vg_f",
  .text "// mov rax, rdx", .text ".byte 0x48,0x89,0xd0", .text "// ret", .text ".byte 0xc3"]
#guard AArch64.printer.function (.call "vg_f" (.block []) : Prog AArch64.isa) ==
  [.call "vg_f", .text "// ret", .text ".inst 0xd65f03c0"]
#guard X86.printer.function (.call "vg_f" (.block []) : Prog X86.isa) ==
  [.call "vg_f", .text "// ret", .text ".byte 0xc3"]
#guard Arm.printer.function (.call "vg_f" (.block []) : Prog Arm.isa) == [.call "vg_f", .text "bx lr"]
#guard PPC64LE.printer.function (.call "vg_f" (.block []) : Prog PPC64LE.isa) ==
  [.call "vg_f", .text "// blr", .text ".long 0x4e800020"]
#guard Rust.line PPC64LE.printer.call (.call "vg_f") == "        r\"bl {vg_f}\",\n"

#guard Rust.line printer.call (.call "vg_f") == "        r\"call {vg_f}\",\n"
#guard Rust.line Arm.printer.call (.call "vg_f") == "        r\"bl {vg_f}\",\n"
#guard Rust.line printer.call (.text "mov rax, QWORD PTR [rdi]") ==
  "        r\"mov rax, QWORD PTR [rdi]\",\n"

-- A raw string literal, `r#"…"#` if the text has a `"`, unless it has a
-- carriage return or a `"#`.
#guard Rust.literal "mov rax, rbx\nret" == "r\"mov rax, rbx\nret\""
#guard Rust.literal ".ascii \"a\\b\"\nret" == "r#\".ascii \"a\\b\"\nret\"#"
#guard Rust.literal "a\"#b" == "\"a\\\"#b\""
#guard Rust.literal "a\rb" == "\"a\\rb\""

-- A run of lines that are text alone is one string literal, its lines
-- separated by newlines (as `naked_asm!` joins its arguments); the page of a
-- static's address, which a macro writes, is an argument of its own.
#guard Rust.template "bl" [.text "mov x0, x1", .call "vg_f", .sym "adrp x16, " .page "VG_T",
    .text "ret", .text ".p2align 6"] ==
  "        r\"mov x0, x1\nbl {vg_f}\",\n" ++
  "        concat!(\"adrp x16, \", vg_sym_page!(\"{VG_T}\")),\n" ++
  "        r\"ret\n.p2align 6\",\n"
#guard Rust.template "bl" [] == ""

/-! ## Frames

A frame is its push, its body and its pop, each printed as the target's
instructions. -/

-- Save the link register around a call (AArch64).
#guard text (AArch64.printer.function
    (.frame (.push .x30) (.call "vg_f" (.block [])) (.pop .x30) : Prog AArch64.isa)) == [
  "// str x30, [sp, #-16]!", ".inst 0xf81f0ffe", "<call vg_f>", "// ldr x30, [sp], #16", ".inst 0xf84107fe", "// ret", ".inst 0xd65f03c0"]

-- The address of a static (AArch64): its page and the offset in the page, in the
-- syntax of the object format (`TCB/Rust.lean`).
#guard text (AArch64.printer.function (.block [.adrSym .x16 "VG_TABLE"] : Prog AArch64.isa)) == [
  "adrp x16, <page VG_TABLE>", "add x16, x16, <pageoff VG_TABLE>", "// ret", ".inst 0xd65f03c0"]

-- The address of a static (ARMv7): `movw` and `movt` of its distance from the
-- `pc` the `add` between labels 2 and 3 reads, the same text in ARM and Thumb
-- code. `asm` gives the text `Rust.line` writes, for reading.
#guard text (Arm.printer.function (.block [.adrSym .r4 "VG_TABLE"] : Prog Arm.isa)) == [
  "movw r4, #:lower16:(<armpcrel VG_TABLE>", "movt r4, #:upper16:(<armpcrel VG_TABLE>", "2:",
  "add r4, pc", "3:", "bx lr"]
#guard Rust.line Arm.printer.call (.sym "movw r4, #:lower16:(" .armPcRel "VG_TABLE") ==
  "        r\"movw r4, #:lower16:({VG_TABLE} - (2f + 2 * (3f - 2f)))\",\n"
#guard Arm.Instr.asm (.adrSym .r4 "VG_TABLE") == [
  "movw r4, #:lower16:(VG_TABLE - (2f + 2 * (3f - 2f)))",
  "movt r4, #:upper16:(VG_TABLE - (2f + 2 * (3f - 2f)))", "2:", "add r4, pc", "3:"]
-- It writes the static's address to its register alone.
#guard match Arm.exec (.adrSym .lr "VG_TABLE")
    { gpr := fun _ => 17, sp := 4096, n := true, z := false, c := true, v := false,
      mem := fun _ => 0, rd := [], wr := [], syms := fun _ => 12288 } with
  | none => false
  | some s => s.gpr .lr == 12288 && s.gpr .r4 == 17 && s.sp == 4096 && s.n && !s.z && s.c && !s.v

-- The address of a static (PPC64LE): `bcl` to the next instruction, label 2,
-- whose address it leaves in the link register, `mflr` of it, then `addis`
-- and `addi` of the high and low halves of the static's distance from label
-- 2. `asm` gives the text `Rust.line` writes, for reading.
#guard text (PPC64LE.printer.function (.block [.adrSym .r4 "VG_TABLE"] : Prog PPC64LE.isa)) == [
  "bcl 20, 31, 2f", "2:", "mflr %r4", "addis %r4, %r4, (<ppcha VG_TABLE>",
  "addi %r4, %r4, (<ppclo VG_TABLE>", "// blr", ".long 0x4e800020"]
#guard Rust.line PPC64LE.printer.call (.sym "addis %r4, %r4, (" .ppcHa "VG_TABLE") ==
  "        r\"addis %r4, %r4, ({VG_TABLE} - 2b)@ha\",\n"
#guard Rust.line PPC64LE.printer.call (.sym "addi %r4, %r4, (" .ppcLo "VG_TABLE") ==
  "        r\"addi %r4, %r4, ({VG_TABLE} - 2b)@l\",\n"
#guard PPC64LE.Instr.asm (.adrSym .r4 "VG_TABLE") == [
  "bcl 20, 31, 2f", "2:", "mflr %r4", "addis %r4, %r4, (VG_TABLE - 2b)@ha",
  "addi %r4, %r4, (VG_TABLE - 2b)@l"]
-- It writes the static's address to its register, and the next unknown value
-- to the link register, and nothing else.
#guard match PPC64LE.exec (.adrSym .r4 "VG_TABLE")
    { gpr := fun _ => 17, lr := 5, sp := 4096, mem := fun _ => 0, rd := [], wr := [],
      unknowns := fun n => 100 + BitVec.ofNat 64 n, syms := fun _ => 12288 } with
  | none => false
  | some s => s.gpr .r4 == 12288 && s.gpr .r3 == 17 && s.lr == 100 && s.unknowns 0 == 101 &&
      s.sp == 4096
-- With `r0`, `addis` and `addi` would read 0: the model faults.
#guard (PPC64LE.exec (.adrSym .r0 "VG_TABLE")
    { gpr := fun _ => 17, lr := 5, sp := 4096, mem := fun _ => 0, rd := [], wr := [] }).isNone

-- Pass two arguments on the stack, inside a frame saving `lr` (ARMv7). A pop
-- loads the lowest word of its frame.
#guard text (Arm.printer.function
    (.frame (.push [.lr])
      (.frame (.push [.r0, .r1]) (.call "vg_f" (.block [])) (.pop .r2 8)) (.pop .lr 4) :
      Prog Arm.isa)) == [
  "push {lr}", "push {r0, r1}", "<call vg_f>", "ldr r2, [sp], #8", "ldr lr, [sp], #4", "bx lr"]

-- Pass two arguments on the stack (x86): the first pushed is the higher
-- address.
#guard text (X86.printer.function
    (.frame (.push [.ecx, .eax]) (.call "vg_f" (.block [])) (.pop .edx 2) : Prog X86.isa)) == [
  "// push ecx", ".byte 0x51", "// push eax", ".byte 0x50", "<call vg_f>", "// pop edx", ".byte 0x5a", "// pop edx", ".byte 0x5a", "// ret", ".byte 0xc3"]

-- Pass two arguments on the stack, inside a frame saving `rbx` (x86-64).
#guard text (printer.function
    (.frame (.push [.rbx])
      (.frame (.push [.rcx, .rax]) (.call "vg_f" (.block [])) (.pop .rdx 2)) (.pop .rbx 1) :
      Prog X86_64.isa)) == [
  "// push rbx", ".byte 0x53", "// push rcx", ".byte 0x51", "// push rax", ".byte 0x50", "<call vg_f>", "// pop rdx", ".byte 0x5a", "// pop rdx", ".byte 0x5a", "// pop rbx", ".byte 0x5b", "// ret", ".byte 0xc3"]

-- Save the link register around a call (PPC64LE): through `r0`, in a frame
-- with a back chain.
#guard text (PPC64LE.printer.function
    (.seq (.block [.mflr .r0])
      (.seq (.frame (.push .r0) (.call "vg_f" (.block [])) (.pop .r0)) (.block [.mtlr .r0])) :
      Prog PPC64LE.isa)) == [
  "// mflr %r0", ".long 0x7c0802a6", "// stdu %r1, -48(%r1)", ".long 0xf821ffd1", "// std %r0, 32(%r1)", ".long 0xf8010020", "<call vg_f>", "// ld %r0, 32(%r1)", ".long 0xe8010020",
  "// addi %r1, %r1, 48", ".long 0x38210030", "// mtlr %r0", ".long 0x7c0803a6", "// blr", ".long 0x4e800020"]

-- A buffer on the stack (PPC64LE): a frame of 112 bytes, the buffer above its 32-byte header.
#guard text (PPC64LE.printer.function
    (.frame (.alloc 112) (.block [.addSp .r6 32]) (.free 112) : Prog PPC64LE.isa)) == [
  "// stdu %r1, -112(%r1)", ".long 0xf821ff91", "// addi %r6, %r1, 32", ".long 0x38c10020", "// addi %r1, %r1, 112", ".long 0x38210070", "// blr", ".long 0x4e800020"]

#guard Rust.line Arm.printer.call (.text "push {r4, lr}") == "        r\"push {{r4, lr}}\",\n"

/-! ## CPU features

`Code.requires` collects what every instruction needs, through calls and
frames; `Rust.featureCheck` accepts exactly the declared set; the emitted
`# Safety` item and constant list it. -/

/-- A stand-in for an ISA's `requires`, over instructions named by strings. -/
def req : String → List String
  | "sha256rnds2" => ["sha"]
  | "pshufb" => ["ssse3"]
  | "pblendw" => ["sse4.1"]
  | _ => []

def featureSample : Code String Unit :=
  .seq (.block ["mov", "sha256rnds2", "sha256rnds2"])
    (.ite () (.loop (.call "vg_f" (.block ["pshufb"])) ())
      (.frame "push" (.block ["pblendw"]) "pop"))

#guard featureSample.requires req == ["sha", "sha", "ssse3", "sse4.1"]
#guard (Code.block ["mov", "add"] : Code String Unit).requires req == []

/-! `Rust.requiresDedup` and `Rust.firstSome?` go through the code of each
call once (`Rust.distinctCalls`): the features of `Code.requires` each once,
and an instruction through any call. -/

/-- Calls of `f` and `g` nested in a call of `k`, and a later call of `f`
whose code requires something else. -/
def nestedSample : Code String Unit :=
  .seq (.call "k" (.seq (.block ["mov"]) (.call "g" (.call "f" (.block ["sha256rnds2"])))))
    (.seq (.call "f" (.block ["sha256rnds2"])) (.call "f" (.block ["pblendw"])))

#guard Rust.requiresDedup req featureSample == ["sha", "sse4.1", "ssse3"]
#guard Rust.requiresDedup req nestedSample == ["sha", "sse4.1"]
#guard Rust.requiresDedup req (Code.block ["mov", "add"] : Code String Unit) == []
-- The value of each call's code, but for a later call of a function whose
-- value is the first call's.
#guard Rust.distinctCalls (Rust.ownRequires req []) nestedSample.calls ==
  [[], [], ["sha"], ["sse4.1"]]

/-- The instruction `bad`, which a printer cannot encode. -/
def badInstr (i : String) : Option String := if i == "bad" then some i else none

#guard Rust.firstSome? badInstr nestedSample == none
#guard Rust.firstSome? badInstr (.seq nestedSample (.call "f" (.block ["bad"]))) == some "bad"
#guard Rust.firstSome? badInstr
  (.call "k" (.call "g" (.call "f" (.block ["bad"]))) : Code String Unit) == some "bad"
#guard Rust.firstSome? badInstr (.frame "bad" (.block []) "pop" : Code String Unit) == some "bad"

/-- The error of a failed check. -/
def err : Except String Unit → Option String
  | .error e => some e
  | .ok _ => none

def safeDoc : String := "Does things.\n\n# Safety\n\n* `p` must be valid."

#guard (Rust.featureCheck "f" "No safety requirements." [] []).toBool
#guard (Rust.featureCheck "f" safeDoc (featureSample.requires req) ["sse4.1", "sha", "ssse3"]).toBool
-- An undeclared feature, an unneeded one, and a doc the item can't be added to.
#guard err (Rust.featureCheck "f" safeDoc ["sha", "ssse3"] ["sha"]) ==
  some "f requires the CPU feature ssse3 but does not declare it"
#guard err (Rust.featureCheck "f" safeDoc ["sha"] ["sha", "avx2"]) ==
  some "f declares the CPU feature avx2, which none of its code requires"
#guard err (Rust.featureCheck "f" "No safety requirements." ["sha"] ["sha"]) ==
  some "f needs CPU features but its doc has no `# Safety` section"
#guard err (Rust.featureCheck "f" (safeDoc ++ "\n\n# Panics\n\nNever.") ["sha"] ["sha"]) ==
  some "f needs CPU features but its doc does not end with its `# Safety` section"

#guard Rust.featureDoc safeDoc [] == safeDoc
#guard Rust.featureDoc safeDoc ["sha"] ==
  safeDoc ++ "\n* The CPU must support the `sha` target feature."
#guard Rust.featureDoc safeDoc ["sha", "ssse3"] ==
  safeDoc ++ "\n* The CPU must support the `sha` and `ssse3` target features."
#guard Rust.featureDoc safeDoc ["sha", "ssse3", "sse4.1"] ==
  safeDoc ++ "\n* The CPU must support the `sha`, `ssse3` and `sse4.1` target features."

#guard Rust.featuresConst "vg_f" "" [] == ""
#guard Rust.featuresConst "vg_sha256_compress_shani" "" ["sha", "ssse3"] ==
  "/// The CPU features `vg_sha256_compress_shani` requires (`Artifact.features`).\n\
  pub const VG_SHA256_COMPRESS_SHANI_FEATURES: verified_garbage_cpu::Features = \
  verified_garbage_cpu::Features(verified_garbage_cpu::feature::SHA | verified_garbage_cpu::feature::SSSE3);\n\n"
#guard Rust.featureConst "avx512ifma" == "AVX512IFMA"
#guard Rust.featureConst "sse4.1" == "SSE4_1"

-- A feature some of the target's configurations cannot assemble or must
-- never run compiles its functions and constants only under its `cfg`.
#guard Rust.cfgGate [] == ""
#guard Rust.cfgGate ["target_os = \"linux\""] == "#[cfg(target_os = \"linux\")]\n"
#guard Rust.cfgGate ["a", "b"] == "#[cfg(all(a, b))]\n"
#guard Arm.Instr.asm (.umaal .r3 .r11 .r2 .r9) == ["umaal r3, r11, r2, r9"]
#guard Arm.Instr.requires (.umaal .r3 .r11 .r2 .r9) == ["umaal"]
#guard Arm.Instr.requires (.mla .r3 .r11 .r2 .r9) == []
#guard (Arm.printer.featureCfg "umaal").isSome
#guard (Arm.printer.featureCfg "neon").isNone
#guard Rust.featuresConst "vg_f_umaal" "#[cfg(c)]\n" ["umaal"] ==
  "/// The CPU features `vg_f_umaal` requires (`Artifact.features`).\n#[cfg(c)]\n\
  pub const VG_F_UMAAL_FEATURES: verified_garbage_cpu::Features = \
  verified_garbage_cpu::Features(verified_garbage_cpu::feature::UMAAL);\n\n"

end VG.Test
