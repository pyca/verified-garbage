module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Print
public import VerifiedGarbage.TCB.Arm.Target

/-!
# Printer for the ARMv7 model

**Trusted.** Emits the unified assembler language (UAL) accepted by Rust's
`asm!`/`naked_asm!` on 32-bit ARM, valid for both the ARM and the Thumb
instruction sets.
-/

@[expose] public section

namespace VG.Arm

def Reg.name : Reg → String
  | .r0 => "r0" | .r1 => "r1" | .r2 => "r2" | .r3 => "r3" | .r4 => "r4" | .r5 => "r5"
  | .r6 => "r6" | .r7 => "r7" | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .lr => "lr"

def Shift.name : Shift → String
  | .lsl => "lsl" | .lsr => "lsr" | .ror => "ror"

def Op2.str : Op2 → String
  | .imm v => s!"#{v.toNat}"
  | .reg r => r.name
  | .shifted r sh n => s!"{r.name}, {sh.name} #{n}"

def DpOp.name : DpOp → String
  | .add => "add" | .sub => "sub" | .and => "and" | .orr => "orr" | .eor => "eor" | .bic => "bic"

def Instr.asm : Instr → List String
  | .mov d (.shifted m sh n) => [s!"{sh.name} {d.name}, {m.name}, #{n}"]
  | .mov d op2 => [s!"mov {d.name}, {op2.str}"]
  | .mvn d op2 => [s!"mvn {d.name}, {op2.str}"]
  | .dp op d n op2 => [s!"{op.name} {d.name}, {n.name}, {op2.str}"]
  | .adds d n op2 => [s!"adds {d.name}, {n.name}, {op2.str}"]
  | .adc d n op2 => [s!"adc {d.name}, {n.name}, {op2.str}"]
  | .subs d n op2 => [s!"subs {d.name}, {n.name}, {op2.str}"]
  | .cmp n op2 => [s!"cmp {n.name}, {op2.str}"]
  | .movw d imm => [s!"movw {d.name}, #{imm.toNat}"]
  | .movt d imm => [s!"movt {d.name}, #{imm.toNat}"]
  | .adrSym d name => [s!"movw {d.name}, #:lower16:({name} - (2f + 2 * (3f - 2f)))",
      s!"movt {d.name}, #:upper16:({name} - (2f + 2 * (3f - 2f)))", "2:", s!"add {d.name}, pc", "3:"]
  | .rev d m => [s!"rev {d.name}, {m.name}"]
  | .mul d n m => [s!"mul {d.name}, {n.name}, {m.name}"]
  | .mla d n m a => [s!"mla {d.name}, {n.name}, {m.name}, {a.name}"]
  | .umaal lo hi n m => [s!"umaal {lo.name}, {hi.name}, {n.name}, {m.name}"]
  | .ldr t n off => [s!"ldr {t.name}, [{n.name}, #{off}]"]
  | .str t n off => [s!"str {t.name}, [{n.name}, #{off}]"]
  | .ldrb t n off => [s!"ldrb {t.name}, [{n.name}, #{off}]"]
  | .strb t n off => [s!"strb {t.name}, [{n.name}, #{off}]"]
  | .addSp d imm => [s!"add {d.name}, sp, #{imm}"]
  | .alloc bytes => [s!"sub sp, sp, #{bytes}"]
  | .free bytes => [s!"add sp, sp, #{bytes}"]
  | .ldrSp t off => [s!"ldr {t.name}, [sp, #{off}]"]
  | .blx m => [s!"blx {m.name}"]
  | .push rs => [s!"push \{{", ".intercalate (rs.map Reg.name)}}"]
  | .pop t n => [s!"ldr {t.name}, [sp], #{n}"]

def Cond.name : Cond → String
  | .eq => "eq" | .ne => "ne"

def printer : Printer isa where
  instr := Instr.asm
  branch c l := [s!"b{c.name} {l}"]
  jump l := s!"b {l}"
  ret := ["bx lr"]
  call := "bl"
  -- `umaal` assembles only for ARMv7-A, -R and ARMv7E-M (not for
  -- `thumbv7m-none-eabi`, the Cortex-M3), and its timing is known not to
  -- depend on its operands only on A-profile cores (`TCB/Arm/Isa.lean`): code
  -- needing it is compiled only for the operating systems that run on them
  -- alone, where `src/cpu.rs` reports it.
  featureCfg
    | "umaal" => some "any(target_os = \"linux\", target_os = \"android\", \
        target_os = \"freebsd\", target_os = \"netbsd\", target_os = \"openbsd\")"
    | _ => none
  -- Labels 2 and 3 are private to `adrSym`, around its `add`: structured
  -- control flow uses 20, 21, ...; repeated sequences use the nearest 2f/3f.
  -- `2f + 2 * (3f - 2f)` is the `pc` the `add` reads: its address plus 8 in
  -- ARM state, where it is 4 bytes, and plus 4 in Thumb state, where it is 2.
  symLines
    | .adrSym d name => some [.sym s!"movw {d.name}, #:lower16:(" .armPcRel name,
        .sym s!"movt {d.name}, #:upper16:(" .armPcRel name, .text "2:", .text s!"add {d.name}, pc",
        .text "3:"]
    | _ => none

/-- What the emitter needs of the target (`Emitter`): its printer, its Rust `cfg`
and ABI string, and how documentation names its calling convention's
argument area and reserved memory (`abi`'s `argArea` and `reserved`). -/
instance : Emitter isa where
  printer := printer
  -- `armeb` targets are big-endian. Apple's 32-bit ARM targets do not use AAPCS:
  -- `armv7s-apple-ios` uses APCS, where a 64-bit argument takes the next two
  -- registers (`r1:r2` after one word) rather than an even pair (`r2:r3`,
  -- AAPCS §5.5, "Parameter Passing", rule C.3), and `armv7k-apple-watchos` uses
  -- AAPCS16, Apple's variant of AAPCS, which the model has not been checked
  -- against. The ARMv4T–ARMv6 targets (`armv5te-*`, `arm-*`, …)
  -- are not ARMv7, which the model describes, but Rust has no stable `cfg` for
  -- the architecture version (its ARM target features, `v7` included, are
  -- unstable, and `cfg` does not report them on stable): they are kept out only
  -- because some functions use `movw`, which is new in ARMv7 (and ARMv6T2), so
  -- the crate does not assemble for them.
  rustCfg := "all(target_arch = \"arm\", target_endian = \"little\", \
    not(target_vendor = \"apple\"))"
  rustAbi := "C"
  argAreaDoc ws := if (classify ws 0 0).2 = 0 then none else
    some ("the arguments on the stack", false)
  reservedDoc n := if n = 0 then none else some s!"the {n} bytes of stack below the stack pointer"

end VG.Arm
