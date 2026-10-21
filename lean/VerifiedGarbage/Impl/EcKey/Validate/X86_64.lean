module

public import VerifiedGarbage.Impl.Ecdh.X86_64

/-!
# Standalone public-key validation on x86-64

Reuse ECDSA's setup (including byte decoding and saved registers), ECDH's
peer setup and point check, then return the flag and restore registers.
The three numbers that signature setup loads all come from the encoded
point's x-coordinate; only its copy in slot E is used by validation.
No scalar multiplication or inversion is performed.
-/

@[expose] public section

namespace VG.Impl.EcKey.Validate.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Ecdsa.X86_64

/-- Public key in rdi, scratch in rsi. -/
def args : List Instr :=
  [.mov .r8 (.reg .rsi), .mov .r9 (.reg .rdi), .mov .rcx (.reg .rdi),
    .alu .add .rcx (.imm 1), .mov .rsi (.reg .rcx), .mov .rdx (.reg .rcx)]

/-- Return the flag's low bit and restore the saved registers. -/
def finish (c : Cfg) : List Instr :=
  ([.mov .rcx (.mem (sc (c.sl FLAG))), .mov .rax (.reg .rcx), .alu .and .rax (.imm 1)] : List Instr) ++
    Cfg.saved.map (fun (r, d) => .mov r (.mem (sc d)))

/-- Validate the entire uncompressed encoding. -/
def validate (c : Cfg) : Prog isa :=
  .seq (.block args) <|
  .seq (.block (c.setupWith none)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.check c) (.block (finish c))

end VG.Impl.EcKey.Validate.X86_64
