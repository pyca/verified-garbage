module

public import VerifiedGarbage.Impl.Gcm.X86_64.StitchAvx8

/-!
# Preparing a key context's first sixteen powers in place, on 128-bit registers

`vg_aes_gcm_prepare16` for the backends without VPCLMULQDQ, whose eight-block
loops read no other powers: `H'`–`H'⁸` from the hash subkey at `ctx + 240`,
as those loops compute them (`StitchAvx8.setupG`), already in the prepared
form; stored, then each of the eight multiplied by `H'⁸`, eight independent
multiplications, for `H'⁹`–`H'¹⁶` (`rounds 1`). No calls, no stack.
-/

@[expose] public section

namespace VG.Impl.Gcm.X86_64.PrepareAvx

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Gcm.X86_64.StitchAvx8 (setupG mul preg prepOff)

/-- `H'⁸ʳ⁺ⁱ⁺¹`, in `preg i`, to its place in the context at `rdi`. -/
def stores (r : Nat) : List Instr :=
  (List.range 8).map fun i => .vmovdquStore .l128 (at_ .rdi (prepOff (8 * r + i + 1))) (preg i)

/-- Each of the eight powers times `H'⁸` (in `xmm7`), in place. -/
def times8 : List Instr := (List.range 8).flatMap fun i => mul (preg i) (preg i) .xmm7

/-- The rounds after the first: `H'⁸ʳ⁺⁹`–`H'⁸ʳ⁺¹⁶` (`r < n`), each stored. -/
def rounds : Nat → List Instr
  | 0 => []
  | n + 1 => rounds n ++ times8 ++ stores (n + 1)

/-- `vg_aes_gcm_prepare16`: the first 16 prepared powers into pairs 0–7 of the
context at `rdi`, from its hash subkey, for the eight-block loops, which read
no other. -/
def prepare16 : Prog isa :=
  .block (setupG ++ stores 0 ++ ([.vop (.vmovdqa .l128 .xmm7 .xmm15)] : List Instr) ++ rounds 1)

end VG.Impl.Gcm.X86_64.PrepareAvx
