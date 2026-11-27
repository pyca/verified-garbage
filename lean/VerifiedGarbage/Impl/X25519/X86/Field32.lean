module

public import VerifiedGarbage.Impl.X25519.X86
public import VerifiedGarbage.Spec.X25519

/-!
# Powers in curve25519's field on x86 (32-bit)

`pow250Call` runs the addition chain of ref10's `fe_invert` up to
`a^(2^250 - 1)` for `a` at byte 128 of the working space (`aAt`), inline in
its caller: it copies `a` to `AC` and leaves `a^11` at byte 512 (`E0`) and
`a^(2^250 - 1)` at byte 544 (`E1`), with the temporaries `E2` and `E3`.
Each of its products is a call of `vg_gf25519_r32_mul` (`mulFn`), and each
run of squarings a call of `vg_gf25519_r32_sqn` (`sqnFn`), both internal
functions with the working space in `edi`: the operands copied to `OpA` (and
`OpB`), the result back from `OpA` (`cmul`, `csqn`). `vg_gf25519_r32_mul` sets
`OpA = OpA · OpB`, and `vg_gf25519_r32_sqn` squares `OpA` `eax` times, counted by
`esi` (`eax ≥ 1`). Each saves the callee-saved registers at `SAVE` and
restores them, and uses no stack; the chain uses the 4 bytes of stack below
`esp` of a call's return address, and changes `eax`, `ecx`, `edx`, the
flags and bytes 512 to 1023 of the working space. Every address is `edi`
plus a constant, and the only branches are on the counters: only the
pointer may affect timing.
-/

@[expose] public section

namespace VG.Impl.X25519.X86.Field32

open VG.X86 VG.Impl.X25519.X86

/-- Where `pow250` reads `a`. -/
def aAt : Nat := 128

/-- Where `a^11` is left. -/
def E0 : Nat := 512

/-- Where `a^(2^250 - 1)` is left. -/
def E1 : Nat := 544

/-- The chain's temporaries. -/
def E2 : Nat := 576
def E3 : Nat := 608

/-- The copy of `a`. -/
def AC : Nat := 640

/-- The operands of the calls. -/
def OpA : Nat := 672
def OpB : Nat := 704

/-- Where the functions save `ebx`, `esi`, `edi` and `ebp`. -/
def SAVE : Nat := 928

/-- `[o] = [a]^(2^n)`, for `n ≥ 1`: `a` copied to `o` (unless they are the
same element), then `n` squarings in place, counted by `esi`. -/
def sqn (o a n : Nat) : Prog isa :=
  .seq (.block ((if o = a then [] else copy o a) ++ [.mov .esi (.imm (BitVec.ofNat 32 n))]))
    (.loop (.block (mul o o o ++ [.alu .sub .esi (.imm 1)])) .ne)

/-- The registers restored from `SAVE`, through `edx = ws`. -/
def exit : List Instr :=
  [.mov .edx (.reg .edi), .mov .ebx (.mem (at_ .edx SAVE)), .mov .esi (.mem (at_ .edx (SAVE + 4))),
    .mov .ebp (.mem (at_ .edx (SAVE + 12))), .mov .edi (.mem (at_ .edx (SAVE + 8)))]

/-- The callee-saved registers saved at `SAVE`. -/
def saveRegs : List Instr :=
  [.store (sc SAVE) .ebx, .store (sc (SAVE + 4)) .esi, .store (sc (SAVE + 8)) .edi, .store (sc (SAVE + 12)) .ebp]

/-- `vg_gf25519_r32_mul`: `[OpA] = [OpA] · [OpB]`. -/
def mulFn : Prog isa := .block (saveRegs ++ mul OpA OpA OpB ++ exit)

/-- `vg_gf25519_r32_sqn`: `[OpA] = [OpA]^(2^n)` for `n = eax ≥ 1`, counted by `esi`. -/
def sqnFn : Prog isa :=
  .seq (.block (saveRegs ++ [.mov .esi (.reg .eax)]))
    (.seq (.loop (.block (mul OpA OpA OpA ++ [.alu .sub .esi (.imm 1)])) .ne) (.block exit))

def mulCall : Prog isa := .call "vg_gf25519_r32_mul" mulFn
def sqnCall : Prog isa := .call "vg_gf25519_r32_sqn" sqnFn

/-- `[o] = [a] · [b]`, by a call of `vg_gf25519_r32_mul`. -/
def cmul (o a b : Nat) : Prog isa := .seq (.block (copy OpA a ++ copy OpB b)) (.seq mulCall (.block (copy o OpA)))

/-- `[o] = [a]^(2^n)`, by a call of `vg_gf25519_r32_sqn`. -/
def csqn (o a n : Nat) : Prog isa :=
  .seq (.block (copy OpA a ++ [.mov .eax (.imm (BitVec.ofNat 32 n))])) (.seq sqnCall (.block (copy o OpA)))

/-- From `a` at `AC`, `a^(2^250 - 1)` in `E1` and `a^11` in `E0`. -/
def chain : Prog isa :=
  .seq (csqn E0 AC 1) <| .seq (csqn E1 E0 1) <| .seq (csqn E1 E1 1) <|         -- a^2, a^8
  .seq (cmul E1 AC E1) <| .seq (cmul E0 E0 E1) <| .seq (csqn E2 E0 1) <| .seq (cmul E1 E1 E2) <| -- a^(2^5 - 1)
  .seq (csqn E2 E1 5) <| .seq (cmul E1 E2 E1) <|                              -- a^(2^10 - 1)
  .seq (csqn E2 E1 10) <| .seq (cmul E2 E2 E1) <|                             -- a^(2^20 - 1)
  .seq (csqn E3 E2 20) <| .seq (cmul E2 E3 E2) <|                             -- a^(2^40 - 1)
  .seq (csqn E2 E2 10) <| .seq (cmul E1 E2 E1) <|                             -- a^(2^50 - 1)
  .seq (csqn E2 E1 50) <| .seq (cmul E2 E2 E1) <|                             -- a^(2^100 - 1)
  .seq (csqn E3 E2 100) <| .seq (cmul E2 E3 E2) <|                            -- a^(2^200 - 1)
  .seq (csqn E2 E2 50) (cmul E1 E2 E1)                                        -- a^(2^250 - 1)

/-- The chain, inline: `a` copied to `AC`, then `chain`. It changes `eax`,
`ecx`, `edx`, the flags, bytes 512 to 1023 of the working space and the 4
bytes below `esp`. -/
def pow250Call : Prog isa := .seq (.block (copy AC aAt)) chain

end VG.Impl.X25519.X86.Field32
