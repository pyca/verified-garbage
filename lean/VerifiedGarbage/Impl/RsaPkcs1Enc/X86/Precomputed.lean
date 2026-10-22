module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86.Wrap
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
public import VerifiedGarbage.Impl.Bignum.X86.PublicFn

/-!
# RSAES-PKCS1-v1_5 encryption with a precomputed public key on x86 (32-bit)

`vg_rsa_pkcs1_encrypt_precomputed(out, out_len, n, n_len, e, e_len, msg,
msg_len, ps, ps_len, scratch, scratch_len, pre, pre_len)`, all on the stack.
As on ARMv7 (`Impl/RsaPkcs1Enc/Arm/Precomputed.lean`), it builds the encoded
message `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in its frame and calls
`vg_rsa_public_precomputed_checked` (`pd`, by its name `pdName`) on it, with
`pre` in place of the modulus; that call writes `EM^e mod n` or zeros to
`out`:

1. `0x00 ‖ 0x02`, then `PS` copied byte by byte (`psLoop`), with `ebx`
   collecting, without branches, the mask of a zero byte (`sbb` after
   `byte - 1`, all ones exactly when the byte is 0). `PS` is at least 8
   bytes long (a precondition).
2. The separator, and `M` after it (`Bignum.X86.copyBytes`), unless `M` is
   empty: a branch on a public length.
3. The call, its ten arguments (`out`, `n_len`, `pre`, `pre_len`, `e`,
   `e_len`, `EM`, `n_len`, `scratch`, `scratch_len`) at the frame's base.
4. The mask `keep` (all ones unless `PS` had a zero byte) and the result
   masked with it (`edi`); `out` masked with it (`maskLoop`), and `EM`
   overwritten with zeros. Nothing branches on the call's result.

The frame (`Impl/RsaPkcs1Sig/X86/Wrap.lean`) holds the call's arguments
from its base, the zero mask at `oZ` and `EM` (up to 1024 bytes) at `oEM`.
-/

@[expose] public section

namespace VG.Impl.RsaPkcs1Enc.X86.Precomputed

open VG VG.X86
open VG.Impl.RsaPkcs1Sig.X86 (wrap argOff stk at_)

/-- The size of the inner frame. -/
def frameBytes : Nat := 1072

/-- The zero mask of `PS`, and `EM`. -/
def oZ : Nat := 40
def oEM : Nat := 48

/-- Argument `j` (from 0). -/
def arg (j : Nat) : Src := .mem (stk (argOff frameBytes j))

/-- `EM`'s place in `edi`, `PS` in `esi` and its length in `ecx`; `0x00 ‖
0x02` at `EM`'s start, `edi` after them, and the zero mask `ebx` cleared. -/
def head : List Instr :=
  [.mov .edi (.reg .esp), .alu .add .edi (.imm (BitVec.ofNat 32 oEM)), .mov .esi (arg 8), .mov .ecx (arg 9),
    .mov .eax (.imm 0), .store8 (at_ .edi 0) .al, .mov .eax (.imm 2), .store8 (at_ .edi 1) .al,
    .alu .add .edi (.imm 2), .mov .ebx (.imm 0)]

/-- One byte of `PS`: copied, and `ebx |= (byte = 0 ? ~0 : 0)`. -/
def psBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al, .alu .sub .eax (.imm 1), .alu .sbb .eax (.reg .eax),
    .alu .or .ebx (.reg .eax), .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]

def psLoop : Prog isa := .loop (.block psBody) .ne

/-- The separator; the zero mask to its slot; `M` in `esi`, its place in
`ebx` and its length in `ecx` for `copyBytes`. -/
def sep : List Instr :=
  [.mov .eax (.imm 0), .store8 (at_ .edi 0) .al, .alu .add .edi (.imm 1), .store (stk oZ) .ebx,
    .mov .ebx (.reg .edi), .mov .esi (arg 6), .mov .ecx (arg 7), .alu .cmp .ecx (.imm 0)]

/-- `M`, unless it is empty. -/
def msgCopy : Prog isa := .ite .e (.block []) Impl.Bignum.X86.copyBytes

/-- Argument `j` to the call's argument `i`. -/
def copyArg (j i : Nat) : List Instr := [.mov .eax (arg j), .store (stk (4 * i)) .eax]

/-- The call's arguments. -/
def callArgs : List Instr :=
  copyArg 0 0 ++ copyArg 3 1 ++ copyArg 12 2 ++ copyArg 13 3 ++ copyArg 4 4 ++ copyArg 5 5 ++
    [.mov .eax (.reg .esp), .alu .add .eax (.imm (BitVec.ofNat 32 oEM)), .store (stk 24) .eax] ++
    copyArg 3 7 ++ copyArg 10 8 ++ copyArg 11 9

/-- The mask `keep` (`ebx`), the result masked with it (`edi`), and `out`
(`esi`) and `n_len` (`ecx`) for `maskLoop`. -/
def maskArgs : List Instr :=
  [.mov .ebx (.mem (stk oZ)), .alu .xor .ebx (.imm (BitVec.allOnes 32)), .mov .edi (.reg .eax),
    .alu .and .edi (.reg .ebx), .mov .esi (arg 0), .mov .ecx (arg 3)]

/-- One byte of `out`, masked with `keep`. -/
def maskBody : List Instr :=
  [.movzx8 .edx (at_ .esi 0), .alu .and .edx (.reg .ebx), .store8 (at_ .esi 0) .dl, .alu .add .esi (.imm 1),
    .alu .sub .ecx (.imm 1)]

def maskLoop : Prog isa := .loop (.block maskBody) .ne

/-- `EM` (`esi`), `n_len` (`ecx`) and zero for `zeroLoop`. -/
def wipeArgs : List Instr :=
  [.mov .esi (.reg .esp), .alu .add .esi (.imm (BitVec.ofNat 32 oEM)), .mov .ecx (arg 3), .mov .eax (.imm 0)]

/-- `k` zero bytes from `esi`. -/
def zeroLoop : Prog isa := .loop (.block Impl.Bignum.X86.PublicFn.clearStep) .ne

/-- The inner frame's body. -/
def body (pdName : String) (pd : Prog isa) : Prog isa :=
  .seq (.block head) (.seq psLoop (.seq (.block sep) (.seq msgCopy (.seq (.block callArgs)
    (.seq (.call pdName pd) (.seq (.block maskArgs) (.seq maskLoop (.seq (.block wipeArgs) (.seq zeroLoop
      (.block [.mov .eax (.reg .edi)]))))))))))

/-- `vg_rsa_pkcs1_encrypt_precomputed`, calling a precomputed public
operation (`pd`) by its name. -/
def code (pdName : String) (pd : Prog isa) : Prog isa := wrap frameBytes (body pdName pd)

end VG.Impl.RsaPkcs1Enc.X86.Precomputed
