module

public import VerifiedGarbage.Impl.RsaOaep.X86_64.Precomputed
public import VerifiedGarbage.Impl.ICall

/-!
# RSAES-OAEP on x86-64, with MGF1's hash function given as a table

`encrypt` (precomputed) and `decrypt` of `Impl/RsaOaep/X86_64.lean` for the
hash function `H`, with MGF1 over the hash function of the table `mgf1`
(`Spec/HashTable.lean`) rather than a fixed one: the last argument, the
stack argument 9 when encrypting and 17 when decrypting, which the prologue
puts in the slot `sTab`, with the table's digest length (its word 4) in the
slot `sD`.

MGF1 (`mgfXor`) is that of `Impl/Mgf1/X86_64.lean` but for two things: the
hash function's `init`, `update` and `finalize` are the table's functions 0,
1 and 2, which it calls indirectly (`tcall`: `call r11`, of whichever of
the functions `Fns` lists is at the address the table holds, with the
address in `r11`); and the digest length is read from `sD` rather than
being an immediate. Everything else is the code of `Impl/RsaOaep/X86_64.lean`.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.X86_64.Table

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.Mgf1.X86_64 (seqs sp ix at_ step byteLoop Layout initArgs updSrcArgs updCtrArgs finArgs)

/-- The table's slot. -/
def sTab : Nat := 280
/-- MGF1's digest length's slot. -/
def sD : Nat := 288

/-- The functions an indirect call of each of the table's functions may
reach: for each of `init`, `update` and `finalize`, that function of every
table of the interface, by name. -/
structure Fns where
  init : List (String × Prog isa)
  upd : List (String × Prog isa)
  fin : List (String × Prog isa)

/-- The call of the table's function `j`, among `ts`: its address (word `j`
of the table) into `r11`, then `call r11`. -/
def tcall (j : Nat) (ts : List (String × Prog isa)) : Prog isa :=
  .seq (.block [.mov .r11 (.mem (sp sTab)), .mov .r11 (.mem (at_ .r11 (8 * j)))])
    (Code.icalls (.callr .r11) ts)

variable (L : Layout) (f : Fns)

/-- `xorHead`, with the digest length read from `sD`. -/
def xorHead : List Instr :=
  Impl.Mgf1.X86_64.scr L .rcx L.oDig ++ [.mov .rdx (.mem (sp L.sDone)), .mov .rdi (.mem (sp L.sDst)),
    .alu .add .rdi (.reg .rdx), .mov .rax (.mem (sp L.sDstLen)), .alu .sub .rax (.reg .rdx),
    .mov .r10 (.mem (sp sD)), .alu .cmp .rax (.reg .r10)]

/-- `xorOut`, with the digest length read from `sD`. -/
def xorOut : Prog isa :=
  seqs [.block (xorHead L), .ite .b (.block [.mov .r10 (.reg .rax)]) (.block []), .block [.mov32 .r8 (.imm 0)],
    byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdx (ix .rdi .r8), .alu .xor .rdx (.reg .rax),
      .store8 (ix .rdi .r8) .rdx] (.reg .r10)]

/-- `nextCtr`, with the digest length read from `sD`. -/
def nextCtr : List Instr :=
  [.mov .rax (.mem (sp L.sCtr)), .alu .add .rax (.imm 1), .store (sp L.sCtr) .rax, .mov .rax (.mem (sp L.sDone)),
    .alu .add .rax (.mem (sp sD)), .store (sp L.sDone) .rax, .alu .cmp .rax (.mem (sp L.sDstLen))]

/-- One block: the digest of `src ‖ I2OSP(c, 4)`, XORed into `dst`. -/
def round : Prog isa :=
  seqs [.block (initArgs L), tcall 0 f.init, .block (updSrcArgs L), tcall 1 f.upd,
    .block (updCtrArgs L), tcall 1 f.upd, .block (finArgs L), tcall 2 f.fin, xorOut L,
    .block (nextCtr L)]

/-- `dst ⊕= MGF1(src, dstLen)`, for `dstLen > 0`, with the table's hash
function. -/
def mgfXor : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0), .store (sp L.sCtr) .rax, .store (sp L.sDone) .rax]) (.loop (round L f) .b)

/-- The table, the function's stack argument `j`, to `sTab`, and its digest
length to `sD`. -/
def tabPrologue (j : Nat) : List Instr :=
  argSlot j sTab ++ [.mov .rax (.mem (sp sTab)), .mov .rax (.mem (at_ .rax 32)), .store (sp sD) .rax]

variable (H : Stream)

/-! ## Encryption, with a precomputed public key -/

variable (pubN : String) (pubC : Prog isa)

/-- `Precomputed.encMain`, with MGF1 by the table. -/
def encMain : Prog isa :=
  seqs [encEm H, .block (dbArgs H), mgfXor lay f, .block (seedArgs H), mgfXor lay f,
    .block Precomputed.pubArgs, .call pubN pubC]

/-- `encBodyWith`, with the table (the stack argument 9) to its slots. -/
def encBody : Prog isa :=
  seqs [.block (encPrologue ++ tabPrologue 9 ++ chkK H),
    .ite .b encFail (seqs [.block (chkMsg H), .ite .b encFail (encMain f H pubN pubC)])]

/-- `vg_rsa_oaep_<H>_encrypt_precomputed`. -/
def encrypt : Prog isa := .frame (.alloc frameBytes) (encBody f H pubN pubC) (.free frameBytes)

/-! ## Decryption -/

/-- `decMain`, with MGF1 by the table. -/
def decMain : Prog isa :=
  seqs [hashLabel H oLh, .block (seedArgs H), mgfXor lay f, .block (dbArgs H), mgfXor lay f, accLh H, scan H,
    clearBuf H, copyT, shift, .block okMask, outLoop, .block (decRet H)]

variable (privN : String) (privC : Prog isa)

/-- `decBody`, with the table (the stack argument 17) to its slots. -/
def decBody : Prog isa :=
  seqs [.block (decPrologue ++ tabPrologue 17 ++ privArgs), .call privN privC,
    .block ([.mov32 .rax (.reg .rax), .store (sp sR) .rax] ++ chkK H),
    .ite .b decFail (decMain f H)]

/-- `vg_rsa_oaep_<H>_decrypt`. -/
def decrypt : Prog isa := .frame (.alloc frameBytes) (decBody f H privN privC) (.free frameBytes)

end VG.Impl.RsaOaep.X86_64.Table
