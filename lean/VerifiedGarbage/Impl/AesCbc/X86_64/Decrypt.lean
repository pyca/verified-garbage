module

public import VerifiedGarbage.Impl.Aes.X86_64.AesNiBlocks

/-! # Parallel AES-NI CBC decryption on x86-64 -/

@[expose] public section
namespace VG.Impl.AesCbc.X86_64.Decrypt
open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ loadData regs8 aesDec imcKeys blocksLoad)

/-- The original ciphertext is reloaded before its slot is overwritten.
The chaining register survives all AES rounds. -/
def finish (b : XReg) (j : Nat) : List Instr :=
  [.xop (.bin .pxor b .xmm15), .movdquLoad .xmm15 (at_ .rdx (16*j)),
    .movdquStore (at_ .rdx (16*j)) b]

def finishData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => finish b j ++ finishData bs (j+1)

def group (rs : List XReg) (advance : List Instr) : Prog isa :=
  .seq (.block (loadData rs 0)) (.seq (aesDec rs) (.block (finishData rs 0 ++ advance)))

def blocks8 : Prog isa := group regs8
  [.alu .add .rdx (.imm 128), .alu .sub .rcx (.imm 8), .alu .cmp .rcx (.imm 8)]

def blocks1 : Prog isa := group [.xmm0]
  [.alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)]

def tail : Prog isa :=
  .seq (.ite .b (.block []) (.loop blocks8 .ae))
    (.seq (.block [.alu .test .rcx (.reg .rcx)]) (.ite .e (.block []) (.loop blocks1 .ne)))

def adapt : List Instr :=
  [.mov .r11 (.reg .rdx), .mov .rdx (.reg .rcx), .mov .rcx (.reg .r8), .mov .r8 (.reg .r9),
   .movdquLoad .xmm15 (at_ .r11 0)]

def decrypt : Prog isa :=
  .seq (.seq (.block adapt) (.seq imcKeys (.block blocksLoad)))
    (.seq tail (.block [.movdquStore (at_ .r11 0) .xmm15]))

end VG.Impl.AesCbc.X86_64.Decrypt
