module

public import VerifiedGarbage.Impl.CmacAes.X86_64.AesNi

/-! # AES-CBC encryption with resident round keys on x86-64 -/

@[expose] public section

namespace VG.Impl.AesCbc.X86_64.Encrypt

open VG.X86_64
open VG.Impl.CmacAes.X86_64.AesNi (at_ setup last rounds finish)

/-- The chaining register is biased by K₀, as in CBC-MAC. Store the unbiased
ciphertext through xmm1 while leaving xmm0 ready for the following block. -/
def output : List Instr :=
  [.movdquLoad .xmm1 (at_ .rdi 0), .xop (.bin .pxor .xmm1 .xmm0),
   .movdquStore { base := .rcx, disp := -16 } .xmm1]

def body (nr : Nat) : List Instr := VG.Impl.CmacAes.X86_64.AesNi.body nr ++ output

def blocks (nr : Nat) : Prog isa := .seq (.block (last nr)) (.loop (.block (body nr)) .ne)

def loops : Prog isa :=
  .ite .e (blocks 10) (.seq (.block [.alu .cmp .rsi (.imm 12)]) (.ite .e (blocks 12) (blocks 14)))

/-- No scratch or stack; all branches depend on the public lengths. -/
def encrypt : Prog isa :=
  .seq (.block [.alu .test .r8 (.reg .r8)])
    (.ite .e (.block []) (.seq (.block setup) (.seq loops (.block finish))))

end VG.Impl.AesCbc.X86_64.Encrypt
