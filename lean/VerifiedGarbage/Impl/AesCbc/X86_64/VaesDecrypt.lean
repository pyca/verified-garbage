module

public import VerifiedGarbage.Impl.AesCbc.X86_64.Decrypt
public import VerifiedGarbage.Impl.Aes.X86_64.VaesBlocks

/-! # Sixteen-block CBC decryption with VAES -/

@[expose] public section
namespace VG.Impl.AesCbc.X86_64.VaesDecrypt
open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ regs8 imcKeys blocksLoad)

/-- VEX-encoded CBC stores avoid a legacy-SSE transition inside the VAES loop. -/
def finishVex (b : XReg) (j : Nat) : List Instr :=
  [.vop (.vbin .vpxor .l128 b b .xmm15),
   .vmovdquLoad .l128 .xmm15 (at_ .rdx (16*j)),
   .vmovdquStore .l128 (at_ .rdx (16*j)) b]

def finishBlocks : List XReg → Nat → List Instr
  | [], _ => []
  | b::bs, j => finishVex b j ++ finishBlocks bs (j+1)

/-- Extract a pair's upper plaintext, then perform the two sequential CBC
stores. xmm14 is temporary and xmm15 retains the chaining value. -/
def finishData : List XReg → Nat → List Instr
  | [], _ => []
  | b::bs, j => [.vop (.vextracti128 .xmm14 b 1)] ++
      finishBlocks [b,.xmm14] (2*j) ++ finishData bs (j+1)

def blocks16 : Prog isa :=
  .seq (.block (Impl.Aes.X86_64.VaesBlocks.loadData regs8 0))
    (.seq (Impl.Aes.X86_64.VaesBlocks.aesDec regs8)
      (.block (finishData regs8 0 ++
        [.alu .add .rdx (.imm 256),.alu .sub .rcx (.imm 16),.alu .cmp .rcx (.imm 16)])))

def body : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.imm 16)])
    (.seq (.ite .b (.block []) (.loop blocks16 .ae))
      (.seq (.block [.vop .vzeroupper,.alu .cmp .rcx (.imm 8)])
        (.seq Decrypt.tail (.block [.movdquStore (at_ .r11 0) .xmm15]))))

def decrypt : Prog isa :=
  .seq (.seq (.block Decrypt.adapt) (.seq imcKeys (.block blocksLoad))) body

end VG.Impl.AesCbc.X86_64.VaesDecrypt
