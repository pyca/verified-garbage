module

public import VerifiedGarbage.Impl.AesCbc.X86_64.VaesDecrypt
public import VerifiedGarbage.Impl.Aes.X86_64.VaesZ

/-! # Thirty-two-block CBC decryption with AVX-512 VAES -/

@[expose] public section
namespace VG.Impl.AesCbc.X86_64.Vaes512Decrypt
open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ regs8 imcKeys blocksLoad)

def dround (regs : List XReg) (j : Nat) : List Instr := Impl.Aes.X86_64.VaesZ.keyOpZ .xmm8 regs .vaesdec (at_ .r8 (16 * j))

/-- The inverse cipher on all four lanes of each block register, with `rounds`
in `rsi`, the key schedule at `rdi`, its last round key at `r10`, and round
keys 1 … `Nr − 1` through `aesimc` in the scratch buffer at `r8`. -/
def aesDec (regs : List XReg) : Prog isa :=
  .seq (.block (Impl.Aes.X86_64.VaesZ.keyOpZ .xmm8 regs .vpxord (at_ .r10 0) ++ ([.alu .cmp .rsi (.imm 10)] : List Instr)))
    (.seq
      (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (dround regs 13 ++ dround regs 12)))
            (.block (dround regs 11 ++ dround regs 10)))))
      (.block ((List.range 9).flatMap (fun j => dround regs (9 - j)) ++
        Impl.Aes.X86_64.VaesZ.keyOpZ .xmm8 regs .vaesdeclast (at_ .rdi 0))))


def loadData : List XReg → Nat → List Instr
  | [], _ => []
  | b::bs, j => .vmovdqu32Load b (at_ .rdx (64*j)) :: loadData bs (j+1)

/-- Form [previous ciphertext, C₀, C₁, C₂] and XOR all four lanes, with
EVEX and VEX instructions only (a legacy-SSE write of an `xmm` register after
the `zmm` writes would pay an SSE/AVX transition on each one): the previous
ciphertext, lane 0 of `zmm15`, joins the lanes of the loaded `zmm14` by two
shuffles. Load C₃ before the in-place 64-byte store. -/
def finish4 (b : XReg) (j : Nat) : List Instr :=
  [.vmovdqu32Load .xmm14 (at_ .rdx (64*j)),
   .zop (.vshufi32x4 .xmm15 .xmm15 .xmm14 0),
   .zop (.vshufi32x4 .xmm15 .xmm15 .xmm14 152),
   .zop (.zbin .vpxord b b .xmm15),
   .vmovdquLoad .l128 .xmm15 (at_ .rdx (64*j+48)),
   .vmovdqu32Store (at_ .rdx (64*j)) b]

def finishData : List XReg → Nat → List Instr
  | [], _ => []
  | b::bs, j => finish4 b j ++ finishData bs (j+1)

def blocks32 : Prog isa :=
  .seq (.block (loadData regs8 0))
    (.seq (aesDec regs8)
      (.block (finishData regs8 0 ++
        [.alu .add .rdx (.imm 512),.alu .sub .rcx (.imm 32),.alu .cmp .rcx (.imm 32)])))

def body : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.imm 32)])
    (.seq (.ite .b (.block []) (.loop blocks32 .ae)) VaesDecrypt.body)

def decrypt : Prog isa :=
  .seq (.seq (.block Decrypt.adapt) (.seq imcKeys (.block blocksLoad))) body

end VG.Impl.AesCbc.X86_64.Vaes512Decrypt
