module

public import VerifiedGarbage.Impl.Aes.X86_64.VaesZ

/-!
# AES decryption with AVX-512 VAES on x86-64

`aesDecZ k regs`: FIPS 197's equivalent inverse cipher (§5.3.5) on the four
128-bit lanes of each register of `regs`, as `VaesBlocks.aesDec` does on
two: the last round key from `r10`, the middle round keys through `aesimc`
from `scratch + 16 j` (`r8`, as `AesNi.imcKeys` writes them), and the first
round key from the key schedule at `rdi`, each broadcast into the four
lanes of `k` by `vbroadcasti32x4` (`VaesZ.keyOpZ`), with a branch on the
public `rounds` (in `rsi`) around round keys 10–13.
-/

@[expose] public section

namespace VG.Impl.Aes.X86_64.VaesZDec

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Impl.Aes.X86_64.VaesZ (keyOpZ)

/-- The middle round with round key `j` (`1 ≤ j < Nr`) of the four lanes of
each block register, from `scratch + 16 j`, through `k`. -/
def droundZ (k : XReg) (regs : List XReg) (j : Nat) : List Instr := keyOpZ k regs .vaesdec (at_ .r8 (16 * j))

/-- The inverse cipher on the four lanes of each block register, with
`rounds` in `rsi`, the key schedule at `rdi`, its last round key at `r10`,
and round keys 1 … `Nr − 1` through `aesimc` in the scratch buffer at `r8`,
the round keys in `k`. -/
def aesDecZ (k : XReg) (regs : List XReg) : Prog isa :=
  .seq (.block (keyOpZ k regs .vpxord (at_ .r10 0) ++ ([.alu .cmp .rsi (.imm 10)] : List Instr)))
    (.seq
      (.ite .e (.block [])
        (.seq (.block [.alu .cmp .rsi (.imm 12)])
          (.seq (.ite .e (.block []) (.block (droundZ k regs 13 ++ droundZ k regs 12)))
            (.block (droundZ k regs 11 ++ droundZ k regs 10)))))
      (.block ((List.range 9).flatMap (fun j => droundZ k regs (9 - j)) ++
        keyOpZ k regs .vaesdeclast (at_ .rdi 0))))

end VG.Impl.Aes.X86_64.VaesZDec
