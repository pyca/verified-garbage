module

public import VerifiedGarbage.Impl.TripleDes.PPC64LE.Block

/-!
# Triple DES ECB on PPC64LE

`encrypt` and `decrypt` (schedule = r3, data = r4, n = r5, scratch = r6, 1024
bytes) call the block function for each block, with the first 512 bytes of
the scratch buffer as its working space. The return address and the caller's
`r31` are saved in the scratch buffer at 512 and 520. The blocks left are
counted in `r31`, which the block functions never write, so the count stays
public across their calls; `r3`, `r4` and `r5`, which they keep, hold the
schedule, the block's address and the working space.
-/

@[expose] public section

namespace VG.Impl.TripleDes.PPC64LE.Ecb

open VG.PPC64LE VG.Impl.TripleDes.PPC64LE
open VG.Spec.TripleDes (Direction)

def save : List Instr := [.mflr .r0, .store .d .r0 .r6 512, .store .d .r31 .r6 520]
def setup : List Instr := [rr .r31 .r5, rr .r5 .r6]
def restore : List Instr := [.load .d .r0 .r5 512, .mtlr .r0, .load .d .r31 .r5 520]

def blockCall (d : Direction) : Prog isa :=
  match d with
  | .encrypt => .call "vg_triple_des_encrypt_block" encryptBlock
  | .decrypt => .call "vg_triple_des_decrypt_block" decryptBlock

def advance : List Instr := [.addi .r4 .r4 8, .subi .r31 .r31 1]

def ecb (d : Direction) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite (.zero .d .r31) (.block [])
    (.loop (.seq (blockCall d) (.block advance)) (.nonzero .d .r31))) (.block restore))

def encrypt : Prog isa := ecb .encrypt
def decrypt : Prog isa := ecb .decrypt

end VG.Impl.TripleDes.PPC64LE.Ecb
