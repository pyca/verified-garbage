module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Loop
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# AES modes on RISC-V, a block at a time: what the bodies share

What the bodies of `whole`'s loop (`Loop.lean`), AES-CTR's and CMAC's,
need beyond the invariant: that `vg_aes_encrypt_blocks` makes no frames
(`encryptBlocks_noFrames`), and the regions the code reads and writes
(`LInv.regs`, `LInv.wrs`). AES-CBC, AES-CFB128 and XTS run through the
chaining and four-block functions instead (`Proof/Aes/RISCV64/Chain.lean`,
`Wide.lean`).
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.RISCV64.Align VG.Impl.AesCbc.RISCV64
open VG.Spec.Aes (bytesAt)

theorem encryptBlocks_noFrames : Impl.Aes.RISCV64.encryptBlocks.noFrames = true := by lit_decide

section
variable {s₀ : State} (hp : UPre s₀)
include hp

/-- The regions the code reads and writes, from the invariant. -/
theorem LInv.regs {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    s.rd ++ s.wr = [schR s₀, ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.rd, h.wr, hp.rd, hp.wr]; rfl

theorem LInv.wrs {M : Mode} {k : Nat} {s : State} (h : LInv M s₀ k s) :
    s.wr = [ivR s₀, dataR s₀, scrR s₀] := by
  rw [h.wr, hp.wr]

end

end VG.Proof.AesCbc.RISCV64
