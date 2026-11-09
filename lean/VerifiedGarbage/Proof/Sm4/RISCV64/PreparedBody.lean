module

public import VerifiedGarbage.Proof.Sm4.RISCV64.Ecb
import VerifiedGarbage.Proof.Sm4.RISCV64.Crypt16
public import VerifiedGarbage.Impl.Sm4.RISCV64.Prepared
import VerifiedGarbage.Proof.Sm4.Planes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Sm4.RISCV64.Prologue
import VerifiedGarbage.Proof.Sm4.RISCV64.Group
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Sm4.RISCV64.LayersLit
public import VerifiedGarbage.Proof.Sm4.Prepared

/-!
# SM4's prepared round keys and batches on RISCV64: two facts

`entryW_eq`: an entry of the table, as a word of the working space.
`quads_spec`: the rounds with the round keys in the order of a direction
are its cipher.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

open VG VG.RISCV64 VG.RISCV64.Straight VG.Impl.Sm4.RISCV64
open VG.Impl.Aes.RISCV64 (sb t0 t1 movR stS)
open VG.Proof.Sm4 (WordRel specDirA)

/-! ## The encoding -/

theorem entryW_eq (m : Mem) (B : Addr) (e j : Nat) :
    entryW m B e j = m.readW (wordAddr B (tableSlot + 8 * e + j)) 64 := by
  rw [entryW, wordAddr, show 8 * (tableSlot + 8 * e + j) = 8 * tableSlot + 64 * e + 8 * j by omega_arith]

/-! ## The bodies -/

/-- The rounds with the round keys in the order of `d` are its cipher. -/
theorem quads_spec (d : Dir) (sch : Spec.Sm4.Schedule) (blk : Spec.Sm4.Block) :
    Proof.Sm4.outBlock (Proof.Sm4.quads .enc (dirKeys d sch) 8 (Proof.Sm4.ofBlock blk)) =
      Proof.Sm4.blockFn sch (specDirA d) blk := by
  cases d
  · simp only [Proof.Sm4.blockFn, specDirA, Spec.Sm4.encryptBlock, Proof.Sm4.crypt_eq]; rfl
  · simp only [Proof.Sm4.blockFn, specDirA, Spec.Sm4.decryptBlock, Proof.Sm4.crypt_eq]; rfl

end VG.Proof.Sm4.RISCV64
