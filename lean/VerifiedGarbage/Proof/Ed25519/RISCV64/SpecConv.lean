module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldProg
public import VerifiedGarbage.Proof.X25519.Field32Contract
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Power
import VerifiedGarbage.Proof.Ed25519.RISCV64.MulFn
import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
import VerifiedGarbage.Proof.Ed25519.RISCV64.Base

/-!
# Ed25519 on RISC-V: the elements as the contracts read them

What `Base`, `MulFn` and `PointAdd` do not already state: the contracts'
`valAt` of a slot is the proofs' `V` (`valAt_ofNat`), `pow250`'s `Keeps₂`
follows from its frame (`keeps_pow`), and a power of `env` is the
contracts' power of `V` (`val_of_env`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Spec.X25519 (P)

theorem valAt_ofNat (m : Mem) (b : Addr) (i : Slot) :
    Proof.X25519.Field32.valAt m b (BitVec.ofNat 32 (offset i)) = V m b (offset i) := by
  have := slot_range i
  rw [valAt_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← read_V, ← read_V, BitVec.add_zero]

/-- `pow250`'s `Keeps₂`, from its frame. -/
theorem keeps_pow {b : Addr} {m m' : Mem} (hf : Frame [PR b] m m') : Proof.X25519.Field32.Keeps₂ b m m' := by
  intro i hi hown
  simp only [Proof.X25519.Field32.wsBytes, Proof.X25519.Field32.eAt, Proof.X25519.Field32.ownEnd] at hi hown
  exact hf _ fun r hr => by rw [List.mem_singleton.mp hr]; exact byte_out (by omega) (by omega) hown

/-- A power, as the contract states it. -/
theorem val_of_env {m m' : Mem} {b : Addr} {i j : Slot} {e : Nat}
    (h : env m' b i = Proof.X25519.pw (env m b j) e) :
    V m' b (offset i) % P = V m b (offset j) ^ e % P := by
  have := congrArg Fin.val h
  simp only [env, FS, Proof.X25519.toFe_val, Proof.X25519.pw, Fin.val_ofNat] at this
  rw [this, ← Nat.pow_mod]

end VG.Proof.Ed25519.RISCV64
