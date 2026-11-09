module

public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.X25519.RISCV64.Invert
import VerifiedGarbage.Proof.X25519.RISCV64.Bits
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed25519.RISCV64.PointPowers
public import VerifiedGarbage.Proof.Ed25519.ScalarMul
public import VerifiedGarbage.Spec.Ed25519.Contract
public import VerifiedGarbage.Proof.Ed25519.RISCV64.Field
public import VerifiedGarbage.Impl.Ed25519.RISCV64.PointMul
public import VerifiedGarbage.Proof.Ed25519.RISCV64.PointOps
public import VerifiedGarbage.Proof.Framework.Block

/-!
# Ed25519 on RISCV64: the frames of scalar multiplication

What a batch and the multiplication write (`batchW`, `batchR`, `pmulW`),
inside the working space (`bytes_ws`), and a constant point stored in the
slots (`env_constPoint`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Ed25519.RISCV64 VG.Proof.X25519.RISCV64
open VG.Proof.X25519
open VG.Impl.X25519.RISCV64 (cswap)
open VG.Proof.Ed25519 (powerPoint after)

section
variable {b : Addr}

/-- What a batch writes: the field area, the table of its powers and its bits. -/
abbrev batchW (b : Addr) : List Region := [FA b, ⟨b + BitVec.ofNat 64 5728, 2048⟩, ⟨b + BitVec.ofNat 64 BITSB, 16⟩]

/-- The registers a batch writes. -/
abbrev batchR : List Reg := .a5 :: .s0 :: .s1 :: .s2 :: .s6 :: fclob

theorem bytes_ws {m m' : Mem} {rs : List Region} (hf : Frame rs m m') (hs : ∀ r ∈ rs, Region.Sub r ⟨b, 8192⟩)
    {p : Addr} {nb : Nat} (hd : (⟨p, nb⟩ : Region).Disjoint ⟨b, 8192⟩) (hn : nb ≤ 64) {i : Nat} (hi : i < nb) :
    m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
  hf _ fun r hr hc => hd _ (Offset.contains_base _ (by omega_arith) (by omega_arith)) (hs r hr _ hc)

/-- What the multiplication writes: a batch's regions and the table of checkpoints. -/
abbrev pmulW (b : Addr) : List Region := ⟨b + BitVec.ofNat 64 1632, 4096⟩ :: batchW b

theorem env_constPoint (e : Env) (p : Spec.Ed25519.Point) :
    point (evalOps (constPointOps p) e) 0 1 2 3 = p ∧ evalOps (constPointOps p) e 16 = e 16 := ⟨rfl, rfl⟩

end

end VG.Proof.Ed25519.RISCV64
