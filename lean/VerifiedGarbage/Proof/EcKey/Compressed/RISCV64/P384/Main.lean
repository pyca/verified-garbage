module

public import VerifiedGarbage.Proof.EcKey.Compressed.RISCV64.MainAll
public import VerifiedGarbage.Proof.Ecdh.RISCV64.P384.Exchange
public import VerifiedGarbage.Impl.EcKey.Compressed.P384.RISCV64
public import VerifiedGarbage.Spec.EcKey.Compressed.Contract
import VerifiedGarbage.Proof.Framework.KernelRfl

/-!
# P-384's point compression and decompression on RISC-V: correctness

`vg_ec_p384_compress_public_key` and `vg_ec_p384_decompress_public_key`
meet their contracts by register (`compRV`, `compress_ok`; `DPre`, `DPostC`,
`decompress_ok`): the proofs of `Proof/EcKey/Compressed/RISCV64/MainAll.lean`
for every curve, over the curve's kit of ECDH.
-/

@[expose] public section

-- `p`, below `2^384`, is evaluated.
set_option exponentiation.threshold 512

namespace VG.Proof.EcKey.Compressed.RISCV64.P384

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64
open VG.Impl.Ecdsa.RISCV64 VG.Impl.Ecdh.RISCV64 VG.Impl.Ecdh.RISCV64.Cfg VG.Impl.EcKey.Compressed.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64 VG.Proof.Ecdsa.RISCV64.P384
open VG.Proof.Ecdh.RISCV64.P384
open VG.Proof.X25519.RISCV64 (Rest wp_and)
open VG.Spec.Weierstrass (Curve Fe Point ofBytes toBytes)
open VG.Spec.Ecdsa (bytesAt)
open VG.WriteBytes (writeBytes writeBytes_snoc writeBytes_nil writeBytes_append)

/-- `vg_ec_p384_compress_public_key(out = a0, public = a1, scratch = a2)`, by
register. -/
def compRV : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, 49⟩
    let pk : Region := ⟨s.gpr .a1, 97⟩
    let ws : Region := ⟨s.gpr .a2, 8192⟩
    s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
      (s.gpr .a0).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
      (s.gpr .a2).toNat % 8 = 0
  post s s' :=
    match Spec.EcKey.compressPublicKey Spec.P384.curve (bytesAt s.mem (s.gpr .a1) 97) with
    | some bs => s'.gpr .a0 = 1 ∧ bytesAt s'.mem (s.gpr .a0) 49 = bs
    | none => s'.gpr .a0 = 0 ∧ bytesAt s'.mem (s.gpr .a0) 49 = List.replicate 49 0
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2

/-- The contract's postcondition is the kit's. -/
theorem compPost_eq : compRV.post = kit.compPost := by kernel_rfl

/-- `vg_ec_p384_compress_public_key` by register. -/
theorem compress_ok {s : State} (hs : compRV.pre s) :
    WP isa compressP384 s fun s' => abiPreserved s s' ∧ compRV.post s s' := by
  rw [compPost_eq]; exact kit.compress_ok hs

/-! ## Decompression -/

/-- `vg_ec_p384_decompress_public_key(out = a0, public = a1, scratch = a2)`'s
precondition, by register. -/
def DPre (s : State) : Prop :=
  let out : Region := ⟨s.gpr .a0, 97⟩
  let pk : Region := ⟨s.gpr .a1, 49⟩
  let ws : Region := ⟨s.gpr .a2, 8192⟩
  s.rd = [pk] ∧ s.wr = [out, ws] ∧ pk.Disjoint out ∧ pk.Disjoint ws ∧ out.Disjoint ws ∧
    (s.gpr .a0).toNat + 97 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + 49 ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + 8192 ≤ 2 ^ 64 ∧
    (s.gpr .a2).toNat % 8 = 0

/-- `vg_ec_p384_decompress_public_key`'s postcondition, by register. -/
def DPostC (s s' : State) : Prop :=
  let bs := bytesAt s.mem (s.gpr .a1) 49
  (s'.gpr .a0 = 1 ∧ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.P384.curve bs Q ∧
      bytesAt s'.mem (s.gpr .a0) 97 = Spec.EcKey.encodePoint Q) ∨
    (s'.gpr .a0 = 0 ∧ (¬ ∃ Q, Spec.EcKey.matchesCompressedPublicKey Spec.P384.curve bs Q) ∧
      bytesAt s'.mem (s.gpr .a0) 97 = List.replicate 97 0)

/-- `vg_ec_p384_decompress_public_key` by register. -/
theorem decompress_ok (hL : VG.Proof.Weierstrass.Law W) {s : State} (hs : DPre s) :
    WP isa decompressP384 s fun s' => abiPreserved s s' ∧ DPostC s s' :=
  kit.decompress_ok (by decide) hL hs

end VG.Proof.EcKey.Compressed.RISCV64.P384
