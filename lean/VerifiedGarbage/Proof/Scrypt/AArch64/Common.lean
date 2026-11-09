module

import VerifiedGarbage.Proof.Scrypt.Memory
public import VerifiedGarbage.Proof.MdStream.AArch64.Common
public import VerifiedGarbage.Impl.Scrypt.AArch64.BlockMix
public import VerifiedGarbage.Spec.Scrypt.Contract
import all Init.Data.Nat.Power2.Basic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# scrypt on AArch64: common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are the weakest-precondition rules for the
AArch64 forms, and the 64-byte exclusive-or.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.AArch64 in
/-- AArch64 contract for `vg_scrypt_blockmix(b = x0, r = x1, y = x2, ry = x3,
scratch = x4)`: if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at
`b` to `y`. Its frame (saving `x30`) is the 16 bytes below the stack pointer. -/
def blockMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let y : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .x3 = s.gpr .x1 ∧ 0 < r
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x2) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_scrypt_romix(b = x0, r = x1, v = x2, vlen = x3,
scratch = x4, slen = x5)`: if `r > 0`, `vlen = N r` for a power of two `N`,
and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix. It
has no frame (it saves `x30` in `scratch`); its calls of `vg_scrypt_blockmix`
use the 16 bytes below the stack pointer. The indices `j` of step 3 are
public. -/
def roMixAArch64 : Contract AArch64.isa where
  pre s :=
    let r := (s.gpr .x1).toNat
    let b : Region := ⟨s.gpr .x0, r * 128⟩
    let v : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .x4, (s.gpr .x5).toNat * 128⟩
    let stack : Region := ⟨s.sp - 16, 16⟩
    s.rd = [] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (s.gpr .x0).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .x4).toNat + (s.gpr .x5).toNat * 128 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .x3).toNat % r = 0 ∧ ((s.gpr .x3).toNat / r).isPowerOfTwo ∧
    (s.gpr .x5).toNat = r + 2
  post s s' := let r := (s.gpr .x1).toNat
    bytesAt s'.mem (s.gpr .x0) (128 * r) =
      roMix r ((s.gpr .x3).toNat / r) (bytesAt s.mem (s.gpr .x0) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .x1).toNat ((s₁.gpr .x3).toNat / (s₁.gpr .x1).toNat)
        (bytesAt s₁.mem (s₁.gpr .x0) (128 * (s₁.gpr .x1).toNat)) =
      roMixIndices (s₂.gpr .x1).toNat ((s₂.gpr .x3).toNat / (s₂.gpr .x1).toNat)
        (bytesAt s₂.mem (s₂.gpr .x0) (128 * (s₂.gpr .x1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.AArch64.BlockMix

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.MdStream.AArch64 (Upd Mupd wp_ldr wp_str)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length
  bytesAt_add bytesAt_writeBytes_sep)

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_eor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .eor .x d n m :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n ^^^ s.gpr m))
    (by simp [exec, State.read]) (k _ (Upd.write64 _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl .x d n sh :: is)) s Q :=
  Proof.MdStream.AArch64.WP.cons (s' := s.write .x d (s.gpr n <<< sh))
    (by simp [exec, h, State.read]) (k _ (Upd.write64 _ _ _))

end

end VG.Proof.Scrypt.AArch64.BlockMix
