module

import VerifiedGarbage.Proof.Scrypt.Memory
import all Init.Data.Nat.Power2.Basic
public import VerifiedGarbage.Proof.MdStream.PPC64LE.Basic
public import VerifiedGarbage.Impl.Scrypt.PPC64LE.BlockMix
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha256.Stream

/-!
# scrypt on PPC64LE: common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are the contracts of the proofs, and the
64-byte exclusive-or.
-/

@[expose] public section

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.PPC64LE in
/-- PPC64LE contract for `vg_scrypt_blockmix(b = r3, r = r4, y = r5, ry = r6,
scratch = r7)`: if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at
`b` to `y`. Its frame (saving the link register) is the 48 bytes below the
stack pointer. -/
def blockMixPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let r := (s.gpr .r4).toNat
    let b : Region := ⟨s.gpr .r3, r * 128⟩
    let y : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .r7, 128⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .r3).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .r6 = s.gpr .r4 ∧ 0 < r
  post s s' := let r := (s.gpr .r4).toNat
    bytesAt s'.mem (s.gpr .r5) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .r3) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

open VG.PPC64LE in
/-- PPC64LE contract for `vg_scrypt_romix(b = r3, r = r4, v = r5, vlen = r6,
scratch = r7, slen = r8)`: if `r > 0`, `vlen = N r` for a power of two `N`,
and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix. It
has no frame (it saves its return address in `scratch`); its calls of
`vg_scrypt_blockmix` use the 48 bytes below the stack pointer. The indices
`j` of step 3 are public. -/
def roMixPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let r := (s.gpr .r4).toNat
    let b : Region := ⟨s.gpr .r3, r * 128⟩
    let v : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat * 128⟩
    let stack : Region := ⟨s.sp - 48, 48⟩
    s.rd = [] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    48 ≤ s.sp.toNat ∧ stack.Disjoint b ∧ stack.Disjoint v ∧ stack.Disjoint scratch ∧
    (s.gpr .r3).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r7).toNat + (s.gpr .r8).toNat * 128 ≤ 2 ^ 64 ∧
    0 < r ∧ (s.gpr .r6).toNat % r = 0 ∧ ((s.gpr .r6).toNat / r).isPowerOfTwo ∧
    (s.gpr .r8).toNat = r + 2
  post s s' := let r := (s.gpr .r4).toNat
    bytesAt s'.mem (s.gpr .r3) (128 * r) =
      roMix r ((s.gpr .r6).toNat / r) (bytesAt s.mem (s.gpr .r3) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.sp = s₂.sp ∧
    roMixIndices (s₁.gpr .r4).toNat ((s₁.gpr .r6).toNat / (s₁.gpr .r4).toNat)
        (bytesAt s₁.mem (s₁.gpr .r3) (128 * (s₁.gpr .r4).toNat)) =
      roMixIndices (s₂.gpr .r4).toNat ((s₂.gpr .r6).toNat / (s₂.gpr .r4).toNat)
        (bytesAt s₂.mem (s₂.gpr .r3) (128 * (s₂.gpr .r4).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.PPC64LE.BlockMix

open VG VG.PPC64LE VG.Impl.Scrypt.PPC64LE
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_ld wp_std)
open VG.Proof.Scrypt.Memory (sub_off writeW_xor xorBytes_length bytesAt_length
  bytesAt_add bytesAt_writeBytes_sep)

theorem wp_xor {is : List Instr} {s : State} {Q : State → Prop} {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  Proof.MdStream.PPC64LE.WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- The first `n` doublewords of `[dst] ← [x] xor [src]`, for 64-byte blocks
`d`, `x`, `y` in memory, where `d` overlaps neither of the others. The code
uses `r9` and `r10`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .r9 ∧ dR ≠ .r10 ∧ dR ≠ .r0)
    (hx : xR ≠ .r9 ∧ xR ≠ .r10 ∧ xR ≠ .r0) (hs : sR ≠ .r9 ∧ sR ≠ .r10 ∧ sR ≠ .r0)
    {d x y : Addr} (hdx : Region.Disjoint ⟨d, 64⟩ ⟨x, 64⟩) (hdy : Region.Disjoint ⟨d, 64⟩ ⟨y, 64⟩) :
    ∀ n ≤ 8, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ k < 8, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8) →
    (∀ s', (∀ r, r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ld (a := x + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [g₁ _ hx.1 hx.2.1, gx]) (by rw [rd₁, wr₁]; exact hinx n (by omega)) (fun s₂ u₂ => ?_)
      hx.2.2
    refine wp_ld (a := y + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₂.other _ hs.1, g₁ _ hs.1 hs.2.1, gy])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega)) (fun s₃ u₃ => ?_) hs.2.2
    refine wp_xor fun s₄ u₄ => ?_
    refine wp_std (a := d + BitVec.ofNat 64 (8 * n)) ⟨by omega, by omega⟩
      (by rw [u₄.other _ hd.1, u₃.other _ hd.2.1, u₂.other _ hd.1, g₁ _ hd.1 hd.2.1, gd])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      (fun s₅ u₅ => k s₅ (fun r h9 h10 => by
          rw [u₅.gpr, u₄.other r h9, u₃.other r h10, u₂.other r h9, g₁ r h9 h10])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_) hd.2.2
    have hl : (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))).length = 8 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (8 * n), 8⟩ ⟨d, (xorBytes (bytesAt s.mem x (8 * n))
        (bytesAt s.mem y (8 * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, writeW_xor,
      m₁, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := writeBytes_append s.mem d _ (xorBytes (bytesAt s.mem (x + BitVec.ofNat 64 (8 * n)) 8)
      (bytesAt s.mem (y + BitVec.ofNat 64 (8 * n)) 8))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

end VG.Proof.Scrypt.PPC64LE.BlockMix
