module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Spec.Aes.Contract
public import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.Proof.Framework.PowLit

/-! # PPC64LE AES contracts -/

@[expose] public section

namespace VG.Proof.Aes

open VG.PPC64LE in
/-- PPC64LE contract for `vg_aes_encrypt_blocks(schedule: *const [u8; 240],
rounds: usize, data: *mut [u8; 16], n: usize, scratch: *mut [u64; 256])` (and
`vg_aes_decrypt_blocks`, with `f` the inverse cipher): replaces each of the
`n` blocks at `data` with `f rounds w` of it, for the key schedule `w`.

The code may read `schedule` (240 bytes) and read and write `data` (`16 n`
bytes) and `scratch` (2048 bytes, whose contents on exit are unspecified).
These may not overlap each other, and `data` may not wrap around the end of
the address space. `rounds` is 10, 12 or 14. The pointers, `rounds` and `n`
are public; the key schedule and the data are secret. -/
def blocksPPC64LE (f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State) : Contract PPC64LE.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let data : Region := ⟨s.gpr .r5, 16 * (s.gpr .r6).toNat⟩
    let scratch : Region := ⟨s.gpr .r7, 2048⟩
    s.rd = [sched] ∧ s.wr = [data, scratch] ∧
    sched.Disjoint data ∧ sched.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .r5).toNat + 16 * (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    Spec.Aes.statesAt s'.mem (s.gpr .r5) (s.gpr .r6).toNat =
      (Spec.Aes.statesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat).map
        (f (s.gpr .r4).toNat (Spec.Aes.bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1))))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes

open Spec.Gcm

open VG.PPC64LE in
/-- PPC64LE contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds: usize,
counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut [u64;
256])`: XORs the AES counter-mode keystream from the counter block at `counter`
into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block and
the data are secret. -/
def ctr32PPC64LE : Contract PPC64LE.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .r3, 240⟩
    let counter : Region := ⟨s.gpr .r5, 16⟩
    let data : Region := ⟨s.gpr .r6, 16 * (s.gpr .r7).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 2048⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .r6).toNat + 16 * (s.gpr .r7).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .r4).toNat = 10 ∨ (s.gpr .r4).toNat = 12 ∨ (s.gpr .r4).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .r4).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .r3) (16 * ((s.gpr .r4).toNat + 1)))
    blocksAt s'.mem (s.gpr .r6) (s.gpr .r7).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .r5)) (blocksAt s.mem (s.gpr .r6) (s.gpr .r7).toNat) ∧
      blockAt s'.mem (s.gpr .r5) = Nat.repeat inc32 (s.gpr .r7).toNat (blockAt s.mem (s.gpr .r5))
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
    s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes

open VG.PPC64LE in
/-- PPC64LE contract for `vg_aes_expand_key_scratch(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: writes the key schedule of
the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other. `key_len` is 16, 24 or 32. The
pointers and `key_len` are public; the key is secret. -/
def expandKeyPPC64LE : Contract PPC64LE.isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sched : Region := ⟨s.gpr .r5, 240⟩
    let scratch : Region := ⟨s.gpr .r6, 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ((s.gpr .r4).toNat = 16 ∨ (s.gpr .r4).toNat = 24 ∨ (s.gpr .r4).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .r5) (16 * (Spec.Aes.rounds ((s.gpr .r4).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes
open VG.PPC64LE

/-- The direct key API needs no scratch region or stack frame. -/
def expandKeyDirectPPC64LE : Contract PPC64LE.isa where
  pre s :=
    s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩] ∧ s.wr = [⟨s.gpr .r5, 240⟩] ∧
    (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r5, 240⟩ ∧
    ((s.gpr .r4).toNat = 16 ∨ (s.gpr .r4).toNat = 24 ∨ (s.gpr .r4).toNat = 32)
  post := expandKeyPPC64LE.post
  pub s₁ s₂ := s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧
    s₁.gpr .r5 = s₂.gpr .r5 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes
