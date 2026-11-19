module

import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
public import VerifiedGarbage.Spec.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.Contract
meta import VerifiedGarbage.Proof.Gcm.Contract
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.AArch64.Spill
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Spec.Gcm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AArch64.Spill
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
public import VerifiedGarbage.Proof.Framework.Bitslice.Sym
public import VerifiedGarbage.Proof.Aes.Blocks
meta import VerifiedGarbage.Proof.Aes.AArch64.Encrypt
meta import VerifiedGarbage.Proof.Framework.Bitslice.Sym
meta import VerifiedGarbage.Proof.Aes.Blocks

/-! ### `Aes.AArch64.Group`, which this module and modules that import it used -/

section

@[expose] public section

section

/-!
# AES counter mode on AArch64: the data's invariant

What the proofs of the counter-mode functions share: arithmetic of their
loops, and the data after `k` blocks, with the keystream (`keyStream`) XORed
into the first `16 k` bytes in place (`DataInv`) or out of place
(`DataInvM`).
-/

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-! ## The loop -/

theorem ofNat_sub_one {j : Nat} (h : 0 < j) : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
  rw [show j = (j - 1) + 1 by omega_arith, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

end VG.Proof.Aes.AArch64

end


namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-- An access at an offset of a region. -/
theorem in_off {rs : List Region} {b : Addr} {len : Nat} (hr : (⟨b, len⟩ : Region) ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    InRegions rs (b + BitVec.ofNat 64 off) n :=
  ⟨_, hr, Offset.contains_base b h (by omega_arith)⟩

/-! ## The counter blocks -/

theorem sw_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp

/-! ## The counter blocks as states -/

theorem rev32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (rev32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold rev32
  obtain ⟨t0, t1, t2, t3⟩ := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp
    (show (List.range 4).all (fun k => (List.range 8).all fun j => decide (
      (8 * k + j < 8 → 24 + (8 * k + j) = 8 * (3 - k) + j) ∧
      (¬ 8 * k + j < 8 ∧ 8 * k + j - 8 < 8 → 16 + (8 * k + j - 8) = 8 * (3 - k) + j) ∧
      (¬ 8 * k + j < 8 ∧ ¬ 8 * k + j - 8 < 8 ∧ 8 * k + j - 8 - 8 < 8 →
        8 + (8 * k + j - 8 - 8) = 8 * (3 - k) + j) ∧
      (¬ 8 * k + j < 8 ∧ ¬ 8 * k + j - 8 < 8 ∧ ¬ 8 * k + j - 8 - 8 < 8 →
        8 * k + j - 8 - 8 - 8 < 8 ∧ 0 + (8 * k + j - 8 - 8 - 8) = 8 * (3 - k) + j))) = true by decide +kernel)
    k (List.mem_range.mpr hk)) j (List.mem_range.mpr hj))
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split
  next h0 => rw [decide_eq_true h0, Bool.true_and, t0 h0]
  next h0 =>
    split
    next h1 => rw [decide_eq_true h1, Bool.true_and, t1 ⟨h0, h1⟩]
    next h1 =>
      split
      next h2 => rw [decide_eq_true h2, Bool.true_and, t2 ⟨h0, h1, h2⟩]
      next h2 => rw [decide_eq_true (t3 ⟨h0, h1, h2⟩).1, Bool.true_and, (t3 ⟨h0, h1, h2⟩).2]

/-! ## XOR into the data -/

/-- The data after `k` blocks: the keystream `ks` XORed into the first
`16 k` of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 16 * k then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := Offset.sub_toNat' D hj hi

/-- The bytes at `O`: the `16 k` first, the `16 k` at `D` XORed with the
keystream; the rest, as they were. With `O = D`, `DataInv` (`dataInvM_self`). -/
def DataInvM (m₀ m : Mem) (D O : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (O + BitVec.ofNat 64 i) =
    if i < 16 * k then m₀ (D + BitVec.ofNat 64 i) ^^^ ks i else m₀ (O + BitVec.ofNat 64 i)

theorem dataInvM_self {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} :
    DataInvM m₀ m D D n k ks ↔ DataInv m₀ m D n k ks := by
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩ <;> rw [h i hi] <;> by_cases hk : i < 16 * k
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]; exact BitVec.xor_zero.symm
  · rw [ite_eq_left hk, ite_eq_left hk]
  · rw [ite_eq_right hk, ite_eq_right hk]; exact BitVec.xor_zero

/-- A block of the text at `D` XORed with the keystream, stored at `O`. -/
theorem dataInvM_store1 {m₀ m : Mem} {D O : Addr} {n k : Nat} {ks : Nat → Byte} {v : BitVec 128}
    (hn : 16 * n < 2 ^ 64) (hk : k < n) (h : DataInvM m₀ m D O n k ks)
    (hv : ∀ t < 16, vbyte v t = ks (16 * k + t) ^^^ m₀ (D + BitVec.ofNat 64 (16 * k + t))) :
    DataInvM m₀ (m.write (O + BitVec.ofNat 64 (16 * k)) 16 v) D O n (k + 1) ks ∧
      Frame [⟨O, 16 * n⟩] m (m.write (O + BitVec.ofNat 64 (16 * k)) 16 v) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · show (if _ then _ else _) = _
    rw [off_toNat O (by omega_arith) (by omega_arith)]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
        show vbyte _ _ = _
        rw [hv _ h2, show 16 * k + (i - 16 * k) = i by omega_arith, BitVec.xor_comm]
      · rw [ite_eq_right h2, h i hi, ite_eq_right (show ¬ i < 16 * k by omega_arith),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega_arith)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega_arith), h i hi,
        ite_eq_left (show i < 16 * k by omega_arith), ite_eq_left (show i < 16 * (k + 1) by omega_arith)]
  · have hx' : ¬ (x - O).toNat + 1 ≤ 16 * n := hx ⟨O, 16 * n⟩ (List.mem_singleton_self _)
    show (if _ then _ else _) = _
    rw [ite_eq_right]
    intro hlt
    apply hx'
    have e := Offset.toNat_sub_add x O (d := 16 * k) (by omega_arith)
    rw [Offset.sub_add_eq] at hlt
    have := (x - O).isLt
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 16 * k < 2 ^ 64 by omega_arith)] at hlt
    omega_arith

/-- The text at `D` from block `k` on is as in `m₀`: in place by `DataInvM`;
out of place, as in `m₃` (from block `j` on), which only the output's
stores, which do not overlap it, changed. -/
theorem src_keep {m₀ m₃ m : Mem} {D O : Addr} {n k j : Nat} {ks : Nat → Byte}
    (hDO : O = D ∨ Region.Disjoint ⟨D, 16 * n⟩ ⟨O, 16 * n⟩) (hn : 16 * n < 2 ^ 64)
    (h₃ : ∀ i, 16 * j ≤ i → i < 16 * n → m₃ (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i))
    (hf : Frame [⟨O, 16 * n⟩] m₃ m) (h : DataInvM m₀ m D O n k ks) :
    ∀ i, 16 * k ≤ i → 16 * j ≤ i → i < 16 * n → m (D + BitVec.ofNat 64 i) = m₀ (D + BitVec.ofNat 64 i) := by
  intro i hk hj hi
  rcases hDO with rfl | hd
  · rw [h i hi, ite_eq_right (by omega_arith)]
  · rw [hf.bytes (R := ⟨D, 16 * n⟩) (by simp only [List.mem_singleton, forall_eq]; exact hd)
      (by simp only; omega_arith) hi]
    exact h₃ i hj hi

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

/-! ## A group -/

theorem dataInvM_frame {m₀ m m' : Mem} {D O : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨O, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInvM m₀ m D O n k ks) : DataInvM m₀ m' D O n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨O, 16 * n⟩) hd (by simp only; omega_using [hn]) hi

end VG.Proof.Aes.AArch64

end

end

/-!
# AES counter mode on AArch64: the contracts, and the saved registers

The AArch64 contracts of `vg_aes_ctr32`, `vg_aes_ctr32_to` and
`vg_aes_expand_key` (`ctr32AArch64`, `ctr32ToAArch64`, `expandKeyAArch64`);
the callee-saved registers saved in their slots of a scratch buffer and
restored from them (`save_ok`, `restore_ok`); and the final counter and the
contract's postcondition from the data's invariant (`ctr_after`,
`ctr32_of_dataInvM`).
-/

@[expose] public section

namespace VG.Proof.Aes

open Spec.Gcm

open VG.AArch64 in
/-- AArch64 contract for `vg_aes_ctr32(schedule: *const [u8; 240], rounds:
usize, counter: *mut [u8; 16], data: *mut [u8; 16], n: usize, scratch: *mut
[u64; 256])`: XORs the AES counter-mode keystream from the counter block at
`counter` into the `n` blocks at `data`, and advances the counter block by `n`.

The code may read `schedule` (240 bytes) and read and write `counter` (16
bytes), `data` (`16 n` bytes) and `scratch` (2048 bytes, whose contents on
exit are unspecified). These may not overlap each other, and `data` may not
wrap around the end of the address space. `rounds` is 10, 12 or 14. The
pointers, `rounds` and `n` are public; the key schedule, the counter block
and the data are secret. -/
def ctr32AArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let counter : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 2048⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .x1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
    blocksAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .x2)) (blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) ∧
      blockAt s'.mem (s.gpr .x2) = Nat.repeat inc32 (s.gpr .x4).toNat (blockAt s.mem (s.gpr .x2))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.sp = s₂.sp

open VG.AArch64 in
/-- `ctr32AArch64` with `n` bytes of `scratch`: for the implementations that
need less of it (`Ctr32Impl.scratch`), so that their callers allocate only
that. -/
def ctr32AArch64With (n : Nat) : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let counter : Region := ⟨s.gpr .x2, 16⟩
    let data : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, n⟩
    s.rd = [sched] ∧ s.wr = [counter, data, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint data ∧ sched.Disjoint scratch ∧
    counter.Disjoint data ∧ counter.Disjoint scratch ∧ data.Disjoint scratch ∧
    (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post := ctr32AArch64.post
  pub := ctr32AArch64.pub

theorem ctr32AArch64With_2048 : ctr32AArch64With 2048 = ctr32AArch64 := rfl

open VG.AArch64 in
/-- `ctr32AArch64` out of place, for the internal `vg_aes_ctr32_to` and
`vg_aes_ctr32_to_aes` (`schedule = x0, rounds = x1, counter = x2, src = x3,
n = x4, scratch = x5, dst = x6`): the `n` blocks at `src` XORed with the
keystream into the `n` blocks at `dst`, with `src` only read. `src` and `dst`
may not overlap each other, nor the other buffers (but `schedule` and `src`,
both only read), and may not wrap around the end of the address space. `dst`
is public too. -/
def ctr32ToAArch64 : Contract AArch64.isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 240⟩
    let counter : Region := ⟨s.gpr .x2, 16⟩
    let src : Region := ⟨s.gpr .x3, 16 * (s.gpr .x4).toNat⟩
    let dst : Region := ⟨s.gpr .x6, 16 * (s.gpr .x4).toNat⟩
    let scratch : Region := ⟨s.gpr .x5, 2048⟩
    s.rd = [sched, src] ∧ s.wr = [counter, dst, scratch] ∧
    sched.Disjoint counter ∧ sched.Disjoint dst ∧ sched.Disjoint scratch ∧
    counter.Disjoint src ∧ counter.Disjoint dst ∧ counter.Disjoint scratch ∧
    src.Disjoint dst ∧ src.Disjoint scratch ∧ dst.Disjoint scratch ∧
    (s.gpr .x3).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x6).toNat + 16 * (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
    ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    let ciph := aesWith (s.gpr .x1).toNat
      (Spec.Aes.bytesAt s.mem (s.gpr .x0) (16 * ((s.gpr .x1).toNat + 1)))
    blocksAt s'.mem (s.gpr .x6) (s.gpr .x4).toNat =
        ctr32 ciph (blockAt s.mem (s.gpr .x2)) (blocksAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) ∧
      blockAt s'.mem (s.gpr .x2) = Nat.repeat inc32 (s.gpr .x4).toNat (blockAt s.mem (s.gpr .x2))
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧
    s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.sp = s₂.sp

open VG.AArch64 in
/-- AArch64 contract for `vg_aes_expand_key(key: *const u8, key_len: usize,
schedule: *mut [u8; 240], scratch: *mut [u64; 64])`: writes the key schedule of
the `key_len`-byte key at `key` to `schedule`.

The code may read `key` (`key_len` bytes) and read and write `schedule`
(240 bytes) and `scratch` (512 bytes, whose contents on exit are
unspecified). These may not overlap each other. `key_len` is 16, 24 or 32.
The pointers and `key_len` are public; the key is secret. -/
def expandKeyAArch64 : Contract AArch64.isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let sched : Region := ⟨s.gpr .x2, 240⟩
    let scratch : Region := ⟨s.gpr .x3, 512⟩
    s.rd = [key] ∧ s.wr = [sched, scratch] ∧
    key.Disjoint sched ∧ key.Disjoint scratch ∧ sched.Disjoint scratch ∧
    ((s.gpr .x1).toNat = 16 ∨ (s.gpr .x1).toNat = 24 ∨ (s.gpr .x1).toNat = 32)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x2) (16 * (Spec.Aes.rounds ((s.gpr .x1).toNat / 4) + 1)) =
      Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Aes

namespace VG.Proof.Aes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Bitslice VG.Impl.Aes.AArch64 VG.Proof.Aes

/-! ## Saving and restoring the callee-saved registers -/

/-- The callee-saved registers the code uses, in the order of `savedRegs`. -/
def sreg : Nat → Reg
  | 0 => .x19 | 1 => .x20 | 2 => .x21 | 3 => .x22 | 4 => .x23 | 5 => .x24 | 6 => .x25
  | 7 => .x26 | 8 => .x27 | _ => .x28

/-- `savedRegs` at their offsets in bytes. -/
abbrev savedSlots : List (Reg × Nat) := savedRegs.map fun (r, k) => (r, 8 * k)

theorem savedSlots_eq : savedSlots = (List.range 10).map fun i => (sreg i, 8 * (48 + i)) := rfl

theorem slots_idx {p : Reg × Nat} (hp : p ∈ savedSlots) : ∃ i < 10, p = (sreg i, 8 * (48 + i)) := by
  rw [savedSlots_eq] at hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  exact ⟨i, List.mem_range.mp hi, rfl⟩

theorem slots_mem {i : Nat} (hi : i < 10) : (sreg i, 8 * (48 + i)) ∈ savedSlots := by
  rw [savedSlots_eq]; exact List.mem_map_of_mem (List.mem_range.mpr hi)

theorem slots_fits : Spill.Fits savedSlots := by decide

theorem slots_restorable : Spill.Restorable sb savedSlots := by decide

theorem slots_end : ∀ p ∈ savedSlots, p.2 + 8 ≤ 8 * 59 := by decide

theorem saveRegs_eq : saveRegs = Spill.saveCode sb savedSlots := rfl

theorem restoreRegs_eq : restoreRegs = Spill.restoreCode sb savedSlots := rfl

/-- The saved registers are in slots 48–57. -/
def Saved (s₀ : State) (b : Addr) (m : Mem) : Prop :=
  ∀ i < 10, m.readW (wordAddr b (48 + i)) 64 = s₀.gpr (sreg i)

theorem save_ok {s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr) (hb : s.gpr sb = b)
    (hn : 8 * 59 ≤ n) :
    WP isa (.block saveRegs) s fun s' => Saved s b s'.mem ∧ s'.gpr = s.gpr ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨b, 8 * 59⟩] s.mem s'.mem := by
  rw [saveRegs_eq]; subst hb
  refine WP.mono (Spill.save_wp slots_fits.1 fun p hp => ?_) fun s' h =>
    ⟨fun i hi => ?_, h.gpr, h.rd, h.wr, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := slots_idx hp
    refine ⟨_, hw, ?_⟩
    show (⟨s.gpr sb, n⟩ : Region).Contains (s.gpr sb + BitVec.ofNat 64 (8 * (48 + i))) 8
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · have h' := Spill.saveMem_saved slots_fits s.mem (s.gpr sb) s.gpr _ (slots_mem hi)
    dsimp only at h'
    rw [h.mem]; exact h'
  · rw [h.mem]; exact Spill.saveMem_frame_base slots_end (by decide) _ _ _

theorem restore_ok {s₀ s : State} {b : Addr} {n : Nat} (hw : (⟨b, n⟩ : Region) ∈ s.wr)
    (hb : s.gpr sb = b) (hn : 8 * 59 ≤ n) (hs : Saved s₀ b s.mem) :
    WP isa (.block restoreRegs) s fun s' => (∀ i < 10, s'.gpr (sreg i) = s₀.gpr (sreg i)) ∧
      s'.mem = s.mem ∧ (∀ r, r ∉ savedSlots.map Prod.fst → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  rw [restoreRegs_eq]
  refine WP.mono (Spill.restore_wp hb slots_fits.1 slots_restorable (fun p hp => ?_) (fun p hp => ?_))
    fun s' h => ⟨fun i hi => h.gpr _ (slots_mem hi), h.mem, h.other, h.rd, h.wr⟩
  · obtain ⟨i, hi, rfl⟩ := slots_idx hp
    refine ⟨_, List.mem_append_right _ hw, ?_⟩
    show (⟨b, n⟩ : Region).Contains (b + BitVec.ofNat 64 (8 * (48 + i))) 8
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  · obtain ⟨i, hi, rfl⟩ := slots_idx hp
    exact hs i hi

/-! ## The counter block -/

theorem c_off (base : Addr) {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n :=
  Offset.contains_base base h ho

theorem out_of_disj {r₁ r₂ : Region} (hd : r₁.Disjoint r₂) {x a : Addr} {n : Nat} (hx : r₁.Contains x 1)
    (ha : r₂.Contains a n) : ¬ (x - a).toNat < n := fun h => hd x hx (ha.byte h)

section Setup

variable {m : Mem} {b ctr : Addr} {N : BitVec 64}

theorem writeW_apply {m : Mem} {a x : Addr} {w : Nat} (v : BitVec w) :
    m.writeW a v x = if (x - a).toNat < w / 8 then
      (v.setWidth (8 * (w / 8))).extractLsb' (8 * (x - a).toNat) 8 else m x := rfl

end Setup

/-! ## The counter block and the data, as blocks -/

/-- The counter, as the slot holds it. -/
theorem icb_lo (m : Mem) (ctr : Addr) :
    rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) = (Spec.Gcm.blockAt m ctr).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have e : t = 8 * (t / 8) + t % 8 := by omega_arith
  rw [e, rev32_bit _ (by omega_arith) (by omega_arith), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega_arith : 8 * (t / 8) + t % 8 < 32), Bool.true_and,
    show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega_arith,
    blockAt_bit _ _ (by omega_arith) (by omega_arith)]
  have hb := Mem.readW_byte m (ctr + BitVec.ofNat 64 12) (i := 3 - t / 8) (by omega_arith)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 12 + (3 - t / 8) = 15 - t / 8 by omega_arith] at hb
  rw [hb, BitVec.getLsbD_extractLsb']
  simp [show t % 8 < 8 by omega_arith]

theorem ctr_after {m m' : Mem} {ctr : Addr} {n : Nat}
    (h : ∀ k < 16, m' (ctr + BitVec.ofNat 64 k) = if k < 12 then m (ctr + BitVec.ofNat 64 k)
      else (rev32 (rev32 (m.readW (ctr + BitVec.ofNat 64 12) 32) +
        (BitVec.ofNat 64 n).setWidth 32)).extractLsb' (8 * (k - 12)) 8) :
    Spec.Gcm.blockAt m' ctr = Nat.repeat Spec.Gcm.inc32 n (Spec.Gcm.blockAt m ctr) := by
  refine block_ext fun k hk => ?_
  rw [toBytes_blockAt _ _ hk, h k hk, ctrBlock_byte _ _ hk]
  split
  · rw [toBytes_blockAt _ _ hk]
  · rw [icb_lo, show (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n by
      apply BitVec.eq_of_toNat_eq; simp]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', rev32_bit _ (by omega_arith) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega_arith

/-- The blocks of the output, once all are written. -/
theorem ctr32_of_dataInvM {m₀ m : Mem} {D O : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (h : DataInvM m₀ m D O n n (keyStream R w icb)) :
    Spec.Gcm.blocksAt m O n = Spec.Gcm.ctr32 (Spec.Gcm.aesWith R w) icb (Spec.Gcm.blocksAt m₀ D n) := by
  unfold Spec.Gcm.ctr32 Spec.Gcm.keystream Spec.Gcm.blocksAt
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_zipWith, List.length_map,
    List.length_range]
  simp only [List.length_map, List.length_range] at h1
  refine block_ext fun k hk => ?_
  rw [toBytes_xor _ _ hk, toBytes_blockAt _ _ hk, toBytes_blockAt _ _ hk,
    BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add, h _ (by omega_arith),
    ite_eq_left (by omega_arith)]
  refine congrArg (_ ^^^ ·) ?_
  unfold Spec.Gcm.aesWith
  rw [toBytes_ofBytes (by simp) hk, keyStream, show (16 * i + k) / 16 = i by omega_arith,
    show (16 * i + k) % 16 = k by omega_arith, getD_eq _ hk, List.getD_eq_getElem?_getD,
    Vector.getElem?_toList, Vector.getElem?_eq_getElem hk, Option.getD_some]
  rfl

/-! ## Setting up the loops -/

theorem shl4 (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

/-! ## The whole function -/

theorem saved_frame {s₀ : State} {b : Addr} {m m' : Mem} {rs : List Region} (h : Saved s₀ b m)
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 384, 88⟩ r) :
    Saved s₀ b m' := fun i hi => by
  rw [← h i hi]
  exact hf.readW (off_contains b (by omega_arith) (by omega_arith) (by omega_arith)) hd (by decide)

end VG.Proof.Aes.AArch64
