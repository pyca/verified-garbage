module

public import VerifiedGarbage.Proof.Sha256.Stream
public import VerifiedGarbage.Spec.Pbkdf2
import VerifiedGarbage.Proof.Hmac.Common
meta import Lean.Elab.Tactic.Omega.Frontend
import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# PBKDF2-HMAC-SHA-256's iteration: memory lemmas

Facts about bytes of memory, regions, the exclusive-or of words and the
iteration itself that the proofs of every target share, so that none imports
another target's proof.
-/

@[expose] public section

namespace VG.Proof.Pbkdf2.Memory

open VG.Proof.Sha256.Stream (writeBytes writeBytes_append write_eq_writeBytes)
open VG.Spec.Sha256 (bytesAt stateAt blockAt HashValue)
open VG.Proof.Hmac.Common (bytesAt_add read_congr₂ stateAt_eq_of_bytes writeBytes_at bytesAt_getD'
  bytesAt_length bytesAt_writeBytes_self)

/-! ## Helpers

Copies of lemmas of the x86-64 SHA-256 proofs, which this module does not
import; the lemmas about bytes are the target-independent HMAC ones
(`Proof/Hmac/Common.lean`). -/

private theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

private theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := by
  intro a ha
  simp only [Region.Contains] at *
  have : (a - base).toNat ≤ (a - (base + BitVec.ofNat 64 off)).toNat + off := by
    rw [show a - base = (a - (base + BitVec.ofNat 64 off)) + BitVec.ofNat 64 off by bv_omega,
      BitVec.toNat_add, toNat_ofNat_lt ho]
    exact Nat.mod_le _ _
  omega

/-! ## Memory -/

theorem frame_bytesAt {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => hf.bytes (R := ⟨p, n⟩) hd hn (List.mem_range.mp hi)

theorem contains_base {a : Addr} {n len : Nat} (h : n ≤ len) : (⟨a, len⟩ : Region).Contains a n := by
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem off_contains {a x : Addr} {o n len : Nat} (h : (x - (a + BitVec.ofNat 64 o)).toNat < n)
    (hl : o + n ≤ len) (ho : o < 2 ^ 64) : (⟨a, len⟩ : Region).Contains x 1 :=
  sub_offset (off := o) (len := n) hl ho x (by simp only [Region.Contains]; omega)

/-- Bytes from `p + a` are not among the first `a` from `p`. -/
theorem sep_after {p x : Addr} {a n : Nat} (h₁ : (x - (p + BitVec.ofNat 64 a)).toNat < n) (h₂ : (x - p).toNat < a)
    (ha : a + n < 2 ^ 64) : False := by
  rw [show x - p = (x - (p + BitVec.ofNat 64 a)) + BitVec.ofNat 64 a by bv_omega, BitVec.toNat_add,
    toNat_ofNat_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h₂
  omega

theorem xorBytes_length (a b : List Byte) (h : a.length = b.length) :
    (Spec.Pbkdf2.xorBytes a b).length = a.length := by
  simp [Spec.Pbkdf2.xorBytes, h]

theorem writeW_bytes (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (xs : List Byte)
    (h : ((List.range (w / 8)).map fun j => (v.setWidth (8 * (w / 8))).extractLsb' (8 * j) 8) = xs) :
    m.writeW a v = writeBytes m a xs := by
  rw [Mem.writeW, write_eq_writeBytes, h]

theorem writeBytes_append' (m : Mem) {q q' : Addr} (xs ys : List Byte) (hq : q' = q + BitVec.ofNat 64 xs.length)
    (h : xs.length + ys.length < 2 ^ 64) : writeBytes (writeBytes m q xs) q' ys = writeBytes m q (xs ++ ys) := by
  subst hq; exact writeBytes_append m q xs ys h

/-! ## Regions -/

theorem add_ofNat (a : Addr) (o j : Nat) : a + BitVec.ofNat 64 o + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The result -/

/-- A byte of the low 32 bits of `i`: `INT (i)`'s bytes. -/
theorem mod32_div_mod8 (i k : Nat) (hk : k + 8 ≤ 32) : i % 2 ^ 32 / 2 ^ k % 2 ^ 8 = i / 2 ^ k % 2 ^ 8 := by
  rw [show 2 ^ 32 = 2 ^ k * 2 ^ (32 - k) by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)],
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

end VG.Proof.Pbkdf2.Memory
