module

import VerifiedGarbage.Proof.AesGcm.AArch64.Stitch.ShortAes
import VerifiedGarbage.Proof.Gcm.Short
import VerifiedGarbage.Proof.AesCcm.BytesAt
import VerifiedGarbage.Proof.AesGcm.AArch64.Env
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.AesGcm.AArch64.Callee
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
import VerifiedGarbage.Proof.AesGcm.AArch64.Fn
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Seal
import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Entry
public import VerifiedGarbage.Proof.Gcm.Ctr
public import VerifiedGarbage.Proof.Framework.WriteBytes
public import VerifiedGarbage.Proof.Aes.AArch64.Group
import Mathlib.Data.List.Induction
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Aes.AArch64.CodeLit
public import VerifiedGarbage.Proof.Aes.KeyExp
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.AesGcm.AArch64.Loops

/-!
# AES-GCM on AArch64, short records: what the buffers hold

Untrusted: everything here is checked by Lean. After one `aesPart` over
`B₁` from the counter `c₀ + n − 7`, its blocks from `p = 7 − n` on are the
text XORed with counter mode from `inc₃₂(J₀)` (`b1_gctr`, the counter
having wrapped around: `ksByte_wrap`), and block `p − 1`, zero before, is
`CIPH_K(J₀)` (`b1_j0`). `B₂` holds zero blocks, the additional data and the
text each padded, and the lengths block (`b2_layout`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.AArch64.Stitch

open VG VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt zeros ofBytes toBytes inc32 aesWith gctr)
open VG.Proof.Gcm (xorKs ksByte)
open VG.Proof.Aes.AArch64 (keyStream)

/-- The keystream of `keyStream` is counter mode's. -/
theorem keyStream_ks (R : Nat) (w : List Byte) (icb : Block) (i : Nat) :
    keyStream R w icb i = ksByte (aesWith R w) icb i := by
  have ht : i % 16 < 16 := Nat.mod_lt _ (by decide)
  rw [keyStream, ksByte, aesWith, Proof.Aes.toBytes_ofBytes (by simp) ht, Proof.Aes.getD_eq _ ht,
    List.getD_eq_getElem?_getD, Vector.getElem?_toList, Vector.getElem?_eq_getElem ht, Option.getD_some]
  rfl

/-- `B₁`'s blocks from `7 − c` on, `n` bytes of `P` XORed with the keystream
of `aesPart` from `2³² + c − 7` blocks on: counter mode from `icb`. -/
theorem b1_gctr {m₀ m : Mem} {B : Addr} {R c n : Nat} {w : List Byte} {icb : Block} {P : List Byte}
    (hn : n ≤ 16 * c) (hc6 : c ≤ 6)
    (hks : ∀ j < 8, ∀ t < 16, m (B + BitVec.ofNat 64 (16 * j + t)) =
      keyStream R w icb (16 * (2 ^ 32 + c - 7 + j) + t) ^^^ m₀ (B + BitVec.ofNat 64 (16 * j + t)))
    (hP : bytesAt m₀ (B + BitVec.ofNat 64 (16 * (7 - c))) n = P) :
    bytesAt m (B + BitVec.ofNat 64 (16 * (7 - c))) n = gctr (aesWith R w) icb P := by
  have hPl : P.length = n := by rw [← hP, Proof.AesCcm.length_bytesAt]
  rw [Proof.Gcm.gctr_eq]
  refine Proof.Gcm.list_ext (by rw [Proof.AesCcm.length_bytesAt, Proof.Gcm.length_xorKs, hPl]) fun k hk => ?_
  rw [Proof.AesCcm.length_bytesAt] at hk
  rw [Proof.Gcm.getD_xorKs _ _ _ _ (by rw [hPl]; exact hk), Nat.zero_add, ← hP, Proof.Gcm.getD_bytesAt' _ _ hk,
    Proof.Gcm.getD_bytesAt' _ _ hk, Offset.add_add,
    show 16 * (7 - c) + k = 16 * (7 - c + k / 16) + k % 16 by omega,
    hks _ (by omega) _ (Nat.mod_lt _ (by decide)), keyStream_ks,
    show 16 * (2 ^ 32 + c - 7 + (7 - c + k / 16)) + k % 16 = 16 * 2 ^ 32 + k by omega, Proof.Gcm.ksByte_wrap,
    BitVec.xor_comm]

/-- Block `6 − c` of `B₁`, zero before: `CIPH(J)`, for the keystream from `inc₃₂(J)`. -/
theorem b1_j0 {m₀ m : Mem} {B : Addr} {R c : Nat} {w : List Byte} {J : Block} (hc6 : c ≤ 6)
    (hks : ∀ j < 8, ∀ t < 16, m (B + BitVec.ofNat 64 (16 * j + t)) =
      keyStream R w (inc32 J) (16 * (2 ^ 32 + c - 7 + j) + t) ^^^ m₀ (B + BitVec.ofNat 64 (16 * j + t)))
    (hz : bytesAt m₀ (B + BitVec.ofNat 64 (16 * (6 - c))) 16 = zeros 16) :
    blockAt m (B + BitVec.ofNat 64 (16 * (6 - c))) = aesWith R w J := by
  refine Proof.Aes.block_ext fun t ht => ?_
  have h0 : m₀ (B + BitVec.ofNat 64 (16 * (6 - c) + t)) = 0 := by
    have := congrArg (·.getD t 0) hz
    simp only [Proof.Gcm.getD_bytesAt' _ _ ht, Offset.add_add] at this
    rw [this]
    simp only [zeros, List.getD_eq_getElem?_getD, List.getElem?_replicate, ht, ite_true, Option.getD_some]
  rw [Proof.Aes.toBytes_blockAt _ _ ht, Offset.add_add, hks _ (by omega) _ ht, h0,
    show ∀ x : Byte, x ^^^ 0 = x from fun _ => BitVec.xor_zero,
    keyStream_ks, show 2 ^ 32 + c - 7 + (6 - c) = 2 ^ 32 - 1 by omega, Proof.Gcm.ksByte_pred _ _ ht]

/-- What `B₂` (at `G`) holds: zeroed, then, after writes elsewhere, the `16 c`
bytes `Q` at block `7 − c`, 16 zeros after their first `n`, the additional
data `A` at block `6 − c` and the lengths block at block 7. -/
theorem b2_layout {G : Addr} {c n : Nat} {Q A lens : List Byte} {mZ mY mL : Mem} {rs : List Region}
    (hc6 : c ≤ 6) (hn : n ≤ 16 * c) (hn' : 16 * c ≤ n + 16) (hQ : Q.length = 16 * c)
    (hA : A.length ≤ 16)
    (hZ : bytesAt mZ G 128 = zeros 128) (fY : Frame rs mZ mY) (hrs : ∀ r ∈ rs, (⟨G, 128⟩ : Region).Disjoint r)
    (fL : Frame [⟨G + BitVec.ofNat 64 112, 16⟩]
      (writeBytes (writeBytes (writeBytes mY (G + BitVec.ofNat 64 (112 - 16 * c)) Q)
        (G + BitVec.ofNat 64 (112 - 16 * c + n)) (List.replicate 16 0)) (G + BitVec.ofNat 64 (96 - 16 * c)) A) mL)
    (hL : bytesAt mL (G + BitVec.ofNat 64 112) 16 = lens) :
    bytesAt mL G 128 =
      zeros (16 * (6 - c)) ++ A ++ zeros (16 - A.length) ++ Q.take n ++ zeros (16 * c - n) ++ lens := by
  have Z : ∀ a b, zeros a ++ zeros b = zeros (a + b) := fun a b => List.replicate_append_replicate
  have lz : ∀ a, (zeros a).length = a := fun a => List.length_replicate
  -- The first `k` bytes, and those after the first `k`, of a list split there.
  have tk : ∀ (l₁ l₂ : List Byte) (k : Nat), l₁.length = k → (l₁ ++ l₂).take k = l₁ :=
    fun _ _ _ h => List.take_left' h
  have dk : ∀ (l₁ l₂ : List Byte) (k : Nat), l₁.length = k → (l₁ ++ l₂).drop k = l₂ :=
    fun _ _ _ h => List.drop_left' h
  have wr : ∀ (m : Mem) (o : Nat) (xs : List Byte), o + xs.length ≤ 128 → ∀ (l₁ l₂ l₃ : List Byte),
      bytesAt m G 128 = l₁ ++ l₂ ++ l₃ → l₁.length = o → l₂.length = xs.length →
      bytesAt (writeBytes m (G + BitVec.ofNat 64 o) xs) G 128 = l₁ ++ xs ++ l₃ := by
    intro m o xs h l₁ l₂ l₃ e h₁ h₂
    rw [Proof.AesCcm.bytesAt_writeBytes_at _ _ _ h (by decide), e,
      show l₁ ++ l₂ ++ l₃ = l₁ ++ (l₂ ++ l₃) from List.append_assoc .., tk _ _ _ h₁,
      show o + xs.length = (l₁ ++ l₂).length by simp [h₁, h₂], ← List.append_assoc l₁ l₂ l₃, dk _ _ _ rfl]
  -- `B₂` before the writes.
  have L0 : bytesAt mY G 128 = zeros (112 - 16 * c) ++ zeros (16 * c) ++ zeros 16 := by
    rw [bytesAt_frame fY hrs (by decide), hZ, Z, Z]; congr 1; omega
  have L1 := wr _ (112 - 16 * c) Q (by rw [hQ]; omega) _ _ _ L0 (lz _) (by rw [lz, hQ])
  rw [← List.take_append_drop n Q,
    show zeros 16 = zeros (16 - (16 * c - n)) ++ zeros (16 * c - n) by rw [Z]; congr 1; omega] at L1
  have L2 := wr _ (112 - 16 * c + n) (List.replicate 16 0) (by simp; omega)
    (zeros (112 - 16 * c) ++ Q.take n) (Q.drop n ++ zeros (16 - (16 * c - n))) (zeros (16 * c - n))
    (by rw [L1]; simp only [List.append_assoc]) (by simp [lz]; omega) (by simp [lz]; omega)
  have L2' : bytesAt (writeBytes (writeBytes mY (G + BitVec.ofNat 64 (112 - 16 * c)) (List.take n Q ++ List.drop n Q))
      (G + BitVec.ofNat 64 (112 - 16 * c + n)) (List.replicate 16 0)) G 128 =
      zeros (96 - 16 * c) ++ zeros A.length ++
        (zeros (16 - A.length) ++ Q.take n ++ zeros 16 ++ zeros (16 * c - n)) := by
    rw [L2, show zeros (112 - 16 * c) = zeros (96 - 16 * c) ++ zeros A.length ++ zeros (16 - A.length) by
      rw [Z, Z]; congr 1; omega]
    simp only [List.append_assoc]; rfl
  have L3 := wr _ (96 - 16 * c) A (by omega) _ _ _ L2' (lz _) (lz _)
  rw [List.take_append_drop] at L3
  have e128 : (128 : Nat) = 112 + 16 := rfl
  rw [e128, bytesAt_add, hL, bytesAt_frame fL (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.base_disjoint G (Nat.le_refl _) (by decide))
      (by decide), Proof.AesCcm.bytesAt_prefix _ _ (show 112 ≤ 128 by decide), L3]
  simp only [List.append_assoc]
  rw [show zeros 16 ++ zeros (16 * c - n) = zeros (16 * c - n) ++ zeros 16 by rw [Z, Z, Nat.add_comm],
    show 16 * (6 - c) = 96 - 16 * c by omega]
  simp only [← List.append_assoc]
  rw [tk _ _ _ (by simp only [List.length_append, lz, List.length_take, hQ]; omega)]

end VG.Proof.AesGcm.AArch64.Stitch
