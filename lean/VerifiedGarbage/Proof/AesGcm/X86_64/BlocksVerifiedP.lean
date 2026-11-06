module

public import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified
import VerifiedGarbage.Proof.AesGcm.X86_64.Blocks.CT
public import VerifiedGarbage.Spec.Gcm.Precomputed
public import VerifiedGarbage.Proof.Gcm.Contract
public import VerifiedGarbage.Proof.Gcm.OutOfPlaceContract

/-!
# AES-GCM on whole blocks, x86-64: the `_precomputed` functions

Untrusted: everything here is checked by Lean. The shared contracts of
`vg_aes_gcm_encrypt_blocks_precomputed` and `_decrypt_blocks_precomputed`
(`Spec/Gcm/Precomputed.lean`) imply the contracts of `BlocksContract.lean`
for the key context of `vg_aes_gcm_init_precomputed` (`CtxMode.powers`).
The states satisfying them are those of `vg_aes_gcm_encrypt_blocks` with a
key context of 1024 bytes, all zero: its hash subkey is zero, and so are its
powers (`powersRepr_zero`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt hpow mul)

theorem foldl_fix {α β : Type} (f : α → β → α) (a : α) (h : ∀ b, f a b = a) : ∀ l : List β, l.foldl f a = a
  | [] => rfl
  | b :: l => by rw [List.foldl_cons, h b]; exact foldl_fix f a h l

theorem mul_zero_right (x : Block) : mul x 0 = 0 := by
  unfold mul
  rw [foldl_fix _ _ fun i => ?_]
  have e : (0 : Block).getLsbD 0 = false := by decide
  simp only [BitVec.xor_self, e, Bool.false_eq_true, ↓reduceIte]
  split <;> decide

theorem hpow_zero_succ (k : Nat) : hpow 0 (k + 1) = 0 := mul_zero_right _

/-- Memory of zeros holds the powers of its hash subkey, zero. -/
theorem powersRepr_zero (p : Addr) : Spec.Gcm.PowersRepr (fun _ => 0) p := by
  intro k _
  have z : ∀ q : Addr, blockAt (fun _ => 0) q = 0 := fun q => by
    simp [blockAt, Spec.Aes.bytesAt, Spec.Gcm.ofBytes]; decide
  rw [Spec.Gcm.ctxH, z, z, hpow_zero_succ]

end VG.Proof.AesGcm.X86_64
