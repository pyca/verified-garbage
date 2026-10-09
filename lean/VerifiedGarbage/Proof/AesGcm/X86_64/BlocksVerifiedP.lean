import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerified

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

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

/-- A state satisfying the preconditions of `vg_aes_gcm_encrypt_blocks_precomputed`
and `_decrypt_blocks_precomputed`: `blocksSat`, with a key context of 1024 bytes. -/
def blocksSatP : State := { blocksSat with rd := [⟨0x1000, 1024⟩, ⟨0x8008, 8⟩] }

theorem encryptBlocksP_verified (v : GcmImpl) (st : Option (StitchCode CtxMode.powers)) :
    Verified X86_64.target (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)) false (encFull st))
      (Spec.Gcm.encryptBlocksPrecomputedContract X86_64.abi 8) :=
  Verified.of_correct (encryptBlocksM_correct v st) (Blocks.encrypt_ct v st)
    { pre := by
        sig_implies_pre [Spec.Gcm.encryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPrecomputedPre, Proof.AesGcm.encryptBlocksX86_64M, Proof.AesGcm.blocksPreM,
          CtxMode.powers, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
          Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
          List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.encryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPrecomputedPre, Proof.AesGcm.encryptBlocksX86_64M,
          Proof.AesGcm.encryptBlocksX86_64, X86_64.abi, Proof.AesGcm.arg, X86_64.stackArg,
          X86_64.stackArgAddr, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.encryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Proof.AesGcm.encryptBlocksX86_64M, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, X86_64.argRegs]
      sat := ⟨blocksSatP, by
        sig_pre [Spec.Gcm.encryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPrecomputedPre, X86_64.abi, X86_64.argRegs, blocksSatP, blocksSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact powersRepr_zero _
          | exact Region.disjoint_of_sep (by decide)⟩ }

theorem decryptBlocksP_verified (v : GcmImpl) (st : Option (StitchCode CtxMode.powers)) :
    Verified X86_64.target (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)))
      (Spec.Gcm.decryptBlocksPrecomputedContract X86_64.abi 8) :=
  Verified.of_correct (decryptBlocksM_correct v st) (Blocks.decrypt_ct v st)
    { pre := by
        sig_implies_pre [Spec.Gcm.decryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPrecomputedPre, Proof.AesGcm.decryptBlocksX86_64M, Proof.AesGcm.blocksPreM,
          CtxMode.powers, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
          Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
          List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.decryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPrecomputedPre, Proof.AesGcm.decryptBlocksX86_64M,
          Proof.AesGcm.decryptBlocksX86_64, X86_64.abi, Proof.AesGcm.arg, X86_64.stackArg,
          X86_64.stackArgAddr, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.decryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Proof.AesGcm.decryptBlocksX86_64M, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, X86_64.argRegs]
      sat := ⟨blocksSatP, by
        sig_pre [Spec.Gcm.decryptBlocksPrecomputedContract, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPrecomputedPre, X86_64.abi, X86_64.argRegs, blocksSatP, blocksSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact powersRepr_zero _
          | exact Region.disjoint_of_sep (by decide)⟩ }

end VG.Proof.AesGcm.X86_64
