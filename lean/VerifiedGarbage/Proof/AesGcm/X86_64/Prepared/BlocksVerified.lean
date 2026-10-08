import VerifiedGarbage.Proof.AesGcm.X86_64.BlocksVerifiedP
import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context

/-! # Whole-block functions with prepared contexts -/
namespace VG.Proof.AesGcm.X86_64
open VG VG.X86_64 VG.Impl.AesGcm.X86_64
open Gcm.X86_64.Stitch (CtxMode)

theorem preparedPowersRepr_zero (p : Addr) : Spec.Gcm.PreparedPowersRepr (fun _ => 0) p := by
  intro k hk
  have z : ∀ q : Addr, Spec.Gcm.blockAt (fun _ => 0) q = 0 := fun q => by
    simp [Spec.Gcm.blockAt, Spec.Aes.bytesAt, Spec.Gcm.ofBytes]; decide
  have w : ∀ q : Addr, Mem.readW (fun _ => 0) q 128 = 0 := fun q => by
    simp [Mem.readW, Mem.read]
  simp only [Spec.Gcm.ctxH, z, hpow_zero_succ, w]
  constructor <;> decide

theorem encryptBlocksPrepared_verified (v : GcmImpl) (st : Option (StitchCode CtxMode.prepared)) :
    Verified X86_64.target (Blocks.encrypt v.callees.ctr v.callees.gh (st.map (·.enc)))
      (Spec.Gcm.encryptBlocksPreparedContract X86_64.abi 8) :=
  Verified.of_correct (encryptBlocksM_correct v st) (Blocks.encrypt_ct v st)
    { pre := by
        sig_implies_pre [Spec.Gcm.encryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.encryptBlocksX86_64M, Proof.AesGcm.blocksPreM,
          CtxMode.prepared, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
          Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
          List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.encryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.encryptBlocksX86_64M,
          Proof.AesGcm.encryptBlocksX86_64, X86_64.abi, Proof.AesGcm.arg, X86_64.stackArg,
          X86_64.stackArgAddr, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.encryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Proof.AesGcm.encryptBlocksX86_64M, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, X86_64.argRegs]
      sat := ⟨blocksSatP, by
        sig_pre [Spec.Gcm.encryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPreparedPre, X86_64.abi, X86_64.argRegs, blocksSatP, blocksSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact preparedPowersRepr_zero _
          | exact Region.disjoint_of_sep (by decide)⟩ }

theorem decryptBlocksPrepared_verified (v : GcmImpl) (st : Option (StitchCode CtxMode.prepared)) :
    Verified X86_64.target (Blocks.decrypt v.callees.ctr v.callees.gh (st.map (·.dec)))
      (Spec.Gcm.decryptBlocksPreparedContract X86_64.abi 8) :=
  Verified.of_correct (decryptBlocksM_correct v st) (Blocks.decrypt_ct v st)
    { pre := by
        sig_implies_pre [Spec.Gcm.decryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.decryptBlocksX86_64M, Proof.AesGcm.blocksPreM,
          CtxMode.prepared, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg, Proof.AesGcm.args,
          Proof.AesGcm.stk, Proof.AesGcm.ret, Proof.AesGcm.rounds, X86_64.stackArg, X86_64.stackArgAddr,
          List.getD, List.range, List.range.loop, VG.X86_64.below, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Gcm.decryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPreparedPre, Proof.AesGcm.decryptBlocksX86_64M,
          Proof.AesGcm.decryptBlocksX86_64, X86_64.abi, Proof.AesGcm.arg, X86_64.stackArg,
          X86_64.stackArgAddr, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Gcm.decryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Proof.AesGcm.decryptBlocksX86_64M, Proof.AesGcm.blocksPub, X86_64.abi, Proof.AesGcm.arg,
          X86_64.stackArg, X86_64.stackArgAddr, List.getD, List.range, List.range.loop, X86_64.argRegs]
      sat := ⟨blocksSatP, by
        sig_pre [Spec.Gcm.decryptBlocksPreparedContract, Spec.Gcm.cryptBlocksPreparedSig, Spec.Gcm.cryptBlocksPrecomputedSig,
          Spec.Gcm.cryptBlocksPreparedPre, X86_64.abi, X86_64.argRegs, blocksSatP, blocksSat]
        sig_and_intros
        all_goals first
          | rfl
          | decide
          | exact preparedPowersRepr_zero _
          | exact Region.disjoint_of_sep (by decide)⟩ }

end VG.Proof.AesGcm.X86_64
