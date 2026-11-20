module

public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Framework.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.RISCV64.ScrubProved
public import VerifiedGarbage.Impl.Cast5.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalVerified
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ScrubLocal

/-!
# CAST5 on RISC-V, without secret residue

The eleven CAST5 functions, each followed by `Impl.Scrub.RISCV64.scrubTail`
(`Impl.Cast5.RISCV64.Fn`, the functions as emitted), which clears the
caller-saved registers and the stack its frames used: none for key expansion and ECB, whose working space
is their caller's `scratch`, and the 128-byte frame of the modes, which holds
the chaining block. Their postconditions read the memory on return only
within the buffers (`RISCV64.Scrub.PostOut`): the schedule, the data and the
chaining block, as on x86-64 (`Proof/Cast5/X86_64/Scrub.lean`).
-/

@[expose] public section

namespace VG.Proof.Cast5.RISCV64.Scrub

open VG.RISCV64 VG.RISCV64.Scrub VG.Proof.Aes.ScrubLocal VG.Proof.Cast5.ScrubLocal

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (RISCV64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (RISCV64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract (RISCV64.abi.withConsts Impl.Cast5.keyConsts) stack)
      (Spec.Cast5.expandKeySig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [k, kl, sch, sc], _ =>
      simp only [Spec.Cast5.expandKeySig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show Spec.Cast5.scheduleAt m₂ sch = _
      rw [scheduleAt_of hb.2.1]
      exact h

theorem ecbOut (d : Spec.Cast5.Direction) (stack : Nat) :
    PostOut (Spec.Cast5.ecbContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) d stack)
      (Spec.Cast5.ecbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, dt, ln, sc], _ =>
      simp only [Spec.Cast5.ecbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key → Spec.Cast5.blocksAt m₂ dt _ = _
      intro key hk
      rw [blocksAt_of0 hb.2.1 (lenC ln 8)]
      exact h key hk

theorem cbcEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcEncryptChainedContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cbcDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cbcDecryptChainedContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cbcChainedSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cbcChainedSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Cast5.cbcBlocksAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [cbcBlocksAt_of0 hb.2.2 (lenC ln 8), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbEncryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbEncryptFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem cfbDecryptFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.cfbDecryptFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.cfbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.cfbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

theorem ofbFinalOut (stack : Nat) :
    PostOut (Spec.Cast5.ofbFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) stack)
      (Spec.Cast5.ofbFinalSig.retBits 64) :=
  postOut_of_local (ScrubAbi.consts _) fun vs m m₁ m₂ r hlen hb h => by
    match vs, hlen with
    | [sch, rd, iv, dt, ln], _ =>
      simp only [Spec.Cast5.ofbFinalSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hb
      show ∀ key, Spec.Cast5.KeySchedule m sch _ key →
        Spec.Aes.bytesAt m₂ dt _ = _ ∧ Spec.Aes.bytesAt m₂ iv 8 = _
      intro key hk
      rw [bytesAt_of0 hb.2.2 (len1C ln), bytesAt_of0 (n := 8) hb.2.1 (Nat.le_refl _)]
      exact h key hk

/-! ## The functions as emitted

Each theorem states that a function as emitted (`Impl.Cast5.RISCV64.Fn`) meets its
contract in constant time and returns without secret residue
(`VerifiedScrubbed`, by `RISCV64.Scrub.verifiedScrubbed`, or
`verifiedScrubbedSelT` for the selective cleanup, whose residue analysis the
kernel evaluates here): what its registration binds. -/

/-- `Spec.Cast5.expandKeyApi` as emitted (`Impl.Cast5.RISCV64.Fn.expandKey`) meets its contract
in constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.expandKey
      (Spec.Cast5.expandKeyContract (RISCV64.abi.withConsts Impl.Cast5.keyConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.expandKeyApi) (W := 0) (rb := 0)
    { code := Impl.Cast5.RISCV64.expandKey
      verified := Proof.Cast5.RISCV64.expandKey_verified }
    (expandKeyOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.ecbEncryptApi` as emitted (`Impl.Cast5.RISCV64.Fn.ecbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.ecbEncrypt
      (Spec.Cast5.ecbEncryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ecbEncryptApi) (W := 0) (rb := 0)
    { code := Impl.Cast5.RISCV64.ecbEncrypt
      verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.RISCV64.ecbEncrypt_verified }
    (ecbOut .encrypt _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.ecbDecryptApi` as emitted (`Impl.Cast5.RISCV64.Fn.ecbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.ecbDecrypt
      (Spec.Cast5.ecbDecryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts)) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ecbDecryptApi) (W := 0) (rb := 0)
    { code := Impl.Cast5.RISCV64.ecbDecrypt
      verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.RISCV64.ecbDecrypt_verified }
    (ecbOut .decrypt _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.cbcEncryptChainedApi` as emitted (`Impl.Cast5.RISCV64.Fn.cbcEncryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.cbcEncryptChained
      (Spec.Cast5.cbcEncryptChainedContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.cbcEncryptChainedApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.cbcEncryptChained
      verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.RISCV64.Modes.cbcEncryptChained_verified }
    (cbcEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.cbcDecryptChainedApi` as emitted (`Impl.Cast5.RISCV64.Fn.cbcDecryptChained`) meets its contract
in constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.cbcDecryptChained
      (Spec.Cast5.cbcDecryptChainedContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.cbcDecryptChainedApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.cbcDecryptChained
      verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.RISCV64.Modes.cbcDecryptChained_verified }
    (cbcDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.cfbEncryptApi` as emitted (`Impl.Cast5.RISCV64.Fn.cfbEncrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.cfbEncrypt
      (Spec.Cast5.cfbEncryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.cfbEncryptApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.cfbEncrypt
      verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.RISCV64.Modes.cfbEncrypt_verified }
    (cfbEncryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.cfbDecryptApi` as emitted (`Impl.Cast5.RISCV64.Fn.cfbDecrypt`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.cfbDecrypt
      (Spec.Cast5.cfbDecryptContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.cfbDecryptApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.cfbDecrypt
      verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.RISCV64.Modes.cfbDecrypt_verified }
    (cfbDecryptOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.cfbEncryptFinalApi` as emitted (`Impl.Cast5.RISCV64.Fn.cfbEncryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.cfbEncryptFinal
      (Spec.Cast5.cfbEncryptFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.cfbEncryptFinalApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.cfbEncryptFinal
      verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.RISCV64.Modes.cfbEncryptFinal_verified }
    (cfbEncryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.cfbDecryptFinalApi` as emitted (`Impl.Cast5.RISCV64.Fn.cfbDecryptFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.cfbDecryptFinal
      (Spec.Cast5.cfbDecryptFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.cfbDecryptFinalApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.cfbDecryptFinal
      verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.RISCV64.Modes.cfbDecryptFinal_verified }
    (cfbDecryptFinalOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.ofbApi` as emitted (`Impl.Cast5.RISCV64.Fn.ofb`) meets its contract
in constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.ofb
      (Spec.Cast5.ofbContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ofbApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.ofb
      verified := Proof.Cast5.ofb_keyed Proof.Cast5.RISCV64.Modes.ofb_verified }
    (ofbOut _) (by dsimp only; lit_decide)

/-- `Spec.Cast5.ofbFinalApi` as emitted (`Impl.Cast5.RISCV64.Fn.ofbFinal`) meets its contract
in constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed RISCV64.target Impl.Cast5.RISCV64.Fn.ofbFinal
      (Spec.Cast5.ofbFinalContract (RISCV64.abi.withConsts Impl.Cast5.ecbConsts) Proof.Cast5.RISCV64.Modes.frameBytes) 0 :=
  verifiedScrubbed (api := Spec.Cast5.ofbFinalApi) (W := 128) (rb := 0)
    { code := Impl.Cast5.RISCV64.ofbFinal
      verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.RISCV64.Modes.ofbFinal_verified }
    (ofbFinalOut _) (by dsimp only; lit_decide)

end VG.Proof.Cast5.RISCV64.Scrub
