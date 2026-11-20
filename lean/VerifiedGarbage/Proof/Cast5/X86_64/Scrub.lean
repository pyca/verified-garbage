module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFn
public import VerifiedGarbage.Impl.Cast5.X86_64.Fn
public import VerifiedGarbage.Spec.Cast5.Contract
public import VerifiedGarbage.Spec.Cast5.Cbc
public import VerifiedGarbage.Spec.Cast5.Cfb
public import VerifiedGarbage.Spec.Cast5.Ofb
public import VerifiedGarbage.Spec.Cast5.CfbFinal
public import VerifiedGarbage.Spec.Cast5.OfbFinal
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubOr
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Cast5.Rounds
public import VerifiedGarbage.Proof.Cast5.CfbFinal
public import VerifiedGarbage.Proof.Cast5.X86_64.KeyVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.EcbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.FbVerified
public import VerifiedGarbage.Proof.Cast5.X86_64.FbFinalVerified
import VerifiedGarbage.Proof.Aes.X86_64.ModesScrub
import VerifiedGarbage.Proof.Aes.ScrubLocal
import VerifiedGarbage.Proof.Cast5.ScrubLocal

/-!
# CAST5 on x86-64, without secret residue

The eleven CAST5 functions, each followed by `Impl.Scrub.X86_64.scrub` with
every granule of its stack wiped (`X86_64.RScrub.withScrubAllM`): none for
key expansion and ECB, whose working space is their caller's `scratch`, and
the 240-byte frame of the modes, which no longer zero its scratch words
themselves (`withStackScratchWiped 240 .r9 0`). Their postconditions read the
memory on return only within the buffers (`X86_64.Scrub.PostOut`): the
schedule, the data and the chaining block.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86_64.Scrub

open VG.X86_64 VG.X86_64.Scrub VG.Proof.Aes.X86_64.ModesScrub VG.Proof.Aes.ScrubLocal VG.Proof.Cast5.ScrubLocal

/-- The data's length, under the tables' ABI. -/
theorem lenC (x : BitVec 64) (k : Nat) :
    ((ArgWord.int (X86_64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat * k ≤ x.toNat * k :=
  Nat.le_refl _

theorem len1C (x : BitVec 64) :
    ((ArgWord.int (X86_64.abi.withConsts Impl.Cast5.ecbConsts).ptrBits).ofRaw x).toNat ≤ x.toNat * Elem.u8.size :=
  Nat.le_of_eq (Nat.mul_one _).symm

/-! ## Postconditions -/

theorem expandKeyOut (stack : Nat) :
    PostOut (Spec.Cast5.expandKeyContract (X86_64.abi.withConsts Impl.Cast5.keyConsts) stack)
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
    PostOut (Spec.Cast5.ecbContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) d stack)
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
    PostOut (Spec.Cast5.cbcEncryptChainedContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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
    PostOut (Spec.Cast5.cbcDecryptChainedContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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
    PostOut (Spec.Cast5.cfbEncryptContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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
    PostOut (Spec.Cast5.cfbDecryptContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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
    PostOut (Spec.Cast5.ofbContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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
    PostOut (Spec.Cast5.cfbEncryptFinalContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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
    PostOut (Spec.Cast5.cfbDecryptFinalContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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
    PostOut (Spec.Cast5.ofbFinalContract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) stack)
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

/-! ## The registrations -/

open VG.X86_64.RScrub

/-! ## The functions as emitted -/

theorem expandKey_codeSp : (Impl.Cast5.X86_64.expandKey).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.expandKeyApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.expandKey`) meets its contract in
constant time and returns without secret residue. -/
theorem expandKey_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.expandKey (Spec.Cast5.expandKeyApi.contract (X86_64.abi.withConsts Impl.Cast5.keyConsts) 0) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.expandKeyApi)
    { code := Impl.Cast5.X86_64.expandKey
      stack := 0
      verified := Proof.Cast5.X86_64.expandKey_verified
      consts := Impl.Cast5.keyConsts
      spSafe := expandKey_codeSp }
    .sse (expandKeyOut _)

theorem expandKey_spSafe : Impl.Cast5.X86_64.Fn.expandKey.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe expandKey_codeSp

theorem ecbEncrypt_codeSp : (Impl.Cast5.X86_64.ecbEncrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.ecbEncryptApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.ecbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.ecbEncrypt (Spec.Cast5.ecbEncryptApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 0) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ecbEncryptApi)
    { code := Impl.Cast5.X86_64.ecbEncrypt
      stack := 0
      verified := Proof.Cast5.ecbEncrypt_keyed Proof.Cast5.X86_64.ecbEncrypt_verified
      consts := Impl.Cast5.ecbConsts
      spSafe := ecbEncrypt_codeSp }
    .sse (ecbOut .encrypt _)

theorem ecbEncrypt_spSafe : Impl.Cast5.X86_64.Fn.ecbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbEncrypt_codeSp

theorem ecbDecrypt_codeSp : (Impl.Cast5.X86_64.ecbDecrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.ecbDecryptApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.ecbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem ecbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.ecbDecrypt (Spec.Cast5.ecbDecryptApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 0) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ecbDecryptApi)
    { code := Impl.Cast5.X86_64.ecbDecrypt
      stack := 0
      verified := Proof.Cast5.ecbDecrypt_keyed Proof.Cast5.X86_64.ecbDecrypt_verified
      consts := Impl.Cast5.ecbConsts
      spSafe := ecbDecrypt_codeSp }
    .sse (ecbOut .decrypt _)

theorem ecbDecrypt_spSafe : Impl.Cast5.X86_64.Fn.ecbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ecbDecrypt_codeSp

theorem cbcEncryptChained_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcEncryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.cbcEncryptChainedApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.cbcEncryptChained`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcEncryptChained_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.cbcEncryptChained (Spec.Cast5.cbcEncryptChainedApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cbcEncryptChainedApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcEncryptChained
      stack := 240
      verified := Proof.Cast5.cbcEncryptChained_keyed Proof.Cast5.X86_64.cbcEncryptChained_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := cbcEncryptChained_codeSp }
    .sse (cbcEncryptOut _)

theorem cbcEncryptChained_spSafe : Impl.Cast5.X86_64.Fn.cbcEncryptChained.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcEncryptChained_codeSp

theorem cbcDecryptChained_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcDecryptChained).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.cbcDecryptChainedApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.cbcDecryptChained`) meets its contract in
constant time and returns without secret residue. -/
theorem cbcDecryptChained_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.cbcDecryptChained (Spec.Cast5.cbcDecryptChainedApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cbcDecryptChainedApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cbcDecryptChained
      stack := 240
      verified := Proof.Cast5.cbcDecryptChained_keyed Proof.Cast5.X86_64.cbcDecryptChained_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := cbcDecryptChained_codeSp }
    .sse (cbcDecryptOut _)

theorem cbcDecryptChained_spSafe : Impl.Cast5.X86_64.Fn.cbcDecryptChained.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cbcDecryptChained_codeSp

theorem cfbEncrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.cfbEncryptApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.cfbEncrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncrypt_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.cfbEncrypt (Spec.Cast5.cfbEncryptApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbEncryptApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncrypt
      stack := 240
      verified := Proof.Cast5.cfbEncrypt_keyed Proof.Cast5.X86_64.cfbEncrypt_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := cfbEncrypt_codeSp }
    .sse (cfbEncryptOut _)

theorem cfbEncrypt_spSafe : Impl.Cast5.X86_64.Fn.cfbEncrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncrypt_codeSp

theorem cfbDecrypt_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecrypt).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.cfbDecryptApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.cfbDecrypt`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecrypt_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.cfbDecrypt (Spec.Cast5.cfbDecryptApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbDecryptApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecrypt
      stack := 240
      verified := Proof.Cast5.cfbDecrypt_keyed Proof.Cast5.X86_64.cfbDecrypt_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := cfbDecrypt_codeSp }
    .sse (cfbDecryptOut _)

theorem cfbDecrypt_spSafe : Impl.Cast5.X86_64.Fn.cfbDecrypt.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecrypt_codeSp

theorem cfbEncryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.cfbEncryptFinalApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.cfbEncryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbEncryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.cfbEncryptFinal (Spec.Cast5.cfbEncryptFinalApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbEncryptFinalApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbEncryptFinal
      stack := 240
      verified := Proof.Cast5.cfbEncryptFinal_keyed Proof.Cast5.X86_64.cfbEncryptFinal_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := cfbEncryptFinal_codeSp }
    .sse (cfbEncryptFinalOut _)

theorem cfbEncryptFinal_spSafe : Impl.Cast5.X86_64.Fn.cfbEncryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbEncryptFinal_codeSp

theorem cfbDecryptFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecryptFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.cfbDecryptFinalApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.cfbDecryptFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem cfbDecryptFinal_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.cfbDecryptFinal (Spec.Cast5.cfbDecryptFinalApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.cfbDecryptFinalApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.cfbDecryptFinal
      stack := 240
      verified := Proof.Cast5.cfbDecryptFinal_keyed Proof.Cast5.X86_64.cfbDecryptFinal_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := cfbDecryptFinal_codeSp }
    .sse (cfbDecryptFinalOut _)

theorem cfbDecryptFinal_spSafe : Impl.Cast5.X86_64.Fn.cfbDecryptFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe cfbDecryptFinal_codeSp

theorem ofb_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofb).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.ofbApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.ofb`) meets its contract in
constant time and returns without secret residue. -/
theorem ofb_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.ofb (Spec.Cast5.ofbApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ofbApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofb
      stack := 240
      verified := Proof.Cast5.ofb_keyed Proof.Cast5.X86_64.ofb_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := ofb_codeSp }
    .sse (ofbOut _)

theorem ofb_spSafe : Impl.Cast5.X86_64.Fn.ofb.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofb_codeSp

theorem ofbFinal_codeSp : (Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofbFinal).all (fun i => !VG.X86_64.isa.writesSp i) = true := by
  sp_safe

/-- `Spec.Cast5.ofbFinalApi`'s function as emitted (`Impl.Cast5.X86_64.Fn.ofbFinal`) meets its contract in
constant time and returns without secret residue. -/
theorem ofbFinal_scrubbed :
    VerifiedScrubbed target Impl.Cast5.X86_64.Fn.ofbFinal (Spec.Cast5.ofbFinalApi.contract (X86_64.abi.withConsts Impl.Cast5.ecbConsts) 240) 0 :=
  verifiedScrubbedAll (api := Spec.Cast5.ofbFinalApi)
    { code := Impl.StackScratch.X86_64.withStackScratchWiped 240 .r9 0 Impl.Cast5.X86_64.ofbFinal
      stack := 240
      verified := Proof.Cast5.ofbFinal_keyed Proof.Cast5.X86_64.ofbFinal_framed
      consts := Impl.Cast5.ecbConsts
      spSafe := ofbFinal_codeSp }
    .sse (ofbFinalOut _)

theorem ofbFinal_spSafe : Impl.Cast5.X86_64.Fn.ofbFinal.all (fun i => !VG.X86_64.isa.writesSp i) = true :=
  scrubKs_spSafe ofbFinal_codeSp
end VG.Proof.Cast5.X86_64.Scrub
