module

public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.SignEntry
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Sign.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.VerifyEntry
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Verify.Inst
public import VerifiedGarbage.Proof.MlDsa.RISCV64.PreparedKey.Prepare
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on RISC-V: the entries of the kernels, with this library's kernels

`vg_mldsa*_sign` and `vg_mldsa*_verify` call `vg_mldsa*_sign_with_cache` and
`vg_mldsa*_verify_with_cache` (`Sign/Inst.lean`, `Verify/Inst.lean`), verified
with 1168 bytes of stack, in a frame of 16: so they are verified with 1184
(`sign44_verified`, `verify44_verified`, …).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.PreparedKey

open VG VG.RISCV64
open VG.Spec.MlDsa

/-- A state that satisfies `signContract`'s precondition. -/
def signSat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x8000 | .a2 => 0x9000 | .a3 => 0xA000 | .a4 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.skLen⟩, ⟨0x8000, 64⟩, ⟨0x9000, 32⟩]
  wr := [⟨0xA000, p.sigLen⟩, ⟨0x10000, scratchWords p * 8⟩]

theorem sign44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign44 (signContract mlDsa44 RISCV64.abi 1184) :=
  signEntry_verified (.inl rfl) Sign.withCache44_verified (by decide +kernel) _ false
    ⟨signSat mlDsa44, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

theorem sign65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign65 (signContract mlDsa65 RISCV64.abi 1184) :=
  signEntry_verified (.inr (.inl rfl)) Sign.withCache65_verified (by decide +kernel) _ false
    ⟨signSat mlDsa65, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

theorem sign87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Sign.sign87 (signContract mlDsa87 RISCV64.abi 1184) :=
  signEntry_verified (.inr (.inr rfl)) Sign.withCache87_verified (by decide +kernel) _ false
    ⟨signSat mlDsa87, by simp only [signEK, Bool.false_eq_true, ↓reduceIte]; sig_sat_check [signContract, signSig, RISCV64.abi, RISCV64.argRegs, signSat]⟩

/-- A state that satisfies `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 0x3000 | .a3 => 0x10000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩]
  wr := [⟨0x10000, scratchWords p * 8⟩]

theorem verify44_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify44 (verifyContract mlDsa44 RISCV64.abi 1184) :=
  verifyEntry_verified (.inl rfl) Verify.withCache44_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa44, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

theorem verify65_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify65 (verifyContract mlDsa65 RISCV64.abi 1184) :=
  verifyEntry_verified (.inr (.inl rfl)) Verify.withCache65_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa65, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

theorem verify87_verified :
    Verified RISCV64.target Impl.MlDsa.RISCV64.Verify.verify87 (verifyContract mlDsa87 RISCV64.abi 1184) :=
  verifyEntry_verified (.inr (.inr rfl)) Verify.withCache87_verified (by decide +kernel) _ false
    ⟨verifySat mlDsa87, by
      simp only [verifyEK, Bool.false_eq_true, ↓reduceIte]
      sig_sat_check [verifyContract, verifySig, RISCV64.abi, RISCV64.argRegs, verifySat]⟩

/-! ## Preparing keys -/

/-- A state that satisfies the precondition of preparing a key of `kl` bytes
into `ol`, with the buffer (`buf`) or without it. -/
def prepSat (kl ol : Nat) (buf : Bool) : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x4000 | .a2 => 0x10000 | .a3 => 0x11000 | _ => 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, kl⟩]
  wr := [⟨0x4000, ol⟩, ⟨0x10000, 1024⟩] ++ if buf then [⟨0x11000, 1072⟩] else []

theorem preparePublic44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa44)
      (preparePublicKeyContract mlDsa44 RISCV64.abi 1072) :=
  preparePublic_verified (.inl rfl)
    ⟨prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa44.pkLen (preparedPublicKeyBytes mlDsa44) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa44)
      (prepareSecretKeyContract mlDsa44 RISCV64.abi 1072) :=
  prepareSecret_verified (.inl rfl)
    ⟨prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa44.skLen (preparedSecretKeyBytes mlDsa44) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem preparePublic65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa65)
      (preparePublicKeyContract mlDsa65 RISCV64.abi 1072) :=
  preparePublic_verified (.inr (.inl rfl))
    ⟨prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa65.pkLen (preparedPublicKeyBytes mlDsa65) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa65)
      (prepareSecretKeyContract mlDsa65 RISCV64.abi 1072) :=
  prepareSecret_verified (.inr (.inl rfl))
    ⟨prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa65.skLen (preparedSecretKeyBytes mlDsa65) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem preparePublic87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic mlDsa87)
      (preparePublicKeyContract mlDsa87 RISCV64.abi 1072) :=
  preparePublic_verified (.inr (.inr rfl))
    ⟨prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87) true, by
      sig_sat_check [publicScratchContract, publicScratchSig, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa87.pkLen (preparedPublicKeyBytes mlDsa87) false, by
      sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

theorem prepareSecret87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret mlDsa87)
      (prepareSecretKeyContract mlDsa87 RISCV64.abi 1072) :=
  prepareSecret_verified (.inr (.inr rfl))
    ⟨prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87) true, by
      sig_sat_check [secretScratchContract, secretScratchSig, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs,
        prepSat]⟩
    ⟨prepSat mlDsa87.skLen (preparedSecretKeyBytes mlDsa87) false, by
      sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat]⟩

/-! ## Signing and verifying with a prepared key -/

/-- A prepared private key, at `0x4000` of some memory: the one `prepareSecret` writes from `prepSat`. -/
theorem secret_mem {p : Params}
    (hv : Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.prepareSecret p)
      (prepareSecretKeyContract p RISCV64.abi 1072))
    (hs : (prepareSecretKeyContract p RISCV64.abi 1072).pre (prepSat p.skLen (preparedSecretKeyBytes p) false)) :
    ∃ m, PreparedSecretKey p m 0x4000 := by
  obtain ⟨_, t, _, _, post⟩ := hv.1 _ hs
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs] at post
  exact ⟨t.mem, post.2⟩

/-- A prepared public key, at `0x4000` of some memory. -/
theorem public_mem {p : Params}
    (hv : Verified RISCV64.target (Impl.MlDsa.RISCV64.PreparedKey.preparePublic p)
      (preparePublicKeyContract p RISCV64.abi 1072))
    (hs : (preparePublicKeyContract p RISCV64.abi 1072).pre (prepSat p.pkLen (preparedPublicKeyBytes p) false)) :
    ∃ m, PreparedPublicKey p m 0x4000 := by
  obtain ⟨_, t, _, _, post⟩ := hv.1 _ hs
  sig_post [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs] at post
  exact ⟨t.mem, post.2⟩

/-- A state that satisfies `preparedSignContract`'s precondition, with the prepared key in `m`. -/
def psSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a2 => 0x10100 | .a3 => 0x11000 | .a4 => 0x20000 | _ => 0
  sp := 0x100000
  mem := m
  rd := [⟨0x4000, preparedSecretKeyBytes p⟩, ⟨0x10000, 64⟩, ⟨0x10100, 32⟩]
  wr := [⟨0x11000, p.sigLen⟩, ⟨0x20000, scratchWords p * 8⟩]

/-- A state that satisfies `preparedVerifyContract`'s precondition, with the prepared key in `m`. -/
def pvSat (p : Params) (m : Mem) : State where
  gpr r := match r with
    | .a0 => 0x4000 | .a1 => 0x10000 | .a2 => 0x11000 | .a3 => 0x20000 | _ => 0
  sp := 0x100000
  mem := m
  rd := [⟨0x4000, preparedPublicKeyBytes p⟩, ⟨0x10000, 64⟩, ⟨0x11000, p.sigLen⟩]
  wr := [⟨0x20000, scratchWords p * 8⟩]

theorem psSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedSecretKey p m 0x4000) : (signEK p true 1184).pre (psSat p m) := by
  simp only [signEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedSignContract, preparedSignSig, RISCV64.abi, RISCV64.argRegs, psSat]
    sig_and_intros
    all_goals first
      | exact hk
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem pvSat_pre {p : Params} (hp3 : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) {m : Mem}
    (hk : PreparedPublicKey p m 0x4000) : (verifyEK p true 1184).pre (pvSat p m) := by
  simp only [verifyEK, ↓reduceIte]
  rcases hp3 with rfl | rfl | rfl
  all_goals
    sig_pre [preparedVerifyContract, preparedVerifySig, RISCV64.abi, RISCV64.argRegs, pvSat]
    sig_and_intros
    all_goals first
      | exact hk
      | rfl
      | decide
      | exact Region.disjoint_of_sep (by decide)

theorem secret44_mem : ∃ m, PreparedSecretKey mlDsa44 m 0x4000 :=
  secret_mem prepareSecret44_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public44_mem : ∃ m, PreparedPublicKey mlDsa44 m 0x4000 :=
  public_mem preparePublic44_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign44E true) (signEK mlDsa44 true 1184) :=
  signEntry_verified (.inl rfl) Sign.withCache44_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret44_mem; exact ⟨psSat _ m, psSat_pre (.inl rfl) hm⟩)

theorem verifyPrepared44_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify44E true) (verifyEK mlDsa44 true 1184) :=
  verifyEntry_verified (.inl rfl) Verify.withCache44_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public44_mem; exact ⟨pvSat _ m, pvSat_pre (.inl rfl) hm⟩)

theorem secret65_mem : ∃ m, PreparedSecretKey mlDsa65 m 0x4000 :=
  secret_mem prepareSecret65_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public65_mem : ∃ m, PreparedPublicKey mlDsa65 m 0x4000 :=
  public_mem preparePublic65_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign65E true) (signEK mlDsa65 true 1184) :=
  signEntry_verified (.inr (.inl rfl)) Sign.withCache65_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret65_mem; exact ⟨psSat _ m, psSat_pre (.inr (.inl rfl)) hm⟩)

theorem verifyPrepared65_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify65E true) (verifyEK mlDsa65 true 1184) :=
  verifyEntry_verified (.inr (.inl rfl)) Verify.withCache65_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public65_mem; exact ⟨pvSat _ m, pvSat_pre (.inr (.inl rfl)) hm⟩)

theorem secret87_mem : ∃ m, PreparedSecretKey mlDsa87 m 0x4000 :=
  secret_mem prepareSecret87_verified (by
    sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem public87_mem : ∃ m, PreparedPublicKey mlDsa87 m 0x4000 :=
  public_mem preparePublic87_verified (by
    sig_sat_check [preparePublicKeyContract, preparePublicKeySig, RISCV64.abi, RISCV64.argRegs, prepSat])

theorem signPrepared87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Sign.sign87E true) (signEK mlDsa87 true 1184) :=
  signEntry_verified (.inr (.inr rfl)) Sign.withCache87_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := secret87_mem; exact ⟨psSat _ m, psSat_pre (.inr (.inr rfl)) hm⟩)

theorem verifyPrepared87_verified :
    Verified RISCV64.target (Impl.MlDsa.RISCV64.Verify.verify87E true) (verifyEK mlDsa87 true 1184) :=
  verifyEntry_verified (.inr (.inr rfl)) Verify.withCache87_verified (by decide +kernel) _ true
    (by obtain ⟨m, hm⟩ := public87_mem; exact ⟨pvSat _ m, pvSat_pre (.inr (.inr rfl)) hm⟩)

end VG.Proof.MlDsa.RISCV64.PreparedKey
