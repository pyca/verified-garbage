module

public import VerifiedGarbage.Proof.Gcm.PreparedPowers
public import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
public import VerifiedGarbage.Proof.AesGcm.X86_64.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Verified
public import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
public import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
public import VerifiedGarbage.Proof.AesGcm.Rounds
public import VerifiedGarbage.Proof.AesGcm.RoundsTo
public import VerifiedGarbage.Proof.Framework.X86_64.WidenArray
public import VerifiedGarbage.Proof.AesGcm.Flag
public import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.SigEval
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Gcm.X86_64.Flag

/-!
# AES-GCM on x86-64 against the flagged prepared contracts

Every implementation of the functions on the prepared key context, against
the contracts of `Proof/AesGcm/Flag.lean`:

* an implementation that reads no powers runs its code on the key context,
  whose proof moves to the 1088-byte context (`Verified.widenFirstArray`)
  and leaks the flag's (`Verified.with_leak`, `Verified.leak_mono`);
* one that reads them runs, by the flag (`onFlag`), its code on the prepared
  powers if they are there, and its code on the key context if not
  (`Verified.of_onFlagCtx`).
-/

@[expose] public section

-- separate module: what only the registration of the flagged contracts needs

namespace VG.Proof.AesGcm.X86_64.Flag

open VG VG.X86_64

/-! ## `seal` -/

def sealSatF : State :=
  { sealFrameSat with rd := [⟨0x1000, 1088⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩] }

theorem seal_satF : ∃ s, (Spec.Gcm.sealPreparedSig.contract abi (Spec.Gcm.sealPreparedPre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
    X86_64.argRegs, sealSatF, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       refine preparedPowersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)


theorem seal_satpow : ∃ s, (Spec.Gcm.sealPreparedSig.contract abi (Proof.Gcm.sealPowersPre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [Spec.Gcm.sealPreparedSig, Proof.Gcm.sealPowersPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
    X86_64.argRegs, sealSatF, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)


theorem seal_satpow16 : ∃ s, (Spec.Gcm.sealPreparedSig.contract abi (Spec.Gcm.sealPrepared16Pre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPrepared16Pre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
    X86_64.argRegs, sealSatF, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       refine preparedPowersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)


theorem seal_satbase : ∃ s, (Spec.Gcm.sealPreparedSig.contract abi (Spec.Gcm.sealPre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [Spec.Gcm.sealPreparedSig, Spec.Gcm.sealPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
    X86_64.argRegs, sealSatF, sealFrameSat, sealSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


/-- From the key context. -/
theorem seal_of_base {c : Prog isa}
    (h : Verified target c (Proof.AesGcm.sealRoundsContract abi 2624)) :
    Verified target c (AesGcm.Flag.sealRoundsContract abi 2624) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ h => h.1) seal_satF) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem seal_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealPreparedRoundsContract abi 2624))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealRoundsContract abi 2624)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.sealRoundsContract abi 2624) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ => rfl)
    seal_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem seal_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealPrepared16RoundsContract abi 2624))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealRoundsContract abi 2624)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.sealRoundsContract abi 2624) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, preparedPowers16Repr_of (h.2.resolve_left hf)⟩)
    (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ => rfl)
    seal_satF

/-! ## `open` -/

def openSatF : State :=
  { openFrameSat with rd := [⟨0x1000, 1088⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩] }

theorem open_satF : ∃ s, (Spec.Gcm.openPreparedSig.contract abi (Spec.Gcm.openPreparedPre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [Spec.Gcm.openPreparedSig, Spec.Gcm.openPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
    X86_64.argRegs, openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem open_satpow : ∃ s, (Spec.Gcm.openPreparedSig.contract abi (Proof.Gcm.openPowersPre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [Spec.Gcm.openPreparedSig, Proof.Gcm.openPowersPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
    X86_64.argRegs, openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem open_satpow16 : ∃ s, (Spec.Gcm.openPreparedSig.contract abi (Spec.Gcm.openPrepared16Pre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [Spec.Gcm.openPreparedSig, Spec.Gcm.openPrepared16Pre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
    X86_64.argRegs, openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem open_satbase : ∃ s, (Spec.Gcm.openPreparedSig.contract abi (Spec.Gcm.openPre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [Spec.Gcm.openPreparedSig, Spec.Gcm.openPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
    X86_64.argRegs, openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


/-- From the key context. -/
theorem open_of_base {c : Prog isa}
    (h : Verified target c (Proof.AesGcm.openRoundsContract abi 2632)) :
    Verified target c (AesGcm.Flag.openRoundsContract abi 2632) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ h => h.1) open_satF) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem open_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openPreparedRoundsContract abi 2632))
    (h₂ : Verified target c₂ (Proof.AesGcm.openRoundsContract abi 2632)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openRoundsContract abi 2632) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    open_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem open_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openPrepared16RoundsContract abi 2632))
    (h₂ : Verified target c₂ (Proof.AesGcm.openRoundsContract abi 2632)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openRoundsContract abi 2632) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, preparedPowers16Repr_of (h.2.resolve_left hf)⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    open_satF

/-! ## `streamEncrypt` -/

def crSatF : State := { crFrameSat with rd := [⟨0x1000, 1088⟩, ⟨0x8008, 8⟩] }

theorem streamEncrypt_satF : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Spec.Gcm.streamCryptPreparedPre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamEncrypt_satpow : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Proof.Gcm.streamCryptPowersPre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Proof.Gcm.streamCryptPowersPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamEncrypt_satpow16 : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Spec.Gcm.streamCryptPrepared16Pre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamEncrypt_satbase : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Spec.Gcm.streamTextPre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamTextPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


/-- From the key context. -/
theorem streamEncrypt_of_base {c : Prog isa}
    (h : Verified target c (Proof.AesGcm.streamEncryptRoundsContract abi 2608)) :
    Verified target c (AesGcm.Flag.streamEncryptRoundsContract abi 2608) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => h.1) streamEncrypt_satF) (fun _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem streamEncrypt_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamEncryptPreparedRoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamEncryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.streamEncryptRoundsContract abi 2608) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamEncrypt_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem streamEncrypt_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamEncryptPrepared16RoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamEncryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.streamEncryptRoundsContract abi 2608) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, preparedPowers16Repr_of (h.2.resolve_left hf)⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamEncrypt_satF

/-! ## `streamDecrypt` -/

theorem streamDecrypt_satF : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Spec.Gcm.streamCryptPreparedPre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamDecrypt_satpow : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Proof.Gcm.streamCryptPowersPre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Proof.Gcm.streamCryptPowersPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamDecrypt_satpow16 : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Spec.Gcm.streamCryptPrepared16Pre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamCryptPrepared16Pre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamDecrypt_satbase : ∃ s, (Spec.Gcm.streamCryptPreparedSig.contract abi (Spec.Gcm.streamTextPre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [Spec.Gcm.streamCryptPreparedSig, Spec.Gcm.streamTextPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


/-- From the key context. -/
theorem streamDecrypt_of_base {c : Prog isa}
    (h : Verified target c (Proof.AesGcm.streamDecryptRoundsContract abi 2608)) :
    Verified target c (AesGcm.Flag.streamDecryptRoundsContract abi 2608) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => h.1) streamDecrypt_satF) (fun _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem streamDecrypt_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamDecryptPreparedRoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamDecryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.streamDecryptRoundsContract abi 2608) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamDecrypt_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem streamDecrypt_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamDecryptPrepared16RoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamDecryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.streamDecryptRoundsContract abi 2608) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, preparedPowers16Repr_of (h.2.resolve_left hf)⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamDecrypt_satF

/-! ## `sealGather` -/

def gatherSatF : State :=
  { Gather.gatherFrameSat with rd := [⟨0x1000, 1088⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 40⟩] }

theorem sealGather_satF : ∃ s, (Spec.Gcm.sealGatherPreparedSig.contract abi (Spec.Gcm.sealGatherPreparedPre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [Spec.Gcm.sealGatherPreparedSig, Spec.Gcm.sealGatherPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, gatherSatF, Gather.gatherFrameSat, Gather.gatherSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ hi => by simp only [Gather.ctx_low hi, ite_false])


theorem sealGather_satpow : ∃ s, (Spec.Gcm.sealGatherPreparedSig.contract abi (Proof.Gcm.sealGatherPowersPre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [Spec.Gcm.sealGatherPreparedSig, Proof.Gcm.sealGatherPowersPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, gatherSatF, Gather.gatherFrameSat, Gather.gatherSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ hi => by simp only [Gather.ctx_low hi, ite_false])


theorem sealGather_satpow16 : ∃ s, (Spec.Gcm.sealGatherPreparedSig.contract abi (Spec.Gcm.sealGatherPrepared16Pre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [Spec.Gcm.sealGatherPreparedSig, Spec.Gcm.sealGatherPrepared16Pre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, gatherSatF, Gather.gatherFrameSat, Gather.gatherSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ hi => by simp only [Gather.ctx_low hi, ite_false])


theorem sealGather_satbase : ∃ s, (Spec.Gcm.sealGatherPreparedSig.contract abi (Spec.Gcm.sealGatherPre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [Spec.Gcm.sealGatherPreparedSig, Spec.Gcm.sealGatherPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, gatherSatF, Gather.gatherFrameSat, Gather.gatherSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


/-- From the key context. -/
theorem sealGather_of_base {c : Prog isa}
    (h : Verified target c (Proof.AesGcm.sealGatherRoundsContract abi 5128)) :
    Verified target c (AesGcm.Flag.sealGatherRoundsContract abi 5128) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) sealGather_satF) (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem sealGather_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealGatherPreparedRoundsContract abi 5128))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealGatherRoundsContract abi 5128)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.sealGatherRoundsContract abi 5128) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    sealGather_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem sealGather_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealGatherPrepared16RoundsContract abi 5128))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealGatherRoundsContract abi 5128)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.sealGatherRoundsContract abi 5128) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, preparedPowers16Repr_of (h.2.2.resolve_left hf)⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    sealGather_satF

/-! ## `openTo` -/

def toSatF : State :=
  { OpenTo.toSat with rd := [⟨0x1000, 1088⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩] }

theorem openTo_satF : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Spec.Gcm.openToPreparedPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Proof.Gcm.openToPowersPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Proof.Gcm.openToPowersPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow16 : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Spec.Gcm.openToPrepared16Pre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPrepared16Pre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satbase : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Spec.Gcm.openToPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


/-- From the key context. -/
theorem openTo_of_base {c : Prog isa}
    (h : Verified target c (Proof.AesGcm.openToRoundsContract abi 2728)) :
    Verified target c (AesGcm.Flag.openToRoundsContract abi 2728) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) openTo_satF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem openTo_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPreparedRoundsContract abi 2728))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2728)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2728) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem openTo_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPrepared16RoundsContract abi 2728))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2728)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2728) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, preparedPowers16Repr_of (h.2.2.resolve_left hf)⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF

theorem openTo_satF2776 : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Spec.Gcm.openToPreparedPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPreparedPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow2776 : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Proof.Gcm.openToPowersPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Proof.Gcm.openToPowersPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow162776 : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Spec.Gcm.openToPrepared16Pre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPrepared16Pre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satbase2776 : ∃ s, (Spec.Gcm.openToPreparedSig.contract abi (Spec.Gcm.openToPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [Spec.Gcm.openToPreparedSig, Spec.Gcm.openToPre, Spec.Gcm.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


/-- `open_to` on the key context, with the larger stack of the prepared
code that splits. -/
theorem openTo_satK2776 : ∃ s, (Proof.AesGcm.openToRoundsContract abi 2776).pre s := by
  sig_implies_sat [Proof.AesGcm.openToRoundsContract, Spec.Gcm.openToSig, Spec.Gcm.openToPre, X86_64.abi,
    X86_64.argRegs, OpenTo.stackArgs_six, List.append_eq] [OpenTo.toSat, stackArg, stackArgAddr, Mem.readW,
    Mem.read] using OpenTo.toSat

/-- From the key context. -/
theorem openTo_of_base2776 {c : Prog isa}
    (h : Verified target c (Proof.AesGcm.openToRoundsContract abi 2776)) :
    Verified target c (AesGcm.Flag.openToRoundsContract abi 2776) :=
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) openTo_satF2776) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem openTo_onFlag2776 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPreparedRoundsContract abi 2776))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2776)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2776) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow2776)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase2776)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF2776

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem openTo_onFlag162776 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPrepared16RoundsContract abi 2776))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2776)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2776) :=
  Verified.of_onFlagCtx (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 136) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow162776)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase2776)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, preparedPowers16Repr_of (h.2.2.resolve_left hf)⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF2776

/-- By the flag: `c₁` on a context whose powers are present, `c₂` on the key
context. -/
theorem openTo_onFlagF {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (AesGcm.Flag.openToFlaggedRoundsContract abi 2728))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2728)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2728) :=
  Verified.of_onFlagCtx (by decide) h₁
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, hf, h.2.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF

/-- By the flag: `c₁` on a context whose powers are present, `c₂` on the key
context, with the stack of the code that splits. -/
theorem openTo_onFlagF2776 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (AesGcm.Flag.openToFlaggedRoundsContract abi 2776))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2776)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2776) :=
  Verified.of_onFlagCtx (by decide) h₁
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 136) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase2776)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, hf, h.2.2.resolve_left hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF2776

end VG.Proof.AesGcm.X86_64.Flag
