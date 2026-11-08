module

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
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
public import VerifiedGarbage.Impl.Gcm.X86_64.Flag
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Frame
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Verified
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Gather.Verified
meta import VerifiedGarbage.Proof.AesGcm.X86_64.OpenTo.Verified
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Prepared.Verified
meta import VerifiedGarbage.Proof.AesGcm.ScratchPrepared
meta import VerifiedGarbage.Proof.AesGcm.Rounds
meta import VerifiedGarbage.Proof.AesGcm.RoundsTo
meta import VerifiedGarbage.Proof.Framework.X86_64.WidenArray
meta import VerifiedGarbage.Proof.AesGcm.Flag
meta import VerifiedGarbage.Proof.Framework.X86_64.FlagBranch
meta import VerifiedGarbage.Proof.Framework.Sig
meta import VerifiedGarbage.Proof.Framework.SigEval
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCT
meta import VerifiedGarbage.Impl.Gcm.X86_64.Flag

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

theorem seal_satF : ∃ s, (AesGcm.Flag.sealSig.contract abi (AesGcm.Flag.sealPre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealSig, AesGcm.Flag.sealPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
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


theorem seal_satpow : ∃ s, (AesGcm.Flag.sealSig.contract abi (Spec.Gcm.sealPreparedPre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealSig, Spec.Gcm.sealPreparedPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
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


theorem seal_satpow16 : ∃ s, (AesGcm.Flag.sealSig.contract abi (Spec.Gcm.sealPrepared16Pre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealSig, Spec.Gcm.sealPrepared16Pre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
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


theorem seal_satbase : ∃ s, (AesGcm.Flag.sealSig.contract abi (Spec.Gcm.sealPre 64)
    (Proof.AesGcm.sealRoundsPost 64) true 2624 none).pre s := by
  refine ⟨sealSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealSig, Spec.Gcm.sealPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealRoundsPost, X86_64.abi,
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

theorem open_satF : ∃ s, (AesGcm.Flag.openSig.contract abi (AesGcm.Flag.openPre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [AesGcm.Flag.openSig, AesGcm.Flag.openPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
    X86_64.argRegs, openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem open_satpow : ∃ s, (AesGcm.Flag.openSig.contract abi (Spec.Gcm.openPreparedPre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [AesGcm.Flag.openSig, Spec.Gcm.openPreparedPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
    X86_64.argRegs, openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem open_satpow16 : ∃ s, (AesGcm.Flag.openSig.contract abi (Spec.Gcm.openPrepared16Pre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [AesGcm.Flag.openSig, Spec.Gcm.openPrepared16Pre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
    X86_64.argRegs, openSatF, openFrameSat, openSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem open_satbase : ∃ s, (AesGcm.Flag.openSig.contract abi (Spec.Gcm.openPre 64)
    (Proof.AesGcm.openRoundsPost 64) true 2632 none).pre s := by
  refine ⟨openSatF, ?_⟩
  sig_pre [AesGcm.Flag.openSig, Spec.Gcm.openPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openRoundsPost, X86_64.abi,
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

theorem streamEncrypt_satF : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (AesGcm.Flag.streamCryptPre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, AesGcm.Flag.streamCryptPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamEncrypt_satpow : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (Spec.Gcm.streamCryptPreparedPre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, Spec.Gcm.streamCryptPreparedPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamEncrypt_satpow16 : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (Spec.Gcm.streamCryptPrepared16Pre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, Spec.Gcm.streamCryptPrepared16Pre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamEncrypt_satbase : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (Spec.Gcm.streamTextPre 64)
    (Proof.AesGcm.streamEncryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, Spec.Gcm.streamTextPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamEncryptRoundsPost, X86_64.abi,
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

theorem streamDecrypt_satF : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (AesGcm.Flag.streamCryptPre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, AesGcm.Flag.streamCryptPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamDecrypt_satpow : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (Spec.Gcm.streamCryptPreparedPre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, Spec.Gcm.streamCryptPreparedPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamDecrypt_satpow16 : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (Spec.Gcm.streamCryptPrepared16Pre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, Spec.Gcm.streamCryptPrepared16Pre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
    X86_64.argRegs, crSatF, crFrameSat, crSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ _ => rfl)


theorem streamDecrypt_satbase : ∃ s, (AesGcm.Flag.streamCryptSig.contract abi (Spec.Gcm.streamTextPre 64)
    (Proof.AesGcm.streamDecryptRoundsPost 64) true 2608 none).pre s := by
  refine ⟨crSatF, ?_⟩
  sig_pre [AesGcm.Flag.streamCryptSig, Spec.Gcm.streamTextPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.streamDecryptRoundsPost, X86_64.abi,
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

theorem sealGather_satF : ∃ s, (AesGcm.Flag.sealGatherSig.contract abi (AesGcm.Flag.sealGatherPre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealGatherSig, AesGcm.Flag.sealGatherPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, gatherSatF, Gather.gatherFrameSat, Gather.gatherSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact preparedPowersRepr_of_zero fun _ hi => by simp only [Gather.ctx_low hi, ite_false])


theorem sealGather_satpow : ∃ s, (AesGcm.Flag.sealGatherSig.contract abi (Spec.Gcm.sealGatherPreparedPre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealGatherSig, Spec.Gcm.sealGatherPreparedPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, gatherSatF, Gather.gatherFrameSat, Gather.gatherSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact preparedPowersRepr_of_zero fun _ hi => by simp only [Gather.ctx_low hi, ite_false])


theorem sealGather_satpow16 : ∃ s, (AesGcm.Flag.sealGatherSig.contract abi (Spec.Gcm.sealGatherPrepared16Pre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealGatherSig, Spec.Gcm.sealGatherPrepared16Pre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, gatherSatF, Gather.gatherFrameSat, Gather.gatherSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact preparedPowersRepr_of_zero fun _ hi => by simp only [Gather.ctx_low hi, ite_false])


theorem sealGather_satbase : ∃ s, (AesGcm.Flag.sealGatherSig.contract abi (Spec.Gcm.sealGatherPre 64)
    (Proof.AesGcm.sealGatherRoundsPost 64) true 5128 none).pre s := by
  refine ⟨gatherSatF, ?_⟩
  sig_pre [AesGcm.Flag.sealGatherSig, Spec.Gcm.sealGatherPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.sealGatherRoundsPost, Gather.stackArgs_five, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
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

theorem openTo_satF : ∃ s, (AesGcm.Flag.openToSig.contract abi (AesGcm.Flag.openToPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, AesGcm.Flag.openToPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow : ∃ s, (AesGcm.Flag.openToSig.contract abi (Spec.Gcm.openToPreparedPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, Spec.Gcm.openToPreparedPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow16 : ∃ s, (AesGcm.Flag.openToSig.contract abi (Spec.Gcm.openToPrepared16Pre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, Spec.Gcm.openToPrepared16Pre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satbase : ∃ s, (AesGcm.Flag.openToSig.contract abi (Spec.Gcm.openToPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2728 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, Spec.Gcm.openToPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
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

theorem openTo_satF2776 : ∃ s, (AesGcm.Flag.openToSig.contract abi (AesGcm.Flag.openToPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, AesGcm.Flag.openToPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine Or.inr ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow2776 : ∃ s, (AesGcm.Flag.openToSig.contract abi (Spec.Gcm.openToPreparedPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, Spec.Gcm.openToPreparedPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satpow162776 : ∃ s, (AesGcm.Flag.openToSig.contract abi (Spec.Gcm.openToPrepared16Pre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, Spec.Gcm.openToPrepared16Pre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)
    | (refine preparedPowers16Repr_of ?_
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])


theorem openTo_satbase2776 : ∃ s, (AesGcm.Flag.openToSig.contract abi (Spec.Gcm.openToPre 64)
    (Proof.AesGcm.openToRoundsPost 64) true 2776 none).pre s := by
  refine ⟨toSatF, ?_⟩
  sig_pre [AesGcm.Flag.openToSig, Spec.Gcm.openToPre, AesGcm.Flag.PreparedRepr, Proof.AesGcm.openToRoundsPost, OpenTo.stackArgs_six, List.append_eq, stackArg, stackArgAddr, Mem.readW, Mem.read, X86_64.abi,
    X86_64.argRegs, toSatF, OpenTo.toSat]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)


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

/-! ## `prepare` -/

/-- A state meeting the flagged `prepareContract`'s precondition. -/
def prepareSatF : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 1088⟩]

theorem prepare_satF : ∃ s, (AesGcm.Flag.prepareContract abi).pre s := by
  refine ⟨prepareSatF, ?_⟩
  sig_pre [AesGcm.Flag.prepareContract, AesGcm.Flag.prepareSig, X86_64.abi, X86_64.argRegs, prepareSatF]
  sig_and_intros
  all_goals first
    | rfl
    | decide
    | exact Region.disjoint_of_sep (by decide)

/-- From a `prepare` that writes the powers. -/
theorem prepare_of_powers {c : Prog isa}
    (h : Verified target c (Spec.Gcm.prepareContract abi)) :
    Verified target c (AesGcm.Flag.prepareContract abi) :=
  Verified.post_mono
    (VG.X86_64.Verified.widenFirstArrayW (n := 128) (n' := 136) (by decide) h
      (fun _ _ h => h) prepare_satF)
    (fun _ _ _ _ ⟨hb, hp⟩ => ⟨hb, Or.inr hp⟩)

/-- `vg_aes_gcm_prepare`'s flagged contract, on the registers. -/
def absentX86_64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 1088⟩] ∧ (s.gpr .rdi).toNat + 1088 ≤ 2 ^ 64 ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 1088⟩
  post s s' := Spec.Aes.bytesAt s'.mem (s.gpr .rdi) 256 = Spec.Aes.bytesAt s.mem (s.gpr .rdi) 256 ∧
    AesGcm.Flag.PreparedRepr s'.mem (s.gpr .rdi)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi

theorem absent_ct :
    ConstantTime isa absentX86_64.pre absentX86_64.pub Impl.Gcm.X86_64.Flag.prepareAbsent := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ h
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr; exact h

theorem absent_run (s₀ : State) (hw : InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 1024) 8) :
    WP isa Impl.Gcm.X86_64.Flag.prepareAbsent s₀ fun s =>
      s.mem = s₀.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 1024) (1#64) ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  have h1 : (1 : BitVec 32).signExtend 64 = 1#64 := by decide
  have ho : BitVec.ofInt 64 ((1024 : Nat) : Int) = BitVec.ofNat 64 1024 := rfl
  refine WP.of_runBlock ⟨{ s₀.setReg .rax 1#64 with
    mem := s₀.mem.writeW (s₀.gpr .rdi + BitVec.ofNat 64 1024) (1#64) }, ?_, ?_⟩
  · simp only [Impl.Gcm.X86_64.Flag.flagOff, runBlock_cons,
      runStep_some, runBlock_nil, exec, readSrc, Option.map_some, h1, State.store64, State.ea,
      ho, RegUpd.wr_setReg, hw, ↓reduceIte, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne _ _ (show ¬Reg.rdi = .rax by decide)]
    rfl
  · exact ⟨rfl, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩

theorem absent_correct (s₀ : State) (hp : absentX86_64.pre s₀) :
    ∃ t s', Exec isa Impl.Gcm.X86_64.Flag.prepareAbsent s₀ t s' ∧ abiPreserved s₀ s' ∧
      absentX86_64.post s₀ s' := by
  obtain ⟨_, hwr, hwrap, hret⟩ := hp
  have hw : InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofNat 64 1024) 8 := by
    rw [hwr]; exact ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by decide) (by decide)⟩
  obtain ⟨t, s', he, hm, hg, _, _⟩ := absent_run s₀ hw
  have fr : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 1024, 8⟩] s₀.mem s'.mem := by
    rw [hm]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨t, s', he, abiPreserved_of_exec (by rfl) he ⟨fun r hr => hg r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩, ?_, Or.inl ?_⟩
  · exact fr.readW (Region.contains_self _ _) (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact hret.sub_right (Offset.sub_base (s₀.gpr .rdi) (by decide))) (by decide)
  · exact Proof.Gcm.X86_64.Prepare.bytesAt_frame fr (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.base_disjoint _ (by decide) (by omega)) (by decide)
  · rw [hm]; exact Mem.readW_writeW_self64 _ _ _

theorem absent_verified :
    Verified target Impl.Gcm.X86_64.Flag.prepareAbsent (AesGcm.Flag.prepareContract abi) :=
  Verified.of_correct absent_correct absent_ct (by
    sig_implies [AesGcm.Flag.prepareContract, AesGcm.Flag.prepareSig, AesGcm.Flag.preparePost,
      absentX86_64, X86_64.abi, X86_64.argRegs] [prepareSatF] using prepareSatF)

end VG.Proof.AesGcm.X86_64.Flag
