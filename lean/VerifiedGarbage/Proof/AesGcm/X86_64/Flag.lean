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
public import VerifiedGarbage.Impl.Gcm.X86_64.Flag

/-!
# AES-GCM on x86-64 against the flagged prepared contracts

Every implementation of the functions on the prepared key context, against
the contracts of `Proof/AesGcm/Flag.lean`:

* an implementation that reads no powers runs its code on the key context,
  whose proof moves to the 1032-byte context (`Verified.widenFirstArray`)
  and leaks the flag's (`Verified.with_leak`, `Verified.leak_mono`);
* one that reads them runs, by the count (`onFlag t`, `t` the powers it
  reads, 48 or 16), its code on the prepared powers if they are there, and its
  code on the key context if not (`Verified.of_onFlagCtx`).
-/

@[expose] public section

-- separate module: what only the registration of the flagged contracts needs

namespace VG.Proof.AesGcm.X86_64.Flag

open VG VG.X86_64

/-! ## `seal` -/

def sealSatF : State :=
  { sealFrameSat with rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0x8008, 24⟩] }

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
    | (intro _
       refine preparedPowersRepr_of_zero fun i hi => ?_
       split
       · next h => exfalso; bv_omega
       · rfl)
    | (intro _
       refine preparedPowers16Repr_of ?_
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
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ h => h.1) seal_satF) (fun _ _ _ _ _ _ _ _ _ _ => rfl)

/-- From its proof leaking only whether the count is at least `t`. -/
theorem seal_ofB {t : Nat} (ht : t = 16 ∨ t = 48) {c : Prog isa} {stack : Nat}
    (h : Verified target c (AesGcm.Flag.sealRoundsContractB t abi stack)) :
    Verified target c (AesGcm.Flag.sealRoundsContract abi stack) :=
  Verified.leak_head (AesGcm.Flag.flagBit t) Proof.AesGcm.Flag.flagLeak (AesGcm.Flag.flagBit_of_flagLeak ht) h
    (fun _ _ _ _ _ _ _ _ _ _ => ⟨_, rfl, rfl⟩)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem seal_onFlagB {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealPreparedRoundsContract abi 2624))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealRoundsContract abi 2624)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.sealRoundsContractB 48 abi 2624) :=
  Verified.of_onFlagCtxL (Or.inr rfl) (VG.X86_64.flagBit 48) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.2 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ => rfl)
    seal_satF

theorem seal_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealPreparedRoundsContract abi 2624))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealRoundsContract abi 2624)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.sealRoundsContract abi 2624) :=
  seal_ofB (Or.inr rfl) (seal_onFlagB h₁ h₂)

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem seal_onFlag16B {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealPrepared16RoundsContract abi 2624))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealRoundsContract abi 2624)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.sealRoundsContractB 16 abi 2624) :=
  Verified.of_onFlagCtxL (Or.inl rfl) (VG.X86_64.flagBit 16) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ h => h) seal_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ => rfl)
    seal_satF

theorem seal_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealPrepared16RoundsContract abi 2624))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealRoundsContract abi 2624)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.sealRoundsContract abi 2624) :=
  seal_ofB (Or.inl rfl) (seal_onFlag16B h₁ h₂)

/-! ## `open` -/

def openSatF : State :=
  { openFrameSat with rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x2100, 0⟩, ⟨0, 0⟩, ⟨0x8008, 32⟩] }

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
    | (intro _
       exact preparedPowersRepr_of_zero fun _ _ => rfl)
    | (intro _
       refine preparedPowers16Repr_of ?_
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
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ h => h.1) open_satF) (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- From its proof leaking only whether the count is at least `t`. -/
theorem open_ofB {t : Nat} (ht : t = 16 ∨ t = 48) {c : Prog isa} {stack : Nat}
    (h : Verified target c (AesGcm.Flag.openRoundsContractB t abi stack)) :
    Verified target c (AesGcm.Flag.openRoundsContract abi stack) :=
  Verified.leak_head (AesGcm.Flag.flagBit t) Proof.AesGcm.Flag.flagLeak (AesGcm.Flag.flagBit_of_flagLeak ht) h
    (fun _ _ _ _ _ _ _ _ _ _ _ => ⟨_, rfl, rfl⟩)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem open_onFlagB {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openPreparedRoundsContract abi 2632))
    (h₂ : Verified target c₂ (Proof.AesGcm.openRoundsContract abi 2632)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.openRoundsContractB 48 abi 2632) :=
  Verified.of_onFlagCtxL (Or.inr rfl) (VG.X86_64.flagBit 48) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.2 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    open_satF

theorem open_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openPreparedRoundsContract abi 2632))
    (h₂ : Verified target c₂ (Proof.AesGcm.openRoundsContract abi 2632)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.openRoundsContract abi 2632) :=
  open_ofB (Or.inr rfl) (open_onFlagB h₁ h₂)

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem open_onFlag16B {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openPrepared16RoundsContract abi 2632))
    (h₂ : Verified target c₂ (Proof.AesGcm.openRoundsContract abi 2632)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.openRoundsContractB 16 abi 2632) :=
  Verified.of_onFlagCtxL (Or.inl rfl) (VG.X86_64.flagBit 16) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ h => h) open_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ _ _ _ => rfl)
    open_satF

theorem open_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openPrepared16RoundsContract abi 2632))
    (h₂ : Verified target c₂ (Proof.AesGcm.openRoundsContract abi 2632)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.openRoundsContract abi 2632) :=
  open_ofB (Or.inl rfl) (open_onFlag16B h₁ h₂)

/-! ## `streamEncrypt` -/

def crSatF : State := { crFrameSat with rd := [⟨0x1000, 1032⟩, ⟨0x8008, 8⟩] }

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
    | (intro _
       exact preparedPowersRepr_of_zero fun _ _ => rfl)
    | (intro _
       refine preparedPowers16Repr_of ?_
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
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => h.1) streamEncrypt_satF) (fun _ _ _ _ _ _ _ _ => rfl)

/-- From its proof leaking only whether the count is at least `t`. -/
theorem streamEncrypt_ofB {t : Nat} (ht : t = 16 ∨ t = 48) {c : Prog isa} {stack : Nat}
    (h : Verified target c (AesGcm.Flag.streamEncryptRoundsContractB t abi stack)) :
    Verified target c (AesGcm.Flag.streamEncryptRoundsContract abi stack) :=
  Verified.leak_head (AesGcm.Flag.flagBit t) Proof.AesGcm.Flag.flagLeak (AesGcm.Flag.flagBit_of_flagLeak ht) h
    (fun _ _ _ _ _ _ _ _ => ⟨_, rfl, rfl⟩)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem streamEncrypt_onFlagB {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamEncryptPreparedRoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamEncryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.streamEncryptRoundsContractB 48 abi 2608) :=
  Verified.of_onFlagCtxL (Or.inr rfl) (VG.X86_64.flagBit 48) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.2 hf⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamEncrypt_satF

theorem streamEncrypt_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamEncryptPreparedRoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamEncryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.streamEncryptRoundsContract abi 2608) :=
  streamEncrypt_ofB (Or.inr rfl) (streamEncrypt_onFlagB h₁ h₂)

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem streamEncrypt_onFlag16B {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamEncryptPrepared16RoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamEncryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.streamEncryptRoundsContractB 16 abi 2608) :=
  Verified.of_onFlagCtxL (Or.inl rfl) (VG.X86_64.flagBit 16) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamEncrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamEncrypt_satF

theorem streamEncrypt_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamEncryptPrepared16RoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamEncryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.streamEncryptRoundsContract abi 2608) :=
  streamEncrypt_ofB (Or.inl rfl) (streamEncrypt_onFlag16B h₁ h₂)

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
    | (intro _
       exact preparedPowersRepr_of_zero fun _ _ => rfl)
    | (intro _
       refine preparedPowers16Repr_of ?_
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
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ h => h.1) streamDecrypt_satF) (fun _ _ _ _ _ _ _ _ => rfl)

/-- From its proof leaking only whether the count is at least `t`. -/
theorem streamDecrypt_ofB {t : Nat} (ht : t = 16 ∨ t = 48) {c : Prog isa} {stack : Nat}
    (h : Verified target c (AesGcm.Flag.streamDecryptRoundsContractB t abi stack)) :
    Verified target c (AesGcm.Flag.streamDecryptRoundsContract abi stack) :=
  Verified.leak_head (AesGcm.Flag.flagBit t) Proof.AesGcm.Flag.flagLeak (AesGcm.Flag.flagBit_of_flagLeak ht) h
    (fun _ _ _ _ _ _ _ _ => ⟨_, rfl, rfl⟩)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem streamDecrypt_onFlagB {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamDecryptPreparedRoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamDecryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.streamDecryptRoundsContractB 48 abi 2608) :=
  Verified.of_onFlagCtxL (Or.inr rfl) (VG.X86_64.flagBit 48) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.2 hf⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamDecrypt_satF

theorem streamDecrypt_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamDecryptPreparedRoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamDecryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.streamDecryptRoundsContract abi 2608) :=
  streamDecrypt_ofB (Or.inr rfl) (streamDecrypt_onFlagB h₁ h₂)

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem streamDecrypt_onFlag16B {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamDecryptPrepared16RoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamDecryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.streamDecryptRoundsContractB 16 abi 2608) :=
  Verified.of_onFlagCtxL (Or.inl rfl) (VG.X86_64.flagBit 16) VG.X86_64.flagBit_iff (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ h => h) streamDecrypt_satbase)
    (fun _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1 hf⟩)
    (fun _ _ _ _ _ _ _ _ h _ => h.1)
    (fun _ _ _ _ _ _ _ _ => rfl)
    streamDecrypt_satF

theorem streamDecrypt_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.streamDecryptPrepared16RoundsContract abi 2608))
    (h₂ : Verified target c₂ (Proof.AesGcm.streamDecryptRoundsContract abi 2608)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.streamDecryptRoundsContract abi 2608) :=
  streamDecrypt_ofB (Or.inl rfl) (streamDecrypt_onFlag16B h₁ h₂)

/-! ## `sealGather` -/

def gatherSatF : State :=
  { Gather.gatherFrameSat with rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x9008, 40⟩] }

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
    | (intro _
       exact preparedPowersRepr_of_zero fun _ hi => by simp only [Gather.ctx_low hi, ite_false])
    | (intro _
       refine preparedPowers16Repr_of ?_
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
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) sealGather_satF) (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem sealGather_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealGatherPreparedRoundsContract abi 5128))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealGatherRoundsContract abi 5128)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.sealGatherRoundsContract abi 5128) :=
  Verified.of_onFlagCtx (Or.inr rfl) (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.2 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    sealGather_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem sealGather_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.sealGatherPrepared16RoundsContract abi 5128))
    (h₂ : Verified target c₂ (Proof.AesGcm.sealGatherRoundsContract abi 5128)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.sealGatherRoundsContract abi 5128) :=
  Verified.of_onFlagCtx (Or.inl rfl) (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ h => h) sealGather_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.1 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    sealGather_satF

/-! ## `openTo` -/

def toSatF : State :=
  { OpenTo.toSat with rd := [⟨0x1000, 1032⟩, ⟨0x2000, 0⟩, ⟨0x3000, 0⟩, ⟨0x4000, 0⟩, ⟨0x6000, 0⟩, ⟨0x9008, 48⟩] }

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
    | (intro _
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])
    | (intro _
       refine preparedPowers16Repr_of ?_
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
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) openTo_satF) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem openTo_onFlag {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPreparedRoundsContract abi 2728))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2728)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2728) :=
  Verified.of_onFlagCtx (Or.inr rfl) (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.2 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem openTo_onFlag16 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPrepared16RoundsContract abi 2728))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2728)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2728) :=
  Verified.of_onFlagCtx (Or.inl rfl) (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow16)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.1 hf⟩)
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
    | (intro _
       exact Proof.AesGcm.preparedPowersRepr_of_zeroMem fun _ hi => by simp only [OpenTo.ctx_low hi, ite_false])
    | (intro _
       refine preparedPowers16Repr_of ?_
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
  Verified.leak_flag (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) openTo_satF2776) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)

/-- By the flag: `c₁` on the prepared powers, `c₂` on the key context. -/
theorem openTo_onFlag2776 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPreparedRoundsContract abi 2776))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2776)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 48 c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2776) :=
  Verified.of_onFlagCtx (Or.inr rfl) (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow2776)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase2776)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.2 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF2776

/-- By the flag: `c₁` on the first sixteen prepared powers, `c₂` on the key
context. -/
theorem openTo_onFlag162776 {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (Proof.AesGcm.openToPrepared16RoundsContract abi 2776))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2776)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag 16 c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2776) :=
  Verified.of_onFlagCtx (Or.inl rfl) (by decide)
    (VG.X86_64.Verified.widenFirstArray (n := 128) (n' := 129) (by decide) h₁
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satpow162776)
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase2776)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, h.2.2.1 hf⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF2776

/-- By the flag: `c₁` on a context whose powers are present, `c₂` on the key
context. -/
theorem openTo_onFlagF {t : Nat} (ht : t = 16 ∨ t = 48) {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (AesGcm.Flag.openToFlaggedRoundsContract t abi 2728))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2728)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag t c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2728) :=
  Verified.of_onFlagCtx ht (by decide) h₁
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, hf, h.2.2⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF

/-- By the flag: `c₁` on a context whose powers are present, `c₂` on the key
context, with the stack of the code that splits. -/
theorem openTo_onFlagF2776 {t : Nat} (ht : t = 16 ∨ t = 48) {c₁ c₂ : Prog isa}
    (h₁ : Verified target c₁ (AesGcm.Flag.openToFlaggedRoundsContract t abi 2776))
    (h₂ : Verified target c₂ (Proof.AesGcm.openToRoundsContract abi 2776)) :
    Verified target (Impl.Gcm.X86_64.Flag.onFlag t c₁ c₂) (AesGcm.Flag.openToRoundsContract abi 2776) :=
  Verified.of_onFlagCtx ht (by decide) h₁
    (VG.X86_64.Verified.widenFirstArray (n := 32) (n' := 129) (by decide) h₂
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h => h) openTo_satbase2776)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hf => ⟨h.1, h.2.1, hf, h.2.2⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => ⟨h.1, h.2.1⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
    openTo_satF2776

end VG.Proof.AesGcm.X86_64.Flag
