module

public import VerifiedGarbage.Impl.Dsa.AArch64.RandomSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCall
public import VerifiedGarbage.Spec.Dsa.RandomSign
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallResult
public import VerifiedGarbage.Proof.Dsa.AArch64.PrevalidatedSignVerified
public import VerifiedGarbage.Proof.Dsa.SignContractWith
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignABI
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublic
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInvalidCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBodyCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.Encoding

/-! ### `Dsa.AArch64.RandomSignCorrect`, which only this module used -/

section

/-! Randomized signing's functional correctness against its shared contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_shared_post {extra : Nat} {s t : State} (h : RandomSignABI extra s)
    (hp : RandomSignCodePost s (randomSignRemaining (randomInput s) 0 8) t) :
    (randomSignCheckedContract abi (extra + 256)).post s t := by
  sig_post [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_post [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  have he := random_remaining_bytes h
  have hb : (randomSignRemaining (randomInput s) 0 8).status < 2 ^ 32 := by
    have := randomSignLoop_status_le (randomInput s).pLen (randomInput s).qLen 8
      (randomInput s).key (randomInput s).digest ((randomInput s).rand.drop 0)
    change (randomSignRemaining (randomInput s) 0 8).status ≤ 2 at this
    omega_using [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    exact congrArg Spec.Dsa.RandomSignResult.status he
  · exact (hp.output.trans (congrArg (fun r : Spec.Dsa.RandomSignResult => r.signature.getD
      (List.replicate (s.gpr .x1).toNat 0)) he))
  · change Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    exact congrArg (fun r : Spec.Dsa.RandomSignResult => [BitVec.ofNat 64 r.used]) he

theorem random_sign_correct (S : Signer) (s : State)
    (hpre : (randomSignCheckedContract abi (S.stack + 256)).pre s) (hval : RandomValid S s) :
    ∃ trace t, Exec isa (RandomSign.code S.name S.code) s trace t ∧
      abiPreserved s t ∧ (randomSignCheckedContract abi (S.stack + 256)).post s t := by
  have h := randomSignABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := random_sign_code S h hval
  exact ⟨trace, t, he, ⟨hp.callee, hp.sp, hp.vectors⟩, random_sign_shared_post h hp⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.RandomSignConstantTime`, which only this module used -/

section

/-! Whole-entry leakage equality against the merged randomized-signing contract. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

theorem random_sign_body_agreement (S : Signer) {s t : State}
    (hs : RandomSignABI S.stack s) (ht : RandomSignABI S.stack t) (hp : RandomSignPublicAgree s t)
    (hvs : RandomValid S s) (hvt : RandomValid S t)
    (htrace : (randomSignRemaining (randomInput s) 0 8).trace = (randomSignRemaining (randomInput t) 0 8).trace)
    (hstatus : (randomSignRemaining (randomInput s) 0 8).status = (randomSignRemaining (randomInput t) 0 8).status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (RandomSign.body S.name S.code) (allocated Random.frameBytes t) tsb w) : tsa = tsb := by
  by_cases hq : 1 < Spec.Dsa.decodeBE (randomQBytes s)
  · exact random_sign_body_valid_ct S hs ht hp hvs hvt hq htrace hstatus ea eb
  · exact random_sign_body_invalid_ct S hs ht hp hq ea eb

theorem random_sign_alloc {extra : Nat} {s : State} (h : RandomSignABI extra s) :
    isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
  have hl := h.stackLower
  simp only [isa, push, allocated]
  exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega_using [hl]⟩

theorem random_sign_constantTime (S : Signer) :
    ConstantTime isa (fun s => (randomSignCheckedContract abi (S.stack + 256)).pre s ∧ RandomValid S s)
      (randomSignCheckedContract abi (S.stack + 256)).pub
      (RandomSign.code S.name S.code) := by
  intro s t tsa tsb u w ⟨hs, hvs⟩ ⟨ht, hvt⟩ hpub ea eb
  have hsa := randomSignABI_of hs
  have hta := randomSignABI_of ht
  obtain ⟨hp, hstatus, _, htrace⟩ := random_sign_public_related hsa hta hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [random_sign_alloc hsa, Option.some.injEq] at hap
      rw [random_sign_alloc hta, Option.some.injEq] at hbp
      subst hap
      subst hbp
      have hh := random_sign_body_agreement S hsa hta hp hvs hvt htrace hstatus hab hbb
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.AArch64

end

end

/-! Complete verification of randomized DSA signing for every AArch64 backend:
`vg_dsa_sign_random`, which calls the fully checked signer, and
`vg_dsa_sign_random_prevalidated`, which calls the signer for a validated
private key. -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def randomSignSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 40 | .x2 => 0x7000 | .x3 => 0x2000
    | .x4 => 424 | .x5 => 128 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x1000000000000
  mem a := if 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 then
      VG.Proof.Dsa.validPrivateKeyWitness[a.toNat - 0x2000]?.getD 0
    else if a = 0x1000000000009 then 0x60 else if a = 0x1000000000019 then 0x80
    else if a = 0x1000000000020 then 0x40 else if a = 0x1000000000021 then 8 else 0
  rd := [⟨0x2000, 424⟩, ⟨0x5000, 0⟩, ⟨0x6000, 0⟩, ⟨0x1000000000000, 40⟩]
  wr := [⟨0x1000, 40⟩, ⟨0x7000, 8⟩, ⟨0x8000, 16896⟩]

private theorem sat_arg_0 : stackArg randomSignSatState 0 = 0 := by decide +kernel
private theorem sat_arg_1 : stackArg randomSignSatState 1 = 24576 := by decide +kernel
private theorem sat_arg_2 : stackArg randomSignSatState 2 = 0 := by decide +kernel
private theorem sat_arg_3 : stackArg randomSignSatState 3 = 32768 := by decide +kernel
private theorem sat_arg_4 : stackArg randomSignSatState 4 = 2112 := by decide +kernel

theorem random_sign_sat_pre (extra : Nat) (hb : extra < 2 ^ 32) :
    (randomSignCheckedContract abi (extra + 256)).pre randomSignSatState := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2, sat_arg_3, sat_arg_4]
  all_goals first
    | (change extra + 256 ≤ 281474976710656; omega_using [hb])
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, randomSignSatState] at h₁ h₂; bv_omega)

theorem random_sign_satisfiable (v : Backend) :
    ∃ s, (randomSignCheckedContract abi (v.stack + 256)).pre s :=
  ⟨_, random_sign_sat_pre v.stack v.stackBound⟩

/-- A backend's fully checked signer, which accepts every key. -/
def Backend.signer (v : Backend) : Signer where
  name := randomSignerName v
  code := SignVerify.sign v.mul
  stack := v.stack
  valid := fun _ _ _ => true
  verified := Verified.of_narrow v.signVerified (fun s => s) (fun _ s => s)
    (fun _ h => (signWith_pre h).1) (fun _ _ _ _ e => e) (fun _ _ _ _ _ ha hp => ⟨ha, signWith_post hp⟩)
    (fun _ _ _ _ h => signWith_pub h)
    (by obtain ⟨s, hs⟩ := v.signVerified.2.2; exact ⟨s, signWith_of_pre hs rfl⟩)
  sp := v.signSp
  depth := v.signDepth
  stackBound := v.stackBound

theorem random_sign_verified (v : Backend) :
    Verified target (RandomSign.code (randomSignerName v) (SignVerify.sign v.mul))
      (randomSignCheckedContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.signer s h rfl,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.signer s₁ s₂ t₁ t₂ u₁ u₂ ⟨h₁, rfl⟩ ⟨h₂, rfl⟩,
    random_sign_satisfiable v⟩

def prevalidatedSignerName (v : Backend) : String := "vg_dsa_sign_prevalidated" ++ v.suffix

/-- A backend's signer for a validated private key. -/
def Backend.prevalidatedSigner (v : Backend) : Signer where
  name := prevalidatedSignerName v
  code := PrevalidatedSign.sign v.mul
  stack := v.stack
  valid := Spec.Dsa.validatePrivateKeyBytes
  verified := v.prevalidatedSignVerified
  sp := v.prevalidatedSignSp
  depth := v.prevalidatedSignDepth
  stackBound := v.stackBound

theorem randomPrevalidated_pre {extra : Nat} {s : State}
    (h : (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s) :
    (randomSignCheckedContract abi (extra + 256)).pre s ∧
      Spec.Dsa.validatePrivateKeyBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = true := by
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs,
    randomSignStackArgs] at h
  sig_split h
  refine ⟨?_, by assumption⟩
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl]
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs]
  sig_and_intros <;> with_reducible assumption

theorem randomPrevalidated_of_pre {extra : Nat} {s : State}
    (h : (randomSignCheckedContract abi (extra + 256)).pre s)
    (hv : Spec.Dsa.validatePrivateKeyBytes (s.gpr .x5).toNat (s.gpr .x6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) = true) :
    (Spec.Dsa.randomSignPrevalidatedContract abi (extra + 256)).pre s := by
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl] at h
  sig_pre [randomSignCheckedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs] at h
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs, randomSignStackArgs,
    show extra + 256 = (extra + 255) + 1 from rfl]
  sig_pre [Spec.Dsa.randomSignPrevalidatedContract, Spec.Dsa.randomSignSig, abi, argRegs,
    randomSignStackArgs]
  sig_split h
  sig_and_intros <;> with_reducible assumption

theorem random_sign_sat_key :
    Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424 = VG.Proof.Dsa.validPrivateKeyWitness :=
  VG.Proof.Dsa.bytesAt_of_list (lo := 0x2000) (by decide +kernel) (by decide) fun a h1 h2 => by
    have h : 0x2000 ≤ a.toNat ∧ a.toNat < 0x21a8 := ⟨h1, h2⟩
    simp only [randomSignSatState, h, and_self, ↓reduceIte]

theorem random_sign_prevalidated_verified (v : Backend) :
    Verified target (RandomSign.code (prevalidatedSignerName v) (PrevalidatedSign.sign v.mul))
      (Spec.Dsa.randomSignPrevalidatedContract abi (v.stack + 256)) :=
  ⟨fun s h => random_sign_correct v.prevalidatedSigner s (randomPrevalidated_pre h).1
      (randomPrevalidated_pre h).2,
    fun s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ => random_sign_constantTime v.prevalidatedSigner s₁ s₂ t₁ t₂ u₁ u₂
      (randomPrevalidated_pre h₁) (randomPrevalidated_pre h₂),
    ⟨_, randomPrevalidated_of_pre (random_sign_sat_pre v.stack v.stackBound) (by
      change Spec.Dsa.validatePrivateKeyBytes 128 20 (Spec.Rsa.bytesAt randomSignSatState.mem 0x2000 424) = true
      rw [random_sign_sat_key]
      exact VG.Proof.Dsa.validPrivateKeyWitness_valid)⟩⟩

end VG.Proof.Dsa.AArch64
