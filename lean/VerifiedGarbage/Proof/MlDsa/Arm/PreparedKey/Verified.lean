module

public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.CT
public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Entry
public import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.Body
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Inst
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.MlDsa.Arm.PreparedKey.CT
meta import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on ARMv7, preparing keys: verified

`vg_mldsa*_prepare_verifying_key` and `vg_mldsa*_prepare_signing_key`, with
the ARM implementations of the primitives, are verified against
`preparePublicKeyContract` and `prepareSecretKeyContract` with 44 bytes of
stack.
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.PreparedKey

open VG VG.Arm VG.Spec.MlDsa
open VG.Impl.MlDsa.Arm.PreparedKey
open VG.Impl.MlDsa.Arm.Sign (Ptr copy seqR)
open VG.Proof.MlDsa.Arm.Sign
open VG.Spec.Sha3 (bytesAt)

/-- `vg_mldsa_unpack_t1`, with no stack. -/
def t1Callee : Callee (fun S => unpackT1Contract Arm.abi S) 0 callStack Impl.MlDsa.Arm.Pack.unpackT1 :=
  ⟨0, by decide, Pack.unpackT1_verified, by decide +kernel⟩

theorem writes_in (bytes count : Nat) :
    ∀ w ∈ writes bytes count, inB (input bytes ++ output bytes count) w.1 w.2 = true := by
  intro w hw
  simp only [writes, List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hw
  rcases hw with rfl | rfl | hw | ⟨i, hi, rfl⟩
  · rw [in8]; simp
  · rw [in7]; simp
  · simp at hw
  · rw [in8, decide_eq_true_eq]; have : 1024 * i + 1024 ≤ 1024 * count := by omega
    omega

theorem writes_sub (bytes count : Nat) (u : State) :
    ∀ R ∈ (writes bytes count).map (toR u), ∃ b ∈ input bytes ++ output bytes count,
      Region.Sub R ⟨State.addr (u.gpr b.1), b.2⟩ := by
  intro R hR
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hR
  obtain ⟨n, hn, hs⟩ := sub_of_inB (s := u) (writes_in bytes count w hw)
  exact ⟨_, hn, hs⟩

/-- The body of `vg_mldsa*_prepare_verifying_key`, as `entry_correct` takes it. -/
theorem public_wp {p : Params} (hp : Ok3 p) (u : State) (L : Lay callStack (input p.pkLen) (output p.pkLen p.k) u) :
    WP isa (.seq (copy (.r8, 0) (.r4, 0) p.pkLen) (seqR (publicPoly prims p) 0 p.k)) u fun t =>
      PostB callStack u t ((writes p.pkLen p.k).map (toR u)) ∧ CS u t ∧
      bytesAt t.mem (pa t (.r8, 0)) p.pkLen = bytesAt u.mem (pa u (.r4, 0)) p.pkLen ∧
      PreparedPublicKey p t.mem (pa t (.r8, 0)) :=
  WP.mono (public_body prims_ok t1Callee hp u L) fun _ ⟨h, hk⟩ => ⟨h.post, h.cs, h.encoded, hk⟩

theorem secret_wp {p : Params} (hp : Ok3 p) (u : State)
    (L : Lay callStack (input p.skLen) (output p.skLen (p.ℓ + 2 * p.k)) u) :
    WP isa (.seq (copy (.r8, 0) (.r4, 0) p.skLen) (seqR (secretPoly prims p) 0 (p.ℓ + 2 * p.k))) u fun t =>
      PostB callStack u t ((writes p.skLen (p.ℓ + 2 * p.k)).map (toR u)) ∧ CS u t ∧
      bytesAt t.mem (pa t (.r8, 0)) p.skLen = bytesAt u.mem (pa u (.r4, 0)) p.skLen ∧
      PreparedSecretKey p t.mem (pa t (.r8, 0)) :=
  WP.mono (secret_body prims_ok hp u L) fun _ ⟨h, hk⟩ => ⟨h.post, h.cs, h.encoded, hk⟩

theorem sizes {p : Params} (hp : Ok3 p) :
    p.pkLen < 2 ^ 32 ∧ p.pkLen + 1024 * p.k < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧
      p.skLen + 1024 * (p.ℓ + 2 * p.k) < 2 ^ 32 := by
  rcases hp with rfl | rfl | rfl <;> decide

/-- A state satisfying the precondition of the preparations. -/
def prepSat (bytes total : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x200000 | .r2 => 0x10000 | _ => 0
  sp := 0x80000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, bytes⟩]
  wr := [⟨0x200000, total⟩, ⟨0x10000, 1024⟩]

theorem prepSat_public {p : Params} (hp : Ok3 p) :
    (preparePublicKeyContract p Arm.abi prepStack).pre (prepSat p.pkLen (preparedPublicKeyBytes p)) := by
  rcases hp with rfl | rfl | rfl <;>
  sig_sat_check [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, prepSat]

theorem prepSat_secret {p : Params} (hp : Ok3 p) :
    (prepareSecretKeyContract p Arm.abi prepStack).pre (prepSat p.skLen (preparedSecretKeyBytes p)) := by
  rcases hp with rfl | rfl | rfl <;>
  sig_sat_check [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, prepSat]

theorem preparePublic_verified {p : Params} (hp : Ok3 p) :
    Verified Arm.target (preparePublic prims p) (preparePublicKeyContract p Arm.abi prepStack) := by
  obtain ⟨s1, s2, -, -⟩ := sizes hp
  refine ⟨fun σ hσ => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, ha, hb, hk⟩ := entry_correct (B := fun m a => PreparedPublicKey p m a) _ s1 s2
      (writes_sub _ _) (public_wp hp) (public_pre hσ)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨hb, hk⟩
  · refine RelCT.constantTime (RelCT.mono (entry_tr s1 s2 (public_rel prims_ok t1Callee hp))
      (fun x y ⟨hx, hy, hpub⟩ => ?_) fun _ _ h => h)
    sig_pub [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    exact ⟨public_pre hx, public_pre hy, hpub⟩
  · exact ⟨_, prepSat_public hp⟩

theorem prepareSecret_verified {p : Params} (hp : Ok3 p) :
    Verified Arm.target (prepareSecret prims p) (prepareSecretKeyContract p Arm.abi prepStack) := by
  obtain ⟨-, -, s1, s2⟩ := sizes hp
  refine ⟨fun σ hσ => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, ha, hb, hk⟩ := entry_correct (B := fun m a => PreparedSecretKey p m a) _ s1 s2
      (writes_sub _ _) (secret_wp hp) (secret_pre hσ)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    exact ⟨hb, hk⟩
  · refine RelCT.constantTime (RelCT.mono (entry_tr s1 s2 (secret_rel prims_ok hp))
      (fun x y ⟨hx, hy, hpub⟩ => ?_) fun _ _ h => h)
    sig_pub [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    exact ⟨secret_pre hx, secret_pre hy, hpub⟩
  · exact ⟨_, prepSat_secret hp⟩

/-- Memory holding a prepared public key at `0x200000`, of the key of zeros. -/
theorem prepared_public_mem {p : Params} (hp : Ok3 p) : ∃ m : Mem,
    bytesAt m 0x200000 p.pkLen = bytesAt (fun _ => 0) 0x1000 p.pkLen ∧ PreparedPublicKey p m 0x200000 := by
  obtain ⟨_, s', -, -, hq⟩ := (preparePublic_verified hp).1 _ (prepSat_public hp)
  sig_post [preparePublicKeyContract, preparePublicKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at hq
  exact ⟨s'.mem, hq.1, hq.2⟩

/-- Memory holding a prepared private key at `0x200000`. -/
theorem prepared_secret_mem {p : Params} (hp : Ok3 p) : ∃ m : Mem, PreparedSecretKey p m 0x200000 := by
  obtain ⟨_, s', -, -, hq⟩ := (prepareSecret_verified hp).1 _ (prepSat_secret hp)
  sig_post [prepareSecretKeyContract, prepareSecretKeySig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at hq
  exact ⟨s'.mem, hq.2⟩

end VG.Proof.MlDsa.Arm.PreparedKey
