module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Sig
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyState
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinish
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignPublishValue
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeySample
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCheckedVerified
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.DomainChecked
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyABI
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyEntry
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Dsa.AArch64.Run

/-! ### `Dsa.AArch64.GenerateKeySampled`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyDeriveCall`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyDerivePre`, which this module and modules that import it used -/

section

/-! ### `Dsa.AArch64.GenerateKeyDerive`, which this module and modules that import it used -/

section

/-! # Key generation's call of key derivation, with the sampled x -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def keygenDeriveOutgoing : List (Nat × Nat) := [(Random.oScratchLen, 0)]

theorem keygen_deriveArgs_ok {s : State} {B : Addr}
    (hs : Scr s B Random.frameBytes) (hsp : s.sp = B) :
    WP isa (.block GenerateKey.deriveArgs) s fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧
      t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧
      t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oScratch ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] s t := by
  unfold GenerateKey.deriveArgs
  rw [WP.block_append_iff]
  refine WP.mono (random_copySlot_ok Random.oScratchLen 0 hsp (by decide) (by decide)
    (hs.ld (by decide)) (hs.st (by decide))) fun u ⟨hum, hku⟩ => ?_
  have hus := hs.congr hku.wr
  have husp := hku.sp.trans hsp
  refine WP.mono (WP.keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7] (Q := fun t =>
      t.gpr .x0 = word s.mem B Random.oOut ∧ t.gpr .x1 = word s.mem B Random.oOutLen ∧
      t.gpr .x2 = word s.mem B Random.oKey ∧ t.gpr .x3 = word s.mem B Random.oKeyLen ∧
      t.gpr .x4 = word s.mem B Random.oPLen ∧ t.gpr .x5 = off B Random.oNonce ∧
      t.gpr .x6 = word s.mem B Random.oQLen ∧ t.gpr .x7 = word s.mem B Random.oScratch ∧
      t.mem = randomSlotsMem B s.mem keygenDeriveOutgoing) ?_ rfl rfl rfl)
    fun t ⟨ht, hkt⟩ => ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1,
      ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.2, (hku.trans hkt).mono (by decide)⟩
  brun [exec_ldrSp_x', exec_addSp (show Random.oNonce < 4096 by decide), husp, hus.ld (d := Random.oOut) (by decide),
    hus.ld (d := Random.oOutLen) (by decide), hus.ld (d := Random.oKey) (by decide),
    hus.ld (d := Random.oKeyLen) (by decide), hus.ld (d := Random.oPLen) (by decide),
    hus.ld (d := Random.oQLen) (by decide), hus.ld (d := Random.oScratch) (by decide)]
  simp only [hum, keygenDeriveOutgoing, randomSlotsMem]
  simp (disch := decide) only [random_word_write_other]
  trivial

theorem keygen_deriveOutgoing_frame (m : Mem) (B : Addr) :
    Outside B 0 8 m (randomSlotsMem B m keygenDeriveOutgoing) := by
  apply random_slots_outside
  intro p hp
  simp only [keygenDeriveOutgoing, List.mem_cons, List.not_mem_nil, or_false] at hp
  subst hp
  decide

theorem keygen_deriveOutgoing_words (m : Mem) (B : Addr) :
    word (randomSlotsMem B m keygenDeriveOutgoing) B 0 = word m B Random.oScratchLen := by
  exact word_writeW_self _ _ _ _

theorem keygen_deriveArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : KeygenSaved s t.mem) :
    WP isa (.block GenerateKey.deriveArgs) t fun u =>
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x1 ∧
      u.gpr .x2 = s.gpr .x3 ∧ u.gpr .x3 = s.gpr .x4 ∧
      u.gpr .x4 = s.gpr .x5 ∧ u.gpr .x5 = off (randomBase s) Random.oNonce ∧
      u.gpr .x6 = s.gpr .x6 ∧ u.gpr .x7 = stackArg s 1 ∧
      word u.mem (randomBase s) 0 = stackArg s 2 ∧
      KeygenSaved s u.mem ∧ Outside (randomBase s) 0 8 t.mem u.mem ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] t u := by
  refine WP.mono (keygen_deriveArgs_ok hs hsp) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 8 t.mem u.mem := by rw [hm]; exact keygen_deriveOutgoing_frame _ _
  exact ⟨hdi.trans (hv (40, s.gpr .x0) (by simp [keygenSavedValues])),
    hsi.trans (hv (48, s.gpr .x1) (by simp [keygenSavedValues])),
    hdx.trans (hv (64, s.gpr .x3) (by simp [keygenSavedValues])),
    hcx.trans (hv (72, s.gpr .x4) (by simp [keygenSavedValues])),
    h8.trans (hv (80, s.gpr .x5) (by simp [keygenSavedValues])), h9,
    h6.trans (hv (88, s.gpr .x6) (by simp [keygenSavedValues])),
    h7.trans (hv (128, stackArg s 1) (by simp [keygenSavedValues])),
    by rw [hm, keygen_deriveOutgoing_words]; exact hv (136, stackArg s 2) (by simp [keygenSavedValues]),
    hv.congr (fun d hd hd' => hf.word (Or.inr (by omega_using [hd])) (by omega_using [hd'])), hf, hk⟩

def keygenDeriveRd (s : State) : List Region :=
  [⟨s.gpr .x3, (s.gpr .x4).toNat⟩, ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩,
    ⟨randomBase s, 8⟩]

def keygenDeriveWr (s : State) : List Region :=
  [⟨s.gpr .x0, (s.gpr .x1).toNat⟩, ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩]

theorem keygen_derive_covers {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr) :
    Covers (keygenDeriveRd s ++ keygenDeriveWr s) (t.rd ++ t.wr) ∧ Covers (keygenDeriveWr s) t.wr := by
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  have hf : (⟨randomBase s, Random.frameBytes⟩ : Region) ∈ t.wr := by rw [hwr]; exact .head _
  have ho : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have hs : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region) ∈ t.wr := by rw [hwr, h.wr]; simp
  have zero (p : Addr) : p = p + BitVec.ofNat 64 0 := (BitVec.add_zero p).symm
  have cw : Covers (keygenDeriveWr s) t.wr := Covers.of_sub fun r hr => by
    simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, ho, 0, zero _, by simp⟩
    · exact ⟨_, hs, 0, zero _, by simp⟩
  refine ⟨Covers.append_left (Covers.of_sub fun r hr => ?_) cw.right, cw⟩
  simp only [keygenDeriveRd, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_append_left _ (by rw [hrd, h.rd]; simp), 0, zero _, by simp⟩
  · exact ⟨_, List.mem_append_right _ hf, 200, rfl, by change 200 + (s.gpr .x6).toNat ≤ 256; omega_using [hq]⟩
  · exact ⟨_, List.mem_append_right _ hf, 0, zero _, by change 0 + 8 ≤ 256; decide⟩

end VG.Proof.Dsa.AArch64

end

end

/-! Establish the key-derivation contract at the wrapper's call boundary. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1) :
    (Spec.Dsa.deriveKeyContract abi extra).pre (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  have hE : stackArg (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) 0 = stackArg s 2 :=
    (random_call_stackArg hsp _ _ 0).trans hw
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  sig_pre [Spec.Dsa.deriveKeyContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6, h7, hsp,
    random_call_stackArgAddr hsp, hE]
  simp only [keygenDeriveRd, keygenDeriveWr]
  have hl := h.stackLower
  have hb := (s.sp).isLt
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hh := h.lengths
    unfold Spec.Dsa.lengthsValid at hh
    omega_using [hh]
  have hk := keygenStackBase_toNat h
  have hR : (randomBase s).toNat = (randomStackBase extra s).toNat + extra := by
    rw [random_frameBase extra s, keygenStack_offset_toNat h (by omega_using [])]
  have hN : (off (randomBase s) Random.oNonce).toNat =
      (randomStackBase extra s).toNat + (extra + 200) := by
    rw [random_nonceBase extra s, keygenStack_offset_toNat h (by omega_using [])]
  have sM : Region.Sub ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩
      (below (s.sp) (extra + 256)) := by
    rw [random_nonceBase extra s]
    exact Offset.sub_base _ (by omega_using [hq])
  have sA : Region.Sub ⟨randomBase s, 8⟩ (below (s.sp) (extra + 256)) := by
    rw [random_frameBase extra s]
    exact Offset.sub_base _ (by omega_using [])
  have sK : Region.Sub (below (randomBase s) extra) (below (s.sp) (extra + 256)) := by
    change Region.Sub ⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ _
    rw [random_calleeBase extra s]
    exact Region.sub_prefix (by omega_using [])
  have dKM : (below (randomBase s) extra).Disjoint
      ⟨off (randomBase s) Random.oNonce, (s.gpr .x6).toNat⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_nonceBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl, hq])
  have dKA : (below (randomBase s) extra).Disjoint ⟨randomBase s, 8⟩ := by
    change (⟨randomBase s - BitVec.ofNat 64 extra, extra⟩ : Region).Disjoint _
    rw [random_calleeBase extra s, random_frameBase extra s]
    exact Offset.base_disjoint _ (by omega_using []) (by omega_using [hl])
  refine ⟨?_, by omega_using [hl, hk, hR], trivial, trivial, h.outParams, (h.stackOut.sub_left sM).symm,
    h.outScratch, (h.stackOut.sub_left sA).symm, h.paramsScratch,
    h.stackScratch.sub_left sM, (h.stackScratch.sub_left sA).symm,
    ?_, h.outBound, h.paramsBound, by omega_using [hl, hq, hk, hN], h.scratchBound,
    h.lengths, h.outLength, h.paramsLength, ?_⟩
  · cases extra <;> simp only <;> omega_using [hR]
  · cases extra with
    | zero => trivial
    | succ n => exact ⟨h.stackOut.sub_left sK, h.stackParams.sub_left sK, dKM,
        h.stackScratch.sub_left sK, dKA⟩
  · have hh := h.scratchLength
    unfold Spec.Dsa.generationScratchWords at hh
    unfold Spec.Dsa.scratchWords
    omega_using [hh]

/-- The checked derivation's contract at key generation's call, once the
domain check has passed. -/
theorem keygen_derive_checked_pre {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    (Spec.Dsa.deriveKeyDomainCheckedContract abi extra).pre
      (t.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) := by
  refine deriveChecked_of_pre (keygen_derive_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7) ?_
  simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem,
    State.callEntry_gpr _ (r := .x2) (by decide), State.callEntry_gpr _ (r := .x3) (by decide),
    State.callEntry_gpr _ (r := .x4) (by decide), State.callEntry_gpr _ (r := .x6) (by decide),
    hdx, hcx, h8, h6, hparams]
  exact hc

end VG.Proof.Dsa.AArch64

end

end

/-! # Verified call of key derivation from the generation controller -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_call (v : Backend) {s t : State} (h : GenerateKeyABI v.stack s)
    (hsp : t.sp = randomBase s)
    (hw : word t.mem (randomBase s) 0 = stackArg s 2)
    (hdi : t.gpr .x0 = s.gpr .x0) (hsi : t.gpr .x1 = s.gpr .x1)
    (hdx : t.gpr .x2 = s.gpr .x3) (hcx : t.gpr .x3 = s.gpr .x4)
    (h8 : t.gpr .x4 = s.gpr .x5) (h9 : t.gpr .x5 = off (randomBase s) Random.oNonce)
    (h6 : t.gpr .x6 = s.gpr .x6) (h7 : t.gpr .x7 = stackArg s 1)
    (hrd : t.rd = s.rd) (hwr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr)
    (hparams : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params)
    (hck : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.call (keygenDeriveName v) (Generate.deriveChecked v.mul)) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen
        (Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat)
        (Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat)
      u.rd = t.rd ∧ u.wr = t.wr ∧ u.sp = t.sp ∧
      (∀ r ∈ preserved, r ≠ .x30 → u.gpr r = t.gpr r) ∧
      Frame (keygenDeriveWr s ++ [below (randomBase s) v.stack]) t.mem u.mem ∧
      ((u.gpr .x0).setWidth 32).toNat = Spec.Dsa.signStatus res ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
        res.getD (List.replicate (s.gpr .x1).toNat 0) ∧
      (∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) := by
  obtain ⟨hc, hcw⟩ := keygen_derive_covers h hrd hwr
  have hd := v.deriveCheckedDepth
  have hb := v.stackBound
  refine WP.callFV v.deriveCheckedVerified.1
    (keygen_derive_checked_pre h hsp hw hdi hsi hdx hcx h8 h9 h6 h7 hparams hck) hc hcw
    (fun u hur huw husp hf huc hv hp => ?_) (by omega_using [hd, hb])
  sig_post [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs] at hp
  simp only [hdi, hsi, hdx, hcx, h8, h9, h6] at hp
  refine ⟨hur, huw, husp, huc, ?_, hp.1, hp.2, hv⟩
  rw [hsp] at hf
  exact Frame.below_mono hf hd (by omega_using [hb])

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyGenerate`, which this module and modules that import it used -/

section

/-! # Key generation after an accepted domain: x sampled, then the key derived -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_storeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.sp = B) :
    WP isa (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr))) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ u.gpr .x4 = t.gpr .x0 - 1 ∧
      Keep [.x4, .x15] t u := by
  refine WP.mono (WP.keep [.x4, .x15] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ u.gpr .x4 = t.gpr .x0 - 1)
    ?_ rfl rfl rfl) fun u ⟨hu, hk⟩ => ⟨hu.1, hu.2, hk⟩
  unfold Random.store
  brun [exec_addSp (show Random.oStatus < 4096 by decide), hsp, hs.st (d := Random.oStatus) (by decide)]
  rfl

theorem keygen_writeStatus_ok {t : State} {B : Addr} (hs : Scr t B Random.frameBytes) (hsp : t.sp = B) :
    WP isa (.block (Random.store Random.oStatus .x0)) t fun u =>
      u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0) ∧ Keep [.x15] t u := by
  refine WP.keep [.x15] (Q := fun u =>
    u.mem = t.mem.writeW (off B Random.oStatus) (t.gpr .x0)) ?_ rfl rfl rfl
  unfold Random.store
  brun [exec_addSp (show Random.oStatus < 4096 by decide), hsp, hs.st (d := Random.oStatus) (by decide)]

/-- Writing the status keeps the frame state. -/
theorem KeygenState.write_status {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) {v : BitVec 64}
    (hm : u.mem = t.mem.writeW (off (randomBase s) Random.oStatus) v) (hk : Keep randomVolatile t u)
    : KeygenState h used u := by
  have hf : Outside (randomBase s) Random.oStatus 8 t.mem u.mem := by
    rw [hm]; exact writeW_outside _ _ _ (by decide)
  refine ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd hd' => hf.word (Or.inl (by
    change d + 8 ≤ 192; omega_using [hd'])) (by omega_using [hd'])) hk (hf.word (by decide) (by decide))

/-- Writes to the frame's outgoing-argument words keep the frame state. -/
theorem KeygenState.of_outgoing {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) (hf : Outside (randomBase s) 0 8 t.mem u.mem)
    (hk : Keep randomVolatile t u) : KeygenState h used u :=
  ht.of_frame (InScr.of_outside hf (by decide)) (fun d hd _ => hf.word (Or.inr (by omega_using [hd])) (by omega_arith)) hk
    (hf.word (by decide) (by decide))

theorem keygen_bytes_params {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    (ht : KeygenState h used t) :
    Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params := by
  apply List.ext_getElem (by simp only [keygenInput, bytesAt_length])
  intro i h₁ h₂
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
  exact ht.params.val i h₂

/-- What generation leaves for the finish. -/
def KeygenGenerated {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (u : State) : Prop :=
  KeygenState h (keygenResult s).used u ∧
  word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (keygenResult s).status ∧
  ((keygenResult s).status = 1 → Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat =
    (keygenResult s).key.getD (List.replicate (s.gpr .x1).toNat 0))

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyDeriveStep`, which only this module used -/

section

/-! # Derive the key and restore the generation controller's state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s} {used k : Nat}
    (ht : KeygenState h used t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k)
    (hc : Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true) :
    WP isa (.seq (.block GenerateKey.deriveArgs)
      (.seq (.call (keygenDeriveName v) (Generate.deriveChecked v.mul)) (.block GenerateKey.keepStatus))) t fun u =>
      let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k)
      KeygenState h used u ∧
      word u.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 (Spec.Dsa.signStatus res) ∧
      Spec.Rsa.bytesAt u.mem (s.gpr .x0) (s.gpr .x1).toNat = res.getD (List.replicate (s.gpr .x1).toNat 0) := by
  refine WP.seq (WP.mono (keygen_deriveArgs_saved ht.scr ht.sp ht.saved)
    fun a ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hw, _, hargs, hka⟩ => ?_)
  have ha := ht.of_outgoing hargs (hka.mono (by decide))
  have hnA : Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k := by
    have hq : (s.gpr .x6).toNat ≤ 32 := by
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega_using [hl]
    exact (random_outside_bytes hargs (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega_using [hq]) (Or.inr (show 0 + 8 ≤ Random.oNonce by decide))).trans hnonce
  refine WP.seq (WP.mono (keygen_derive_call v h ha.sp hw hdi hsi hdx hcx h8 h9 h6 h7 ha.rd ha.wr
    (keygen_bytes_params ha) hc)
    fun b ⟨hbr, hbw, hbsp, hbc, hf, hst, hout, hvb⟩ => ?_)
  rw [keygen_bytes_params ha, hnA] at hst hout
  have hoF : (⟨s.gpr .x0, (s.gpr .x1).toNat⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackOut.sub_left (keygen_frame_sub h)).symm
  have hsF : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  have hwrs : ∀ r ∈ keygenDeriveWr s, r.Disjoint ⟨randomBase s, Random.frameBytes⟩ := by
    intro r hr
    simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hoF
    · exact hsF
  have hbl := (random_frame_words (keygen_call_frameBytes h hwrs hf) (d := RandomSign.oLink) (by decide)).trans ha.link
  unfold GenerateKey.keepStatus
  rw [WP.block_append_iff]
  refine WP.mono (keygen_restore_ok (ha.scr.congr hbw) (hbsp.trans ha.sp))
    fun c ⟨hcl, hcx, hcm, hkc⟩ => ?_
  have hcc : ∀ r ∈ preserved, c.gpr r = a.gpr r := by
    intro r hr
    by_cases hl : r = .x30
    · subst r
      exact (hcl.trans hbl).trans (ha.callee .x30 (by decide)).symm
    · exact (hkc.gpr r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)).trans (hbc r hr hl)
  obtain ⟨hc, _⟩ := ha.after_call (wr := keygenDeriveWr s) hwrs
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outParams
      · exact h.paramsScratch.symm)
    (fun r hr => by
      simp only [keygenDeriveWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h.outRand
      · exact h.randScratch.symm)
    (by rw [hcm]; exact hf) (hkc.rd.trans hbr) (hkc.wr.trans hbw) (hkc.sp.trans hbsp) hcc
    (fun r hr => (hkc.vcs r hr).trans (hvb r hr))
  refine WP.mono (keygen_writeStatus_ok hc.scr hc.sp) fun u ⟨hum, hku⟩ => ?_
  refine ⟨hc.write_status hum (hku.mono (by decide)), ?_, ?_⟩
  · rw [hum, word_writeW_self, hcx]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hst ⊢
    rw [hst]
    rfl
  · have hp := random_private_bytes
      (InScr.of_outside (writeW_outside c.mem (randomBase s) (c.gpr .x0)
        (d := Random.oStatus) (by decide)) (by decide)) hoF (Nat.le_of_lt (s.gpr .x1).isLt)
    rw [hum, hp, hcm]
    exact hout

end VG.Proof.Dsa.AArch64

end

end


/-! # Key generation after an accepted domain: the sampler, then the derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_sampleStatus_le (S : Spec.Dsa.Random.Sample) : VG.Proof.Dsa.Random.sampleStatus S ≤ 2 := by
  unfold VG.Proof.Dsa.Random.sampleStatus; split
  · decide
  · split <;> decide

/-- The draw and its status stored: the frame state, the flag for success, and x. -/
theorem keygen_sampled {extra : Nat} {s t b : State} {h : GenerateKeyABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)} {draws : Nat} (ht : KeygenState h 0 t)
    (hrb : RandomReady (keygenContextOf h t.mem hq) 0 draws b) (hkb : Keep randomVolatile t b)
    :
    WP isa (.seq Random.sample (.block (Random.store Random.oStatus .x0 ++ ([.subImm .x .x4 .x0 1] : List Instr)))) b
      fun d =>
        KeygenState h (keygenDraw s).used d ∧
        d.gpr .x4 = BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) - 1 ∧
        word d.mem (randomBase s) Random.oStatus =
          BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) ∧
        (∀ k, (keygenDraw s).scalar = some k →
          Spec.Rsa.bytesAt d.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
            Spec.Dsa.encodeBE (s.gpr .x6).toNat k) := by
  have hd : randomRemaining (keygenContextOf h t.mem hq) 0 128 = keygenDraw s := by
    unfold randomRemaining; rfl
  refine WP.seq (WP.mono (random_sample_encoded hq hrb)
    fun c ⟨hcax, _, _, hnonce, _, ⟨draws', hrc⟩, hkc⟩ => ?_)
  rw [hd, Nat.zero_add] at hrc
  rw [hd] at hcax hnonce
  have hkc' : Keep randomVolatile b c := hkc.mono (by decide)
  have hkt : Keep randomVolatile t c := (hkb.trans hkc').mono (by decide)
  have hsc : KeygenState h (keygenDraw s).used c :=
    ht.of_ready hrc hkt
  refine WP.mono (keygen_storeStatus_ok hsc.scr hsc.sp) fun d ⟨hdm, hdz, hkd⟩ => ?_
  have hsd := hsc.write_status hdm (hkd.mono (by decide))
  rw [hcax] at hdm hdz
  refine ⟨hsd, hdz, by rw [hdm, word_writeW_self], fun k hk => ?_⟩
  have hn := hnonce k hk
  simp only [keygenContextOf, keygen_q_length h] at hn
  have hql : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  rw [hdm]
  exact (random_outside_bytes (writeW_outside _ _ _ (by decide))
    (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by unfold Random.oNonce; omega_using [hql])
    (Or.inr (by decide))).trans hn

theorem keygen_generate (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5)
    (hc : keygenChecked s = true) :
    WP isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveChecked v.mul)) t
      (KeygenGenerated h) := by
  have hq := keygen_q_valid h hc
  have hres := keygen_result_checked h hc
  unfold GenerateKey.generate
  refine WP.seq (WP.mono (keygen_prepare ht hQ hq) fun b ⟨hbz, ⟨draws, hrb⟩, hkb⟩ => ?_)
  refine WP.ite false (by simp [eval, State.read, hbz]) (fun he => Bool.noConfusion he) fun _ => ?_
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_sampled ht hrb hkb) fun d ⟨hsd, hdz, hdw, hnd⟩ => ?_)
  have hlt : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (keygen_sampleStatus_le _) (by decide)
  cases hx : (keygenDraw s).scalar with
  | none =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) ≠ 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]; split <;> decide
    refine WP.ite false (by
      change some (d.gpr .x4 == (0#64)) = some false
      rw [hdz]
      congr 1
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro he
      apply hs1
      have he' : BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus (keygenDraw s)) = 1 :=
        by simpa only [BitVec.sub_eq_iff_eq_add, BitVec.zero_add] using he
      have := congrArg BitVec.toNat he'
      rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at this)
      (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.block_nil ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hsd, hdw, fun h1 => absurd h1 hs1⟩
  | some k =>
    have hs1 : VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) = 1 := by
      simp only [VG.Proof.Dsa.Random.sampleStatus, hx]
    rw [hs1] at hdz
    refine WP.ite true (by change some (d.gpr .x4 == (0#64)) = some true; rw [hdz]; rfl) (fun _ => ?_) (fun he => Bool.noConfusion he)
    refine WP.mono (keygen_derive_step v hsd (hnd k hx) hc) fun u ⟨hu, hw, hb⟩ => ?_
    unfold KeygenGenerated
    rw [hres]
    simp only [hx]
    exact ⟨hu, hw, fun _ => hb⟩

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyFinish`, which only this module used -/

section

/-! # Key generation's finish: the status, the key or zeros, and the draws used -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

structure KeygenBodyPost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  sp : t.sp = randomBase s
  rd : t.rd = s.rd
  wr : t.wr = ⟨randomBase s, Random.frameBytes⟩ :: s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.key.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem keygen_bytes_zero {m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, m (p + BitVec.ofNat 64 i) = 0) :
    Spec.Rsa.bytesAt m p n = List.replicate n 0 := by
  apply List.ext_getElem (by simp [Spec.Rsa.bytesAt])
  intro i hi _
  simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
  exact h i (by simpa only [bytesAt_length] using hi)

theorem keygen_finish_result {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    {result : Spec.Dsa.GenerateKeyResult} (hr : KeygenState h result.used t)
    (hstatus : word t.mem (randomBase s) Random.oStatus = BitVec.ofNat 64 result.status)
    (houtput : result.status = 1 → Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
      result.key.getD (List.replicate (s.gpr .x1).toNat 0))
    (hbound : result.status ≤ 2) (hkey : result.status ≠ 1 → result.key = none) :
    WP isa RandomSign.finish t (KeygenBodyPost s result) := by
  have houtlen : 0 < (s.gpr .x1).toNat := by
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl, ho]
  have hptr : word t.mem (randomBase s) Random.oUsedPtr = s.gpr .x2 :=
    hr.saved (56, s.gpr .x2) (by simp [keygenSavedValues])
  have hframeOut := h.stackOut.sub_left (keygen_frame_sub h)
  have hframeUsed := h.stackUsed.sub_left (keygen_frame_sub h)
  have hsep (d : Nat) (hd : d + 8 ≤ Random.frameBytes) :
      Mem.Sep (off (randomBase s) d) 8 (s.gpr .x0) (s.gpr .x1).toNat :=
    (hframeOut.sub_left (Offset.sub_base _ hd)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  have hused : InRegions t.wr (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact ⟨⟨s.gpr .x2, 8⟩, by rw [hr.wr, h.wr]; simp, Region.contains_self _ _⟩
  have hsepUsed : Mem.Sep (off (randomBase s) Random.oStatus) 8 (word t.mem (randomBase s) Random.oUsedPtr) 8 := by
    rw [hptr]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)
  refine WP.mono (random_finish_ok (B := randomBase s) (op := s.gpr .x0) (k := (s.gpr .x1).toNat)
    hr.scr hr.sp
    (hr.saved (40, s.gpr .x0) (by simp [keygenSavedValues]))
    (by simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .x1) (by simp [keygenSavedValues]))
    houtlen (s.gpr .x1).isLt
    (fun j hj => ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .x1).isLt)⟩)
    hsep hused hsepUsed)
    fun u ⟨hret, ⟨m, hgood, hbad, hwords, hum⟩, hk⟩ => ?_
  have hpM : word m (randomBase s) Random.oUsedPtr = s.gpr .x2 := (hwords _ (by decide)).trans hptr
  have huM : word m (randomBase s) Random.oUsed = BitVec.ofNat 64 result.used := by
    rw [hwords _ (by decide)]
    exact hr.usedWord
  have hkv : Keep randomVolatile t u := hk.mono (by decide)
  refine ⟨hk.sp.trans hr.sp, hk.rd.trans hr.rd, hk.wr.trans hr.wr,
    hret.trans hstatus, ?_, ?_,
    fun r hc => (hkv.gpr r (random_saved_not_volatile hc)).trans (hr.callee r hc),
    fun r hc => (hk.vcs r hc).trans (hr.vectors r hc), ?_⟩
  · rw [hum, random_publish_output hframeOut.symm (by
      rw [hpM]; exact h.outUsed.sep (Region.contains_self _ _) (Region.contains_self _ _)) (s.gpr .x1).isLt]
    by_cases hs : result.status = 1
    · have hw : word t.mem (randomBase s) Random.oStatus = 1 := by rw [hstatus, hs]; rfl
      rw [hgood hw]
      exact houtput hs
    · have hw : word t.mem (randomBase s) Random.oStatus ≠ 1 := by
        intro he
        rw [hstatus] at he
        have hn := congrArg BitVec.toNat he
        change result.status % 2 ^ 64 = 1 at hn
        omega_using [hbound, hs, hn]
      rw [hkey hs]
      exact keygen_bytes_zero (hbad hw)
  · rw [hum, ← hpM, random_publish_used, huM]
  · intro i hi
    rw [hum]
    apply random_publish_nonce_zero _ i hi
    rw [hpM]
    exact (hframeUsed.sub_left (Offset.sub_base _ (by decide))).sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- Key generation's status is at most 2, and only success returns a key. -/
theorem keygen_result_bounds {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    (keygenResult s).status ≤ 2 ∧ ((keygenResult s).status ≠ 1 → (keygenResult s).key = none) := by
  by_cases hc : keygenChecked s = true
  · rw [keygen_result_checked h hc]
    cases hx : (keygenDraw s).scalar with
    | none => exact ⟨keygen_sampleStatus_le _, fun _ => rfl⟩
    | some k =>
      dsimp only
      unfold Spec.Dsa.signStatus
      cases hd : Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
        (Spec.Dsa.encodeBE (keygenInput s).qLen k) with
      | none => exact ⟨by decide, fun _ => rfl⟩
      | some key => exact ⟨by simp, fun hn => absurd (by simp) hn⟩
  · have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
      simp only [keygenInput, bytesAt_length]; exact h.paramsLength
    unfold keygenResult
    rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
      h.lengths hpl]
    simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
      = false from Bool.eq_false_iff.mpr hc, Bool.false_eq_true, ↓reduceIte]
    exact ⟨by decide, fun _ => trivial⟩

end VG.Proof.Dsa.AArch64

end

end

/-! # Key generation's functional correctness against its shared contract -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/GenerateKeyBody.lean`, which only this module imported.
section

/-! # Key generation's body: entry, the domain check, generation, the finish -/

section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_result_unchecked {extra : Nat} {s : State} (h : GenerateKeyABI extra s)
    (hc : keygenChecked s = false) : keygenResult s = ⟨none, 0, 0, [4]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = false from hc, Bool.false_eq_true, ↓reduceIte]

theorem keygen_body (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.mul) (Generate.deriveChecked v.mul))
      (allocated Random.frameBytes s) (KeygenBodyPost s (keygenResult s)) := by
  have hb := keygen_result_bounds h
  unfold GenerateKey.body
  refine WP.seq (WP.mono (keygen_head h) fun t ⟨ht, hst, hQ, hdi, hsi, hdx, hcx, h8, h9⟩ => ?_)
  apply WP.assoc
  refine WP.seq (WP.mono (keygen_check_step v ht hdi hsi hdx hcx h8 h9) fun u ⟨hu, hw, hax⟩ => ?_)
  refine WP.seq ?_
  cases hc : keygenChecked s with
  | false =>
    rw [hc] at hax
    refine WP.ite true (by simp [eval, State.read, hax]) (fun _ => WP.block_nil ?_)
      (fun he => Bool.noConfusion he)
    have hr := keygen_result_unchecked h hc
    rw [hr] at hb ⊢
    exact keygen_finish_result hu (by rw [hw _ (by decide), hst]; rfl) (fun he => absurd he (by decide))
      hb.1 hb.2
  | true =>
    rw [hc] at hax
    refine WP.ite false (by simp [eval, State.read, hax]) (fun he => Bool.noConfusion he) fun _ => ?_
    refine WP.mono (keygen_generate v hu (by rw [hw _ (by decide)]; exact hQ) hc)
      fun x ⟨hx, hxs, hxo⟩ => keygen_finish_result hx hxs hxo hb.1 hb.2

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_sp (v : Backend) :
    (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
      (Generate.deriveChecked v.mul)).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_forall (fun _ => rfl) _

structure KeygenCodePost (s : State) (result : Spec.Dsa.GenerateKeyResult) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  status : t.gpr .x0 = BitVec.ofNat 64 result.status
  output : Spec.Rsa.bytesAt t.mem (s.gpr .x0) (s.gpr .x1).toNat =
    result.key.getD (List.replicate (s.gpr .x1).toNat 0)
  used : t.mem.readW (s.gpr .x2) 64 = BitVec.ofNat 64 result.used
  callee : ∀ r ∈ preserved, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  vectors : ∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64
  nonce : ∀ i < 32, t.mem (off (randomBase s) (200 + i)) = 0

theorem keygen_code (v : Backend) {s : State} (h : GenerateKeyABI v.stack s) :
    WP isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
      (Generate.deriveChecked v.mul)) s (KeygenCodePost s (keygenResult s)) := by
  apply keygen_frame_ok h
  refine WP.mono (keygen_body v h) fun t ht => ⟨ht.sp, ht.wr, ?_⟩
  refine ⟨ht.rd, by change t.wr.tail = _; rw [ht.wr]; rfl, ht.status, ht.output, ht.used,
    ht.callee, ?_, ht.vectors, ht.nonce⟩
  change t.sp + BitVec.ofNat 64 Random.frameBytes = s.sp
  rw [ht.sp, randomBase, BitVec.sub_add_cancel]

theorem keygen_shared_post {extra : Nat} {s t : State} (h : GenerateKeyABI extra s)
    (hp : KeygenCodePost s (keygenResult s) t) :
    (Spec.Dsa.generateKeyContract abi (extra + 256)).post s t := by
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  sig_post [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  have hb : (keygenResult s).status < 2 ^ 32 := by
    have := (keygen_result_bounds h).1
    omega_using [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [hp.status]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 2 ^ 64),
      Nat.mod_eq_of_lt hb]
    rfl
  · exact hp.output
  · change Spec.Rsa.wordsAt t.mem (s.gpr .x2) 1 = _
    simp only [Spec.Rsa.wordsAt, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, Nat.mul_zero, BitVec.add_zero, hp.used]
    rfl

theorem keygen_correct (v : Backend) (s : State)
    (hpre : (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s) :
    ∃ trace t, Exec isa (GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Generate.checkParameters v.mul) (Generate.deriveChecked v.mul)) s trace t ∧
      abiPreserved s t ∧ (Spec.Dsa.generateKeyContract abi (v.stack + 256)).post s t := by
  have h := generateKeyABI_of hpre
  obtain ⟨trace, t, he, hp⟩ := keygen_code v h
  exact ⟨trace, t, he, ⟨hp.callee, hp.sp, hp.vectors⟩, keygen_shared_post h hp⟩

end VG.Proof.Dsa.AArch64
