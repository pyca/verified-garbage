module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyBlockCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Dsa.AArch64.DeriveCheckedVerified
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
import VerifiedGarbage.Proof.Dsa.AArch64.ParametersVerified
public import VerifiedGarbage.Proof.Dsa.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleAgreement
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishAgreement
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeySample

/-! ### `Dsa.AArch64.GenerateKeyPublic`, which only this module used -/

section

/-! # Key generation's public inputs, and what its leak fixes -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

structure KeygenPublicAgree (s t : State) : Prop where
  sp : s.sp = t.sp
  regs : ∀ r ∈ argRegs, s.gpr r = t.gpr r
  args : ∀ i < 3, stackArg s i = stackArg t i
  params : (keygenInput s).params = (keygenInput t).params

theorem KeygenPublicAgree.base {s t : State} (h : KeygenPublicAgree s t) : randomBase s = randomBase t := by
  unfold randomBase
  rw [h.sp]

theorem KeygenPublicAgree.pLen {s t : State} (h : KeygenPublicAgree s t) :
    (keygenInput s).pLen = (keygenInput t).pLen :=
  congrArg BitVec.toNat (h.regs .x5 (by decide))

theorem KeygenPublicAgree.qLen {s t : State} (h : KeygenPublicAgree s t) :
    (keygenInput s).qLen = (keygenInput t).qLen :=
  congrArg BitVec.toNat (h.regs .x6 (by decide))

theorem KeygenPublicAgree.checked {s t : State} (h : KeygenPublicAgree s t) : keygenChecked s = keygenChecked t := by
  unfold keygenChecked
  rw [h.pLen, h.qLen, h.params]

theorem KeygenPublicAgree.qBytes {s t : State} (h : KeygenPublicAgree s t) : keygenQBytes s = keygenQBytes t := by
  unfold keygenQBytes
  rw [h.pLen, h.qLen, h.params]

theorem keygen_public_related {extra : Nat} {s t : State}
    (h : (Spec.Dsa.generateKeyContract abi (extra + 256)).pub s t) :
    KeygenPublicAgree s t ∧ (keygenResult s).status = (keygenResult t).status ∧
      (keygenResult s).used = (keygenResult t).used ∧ (keygenResult s).trace = (keygenResult t).trace := by
  sig_pub [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, hdi, hsi, hdx, hcx, h8, h9, h6, h7, a0, a1, a2⟩ := h
  have hregs : ∀ r ∈ argRegs, s.gpr r = t.gpr r := by
    intro r hr
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hdi, hsi, hdx, hcx, h8, h9, h6, h7]
  have hargs : ∀ i < 3, stackArg s i = stackArg t i := by
    intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega_using [hi]
    rcases hc with rfl | rfl | rfl
    exacts [a0, a1, a2]
  change ((keygenInput s).params.map (·.toNat) ++ [(keygenResult s).status, (keygenResult s).used] ++
      (keygenResult s).trace) = ((keygenInput t).params.map (·.toNat) ++
      [(keygenResult t).status, (keygenResult t).used] ++ (keygenResult t).trace) at hleak
  rw [List.append_assoc, List.append_assoc] at hleak
  have hlen : ((keygenInput s).params.map (·.toNat)).length = ((keygenInput t).params.map (·.toNat)).length := by
    simp only [keygenInput, List.length_map, bytesAt_length, h8]
  obtain ⟨hp, hrest⟩ := List.append_inj hleak hlen
  have hp' := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hp
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hrest
  exact ⟨⟨hsp, hregs, hargs, hp'⟩, hrest⟩

theorem keygen_sample_trace_le (q fuel : Nat) (rand : List Byte) :
    ∀ x ∈ (Spec.Dsa.Random.sample q fuel rand).trace, x ≤ 4 := by
  induction fuel generalizing rand with
  | zero => simp [Spec.Dsa.Random.sample]
  | succ fuel ih =>
    rw [Spec.Dsa.Random.sample]
    split
    · simp
    · dsimp only
      split
      · simp
      · split
        · simp
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · decide
          · exact ih _ x hx

/-- The sampler's trace is the result's trace without the derivation's mark. -/
theorem keygen_draw_trace {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (hc : keygenChecked s = true) :
    (keygenResult s).trace.filter (fun x => decide (x ≤ 4)) = (keygenDraw s).trace := by
  have hle := keygen_sample_trace_le (Spec.Dsa.decodeBE (keygenQBytes s)) 128 (keygenInput s).rand
  rw [keygen_result_checked h hc]
  cases (keygenDraw s).scalar with
  | none => exact List.filter_eq_self.mpr fun x hx => decide_eq_true (hle x hx)
  | some k =>
    dsimp only
    rw [List.filter_append, List.filter_eq_self.mpr fun x hx => decide_eq_true (hle x hx)]
    split <;> exact List.append_nil _

end VG.Proof.Dsa.AArch64

end

end

/-! ### `Dsa.AArch64.GenerateKeyGenerateCT`, which only this module used -/

section

/-! ### `Dsa.AArch64.GenerateKeyCallCT`, which only this module used -/

section

/-! # Key generation's calls, by their callees' leakage contracts -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.Dsa.AArch64

/-- The registers the domain check is called with. -/
def KeygenCheckRegs (s t : State) : Prop :=
  t.gpr .x0 = s.gpr .x3 ∧ t.gpr .x1 = s.gpr .x4 ∧ t.gpr .x2 = s.gpr .x5 ∧
    t.gpr .x3 = s.gpr .x6 ∧ t.gpr .x4 = stackArg s 1 ∧ t.gpr .x5 = stackArg s 2

def KeygenCheckRelated (v : Backend) (a b : State) : Prop :=
  ∃ s t, ∃ hs : GenerateKeyABI v.stack s, ∃ ht : GenerateKeyABI v.stack t,
    KeygenState hs 0 a ∧ KeygenState ht 0 b ∧ KeygenCheckRegs s a ∧ KeygenCheckRegs t b ∧
    KeygenPublicAgree s t

theorem keygen_check_ct (v : Backend) : RelCT isa (KeygenCheckRelated v)
    (.call (keygenCheckName v) (Generate.checkParameters v.mul)) (fun _ _ => True) := by
  apply VG.AArch64.RelCT.callExDit v.parametersVerified.1 v.parametersVerified.2.1 v.parametersNoDit (fun _ _ h => h)
  intro a b ⟨s, t, hs, ht, ha, hb, ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, hp⟩
  obtain ⟨hca, hwa⟩ := keygen_check_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := keygen_check_covers ht hb.rd hb.wr
  refine ⟨keygenCheckRd s, keygenCheckWr s, keygenCheckRd t, keygenCheckWr t,
    keygen_check_pre hs ha.sp a1 a2 a3 a4 a5 a6, keygen_check_pre ht hb.sp b1 b2 b3 b4 b5 b6, ?_,
    hca, hwa, hcb, hwb⟩
  sig_pub [Proof.Dsa.checkParametersContract, Proof.Dsa.checkParametersSig, abi, argRegs, stackArgs_zero]
  rw [a1, a2, b1, b2, keygen_bytes_params ha, keygen_bytes_params hb, hp.params,
    a3, a4, a5, a6, b3, b4, b5, b6, ha.sp, hb.sp, hp.base]
  exact ⟨rfl, rfl, hp.regs .x3 (by decide), hp.regs .x4 (by decide), hp.regs .x5 (by decide),
    hp.regs .x6 (by decide), hp.args 1 (by decide), hp.args 2 (by decide)⟩

/-- The registers and outgoing words the derivation is called with. -/
def KeygenDeriveRegs (s t : State) : Prop :=
  t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x3 ∧ t.gpr .x3 = s.gpr .x4 ∧
    t.gpr .x4 = s.gpr .x5 ∧ t.gpr .x5 = off (randomBase s) Random.oNonce ∧
    t.gpr .x6 = s.gpr .x6 ∧ t.gpr .x7 = stackArg s 1 ∧
    word t.mem (randomBase s) 0 = stackArg s 2

/-- The derivation's status from the x in the frame. -/
def keygenDeriveStatus (s a : State) : Nat :=
  Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    (Spec.Rsa.bytesAt a.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat))

def KeygenDeriveRelated (v : Backend) (a b : State) : Prop :=
  ∃ s t, ∃ hs : GenerateKeyABI v.stack s, ∃ ht : GenerateKeyABI v.stack t, ∃ ua ub : Nat,
    KeygenState hs ua a ∧ KeygenState ht ub b ∧ KeygenDeriveRegs s a ∧ KeygenDeriveRegs t b ∧
    KeygenPublicAgree s t ∧ keygenDeriveStatus s a = keygenDeriveStatus t b ∧
    Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params = true ∧
    Spec.Dsa.checkParametersBytes (keygenInput t).pLen (keygenInput t).qLen (keygenInput t).params = true

theorem keygen_derive_ct (v : Backend) : RelCT isa (KeygenDeriveRelated v)
    (.call (keygenDeriveName v) (Generate.deriveChecked v.mul)) (fun _ _ => True) := by
  apply VG.AArch64.RelCT.callExDit v.deriveCheckedVerified.1 v.deriveCheckedVerified.2.1 v.deriveCheckedNoDit (fun _ _ h => h)
  intro a b ⟨s, t, hs, ht, _, _, ha, hb, ⟨a1, a2, a3, a4, a5, a6, a7, a8, aw⟩, ⟨b1, b2, b3, b4, b5, b6, b7, b8, bw⟩, hp, hst,
    hcs, hct⟩
  obtain ⟨hca, hwa⟩ := keygen_derive_covers hs ha.rd ha.wr
  obtain ⟨hcb, hwb⟩ := keygen_derive_covers ht hb.rd hb.wr
  refine ⟨keygenDeriveRd s, keygenDeriveWr s, keygenDeriveRd t, keygenDeriveWr t,
    keygen_derive_checked_pre hs ha.sp aw a1 a2 a3 a4 a5 a6 a7 a8 (keygen_bytes_params ha) hcs,
    keygen_derive_checked_pre ht hb.sp bw b1 b2 b3 b4 b5 b6 b7 b8 (keygen_bytes_params hb) hct, ?_,
    hca, hwa, hcb, hwb⟩
  have hA : stackArg (a.callEntry.withRegions (keygenDeriveRd s) (keygenDeriveWr s)) 0 = stackArg s 2 :=
    (random_call_stackArg ha.sp _ _ 0).trans aw
  have hB : stackArg (b.callEntry.withRegions (keygenDeriveRd t) (keygenDeriveWr t)) 0 = stackArg t 2 :=
    (random_call_stackArg hb.sp _ _ 0).trans bw
  sig_pub [Spec.Dsa.deriveKeyDomainCheckedContract, Spec.Dsa.deriveKeySig, abi, argRegs, deriveStackArgs]
  simp only [stackArg_withDit, hA, hB, List.getD_cons_succ, List.getD_cons_zero]
  rw [a3, a4, a5, a6, a7, a8, b3, b4, b5, b6, b7, b8,
    keygen_bytes_params ha, keygen_bytes_params hb, a1, a2, b1, b2, ha.sp, hb.sp]
  refine ⟨by rw [hp.base], ?_, hp.regs .x0 (by decide), hp.regs .x1 (by decide), hp.regs .x3 (by decide),
    hp.regs .x4 (by decide), hp.regs .x5 (by decide), by rw [hp.base], hp.regs .x6 (by decide), hp.args 1 (by decide),
    hp.args 2 (by decide)⟩
  have hst' := hst
  unfold keygenDeriveStatus at hst'
  change List.map _ (keygenInput s).params ++ [Spec.Dsa.signStatus (Spec.Dsa.deriveKeyBytes (keygenInput s).pLen
    (keygenInput s).qLen _ _)] = List.map _ (keygenInput t).params ++ [Spec.Dsa.signStatus
    (Spec.Dsa.deriveKeyBytes (keygenInput t).pLen (keygenInput t).qLen _ _)]
  rw [hst', hp.params]

end VG.Proof.Dsa.AArch64

end

end


/-! # Key generation's sampling and derivation leak only its public trace -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_prepare_pre {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5) :
    RandomPreparePre ⟨randomBase s, s.gpr .x3 + s.gpr .x5, keygenQBytes s⟩ t := by
  have hl := h.lengths
  unfold Spec.Dsa.lengthsValid at hl
  refine ⟨ht.scr, ht.sp, hQ, ?_, ?_, ?_, ?_⟩
  · simpa only [Random.oQLen, keygen_q_length h, ofNat_toNat64] using
      ht.saved (88, s.gpr .x6) (by simp [keygenSavedValues])
  · have hh := random_src_take (random_src_drop ht.params (keygenInput s).pLen) (keygenInput s).qLen
    simpa only [keygenQBytes, keygenInput, ofNat_toNat64] using hh
  · change 0 < (keygenQBytes s).length
    rw [keygen_q_length h]
    omega_using [hl]
  · change (keygenQBytes s).length < 2 ^ 64
    rw [keygen_q_length h]
    exact (s.gpr .x6).isLt

theorem keygen_deriveArgs_step {extra : Nat} {s d : State} {h : GenerateKeyABI extra s} {used : Nat}
    (hd : KeygenState h used d) :
    WP isa (.block GenerateKey.deriveArgs) d fun e =>
      KeygenState h used e ∧ KeygenDeriveRegs s e ∧
      Spec.Rsa.bytesAt e.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
        Spec.Rsa.bytesAt d.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat := by
  refine WP.mono (keygen_deriveArgs_saved hd.scr hd.sp hd.saved)
    fun e ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hw, _, hargs, hke⟩ => ?_
  have hq : (s.gpr .x6).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega_using [hl]
  exact ⟨hd.of_outgoing hargs (hke.mono (by decide)), ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hw⟩,
    random_outside_bytes hargs (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega_using [hq]) (Or.inr (show 0 + 8 ≤ Random.oNonce by decide))⟩

theorem keygen_block_nil {a u : State} {tr : List Leak} (e : Exec isa (.block []) a tr u) :
    tr = [] ∧ u = a := by
  cases e with
  | block h => cases h; exact ⟨rfl, rfl⟩

theorem keygen_scalar_of_flag {S : Spec.Dsa.Random.Sample}
    (h : (BitVec.ofNat 64 (VG.Proof.Dsa.Random.sampleStatus S) == 1) = true) : ∃ k, S.scalar = some k := by
  cases hx : S.scalar with
  | some k => exact ⟨k, rfl⟩
  | none =>
    simp only [VG.Proof.Dsa.Random.sampleStatus, hx] at h
    split at h <;> exact absurd h (by decide)

theorem keygen_deriveStatus_eq {extra : Nat} {s t x y : State} {ks kt : Nat}
    (hs : GenerateKeyABI extra s) (ht : GenerateKeyABI extra t)
    (hc : keygenChecked s = true) (hct : keygenChecked t = true)
    (hxs : (keygenDraw s).scalar = some ks) (hxt : (keygenDraw t).scalar = some kt)
    (hstatus : (keygenResult s).status = (keygenResult t).status)
    (hx : Spec.Rsa.bytesAt x.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat ks)
    (hy : Spec.Rsa.bytesAt y.mem (off (randomBase t) Random.oNonce) (t.gpr .x6).toNat =
      Spec.Dsa.encodeBE (t.gpr .x6).toNat kt) :
    keygenDeriveStatus s x = keygenDeriveStatus t y := by
  unfold keygenDeriveStatus
  rw [hx, hy]
  have he := hstatus
  rw [keygen_result_checked hs hc, keygen_result_checked ht hct] at he
  simp only [hxs, hxt] at he
  exact he

theorem keygen_generate_ct (v : Backend) {s t a b : State}
    {hs : GenerateKeyABI v.stack s} {ht : GenerateKeyABI v.stack t}
    (ha : KeygenState hs 0 a) (hb : KeygenState ht 0 b)
    (hQa : word a.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5)
    (hQb : word b.mem (randomBase t) Random.oQ = t.gpr .x3 + t.gpr .x5)
    (hc : keygenChecked s = true) (hp : KeygenPublicAgree s t)
    (hstatus : (keygenResult s).status = (keygenResult t).status)
    (htrace : (keygenResult s).trace = (keygenResult t).trace)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveChecked v.mul)) a tsa u)
    (eb : Exec isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveChecked v.mul)) b tsb w) :
    tsa = tsb := by
  have hct : keygenChecked t = true := hp.checked ▸ hc
  have hqs := keygen_q_valid hs hc
  have hqt := keygen_q_valid ht hct
  have hdq : Spec.Dsa.decodeBE (keygenQBytes s) = Spec.Dsa.decodeBE (keygenQBytes t) := by rw [hp.qBytes]
  have hdt : (keygenDraw s).trace = (keygenDraw t).trace := by
    rw [← keygen_draw_trace hs hc, ← keygen_draw_trace ht hct, htrace]
  have hag : (keygenDraw s).scalar.isSome = (keygenDraw t).scalar.isSome ∧
      VG.Proof.Dsa.Random.sampleStatus (keygenDraw s) = VG.Proof.Dsa.Random.sampleStatus (keygenDraw t) := by
    have hh := hdt
    unfold keygenDraw at hh ⊢
    rw [hdq] at hh ⊢
    exact (VG.Proof.Dsa.Random.sample_trace_agree hh).2
  unfold GenerateKey.generate at ea eb
  cases ea with | seq eaP eaI =>
  cases eb with | seq ebP ebI =>
  have hP := (random_prepare_ct _ _ _ _ _ _ ⟨_, keygen_prepare_pre ha hQa, by
    rw [hp.base, hp.regs .x3 (by decide), hp.regs .x5 (by decide), hp.qBytes]
    exact keygen_prepare_pre hb hQb, ha.sp.trans (hp.base.trans hb.sp.symm)⟩ eaP ebP).1
  obtain ⟨hza, ⟨da, hra⟩, hka⟩ := random_post_of_exec (keygen_prepare ha hQa hqs) eaP
  obtain ⟨hzb, ⟨db, hrb⟩, hkb⟩ := random_post_of_exec (keygen_prepare hb hQb hqt) ebP
  cases eaI with
  | iteT hc' _ => simp [eval, State.read, hza] at hc'
  | iteF _ eaS =>
  cases ebI with
  | iteT hc' _ => simp [eval, State.read, hzb] at hc'
  | iteF _ ebS =>
  cases eaS with | seq eaSa eaR2 => cases eaR2 with | seq eaSt eaI2 =>
  cases ebS with | seq ebSa ebR2 => cases ebR2 with | seq ebSt ebI2 =>
  have hS := random_sample_agreement hra hrb hqs hp.base (hp.regs .x7 (by decide))
    (by change s.gpr .x3 + s.gpr .x5 = t.gpr .x3 + t.gpr .x5
        rw [hp.regs .x3 (by decide), hp.regs .x5 (by decide)])
    hp.qBytes
    (by simp only [keygenContextOf, keygenInput, bytesAt_length, hp.args 0 (by decide)])
    (by simpa only [keygenContextOf, List.drop_zero] using hdt) eaSa ebSa
  have hspa : _ := random_post_of_exec (random_sample_encoded hqs hra) eaSa
  have hspb : _ := random_post_of_exec (random_sample_encoded hqt hrb) ebSa
  obtain ⟨_, ra⟩ := hspa.2.2.2.2.2.1
  obtain ⟨_, rb⟩ := hspb.2.2.2.2.2.1
  have hSt := (keygen_storeStatus_ct _ _ _ _ _ _ (by
    dsimp only
    rw [ra.sp, rb.sp]
    exact hp.base) eaSt ebSt).1
  obtain ⟨hda, hdza, -, hna⟩ := random_post_of_exec (keygen_sampled ha hra hka) (.seq eaSa eaSt)
  obtain ⟨hdb, hdzb, -, hnb⟩ := random_post_of_exec (keygen_sampled hb hrb hkb) (.seq ebSa ebSt)
  have hflag (z : State) (q : Nat) (hz : z.gpr .x4 = BitVec.ofNat 64 q - 1) :
      eval (.zero .x .x4) z = some (BitVec.ofNat 64 q == (1 : BitVec 64)) := by
    change some (z.gpr .x4 == (0#64)) = _
    rw [hz]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add, BitVec.zero_add]
  have hfza := hflag _ _ hdza
  have hfzb := hflag _ _ hdzb
  rw [← hag.2] at hfzb
  cases eaI2 with
  | iteF hca eaN =>
    cases ebI2 with
    | iteT hcb _ => simp only [hfza] at hca; simp only [hfzb] at hcb; rw [hca] at hcb; cases hcb
    | iteF _ ebN =>
      rw [(keygen_block_nil eaN).1, (keygen_block_nil ebN).1, hP, hS, hSt]
  | iteT hca eaT =>
    cases ebI2 with
    | iteF hcb _ => simp only [hfza] at hca; simp only [hfzb] at hcb; rw [hca] at hcb; cases hcb
    | iteT hcb ebT =>
      simp only [hfza, Option.some.injEq] at hca
      simp only [hfzb, Option.some.injEq] at hcb
      obtain ⟨ks, hxs⟩ := keygen_scalar_of_flag hca
      obtain ⟨kt, hxt⟩ := keygen_scalar_of_flag (by rw [← hag.2]; exact hcb)
      cases eaT with | seq eaDA eaR3 => cases eaR3 with | seq eaCall eaK =>
      cases ebT with | seq ebDA ebR3 => cases ebR3 with | seq ebCall ebK =>
      have hDA := (keygen_deriveArgs_ct _ _ _ _ _ _ (by
        dsimp only
        rw [hda.sp, hdb.sp]
        exact hp.base) eaDA ebDA).1
      obtain ⟨hea, hrega, hnea⟩ := random_post_of_exec (keygen_deriveArgs_step hda) eaDA
      obtain ⟨heb, hregb, hneb⟩ := random_post_of_exec (keygen_deriveArgs_step hdb) ebDA
      have hst := keygen_deriveStatus_eq hs ht hc hct hxs hxt hstatus ((hnea).trans (hna ks hxs))
        ((hneb).trans (hnb kt hxt))
      have hCall := (keygen_derive_ct v _ _ _ _ _ _
        ⟨s, t, hs, ht, _, _, hea, heb, hrega, hregb, hp, hst, hc, hct⟩ eaCall ebCall).1
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, aw⟩ := hrega
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, bw⟩ := hregb
      obtain ⟨-, -, huca, -⟩ := random_post_of_exec
        (keygen_derive_call v hs hea.sp aw a1 a2 a3 a4 a5 a6 a7 a8 hea.rd hea.wr (keygen_bytes_params hea) hc) eaCall
      obtain ⟨-, -, hucb, -⟩ := random_post_of_exec
        (keygen_derive_call v ht heb.sp bw b1 b2 b3 b4 b5 b6 b7 b8 heb.rd heb.wr (keygen_bytes_params heb) hct) ebCall
      have hK := (keygen_keepStatus_ct _ _ _ _ _ _ (by
        dsimp only
        rw [huca, hucb, hea.sp, heb.sp]
        exact hp.base) eaK ebK).1
      rw [hP, hS, hSt, hDA, hCall, hK]

end VG.Proof.Dsa.AArch64

end

end

/-! # Complete verification of DSA key generation for every AArch64 backend -/

-- Formerly `VerifiedGarbage/Proof/Dsa/AArch64/GenerateKeyConstantTime.lean`, which only this module imported.
section

/-! # Key generation's leak: the domain, its status, its draws used and its trace -/

section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_finish_public_pre {extra : Nat} {s t : State} {h : GenerateKeyABI extra s} {used : Nat}
    {status : BitVec 64} (hr : KeygenState h used t)
    (hz : word t.mem (randomBase s) Random.oStatus = status) :
    RandomFinishPre (randomFinishPublic s status) t := by
  refine ⟨hr.scr, hr.sp,
    hr.saved (40, s.gpr .x0) (by simp [keygenSavedValues]), ?_,
    hr.saved (56, s.gpr .x2) (by simp [keygenSavedValues]), hz, ?_, (s.gpr .x1).isLt, ?_, ?_⟩
  · change word t.mem (randomBase s) Random.oOutLen = BitVec.ofNat 64 (s.gpr .x1).toNat
    simpa only [Random.oOutLen, ofNat_toNat64] using hr.saved (48, s.gpr .x1) (by simp [keygenSavedValues])
  · change 0 < (s.gpr .x1).toNat
    have hl := h.lengths
    have ho := h.outLength
    unfold Spec.Dsa.lengthsValid at hl
    omega
  · intro j hj
    exact ⟨⟨s.gpr .x0, (s.gpr .x1).toNat⟩, by rw [hr.wr, h.wr]; simp,
      contains_byte _ hj (Nat.le_of_lt (s.gpr .x1).isLt)⟩
  · intro d hd
    exact ((h.stackOut.sub_left (keygen_frame_sub h)).sub_left (Offset.sub_base _ hd)).sep
      (Region.contains_self _ _) (Region.contains_self _ _)

theorem keygen_finish_agreement {extra : Nat} {s t a b : State} {hs : GenerateKeyABI extra s}
    {ht : GenerateKeyABI extra t} {useda usedb : Nat} {status : BitVec 64}
    (ha : KeygenState hs useda a) (hb : KeygenState ht usedb b) (hpub : KeygenPublicAgree s t)
    (hsa : word a.mem (randomBase s) Random.oStatus = status)
    (hsb : word b.mem (randomBase t) Random.oStatus = status)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa RandomSign.finish a tsa u) (eb : Exec isa RandomSign.finish b tsb w) : tsa = tsb := by
  have hpa := keygen_finish_public_pre ha hsa
  have hpb := keygen_finish_public_pre hb hsb
  have he : randomFinishPublic s status = randomFinishPublic t status := by
    unfold randomFinishPublic
    rw [hpub.base, hpub.regs .x0 (by decide), hpub.regs .x1 (by decide), hpub.regs .x2 (by decide)]
  rw [← he] at hpb
  exact (random_finish_ct _ _ _ _ _ _ ⟨_, hpa, hpb, ha.sp.trans (hpub.base.trans hb.sp.symm)⟩ ea eb).1

theorem keygen_alloc_sp (s : State) : (allocated Random.frameBytes s).sp = randomBase s := rfl

theorem keygen_body_ct (v : Backend) {s t : State}
    (hs : GenerateKeyABI v.stack s) (ht : GenerateKeyABI v.stack t) (hp : KeygenPublicAgree s t)
    (hstatus : (keygenResult s).status = (keygenResult t).status)
    (htrace : (keygenResult s).trace = (keygenResult t).trace)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.mul) (Generate.deriveChecked v.mul)) (allocated Random.frameBytes s) tsa u)
    (eb : Exec isa (GenerateKey.body (keygenCheckName v) (keygenDeriveName v)
      (Generate.checkParameters v.mul) (Generate.deriveChecked v.mul)) (allocated Random.frameBytes t) tsb w) :
    tsa = tsb := by
  unfold GenerateKey.body at ea eb
  cases ea with | seq eaA eaR => cases eaR with | seq eaCall eaR2 =>
  cases eaR2 with | seq eaT eaR3 => cases eaR3 with | seq eaI eaF =>
  cases eb with | seq ebA ebR => cases ebR with | seq ebCall ebR2 =>
  cases ebR2 with | seq ebT ebR3 => cases ebR3 with | seq ebI ebF =>
  have hA := (keygen_head_ct _ _ _ _ _ _ (by
    dsimp only
    rw [keygen_alloc_sp, keygen_alloc_sp]
    exact hp.base) eaA ebA).1
  obtain ⟨ha, hsta, hQa, a1, a2, a3, a4, a5, a6⟩ := random_post_of_exec (keygen_head hs) eaA
  obtain ⟨hb, hstb, hQb, b1, b2, b3, b4, b5, b6⟩ := random_post_of_exec (keygen_head ht) ebA
  have hCall := (keygen_check_ct v _ _ _ _ _ _
    ⟨s, t, hs, ht, ha, hb, ⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5, b6⟩, hp⟩ eaCall ebCall).1
  obtain ⟨hua, hwa, haxa⟩ := random_post_of_exec (keygen_check_step v ha a1 a2 a3 a4 a5 a6) (.seq eaCall eaT)
  obtain ⟨hub, hwb, haxb⟩ := random_post_of_exec (keygen_check_step v hb b1 b2 b3 b4 b5 b6) (.seq ebCall ebT)
  obtain ⟨-, -, hspa, -⟩ := random_post_of_exec
    (keygen_check_call v hs ha.sp a1 a2 a3 a4 a5 a6 ha.rd ha.wr) eaCall
  obtain ⟨-, -, hspb, -⟩ := random_post_of_exec
    (keygen_check_call v ht hb.sp b1 b2 b3 b4 b5 b6 hb.rd hb.wr) ebCall
  have hT := (keygen_testCheck_ct _ _ _ _ _ _ (by
    dsimp only
    rw [hspa, hspb, ha.sp, hb.sp]
    exact hp.base) eaT ebT).1
  have hct := hp.checked
  cases hcs : keygenChecked s with
  | false =>
    rw [hcs] at haxa hct
    rw [← hct] at haxb
    cases eaI with
    | iteF hc' _ => simp only [eval, State.read, haxa, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteT _ eaN =>
    cases ebI with
    | iteF hc' _ => simp only [eval, State.read, haxb, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteT _ ebN =>
    obtain ⟨hna, rfl⟩ := keygen_block_nil eaN
    obtain ⟨hnb, rfl⟩ := keygen_block_nil ebN
    have hF := keygen_finish_agreement hua hub hp
      (by rw [hwa _ (by decide), hsta]) (by rw [hwb _ (by decide), hstb]) eaF ebF
    rw [hA, hCall, hT, hna, hnb, hF]
  | true =>
    rw [hcs] at haxa hct
    rw [← hct] at haxb
    cases eaI with
    | iteT hc' _ => simp only [eval, State.read, haxa, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteF _ eaG =>
    cases ebI with
    | iteT hc' _ => simp only [eval, State.read, haxb, Option.some.injEq] at hc'; exact absurd hc' (by decide)
    | iteF _ ebG =>
    have hQa' := (hwa _ (by decide)).trans hQa
    have hQb' := (hwb _ (by decide)).trans hQb
    have hG := keygen_generate_ct v hua hub hQa' hQb' hcs hp hstatus htrace eaG ebG
    obtain ⟨hga, hgsa, -⟩ := random_post_of_exec (keygen_generate v hua hQa' hcs) eaG
    obtain ⟨hgb, hgsb, -⟩ := random_post_of_exec (keygen_generate v hub hQb' hct.symm) ebG
    rw [hstatus] at hgsa
    have hF := keygen_finish_agreement hga hgb hp hgsa hgsb eaF ebF
    rw [hA, hCall, hT, hG, hF]

theorem keygen_alloc {extra : Nat} {s : State} (h : GenerateKeyABI extra s) :
    isa.push (.alloc Random.frameBytes) s = some (allocated Random.frameBytes s) := by
  have hl := h.stackLower
  simp only [isa, push, allocated]
  exact ite_eq_left ⟨by decide, by decide, by decide, by unfold Random.frameBytes; omega⟩

theorem keygen_constantTime (v : Backend) :
    ConstantTime isa (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pub
      (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
        (Generate.deriveChecked v.mul)) := by
  intro s t tsa tsb u w hs ht hpub ea eb
  have hsa := generateKeyABI_of hs
  have hta := generateKeyABI_of ht
  obtain ⟨hp, hstatus, _, htrace⟩ := keygen_public_related hpub
  cases ea with
  | frame hap hab _ =>
    cases eb with
    | frame hbp hbb _ =>
      rw [keygen_alloc hsa, Option.some.injEq] at hap
      rw [keygen_alloc hta, Option.some.injEq] at hbp
      subst hap
      subst hbp
      have hh := keygen_body_ct v hsa hta hp hstatus htrace hab hbb
      simpa only [isa, addrs, List.map_nil, List.nil_append, List.append_nil] using hh

end VG.Proof.Dsa.AArch64
end

end

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Dsa.AArch64

def keygenSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 424 | .x2 => 0x7000 | .x3 => 0x2000
    | .x4 => 276 | .x5 => 128 | .x6 => 20 | .x7 => 0x5000 | _ => 0
  sp := 0x1000000000000
  mem a := if a = 0x1000000000009 then 0x80 else if a = 0x1000000000011 then 0x24 else 0
  rd := [⟨0x2000, 276⟩, ⟨0x5000, 0⟩, ⟨0x1000000000000, 24⟩]
  wr := [⟨0x1000, 424⟩, ⟨0x7000, 8⟩, ⟨0x8000, 73728⟩]

private theorem sat_arg_0 : stackArg keygenSatState 0 = 0 := by decide +kernel
private theorem sat_arg_1 : stackArg keygenSatState 1 = 32768 := by decide +kernel
private theorem sat_arg_2 : stackArg keygenSatState 2 = 9216 := by decide +kernel

theorem keygen_satisfiable (v : Backend) :
    ∃ s, (Spec.Dsa.generateKeyContract abi (v.stack + 256)).pre s := by
  have hb := v.stackBound
  refine ⟨keygenSatState, ?_⟩
  sig_pre [Spec.Dsa.generateKeyContract, Spec.Dsa.generateKeySig, abi, argRegs, keygenStackArgs]
  sig_and_intros
  all_goals try simp only [sat_arg_0, sat_arg_1, sat_arg_2]
  all_goals first
    | (change v.stack + 256 ≤ 281474976710656; omega_using [hb])
    | exact Region.disjoint_of_sep (by decide +kernel)
    | decide +kernel
    | (intro a h₁ h₂; simp only [Region.Contains, stackArgAddr, keygenSatState] at h₁ h₂; bv_omega)

theorem keygen_verified (v : Backend) :
    Verified target (GenerateKey.code (keygenCheckName v) (keygenDeriveName v) (Generate.checkParameters v.mul)
        (Generate.deriveChecked v.mul))
      (Spec.Dsa.generateKeyContract abi (v.stack + 256)) :=
  ⟨keygen_correct v, keygen_constantTime v, keygen_satisfiable v⟩

end VG.Proof.Dsa.AArch64
