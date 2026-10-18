module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyBlockCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleAgreement
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignBodyCT
import VerifiedGarbage.Proof.Framework.Omega

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
    omega
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
    omega
  exact ⟨hd.of_outgoing hargs (hke.mono (by decide)), ⟨hdi, hsi, hdx, hcx, h8, h9, h6, h7, hw⟩,
    random_outside_bytes hargs (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega) (Or.inr (show 0 + 8 ≤ Random.oNonce by decide))⟩

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
    (ea : Exec isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveKey v.mul)) a tsa u)
    (eb : Exec isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveKey v.mul)) b tsb w) :
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
        ⟨s, t, hs, ht, _, _, hea, heb, hrega, hregb, hp, hst⟩ eaCall ebCall).1
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, aw⟩ := hrega
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, bw⟩ := hregb
      obtain ⟨-, -, huca, -⟩ := random_post_of_exec
        (keygen_derive_call v hs hea.sp aw a1 a2 a3 a4 a5 a6 a7 a8 hea.rd hea.wr) eaCall
      obtain ⟨-, -, hucb, -⟩ := random_post_of_exec
        (keygen_derive_call v ht heb.sp bw b1 b2 b3 b4 b5 b6 b7 b8 heb.rd heb.wr) ebCall
      have hK := (keygen_keepStatus_ct _ _ _ _ _ _ (by
        dsimp only
        rw [huca, hucb, hea.sp, heb.sp]
        exact hp.base) eaK ebK).1
      rw [hP, hS, hSt, hDA, hCall, hK]

end VG.Proof.Dsa.AArch64
