module

import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyBlockCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareCT
public import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeyCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSampleAgreement
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignBodyCT
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.GenerateKeySampled
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSample
import VerifiedGarbage.Proof.Dsa.X86_64.RandomMemory
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Key generation's sampling and derivation leak only its public trace -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem keygen_prepare_pre {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9) :
    RandomPreparePre ⟨randomBase s, s.gpr .rcx + s.gpr .r9, keygenQBytes s⟩ t := by
  have hl := h.lengths
  unfold Spec.Dsa.lengthsValid at hl
  refine ⟨ht.scr, ht.sp, hQ, ?_, ?_, ?_, ?_⟩
  · simpa only [Random.oQLen, keygen_q_length h, ofNat_toNat64] using
      ht.saved (88, stackArg s 0) (by simp [keygenSavedValues])
  · have hh := random_src_take (random_src_drop ht.params (keygenInput s).pLen) (keygenInput s).qLen
    simpa only [keygenQBytes, keygenInput, ofNat_toNat64] using hh
  · change 0 < (keygenQBytes s).length
    rw [keygen_q_length h]
    omega
  · change (keygenQBytes s).length < 2 ^ 64
    rw [keygen_q_length h]
    exact (stackArg s 0).isLt

theorem keygen_deriveArgs_step {extra : Nat} {s d : State} {h : GenerateKeyABI extra s} {used : Nat}
    (hd : KeygenState h used d) :
    WP isa (.block GenerateKey.deriveArgs) d fun e =>
      KeygenState h used e ∧ KeygenDeriveRegs s e ∧
      Spec.Rsa.bytesAt e.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
        Spec.Rsa.bytesAt d.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat := by
  refine WP.mono_mx (by decide) (keygen_deriveArgs_saved hd.scr hd.sp hd.saved)
    fun e ⟨hdi, hsi, hdx, hcx, h8, h9, hw, _, hargs, hke⟩ hmxe => ?_
  have hq : (stackArg s 0).toNat ≤ 32 := by
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  exact ⟨hd.of_outgoing hargs (hke.mono (by decide)) hmxe, ⟨hdi, hsi, hdx, hcx, h8, h9, hw⟩,
    random_outside_bytes hargs (show Random.oNonce + (stackArg s 0).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega) (Or.inr (show 0 + 24 ≤ Random.oNonce by decide))⟩

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
    (hx : Spec.Rsa.bytesAt x.mem (off (randomBase s) Random.oNonce) (stackArg s 0).toNat =
      Spec.Dsa.encodeBE (stackArg s 0).toNat ks)
    (hy : Spec.Rsa.bytesAt y.mem (off (randomBase t) Random.oNonce) (stackArg t 0).toNat =
      Spec.Dsa.encodeBE (stackArg t 0).toNat kt) :
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
    (hQa : word a.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9)
    (hQb : word b.mem (randomBase t) Random.oQ = t.gpr .rcx + t.gpr .r9)
    (hc : keygenChecked s = true) (hp : KeygenPublicAgree s t)
    (hstatus : (keygenResult s).status = (keygenResult t).status)
    (htrace : (keygenResult s).trace = (keygenResult t).trace)
    {tsa tsb : List Leak} {u w : State}
    (ea : Exec isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveKey v.sq v.mul)) a tsa u)
    (eb : Exec isa (GenerateKey.generate (keygenDeriveName v) (Generate.deriveKey v.sq v.mul)) b tsb w) :
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
  cases ea with | seq eaP eaR => cases eaR with | seq eaC eaI =>
  cases eb with | seq ebP ebR => cases ebR with | seq ebC ebI =>
  have hP := (random_prepare_ct _ _ _ _ _ _ ⟨_, keygen_prepare_pre ha hQa, by
    rw [hp.base, hp.regs .rcx (by decide), hp.regs .r9 (by decide), hp.qBytes]
    exact keygen_prepare_pre hb hQb⟩ eaP ebP).1
  have hC := (random_sign_cmp_zero_ct _ _ _ _ _ _ trivial eaC ebC).1
  obtain ⟨hza, ⟨da, hra⟩, hka, hmxa⟩ := random_post_of_exec (keygen_prepared ha hQa hqs) (.seq eaP eaC)
  obtain ⟨hzb, ⟨db, hrb⟩, hkb, hmxb⟩ := random_post_of_exec (keygen_prepared hb hQb hqt) (.seq ebP ebC)
  cases eaI with
  | iteT hc' _ => simp only [eval, hza] at hc'; contradiction
  | iteF _ eaS =>
  cases ebI with
  | iteT hc' _ => simp only [eval, hzb] at hc'; contradiction
  | iteF _ ebS =>
  cases eaS with | seq eaSa eaR2 => cases eaR2 with | seq eaSt eaI2 =>
  cases ebS with | seq ebSa ebR2 => cases ebR2 with | seq ebSt ebI2 =>
  have hS := random_sample_agreement hra hrb hqs hp.base (hp.args 1 (by decide))
    (by change s.gpr .rcx + s.gpr .r9 = t.gpr .rcx + t.gpr .r9
        rw [hp.regs .rcx (by decide), hp.regs .r9 (by decide)])
    hp.qBytes
    (by simp only [keygenContextOf, keygenInput, bytesAt_length, hp.args 2 (by decide)])
    (by simpa only [keygenContextOf, List.drop_zero] using hdt) eaSa ebSa
  have hspa : _ := random_post_of_exec (random_sample_encoded hqs hra) eaSa
  have hspb : _ := random_post_of_exec (random_sample_encoded hqt hrb) ebSa
  obtain ⟨_, ra⟩ := hspa.2.2.2.2.2.1
  obtain ⟨_, rb⟩ := hspb.2.2.2.2.2.1
  have hSt := (keygen_storeStatus_ct _ _ _ _ _ _ (by
    dsimp only
    rw [ra.sp, rb.sp]
    exact hp.base) eaSt ebSt).1
  obtain ⟨hda, hdza, -, hna⟩ := random_post_of_exec (keygen_sampled ha hra hka hmxa) (.seq eaSa eaSt)
  obtain ⟨hdb, hdzb, -, hnb⟩ := random_post_of_exec (keygen_sampled hb hrb hkb hmxb) (.seq ebSa ebSt)
  rw [← hag.2] at hdzb
  cases eaI2 with
  | iteF hca eaN =>
    cases ebI2 with
    | iteT hcb _ => simp only [eval, hdza] at hca; simp only [eval, hdzb] at hcb; rw [hca] at hcb; cases hcb
    | iteF _ ebN =>
      rw [(keygen_block_nil eaN).1, (keygen_block_nil ebN).1, hP, hC, hS, hSt]
  | iteT hca eaT =>
    cases ebI2 with
    | iteF hcb _ => simp only [eval, hdza] at hca; simp only [eval, hdzb] at hcb; rw [hca] at hcb; cases hcb
    | iteT hcb ebT =>
      simp only [eval, hdza, Option.some.injEq] at hca
      simp only [eval, hdzb, Option.some.injEq] at hcb
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
      obtain ⟨a1, a2, a3, a4, a5, a6, aw⟩ := hrega
      obtain ⟨b1, b2, b3, b4, b5, b6, bw⟩ := hregb
      obtain ⟨-, -, huca, -⟩ := random_post_of_exec
        (keygen_derive_call v hs hea.sp aw a1 a2 a3 a4 a5 a6 hea.rd hea.wr) eaCall
      obtain ⟨-, -, hucb, -⟩ := random_post_of_exec
        (keygen_derive_call v ht heb.sp bw b1 b2 b3 b4 b5 b6 heb.rd heb.wr) ebCall
      have hK := (keygen_keepStatus_ct _ _ _ _ _ _ (by
        dsimp only
        rw [huca .rsp (by decide), hucb .rsp (by decide), hea.sp, heb.sp]
        exact hp.base) eaK ebK).1
      rw [hP, hC, hS, hSt, hDA, hCall, hK]

end VG.Proof.Dsa.X86_64
