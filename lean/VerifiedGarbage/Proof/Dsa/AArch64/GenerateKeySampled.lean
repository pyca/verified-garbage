module
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyGenerate
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeySample
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyState
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheckStep
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDeriveCall
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSample
import VerifiedGarbage.Proof.Framework.RelCTAssoc

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
