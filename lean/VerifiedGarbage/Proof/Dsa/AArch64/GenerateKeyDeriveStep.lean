module
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyState

import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyGenerate
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheckStep
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyDeriveCall
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Framework.Block

/-! # Derive the key and restore the generation controller's state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem keygen_derive_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s} {used k : Nat}
    (ht : KeygenState h used t)
    (hnonce : Spec.Rsa.bytesAt t.mem (off (randomBase s) Random.oNonce) (s.gpr .x6).toNat =
      Spec.Dsa.encodeBE (s.gpr .x6).toNat k) :
    WP isa (.seq (.block GenerateKey.deriveArgs)
      (.seq (.call (keygenDeriveName v) (Generate.deriveKey v.mul)) (.block GenerateKey.keepStatus))) t fun u =>
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
      omega
    exact (random_outside_bytes hargs (show Random.oNonce + (s.gpr .x6).toNat ≤ 2 ^ 64 by
      unfold Random.oNonce; omega) (Or.inr (show 0 + 8 ≤ Random.oNonce by decide))).trans hnonce
  refine WP.seq (WP.mono (keygen_derive_call v h ha.sp hw hdi hsi hdx hcx h8 h9 h6 h7 ha.rd ha.wr)
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
