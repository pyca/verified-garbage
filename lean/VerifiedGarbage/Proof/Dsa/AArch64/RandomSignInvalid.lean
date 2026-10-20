module
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishResult

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepare
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Octets

/-! Invalid moduli exit before sampling and publish zero consumption. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_sign_init_invalid {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocated Random.frameBytes s) fun t =>
      t.gpr .x0 = 0 ∧ RandomSignFinishPre s 0 t := by
  refine WP.mono (WP.keep randomVolatile (Q := fun t =>
      t.gpr .x0 = 0 ∧ Scr t (randomBase s) Random.frameBytes ∧ t.sp = randomBase s ∧
      RandomSaved s t.mem ∧ word t.mem (randomBase s) Random.oUsed = 0) ?_ rfl rfl rfl)
    fun t ⟨⟨ha, hscr, hsp, hsaved, hu⟩, hk⟩ => ?_
  · have hsp : (allocated Random.frameBytes s).sp = randomBase s := rfl
    refine WP.seq (WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
      fun u ⟨hum, hku⟩ => ?_)
    have hus := (random_alloc_scr h).congr hku.wr
    have husp := hku.sp.trans hsp
    have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
    have hf : InScr (randomBase s) Random.frameBytes (allocated Random.frameBytes s).mem u.mem := by
      rw [hum]; exact InScr.of_outside (random_entry_outside _ _) (by decide)
    have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocated Random.frameBytes s) (randomBase s)) :
        word u.mem (randomBase s) p.1 = p.2 := by
      rw [hum]; exact random_entry_values _ _ p hp
    have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5 :=
      hv (168, s.gpr .x3 + s.gpr .x5) (by simp [randomEntryValues, allocated])
    have huu : word u.mem (randomBase s) Random.oUsed = 0 :=
      hv (144, 0) (by simp [randomEntryValues])
    have hql : word u.mem (randomBase s) Random.oQLen = BitVec.ofNat 64 (randomQBytes s).length := by
      simpa only [Random.oQLen, random_q_length h, ofNat_toNat64] using
        hsaved (88, s.gpr .x6) (by simp [randomSavedValues])
    have hlen : 0 < (randomQBytes s).length := by
      rw [random_q_length h]
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega
    refine WP.mono (random_prepare_valid hus husp hqu hql ((random_initial_q h).congrK hf hku)
      hlen (by rw [random_q_length h]; exact (s.gpr .x6).isLt)) fun t ⟨ha, hm, hk⟩ => ?_
    have hw (d : Nat) (hd : d + 8 ≤ 168) : word t.mem (randomBase s) d = word u.mem (randomBase s) d := by
      rw [hm]
      exact (random_prepare_outside _ _ _ _).word (by omega) (by omega)
    exact ⟨by rw [ite_eq_right hq] at ha; exact ha, hus.congr hk.wr,
      hk.sp.trans husp, hsaved.congr (fun d _ hd => hw d (by omega)),
      (hw 144 (by decide)).trans huu⟩
  · refine ⟨ha, hscr, hsp, hsaved, hu, hk.rd, hk.wr, ?_, ?_⟩
    · intro r hr
      exact hk.gpr r (random_saved_not_volatile hr)
    · intro r hr
      exact hk.vcs r hr

theorem random_invalid_remaining {s : State}
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    randomSignRemaining (randomInput s) 0 8 = ⟨none, 0, 0, [4]⟩ := by
  have hle : (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen
      (randomInput s).key).params.q ≤ 1 := by rw [← random_q_decode]; omega
  have hd : Spec.Dsa.Random.sample (Spec.Dsa.privateKeyBytes (randomInput s).pLen (randomInput s).qLen
      (randomInput s).key).params.q 128 (randomInput s).rand = ⟨none, 0, [4]⟩ := by
    rw [Spec.Dsa.Random.sample]
    simp only [hle, ite_true]
  unfold randomSignRemaining
  rw [List.drop_zero, randomSignLoop_sample_none _ _ 7 _ _ _ (by rw [hd]), hd]
  rfl

theorem random_sign_invalid_store {s t : State} (hr : RandomSignFinishPre s 0 t)
    (ha : t.gpr .x0 = 0) :
    WP isa (.block (Random.store Random.oStatus .x0)) t fun w =>
      RandomSignFinishPre s 0 w ∧ word w.mem (randomBase s) Random.oStatus = 0 := by
  refine WP.mono (WP.keep [.x15] (Q := fun w =>
      w.mem = t.mem.writeW (off (randomBase s) Random.oStatus) (0 : BitVec 64))
      (by brun [Random.store, hr.sp, hr.scr.st (d := Random.oStatus) (by decide), ha,
        exec_addSp, off]) rfl rfl rfl) fun w ⟨hwm, hk⟩ => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 192) : word w.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hwm, (writeW_outside _ (randomBase s) _ (by decide)).word (by simp only [Random.oStatus]; omega) (by omega)]
  refine ⟨⟨hr.scr.congr hk.wr, hk.sp.trans hr.sp,
    hr.saved.congr (fun d _ hd => hw d (by omega)), (hw 144 (by decide)).trans hr.usedWord,
    hk.rd.trans hr.rd, hk.wr.trans hr.wr, ?_, ?_⟩, ?_⟩
  · intro r hc
    have hkv := hk.mono (show [.x15] ⊆ randomVolatile by decide)
    exact (hkv.gpr r (random_saved_not_volatile hc)).trans (hr.callee r hc)
  · intro r hc
    exact (hk.vcs r hc).trans (hr.vectors r hc)
  · rw [hwm, word_writeW_self]

theorem random_sign_body_invalid (v : Backend) {s : State} (h : RandomSignABI v.stack s)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.mul))
      (allocated Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  rw [random_invalid_remaining hq]
  unfold RandomSign.body
  apply WP.assoc
  refine WP.seq (WP.mono (random_sign_init_invalid h hq) fun t ⟨ha, hr⟩ => ?_)
  refine WP.seq (WP.ite true (by simp [eval, State.read, ha]) (fun _ => ?_) (fun he => Bool.noConfusion he))
  refine WP.mono (random_sign_invalid_store hr ha) fun w ⟨hwr, hstatus⟩ => ?_
  exact random_finish_ready_result h hwr hstatus (fun he => by contradiction) (by decide) (fun _ => rfl)

end VG.Proof.Dsa.AArch64
