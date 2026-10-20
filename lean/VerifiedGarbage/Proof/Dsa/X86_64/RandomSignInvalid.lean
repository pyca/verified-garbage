module
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignFinishResult

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepare
import VerifiedGarbage.Proof.Dsa.X86_64.RandomFrame
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets

/-! Invalid moduli exit before sampling and publish zero consumption. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_sign_init_invalid {extra : Nat} {s : State} (h : RandomSignABI extra s)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (.seq (.block RandomSign.entry) Random.prepare) (allocState Random.frameBytes s) fun t =>
      t.gpr .rax = 0 ∧ RandomSignFinishPre s 0 t := by
  refine WP.mono_mx (by decide) (WP.keep randomVolatile (Q := fun t =>
      t.gpr .rax = 0 ∧ Scr t (randomBase s) Random.frameBytes ∧ t.gpr .rsp = randomBase s ∧
      RandomSaved s t.mem ∧ word t.mem (randomBase s) Random.oUsed = 0) ?_ (by rfl))
    fun t ⟨⟨ha, hscr, hsp, hsaved, hu⟩, hk⟩ hmx => ?_
  · have hsp : (allocState Random.frameBytes s).gpr .rsp = randomBase s := rfl
    refine WP.seq (WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
      fun u ⟨hum, hku⟩ => ?_)
    have hus := (random_alloc_scr h).congr hku.2.2
    have husp := (hku.gpr (by decide)).trans hsp
    have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
    have hf : InScr (randomBase s) Random.frameBytes (allocState Random.frameBytes s).mem u.mem := by
      rw [hum]; exact InScr.of_outside (random_entry_outside _ _) (by decide)
    have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocState Random.frameBytes s) (randomBase s)) :
        word u.mem (randomBase s) p.1 = p.2 := by
      rw [hum]; exact random_entry_values _ _ p hp
    have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9 :=
      hv (168, s.gpr .rcx + s.gpr .r9) (by simp [randomEntryValues, allocState, State.setReg])
    have huu : word u.mem (randomBase s) Random.oUsed = 0 :=
      hv (144, 0) (by simp [randomEntryValues])
    have hql : word u.mem (randomBase s) Random.oQLen = BitVec.ofNat 64 (randomQBytes s).length := by
      simpa only [Random.oQLen, random_q_length h, ofNat_toNat64] using
        hsaved (88, stackArg s 0) (by simp [randomSavedValues])
    have hlen : 0 < (randomQBytes s).length := by
      rw [random_q_length h]
      have hl := h.lengths
      unfold Spec.Dsa.lengthsValid at hl
      omega
    refine WP.mono (random_prepare_valid hus husp hqu hql ((random_initial_q h).congrK hf hku)
      hlen (by rw [random_q_length h]; exact (stackArg s 0).isLt)) fun t ⟨ha, hm, hk⟩ => ?_
    have hw (d : Nat) (hd : d + 8 ≤ 168) : word t.mem (randomBase s) d = word u.mem (randomBase s) d := by
      rw [hm]
      exact (random_prepare_outside _ _ _ _).word (by omega) (by omega)
    exact ⟨by rw [ite_eq_right hq] at ha; exact ha, hus.congr hk.2.2,
      (hk.gpr (by decide)).trans husp, hsaved.congr (fun d _ hd => hw d (by omega)),
      (hw 144 (by decide)).trans huu⟩
  · refine ⟨ha, hscr, hsp, hsaved, hu, hk.2.1, hk.2.2, ?_, ?_⟩
    · intro r hr hne
      rw [hk.gpr (random_saved_not_volatile hr)]
      simp only [allocState, State.setReg, ite_eq_right hne]
    · rw [hmx]; rfl

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
    (ha : t.gpr .rax = 0) :
    WP isa (.block [.alu .cmp .rax (.imm 0)]) t fun u =>
      u.zf = some true ∧ WP isa (.block [.store (Random.sp Random.oStatus) .rax]) u fun w =>
        RandomSignFinishPre s 0 w ∧ word w.mem (randomBase s) Random.oStatus = 0 := by
  refine WP.mono_mx (by decide) (WP.keep [.rax] (Q := fun u =>
      u.mem = t.mem ∧ u.gpr .rax = 0 ∧ u.zf = some true)
      (by xrun [ha]) rfl) fun u ⟨⟨hum, hua, huz⟩, hku⟩ hmx => ?_
  refine ⟨huz, ?_⟩
  have hus := hr.scr.congr hku.2.2
  have husp := (hku.gpr (by decide)).trans hr.sp
  refine WP.mono_mx (by decide) (WP.keep [] (Q := fun w =>
      w.mem = u.mem.writeW (off (randomBase s) Random.oStatus) (0 : BitVec 64))
      (by xrun [random_ea_sp, husp, hus.st (d := Random.oStatus) (by decide), hua]) rfl)
    fun w ⟨hwm, hkw⟩ hmxw => ?_
  have hw (d : Nat) (hd : d + 8 ≤ 192) : word w.mem (randomBase s) d = word t.mem (randomBase s) d := by
    rw [hwm, (writeW_outside _ (randomBase s) _ (by decide)).word (by simp only [Random.oStatus]; omega) (by omega), hum]
  refine ⟨⟨hus.congr hkw.2.2, (hkw.gpr (by decide)).trans husp,
    hr.saved.congr (fun d _ hd => hw d (by omega)), (hw 144 (by decide)).trans hr.usedWord,
    hkw.2.1.trans (hku.2.1.trans hr.rd), hkw.2.2.trans (hku.2.2.trans hr.wr), ?_, ?_⟩, ?_⟩
  · intro r hc hn
    exact (hkw.gpr (by simp)).trans ((hku.gpr (by
      have := random_saved_not_volatile hc
      simp only [randomVolatile, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
      simpa using this.1)).trans (hr.callee r hc hn))
  · rw [hmxw, hmx]; exact hr.mxcsr
  · rw [hwm, word_writeW_self]

theorem random_sign_body_invalid (v : Backend) {s : State} (h : RandomSignABI v.stack s)
    (hq : ¬ 1 < Spec.Dsa.decodeBE (randomQBytes s)) :
    WP isa (RandomSign.body (randomSignerName v) (SignVerify.sign v.sq v.mul))
      (allocState Random.frameBytes s)
      (RandomSignBodyPost s (randomSignRemaining (randomInput s) 0 8)) := by
  rw [random_invalid_remaining hq]
  unfold RandomSign.body
  apply WP.assoc
  refine WP.seq (WP.mono (random_sign_init_invalid h hq) fun t ⟨ha, hr⟩ => ?_)
  refine WP.seq (WP.mono (random_sign_invalid_store hr ha) fun u ⟨hz, hw⟩ => ?_)
  refine WP.seq (WP.ite true (by simp only [eval, hz]) (fun _ => ?_) (fun he => Bool.noConfusion he))
  refine WP.mono hw fun w ⟨hwr, hstatus⟩ => ?_
  exact random_finish_ready_result h hwr hstatus (fun he => by contradiction) (by decide) (fun _ => rfl)

end VG.Proof.Dsa.X86_64
