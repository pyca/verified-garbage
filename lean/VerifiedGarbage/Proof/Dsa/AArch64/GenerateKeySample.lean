module

public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheckStep
import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareState
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets

/-! # Key generation's sampling of x and its derivation -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- An accepted domain has q > 1, as the sampler needs. -/
theorem keygen_q_valid {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (hc : keygenChecked s = true) :
    1 < Spec.Dsa.decodeBE (keygenQBytes s) := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenChecked Spec.Dsa.checkParametersBytes at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  have hb := (VG.Proof.Dsa.supported_bounds hc.2.1).2.1
  rw [keygen_q_decode]
  omega

/-- The sampler's draw, from the start of the tape. -/
abbrev keygenDraw (s : State) : Spec.Dsa.Random.Sample :=
  Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (keygenQBytes s)) 128 (keygenInput s).rand

/-- Key generation's result after an accepted domain, as the wrapper computes it. -/
theorem keygen_result_checked {extra : Nat} {s : State} (h : GenerateKeyABI extra s) (hc : keygenChecked s = true) :
    keygenResult s =
      match (keygenDraw s).scalar with
      | none => ⟨none, VG.Proof.Dsa.Random.sampleStatus (keygenDraw s), (keygenDraw s).used, (keygenDraw s).trace⟩
      | some x =>
        let res := Spec.Dsa.deriveKeyBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
          (Spec.Dsa.encodeBE (keygenInput s).qLen x)
        ⟨res, Spec.Dsa.signStatus res, (keygenDraw s).used, (keygenDraw s).trace ++ [if res.isSome then 5 else 6]⟩ := by
  have hpl : (keygenInput s).params.length = 2 * (keygenInput s).pLen + (keygenInput s).qLen := by
    simp only [keygenInput, bytesAt_length]; exact h.paramsLength
  unfold keygenResult
  rw [VG.Proof.Dsa.generateKeyBytes_eq (pLen := (keygenInput s).pLen) (qLen := (keygenInput s).qLen)
    h.lengths hpl]
  simp only [show Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params
    = true from hc, ↓reduceIte]
  change (match (keygenDraw s).scalar with
    | none => (⟨none, if (keygenDraw s).trace.getLast? == some 2 then 2 else 0, (keygenDraw s).used,
        (keygenDraw s).trace⟩ : Spec.Dsa.GenerateKeyResult)
    | some x => _) = _
  cases hx : (keygenDraw s).scalar with
  | none => simp only [VG.Proof.Dsa.Random.sampleStatus, hx]
  | some x => rfl

/-- The frame state once the sampler has run, from its own state. -/
theorem KeygenState.of_ready {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s}
    {hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)} {used draws : Nat}
    (ht : KeygenState h 0 t) (hr : RandomReady (keygenContextOf h t.mem hq) used draws u)
    (hk : Keep randomVolatile t u) :
    KeygenState h used u := by
  have fits : ∀ r ∈ randomWriteRanges, r.1 + r.2 ≤ Random.frameBytes := by decide
  have hf : InScr (randomBase s) Random.frameBytes t.mem u.mem := InScr.of_frm hr.frame fits
  refine ⟨hr.scr, hr.sp, ht.saved.congr fun d _ hd => hr.frame.word_eq ?_ (by omega), hr.usedWord,
    hk.rd.trans ht.rd, hk.wr.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc => (hk.gpr r (random_saved_not_volatile hc)).trans (ht.callee r hc),
    fun r hc => (hk.vcs r hc).trans (ht.vectors r hc), ?_⟩
  · intro r hm
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> dsimp only <;> omega
  · apply Eq.trans (hr.frame.word_eq ?_ (by decide)) ht.link
    intro r hm
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> decide

theorem keygen_prepare {extra : Nat} {s t : State} {h : GenerateKeyABI extra s}
    (ht : KeygenState h 0 t) (hQ : word t.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5)
    (hq : 1 < Spec.Dsa.decodeBE (keygenQBytes s)) :
    WP isa Random.prepare t fun u =>
      u.gpr .x0 = 1 ∧ (∃ draws, RandomReady (keygenContextOf h t.mem hq) 0 draws u) ∧ Keep randomVolatile t u := by
  let C := keygenContextOf h t.mem hq
  have hrl : word t.mem C.B Random.oRandLen = BitVec.ofNat 64 C.rand.length := by
    simpa only [Random.oRandLen, C, keygenContextOf, keygenInput, bytesAt_length, ofNat_toNat64] using
      ht.saved (120, stackArg s 0) (by simp [keygenSavedValues])
  have hql : word t.mem C.B Random.oQLen = BitVec.ofNat 64 C.qBytes.length := by
    simpa only [Random.oQLen, C, keygenContextOf, keygen_q_length h, ofNat_toNat64] using
      ht.saved (88, s.gpr .x6) (by simp [keygenSavedValues])
  have hqs : Src t C.B Random.frameBytes C.Q C.qBytes := by
    have hh := random_src_take (random_src_drop ht.params (keygenInput s).pLen) (keygenInput s).qLen
    simpa only [C, keygenContextOf, keygenQBytes, keygenInput, ofNat_toNat64] using hh
  refine WP.mono (WP.keep [.x0, .x1, .x3, .x4, .x8, .x9, .x10, .x12, .x13, .x15]
    (random_prepare_ready (C := C) (draws := (word t.mem C.B Random.oDraws).toNat)
      ht.scr ht.sp (ht.saved (112, s.gpr .x7) (by simp [keygenSavedValues])) hrl ht.usedWord
      (ofNat_toNat64 _).symm hQ hql ht.rand hqs (Frm.refl _ _ _) (Nat.zero_le _) hq) rfl rfl rfl)
    fun u ⟨⟨hax, hr⟩, hk⟩ => ⟨hax, ⟨_, hr⟩, hk.mono (by decide)⟩

end VG.Proof.Dsa.AArch64
