module

import VerifiedGarbage.Proof.Dsa.Derive
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRunning
import VerifiedGarbage.Proof.Dsa.AArch64.RandomMemory
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyState
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCheck
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallMemory
import VerifiedGarbage.Proof.Bignum.AArch64.PdCode
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! ### `Dsa.AArch64.GenerateKeyCheckStep`, which this module and modules that import it used -/

section

/-! # Key generation's domain check, on its frame state -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

/-- Whether the domain is one key generation accepts. -/
abbrev keygenChecked (s : State) : Bool :=
  Spec.Dsa.checkParametersBytes (keygenInput s).pLen (keygenInput s).qLen (keygenInput s).params

/-- After a call: the frame's bytes kept, the inputs kept, the callee-saved
registers kept. -/
theorem KeygenState.after_call {extra : Nat} {s t u : State} {h : GenerateKeyABI extra s} {used : Nat}
    {wr : List Region} (ht : KeygenState h used t)
    (hwrF : ∀ r ∈ wr, r.Disjoint ⟨randomBase s, Random.frameBytes⟩)
    (hwrP : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .x3, (s.gpr .x4).toNat⟩)
    (hwrR : ∀ r ∈ wr, r.Disjoint ⟨s.gpr .x7, (stackArg s 0).toNat⟩)
    (hf : Frame (wr ++ [below (randomBase s) extra]) t.mem u.mem)
    (hur : u.rd = t.rd) (huw : u.wr = t.wr) (husp : u.sp = t.sp) (huc : ∀ r ∈ preserved, u.gpr r = t.gpr r)
    (hv : ∀ r ∈ preservedV, (u.v r).extractLsb' 0 64 = (t.v r).extractLsb' 0 64) :
    KeygenState h used u ∧
      ∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d := by
  have hb := keygen_call_frameBytes h hwrF hf
  have hw (d : Nat) (hd : d + 8 ≤ Random.frameBytes) := random_frame_words hb hd
  have hpl : (keygenInput s).params.length = (s.gpr .x4).toNat := bytesAt_length _ _ _
  have hrl : (keygenInput s).rand.length = (stackArg s 0).toNat := bytesAt_length _ _ _
  refine ⟨⟨ht.scr.congr huw, husp.trans ht.sp,
    ht.saved.congr (fun d _ hd => hw d (by unfold Random.frameBytes; omega_using [hd])),
    (hw _ (by decide)).trans ht.usedWord, hur.trans ht.rd, huw.trans ht.wr,
    keygen_call_source ht.params hf hur huw (by rw [hpl]; exact hwrP) (by rw [hpl]; exact h.stackParams)
      (by rw [hpl]; exact Nat.le_of_lt (s.gpr .x4).isLt),
    keygen_call_source ht.rand hf hur huw (by rw [hrl]; exact hwrR) (by rw [hrl]; exact h.stackRand)
      (by rw [hrl]; exact Nat.le_of_lt (stackArg s 0).isLt),
    fun r hc => (huc r hc).trans (ht.callee r hc),
    fun r hc => (hv r hc).trans (ht.vectors r hc), (hw _ (by decide)).trans ht.link⟩, hw⟩

theorem keygen_restore_ok {s : State} {B : Addr} (hs : Scr s B Random.frameBytes)
    (hsp : s.sp = B) :
    WP isa (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0]) s fun t =>
      t.gpr .x30 = word s.mem B RandomSign.oLink ∧
      t.gpr .x0 = ((s.gpr .x0).setWidth 32).setWidth 64 ∧ t.mem = s.mem ∧ Keep [.x0, .x30] s t := by
  refine WP.mono (WP.keep [.x0, .x30] (Q := fun t =>
    t.gpr .x30 = word s.mem B RandomSign.oLink ∧
    t.gpr .x0 = ((s.gpr .x0).setWidth 32).setWidth 64 ∧ t.mem = s.mem) ?_ rfl rfl rfl)
    fun t ⟨⟨hl, hx, hm⟩, hk⟩ => ⟨hl, hx, hm, hk⟩
  brun [exec_ldrSp_x', hsp, hs.ld (d := RandomSign.oLink) (by decide),
    exec_logic, State.read, State.write, BitVec.or_self]

theorem keygen_check_step (v : Backend) {s t : State} {h : GenerateKeyABI v.stack s}
    (ht : KeygenState h 0 t)
    (hdi : t.gpr .x0 = s.gpr .x3) (hsi : t.gpr .x1 = s.gpr .x4) (hdx : t.gpr .x2 = s.gpr .x5)
    (hcx : t.gpr .x3 = s.gpr .x6) (h8 : t.gpr .x4 = stackArg s 1) (h9 : t.gpr .x5 = stackArg s 2) :
    WP isa (.seq (.call (keygenCheckName v) (Generate.checkParameters v.mul))
      (.block [.ldrSp .x30 RandomSign.oLink, .logic .orr .w .x0 .x0 .x0])) t fun u =>
      KeygenState h 0 u ∧
      (∀ d, d + 8 ≤ Random.frameBytes → word u.mem (randomBase s) d = word t.mem (randomBase s) d) ∧
      u.gpr .x0 = if keygenChecked s then 1 else 0 := by
  refine WP.seq (WP.mono (keygen_check_call v h ht.sp hdi hsi hdx hcx h8 h9 ht.rd ht.wr)
    fun u ⟨hur, huw, husp, huc, hf, hres, hv⟩ => ?_)
  have hscratch : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨randomBase s, Random.frameBytes⟩ :=
    (h.stackScratch.sub_left (keygen_frame_sub h)).symm
  have hwrs : ∀ r ∈ keygenCheckWr s, r.Disjoint ⟨randomBase s, Random.frameBytes⟩ := by
    intro r hr
    simp only [keygenCheckWr, List.mem_singleton] at hr
    subst hr
    exact hscratch
  have hul := (random_frame_words (keygen_call_frameBytes h hwrs hf) (d := RandomSign.oLink) (by decide)).trans ht.link
  refine WP.mono (keygen_restore_ok (ht.scr.congr huw) (husp.trans ht.sp))
    fun w ⟨hwl, hwx, hwm, hkw⟩ => ?_
  have hwc : ∀ r ∈ preserved, w.gpr r = t.gpr r := by
    intro r hr
    by_cases hl : r = .x30
    · subst r
      exact (hwl.trans hul).trans (ht.callee .x30 (by decide)).symm
    · exact (hkw.gpr r (by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all)).trans (huc r hr hl)
  obtain ⟨hw, hwords⟩ := ht.after_call (wr := keygenCheckWr s) hwrs
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.paramsScratch.symm)
    (fun r hr => by simp only [keygenCheckWr, List.mem_singleton] at hr; subst hr; exact h.randScratch.symm)
    (by rw [hwm]; exact hf) (hkw.rd.trans hur) (hkw.wr.trans huw) (hkw.sp.trans husp) hwc
    (fun r hr => (hkw.vcs r hr).trans (hv r hr))
  refine ⟨hw, hwords, ?_⟩
  have hp : Spec.Rsa.bytesAt t.mem (s.gpr .x3) (s.gpr .x4).toNat = (keygenInput s).params := by
    apply List.ext_getElem (by simp only [keygenInput, bytesAt_length])
    intro i h₁ h₂
    simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
    exact ht.params.val i h₂
  rw [hp] at hres
  rw [hwx]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth] at hres ⊢
  rw [hres]
  change (if keygenChecked s then 1 else 0) % 2 ^ 64 = (if keygenChecked s then (1 : BitVec 64) else 0).toNat
  cases keygenChecked s <;> rfl

end VG.Proof.Dsa.AArch64

end

end

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
  omega_using [hb]

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
  refine ⟨hr.scr, hr.sp, ht.saved.congr fun d _ hd => hr.frame.word_eq ?_ (by omega_using [hd]), hr.usedWord,
    hk.rd.trans ht.rd, hk.wr.trans ht.wr, ht.params.congrK hf hk, ht.rand.congrK hf hk,
    fun r hc => (hk.gpr r (random_saved_not_volatile hc)).trans (ht.callee r hc),
    fun r hc => (hk.vcs r hc).trans (ht.vectors r hc), ?_⟩
  · intro r hm
    simp only [randomWriteRanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> dsimp only <;> omega_using [hd]
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
