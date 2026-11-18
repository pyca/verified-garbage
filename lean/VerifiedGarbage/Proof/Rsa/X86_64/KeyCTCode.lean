module

public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCode
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCode
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Rsa.X86_64.KeyWide
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyWide
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyPhases
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyWord
public import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyCTPieces
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyWord
meta import VerifiedGarbage.Proof.Rsa.X86_64.WordFastCT
meta import VerifiedGarbage.Proof.Rsa.X86_64.CTBase
meta import VerifiedGarbage.Proof.Rsa.X86_64.CvLoad
public import VerifiedGarbage.Impl.Rsa.X86_64.CheckCrtKey
import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Impl.Rsa.X86_64.CheckCrtKey
meta import VerifiedGarbage.Proof.Rsa.X86_64.CrtKeyReduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
public import VerifiedGarbage.Proof.Rsa.X86_64.KeyMain
import VerifiedGarbage.Proof.Bignum.X86_64.R2
meta import VerifiedGarbage.Proof.Rsa.X86_64.KeyMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.R2

/-! ### `Rsa.X86_64.KeyCTMain`, which only this module used -/

section

/-! ### `Rsa.X86_64.KeyWordCT`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86_64.CrtKeyCTReduce`, which this module and modules that import it used -/

section

/-! ### `Rsa.X86_64.KeyCTLoads`, which this module and modules that import it used -/

section

/-!
# RSA key checking on x86-64: shared constant-time loads

Shared component loads, comparisons and result extraction from `KK`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

theorem kk_app {a b : List (Prog isa)} (ha : a ≠ []) (hb : b ≠ []) (h₁ : RelCT isa (Two KK) (seqs a) (Two KK))
    (h₂ : RelCT isa (Two KK) (seqs b) (Two KK)) : RelCT isa (Two KK) (seqs (a ++ b)) (Two KK) :=
  RelCT.seqs_append ha hb (RelCT.seq h₁ h₂)

theorem ld_D : RelCT isa (Two KK) (seqs (loadNum aX sD sDlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pd) (·.dl)
    (fun _ _ h => ⟨h.hD, h.hDl, h.srD, h.dl1, h.dl2⟩) (by taint_decide) (by taint_decide)

theorem ld_PX : RelCT isa (Two KK) (seqs (loadNum aX sP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pp) (·.pl)
    (fun _ _ h => ⟨h.hP, h.hPl, h.srP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_PM : RelCT isa (Two KK) (seqs (loadNum aM sP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pp) (·.pl)
    (fun _ _ h => ⟨h.hP, h.hPl, h.srP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_QR : RelCT isa (Two KK) (seqs (loadNum aR sQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pq) (·.ql)
    (fun _ _ h => ⟨h.hQ, h.hQl, h.srQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_QM : RelCT isa (Two KK) (seqs (loadNum aM sQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pq) (·.ql)
    (fun _ _ h => ⟨h.hQ, h.hQl, h.srQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_DP : RelCT isa (Two KK) (seqs (loadNum aX sDP sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pdp) (·.pl)
    (fun _ _ h => ⟨h.hDP, h.hPl, h.srDP, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ld_DQ : RelCT isa (Two KK) (seqs (loadNum aX sDQ sQlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pdq) (·.ql)
    (fun _ _ h => ⟨h.hDQ, h.hQl, h.srDQ, h.ql1, h.ql2⟩) (by taint_decide) (by taint_decide)

theorem ld_QI : RelCT isa (Two KK) (seqs (loadNum aX sQI sPlen)) (Two KK) :=
  loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pqi) (·.pl)
    (fun _ _ h => ⟨h.hQI, h.hPl, h.srQI, h.pl1, h.pl2⟩) (by taint_decide) (by taint_decide)

theorem ltXN : RelCT isa (Two KK) (seqs (ltMask aX aN)) (Two KK) := ltMaskK_ct (by decide) (by decide) (by taint_decide)

theorem ltXM : RelCT isa (Two KK) (seqs (ltMask aX aM)) (Two KK) := ltMaskK_ct (by decide) (by decide) (by taint_decide)

/-- The result, from `KK`. -/
theorem outK_ct : RelCT isa (Two KK)
    (.block (([.mov .rax (.mem (hdr sMask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit)) fun _ _ => True :=
  two_taint [.rdi] pins_kk (by taint_decide)

end VG.Proof.Rsa.X86_64.Key

end

end

/-! ### `Rsa.X86_64.KeyCTSetup`, which this module and modules that import it used -/

section

/-!
# `vg_rsa_check_key` on x86-64: constant time of the setup

From `main`'s hypotheses (`M0`), the setup leaves the checks' context
(`KK`). Its pieces load from the header and from `n`, so each runs from
the registers that correctness pins after the one before: `setup_nested`
states them, piece by piece, and `setupK_ct` follows it.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK)

/-- The public data of `main`: the checks', `n`'s pointer and its length. -/
structure MPub where
  kp : KPub
  np : Addr
  k : Nat

/-- `main`'s hypotheses, with the public data `a`. -/
def M0 (a : MPub) (s : State) : Prop :=
  ∃ nb db pb qb dpb dqb qib ev, MainPre s a.kp.B a.kp.Z a.k a.np a.kp.pd a.kp.pp a.kp.pq a.kp.pdp a.kp.pdq
    a.kp.pqi nb db pb qb dpb dqb qib ev ∧ a.kp.w = (a.k + 7) / 8 ∧ db.length = a.kp.dl ∧ pb.length = a.kp.pl ∧
    qb.length = a.kp.ql ∧ a.kp.k = a.k ∧ a.kp.np = a.np ∧ a.kp.nb = nb

/-- Before the last piece. -/
def S4 (a : MPub) (t : State) : Prop := t.gpr .rdi = a.kp.B ∧ WP isa (.block maskInit) t (KK a.kp)

/-- Before `setWord`. -/
def S3 (a : MPub) (t : State) : Prop :=
  RegsAre [(.rdi, a.kp.B), (.r12, BitVec.ofNat 64 a.kp.w), (.rcx, BitVec.ofNat 64 0)] t ∧
    WP isa (.block [.mov .r8 (.mem (hdr (sArr aOne)))]) t (RegsAre [(.r8, kb a.kp aOne)]) ∧
    WP isa (setWord aOne .rcx) t (S4 a)

/-- Before the constants. -/
def S2 (a : MPub) (t : State) : Prop := WP isa (.block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)]) t (S3 a)

/-- Before `n`'s load. -/
def S1 (a : MPub) (t : State) : Prop :=
  RegsAre [(.rsi, a.np), (.rcx, BitVec.ofNat 64 a.k), (.rbx, kb a.kp aN)] t ∧ WP isa loadBE t (S2 a)

theorem setup_nested {a : MPub} {s : State} (h : M0 a s) : WP isa (.block VG.Impl.Rsa.X86_64.head) s (S1 a) := by
  obtain ⟨nb, db, pb, qb, dpb, dqb, qib, ev, hp, hw, hdl, hpl, hql, hkk, hnpp, hnbb⟩ := h
  obtain ⟨⟨B, Z, w, pd, pp, pq, pdp, pdq, pqi, dl, pl, ql, kk', npp, nbb⟩, np, k⟩ := a
  simp only at hp hw hdl hpl hql hkk hnpp hnbb ⊢
  subst hw hdl hpl hql
  subst kk' npp nbb
  have hs := hp.scr
  have hn := hs.nowrap
  have := hp.k1
  have := hp.k2
  have := hp.dl2
  have := hp.pl2
  have := hp.ql2
  obtain hZ : slot ((k + 7) / 8) 8 ≤ Z := by have := hp.zk; unfold slot hdrBytes; omega_arith
  obtain h8 := hdr_lt_slot ((k + 7) / 8) 0 (show 31 < 32 by decide)
  obtain h0 := slot_le (w := (k + 7) / 8) (show 0 < 8 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eM : sMask = 22 := rfl
  have eI : sMinv = 7 := rfl
  have e1 : sArr aOne = 15 := rfl
  obtain hsl : ∀ r ∈ [(8 * sW, 8), (8 * sArr 0, 64)], r.1 + r.2 ≤ Z := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> simp only [eW, eA] <;> omega_arith
  obtain hfw : ∀ i, i ≠ 6 → (i < 8 ∨ 16 ≤ i) → ∀ r ∈ [(8 * sW, 8), (8 * sArr 0, 64)],
      8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
    intro i h6 hr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl) <;> simp only [eW, eA] <;> omega_arith
  refine WP.mono (setupHead_ok hs hp.rdi hZ (by omega_arith) hp.hK hp.hN)
    fun t₁ ⟨h12, hcx, hsi, hbx, hW₁, hb₁, hf₁, k₁⟩ => ⟨regsAre_cons hsi (regsAre_cons hcx (regsAre_cons hbx
      regsAre_nil)), ?_⟩
  obtain hs₁ := hs.congr k₁.2.2
  obtain in₁ : InScr B Z s.mem t₁.mem := InScr.of_frm hf₁ hsl
  refine WP.mono (loadArr_ok hs₁ (j := aN) (by decide) hZ (hp.srN.congrK in₁ k₁) hp.nl (by omega_arith)
    (by omega_arith) hsi hcx hbx) fun t₂ ⟨hv₂, ha₂, k₂⟩ => ?_
  obtain hs₂ := hs₁.congr k₂.2.2
  obtain hdi₂ : t₂.gpr .rdi = B := (k₂.gpr (by decide)).trans ((k₁.gpr (by decide)).trans hp.rdi)
  refine WP.mono (WP.keep [.rdx, .rcx] (Q := fun t => t.gpr .rdx = 1 ∧
      t.gpr .rcx = BitVec.ofNat 64 0 ∧ t.mem = t₂.mem) (by xrun []) rfl)
    fun t₃ ⟨⟨hdx₃, hcx₃, hm₃⟩, k₃⟩ => ?_
  obtain hH : Hdr t₃.mem B ((k + 7) / 8) (word s.mem B (8 * sMinv)) :=
    ⟨by rw [hm₃, ha₂.hslot (by decide)]; exact hW₁,
      by rw [hm₃, ha₂.hslot (by decide), hf₁.word_eq (hfw sMinv (by decide) (by decide)) (by omega_arith)],
      fun j hj => by rw [hm₃, ha₂.hslot (by unfold sArr; omega_arith)]; exact hb₁ j hj⟩
  obtain hs₃ := hs₂.congr k₃.2.2
  obtain h12₃ : t₃.gpr .r12 = BitVec.ofNat 64 ((k + 7) / 8) :=
    (k₃.gpr (by decide)).trans ((k₂.gpr (by decide)).trans h12)
  obtain hdi₃ : t₃.gpr .rdi = B := (k₃.gpr (by decide)).trans hdi₂
  refine ⟨regsAre_cons hdi₃ (regsAre_cons h12₃ (regsAre_cons hcx₃ regsAre_nil)),
    WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = off B (slot ((k + 7) / 8) aOne)) (by
      xrun [State.ea, hdr, hdi₃, hdrOff, hs₃.ld (d := 8 * sArr aOne) (by rw [e1]; omega_arith),
        hH.harr aOne (by decide)]) rfl) fun t ⟨h8', _⟩ => regsAre_cons h8' regsAre_nil, ?_⟩
  refine WP.mono (setWord_ok hs₃ hdi₃ hH hZ h12₃ (by omega_arith) (by omega_arith) (o := aOne) (by decide)
    (ri := .rcx) (by decide) (i := 0) (by omega_arith) hcx₃) fun t₄ ⟨hone, ho₄, k₄⟩ => ?_
  obtain hs₄ := hs₃.congr k₄.2.2
  obtain hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans hdi₃
  obtain ha₄ : Arrays B ((k + 7) / 8) [aOne] t₃.mem t₄.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₄ (Nat.le_refl _) (Nat.le_refl _)
  obtain hW₄ : word t₄.mem B (8 * sW) = BitVec.ofNat 64 ((k + 7) / 8) := (ha₄.hdr hH).hw
  have eS : Impl.Rsa.X86_64.Keys.sStride = 28 := rfl
  refine ⟨hdi₄, ?_⟩
  rw [show maskInit = strideInit ++ maskSet from rfl]
  refine WP.block_append_iff.mpr (WP.mono (WP.keep [.rax] (Q := fun t => t.mem =
      t₄.mem.writeW (off B (8 * Impl.Rsa.X86_64.Keys.sStride)) (BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)))) (by
    xrun [strideInit, State.ea, hdr, hdi₄, hdrOff, hs₄.ld (d := 8 * sW) (by omega_arith), hW₄,
      hs₄.st (d := 8 * Impl.Rsa.X86_64.Keys.sStride) (by rw [eS]; omega_arith)]
    exact congrArg _ (stride_bv _)) rfl) fun t₅ ⟨hm₅, k₅'⟩ => ?_)
  obtain hs₅ := hs₄.congr k₅'.2.2
  obtain hdi₅ : t₅.gpr .rdi = B := (k₅'.gpr (by decide)).trans hdi₄
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.mem = t₅.mem.writeW (off B (8 * sMask)) (mask true)) (by
    xrun [maskSet, State.ea, hdr, hdi₅, hdrOff, hs₅.st (d := 8 * sMask) (by omega_arith)]
    exact congrArg _ (by decide)) rfl) fun t ⟨hm, k₅⟩ => ?_
  obtain hn' : B.toNat + slot ((k + 7) / 8) 8 ≤ 2 ^ 64 := by omega_arith
  obtain hoS : Outside B (8 * Impl.Rsa.X86_64.Keys.sStride) 8 t₄.mem t₅.mem := by
    rw [hm₅]; exact writeW_outside _ B _ (by rw [eS]; omega_arith)
  obtain ho₅ : Outside B (8 * sMask) 8 t₅.mem t.mem := by rw [hm]; exact writeW_outside _ B _ (by omega_arith)
  obtain kk : Keep mmRegs s t := (((((k₁.trans k₂).trans k₃).trans k₄).trans k₅').trans k₅).mono (by decide)
  obtain hin : InScr B Z s.mem t.mem :=
    ((((in₁.trans (InScr.of_arrays ha₂ hZ (by decide))).trans (by rw [hm₃]; exact InScr.refl _ _ _)).trans
      (InScr.of_arrays ha₄ hZ (by decide))).trans (InScr.of_outside hoS (by rw [eS]; omega_arith))).trans
      (InScr.of_outside ho₅ (by omega_arith))
  obtain hSl : ∀ j < 8, ∀ k' ≤ (k + 7) / 8 + 2, wv t₅.mem B (slot ((k + 7) / 8) j) k' = wv t₄.mem B (slot ((k + 7) / 8) j) k' :=
    fun j hj k' hk' => hoS.wv (Or.inr (by have := hdr_lt_slot ((k + 7) / 8) j (show 28 < 32 by decide); rw [eS]; omega_arith))
      (by have := slot_le (w := (k + 7) / 8) hj; omega_arith)
  obtain hh : ∀ i < 32, setupSlot i = false → word t.mem B (8 * i) = word s.mem B (8 * i) := fun i hi hsi => by
    obtain ⟨h6, hr, h22, h28⟩ := setupSlot_false i hi hsi
    rw [hm, hdrStore_hdr _ _ _ (by decide) hi (by rw [eM]; omega_arith), hm₅,
      hdrStore_hdr _ _ _ (by decide) hi (by rw [eS]; omega_arith), ha₄.hslot hi, hm₃, ha₂.hslot hi,
      hf₁.word_eq (hfw i h6 hr) (by omega_arith)]
  obtain hH₅ : Hdr t.mem B ((k + 7) / 8) (word s.mem B (8 * sMinv)) := by
    rw [hm, hm₅]
    exact Hdr.store (Hdr.store (ha₄.hdr hH) (i := Impl.Rsa.X86_64.Keys.sStride) (by decide) (by decide) _)
      (i := sMask) (by decide) (by decide) _
  obtain sr : ∀ {p : Addr} {bs : List Byte}, Src s B Z p bs → Src t B Z p bs := fun h => h.congr hin kk.2.1 kk.2.2
  refine ⟨t, word s.mem B (8 * sMinv), Spec.Rsa.os2ip nb, ⟨⟨hs₅.congr k₅.2.2, (k₅.gpr (by decide)).trans hdi₅, hH₅⟩,
    hZ, by dsimp only; omega_arith, by dsimp only; omega_arith, fun _ _ _ => rfl, InScr.refl _ _ _, rfl, rfl, ?_, ?_,
    Keep.refl _ _⟩,
    { hD := by rw [hh sD (by decide) (by decide)]; exact hp.hD
      hDl := by rw [hh sDlen (by decide) (by decide)]; exact hp.hDl
      hP := by rw [hh sP (by decide) (by decide)]; exact hp.hP
      hPl := by rw [hh sPlen (by decide) (by decide)]; exact hp.hPl
      hQ := by rw [hh sQ (by decide) (by decide)]; exact hp.hQ
      hQl := by rw [hh sQlen (by decide) (by decide)]; exact hp.hQl
      hDP := by rw [hh sDP (by decide) (by decide)]; exact hp.hDP
      hDQ := by rw [hh sDQ (by decide) (by decide)]; exact hp.hDQ
      hQI := by rw [hh sQI (by decide) (by decide)]; exact hp.hQI
      srD := ⟨db, sr hp.srD, rfl⟩
      srP := ⟨pb, sr hp.srP, rfl⟩
      srQ := ⟨qb, sr hp.srQ, rfl⟩
      srDP := ⟨dpb, sr hp.srDP, hp.dpl⟩
      srDQ := ⟨dqb, sr hp.srDQ, hp.dql⟩
      srQI := ⟨qib, sr hp.srQI, hp.qil⟩
      dl1 := hp.dl1
      dl2 := by dsimp only; omega_arith
      pl1 := hp.pl1
      pl2 := by dsimp only; omega_arith
      ql1 := hp.ql1
      ql2 := by dsimp only; omega_arith
      word_w1 := by dsimp only; omega_arith
      word_w2 := by dsimp only; omega_arith
      word_room := by
        dsimp only
        simp only [slot, hdrBytes]
        omega_using [hp.zk, hp.k1]
      hS := by dsimp only; rw [hm, hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), hm₅, word_writeW_self]
      hK := by dsimp only; rw [hh _ (by decide) (by decide)]; exact hp.hK
      hN := by dsimp only; rw [hh _ (by decide) (by decide)]; exact hp.hN
      srN := sr hp.srN
      nl := by dsimp only; rw [hp.nl]; omega_arith }⟩
  · rw [Outside.wv_arr ho₅ (by decide) hZ hn (by dsimp only; omega_arith), hSl _ (by decide) _ (by dsimp only; omega_arith),
      ha₄.wv_of_not_mem (by decide) (by decide) hn', hm₃]
    exact hv₂
  · rw [Outside.wv_arr ho₅ (by decide) hZ hn (by dsimp only; omega_arith), hSl _ (by decide) _ (by dsimp only; omega_arith), hone,
      hdx₃]; rfl

theorem pins_regsAre {α : Type} {Φ : α → State → Prop} (vs : α → List (Reg × BitVec 64)) {rs : List Reg}
    (hrs : ∀ a, (vs a).map Prod.fst = rs) (h : ∀ a s, Φ a s → RegsAre (vs a) s) : Pins Φ rs :=
  fun a s₁ s₂ h₁ h₂ => pins_regs vs hrs a s₁ s₂ (h a s₁ h₁) (h a s₂ h₂)

/-- The setup is constant time from `M0`, and leaves `KK`. -/
theorem setupK_ct : RelCT isa (Two M0) (seqs [.block VG.Impl.Rsa.X86_64.head, loadBE,
    .block [.mov32 .rdx (.imm 1), .mov32 .rcx (.imm 0)], setWord aOne .rcx, .block maskInit])
    (Two fun (a : MPub) t => KK a.kp t) := by
  simp only [seqs]
  refine RelCT.seq (two_piece (Ψ := S1) [.rdi] (pins_of (fun (a : MPub) _ => a.kp.B) fun a s h r hr => by
      obtain ⟨_, _, _, _, _, _, _, _, hp, -⟩ := h
      simp only [List.mem_singleton] at hr; subst hr; exact hp.rdi) (by taint_decide)
    fun _ _ h => setup_nested h) ?_
  refine RelCT.seq (two_post (two_taint [.rsi, .rcx, .rbx]
    (pins_regsAre (fun a => [(.rsi, a.np), (.rcx, BitVec.ofNat 64 a.k), (.rbx, kb a.kp aN)]) (fun _ => rfl)
      fun _ _ h => h.1) (by taint_decide)) fun _ _ h => h.2) ?_
  refine RelCT.seq (two_post (two_taint [] (fun _ _ _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun _ _ h => h) ?_
  refine RelCT.seq (two_post ?_ fun _ _ h => h.2.2) ?_
  · unfold setWord
    refine RelCT.seq (two_piece (Ψ := fun (a : MPub) t => RegsAre [(.r8, kb a.kp aOne), (.r12, BitVec.ofNat 64 a.kp.w),
        (.rcx, BitVec.ofNat 64 0)] t) [.rdi]
      (pins_of (fun a _ => a.kp.B) fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1 (.rdi, _) (List.mem_cons_self ..))
      (by taint_decide) fun a t h => ?_)
      (two_taint [.r8, .r12, .rcx] (pins_regsAre (fun (a : MPub) => [(.r8, kb a.kp aOne), (.r12, BitVec.ofNat 64 a.kp.w),
        (.rcx, BitVec.ofNat 64 0)]) (fun _ => rfl) fun _ _ h => h) (by taint_decide))
    exact WP.mono (WP.keep [.r8] h.2.1 rfl) fun t' ⟨h8, k⟩ => regsAre_cons (h8 (.r8, kb a.kp aOne) (by simp))
      (regsAre_cons ((k.gpr (by decide)).trans (h.1 (.r12, BitVec.ofNat 64 a.kp.w) (by simp)))
        (regsAre_cons ((k.gpr (by decide)).trans (h.1 (.rcx, BitVec.ofNat 64 0) (by simp))) regsAre_nil))
  · exact two_post (two_taint [.rdi] (pins_of (fun a _ => a.kp.B) fun _ _ h r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact h.1) (by taint_decide)) fun _ _ h => h.2

end VG.Proof.Rsa.X86_64.Key

end

end

/-!
# RSA key checking on x86-64: constant time of bounded remainders

`reduceTop` from `KK` (`reduceTopK_ct`): its header loads from `rdi`, the
rest from the registers they pin, which are public (`w'` and `c` from the
lengths); shared by the full-key and CRT-only checkers.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

/-- After `reduceTop`'s first block: `KK`, and the copy's registers. -/
def RT1 (fl fc : KPub → Nat) (p : KPub) (t : State) : Prop :=
  KK p t ∧ RegsAre [(.rdi, p.B), (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)), (.r13, BitVec.ofNat 64 (fc p)),
    (.rsi, off p.B (slot p.w aAcc + 8 * fc p)), (.rbx, kb p aR)] t

/-- After the copy. -/
def RT2 (fl fc : KPub → Nat) (p : KPub) (t : State) : Prop :=
  KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) ∧ t.gpr .r13 = BitVec.ofNat 64 (fc p)

/-- `reduceTop sl top` from `KK`, for the length `fl p` in slot `sl` and the
`c = fc p` that `top` computes. -/
theorem reduceTopK_ct {sl : Nat} {top : List Instr} (fl fc : KPub → Nat) (hsl : sl < 32) (hsl' : sl ≠ sMask)
    (hL : ∀ p s, KS p s → word s.mem p.B (8 * sl) = BitVec.ofNat 64 (fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w)
    (hfc : ∀ p s, KS p s → fc p + (fl p + 7) / 8 ≤ 2 * p.w + 4)
    (htop : ∀ p t, KK p t → WP isa (.block top) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 (fc p) ∧
      t'.mem = t.mem ∧ Keep [.r13] t t')
    (hok : ∀ p s, KK p s → WP isa (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sl top)) s (KK p))
    {hc₁ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Impl.Rsa.X86_64.CheckCrtKey.lenWords sl ++ top ++
      ([.mov .rax (.reg .r13), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov .rsi (.mem (hdr (sArr aAcc))), .alu .add .rsi (.reg .rax),
        .mov .rbx (.mem (hdr (sArr aR)))] : List Instr))) hc₁).isSome = true) :
    RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sl top)) (Two KK) := by
  refine kk_ct ?_ hok
  simp only [Impl.Rsa.X86_64.CheckCrtKey.reduceTop, seqs]
  refine RelCT.seq ((zeroArrK_ct (j := aR) (by decide) (by decide) (by decide) (by taint_decide)).mono
    (fun _ _ h => h) fun _ _ h => two_mono (fun _ _ h => h.1) h) ?_
  refine RelCT.seq (two_piece (Ψ := RT1 fl fc) [.rdi] pins_kk hT fun p s h => ?_) ?_
  · obtain ⟨hdi, hl, -, hb'⟩ := h.lds
    obtain ⟨s₀, minv, N, c, hs⟩ := h
    obtain ⟨hLs, hL1, hLw⟩ := hL p s₀ hs
    rw [← c.hdr sl hsl hsl'] at hLs
    have := c.w2
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (WP.keep [.r12] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) ∧ t.mem = s.mem)
      (by xrun [Impl.Rsa.X86_64.CheckCrtKey.lenWords, State.ea, hdr, hdi, hdrOff, hl sl hsl, hLs,
        shr3_w (fl p) (by omega_arith)]) rfl) fun s₂ ⟨⟨h12₂, hm₂⟩, k₂⟩ => ?_
    have hK₂ : KK p s₂ := KK.keep ⟨s₀, minv, N, c, hs⟩ hm₂ (k₂.mono (by decide))
    refine WP.mono (htop p s₂ hK₂) fun s₃ ⟨h13₃, hm₃, k₃⟩ => ?_
    have hK₃ : KK p s₃ := KK.keep hK₂ hm₃ (k₃.mono (by decide))
    obtain ⟨hdi₃, hl₃, -, hb₃⟩ := hK₃.lds
    have h12₃ : s₃.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) := (k₃.gpr (by decide)).trans h12₂
    refine WP.mono (WP.keep [.rax, .rsi, .rbx] (Q := fun t => t.gpr .rsi = off p.B (slot p.w aAcc + 8 * fc p) ∧
        t.gpr .rbx = kb p aR ∧ t.mem = s₃.mem)
      (by
        xrun [State.ea, hdr, hdi₃, hdrOff, h13₃, hl₃ (sArr aAcc) (by decide), hl₃ (sArr aR) (by decide),
          hb₃ aAcc (by decide), hb₃ aR (by decide)]
        rw [eight_add]; exact off_off p.B _ _) rfl) fun t ⟨⟨a, b, hm⟩, k⟩ => ?_
    exact ⟨KK.keep hK₃ hm (k.mono (by decide)), regsAre_cons ((k.gpr (by decide)).trans hdi₃)
      (regsAre_cons ((k.gpr (by decide)).trans h12₃)
      (regsAre_cons ((k.gpr (by decide)).trans h13₃) (regsAre_cons a (regsAre_cons b regsAre_nil))))⟩
  refine RelCT.seq (R := Two (RT2 fl fc)) (two_post (two_taint [.rdi, .r12, .r13, .rsi, .rbx]
    (pins_regsAre (fun p => [(.rdi, p.B), (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)), (.r13, BitVec.ofNat 64 (fc p)),
      (.rsi, off p.B (slot p.w aAcc + 8 * fc p)), (.rbx, kb p aR)]) (fun _ => rfl) fun _ _ h => h.2)
    (by taint_decide)) fun p s h => ?_) ?_
  · obtain ⟨⟨s₀, minv, N, c, hs⟩, hr⟩ := h
    obtain ⟨hL', hL1, hLw⟩ := hL p s₀ hs
    have hn := c.good.scr.nowrap
    have hZ := c.hZ
    have := c.w2
    have := hfc p s₀ hs
    have eAcc : slot p.w aAcc = 256 + 16 * (p.w + 2) := by unfold slot hdrBytes aAcc; omega_arith
    have eR : slot p.w aR = 256 + 48 * (p.w + 2) := by unfold slot hdrBytes aR; omega_arith
    have e8 : slot p.w 8 = 256 + 64 * (p.w + 2) := by unfold slot hdrBytes; omega_arith
    have hsi : s.gpr .rsi = off p.B (slot p.w aAcc + 8 * fc p) := hr (.rsi, off p.B (slot p.w aAcc + 8 * fc p)) (by simp)
    have hbx : s.gpr .rbx = off p.B (slot p.w aR) := hr (.rbx, kb p aR) (by simp)
    have h12 : s.gpr .r12 = BitVec.ofNat 64 ((fl p + 7) / 8) := hr (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)) (by simp)
    have h13 : s.gpr .r13 = BitVec.ofNat 64 (fc p) := hr (.r13, BitVec.ofNat 64 (fc p)) (by simp)
    refine WP.mono (copyWords_ok hsi hbx h12 (by omega_arith) (by omega_arith) (by omega_arith)
      (fun i hi => c.good.scr.ld (by omega_arith)) (fun i hi => c.good.scr.st (by omega_arith))
      (fun i hi b hb => by rw [ofs_off p.B (by omega_arith)]; omega_arith)) fun t ⟨_, _, ho, k⟩ => ?_
    have ha : Arrays p.B p.w [aR] s.mem t.mem :=
      Arrays.of_outside (j := aR) (by simp) ho (Nat.le_refl _) (by omega_arith)
    exact ⟨⟨s₀, minv, N, c.arr ha (by decide) (by decide) (by decide) (k.mono (by decide)), hs⟩,
      (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans h13⟩
  refine hdr_ct (Φ := RT2 fl fc) (pins_of (fun p _ => p.B) fun _ _ h r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.1.rdi)
    (rs := [.rbx, .r10, .r8, .r12, .rsi, .r9, .r13]) (fun p => [(.rbx, kb p aR), (.r10, kb p aM),
      (.r8, kb p aX), (.r12, BitVec.ofNat 64 ((fl p + 7) / 8)), (.rsi, kb p aT), (.r9, kb p aAcc),
      (.r13, BitVec.ofNat 64 (fc p))]) (fun _ => rfl) (by taint_decide) (by taint_decide) fun p s h => ?_
  obtain ⟨hdi, hl, -, hb'⟩ := h.1.lds
  refine WP.mono (WP.keep [.rbx, .r10, .r8, .rsi, .r9] (Q := fun t => t.gpr .rbx = kb p aR ∧
      t.gpr .r10 = kb p aM ∧ t.gpr .r8 = kb p aX ∧ t.gpr .rsi = kb p aT ∧ t.gpr .r9 = kb p aAcc)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr aR) (by decide), hl (sArr aM) (by decide),
      hl (sArr aX) (by decide), hl (sArr aT) (by decide), hl (sArr aAcc) (by decide), hb' aR (by decide),
      hb' aM (by decide), hb' aX (by decide), hb' aT (by decide), hb' aAcc (by decide)]) rfl)
    fun t ⟨⟨a, b, c, d, e⟩, k⟩ => ?_
  exact regsAre_cons a (regsAre_cons b (regsAre_cons c (regsAre_cons ((k.gpr (by decide)).trans h.2.1)
    (regsAre_cons d (regsAre_cons e (regsAre_cons ((k.gpr (by decide)).trans h.2.2) regsAre_nil))))))

theorem topQK_ok {p : KPub} {t : State} (h : KK p t) :
    WP isa (.block Impl.Rsa.X86_64.CheckCrtKey.topQ) t fun t' => t'.gpr .r13 = BitVec.ofNat 64 ((p.ql + 7) / 8) ∧
      t'.mem = t.mem ∧ Keep [.r13] t t' := by
  obtain ⟨s₀, minv, N, c, hs⟩ := h
  have := c.w2
  have := hs.ql2
  exact topQ_ok c.good c.hZ (by rw [c.hdr sQlen (by decide) (by decide)]; exact hs.hQl) (by omega_arith)

theorem reduceTopQK_ct : RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sPlen
    Impl.Rsa.X86_64.CheckCrtKey.topQ)) (Two KK) :=
  reduceTopK_ct (·.pl) (fun p => (p.ql + 7) / 8) (by decide) (by decide) (fun _ _ h => ⟨h.hPl, h.pl1, h.pl2⟩)
    (fun _ _ h => by have := h.pl2; have := h.ql2; omega_arith) (fun _ _ h => topQK_ok h)
    (fun p s h => by
      obtain ⟨s₀, minv, N, c, hs⟩ := h
      have := c.w2
      have := hs.ql2
      have := hs.pl2
      have := hs.ql1
      have hq : ∀ t : State, (∀ i < 32, word t.mem p.B (8 * i) = word s.mem p.B (8 * i)) →
          word t.mem p.B (8 * sQlen) = BitVec.ofNat 64 p.ql := fun t hh => by
        rw [hh _ (by decide), c.hdr sQlen (by decide) (by decide)]; exact hs.hQl
      exact WP.mono (reduceTopK c (Nx := 2 * p.w + 2) (by decide) (by decide) hs.hPl hs.pl1 hs.pl2
        (fun t hg hh => topQ_ok hg c.hZ (hq t hh) (by omega_arith)) (by omega_arith) (by omega_arith) (by omega_arith))
        fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩) (by taint_decide)

end VG.Proof.Rsa.X86_64.Key

end

end

/-!
# `vg_rsa_check_key` on x86-64: constant time of the word-level checks

The guard reads only public values (the lengths, `n`'s first byte), so both
runs take the same branch (`guard_ct`); the word-level checks' pieces run
from registers pinned after `ws` or the header loads, and keep `KK`.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask)

theorem KS.room {p : KPub} {s : State} (h : KS p s) : WRoom s p.B p.Z p.w :=
  ⟨h.hS, by have := h.word_room; omega_arith, h.word_w1, h.word_w2⟩

theorem KK.ws {p : KPub} {t : State} (h : KK p t) : Ws t p.B p.Z p.w :=
  let ⟨_, _, _, c, hs⟩ := h; c.ws hs.room

theorem KK.z17 {p : KPub} {t : State} (h : KK p t) : slot p.w 17 ≤ p.Z :=
  let ⟨_, _, _, _, hs⟩ := h; hs.room.hZ

theorem KK.w4 {p : KPub} {t : State} (h : KK p t) : 6 ≤ p.w :=
  let ⟨_, _, _, _, hs⟩ := h; hs.word_w1

theorem KK.frm {p : KPub} {t t' : State} (h : KK p t) {rs : List (Nat × Nat)} (hf : Frm p.B rs t.mem t'.mem)
    (ha : ∀ r ∈ rs, Away p.w r) (hz : ∀ r ∈ rs, r.1 + r.2 ≤ p.Z) (hk : Keep mmRegs t t') : KK p t' :=
  let ⟨s, minv, N, c, hs⟩ := h; ⟨s, minv, N, c.frm hf ha hz hk, hs⟩

/-- `copyA o a` into array 5 or 9. -/
theorem copyAK_ct {o a : Nat} (ho : o = 5 ∨ o = 9) (ha : a < 8) (hoa : o ≠ a) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (Impl.Rsa.X86_64.Keys.base a .rsi ++
      Impl.Rsa.X86_64.Keys.base o .rbx)) Impl.Rsa.X86_64.copyWords) hc).isSome = true) :
    RelCT isa (Two KK) (Impl.Rsa.X86_64.Keys.copyA o a) (Two KK) := by
  have e : Impl.Rsa.X86_64.Keys.copyA o a = .seq (.block (Impl.Rsa.X86_64.Keys.ws ++
      (Impl.Rsa.X86_64.Keys.base a .rsi ++ Impl.Rsa.X86_64.Keys.base o .rbx))) Impl.Rsa.X86_64.copyWords := by
    simp only [Impl.Rsa.X86_64.Keys.copyA, List.append_assoc]
  rw [e]
  exact ws_ct KPub.B KPub.Z KPub.w (fun _ _ h => h.ws) ht fun p s h => by
    rw [← e]
    have hZ := h.z17
    exact WP.mono (copyA_ok h.ws (by omega_arith) (by omega_arith) hoa) fun t ⟨_, o', k⟩ =>
      h.frm (Frm.of_outside o' (List.mem_singleton_self _))
        (by simp only [List.mem_singleton, forall_eq]
            rcases ho with rfl | rfl
            · exact away_slot p.w (by decide) (.inl (by decide)) (by omega_arith)
            · exact away_slot p.w (by decide) (.inr (by decide)) (by omega_arith))
        (by simp only [List.mem_singleton, forall_eq]
            rcases ho with rfl | rfl <;> simp only [slot_eq] at hZ ⊢ <;> omega_arith)
        (k.mono (by decide))

/-- `WordDivide`'s normalization and division, of the dividend's words `top` gives. -/
theorem fastAtK_ct {top : Option Nat} (ck : WordDivide.SeedCk top) (hk : ∀ k, top = some k → k ≤ 3) :
    RelCT isa (Two KK) (.seq (.block Impl.Rsa.X86_64.WordDivide.normalize)
      (Impl.Rsa.X86_64.WordDivide.code top)) (Two KK) :=
  two_post (two_map (fun p : KPub => (⟨p.B, p.Z, p.w, 0⟩ : WordDivide.Pub)) (fun _ _ h => ⟨h.ws, h.z17, h.w4⟩)
    (WordDivide.fastAt_ct ck fun _ k hw e => by have := hk k e; omega_arith)) fun p s h =>
    WP.mono (WordDivide.fastAt_ok h.ws h.z17 h.w4 (fun k e => by have := hk k e; have := h.w4; omega_arith))
      fun _ ⟨_, f, k⟩ =>
      h.frm f (norm_away (by have := h.w4; omega_arith)) (norm_bound (by have := h.w4; omega_arith) h.z17) k

theorem fastK_ct : RelCT isa (Two KK) (.seq (.block Impl.Rsa.X86_64.WordDivide.normalize)
    Impl.Rsa.X86_64.WordDivide.code) (Two KK) :=
  fastAtK_ct WordDivide.seedCk_none fun _ e => nomatch e

theorem eqAK_ct {a b : Nat} (ha : a < 16) (hb : b < 16) {hc : VG.Taint.Hint VG.X86_64.Taint.T}
    (ht : (taint.check (Taint.ofRegs [.rdi, .r12, .r9]) (.seq (.block (Impl.Rsa.X86_64.Keys.base a .rbx ++
      (Impl.Rsa.X86_64.Keys.base b .r10 ++ ([.mov32 .rbp (.imm 0)] : List Instr))))
      (wordLoop 0 Impl.Rsa.X86_64.Keys.xorBody)) hc).isSome = true) :
    RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.Keys.eqA a b)) (Two KK) := by
  have e : seqs (Impl.Rsa.X86_64.Keys.eqA a b) = .seq (.block (Impl.Rsa.X86_64.Keys.ws ++
      (Impl.Rsa.X86_64.Keys.base a .rbx ++ (Impl.Rsa.X86_64.Keys.base b .r10 ++
      ([.mov32 .rbp (.imm 0)] : List Instr))))) (wordLoop 0 Impl.Rsa.X86_64.Keys.xorBody) := by
    simp only [Impl.Rsa.X86_64.Keys.eqA, seqs, List.append_assoc]
  rw [e]
  exact ws_ct KPub.B KPub.Z KPub.w (fun _ _ h => h.ws) ht fun p s h => by
    rw [← e]
    exact WP.mono (eqA_ok h.ws ha hb) fun _ ⟨_, hm, k⟩ => h.keep hm (k.mono (by decide))

theorem andZeroK_ct : RelCT isa (Two KK) (.block Impl.Rsa.X86_64.Keys.CrtValues.andZero) (Two KK) :=
  two_piece [.rdi] pins_kk (by taint_decide) fun p s h => by
    obtain ⟨s₀, minv, N, c, hs⟩ := h
    exact WP.mono (andZeroK c) fun _ c' => ⟨s₀, minv, N, c', hs⟩

/-! ## The guard -/

/-- The guard's value from the public data. -/
def pubGuard (p : KPub) : BitVec 64 := WordDivide.guardVal p.w p.k p.pl p.ql ((p.nb[0]?).getD 0)

def KGH (p : KPub) (t : State) : Prop := KK p t ∧ t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rdx = p.np

def KGT (p : KPub) (t : State) : Prop := KK p t ∧ t.zf = some (pubGuard p == 0)

theorem guard_ct : RelCT isa (Two KK) (.block guard) (Two KGT) := by
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KGH) [.rdi] pins_kk (by taint_decide) ?_)
    (two_piece [.rdi, .rdx] ?_ (by taint_decide) ?_))
  · intro p s h
    obtain ⟨s₀, minv, N, c, hs⟩ := id h
    obtain ⟨hdi, hl, hw, -⟩ := h.lds
    exact WP.mono (WP.keep [.r12, .rdx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 p.w ∧ t.gpr .rdx = p.np ∧
        t.mem = s.mem) (by
      xrun [guardHead, State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl Impl.Bignum.X86_64.Public.sN (by decide), hw,
        c.hdr _ (show Impl.Bignum.X86_64.Public.sN < 32 by decide) (by decide), hs.hN]) rfl)
      fun t ⟨⟨h12, hdx, hm⟩, k⟩ => ⟨h.keep hm (k.mono (by decide)), h12, hdx⟩
  · intro p s₁ s₂ h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h₁.1.rdi, h₂.1.rdi]
    · rw [h₁.2.2, h₂.2.2]
  · rintro p s ⟨h, h12, hdx⟩
    obtain ⟨s₀, minv, N, c, hs⟩ := id h
    obtain ⟨hdi, hl, -, -⟩ := h.lds
    have sr := c.src hs.srN
    have hnl := hs.nl
    refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.mem = s.mem ∧
      t.zf = some (pubGuard p == 0)) (by
      xrun [guardTail, State.ea, hdr, hdi, h12, hdx, hdrOff,
        hl Impl.Bignum.X86_64.Public.sK (by decide), hl sPlen (by decide), hl sQlen (by decide),
        c.hdr _ (show Impl.Bignum.X86_64.Public.sK < 32 by decide) (by decide), hs.hK,
        c.hdr _ (show sPlen < 32 by decide) (by decide), hs.hPl, c.hdr _ (show sQlen < 32 by decide) (by decide), hs.hQl,
        show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
        show InRegions (s.rd ++ s.wr) p.np 1 by simpa using sr.rd 0 hnl,
        show s.mem p.np = (p.nb[0]?).getD 0 from by simpa [List.getElem?_eq_getElem hnl] using sr.val 0 hnl,
        pubGuard, WordDivide.guardVal]
      rfl) rfl) fun t ⟨⟨hm, hz⟩, k⟩ => ⟨h.keep hm (k.mono (by decide)), hz⟩

/-! ## The word-level checks -/

theorem wordRem_ct : RelCT isa (Two KK) (seqs wordRem) (Two KK) := by
  unfold wordRem
  simp only [List.append_assoc]
  refine kk_app (by simp) (by simp) (copyAK_ct (.inr rfl) (by decide) (by decide) (by taint_decide))
    (kk_app (by simp [loadNum]) (by simp) ?_ (kk_app (by simp) (by simp [Impl.Rsa.X86_64.Keys.eqA]) fastK_ct
      (kk_app (by simp [Impl.Rsa.X86_64.Keys.eqA]) (by simp) (eqAK_ct (by decide) (by decide) (by taint_decide))
        andZeroK_ct)))
  exact loadNumK_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (·.pd) (·.dl)
    (fun _ _ h => ⟨h.hD, h.hDl, h.srD, h.dl1, h.dl2⟩) (by taint_decide) (by taint_decide)

theorem remOne_ct {top : Option Nat} (ck : WordDivide.SeedCk top) (hk : ∀ k, top = some k → k ≤ 3) :
    RelCT isa (Two KK) (seqs (remOne top)) (Two KK) := by
  simp only [remOne, List.append_assoc]
  exact kk_app (by simp) (by simp) (copyAK_ct (.inl rfl) (by decide) (by decide) (by taint_decide))
    (kk_app (by simp) (by simp) (copyAK_ct (.inr rfl) (by decide) (by decide) (by taint_decide))
      (kk_app (by simp) (by simp [Impl.Rsa.X86_64.Keys.eqA]) (fastAtK_ct ck hk)
        (kk_app (by simp [Impl.Rsa.X86_64.Keys.eqA]) (by simp)
          (eqAK_ct (by decide) (by decide) (by taint_decide)) andZeroK_ct)))

/-- `wordMod`, for the factor `X`. -/
theorem wordMod_ct {sX sXlen sDX : Nat}
    (hM : RelCT isa (Two KK) (seqs (loadNum aM sX sXlen)) (Two KK))
    (hDX : RelCT isa (Two KK) (seqs (loadNum aX sDX sXlen)) (Two KK)) :
    RelCT isa (Two KK) (seqs (wordMod sX sXlen sDX)) (Two KK) := by
  simp only [wordMod, List.append_assoc]
  exact kk_app (by simp [loadNum]) (by simp [decM]) hM (kk_app (by simp [decM]) (by simp [loadNum]) decMK_ct
    (kk_app (by simp [loadNum]) (by simp [ltMask]) hDX (kk_app (by simp [ltMask]) (by simp [wordRem]) ltXM
      (kk_app (by simp [wordRem]) (by simp [mulE]) wordRem_ct (kk_app (by simp [mulE])
        (by simp [remOne]) mulEK_ct
        (remOne_ct WordDivide.seedCk_one fun k e => by obtain rfl := Option.some.inj e; decide))))))

theorem wordQInv_ct : RelCT isa (Two KK) (seqs wordQInv) (Two KK) := by
  simp only [wordQInv, List.append_assoc]
  exact kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM (kk_app (by simp [loadNum]) (by simp [ltMask]) ld_QI
    (kk_app (by simp [ltMask]) (by simp [loadNum]) ltXM (kk_app (by simp [loadNum]) (by simp [mulPQ]) ld_QR
      (kk_app (by simp [mulPQ]) (by simp [remOne]) mulPQK_ct
        (remOne_ct WordDivide.seedCk_none fun _ e => nomatch e)))))

theorem wordChecks_ct : RelCT isa (Two KK) (seqs wordChecks) (Two KK) := by
  unfold wordChecks
  simp only [List.append_assoc]
  exact kk_app (by simp [wordMod, loadNum]) (by simp [wordMod, loadNum])
    (wordMod_ct ld_PM ld_DP)
    (kk_app (by simp [wordMod, loadNum]) (by simp [wordQInv, loadNum])
      (wordMod_ct ld_QM ld_DQ)
      wordQInv_ct)

end VG.Proof.Rsa.X86_64.Key

end

end

/-!
# `vg_rsa_check_key` on x86-64: constant time of `main`

The setup (`setupK_ct`), then each check from `KK` (`KeyCTPieces.lean`),
then the result from `rdi` (`main_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (aN aX aAcc aTmp aOne sMask sN sK exit)

theorem mulEWideK_ct : RelCT isa (Two KK) (seqs mulEWide) (Two KK) := by
  unfold mulEWide
  refine RelCT.seqs_append (by simp) (by simp [mulE]) (RelCT.seq ?_ mulEK_ct)
  simpa only [seqs] using
    (zeroArrK_ct (j := aTmp) (by decide) (by decide) (by decide) (by taint_decide)).mono
      (fun _ _ h => h) (fun _ _ h => two_mono (fun _ _ h => h.1) h)

theorem modChecks_ct {sX sXlen sDX sYlen : Nat} (hsXl : sXlen < 32) (nXl : sXlen ≠ sMask) (fl : KPub → Nat)
    (hX : ∀ p s, KS p s → word s.mem p.B (8 * sXlen) = BitVec.ofNat 64 (fl p) ∧ 1 ≤ fl p ∧ fl p ≤ 8 * p.w)
    (hM : RelCT isa (Two KK) (seqs (loadNum aM sX sXlen)) (Two KK))
    (hDX : RelCT isa (Two KK) (seqs (loadNum aX sDX sXlen)) (Two KK))
    (hsYl : sYlen < 32) (nYl : sYlen ≠ sMask) (fy : KPub → Nat)
    (hY : ∀ p s, KS p s → word s.mem p.B (8 * sYlen) = BitVec.ofNat 64 (fy p) ∧ fy p ≤ 8 * p.w)
    {hc₁ hc₂ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (Impl.Rsa.X86_64.CheckCrtKey.lenWords sXlen ++
      Impl.Rsa.X86_64.CheckCrtKey.topE ++
      ([.mov .rax (.reg .r13), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov .rsi (.mem (hdr (sArr aAcc))), .alu .add .rsi (.reg .rax),
        .mov .rbx (.mem (hdr (sArr aR)))] : List Instr))) hc₁).isSome = true)
    (hTD : (taint.check (Taint.ofRegs [.rdi]) (.block (Impl.Rsa.X86_64.CheckCrtKey.lenWords sXlen ++
      topD sYlen ++
      ([.mov .rax (.reg .r13), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .rax (.reg .rax), .mov .rsi (.mem (hdr (sArr aAcc))), .alu .add .rsi (.reg .rax),
        .mov .rbx (.mem (hdr (sArr aR)))] : List Instr))) hc₂).isSome = true) :
    RelCT isa (Two KK) (seqs (modChecks sX sXlen sDX sYlen)) (Two KK) := by
  unfold modChecks
  have hR : RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sXlen
      Impl.Rsa.X86_64.CheckCrtKey.topE)) (Two KK) :=
    reduceTopK_ct fl (fun _ => 1) hsXl nXl hX (fun p s h => by have := (hX p s h).2.2; omega_arith) (fun _ t _ => topE_ok t)
      (fun p s h => by
        obtain ⟨s₀, minv, N, c, hs⟩ := h
        obtain ⟨a, c1, c2⟩ := hX p s₀ hs
        have := c.w2
        exact WP.mono (reduceTopK c (Nx := p.w + 2) hsXl nXl a c1 c2 (fun t _ _ => topE_ok t) (Nat.le_refl _) (by omega_arith)
          (by omega_arith)) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩) hT
  have hD : RelCT isa (Two KK) (seqs (Impl.Rsa.X86_64.CheckCrtKey.reduceTop sXlen
      (topD sYlen))) (Two KK) :=
    reduceTopK_ct fl (fun p => (fy p + 7) / 8 + 1) hsXl nXl hX
      (fun p s h => by have := (hX p s h).2.2; have := (hY p s h).2; omega_arith)
      (fun p s h => by
        obtain ⟨s₀, minv, N, c, hs⟩ := h
        have := c.w2
        obtain ⟨hL, hLw⟩ := hY p s₀ hs
        exact topD_ok c.good c.hZ hsYl (by rw [c.hdr _ hsYl nYl]; exact hL) (by omega_arith))
      (fun p s h => by
        obtain ⟨s₀, minv, N, c, hs⟩ := h
        obtain ⟨a, c1, c2⟩ := hX p s₀ hs
        obtain ⟨y, y2⟩ := hY p s₀ hs
        have := c.w2
        exact WP.mono (reduceTopK c (top := topD sYlen) (c := (fy p + 7) / 8 + 1) (Nx := 2 * p.w + 4) hsXl nXl a c1 c2
          (fun t hg hh => topD_ok hg c.hZ hsYl
            (by rw [hh _ hsYl, c.hdr _ hsYl nYl]; exact y) (by omega_arith))
          (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨c', _, _⟩ => ⟨s₀, minv, N, c', hs⟩) hTD
  refine kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
    (kk_app (by simp [loadNum]) (by simp [mulE]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
    (kk_app (by simp [loadNum]) (by simp [mulEWide]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [ltMask]) (kk_app (by simp [loadNum]) (by simp [loadNum])
    (kk_app (by simp [loadNum]) (by simp [decM]) hM decMK_ct) hDX) ltXM) ld_D) mulEWideK_ct) hD) eqOneK_ct) hDX)
    mulEK_ct) hR) eqOneK_ct

/-- The checks with bit-serial remainders. -/
theorem bitChecks_eq : bitChecks = modChecks sP sPlen sDP sQlen ++ (modChecks sQ sQlen sDQ sPlen ++
    (loadNum aM sP sPlen ++ loadNum aX sQI sPlen ++ ltMask aX aM ++
      loadNum aR sQ sQlen ++ mulPQ ++ Impl.Rsa.X86_64.CheckCrtKey.reduceTop sPlen Impl.Rsa.X86_64.CheckCrtKey.topQ ++
      eqOne)) := by
  simp only [bitChecks, List.append_assoc]

theorem bitChecks_ct : RelCT isa (Two KK) (seqs bitChecks) (Two KK) := by
  rw [bitChecks_eq]
  refine RelCT.seqs_append (by simp [modChecks, loadNum]) (by simp [modChecks, loadNum]) (RelCT.seq
    (modChecks_ct (by decide) (by decide) (·.pl) (fun _ _ h => ⟨h.hPl, h.pl1, h.pl2⟩) ld_PM ld_DP (by decide) (by decide) (·.ql) (fun _ _ h => ⟨h.hQl, h.ql2⟩) (by taint_decide) (by taint_decide)) ?_)
  refine RelCT.seqs_append (by simp [modChecks, loadNum]) (by simp [loadNum]) (RelCT.seq
    (modChecks_ct (by decide) (by decide) (·.ql) (fun _ _ h => ⟨h.hQl, h.ql1, h.ql2⟩) ld_QM ld_DQ (by decide) (by decide) (·.pl) (fun _ _ h => ⟨h.hPl, h.pl2⟩) (by taint_decide) (by taint_decide)) ?_)
  exact kk_app (by simp [loadNum]) (by simp [eqOne]) (kk_app (by simp [loadNum]) (by simp [Impl.Rsa.X86_64.CheckCrtKey.reduceTop])
      (kk_app (by simp [loadNum]) (by simp [mulPQ, VG.Impl.Rsa.X86_64.Crt.zeroAccs])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) (kk_app (by simp [loadNum]) (by simp [ltMask])
      (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PM ld_QI) ltXM) ld_QR) mulPQK_ct) reduceTopQK_ct) eqOneK_ct

/-- `main` is constant time from `M0`. -/
theorem main_ct : RelCT isa (Two M0) main fun _ _ => True := by
  rw [main_eq]
  refine RelCT.seqs_append (by simp) (by simp [loadNum]) (RelCT.seq setupK_ct
    ((RelCT.seqs_append (by simp [loadNum]) (by simp [loadNum]) (RelCT.seq
      (kk_app (by simp [loadNum]) (by simp [ltMask]) ld_D ltXN) ?_)).mono
      (fun _ _ ⟨a, h₁, h₂⟩ => ⟨a.kp, h₁, h₂⟩) fun _ _ h => h))
  refine RelCT.seqs_append (by simp [loadNum]) (by simp) (RelCT.seq
    (kk_app (by simp [loadNum]) (by simp [VG.Impl.Rsa.X86_64.Crt.eqCheck]) (kk_app (by simp [loadNum])
      (by simp [mulPQ, VG.Impl.Rsa.X86_64.Crt.zeroAccs]) (kk_app (by simp [loadNum]) (by simp [loadNum]) ld_PX ld_QR)
      mulPQK_ct) eqCheckK_ct) ?_)
  simp only [seqs]
  refine RelCT.seq (RelCT.seq guard_ct (two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_)) outK_ct
  · exact wordChecks_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h
  · exact bitChecks_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h

end VG.Proof.Rsa.X86_64.Key

end

end

/-!
# `vg_rsa_check_key` on x86-64: constant time

Runs that agree on the public data (the pointers, the lengths, `n` and
`e`) leak the same: `entry` from `rsp` and then the working space's base,
`expCheck` from `e`'s pointer and length, the branch on `e`'s validity,
the modulus' check from `n`'s pointer and length, the branch on its
validity, and `main` (`keyCode_ct`).
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.Key

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.CheckKey
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64.Public (sN sK sMask exit invalid)

/-- The public data of `vg_rsa_check_key`. -/
structure KCPub where
  m : MPub
  rsp : Addr
  ep : Addr
  ecx : BitVec 64
  nb : List Byte
  eb : List Byte

/-- A state the contract allows, with the public data `p`. -/
def KRel (p : KCPub) (s : State) : Prop :=
  keyContract.pre s ∧ s.gpr .rsp = p.rsp ∧ stackArg s 10 = p.m.kp.B ∧ (stackArg s 11).toNat * 8 = p.m.kp.Z ∧
    (s.gpr .rsi).toNat = p.m.k ∧ s.gpr .rdi = p.m.np ∧ s.gpr .rdx = p.ep ∧ s.gpr .rcx = p.ecx ∧
    s.gpr .r8 = p.m.kp.pd ∧ (s.gpr .r9).toNat = p.m.kp.dl ∧ stackArg s 0 = p.m.kp.pp ∧
    (stackArg s 1).toNat = p.m.kp.pl ∧ stackArg s 2 = p.m.kp.pq ∧ (stackArg s 3).toNat = p.m.kp.ql ∧
    stackArg s 4 = p.m.kp.pdp ∧ stackArg s 6 = p.m.kp.pdq ∧ stackArg s 8 = p.m.kp.pqi ∧ keyN s = p.nb ∧
    keyE s = p.eb ∧ (p.m.kp.w = (p.m.k + 7) / 8 ∧ p.m.kp.k = p.m.k ∧ p.m.kp.np = p.m.np ∧ p.m.kp.nb = p.nb)

theorem KRel.B {p : KCPub} {s : State} (h : KRel p s) : stackArg s 10 = p.m.kp.B := h.2.2.1

theorem keyEntry_split : entry = ([.mov .r11 (.mem { base := .rsp, disp := 88 })] : List Instr) ++ entry.drop 1 :=
  rfl

/-- After `entry`'s first instruction. -/
def KC1 (p : KCPub) (t : State) : Prop :=
  ∃ s, KRel p s ∧ t.gpr .r11 = p.m.kp.B ∧ t.gpr .rsp = p.rsp ∧
    WP isa (.block (entry.drop 1)) t (EntryPost s (stackArg s 10))

/-- After `entry`. -/
def KC2 (p : KCPub) (t : State) : Prop := ∃ s, KRel p s ∧ EntryPost s (stackArg s 10) t

/-- After `expCheck`. -/
def KC3 (p : KCPub) (t : State) : Prop :=
  ∃ s t₁, KRel p s ∧ t.zf = some (Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb)) ∧ AfterExp s t₁ t

/-- After the stores, for a valid `e`. -/
def KC3s (p : KCPub) (t : State) : Prop :=
  ∃ s t₁ t₂, KRel p s ∧ Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true ∧ AfterExp s t₁ t₂ ∧
    t.gpr .rdx = s.gpr .rdi ∧ t.gpr .rcx = s.gpr .rsi ∧
    t.mem = t₂.mem.writeW (off (stackArg s 10) (8 * sEv)) (t₂.gpr .r11) ∧ Keep [.rdx, .rcx] t₂ t

/-- After the modulus' check, for a valid `e`. -/
def KC4 (p : KCPub) (t : State) : Prop :=
  ∃ s t₁ t₂ t₃, KRel p s ∧ Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true ∧
    t.zf = some (Spec.Rsa.modulusValid (Spec.Rsa.os2ip p.nb) p.m.k) ∧ AfterInv s t₁ t₂ t₃ t

theorem keyCode_ct : RelCT isa (Two KRel) code fun _ _ => True := by
  unfold code
  refine RelCT.seq (R := Two KC2) ?_ (RelCT.seq (R := Two KC3) ?_ ?_)
  · rw [keyEntry_split]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := KC1) [.rsp] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2.1, h₂.2.1]) (by taint_decide) ?_)
      (two_piece [.r11, .rsp] (fun p s₁ s₂ ⟨_, _, a₁, b₁, _⟩ ⟨_, _, a₂, b₂, _⟩ r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [a₁, a₂]
        · rw [b₁, b₂]) (by taint_decide) fun p t ⟨s, hs, _, _, hw⟩ => WP.mono hw fun t' h => ⟨s, hs, h⟩))
    intro p s hs
    have c := keyArgs_of hs.1
    have hZ := c.hZ
    have := c.k1
    have hw : ∀ i < 32, InRegions s.wr (off (stackArg s 10) (8 * i)) 8 := fun i hi => c.hs.st (by omega_using [hZ, this, hi])
    have hh : WP isa (.block ([.mov .r11 (.mem { base := .rsp, disp := 88 })] ++ entry.drop 1)) s
        (EntryPost s (stackArg s 10)) := by
      rw [← keyEntry_split]; exact keyEntry_ok rfl hw c.ha c.hsep
    have e10 : s.gpr .rsp + BitVec.ofInt 64 88 = stackArgAddr s 10 := rfl
    have hB' : s.mem.readW (stackArgAddr s 10) 64 = stackArg s 10 := rfl
    refine WP.mono (WP.and (WP.block_append_iff.mp hh) (WP.keep [.r11] (Q := fun t => t.gpr .r11 = stackArg s 10)
      (by xrun [State.ea, e10, c.ha 10 (by decide), hB']) rfl)) fun t ⟨hw, h11, k⟩ =>
        ⟨s, hs, h11.trans hs.B, (k.gpr (by decide)).trans hs.2.1, hw⟩
  · refine two_piece [.r8, .r9] (fun p s₁ s₂ ⟨σ₁, c₁, h₁⟩ ⟨σ₂, c₂, h₂⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h₁.r8, h₂.r8, c₁.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.1]
      · rw [h₁.r9, h₂.r9, c₁.2.2.2.2.2.2.2.1, c₂.2.2.2.2.2.2.2.1]) (by taint_decide) ?_
    rintro p t ⟨s, hs, h₁⟩
    have c := keyArgs_of hs.1
    refine WP.mono (expK_ok c h₁) fun t' ⟨hz, hm, h11, k⟩ => ⟨s, t, hs, ?_, h₁, hm, h11, k⟩
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, heb, -⟩ := hs
    rw [hz, heb]
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, z₁, _⟩ ⟨_, _, _, z₂, _⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · -- `fail`.
    exact two_taint [.rdi] (fun p s₁ s₂ ⟨⟨σ₁, _, c₁, _, e₁⟩, _⟩ ⟨⟨σ₂, _, c₂, _, e₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁.rdi, e₂.rdi, c₁.B, c₂.B]) (by taint_decide)
  simp only [seqs]
  refine RelCT.seq (R := Two KC4) (RelCT.block_append (RelCT.seq (R := Two KC3s) ?_ ?_)) ?_
  · refine two_piece [.rdi] (fun p s₁ s₂ ⟨⟨σ₁, _, c₁, _, e₁⟩, _⟩ ⟨⟨σ₂, _, c₂, _, e₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [e₁.rdi, e₂.rdi, c₁.B, c₂.B]) (by taint_decide) ?_
    rintro p t ⟨⟨s, t₁, hs, hz, e⟩, he⟩
    have c := keyArgs_of hs.1
    have hv : Spec.Rsa.exponentValid (Spec.Rsa.os2ip p.eb) = true := by
      simp only [eval, hz] at he; simpa using he
    exact WP.mono (storesK_ok c e) fun t' ⟨hdx, hcx, hm, k⟩ => ⟨s, t₁, t, hs, hv, e, hdx, hcx, hm, k⟩
  · refine two_piece [.rdx, .rcx] (fun p s₁ s₂ ⟨σ₁, _, _, c₁, _, _, d₁, x₁, _⟩ ⟨σ₂, _, _, c₂, _, _, d₂, x₂, _⟩ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [d₁, d₂, c₁.2.2.2.2.2.1, c₂.2.2.2.2.2.1]
      · rw [x₁, x₂, ← ofNat_toNat64 (σ₁.gpr .rsi), ← ofNat_toNat64 (σ₂.gpr .rsi), c₁.2.2.2.2.1, c₂.2.2.2.2.1])
      (by taint_decide) ?_
    rintro p t ⟨s, t₁, t₂, hs, hv, e, hdx, hcx, hm, k⟩
    have c := keyArgs_of hs.1
    refine WP.mono (invalidK_ok c e hdx hcx hm k) fun t' ⟨hz, h⟩ => ⟨s, t₁, t₂, t, hs, hv, ?_, h⟩
    obtain ⟨-, -, -, -, hk, -, -, -, -, -, -, -, -, -, -, -, -, hnb, -, -⟩ := hs
    rw [hz, hnb, hk]
  refine two_ite (fun p s₁ s₂ ⟨_, _, _, _, _, _, z₁, _⟩ ⟨_, _, _, _, _, _, z₂, _⟩ => by simp only [eval, z₁, z₂]) ?_ ?_
  · exact two_taint [.rdi] (fun p s₁ s₂ ⟨⟨σ₁, _, _, _, c₁, _, _, h₁⟩, _⟩ ⟨⟨σ₂, _, _, _, c₂, _, _, h₂⟩, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.rdi, h₂.rdi, c₁.B, c₂.B]) (by taint_decide)
  · have toM : ∀ p t, KC4 p t ∧ isa.eval .ne t = some false → M0 p.m t := by
      rintro p t ⟨⟨s, t₁, t₂, t₃, hs, hv, hz, h⟩, he⟩
      have c := keyArgs_of hs.1
      obtain ⟨-, -, hB, hZ, hk, hnp, -, -, hpd, hdl, hpp, hpl, hpq, hql, hpdp, hpdq, hpqi, hnb, heb, hw⟩ := hs
      have hm : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (keyN s)) (s.gpr .rsi).toNat = true := by
        simp only [eval, hz] at he; rw [hnb, hk]; simpa using he
      rw [← heb] at hv
      have := h.mainPre c hv hm
      rw [hB, hZ, hk, hnp, hpd, hpp, hpq, hpdp, hpdq, hpqi] at this
      exact ⟨_, _, _, _, _, _, _, _, this, hw.1, by rw [bytesAt_length, hdl], by rw [bytesAt_length, hpl],
        by rw [bytesAt_length, hql], hw.2.1, hw.2.2.1, hw.2.2.2.trans hnb.symm⟩
    exact main_ct.mono (fun _ _ h => two_bind (fun p t₁ t₂ h₁ h₂ => ⟨p.m, toM p t₁ h₁, toM p t₂ h₂⟩) h)
      fun _ _ h => h

/-- The public data of a state. -/
def kcpubOf (s : State) : KCPub :=
  ⟨⟨⟨stackArg s 10, (stackArg s 11).toNat * 8, ((s.gpr .rsi).toNat + 7) / 8, s.gpr .r8, stackArg s 0, stackArg s 2,
    stackArg s 4, stackArg s 6, stackArg s 8, (s.gpr .r9).toNat, (stackArg s 1).toNat, (stackArg s 3).toNat,
    (s.gpr .rsi).toNat, s.gpr .rdi, keyN s⟩,
    s.gpr .rdi, (s.gpr .rsi).toNat⟩, s.gpr .rsp, s.gpr .rdx, s.gpr .rcx, keyN s, keyE s⟩

/-- `vg_rsa_check_key` is constant time but for `n` and `e`. -/
theorem keyCode_constantTime : ConstantTime isa keyContract.pre keyContract.pub code := by
  refine RelCT.constantTime (keyCode_ct.mono (fun s₁ s₂ ⟨h₁, h₂, hp⟩ => ⟨kcpubOf s₁, ?_, ?_⟩) fun _ _ h => h)
  · exact ⟨h₁, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨hr, a0, a1, a2, a3, a4, -, a6, -, a8, -, a10, a11, hn, he⟩ := hp
    have r : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₂.gpr r = s₁.gpr r := fun r h => (hr r h).symm
    exact ⟨h₂, r .rsp (by decide), a10.symm, congrArg (·.toNat * 8) a11.symm, congrArg BitVec.toNat (r .rsi (by decide)),
      r .rdi (by decide), r .rdx (by decide), r .rcx (by decide), r .r8 (by decide),
      congrArg BitVec.toNat (r .r9 (by decide)), a0.symm, congrArg BitVec.toNat a1.symm, a2.symm,
      congrArg BitVec.toNat a3.symm, a4.symm, a6.symm, a8.symm, hn.symm, he.symm, rfl, rfl, rfl, rfl⟩

end VG.Proof.Rsa.X86_64.Key
