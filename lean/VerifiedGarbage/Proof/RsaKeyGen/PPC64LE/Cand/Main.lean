module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Tail
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Setup
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.LoadC
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Close
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Gcd
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.RsaKeyGen.Generate
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# A candidate on PPC64LE: once `rand` holds the candidate's octets

`cOp_eq`: what the contract asks, as `afterDraw` of the candidate from the
first `out_len` octets. `main_ok`: the working space set up, the candidate
loaded, then too close to `p`, `gcd(c − 1, e) ≠ 1`, or the test
(`test_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (main setup loadC closeCheck gcdCheck finish nArr aP aBnd aCm1)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl Env arr)
open VG.Proof.Bignum (slot)

theorem take_bytesAt (m : Mem) (A : Addr) {k n : Nat} (h : k ≤ n) :
    (Spec.Rsa.bytesAt m A n).take k = Spec.Rsa.bytesAt m A k := by
  unfold Spec.Rsa.bytesAt
  rw [← List.map_take, List.take_range, Nat.min_eq_left h]

/-- What the contract asks, from the candidate in the first `8 w` octets. -/
theorem cOp_eq {s0 : State} {w : Nat} (hw : oL s0 = 8 * w) (hw1 : 1 ≤ w) (hav : oL s0 ≤ rL s0) :
    cOp s0 = VG.Proof.RsaKeyGen.afterDraw (64 * w)
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat))
      (Spec.RsaKeyGen.otherPrime (Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat))
      (Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (8 * w))))
      ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)) := by
  unfold cOp Spec.RsaKeyGen.candidateOp
  rw [hw, VG.Proof.RsaKeyGen.candidateStep_eq _ _ _ _ (by omega), show 8 * (8 * w) = 64 * w by omega,
    VG.Proof.RsaKeyGen.ite_t (by rw [bytesAt_length]; omega)]
  unfold VG.Proof.RsaKeyGen.seg
  rw [List.drop_zero, take_bytesAt _ _ (by omega)]

/-- Bytes of a readable region. -/
theorem rd_bytes {s : State} {A : Addr} {n k : Nat} (hm : (⟨A, n⟩ : Region) ∈ s.rd) (hA : A.toNat + n ≤ 2 ^ 64)
    (hk : k ≤ n) : ∀ i < k, InRegions (s.rd ++ s.wr) (off A i) 1 := fun i hi =>
  ⟨_, List.mem_append_left _ hm, Offset.contains_base _ (by omega) (by omega)⟩

/-- Bytes of a region apart from the working space. -/
theorem sep_bytes {A B : Addr} {n k Z : Nat} (hd : (⟨A, n⟩ : Region).Disjoint ⟨B, Z⟩) (hA : A.toNat + n ≤ 2 ^ 64)
    (hk : k ≤ n) : ∀ i < k, ∀ x, ofs B x < Z → off A i ≠ x := fun i hi x hx e => by
  refine hd _ (Offset.contains_base _ (d := i) (by omega) (by omega)) ?_
  show Region.Contains _ (off A i) 1
  rw [e]; simp only [Region.Contains]; simp only [ofs] at hx; omega

/-- An input's octets through `Bx`, for an input apart from what the body
writes. -/
theorem in_bytes {s0 s : State} (hb : Bx s0 s) {ρ : Region}
    (hd : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], ρ.Disjoint r) {k : Nat} (hk : k ≤ ρ.len) (hk' : k < 2 ^ 64) :
    Spec.Rsa.bytesAt s.mem ρ.base k = Spec.Rsa.bytesAt s0.mem ρ.base k :=
  bytes_bx hb hk' fun r hr => (hd r hr).sub_left (Region.sub_prefix hk)

theorem ofNat_toNat64 (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The body's state once `rand` has the candidate's octets. -/
structure MIn (s0 s : State) : Prop where
  ctx : Ctx s0 s
  r21 : s.gpr .r21 = s0.gpr .r6
  r30 : s.gpr .r30 = s0.gpr .r7
  r18 : s.gpr .r18 = s0.gpr .r8
  r19 : s.gpr .r19 = s0.gpr .r9
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  r31 : s.gpr .r31 = sB s0
  r11 : s.gpr .r11 = PPC64LE.stackArg s0 2
  hav : oL s0 ≤ rL s0
  syms : s.syms = s0.syms
  tab : TabOk s0

theorem w32_zero {m : Mem} {B : Addr} {d : Nat} (h : word m B d = 0) : w32 m B d = 0 := by
  have := word_eq_w32 m B d
  rw [h] at this
  simp at this
  omega

theorem main_ok {trial : Prog isa} (D : DivOk trial) (R : RoundImpl) {s0 s : State} (h : MIn s0 s) :
    WP isa (main trial R.name R.code) s fun t => Bx s0 t ∧ CQ s0 (t.gpr .r3) t.mem := by
  have hp := h.ctx.bx.pre
  have hv := hp.valid
  simp only [Spec.RsaKeyGen.primeLenValid] at hv
  obtain ⟨w, hw⟩ : ∃ w, oL s0 = 8 * w := ⟨oL s0 / 8, by simp only [oL]; omega⟩
  have hw4 : 4 ≤ w := by simp only [oL] at hw; omega
  have hw64 : w ≤ 64 := by simp only [oL] at hw; omega
  have hscr := hp.scr
  simp only [Spec.Rsa.scratchWords] at hscr
  have hfS := hp.fS
  have hcB := cB_fit hp
  have hav := h.hav
  have eO : oL s0 = (s0.gpr .r4).toNat := rfl
  have eR : rL s0 = (PPC64LE.stackArg s0 0).toNat := rfl
  have eL : sL s0 = (PPC64LE.stackArg s0 2).toNat := rfl
  have eB : (sB s0).toNat = (PPC64LE.stackArg s0 1).toNat := rfl
  have hZ : slot w nArr ≤ 8 * sL s0 := by simp only [nArr, slot_lin]; omega
  have hZ' := hZ
  simp only [nArr, slot_lin] at hZ'
  have hS : Scr s (sB s0) (8 * sL s0) :=
    Scr.of_mem (by rw [h.ctx.bx.wr, bodyWr, hp.wr, ← cS_eq]; simp) (by omega)
  have h24 : s.gpr .r24 = BitVec.ofNat 64 (8 * w) := by rw [h.ctx.r24, ← hw, eO, ofNat_toNat64]
  have hR : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cR s0).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.oR.symm
    · exact hp.uR.symm
    · exact hp.rS
    · exact hp.Fr.symm
  have hfr := hp.fr
  unfold main
  simp only [VG.Impl.RsaKeyGen.PPC64LE.Candidate.seqs]
  -- The working space.
  refine WP.seq (WP.mono_syms (setup_ok hS h.r31 (by rw [h.r11, eL, ofNat_toNat64]) h24 hw4 hw64 hZ)
    fun t₁ ⟨⟨e₁, lay₁, zs, o₁⟩, k₁⟩ sy₁ => ?_)
  have c₁ := h.ctx.step k₁.sp k₁.rd k₁.wr (frame_outs o₁ (fun x hx => by
      simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · omega
      · have : 256 + nArr * (8 * (w + 2)) = slot w nArr := rfl
        exact this ▸ hZ)) (k₁.gpr _ (by decide))
    (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide)) (k₁.gpr _ (by decide))
  -- The candidate.
  have bR : Spec.Rsa.bytesAt t₁.mem (s0.gpr .r10) (8 * w) = Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (8 * w) :=
    in_bytes c₁.bx (ρ := cR s0) hR (by show 8 * w ≤ (PPC64LE.stackArg s0 0).toNat; omega) (by omega)
  refine WP.seq (WP.mono_syms (loadC_ok e₁ ((k₁.gpr _ (by decide)).trans h.r26) ((k₁.gpr _ (by decide)).trans h24)
    (by rw [k₁.rd, k₁.wr]; exact rd_bytes (n := rL s0) (by rw [h.ctx.bx.rd]; exact hp.rR) hfr (by omega))
    (sep_bytes (n := rL s0) (by rw [← cS_eq]; exact hp.rS) hfr (by omega)))
    fun t₂ ⟨⟨v₂, r28₂, o₂⟩, k₂⟩ sy₂ => ?_)
  rw [bR] at v₂
  generalize hc : Spec.RsaKeyGen.candidate (64 * w) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (8 * w)))
    = c at v₂
  have hshape : PrimeShape (64 * w) c := hc ▸ VG.Proof.RsaKeyGen.candidate_shape (by omega) _
  have c₂ := c₁.step k₂.sp k₂.rd k₂.wr (frame_scr (frame_of_outside o₂ (by rw [slot_lin]; omega)))
    (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide)) (k₂.gpr _ (by decide))
  have e₂ := e₁.keep k₂ (by decide)
  have z₂ : ∀ i, w ≤ i → i < nArr * (w + 2) → word t₂.mem (sB s0) (256 + 8 * i) = 0 := fun i h1 h2 => by
    have h2' := h2
    simp only [nArr] at h2'
    rw [o₂.word (by rw [slot_lin]; omega) (by omega), zs i h2]
  have K12 := k₁.trans k₂
  -- Too close to `p`?
  have hP : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cP s0).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.oP.symm
    · exact hp.uP.symm
    · exact hp.pS
    · exact hp.Fp.symm
  have hfp := hp.fp
  have hplv := hp.plv
  have bP : Spec.Rsa.bytesAt t₂.mem (s0.gpr .r8) (s0.gpr .r9).toNat =
      Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat :=
    in_bytes c₂.bx (ρ := cP s0) hP (Nat.le_refl _) (by omega)
  have hcv : val32 t₂.mem (sB s0) (slot w 0) (2 * w) = c := by rw [Pre.val32_eq_wv]; exact v₂
  refine WP.seq (WP.mono_syms (closeCheck_ok e₂ hZ hcv
    (w32_zero (by rw [slot0]; exact z₂ w (by omega) (by simp only [nArr]; omega)))
    (w32_zero (by
      rw [show slot w aP + 8 * w = 256 + 8 * (28 * (w + 2) + w) by simp only [aP, slot_lin]; omega]
      exact z₂ _ (by omega) (by simp only [nArr]; omega)))
    (fun i hi => by
      rw [show slot w aBnd + 8 * i = 256 + 8 * (32 * (w + 2) + i) by simp only [aBnd, slot_lin]; omega]
      exact z₂ _ (by omega) (by simp only [nArr]; omega))
    ((K12.gpr _ (by decide)).trans h.r18) ((K12.gpr _ (by decide)).trans (h.r19.trans (ofNat_toNat64 _).symm))
    (by omega) ((k₂.gpr _ (by decide)).trans ((k₁.gpr _ (by decide)).trans h24))
    (fun hpl => by
      rw [K12.rd, K12.wr]
      exact rd_bytes (n := (s0.gpr .r9).toNat) (by rw [h.ctx.bx.rd]; exact hp.rP) hfp (by omega))
    (fun hpl => sep_bytes (n := (s0.gpr .r9).toNat) (by rw [← cS_eq]; exact hp.pS) hfp (by omega)))
    fun t₃ ⟨⟨f₃, e₃, o₃⟩, k₃⟩ sy₃ => ?_)
  rw [bP] at f₃
  have c₃ := c₂.step k₃.sp k₃.rd k₃.wr (frame_scr (frame_of_outside o₃ (by simp only [aP, slot_lin]; omega)))
    (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide)) (k₃.gpr _ (by decide))
  have hop := cOp_eq (s0 := s0) hw (by omega) hav
  rw [hc] at hop
  have hlen : ((Spec.Rsa.bytesAt s0.mem (s0.gpr .r10) (rL s0)).drop (8 * w)).length = rL s0 - 8 * w := by
    rw [List.length_drop, bytesAt_length]
  have r28₃ : t₃.gpr .r28 = BitVec.ofNat 64 (8 * w) := (k₃.gpr _ (by decide)).trans r28₂
  refine WP.ite _ (eval_nonzero_ofNat' _ _ (by split <;> decide) f₃) (fun hz => ?_) (fun hz => ?_)
  · -- Too close.
    have hcl : Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime
        (Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat)) c = true := by
      revert hz; cases Spec.RsaKeyGen.tooClose (64 * w) _ c <;> decide
    rw [VG.Proof.RsaKeyGen.afterDraw, hcl] at hop
    simp only [↓reduceIte] at hop
    refine fin_ok 2 (by decide) c₃ (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
    rw [r28₃, usedOf, hop]
    simp only [hlen]
    congr 1; omega
  · have hncl : Spec.RsaKeyGen.tooClose (64 * w) (Spec.RsaKeyGen.otherPrime
        (Spec.Rsa.bytesAt s0.mem (s0.gpr .r8) (s0.gpr .r9).toNat)) c = false := by
      revert hz; cases Spec.RsaKeyGen.tooClose (64 * w) _ c <;> decide
    rw [VG.Proof.RsaKeyGen.afterDraw, hncl] at hop
    simp only [Bool.false_eq_true, ↓reduceIte] at hop
    have K123 := K12.trans k₃
    have hE : ∀ r ∈ [cO s0, cU s0, cS s0, cF s0], (cE s0).Disjoint r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.oE.symm
      · exact hp.uE.symm
      · exact hp.eS
      · exact hp.Fe.symm
    have hfe := hp.fe
    have hel1 := hp.el1
    have hel2 := hp.el2
    have bE : Spec.Rsa.bytesAt t₃.mem (s0.gpr .r6) (s0.gpr .r7).toNat =
        Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat :=
      in_bytes c₃.bx (ρ := cE s0) hE (Nat.le_refl _) (by omega)
    have hc₃ : VG.Proof.Bignum.wv t₃.mem (sB s0) (slot w 0) w = c := by
      rw [← Pre.val32_eq_wv, o₃.val32 (by simp only [aP, slot_lin]; omega) (by rw [slot_lin]; omega),
        Pre.val32_eq_wv]
      exact v₂
    refine WP.seq (WP.mono_syms (gcdCheck_ok e₃ hZ hc₃ hshape.1
      ((K123.gpr _ (by decide)).trans (h.r21.trans (BitVec.add_zero _).symm))
      ((K123.gpr _ (by decide)).trans (h.r30.trans (ofNat_toNat64 _).symm)) hel1 hel2
      (by rw [K123.rd, K123.wr]
          exact rd_bytes (n := (s0.gpr .r7).toNat) (by rw [h.ctx.bx.rd]; exact hp.rE) hfe (by omega)))
      fun t₄ ⟨⟨g₄, o₄⟩, k₄⟩ sy₄ => ?_)
    rw [bE] at g₄
    have o₄ : Outside (sB s0) (slot w aCm1) (8 * w) t₃.mem t₄.mem := fun x hx => o₄ x hx
    have c₄ := c₃.step k₄.sp k₄.rd k₄.wr (frame_scr (frame_of_outside o₄ (by simp only [aCm1, slot_lin]; omega)))
      (k₄.gpr _ (by decide)) (k₄.gpr _ (by decide)) (k₄.gpr _ (by decide)) (k₄.gpr _ (by decide))
    have e₄ := e₃.keep k₄ (by decide)
    have K := K123.trans k₄
    have r28₄ : t₄.gpr .r28 = BitVec.ofNat 64 (8 * w) := (k₄.gpr _ (by decide)).trans r28₃
    refine WP.ite _ (VG.PPC64LE.eval_nonzero _ _) (fun hz => ?_) (fun hz => ?_)
    · -- `gcd(c − 1, e) ≠ 1`.
      have hg : ¬ Nat.gcd (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat)) = 1 :=
        fun e => by rw [g₄.mpr e] at hz; exact absurd hz (by decide)
      have hgb : (Nat.gcd (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat)) == 1)
          = false := by simp [hg]
      simp only [hgb, Bool.and_false, Bool.false_eq_true, ↓reduceIte] at hop
      refine fin_ok 3 (by decide) c₄ (by rw [hop]; rfl) (by rw [outOf, hop]) ?_
      rw [r28₄, usedOf, hop]
      simp only [hlen]
      congr 1; omega
    · have hg : Nat.gcd (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat)) = 1 :=
        g₄.mp (by simpa using hz)
      have hgb : (Nat.gcd (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (s0.gpr .r6) (s0.gpr .r7).toNat)) == 1)
          = true := by simp [hg]
      simp only [hgb, Bool.and_true] at hop
      have ow : ∀ d, d + 8 ≤ 256 → word t₄.mem (sB s0) d = word t₁.mem (sB s0) d := fun d hd => by
        rw [o₄.word (by simp only [aCm1, slot_lin]; omega) (by omega),
          o₃.word (by simp only [aP, slot_lin]; omega) (by omega), o₂.word (by rw [slot_lin]; omega) (by omega)]
      refine test_ok D R ⟨c₄, e₄, ⟨(ow 0 (by omega)).trans lay₁.len, (ow 48 (by omega)).trans lay₁.wW,
        (ow 224 (by omega)).trans lay₁.strideW, fun j hj => (ow _ (by omega)).trans (lay₁.arrW j hj)⟩, hZ, ?_, hshape,
        hw, hw64, (K.gpr _ (by decide)).trans h.r26, (K.gpr _ (by decide)).trans h.r27, r28₄, by omega,
        sy₄.trans (sy₃.trans (sy₂.trans (sy₁.trans h.syms))), h.tab, ?_⟩
      · show val32 t₄.mem (sB s0) (slot w 0) (2 * w) = c
        rw [o₄.val32 (by simp only [aCm1, slot_lin]; omega) (by rw [slot_lin]; omega),
          o₃.val32 (by simp only [aP, slot_lin]; omega) (by rw [slot_lin]; omega)]
        exact hcv
      · rw [hop]
        cases Spec.RsaKeyGen.obviouslyComposite (64 * w) c <;> rfl

end VG.Proof.RsaKeyGen.PPC64LE.Cand
