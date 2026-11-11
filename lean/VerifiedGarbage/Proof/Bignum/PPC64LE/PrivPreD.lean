module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreC
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: the modulus

`partC_ok`: after the factors (`B`), `n`'s values in `pre` (which
`Precompute.core` wrote before the factors) and-ed with the mask, and the
result.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `maskN`'s loop: the `w` words at `r14` (`P`) `&=` the mask of `b`. -/
theorem maskIn_ok {s : State} {P : Addr} {L w : Nat} {b : Bool} (hp : Scr s P L)
    (h14 : s.gpr .r14 = off P 0) (h17 : s.gpr .r17 = BitVec.ofNat 64 w) (h26 : s.gpr .r26 = Crt.bmask b)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hL : 8 * w ≤ L) :
    WP isa (Precompute.countLoop .r17 [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
      .addi .r14 .r14 8]) s fun t =>
      ((∀ i < w, word t.mem P (8 * i) = if b then word s.mem P (8 * i) else 0) ∧
        Outside P 0 (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r17] s t := by
  have hnP := hp.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off P (8 * i) ∧ t.gpr .r26 = Crt.bmask b ∧
      (∀ j < i, word t.mem P (8 * j) = if b then word s.mem P (8 * j) else 0) ∧
      (∀ j, i ≤ j → j < w → word t.mem P (8 * j) = word s.mem P (8 * j)) ∧
      Outside P 0 (8 * i) s.mem t.mem ∧ Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26,
      .store .d .r0 .r14 0, .addi .r14 .r14 8] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j26, jw, jr, jout, jk⟩ _ => ?_)
    ⟨by rw [h14], h26, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, Outside.refl _ _ _ _,
      (Keep.refl [] s).mono (by decide)⟩ h17)
    fun t ⟨_, _, tw, _, tout, tk⟩ => ⟨⟨tw, tout⟩, tk⟩
  have hst : WP isa (.block [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
      .addi .r14 .r14 8, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off P (8 * i + 8) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off P (8 * i)) (word t.mem P (8 * i) &&& Crt.bmask b)) ∧
      Keep [.r0, .r14, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j14, j26, (hp.congr jk.wr).ld (show 8 * i + 8 ≤ L by omega_arith),
      (hp.congr jk.wr).st (show 8 * i + 8 ≤ L by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l14, l17, lm⟩, lk⟩ => ⟨⟨?_, (lk.gpr _ (by decide)).trans j26, fun j hj => ?_,
    fun j hj hj' => ?_, ?_, jk.trans' lk⟩, l17⟩
  · rw [l14, show 8 * i + 8 = 8 * (i + 1) by omega_arith]
  · rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [(writeW_outside t.mem P (d := 8 * i) _ (by omega_arith)).word (by omega_arith) (by omega_arith), jw j hj]
    · rw [word_writeW_self, jr j (Nat.le_refl _) hi, PrivPre.and_bmask]
  · rw [lm, (writeW_outside t.mem P (d := 8 * i) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      jr j (by omega_arith) hj']
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ P (d := 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- What holds after `n`'s values and the mask, from the entry state `s₀`. -/
structure C (s₀ s : State) : Prop where
  r3 : s.gpr .r3 = BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  nW : cb s₀ = true → Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.wordsAt s.mem (s₀.gpr .r3) (2 * cw s₀))
  nZ : cb s₀ = false → ∀ i < 2 * cw s₀, word s.mem (s₀.gpr .r3) (8 * i) = 0
  wP : ∀ i < cwP s₀, word s.mem (s₀.gpr .r3) (16 * cw s₀ + 8 * i) = r2Word (cb s₀) (cwP s₀) (cP s₀) i
  wQ : ∀ i < cwQ s₀, word s.mem (s₀.gpr .r3) (16 * cw s₀ + 8 * cwP s₀ + 8 * i) =
    r2Word (cb s₀) (cwQ s₀) (cQ s₀) i
  r23 : s.gpr .r23 = cS s₀
  keep : Keep (bRegs ++ [.r14, .r17, .r0, .r3]) s₀ s
  sav : ∀ i < 18, s.mem.readW (off (Crt.savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

theorem one_and_bmask (b : Bool) : BitVec.ofNat 64 1 &&& Crt.bmask b = BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> rfl

/-- The words of `wordsAt` from `word`s. -/
theorem wordsAt_eq {m m' : Mem} {P : Addr} {n : Nat} (h : ∀ i < n, word m P (8 * i) = word m' P (8 * i)) :
    Spec.Rsa.wordsAt m P n = Spec.Rsa.wordsAt m' P n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

local macro "oa" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only
  [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith))

/-- `maskN`'s first block: `pre` and `2 w` from the header. -/
theorem maskBlk_ok {s₀ t : State} (hP : PF s₀) (hst : Scr t (cS s₀) (cZ s₀)) (t23 : t.gpr .r23 = cS s₀)
    (hO : word t.mem (cS s₀) oOut = s₀.gpr .r3) (hK : word t.mem (cS s₀) oNLen = s₀.gpr .r6) :
    WP isa (.block [.load .d .r14 .r23 oOut, .load .d .r17 .r23 oNLen, .addi .r17 .r17 7, .lsr .d .r17 .r17 3,
      .lsl .r17 .r17 1]) t fun t3 =>
      (t3.gpr .r14 = off (s₀.gpr .r3) 0 ∧ t3.gpr .r17 = BitVec.ofNat 64 (2 * cw s₀) ∧ t3.mem = t.mem) ∧
        Keep [.r14, .r17] t t3 := by
  have hn := hP.nw; have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  rw [show ([.load .d .r14 .r23 oOut, .load .d .r17 .r23 oNLen, .addi .r17 .r17 7, .lsr .d .r17 .r17 3,
      .lsl .r17 .r17 1] : List Instr) = [.load .d .r14 .r23 oOut] ++ ([.load .d .r17 .r23 oNLen] ++
      [.addi .r17 .r17 7, .lsr .d .r17 .r17 3, .lsl .r17 .r17 1]) from rfl, WP.block_append_iff]
  refine WP.mono (ldH_ok hst t23 (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oOut] at *; omega_arith) (by decide)) fun t1 ⟨⟨a14, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hst.congr k1.wr) ((k1.gpr _ (by decide)).trans t23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oNLen] at *; omega_arith) (by decide))
    fun t2 ⟨⟨a17, m2⟩, k2⟩ => ?_
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have e17 : t2.gpr .r17 = BitVec.ofNat 64 K := by
    rw [a17, m1, hK, ← hKe]; exact (ofNat_toNat64 _).symm
  refine WP.mono (WP.keep [.r17] (Q := fun x => x.gpr .r17 = BitVec.ofNat 64 (2 * cw s₀) ∧ x.mem = t2.mem) (by
      prun [e17, Pre.ofNat_add7_shr3 K (by oa), Pre.ofNat_shl1]
      simp only [cw, hKe]) (by decide)) fun t3 ⟨⟨b17, m3⟩, k3⟩ =>
    ⟨⟨by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), a14, hO]; simp [off], b17, by rw [m3, m2, m1]⟩,
      ((k1.trans k2).trans k3).mono (by decide)⟩

/-- After the factors, `n`'s values and-ed with the mask, and the result. -/
theorem partC_ok {s₀ u : State} (hP : PF s₀) (hB : B s₀ u) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ v, C s₀ v → WP isa c v Q) :
    WP isa (.seq PrivPre.maskN c) u Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have hPS' := sep16 hP
  refine WP.seq ?_
  unfold PrivPre.maskN
  refine WP.seq (WP.mono (maskBlk_ok hP hB.scr hB.r23 hB.hOut hB.hNL) fun t3 ⟨⟨e14, b17, m13⟩, k13⟩ => ?_)
  have hp3 : Scr t3 (s₀.gpr .r3) (16 * cw s₀) := pre16 hP (hB.keep.trans k13).wr
  refine WP.seq (WP.mono (maskIn_ok (b := cb s₀) hp3 e14 b17 ((k13.gpr _ (by decide)).trans hB.r26) (by oa) (by oa)
    (Nat.le_of_eq (by omega_arith))) fun t4 ⟨⟨w4, o4⟩, k4⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun x => x.gpr .r3 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) ∧
      x.mem = t4.mem) (by
        prun [(k4.gpr _ (by decide)).trans ((k13.gpr _ (by decide)).trans hB.r26), one_and_bmask]) (by decide))
    fun t5 ⟨⟨c3, m5⟩, k5⟩ => ?_
  have kall := ((hB.keep.trans k13).trans k4).trans k5
  -- The words of `pre` after the mask, and the header.
  have mh : ∀ d, d + 8 ≤ 256 → word t5.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd => by
    rw [m5, VG.Proof.Bignum.PPC64LE.Outside.word_sep o4 hPS' (by omega_arith) (by oa) (by omega_arith), m13]
  have mp : ∀ d, 16 * cw s₀ ≤ d → d + 8 ≤ (s₀.gpr .r4).toNat * 8 →
      word t5.mem (s₀.gpr .r3) d = word u.mem (s₀.gpr .r3) d := fun d hd hd' => by
    rw [m5, o4.word (Or.inr (by omega_arith)) (by omega_arith), m13]
  have mn : ∀ i < 2 * cw s₀, word t5.mem (s₀.gpr .r3) (8 * i) =
      if cb s₀ then word u.mem (s₀.gpr .r3) (8 * i) else 0 := fun i hi => by
    rw [m5, w4 i hi, m13]
  have hlen : (nB s₀).length = ck s₀ := bytesAt_length _ _ _
  obtain ⟨r, tO⟩ := hB.out
  refine hc t5 ⟨c3, fun hb => ?_, fun hb i hi => by rw [mn i hi, hb]; rfl, fun i hi => ?_, fun i hi => ?_,
    (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans ((k13.gpr _ (by decide)).trans hB.r23)),
    kall.mono (by decide +kernel), fun i hi => ?_, ?_⟩
  · have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = true := by
      have := hb; simp only [cb, privMask, Bool.and_eq_true] at this; exact this.1
    have hs : Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.toWords (cN s₀) (cw s₀) ++
        Spec.Rsa.toWords (2 ^ (128 * cw s₀) % cN s₀) (cw s₀)) := by
      simp only [Spec.Rsa.publicPrecompute, hlen, hv, Spec.Rsa.modulusWords]; rfl
    unfold Pre.preOut at tO
    rw [hs] at tO ⊢
    rw [wordsAt_eq (m' := u.mem) fun i hi => by rw [mn i hi, hb]; rfl, tO.2]
  · rw [mp _ (by omega_arith) (by rw [hpl]; oa), hB.wP i hi]
  · rw [mp _ (by omega_arith) (by rw [hpl]; oa), hB.wQ i hi]
  · have e : off (Crt.savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := by
      simp only [off, Crt.savW]; rw [Offset.add_add]
    rw [e]
    change word t5.mem (cS s₀) (112 + 8 * i) = _
    rw [mh _ (by omega_arith)]
    have h1 := hB.sav i hi
    rw [e] at h1
    exact h1
  · have F2 : Frame [preR s₀, scrR s₀] u.mem t5.mem := by
      rw [m5, ← m13]
      refine (Pre.frame_of_outside o4 (d := 0) (L := 16 * cw s₀) (Nat.le_refl _) (by omega_arith) (Z := (s₀.gpr .r4).toNat * 8)
        (by rw [hpl]; unfold wsWords; oa) hnP).sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨preR s₀, List.mem_cons_self .., Offset.sub_base _ (by rw [hpl]; oa)⟩
    exact hB.frame.trans F2

end VG.Proof.Bignum.PPC64LE.PrivPre
