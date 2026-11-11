module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreC
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: the modulus

`partC_ok`: after the factors (`B`), `n`'s values in `pre` (written by
`Precompute.core` before the factors, `PrivPreN.lean`) and-ed with the mask,
and the result.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Crt (wordsOf savW cmask and_mask)

/-- `maskN`'s loop: the `w` words at `t3` (`P`) `&=` the mask of `b` (`t1`). -/
theorem maskIn_ok {s : State} {P : Addr} {L w : Nat} {b : Bool} (hp : Scr s P L)
    (h3 : s.gpr .t3 = P) (h5 : s.gpr .t5 = BitVec.ofNat 64 w) (h1 : s.gpr .t1 = cmask b)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hL : 8 * w ≤ L) :
    WP isa (countLoop .t5 [.load .d .s0 .t3 0, .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0, .addi .t3 .t3 8]) s
      fun t => ((∀ i < w, Mont.word t.mem P (8 * i) = if b then Mont.word s.mem P (8 * i) else 0) ∧
        Mont.Outside P 0 (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t5] s t := by
  have hnP := hp.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = Mont.off P (8 * i) ∧ t.gpr .t1 = cmask b ∧
      (∀ j < i, Mont.word t.mem P (8 * j) = if b then Mont.word s.mem P (8 * j) else 0) ∧
      (∀ j, i ≤ j → j < w → Mont.word t.mem P (8 * j) = Mont.word s.mem P (8 * j)) ∧
      Mont.Outside P 0 (8 * i) s.mem t.mem ∧ Keep [.s0, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t3 0, .logic .and .s0 .s0 .t1,
      .store .d .s0 .t3 0, .addi .t3 .t3 8] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j3, j1, jw, jr, jout, jk⟩ _ => ?_)
    ⟨by rw [h3]; exact (BitVec.add_zero _).symm, h1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl,
      Mont.Outside.refl _ _ _ _, (Keep.refl [] s).mono (by decide)⟩ h5)
    fun t ⟨_, _, tw, _, tout, tk⟩ => ⟨⟨tw, tout⟩, tk⟩
  have hw8 := Mont.writeW_outside t.mem P (d := 8 * i) (Mont.word t.mem P (8 * i) &&& cmask b) (by omega_arith)
  refine WP.mono (WP.keep [.s0, .t3, .t5] (Q := fun t' =>
    t'.mem = t.mem.writeW (Mont.off P (8 * i)) (Mont.word t.mem P (8 * i) &&& cmask b) ∧
      t'.gpr .t3 = Mont.off P (8 * (i + 1)) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl))
    fun t' ⟨⟨a, b3, c⟩, k⟩ => ⟨⟨b3, (k.gpr (by decide)).trans j1, fun j hj => ?_, fun j hj hj' => ?_, ?_,
      Keep.trans' jk k⟩, c⟩
  · brun [add_ofNat_zero, j3, j1, (hp.congr jk.2.2).ld (show 8 * i + 8 ≤ L by omega_arith),
      (hp.congr jk.2.2).al8 (show 8 * i + 8 ≤ L by omega_arith) (by omega_arith),
      (hp.congr jk.2.2).st (show 8 * i + 8 ≤ L by omega_arith)]
    rw [show 8 * i + 8 = 8 * (i + 1) by omega_arith]
  · rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw8.word (by omega_arith) (by omega_arith)]; exact jw j hj
    · rw [Mont.word_writeW_self, jr j (Nat.le_refl _) hi, and_mask]
  · rw [a, hw8.word (by omega_arith) (by omega_arith)]; exact jr j (by omega_arith) hj'
  · rw [a]; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw8.mono (by omega_arith) (by omega_arith))

/-- What holds after `n`'s values and the mask, from the entry state `s₀`. -/
structure C (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  nW : cb s₀ = true → Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.wordsAt s.mem (s₀.gpr .a0) (2 * cw s₀))
  nZ : cb s₀ = false → ∀ i < 2 * cw s₀, Mont.word s.mem (s₀.gpr .a0) (8 * i) = 0
  wP : ∀ i < cwP s₀, Mont.word s.mem (s₀.gpr .a0) (16 * cw s₀ + 8 * i) = r2Word (cb s₀) (cwP s₀) (cP s₀) i
  wQ : ∀ i < cwQ s₀, Mont.word s.mem (s₀.gpr .a0) (16 * cw s₀ + 8 * cwP s₀ + 8 * i) =
    r2Word (cb s₀) (cwQ s₀) (cQ s₀) i
  s6 : s.gpr .s6 = cS s₀
  keep : Keep (bRegs ++ [.t3, .t5, .t1] ++ [.s0, .t3, .t5] ++ [.a0]) s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

theorem one_and_cmask (b : Bool) : BitVec.ofNat 64 1 &&& cmask b = BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> decide

/-- `maskN`'s first block. -/
abbrev maskBlk : List Instr :=
  [.load .d .t3 .s6 oOut, .load .d .t5 .s6 oNLen, .addi .t5 .t5 7, .shift .srl .d .t5 .t5 3,
    .shift .sll .d .t5 .t5 1, .load .d .t1 .s6 oMask]

/-- `maskN`'s first block, after the factors: `pre`, `2 w` and the mask from
the header. -/
theorem maskBlk_ok {s₀ t : State} (hP : PF s₀) (hB : B s₀ t) :
    WP isa (.block maskBlk) t fun x =>
      (x.gpr .t3 = s₀.gpr .a0 ∧ x.gpr .t5 = BitVec.ofNat 64 (2 * cw s₀) ∧ x.gpr .t1 = cmask (cb s₀) ∧
        x.mem = t.mem) ∧ Keep [.t3, .t5, .t1] t x := by
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have hst : Scr t (cS s₀) (cZ s₀) := hB.scr
  have z : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
  have hO : t.mem.readW (cS s₀) 64 = s₀.gpr .a0 := by rw [← z]; exact hB.hOut
  have l0 : InRegions (t.rd ++ t.wr) (cS s₀) 8 := by rw [← z]; exact hst.ld (by omega_arith)
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have hK : t.mem.readW (Mont.off (cS s₀) 16) 64 = BitVec.ofNat 64 K := by
    rw [← hKe]; exact hB.hNL.trans (Pre.ofNat_toNat64 _).symm
  have hM : t.mem.readW (Mont.off (cS s₀) 88) 64 = cmask (cb s₀) := hB.hMask.trans (Crt.cmask_sub _).symm
  exact WP.keep [.t3, .t5, .t1] (Q := fun x => x.gpr .t3 = s₀.gpr .a0 ∧
      x.gpr .t5 = BitVec.ofNat 64 (2 * cw s₀) ∧ x.gpr .t1 = cmask (cb s₀) ∧ x.mem = t.mem) (by
        brun [hB.s6, add_ofNat_zero, oOut, oNLen, oMask, l0, hst.al, hst.ld (show 16 + 8 ≤ cZ s₀ by omega_arith),
          hst.al8 (show 16 + 8 ≤ cZ s₀ by omega_arith) (by decide), hst.ld (show 88 + 8 ≤ cZ s₀ by omega_arith),
          hst.al8 (show 88 + 8 ≤ cZ s₀ by omega_arith) (by decide), hO, hK, hM,
          Pre.ofNat_add7_shr3 K (by omega_arith), Crt.ofNat_shl _ _ (show 1 < 64 by decide), Nat.reducePow]
        rw [dw, hKe]) (by rfl) (by rfl)

/-- After the factors, `n`'s values and-ed with the mask, and the result. -/
theorem partC_ok {s₀ t : State} (hP : PF s₀) (hB : B s₀ t) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ v, C s₀ v → WP isa c v Q) :
    WP isa (.seq PrivPre.maskN c) t Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have hh : hdrBytes = 256 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have hPS' := sep16 hP
  unfold PrivPre.maskN
  refine WP.seq ?_
  refine WP.seq (WP.mono (maskBlk_ok hP hB) fun t3 ⟨⟨e3, b5, b1, m13⟩, k13⟩ => ?_)
  have hp3 : Scr t3 (s₀.gpr .a0) (16 * cw s₀) := pre16 hP (hB.keep.trans k13).2.2
  refine WP.seq (WP.mono (maskIn_ok (b := cb s₀) hp3 e3 b5 b1 (by omega_arith) (by omega_arith)
    (Nat.le_of_eq (by omega_arith))) fun t4 ⟨⟨w4, o4⟩, k4⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun x => x.gpr .a0 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) ∧
      x.mem = t4.mem) (by
        brun [exec_li, (k4.gpr (by decide)).trans b1]
        exact one_and_cmask _) (by rfl) (by rfl))
    fun t5 ⟨⟨c0, m5⟩, k5⟩ => ?_
  have kall := ((hB.keep.trans k13).trans k4).trans k5
  -- The words of `pre` after the mask, and the header.
  have mh : ∀ d, d + 8 ≤ 256 → Mont.word t5.mem (cS s₀) d = Mont.word t.mem (cS s₀) d := fun d hd => by
    rw [m5, VG.Proof.Bignum.RISCV64.Outside.word_sep o4 hPS' (by omega_arith) (by omega_arith) (by omega_arith), m13]
  have mp : ∀ d, 16 * cw s₀ ≤ d → d + 8 ≤ (s₀.gpr .a1).toNat * 8 →
      Mont.word t5.mem (s₀.gpr .a0) d = Mont.word t.mem (s₀.gpr .a0) d := fun d hd hd' => by
    rw [m5, o4.word (Or.inr (by omega_arith)) (by omega_arith), m13]
  have mn : ∀ i < 2 * cw s₀, Mont.word t5.mem (s₀.gpr .a0) (8 * i) =
      if cb s₀ then Mont.word t.mem (s₀.gpr .a0) (8 * i) else 0 := fun i hi => by
    rw [m5, w4 i hi, m13]
  have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
  obtain ⟨r, tO⟩ := hB.out
  refine hc t5 ⟨c0, fun hb => ?_, fun hb i hi => by rw [mn i hi, hb]; rfl, fun i hi => ?_, fun i hi => ?_,
    (k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans ((k13.gpr (by decide)).trans hB.s6)),
    kall.mono fun _ h => by simp only [List.append_assoc] at h ⊢; exact h, fun i hi => ?_, ?_⟩
  · have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = true := by
      have := hb; simp only [cb, privMask, Bool.and_eq_true] at this; exact this.1
    have hs : Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.toWords (cN s₀) (cw s₀) ++
        Spec.Rsa.toWords (2 ^ (128 * cw s₀) % cN s₀) (cw s₀)) := by
      simp only [Spec.Rsa.publicPrecompute, hlen, hv, Spec.Rsa.modulusWords]; rfl
    unfold Pre.preOut at tO
    rw [hs] at tO ⊢
    rw [wordsAt_eq (m' := t.mem) fun i hi => by rw [mn i hi, hb]; rfl, tO.2]
  · rw [mp _ (by omega_arith) (by omega_arith), hB.wP i hi]
  · rw [mp _ (by omega_arith) (by have := Crt.wordsOf_ge (l := cqL s₀); omega_arith), hB.wQ i hi]
  · have esav : off (savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := by
      simp only [off, Mont.off, savW]; rw [Offset.add_add]
    have h1 := hB.sav i hi
    rw [esav] at h1 ⊢
    change Mont.word t5.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [mh _ (by omega_arith)]
    exact h1
  · have F2 : Frame [preR s₀, scrR s₀] t.mem t5.mem := by
      rw [m5, ← m13]
      refine (Pre.frame_of_outside0 o4 (L := 16 * cw s₀) (by omega_arith)).sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨preR s₀, List.mem_cons_self .., sub_len (by omega_arith)⟩
    exact hB.frame.trans F2

end VG.Proof.Bignum.RISCV64.PrivPre
