module

public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtFn
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtLoad
public import VerifiedGarbage.Proof.Bignum.RISCV64.CrtCheck
public import VerifiedGarbage.Spec.Rsa
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubLoad
import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
import VerifiedGarbage.Proof.Bignum.CrtResult
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The RSA private-key operation on RISC-V: `X`'s checks

`checks_ok`: after `loadX`, the checks of `n`, the input, `p`, `q` and
`qInv` into a mask (`crtMask`), `p`, `q` and `qInv` masked, and the mask in
the header. `mask_true` and `masked_facts`: what the mask gives.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.Crt

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot Arrays Frm)

/-- The mask of the checks. -/
def crtMask (N k C P Q QI : Nat) : Bool :=
  Spec.Rsa.modulusValid N k && decide (C < N) && decide (QI < P) && decide (P * Q = N)

/-- All ones if `b`, else 0. -/
abbrev cmask (b : Bool) : BitVec 64 := if b then BitVec.allOnes 64 else 0

theorem cmask_and (a b : Bool) : cmask a &&& cmask b = cmask (a && b) := by
  cases a <;> cases b <;> decide

theorem ite_cmask (p : Prop) [Decidable p] : (if p then BitVec.allOnes 64 else (0 : BitVec 64)) = cmask (decide p) := by
  by_cases h : p <;> simp [cmask, h]

theorem cmask_sub (b : Bool) : cmask b = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> decide

theorem pq_lt {P Q pL qL k w : Nat} (hP : P < 256 ^ pL) (hQ : Q < 256 ^ qL) (hp : pL < k) (hq : qL < k)
    (hw : 16 * k ≤ 64 * w) : P * Q < 2 ^ (64 * w) - 1 := by
  have h1 : P * Q < 256 ^ pL * 256 ^ qL := Nat.mul_lt_mul_of_lt_of_lt hP hQ
  rw [← Nat.pow_add, VG.Proof.Bignum.pow256_eq] at h1
  have h2 : 2 ^ (8 * (pL + qL)) * 2 ≤ 2 ^ (64 * w) := by
    rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  omega_arith

/-- The words `d + 8 i`, `i < w`, each the same word of `m` under the mask of
`b`: `b`'s number, else 0. -/
theorem wordsVal_masked {m m' : Mem} {B : Addr} {b : Bool} :
    ∀ {d w : Nat}, (∀ i < w, Mont.word m' B (d + 8 * i) = Mont.word m B (d + 8 * i) &&& cmask b) →
      wordsVal m' B d w = if b then wordsVal m B d w else 0
  | _, 0, _ => by simp [wordsVal]
  | d, w + 1, h => by
    have h0 := h 0 (by omega_arith)
    rw [Nat.mul_zero, Nat.add_zero] at h0
    have ih := wordsVal_masked (d := d + 8) (w := w) fun i hi => by
      have := h (i + 1) (by omega_arith)
      rwa [show d + 8 * (i + 1) = d + 8 + 8 * i by omega_arith] at this
    simp only [wordsVal, h0, ih]
    cases b
    · simp [cmask]
    · simp only [cmask, ↓reduceIte, BitVec.and_allOnes]

/-- What `checks` changes: the mask's word and arrays 2–7. -/
abbrev chkR (w : Nat) : List (Nat × Nat) := [(oMask, 8), (slot w 2, 6 * (8 * (w + 2)))]

theorem slot_in {w j : Nat} (h2 : 2 ≤ j) (h7 : j ≤ 7) :
    slot w 2 ≤ slot w j ∧ slot w j + 8 * (w + 2) ≤ slot w 2 + 6 * (8 * (w + 2)) := by
  have := VG.Proof.Bignum.slot_le (w := w) (show j < 8 by omega_arith)
  have e : slot w 8 = slot w 2 + 6 * (8 * (w + 2)) := by unfold slot; omega_arith
  exact ⟨by unfold slot; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h2) _, by omega_arith⟩

theorem frm_out {m m' : Mem} {B : Addr} {w j n : Nat} (h : Mont.Outside B (slot w j) n m m') (h2 : 2 ≤ j)
    (h7 : j ≤ 7) (hn : n ≤ 8 * (w + 2)) : Frm B (chkR w) m m' :=
  Frm.widen (Frm.of_outside h (List.mem_singleton_self _)) fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    have := slot_in (w := w) h2 h7
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), this.1, by simp only; omega_arith⟩

theorem frm_arrs {m m' : Mem} {B : Addr} {w : Nat} {js : List Nat} (h : Arrays B w js m m')
    (hj : ∀ j ∈ js, 2 ≤ j ∧ j ≤ 7) : Frm B (chkR w) m m' :=
  Frm.widen (rs := js.map fun j => (slot w j, 8 * (w + 2)))
    (Frm.of_arrays h fun j hj => List.mem_map.mpr ⟨j, hj, rfl⟩) fun r hr => by
    obtain ⟨j, hj', rfl⟩ := List.mem_map.mp hr
    have := slot_in (w := w) (hj j hj').1 (hj j hj').2
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), this.1, by simp only; omega_arith⟩

theorem frm_wordsVal {B : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Frm B rs m m') {d k : Nat}
    (hd : ∀ r ∈ rs, d + 8 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 8 * k ≤ 2 ^ 64) :
    wordsVal m' B d k = wordsVal m B d k := by
  rw [Pre.wordsVal_eq_wv, Pre.wordsVal_eq_wv]; exact h.wv_eq hd hd'

/-- What `checks` gives, from the state `s` it starts in, for the mask `b`. -/
structure Chk (S : Addr) (w : Nat) (b : Bool) (s t : State) : Prop where
  v4 : wordsVal t.mem S (slot w 4) w = if b then wordsVal s.mem S (slot w 4) w else 3
  v5 : wordsVal t.mem S (slot w 5) w = if b then wordsVal s.mem S (slot w 5) w else 3
  v7 : wordsVal t.mem S (slot w 7) w = if b then wordsVal s.mem S (slot w 7) w else 0
  msk : Mont.word t.mem S oMask = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0)
  fr : Frm S (chkR w) s.mem t.mem
  a7 : t.gpr .a7 = Mont.off S (slot w 0)

/-- The registers `checks` writes. -/
def chkRegs : List Reg := [.s9, .s0, .s7, .s8, .t2, .t3, .t4, .t5] ++ pqRegs

theorem checks_ok {s : State} {S Na : Addr} {Z w k : Nat} {nb : List Byte}
    (hs : Scr s S Z) (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h6 : s.gpr .s6 = S) (h7 : s.gpr .a7 = Mont.off S (slot w 0)) (hra : s.gpr .ra = Mont.off S (slot w 0))
    (h5 : s.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2))) (h0 : s.gpr .t0 = BitVec.ofNat 64 w)
    (hN : Mont.word s.mem S oN = Mont.off Na 0) (hNL : Mont.word s.mem S oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (Mont.off Na i) 1)
    (hb : ∀ i (h : i < k), s.mem (Mont.off Na i) = nb[i]'(by omega_arith))
    (hM : wordsVal s.mem S (slot w 0) w = 2 ^ (64 * w) - 1)
    (hM0 : Mont.word s.mem S (slot w 0) = BitVec.allOnes 64)
    (hn1 : wordsVal s.mem S (slot w 1) w = Spec.Rsa.os2ip nb)
    (h1top : Mont.word s.mem S (slot w 1 + 8 * w) = 0) (h6top : Mont.word s.mem S (slot w 6 + 8 * w) = 0)
    (h7top : Mont.word s.mem S (slot w 7 + 8 * w) = 0)
    (hq : wordsVal s.mem S (slot w 5) w < 2 ^ (64 * w) - 1)
    (hpq : wordsVal s.mem S (slot w 4) w * wordsVal s.mem S (slot w 5) w < 2 ^ (64 * w) - 1) :
    WP isa checks s fun t =>
      Chk S w (crtMask (Spec.Rsa.os2ip nb) k (wordsVal s.mem S (slot w 6) w) (wordsVal s.mem S (slot w 4) w)
        (wordsVal s.mem S (slot w 5) w) (wordsVal s.mem S (slot w 7) w)) s t ∧ Keep chkRegs s t := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8
  have hn8 : S.toNat + slot w 8 ≤ 2 ^ 64 := by omega_arith
  unfold checks
  -- `n`.
  refine WP.seq (WP.mono (checkN_ok (nb := nb) hs (by omega_arith) (by rw [h6]; exact z0 _) hN hNL hk hk' hlen hrd hb)
    fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_)
  have hs₁ := hs.congr k1.2.2
  have r7 : s₁.gpr .a7 = Mont.off S (slot w 0) := (k1.gpr (by decide)).trans h7
  have rra : s₁.gpr .ra = Mont.off S (slot w 0) := (k1.gpr (by decide)).trans hra
  have r5 : s₁.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (k1.gpr (by decide)).trans h5
  have r0 : s₁.gpr .t0 = BitVec.ofNat 64 w := (k1.gpr (by decide)).trans h0
  -- The input below `n`.
  refine WP.seq (WP.mono (checkLt_ok (a := 6) (m := 1) hs₁ (by decide) (by decide) (by decide) (by decide)
    (by omega_arith) hw' hZ r7 rra r5 r0 (by rw [m1]; exact h6top)) fun s₂ ⟨⟨b9, o2, b7⟩, k2⟩ => ?_)
  rw [m1] at b9 o2
  have k12 := k1.trans k2
  have hs₂ := hs.congr k12.2.2
  have wv2 : ∀ {j}, j ≠ 3 → j < 8 → wordsVal s₂.mem S (slot w j) w = wordsVal s.mem S (slot w j) w :=
    fun hj hj' => Mont.Outside.wordsVal o2 (by have := VG.Proof.Bignum.slot_sep (w := w) hj; omega_arith)
      (by have := VG.Proof.Bignum.slot_le (w := w) hj'; omega_arith)
  -- `qInv` below `p`.
  refine WP.seq (WP.mono (checkLt_ok (a := 7) (m := 4) hs₂ (by decide) (by decide) (by decide) (by decide)
    (by omega_arith) hw' hZ b7 ((k2.gpr (by decide)).trans rra) ((k2.gpr (by decide)).trans r5)
    ((k2.gpr (by decide)).trans r0)
    (by rw [Mont.Outside.word o2 (d := slot w 7 + 8 * w) (Or.inr (by omega_arith)) (by omega_arith)]; exact h7top))
    fun s₃ ⟨⟨c9, o3, c7⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have hs₃ := hs.congr k13.2.2
  have wv3 : ∀ {j}, j ≠ 3 → j < 8 → wordsVal s₃.mem S (slot w j) w = wordsVal s.mem S (slot w j) w :=
    fun hj hj' => (Mont.Outside.wordsVal o3 (by have := VG.Proof.Bignum.slot_sep (w := w) hj; omega_arith)
      (by have := VG.Proof.Bignum.slot_le (w := w) hj'; omega_arith)).trans (wv2 hj hj')
  have w3 : ∀ d, (d + 8 ≤ slot w 3 ∨ slot w 3 + 8 * w ≤ d) → d + 8 ≤ 2 ^ 64 →
      Mont.word s₃.mem S d = Mont.word s.mem S d := fun d hd hd' => by
    rw [Mont.Outside.word o3 hd hd', Mont.Outside.word o2 hd hd']
  -- `p q = n`.
  refine WP.seq (WP.mono (checkPQ_ok hs₃ hw2 hw' hZ c7 ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans rra))
    ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans r5)) ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans r0))
    (by rw [wv3 (by decide) (by decide)]; exact hM) (by rw [w3 (slot w 0) (by omega_arith) (by omega_arith)]; exact hM0)
    (by rw [wv3 (by decide) (by decide)]; exact hq)
    (by rw [wv3 (by decide) (by decide), wv3 (by decide) (by decide)]; exact hpq)
    (by rw [w3 (slot w 1 + 8 * w) (by omega_arith) (by omega_arith)]; exact h1top))
    fun s₄ ⟨⟨d9, o4, d7⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  have hs₄ := hs.congr k14.2.2
  have wv4 : ∀ {j}, j ≠ 2 → j ≠ 3 → j ≠ 6 → j < 8 → wordsVal s₄.mem S (slot w j) w = wordsVal s.mem S (slot w j) w :=
    fun h2 h3 h6' hj => by
      rw [Pre.wordsVal_eq_wv, o4.wv_of_not_mem hj (by simp; omega_arith) hn8, ← Pre.wordsVal_eq_wv]
      exact wv3 h3 hj
  -- The mask.
  have hmask : s₄.gpr .s9 = cmask (crtMask (Spec.Rsa.os2ip nb) k (wordsVal s.mem S (slot w 6) w)
      (wordsVal s.mem S (slot w 4) w) (wordsVal s.mem S (slot w 5) w) (wordsVal s.mem S (slot w 7) w)) := by
    rw [d9, c9, b9, a9, wv2 (by decide) (by decide), wv2 (by decide) (by decide), wv3 (by decide) (by decide),
      wv3 (by decide) (by decide), wv3 (by decide) (by decide), hn1, ite_cmask, ite_cmask, ite_cmask, ite_cmask,
      Bool.decide_eq_true, cmask_and, cmask_and, cmask_and]
    rfl
  generalize hB : crtMask (Spec.Rsa.os2ip nb) k (wordsVal s.mem S (slot w 6) w) (wordsVal s.mem S (slot w 4) w)
    (wordsVal s.mem S (slot w 5) w) (wordsVal s.mem S (slot w 7) w) = b at hmask
  -- `p`, `q` masked.
  refine WP.seq (WP.mono (orThree_ok (j := 4) (b := b) hs₄ (by decide) d7
    ((k4.gpr (by decide)).trans ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans r5)))
    ((k4.gpr (by decide)).trans ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans r0)))
    (by omega_arith) hw' hZ hmask) fun s₅ ⟨⟨u4, o5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  have hs₅ := hs.congr k15.2.2
  have r7' : s₅.gpr .a7 = Mont.off S (slot w 0) := (k5.gpr (by decide)).trans d7
  have r5' : s₅.gpr .s5 = BitVec.ofNat 64 (8 * (w + 2)) := (k15.gpr (by decide)).trans h5
  have r0' : s₅.gpr .t0 = BitVec.ofNat 64 w := (k15.gpr (by decide)).trans h0
  refine WP.seq (WP.mono (orThree_ok (j := 5) (b := b) hs₅ (by decide) r7' r5' r0' (by omega_arith) hw' hZ
    ((k5.gpr (by decide)).trans hmask)) fun s₆ ⟨⟨u5, o6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  have hs₆ := hs.congr k16.2.2
  -- `qInv` masked.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .t3) (by decide) ((k6.gpr (by decide)).trans r7')
    ((k6.gpr (by decide)).trans r5') 7) fun s₇ ⟨⟨a3, m7⟩, k7⟩ => ?_)
  have k17 := k16.trans k7
  refine WP.seq (WP.mono (maskWords_ok (hs.congr k17.2.2) a3 ((k17.gpr (by decide)).trans h0) (by omega_arith) hw'
    (slot_al w 7) (by omega_arith)) fun s₈ ⟨⟨u7, o8⟩, k8⟩ => ?_)
  rw [m7] at u7 o8
  have k18 := k17.trans k8
  have hs₈ := hs.congr k18.2.2
  have s9' : s₈.gpr .s9 = cmask b := by
    rw [k8.gpr (by decide), k7.gpr (by decide), k6.gpr (by decide), k5.gpr (by decide)]; exact hmask
  -- The mask into the header.
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s₈.mem.writeW (Mont.off S oMask) (cmask b))
    (by brun [(k18.gpr (by decide)).trans h6, oMask, s9', hs₈.st (show 88 + 8 ≤ Z by omega_arith),
      hs₈.al8 (show 88 + 8 ≤ Z by omega_arith) (by decide)]) (by rfl) (by rfl)) fun t ⟨tm, k9⟩ => ?_
  have oM : Mont.Outside S oMask 8 s₈.mem t.mem := by
    rw [tm]; exact Mont.writeW_outside _ S _ (by unfold oMask; omega_arith)
  have fo : ∀ {m m' : Mem} {j}, Mont.Outside S (slot w j) (8 * w) m m' → 2 ≤ j → j ≤ 7 → Frm S (chkR w) m m' :=
    fun h h2 h7' => frm_out h h2 h7' (by omega_arith)
  have F : Frm S (chkR w) s.mem t.mem :=
    ((((((fo o2 (by decide) (by decide)).trans (fo o3 (by decide) (by decide))).trans
      (frm_arrs o4 fun j hj => by simp at hj; omega_arith)).trans (fo o5 (by decide) (by decide))).trans
      (fo o6 (by decide) (by decide))).trans (fo o8 (by decide) (by decide))).trans
      (Frm.of_outside oM (List.mem_cons_self ..))
  have wo : ∀ {m m' : Mem} {o n : Nat}, Mont.Outside S o n m m' → ∀ {j}, j < 8 →
      (slot w j + 8 * w ≤ o ∨ o + n ≤ slot w j) → wordsVal m' S (slot w j) w = wordsVal m S (slot w j) w :=
    fun h j hj hd => Mont.Outside.wordsVal h hd (by have := VG.Proof.Bignum.slot_le (w := w) hj; omega_arith)
  have s9₇ : s₇.gpr .s9 = cmask b :=
    (k7.gpr (by decide)).trans ((k6.gpr (by decide)).trans ((k5.gpr (by decide)).trans hmask))
  refine ⟨⟨?_, ?_, ?_, ?_, F, ?_⟩, (k18.trans k9).mono (by decide)⟩
  · rw [wo oM (j := 4) (by decide) (Or.inr (by unfold oMask; omega_arith)), wo o8 (j := 4) (by decide)
      (Or.inl (by omega_arith)), wo o6 (j := 4) (by decide) (Or.inl (by omega_arith)), u4,
      wv4 (by decide) (by decide) (by decide) (by decide)]
  · rw [wo oM (j := 5) (by decide) (Or.inr (by unfold oMask; omega_arith)), wo o8 (j := 5) (by decide)
      (Or.inl (by omega_arith)), u5, wo o5 (j := 5) (by decide) (Or.inr (by omega_arith)),
      wv4 (by decide) (by decide) (by decide) (by decide)]
  · rw [wo oM (j := 7) (by decide) (Or.inr (by unfold oMask; omega_arith)),
      wordsVal_masked (m := s₆.mem) (m' := s₈.mem) (B := S) (d := slot w 7) (w := w) (b := b)
        (fun i hi => by rw [u7 i hi, s9₇]),
      wo o6 (j := 7) (by decide) (Or.inr (by omega_arith)), wo o5 (j := 7) (by decide) (Or.inr (by omega_arith)),
      wv4 (by decide) (by decide) (by decide) (by decide)]
  · rw [tm]; exact (Mont.word_writeW_self _ _ _ _).trans (cmask_sub b)
  · exact (k9.gpr (by decide)).trans ((k8.gpr (by decide)).trans ((k7.gpr (by decide)).trans
      ((k6.gpr (by decide)).trans r7')))

end VG.Proof.Bignum.RISCV64.Crt
