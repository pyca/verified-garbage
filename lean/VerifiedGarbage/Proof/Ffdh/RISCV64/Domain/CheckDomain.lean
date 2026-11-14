module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.Rel
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Domain.Rel
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Ffdh.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Power
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Ffdh.Domain
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Ffdh.RISCV64.Power
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_check_domain` on RISC-V: correctness

`vg_ffdh_check_domain(domain = a0, domain_len = a1, p_len = a2,
scratch = a3, scratch_len = a4)` (`cdContract`): `checkDomain` saves the
callee-saved registers and sets up (`cdFront_ok`), loads and checks p
(`loadP_P`), checks g and q (`domainBody_ok`: `withQ_ok`, `withoutQ_ok`) and
restores the registers (`cd_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Domain

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Domain
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-! ## The branches -/

/-- `withoutQ`: g's range. -/
theorem withoutQ_ok {x : DD} {s : State} (h : PV x s) :
    WP isa withoutQ s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if 1 < x.g ∧ x.g < x.p - 1 then 1 else 0)) ∧ DArr x s.mem t.mem := by
  unfold withoutQ
  refine WP.seq (WP.mono (gPtr_ok h.1) fun s₁ ⟨⟨a6, m1⟩, k1⟩ => ?_)
  have p1 : PV x s₁ := h.keep k1 (by rw [m1]; exact DArr.refl _ _) (by rw [m1])
  refine WP.seq (WP.mono (range_g p1 a6) fun s₂ ⟨⟨r2, a2⟩, _⟩ => ?_)
  refine WP.mono (retMask_ok r2.1.1 r2.2.2) fun t ⟨ht, a3⟩ => ⟨ht, ?_⟩
  rw [m1] at a2
  exact a2.trans a3

/-- The condition `withQ` checks. -/
def qCond (x : DD) : Prop :=
  ((1 < x.q ∧ x.q < x.p - 1) ∧ x.q % 2 = 1) ∧ ((1 < x.g ∧ x.g < x.p - 1) ∧ x.p % x.q = 1) ∧
    x.g ^ x.q % x.p = 1

instance (x : DD) : Decidable (qCond x) := by unfold qCond; infer_instance

/-- After the checks of q: what `withQ`'s last branch tests. -/
theorem withQ_tail {x : DD} {s : State} (h : RG x x.g s) (hq : x.L = 3 * x.k)
    (hq1 : (1 < x.q ∧ x.q < x.p - 1) ∧ x.q % 2 = 1) (h10 : s.gpr .s10 = bmask (decide (x.p % x.q = 1))) :
    WP isa (.seq (.block [.logic .and .s9 .s9 .s10]) (.ite (.zero .s9) (.block [.li .a0 0]) subgroup)) s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if qCond x then 1 else 0)) ∧ DArr x s.mem t.mem := by
  obtain ⟨p0, g4, g9⟩ := h
  refine WP.seq (WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = s.gpr .s9 &&& s.gpr .s10 ∧ t.mem = s.mem)
    (by brun) (by rfl) (by rfl)) fun s₁ ⟨⟨a9, m1⟩, k1⟩ => ?_)
  rw [g9, h10, bmask_and] at a9
  have p1 : PV x s₁ := p0.keep k1 (by rw [m1]; exact DArr.refl _ _) (by rw [m1])
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [a9, bmask_beq] at hb
    refine WP.mono (fail_ok p1.1 (c := qCond x) fun hc => ?_) fun t ⟨ht, ar⟩ =>
      ⟨ht, by rw [m1] at ar; exact ar⟩
    exact not_and_of hb hc.2.1
  · rw [a9, bmask_beq] at hb
    refine WP.mono (subgroup_ok (v := x.g) p1 (by rw [m1]; exact g4) hq) fun t ⟨⟨ht, t0⟩, ar⟩ =>
      ⟨⟨ht, ?_⟩, by rw [m1] at ar; exact ar⟩
    rw [t0]
    have hb' : (1 < x.g ∧ x.g < x.p - 1) ∧ x.p % x.q = 1 := by simpa using hb
    unfold qCond
    simp only [hq1, hb', true_and]

/-- `withQ`: q's range and oddness, `p mod q = 1`, g's range, the subgroup. -/
theorem withQ_ok {x : DD} {s : State} (h : PV x s) (hq : x.L = 3 * x.k) :
    WP isa withQ s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if qCond x then 1 else 0)) ∧ DArr x s.mem t.mem := by
  unfold withQ
  refine WP.seq (WP.mono (qPtrA_ok h.1) fun s₁ ⟨⟨a6, m1⟩, k1⟩ => ?_)
  have p1 : PV x s₁ := h.keep k1 (by rw [m1]; exact DArr.refl _ _) (by rw [m1])
  refine WP.seq (WP.mono (range_q p1 hq a6) fun s₂ ⟨⟨r2, a2⟩, _⟩ => ?_)
  refine WP.seq (WP.mono (qOdd_ok r2.1 r2.2.1 r2.2.2) fun s₃ ⟨⟨a9, m3⟩, k3⟩ => ?_)
  have p3 : PV x s₃ := r2.1.keep k3 (by rw [m3]; exact DArr.refl _ _) (by rw [m3])
  have ar3 : DArr x s.mem s₃.mem := by rw [m3, ← m1] at *; exact a2
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [a9, bmask_beq] at hb
    refine WP.mono (fail_ok p3.1 (c := qCond x) fun hc => ?_) fun t ⟨ht, ar⟩ => ⟨ht, ar3.trans ar⟩
    exact not_and_of hb hc.1
  · rw [a9, bmask_beq] at hb
    have hq1 : (1 < x.q ∧ x.q < x.p - 1) ∧ x.q % 2 = 1 := by simpa using hb
    refine WP.seq (WP.mono (qDiv_ok p3 ⟨p3.2.2, by omega, hq⟩) fun s₄ ⟨⟨p4, a10⟩, ar4⟩ => ?_)
    refine WP.seq (WP.mono (gPtr_ok p4.1) fun s₅ ⟨⟨b6, m5⟩, k5⟩ => ?_)
    have p5 : PV x s₅ := p4.keep k5 (by rw [m5]; exact DArr.refl _ _) (by rw [m5])
    refine WP.seq (WP.mono (range_g p5 b6) fun s₆ ⟨⟨r6, ar6⟩, k6⟩ => ?_)
    refine WP.mono (withQ_tail r6 hq hq1 (by rw [k6.gpr (by decide), k5.gpr (by decide)]; exact a10))
      fun t ⟨ht, art⟩ => ⟨ht, ar3.trans (ar4.trans (by rw [m5] at ar6; exact ar6.trans art))⟩

/-- What `domainBody` checks. -/
def bodyCond (x : DD) : Prop := if x.L = 3 * x.k then qCond x else 1 < x.g ∧ x.g < x.p - 1

instance (x : DD) : Decidable (bodyCond x) := by unfold bodyCond; infer_instance

/-- `domainBody`: q's and g's checks. -/
theorem domainBody_ok {x : DD} {s : State} (h : PV x s) :
    WP isa domainBody s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if bodyCond x then 1 else 0)) ∧ DArr x s.mem t.mem := by
  unfold domainBody
  refine WP.seq (WP.mono (hasQ_ok h.1) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have p1 : PV x s₁ := h.keep k1 (by rw [m1]; exact DArr.refl _ _) (by rw [m1])
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hq : x.L = 3 * x.k := a3.mp (by simpa using hb)
    refine WP.mono (withQ_ok p1 hq) fun t ⟨⟨ht, t0⟩, ar⟩ => ⟨⟨ht, ?_⟩, by rw [m1] at ar; exact ar⟩
    have e : bodyCond x = qCond x := ite_eq_left hq
    rw [t0]; simp only [e]
  · have hq : x.L ≠ 3 * x.k := fun e => by simp [a3.mpr e] at hb
    refine WP.mono (withoutQ_ok p1) fun t ⟨⟨ht, t0⟩, ar⟩ => ⟨⟨ht, ?_⟩, by rw [m1] at ar; exact ar⟩
    have e : bodyCond x = (1 < x.g ∧ x.g < x.p - 1) := ite_eq_right hq
    rw [t0]; simp only [e]

/-- After p's check. -/
theorem cdBranch_ok {x : DD} {s : State} (h : P4 x s) :
    WP isa (.ite (.zero .s0) domainBody (.block [.li .a0 0])) s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64
        (if Spec.Rsa.modulusValid x.p x.k = true ∧ bodyCond x then 1 else 0)) ∧ DArr x s.mem t.mem := by
  obtain ⟨hb, hp, h0⟩ := h
  refine WP.ite _ (Steps.eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have hv := h0.mp (by simpa using hz)
    refine WP.mono (domainBody_ok ⟨hb, hp, hv⟩) fun t ⟨⟨ht, t0⟩, ar⟩ => ⟨⟨ht, ?_⟩, ar⟩
    rw [t0]; simp only [hv, true_and]
  · exact fail_ok hb fun hc => by simp [h0.mpr hc.1] at hz

theorem mod_one_iff {p q : Nat} (hq : 2 ≤ q) (hp : 1 ≤ p) : p % q = 1 ↔ (p - 1) % q = 0 := by
  have e := Nat.div_add_mod p q
  constructor
  · intro h
    rw [h] at e
    rw [show p - 1 = q * (p / q) by omega, Nat.mul_mod_right]
  · intro h
    have e' := Nat.div_add_mod (p - 1) q
    rw [h, Nat.add_zero] at e'
    rw [show p = q * ((p - 1) / q) + 1 by omega, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hq

/-- `domainValid`, as `checkDomain` computes it. -/
theorem dv_iff (x : DD) (hlen : x.db.length = x.L) (hL : x.L = 2 * x.k ∨ x.L = 3 * x.k) (hk : 64 ≤ x.k) :
    Spec.Ffdh.domainValid x.k x.db = true ↔ Spec.Rsa.modulusValid x.p x.k = true ∧ bodyCond x := by
  rw [Proof.Ffdh.domainValid_iff]
  simp only [Spec.Ffdh.domainOf, hlen]
  unfold bodyCond
  rcases hL with e | e
  · rw [ite_eq_right (show ¬x.L = 3 * x.k by omega), ite_eq_right (show ¬x.L = 3 * x.k by omega)]
    simp only [reduceCtorEq, false_imp_iff, imp_true_iff, and_true]
  · rw [ite_eq_left e, ite_eq_left e]
    simp only [Option.some.injEq, forall_eq']
    unfold qCond
    simp only [DD.p, DD.g, DD.q]
    constructor
    · rintro ⟨hv, hg, ⟨hq1, hq2, hq3⟩, hd, hgq⟩
      have := (VG.Proof.Bignum.valid_facts hv (by omega)).2.1
      exact ⟨hv, ⟨⟨hq2, hq3⟩, hq1⟩, ⟨hg, (mod_one_iff (by omega) (by omega)).mpr hd⟩, hgq⟩
    · rintro ⟨hv, ⟨⟨hq2, hq3⟩, hq1⟩, ⟨hg, hd⟩, hgq⟩
      have := (VG.Proof.Bignum.valid_facts hv (by omega)).2.1
      exact ⟨hv, hg, ⟨hq1, hq2, hq3⟩, (mod_one_iff (by omega) (by omega)).mp hd, hgq⟩

/-! ## The function -/

/-- `domain`, `domain_len` bytes at `a0`. -/
abbrev cdDom (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩

/-- The working space, `scratch_len` words at `a3`. -/
abbrev cdScr (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat * 8⟩

/-- `vg_ffdh_check_domain`, on the registers. -/
def cdContract : Contract isa where
  pre s :=
    s.rd = [cdDom s] ∧ s.wr = [cdScr s] ∧ (cdDom s).Disjoint (cdScr s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Ffdh.pLenValid (s.gpr .a2).toNat ∧ Spec.Ffdh.domainLenValid (s.gpr .a2).toNat (s.gpr .a1).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .a2).toNat ≤ (s.gpr .a4).toNat ∧ (s.gpr .a3).toNat % 8 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat =
      if Spec.Ffdh.domainValid (s.gpr .a2).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) then 1
      else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat).map (·.toNat)

/-- The public data of a run. -/
def cdData (s : State) : DD :=
  ⟨s.gpr .a0, (s.gpr .a1).toNat, (s.gpr .a2).toNat, s.gpr .a3, (s.gpr .a4).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat, s.gpr .a0,
    (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).take (s.gpr .a2).toNat⟩

/-- The registers the front writes. -/
def cdFrontRegs : List Reg := [.t0, .s6, .s7, .s8, .a1, .a7, .s5, .s10, .s11]

/-- The front: the registers saved, the domain and its length in the header,
`setup`. -/
theorem cdFront_ok {s : State} (h : cdContract.pre s) :
    WP isa (.block cdFront) s fun t => P1 (cdData s) t ∧
      (∀ i < 12, t.mem.readW (off (Pub.savW (s.gpr .a3)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
      Keep cdFrontRegs s t ∧ Outside (s.gpr .a3) 0 256 s.mem t.mem := by
  obtain ⟨hrd, hwr, dDS, nwD, nwS, ⟨hk, hk'⟩, hL, hsl, alS⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat ∨ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hL
  have hs : Scr s (s.gpr .a3) ((s.gpr .a4).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) nwS alS
  rw [show cdFront = ([.addi .t0 .a3 0] ++ PublicChecked.saveRegs) ++ ([.store .d .a0 .s6 0] ++
      ([.store .d .a1 .s6 8] ++ (args ++ PublicChecked.setup))) by
    simp only [cdFront, List.append_assoc, List.cons_append, List.nil_append]]
  refine WP.block_append (WP.mono (pre_ok .a3 rfl hs (by omega_arith)) fun s₁ ⟨h61, sv1, k1, o1⟩ => ?_)
  refine WP.block_append (WP.mono (sth_ok (hs.congr k1.2.2) (by omega_arith) h61 .a0 (d := 0) (by decide)
    (by decide)) fun s₂ ⟨⟨w0, o2⟩, k2⟩ => ?_)
  refine WP.block_append (WP.mono (sth_ok (hs.congr (k1.trans k2).2.2) (by omega_arith)
    ((k2.gpr (by decide)).trans h61) .a1 (d := 8) (by decide) (by decide)) fun s₃ ⟨⟨w8, o3⟩, k3⟩ => ?_)
  have k13 := (k1.trans k2).trans k3
  refine WP.mono (tail_ok (k := (s.gpr .a2).toNat) ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans h61))
    (by rw [k13.gpr (by decide), ofNat_toNat']) hk') fun t ⟨⟨t7, t8, t11, t0, t5, ta7, t6, tm⟩, kt⟩ => ?_
  have hn := hs.nowrap
  have hZ : 256 + 128 * (s.gpr .a2).toNat ≤ (s.gpr .a4).toNat * 8 := by omega_arith
  have hO : Outside (s.gpr .a3) 0 256 s.mem t.mem := by
    rw [tm]
    exact (o1.trans (o2.mono (Nat.le_refl _) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))
  have sepD := Pub.ne_of_disjoint dDS (Nat.le_of_lt (s.gpr .a1).isLt)
  have rdD : ∀ i < (s.gpr .a1).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a0) i) 1 := by
    rw [(k13.trans kt).2.1, (k13.trans kt).2.2]
    exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have bD : Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat :=
    Pub.bytes_apart (o := 0) (n := 256) hO (by omega_arith) sepD
  have hw0 : word t.mem (s.gpr .a3) 0 = s.gpr .a0 := by
    rw [tm, Outside.word o3 (by omega_arith) (by omega_arith), w0, k1.gpr (by decide)]
  have hw8 : word t.mem (s.gpr .a3) 8 = BitVec.ofNat 64 (s.gpr .a1).toNat := by
    rw [tm, w8, k2.gpr (by decide), k1.gpr (by decide), ofNat_toNat']
  refine ⟨⟨⟨⟨hs.congr (k13.trans kt).2.2, hk, hk', hLk, ?_, rdD, sepD, bD,
      fun i hi => rdD i (by change i < (s.gpr .a2).toNat at hi; rcases hLk with e | e <;> omega_arith),
      fun i hi => sepD i (by change i < (s.gpr .a2).toNat at hi; rcases hLk with e | e <;> omega_arith), ?_, hw0,
      hw8⟩,
      t6, ta7, by rw [t5, Nat.mul_add]; rfl, t0, t11⟩,
    by rw [t7, k13.gpr (by decide)]; exact (BitVec.add_zero _).symm, t8⟩, fun i hi => ?_,
    (k13.trans kt).mono (by decide), hO⟩
  · show slot (((s.gpr .a2).toNat + 7) / 8) 24 ≤ (s.gpr .a4).toNat * 8
    unfold slot hdrBytes; omega_arith
  · show Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a2).toNat =
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).take (s.gpr .a2).toNat
    rw [← bD, Proof.Ffdh.take_bytesAt _ _ (by rcases hLk with e | e <;> omega_arith)]
  · have e : off (Pub.savW (s.gpr .a3)) (8 * i) = off (s.gpr .a3) (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← sv1 i hi, tm, e]
    show word s₃.mem (s.gpr .a3) (128 + 8 * i) = word s₁.mem (s.gpr .a3) (128 + 8 * i)
    rw [Outside.word o3 (by omega_arith) (by omega_arith), Outside.word o2 (by omega_arith) (by omega_arith)]

theorem cd_correct (s : State) (h : cdContract.pre s) :
    ∃ tr t, Exec isa checkDomain s tr t ∧ abiPreserved s t ∧ cdContract.post s t := by
  show WP isa checkDomain s fun t => abiPreserved s t ∧ cdContract.post s t
  suffices main : WP isa checkDomain s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ cdContract.post s t from
    WP.mono (WP.rdwr (WP.keep dNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dDS, nwD, nwS, ⟨hk, hk'⟩, hL, hsl, alS⟩ := h
  unfold checkDomain
  refine WP.seq (WP.mono (cdFront_ok hpre) fun s₃ ⟨h1, hsv, _, _⟩ => ?_)
  refine WP.seq (WP.mono (loadP_P h1) fun s₄ ⟨h4, a4⟩ => ?_)
  refine WP.seq (WP.mono (cdBranch_ok h4) fun t₅ ⟨⟨b5, t0⟩, a5⟩ => ?_)
  have hc := b5.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have h24 : 256 ≤ slot (cdData s).w 24 := by unfold slot hdrBytes; omega_arith
  refine WP.mono (dRestore_ok b5 fun i hi => ?_) fun u ⟨urs, u0⟩ => ⟨urs, ?_⟩
  · have e : off (Pub.savW (s.gpr .a3)) (8 * i) = off (s.gpr .a3) (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hsv i hi, e]
    show word t₅.mem (cdData s).S (128 + 8 * i) = word s₃.mem (cdData s).S (128 + 8 * i)
    rw [Outside.word a5 (Or.inl (by omega_arith)) (by omega_arith),
      Outside.word a4 (Or.inl (by omega_arith)) (by omega_arith)]
  · show ((u.gpr .a0).setWidth 32).toNat = _
    rw [u0, t0, ret_bv32]
    refine ite_congr (propext (dv_iff (cdData s) (VG.Proof.Bignum.bytesAt_length _ _ _) hL hk).symm)
      (fun _ => rfl) (fun _ => rfl)

/-! ## Constant time -/

open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- On entry. -/
def C0 (x : DD) (s : State) : Prop := cdContract.pre s ∧ cdData s = x

theorem pins_C0 : Pins C0 [.a0, .a1, .a2, .a3, .a4] := by
  rintro x s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  subst h₁
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have e := congrArg DD.D h₂; have e1 := congrArg DD.L h₂; have e2 := congrArg DD.k h₂
  have e3 := congrArg DD.S h₂; have e4 := congrArg DD.Z h₂
  simp only [cdData] at e e1 e2 e3 e4
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact e.symm
  · exact BitVec.eq_of_toNat_eq e1.symm
  · exact BitVec.eq_of_toNat_eq e2.symm
  · exact e3.symm
  · exact BitVec.eq_of_toNat_eq (by omega)

/-- q's range and oddness. -/
def QR (x : DD) : Prop := (1 < x.q ∧ x.q < x.p - 1) ∧ x.q % 2 = 1

/-- The `and` of g's mask with that of `p mod q = 1`. -/
theorem and9_ok {x : DD} {s : State} {c : Bool} (h : RG x x.g s) (h10 : s.gpr .s10 = bmask c) :
    WP isa (.block [.logic .and .s9 .s9 .s10]) s fun t =>
      PV x t ∧ wordsVal t.mem x.S (slot x.w 4) x.w = x.g ∧
        t.gpr .s9 = bmask (decide (1 < x.g ∧ x.g < x.p - 1) && c) := by
  refine WP.mono (WP.keep [.s9] (Q := fun t => t.gpr .s9 = s.gpr .s9 &&& s.gpr .s10 ∧ t.mem = s.mem)
    (by brun) (by rfl) (by rfl)) fun t ⟨⟨a9, m1⟩, k1⟩ =>
      ⟨h.1.keep k1 (by rw [m1]; exact DArr.refl _ _) (by rw [m1]), by rw [m1]; exact h.2.1, ?_⟩
  rw [a9, h.2.2, h10, bmask_and]

/-- The predicates at the cuts of `withQ` and `withoutQ`. -/
def QA' (x : DD) (s : State) : Prop := QA x s ∧ QR x
def QB' (x : DD) (s : State) : Prop := QB x s ∧ QR x
def QC' (x : DD) (s : State) : Prop := QC x s ∧ QR x
def QD' (x : DD) (s : State) : Prop := QD x s ∧ QR x
def QE' (x : DD) (s : State) : Prop := QE x s ∧ QR x ∧ x.L = 3 * x.k
def GE (x : DD) (s : State) : Prop := QE' x s ∧ s.gpr .a6 = off x.D x.k
def RGQ (x : DD) (s : State) : Prop :=
  RG x x.g s ∧ s.gpr .s10 = bmask (decide (x.p % x.q = 1)) ∧ QR x ∧ x.L = 3 * x.k
def TA (x : DD) (s : State) : Prop :=
  (PV x s ∧ wordsVal s.mem x.S (slot x.w 4) x.w = x.g ∧
    s.gpr .s9 = bmask (decide (1 < x.g ∧ x.g < x.p - 1) && decide (x.p % x.q = 1))) ∧ x.L = 3 * x.k
def W0 (x : DD) (s : State) : Prop := PV x s ∧ x.L = 3 * x.k
def W1 (x : DD) (s : State) : Prop := W0 x s ∧ s.gpr .a6 = off x.D (2 * x.k)
def W2 (x : DD) (s : State) : Prop := RG x x.q s ∧ x.L = 3 * x.k
def W3 (x : DD) (s : State) : Prop :=
  PV x s ∧ x.L = 3 * x.k ∧ s.gpr .s9 = bmask (decide (1 < x.q ∧ x.q < x.p - 1) && decide (x.q % 2 = 1))
def W4 (x : DD) (s : State) : Prop := PV x s ∧ QF x ∧ QR x
def G1 (x : DD) (s : State) : Prop := PV x s ∧ s.gpr .a6 = off x.D x.k
def HQ (x : DD) (s : State) : Prop := PV x s ∧ (s.gpr .t3 = 0 ↔ x.L = 3 * x.k)

/-- The checks of q, after their range. -/
theorem withQrest_rel :
    RelCT isa (Two W4)
      (.seq qDiv (.seq (.block gPtr) (.seq range (.seq (.block [.logic .and .s9 .s9 .s10])
        (.ite (.zero .s9) (.block [.li .a0 0]) subgroup))))) (Two CF) := by
  unfold qDiv
  have pA : Pins QA' (.s7 :: .s8 :: dbaseRegs) :=
    pins_cons (pins_one .s7 (fun x => off x.D (2 * x.k)) fun _ _ h => h.1.2.2.1)
      (pins_cons (pins_one .s8 (fun x => BitVec.ofNat 64 x.k) fun _ _ h => h.1.2.2.2)
        (pins_base id fun _ _ h => h.1.2.1))
  have pC : Pins QC' (.s9 :: .s10 :: dbaseRegs) :=
    pins_cons (pins_one .s9 (fun x => off x.D 0) fun _ _ h => h.1.2.1)
      (pins_cons (pins_one .s10 (fun x => BitVec.ofNat 64 x.k) fun _ _ h => h.1.2.2)
        (pins_base id fun _ _ h => h.1.1.2.1))
  have pD : Pins QD' (.s7 :: .s8 :: dbaseRegs) :=
    pins_cons (pins_one .s7 (fun x => off x.D 0) fun _ _ h => h.1.2.1.2.1)
      (pins_cons (pins_one .s8 (fun x => BitVec.ofNat 64 x.k) fun _ _ h => h.1.2.1.2.2)
        (pins_base id fun _ _ h => h.1.2.1.1))
  have pG : Pins GE (.a6 :: dbaseRegs) :=
    pins_cons (pins_one .a6 (fun x => off x.D x.k) fun _ _ h => h.2) (pins_base id fun _ _ h => h.1.1.1.1)
  refine RelCT.seq (RelCT.seq
    (two_post (Ψ := QA') (two_taint _ (pins_base id fun (_ : DD) _ (h : W4 _ _) => h.1.1) (by taint_decide))
      fun x s h => WP.mono (qdA_ok h.2.1 h.1.1) fun _ g => ⟨g.1, h.2.2⟩)
    (RelCT.seq (two_post (Ψ := QB') (loadN_rel pA) fun x s h => WP.mono (qdB_ok h.1) fun _ g => ⟨g.1, h.2⟩)
      (RelCT.seq (two_post (Ψ := QC') (two_taint _ (pins_base id fun (_ : DD) _ (h : QB' _ _) => h.1.2.1)
          (by taint_decide)) fun x s h => WP.mono (qdC_ok h.1) fun _ g => ⟨g.1, h.2⟩)
        (RelCT.seq (two_post (Ψ := QD') (two_taint _ pC (by taint_decide)) fun x s h =>
            WP.mono (qdD_ok h.1) fun _ g => ⟨g.1, h.2⟩)
          (two_post (Ψ := QE') (loadN_rel pD) fun x s h =>
            WP.mono (qdE_ok h.1) fun _ g => ⟨g.1, h.2, h.1.1.2.2⟩)))))
    (RelCT.seq (two_post (Ψ := GE) (two_taint _ (pins_base id fun (_ : DD) _ (h : QE' _ _) => h.1.1.1)
        (by taint_decide)) fun x s h =>
        WP.mono (gPtr_ok h.1.1.1) fun t ⟨⟨a6, m⟩, k⟩ =>
          ⟨⟨⟨h.1.1.keep k (by rw [m]; exact DArr.refl _ _) (by rw [m]), by rw [k.gpr (by decide)]; exact h.1.2⟩,
            h.2⟩, a6⟩)
      (RelCT.seq (two_post (Ψ := RGQ) (range_rel pG) fun x s h =>
          WP.mono (range_g h.1.1.1 h.2) fun t ⟨⟨r, _⟩, k⟩ =>
            ⟨r, by rw [k.gpr (by decide)]; exact h.1.1.2, h.1.2⟩)
        (RelCT.seq (two_post (Ψ := TA) (two_taint _ (pins_base id fun (_ : DD) _ (h : RGQ _ _) => h.1.1.1)
            (by taint_decide)) fun x s h => WP.mono (and9_ok h.1 h.2.1) fun _ g => ⟨g, h.2.2.2⟩)
          (two_ite (fun x : DD => !(decide (1 < x.g ∧ x.g < x.p - 1) && decide (x.p % x.q = 1)))
            (fun _ _ h => beq_mask h.1.2.2) (fail_CF fun _ _ h => h.1.1.1.1)
            (subgroup_rel (fun x => x.g) fun _ _ h => ⟨h.1.1.1, h.1.1.2.1, h.1.2⟩)))))

theorem withQ_rel : RelCT isa (Two W0) withQ (Two CF) := by
  unfold withQ
  have pQ : Pins W1 (.a6 :: dbaseRegs) :=
    pins_cons (pins_one .a6 (fun x => off x.D (2 * x.k)) fun _ _ h => h.2) (pins_base id fun _ _ h => h.1.1.1)
  refine RelCT.seq (two_post (Ψ := W1) (two_taint _ (pins_base id fun (_ : DD) _ (h : W0 _ _) => h.1.1)
      (by taint_decide)) fun x s h =>
      WP.mono (qPtrA_ok h.1.1) fun t ⟨⟨a6, m⟩, k⟩ =>
        ⟨⟨h.1.keep k (by rw [m]; exact DArr.refl _ _) (by rw [m]), h.2⟩, a6⟩)
    (RelCT.seq (two_post (Ψ := W2) (range_rel pQ) fun x s h =>
        WP.mono (range_q h.1.1 h.1.2 h.2) fun t g => ⟨g.1.1, h.1.2⟩)
      (RelCT.seq (two_post (Ψ := W3) (two_taint _ (pins_base id fun (_ : DD) _ (h : W2 _ _) => h.1.1.1)
          (by taint_decide)) fun x s h =>
          WP.mono (qOdd_ok h.1.1 h.1.2.1 h.1.2.2) fun t ⟨⟨a9, m⟩, k⟩ =>
            ⟨h.1.1.keep k (by rw [m]; exact DArr.refl _ _) (by rw [m]), h.2, a9⟩)
        (two_ite (fun x : DD => !(decide (1 < x.q ∧ x.q < x.p - 1) && decide (x.q % 2 = 1)))
          (fun _ _ h => beq_mask h.2.2) (fail_CF fun _ _ h => h.1.1.1)
          (withQrest_rel.mono (fun _ _ ⟨x, ⟨h₁, c⟩, ⟨h₂, _⟩, sp⟩ => by
            have hq1 : QR x := by unfold QR; simpa using c
            have hq0 : 0 < x.q := by unfold QR at hq1; omega
            exact ⟨x, ⟨h₁.1, ⟨h₁.1.2.2, hq0, h₁.2.1⟩, hq1⟩, ⟨h₂.1, ⟨h₁.1.2.2, hq0, h₁.2.1⟩, hq1⟩, sp⟩)
            fun _ _ h => h))))

theorem withoutQ_rel : RelCT isa (Two PV) withoutQ (Two CF) := by
  unfold withoutQ
  have pG : Pins G1 (.a6 :: dbaseRegs) :=
    pins_cons (pins_one .a6 (fun x => off x.D x.k) fun _ _ h => h.2) (pins_base id fun _ _ h => h.1.1)
  exact RelCT.seq (two_post (Ψ := G1) (two_taint _ (pins_base id fun (_ : DD) _ (h : PV _ _) => h.1)
      (by taint_decide)) fun x s h =>
      WP.mono (gPtr_ok h.1) fun t ⟨⟨a6, m⟩, k⟩ => ⟨h.keep k (by rw [m]; exact DArr.refl _ _) (by rw [m]), a6⟩)
    (RelCT.seq (two_post (Ψ := fun x => RG x x.g) (range_rel pG) fun x s h =>
        WP.mono (range_g h.1 h.2) fun t g => g.1.1)
      (two_post (two_taint _ (pins_base id fun (x : DD) _ (h : RG x x.g _) => h.1.1) (by taint_decide))
        fun x s h => WP.mono (retMask_ok h.1.1 h.2.2) fun t g => g.1.1.s6))

theorem domainBody_rel : RelCT isa (Two PV) domainBody (Two CF) := by
  unfold domainBody
  refine RelCT.seq (two_post (Ψ := HQ) (hasQ_rel (pins_base id fun (_ : DD) _ (h : PV _ _) => h.1)) fun x s h =>
      WP.mono (hasQ_ok h.1) fun t ⟨⟨a3, m⟩, k⟩ => ⟨h.keep k (by rw [m]; exact DArr.refl _ _) (by rw [m]), a3⟩)
    (two_ite (fun x : DD => decide (x.L = 3 * x.k)) (fun _ _ h => by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact h.2)
      (withQ_rel.mono (fun _ _ ⟨x, ⟨h₁, c⟩, ⟨h₂, _⟩, sp⟩ => ⟨x, ⟨h₁.1, by simpa using c⟩, ⟨h₂.1, by simpa using c⟩, sp⟩)
        fun _ _ h => h)
      (withoutQ_rel.mono (fun _ _ ⟨x, ⟨h₁, _⟩, ⟨h₂, _⟩, sp⟩ => ⟨x, h₁.1, h₂.1, sp⟩) fun _ _ h => h))

theorem cd_rel : RelCT isa (Two C0) checkDomain fun _ _ => True := by
  unfold checkDomain
  refine RelCT.seq (two_post (two_taint _ pins_C0 (by taint_decide)) fun x s h =>
      WP.mono (cdFront_ok h.1) fun _ g => h.2 ▸ g.1)
    (RelCT.seq loadP_rel (RelCT.seq (p_ite ?_ pFail_rel) (restore_rel pins_CF)))
  exact domainBody_rel.mono (fun _ _ ⟨x, ⟨h₁, c₁⟩, ⟨h₂, _⟩, sp⟩ => by
    have hv : Spec.Rsa.modulusValid x.p x.k = true := by simpa using c₁
    exact ⟨x, ⟨h₁.1, h₁.2.1, hv⟩, ⟨h₂.1, h₂.2.1, hv⟩, sp⟩) fun _ _ h => h

theorem cd_ct : ConstantTime isa cdContract.pre cdContract.pub checkDomain :=
  RelCT.constantTime (cd_rel.mono (fun s t ⟨hs, ht, hsp, h0, h1, h2, h3, h4, hb⟩ =>
    ⟨cdData s, ⟨hs, rfl⟩, ⟨ht, by
      have hb' := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp hb
      simp only [cdData]
      rw [← hb', ← h0, ← h1, ← h2, ← h3, ← h4]⟩, hsp⟩) fun _ _ h => h)

/-! ## Verified -/

/-- A state meeting `cdContract.pre`: a 512-bit p without q, the domain at
`0x1000` and the working space at `0x4000`. -/
def cdSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 128 | .a2 => 64 | .a3 => 0x4000 | .a4 => 1056 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cd_implies : cdContract.Implies (Spec.Ffdh.checkDomainContract RISCV64.abi) := by
  sig_implies [Spec.Ffdh.checkDomainContract, Spec.Ffdh.checkDomainSig, RISCV64.abi, RISCV64.argRegs, cdContract,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] [cdSatState] using cdSatState

/-- `vg_ffdh_check_domain`, without the standard domains' table. -/
theorem cd_verified :
    Verified RISCV64.target checkDomain (Spec.Ffdh.checkDomainContract RISCV64.abi) :=
  Verified.of_correct cd_correct cd_ct cd_implies

end VG.Proof.Ffdh.RISCV64.Domain
