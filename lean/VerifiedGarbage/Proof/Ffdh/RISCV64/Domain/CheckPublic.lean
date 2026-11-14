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
# `vg_ffdh_check_public` on RISC-V

`vg_ffdh_check_public(domain = a0, domain_len = a1, p_len = a2, y = a3,
y_len = a4, scratch = a5, scratch_len = a6)` (`cpContract`): `checkPublic`
saves the callee-saved registers, stores the domain, its length and y in the
header and sets up (`cpFront_ok`), loads and checks p (`loadP_P`), checks y's
range and, with q, its order (`checkY_ok`), and restores the registers
(`cp_correct`); then constant time (`cp_ct`) and the shared contract
(`cp_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Domain

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Domain
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)

/-! ## The checks of y -/

/-- What `checkY` checks. -/
def cpCond (x : DD) : Prop := (1 < x.y ∧ x.y < x.p - 1) ∧ (x.L = 3 * x.k → x.y ^ x.q % x.p = 1)

instance (x : DD) : Decidable (cpCond x) := by unfold cpCond; infer_instance

/-- `a0 := 1`, for a condition that holds. -/
theorem pass_ok {x : DD} {s : State} (h : DBase x s) {c : Prop} [Decidable c] (hc : c) :
    WP isa (.block [.li .a0 1]) s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if c then 1 else 0)) ∧ DArr x s.mem t.mem :=
  WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = 1 ∧ t.mem = s.mem) (by brun [exec_li]; rfl) (by rfl) (by rfl))
    fun t ⟨⟨t0, tm⟩, kt⟩ => ⟨⟨h.same kt tm, by rw [t0, ite_eq_left hc]; rfl⟩, by rw [tm]; exact DArr.refl _ _⟩

/-- y's address, from the header's word 2. -/
theorem ldY_ok {x : DD} {s : State} (h : PV x s) (hY : word s.mem x.S 16 = x.Y) :
    WP isa (.block [.load .d .a6 .s6 16]) s fun t => PV x t ∧ t.gpr .a6 = x.Y ∧ t.mem = s.mem :=
  WP.mono (ldw_ok h.1.ctx h.1.s6 .a6 (d := 16) (by decide) (by decide)) fun t ⟨⟨a6, m⟩, k⟩ =>
    ⟨h.keep k (by rw [m]; exact DArr.refl _ _) (by rw [m]), by rw [a6, hY], m⟩

/-- `range` on y. -/
theorem range_y {x : DD} {s : State} (h : PV x s) (h6 : s.gpr .a6 = x.Y) :
    WP isa range s fun t => (RG x x.y t ∧ DArr x s.mem t.mem) ∧ Keep rangeRegs s t :=
  range_at h h6 h.1.ctx.rdY h.1.ctx.sepY h.1.ctx.bY

/-- After y's range: whether there is q, and the subgroup. -/
theorem cpTail_ok {x : DD} {s : State} (h : RG x x.y s) (hr : 1 < x.y ∧ x.y < x.p - 1) :
    WP isa (.seq (.block hasQ) (.ite (.zero .t3) subgroup (.block [.li .a0 1]))) s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if cpCond x then 1 else 0)) ∧ DArr x s.mem t.mem := by
  refine WP.seq (WP.mono (hasQ_ok h.1.1) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_)
  have p1 : PV x s₁ := h.1.keep k1 (by rw [m1]; exact DArr.refl _ _) (by rw [m1])
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hq : x.L = 3 * x.k := a3.mp (by simpa using hb)
    refine WP.mono (subgroup_ok (v := x.y) p1 (by rw [m1]; exact h.2.1) hq) fun t ⟨⟨ht, t0⟩, ar⟩ =>
      ⟨⟨ht, ?_⟩, by rw [m1] at ar; exact ar⟩
    rw [t0]
    have e : cpCond x ↔ x.y ^ x.q % x.p = 1 := by unfold cpCond; simp only [hr, hq, true_and, forall_const]
    simp only [e]
  · have hq : x.L ≠ 3 * x.k := fun e => by simp [a3.mpr e] at hb
    refine WP.mono (pass_ok p1.1 (c := cpCond x) ⟨hr, fun e => absurd e hq⟩) fun t ⟨ht, ar⟩ =>
      ⟨ht, by rw [m1] at ar; exact ar⟩

/-- `checkY`. -/
theorem checkY_ok {x : DD} {s : State} (h : PV x s) (hY : word s.mem x.S 16 = x.Y) :
    WP isa checkY s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64 (if cpCond x then 1 else 0)) ∧ DArr x s.mem t.mem := by
  unfold checkY
  refine WP.seq (WP.mono (ldY_ok h hY) fun s₁ ⟨p1, a6, m1⟩ => ?_)
  refine WP.seq (WP.mono (range_y p1 a6) fun s₂ ⟨⟨r2, a2⟩, _⟩ => ?_)
  rw [m1] at a2
  refine WP.ite _ (Steps.eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · rw [beq_mask r2.2.2] at hb
    exact WP.mono (fail_ok r2.1.1 (c := cpCond x) fun hc => by simp [hc.1.1, hc.1.2] at hb) fun t ⟨ht, ar⟩ =>
      ⟨ht, a2.trans ar⟩
  · rw [beq_mask r2.2.2] at hb
    have hr : 1 < x.y ∧ x.y < x.p - 1 := by simpa using hb
    exact WP.mono (cpTail_ok r2 hr) fun t ⟨ht, ar⟩ => ⟨ht, a2.trans ar⟩

/-- After p's check. -/
theorem cpBranch_ok {x : DD} {s : State} (h : P4 x s) (hY : word s.mem x.S 16 = x.Y) :
    WP isa (.ite (.zero .s0) checkY (.block [.li .a0 0])) s fun t =>
      (DBase x t ∧ t.gpr .a0 = BitVec.ofNat 64
        (if Spec.Rsa.modulusValid x.p x.k = true ∧ cpCond x then 1 else 0)) ∧ DArr x s.mem t.mem := by
  obtain ⟨hb, hp, h0⟩ := h
  refine WP.ite _ (Steps.eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · have hv := h0.mp (by simpa using hz)
    refine WP.mono (checkY_ok ⟨hb, hp, hv⟩ hY) fun t ⟨⟨ht, t0⟩, ar⟩ => ⟨⟨ht, ?_⟩, ar⟩
    rw [t0]; simp only [hv, true_and]
  · exact fail_ok hb fun hc => by simp [h0.mpr hc.1] at hz

/-! ## The function -/

abbrev cpDom (s : State) : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
abbrev cpY (s : State) : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
abbrev cpScr (s : State) : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat * 8⟩

/-- `vg_ffdh_check_public`, on the registers. -/
def cpContract : Contract isa where
  pre s :=
    s.rd = [cpDom s, cpY s] ∧ s.wr = [cpScr s] ∧ (cpDom s).Disjoint (cpScr s) ∧ (cpY s).Disjoint (cpScr s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a3).toNat + (s.gpr .a4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat * 8 ≤ 2 ^ 64 ∧ Spec.Ffdh.pLenValid (s.gpr .a2).toNat ∧
      Spec.Ffdh.domainLenValid (s.gpr .a2).toNat (s.gpr .a1).toNat ∧ (s.gpr .a4).toNat = (s.gpr .a2).toNat ∧
      Spec.Rsa.scratchWords (s.gpr .a2).toNat ≤ (s.gpr .a6).toNat ∧ (s.gpr .a5).toNat % 8 = 0
  post s t :=
    Spec.Ffdh.domainValid (s.gpr .a2).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) = true →
      ((t.gpr .a0).setWidth 32).toNat =
        if Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf (s.gpr .a2).toNat
          (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat),
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)⟩ then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧ s₁.gpr .a6 = s₂.gpr .a6 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a3) (s₁.gpr .a4).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat).map (·.toNat) ++
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a3) (s₂.gpr .a4).toNat).map (·.toNat)

/-- The public data of a run. -/
def cpData (s : State) : DD :=
  ⟨s.gpr .a0, (s.gpr .a1).toNat, (s.gpr .a2).toNat, s.gpr .a5, (s.gpr .a6).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat, s.gpr .a3,
    Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a2).toNat⟩

/-- The registers the front writes. -/
def cpFrontRegs : List Reg := [.t0, .s6, .s7, .s8, .a1, .a7, .s5, .s10, .s11]

/-- The front: the registers saved, the domain, its length and y in the
header, `setup`. -/
theorem cpFront_ok {s : State} (h : cpContract.pre s) :
    WP isa (.block cpFront) s fun t => (P1 (cpData s) t ∧ word t.mem (s.gpr .a5) 16 = s.gpr .a3) ∧
      (∀ i < 12, t.mem.readW (off (Pub.savW (s.gpr .a5)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
      Keep cpFrontRegs s t ∧ Outside (s.gpr .a5) 0 256 s.mem t.mem := by
  obtain ⟨hrd, hwr, dDS, dYS, nwD, nwY, nwS, ⟨hk, hk'⟩, hL, hyl, hsl, alS⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  have hLk : (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat ∨ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hL
  have hs : Scr s (s.gpr .a5) ((s.gpr .a6).toNat * 8) := Scr.of_mem (by rw [hwr]; simp) nwS alS
  rw [show cpFront = ([.addi .t0 .a5 0] ++ PublicChecked.saveRegs) ++ ([.store .d .a0 .s6 0] ++
      ([.store .d .a1 .s6 8] ++ ([.store .d .a3 .s6 16] ++ (args ++ PublicChecked.setup)))) by
    simp only [cpFront, List.append_assoc, List.cons_append, List.nil_append]]
  refine WP.block_append (WP.mono (pre_ok .a5 rfl hs (by omega_arith)) fun s₁ ⟨h61, sv1, k1, o1⟩ => ?_)
  refine WP.block_append (WP.mono (sth_ok (hs.congr k1.2.2) (by omega_arith) h61 .a0 (d := 0) (by decide)
    (by decide)) fun s₂ ⟨⟨w0, o2⟩, k2⟩ => ?_)
  refine WP.block_append (WP.mono (sth_ok (hs.congr (k1.trans k2).2.2) (by omega_arith)
    ((k2.gpr (by decide)).trans h61) .a1 (d := 8) (by decide) (by decide)) fun s₃ ⟨⟨w8, o3⟩, k3⟩ => ?_)
  refine WP.block_append (WP.mono (sth_ok (hs.congr ((k1.trans k2).trans k3).2.2) (by omega_arith)
    ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans h61)) .a3 (d := 16) (by decide) (by decide))
    fun s₄ ⟨⟨w16, o4⟩, k4⟩ => ?_)
  have k14 := ((k1.trans k2).trans k3).trans k4
  refine WP.mono (tail_ok (k := (s.gpr .a2).toNat)
    ((k4.gpr (by decide)).trans ((k3.gpr (by decide)).trans ((k2.gpr (by decide)).trans h61)))
    (by rw [k14.gpr (by decide), ofNat_toNat']) hk') fun t ⟨⟨t7, t8, t11, t0, t5, ta7, t6, tm⟩, kt⟩ => ?_
  have hn := hs.nowrap
  have hZ : 256 + 128 * (s.gpr .a2).toNat ≤ (s.gpr .a6).toNat * 8 := by omega_arith
  have hO : Outside (s.gpr .a5) 0 256 s.mem t.mem := by
    rw [tm]
    exact ((o1.trans (o2.mono (Nat.le_refl _) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))).trans
      (o4.mono (by omega_arith) (by omega_arith))
  have sepD := Pub.ne_of_disjoint dDS (Nat.le_of_lt (s.gpr .a1).isLt)
  have sepY := Pub.ne_of_disjoint dYS (Nat.le_of_lt (s.gpr .a4).isLt)
  have rdD : ∀ i < (s.gpr .a1).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a0) i) 1 := by
    rw [(k14.trans kt).2.1, (k14.trans kt).2.2]
    exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have rdY : ∀ i < (s.gpr .a4).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a3) i) 1 := by
    rw [(k14.trans kt).2.1, (k14.trans kt).2.2]
    exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have bD : Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat :=
    Pub.bytes_apart (o := 0) (n := 256) hO (by omega_arith) sepD
  have bY : Spec.Rsa.bytesAt t.mem (s.gpr .a3) (s.gpr .a4).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat :=
    Pub.bytes_apart (o := 0) (n := 256) hO (by omega_arith) sepY
  rw [hyl] at rdY sepY bY
  have hw0 : word t.mem (s.gpr .a5) 0 = s.gpr .a0 := by
    rw [tm, Outside.word o4 (by omega_arith) (by omega_arith), Outside.word o3 (by omega_arith) (by omega_arith), w0,
      k1.gpr (by decide)]
  have hw8 : word t.mem (s.gpr .a5) 8 = BitVec.ofNat 64 (s.gpr .a1).toNat := by
    rw [tm, Outside.word o4 (by omega_arith) (by omega_arith), w8, k2.gpr (by decide), k1.gpr (by decide),
      ofNat_toNat']
  have hw16 : word t.mem (s.gpr .a5) 16 = s.gpr .a3 := by
    rw [tm, w16, k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide)]
  refine ⟨⟨⟨⟨⟨hs.congr (k14.trans kt).2.2, hk, hk', hLk, ?_, rdD, sepD, bD, rdY, sepY, bY, hw0, hw8⟩,
      t6, ta7, by rw [t5, Nat.mul_add]; rfl, t0, t11⟩,
    by rw [t7, k14.gpr (by decide)]; exact (BitVec.add_zero _).symm, t8⟩, hw16⟩, fun i hi => ?_,
    (k14.trans kt).mono (by decide), hO⟩
  · show slot (((s.gpr .a2).toNat + 7) / 8) 24 ≤ (s.gpr .a6).toNat * 8
    unfold slot hdrBytes; omega_arith
  · have e : off (Pub.savW (s.gpr .a5)) (8 * i) = off (s.gpr .a5) (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← sv1 i hi, tm, e]
    show word s₄.mem (s.gpr .a5) (128 + 8 * i) = word s₁.mem (s.gpr .a5) (128 + 8 * i)
    rw [Outside.word o4 (by omega_arith) (by omega_arith), Outside.word o3 (by omega_arith) (by omega_arith),
      Outside.word o2 (by omega_arith) (by omega_arith)]

/-- A word of the header is kept by changes to the arrays. -/
theorem DArr.hdr {x : DD} {s : State} (hc : DCtx x s) {m : Mem} (h : DArr x s.mem m) {d : Nat} (hd : d + 8 ≤ 256) :
    word m x.S d = word s.mem x.S d := by
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have h24 : 256 ≤ slot x.w 24 := by unfold slot hdrBytes; omega_arith
  exact Outside.word h (Or.inl hd) (by omega_arith)

/-- `publicValid`, as `checkPublic` computes it, for a valid domain. -/
theorem pv_iff (x : DD) (hlen : x.db.length = x.L) (hL : x.L = 2 * x.k ∨ x.L = 3 * x.k) (hk : 64 ≤ x.k) :
    Spec.Ffdh.publicValid ⟨Spec.Ffdh.domainOf x.k x.db, x.y⟩ = true ↔ cpCond x := by
  rw [Proof.Ffdh.publicValid_eq]
  unfold cpCond
  simp only [Spec.Ffdh.domainOf, hlen]
  rcases hL with e | e
  · rw [ite_eq_right (show ¬x.L = 3 * x.k by omega)]
    simp only [reduceCtorEq, false_imp_iff, imp_true_iff, and_true, show ¬x.L = 3 * x.k by omega]
  · rw [ite_eq_left e]
    simp only [Option.some.injEq, forall_eq', e, true_imp_iff]

theorem cp_correct (s : State) (h : cpContract.pre s) :
    ∃ tr t, Exec isa checkPublic s tr t ∧ abiPreserved s t ∧ cpContract.post s t := by
  show WP isa checkPublic s fun t => abiPreserved s t ∧ cpContract.post s t
  suffices main : WP isa checkPublic s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ cpContract.post s t from
    WP.mono (WP.rdwr (WP.keep dNotRa main (by rfl))) fun t ⟨⟨⟨hp, hpost⟩, kra⟩, _, _, hsp⟩ =>
      ⟨⟨hp, hsp, kra.gpr (by decide)⟩, hpost⟩
  have hpre := h
  obtain ⟨hrd, hwr, dDS, dYS, nwD, nwY, nwS, ⟨hk, hk'⟩, hL, hyl, hsl, alS⟩ := h
  unfold checkPublic
  refine WP.seq (WP.mono (cpFront_ok hpre) fun s₃ ⟨⟨h1, hY⟩, hsv, _, _⟩ => ?_)
  refine WP.seq (WP.mono (loadP_P h1) fun s₄ ⟨h4, a4⟩ => ?_)
  have hY4 : word s₄.mem (cpData s).S 16 = (cpData s).Y := by rw [a4.hdr h1.1.ctx (by decide)]; exact hY
  refine WP.seq (WP.mono (cpBranch_ok h4 hY4) fun t₅ ⟨⟨b5, t0⟩, a5⟩ => ?_)
  have hc := b5.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  have h24 : 256 ≤ slot (cpData s).w 24 := by unfold slot hdrBytes; omega_arith
  refine WP.mono (dRestore_ok b5 fun i hi => ?_) fun u ⟨urs, u0⟩ => ⟨urs, fun hdv => ?_⟩
  · have e : off (Pub.savW (s.gpr .a5)) (8 * i) = off (s.gpr .a5) (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hsv i hi, e]
    show word t₅.mem (cpData s).S (128 + 8 * i) = word s₃.mem (cpData s).S (128 + 8 * i)
    rw [Outside.word a5 (Or.inl (by omega_arith)) (by omega_arith),
      Outside.word a4 (Or.inl (by omega_arith)) (by omega_arith)]
  · show ((u.gpr .a0).setWidth 32).toNat = _
    have hmod := Proof.Ffdh.domainValid_mod hdv
    have hv : Spec.Rsa.modulusValid (cpData s).p (cpData s).k = true := hmod
    rw [u0, t0, ret_bv32, hyl]
    refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
    have e := pv_iff (cpData s) (VG.Proof.Bignum.bytesAt_length _ _ _) hL hk
    simp only [hv, true_and]
    exact e.symm

/-! ## Constant time -/

open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- On entry. -/
def CP0 (x : DD) (s : State) : Prop := cpContract.pre s ∧ cpData s = x

theorem pins_CP0 : Pins CP0 [.a0, .a1, .a2, .a3, .a4, .a5, .a6] := by
  rintro x s₁ s₂ ⟨p₁, h₁⟩ ⟨p₂, h₂⟩ r hr
  subst h₁
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have e := congrArg DD.D h₂; have e1 := congrArg DD.L h₂; have e2 := congrArg DD.k h₂
  have e3 := congrArg DD.S h₂; have e4 := congrArg DD.Z h₂; have e5 := congrArg DD.Y h₂
  simp only [cpData] at e e1 e2 e3 e4 e5
  have y₁ := p₁.2.2.2.2.2.2.2.2.2.1
  have y₂ := p₂.2.2.2.2.2.2.2.2.2.1
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact e.symm
  · exact BitVec.eq_of_toNat_eq e1.symm
  · exact BitVec.eq_of_toNat_eq e2.symm
  · exact e5.symm
  · exact BitVec.eq_of_toNat_eq (by omega)
  · exact e3.symm
  · exact BitVec.eq_of_toNat_eq (by omega)

/-- The predicates at the cuts, with y's address in the header. -/
def Y1 (x : DD) (s : State) : Prop := P1 x s ∧ word s.mem x.S 16 = x.Y
def Y2 (x : DD) (s : State) : Prop := P2 x s ∧ word s.mem x.S 16 = x.Y
def Y3 (x : DD) (s : State) : Prop := P3 x s ∧ word s.mem x.S 16 = x.Y
def Y4 (x : DD) (s : State) : Prop := P4 x s ∧ word s.mem x.S 16 = x.Y
def YA (x : DD) (s : State) : Prop := PV x s ∧ s.gpr .a6 = x.Y
def YH (x : DD) (s : State) : Prop :=
  PV x s ∧ wordsVal s.mem x.S (slot x.w 4) x.w = x.y ∧ (s.gpr .t3 = 0 ↔ x.L = 3 * x.k)

theorem cpLoadP_rel : RelCT isa (Two Y1) loadP (Two Y4) := by
  unfold loadP Precompute.check
  exact RelCT.seq (two_post (Ψ := Y2) (loadN_rel (pins_and pins_P1)) fun x s h =>
      WP.mono (loadN_P h.1) fun _ g => ⟨g.1, by rw [g.2.1.hdr h.1.1.ctx (by decide)]; exact h.2⟩)
    (RelCT.seq (two_post (Ψ := Y3) (check1_rel (pins_and pins_P2)) fun x s h =>
        WP.mono (check1_P h.1) fun _ g => ⟨g.1, by rw [g.2]; exact h.2⟩)
      (two_post (Ψ := Y4) (check2_rel (pins_and pins_P3)) fun x s h =>
        WP.mono (check2_P h.1) fun _ g => ⟨g.1, by rw [g.2]; exact h.2⟩))

/-- After y's range. -/
theorem cpTail_rel :
    RelCT isa (Two fun x s => RG x x.y s ∧ (1 < x.y ∧ x.y < x.p - 1))
      (.seq (.block hasQ) (.ite (.zero .t3) subgroup (.block [.li .a0 1]))) (Two CF) := by
  refine RelCT.seq (two_post (Ψ := YH) (hasQ_rel (pins_base id fun (_ : DD) _ (h : RG _ _ _ ∧ _) => h.1.1.1))
      fun x s h => WP.mono (hasQ_ok h.1.1.1) fun t ⟨⟨a3, m⟩, k⟩ =>
        ⟨h.1.1.keep k (by rw [m]; exact DArr.refl _ _) (by rw [m]), by rw [m]; exact h.1.2.1, a3⟩)
    (two_ite (fun x : DD => decide (x.L = 3 * x.k)) (fun _ _ h => by
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]; exact h.2.2)
      (subgroup_rel (fun x => x.y) fun _ _ h => ⟨h.1.1, h.1.2.1, by simpa using h.2⟩)
      (two_post (two_taint _ pins_nil (by taint_decide)) fun x s h =>
        WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [exec_li]; exact ⟨_, rfl⟩) (by rfl) (by rfl))
          fun _ ⟨_, k⟩ => (k.gpr (by decide)).trans h.1.1.1.s6))

theorem checkY_rel : RelCT isa (Two fun x s => PV x s ∧ word s.mem x.S 16 = x.Y) checkY (Two CF) := by
  unfold checkY
  have pA : Pins YA (.a6 :: dbaseRegs) :=
    pins_cons (pins_one .a6 (fun x => x.Y) fun _ _ h => h.2) (pins_base id fun _ _ h => h.1.1)
  refine RelCT.seq (two_post (Ψ := YA) (two_taint _ (pins_base id fun (_ : DD) _ (h : PV _ _ ∧ _) => h.1.1)
      (by taint_decide)) fun x s h => WP.mono (ldY_ok h.1 h.2) fun _ g => ⟨g.1, g.2.1⟩)
    (RelCT.seq (two_post (Ψ := fun x => RG x x.y) (range_rel pA) fun x s h =>
        WP.mono (range_y h.1 h.2) fun _ g => g.1.1)
      (two_ite (fun x : DD => !decide (1 < x.y ∧ x.y < x.p - 1)) (fun _ _ h => beq_mask h.2.2)
        (fail_CF fun _ _ h => h.1.1.1)
        (cpTail_rel.mono (fun _ _ ⟨x, ⟨h₁, c⟩, ⟨h₂, _⟩, sp⟩ => by
          have hr : 1 < x.y ∧ x.y < x.p - 1 := by simpa using c
          exact ⟨x, ⟨h₁, hr⟩, ⟨h₂, hr⟩, sp⟩) fun _ _ h => h)))

theorem cp_rel : RelCT isa (Two CP0) checkPublic fun _ _ => True := by
  unfold checkPublic
  refine RelCT.seq (two_post (Ψ := Y1) (two_taint _ pins_CP0 (by taint_decide)) fun x s h =>
      WP.mono (cpFront_ok h.1) fun _ g => h.2 ▸ g.1)
    (RelCT.seq cpLoadP_rel (RelCT.seq ?_ (restore_rel pins_CF)))
  refine two_ite (fun x : DD => Spec.Rsa.modulusValid x.p x.k) (fun _ _ h => ?_)
    (checkY_rel.mono (fun _ _ ⟨x, ⟨h₁, c⟩, ⟨h₂, _⟩, sp⟩ =>
      ⟨x, ⟨⟨h₁.1.1, h₁.1.2.1, c⟩, h₁.2⟩, ⟨⟨h₂.1.1, h₂.1.2.1, c⟩, h₂.2⟩, sp⟩) fun _ _ h => h)
    (fail_CF fun _ _ h => h.1.1.1)
  exact Bool.eq_iff_iff.mpr (by rw [beq_iff_eq]; exact h.1.2.2)

theorem cp_ct : ConstantTime isa cpContract.pre cpContract.pub checkPublic :=
  RelCT.constantTime (cp_rel.mono (fun s t ⟨hs, ht, hsp, h0, h1, h2, h3, h4, h5, h6, hb⟩ =>
    ⟨cpData s, ⟨hs, rfl⟩, ⟨ht, by
      obtain ⟨e1, e2⟩ := List.append_inj hb (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h1])
      have hb1 := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
      have hb2 := (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e2
      rw [hs.2.2.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.2.1] at hb2
      simp only [cpData]
      rw [← hb1, ← hb2, ← h0, ← h1, ← h2, ← h3, ← h5, ← h6]⟩, hsp⟩) fun _ _ h => h)

/-! ## Verified -/

/-- A state meeting `cpContract.pre`: a 512-bit p without q, the domain at
`0x1000`, y at `0x2000` and the working space at `0x4000`. -/
def cpSatState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 128 | .a2 => 64 | .a3 => 0x2000 | .a4 => 64 | .a5 => 0x4000 | .a6 => 1056 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 128⟩, ⟨0x2000, 64⟩]
  wr := [⟨0x4000, 8448⟩]

theorem cp_implies : cpContract.Implies (Spec.Ffdh.checkPublicContract RISCV64.abi) := by
  sig_implies [Spec.Ffdh.checkPublicContract, Spec.Ffdh.checkPublicSig, RISCV64.abi, RISCV64.argRegs, cpContract,
    Spec.Ffdh.pLenValid, Spec.Ffdh.domainLenValid] [cpSatState] using cpSatState

/-- `vg_ffdh_check_public`. -/
theorem checkPublic_verified :
    Verified RISCV64.target checkPublic (Spec.Ffdh.checkPublicContract RISCV64.abi 0) :=
  Verified.of_correct cp_correct cp_ct cp_implies

end VG.Proof.Ffdh.RISCV64.Domain
