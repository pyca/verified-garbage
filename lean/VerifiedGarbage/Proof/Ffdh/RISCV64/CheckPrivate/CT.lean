module

-- separate module: built alongside Correct

public import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Body
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.CheckPrivate.Body
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.Li

/-!
# `vg_ffdh_check_private` on RISC-V: constant time

As `vg_ffdh_derive_public`'s (`Derive/CT.lean`), whose predicates on its data
`DD` (the exchange's public data and x's range, which the status reveals)
this carries with y's address `Yc` and the facts on it (`YE`, the data
`CD`); after the power, the comparison's own predicates (`K6`–`K8`) fix the
registers it uses as addresses and counts, y's address among them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.CheckPrivate

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive VG.Impl.Ffdh.RISCV64.CheckPrivate
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd xRange_ok off_off DD inRange Inv W Z4 RB pins_W pins_Z4 lp_W pins_RB
  pins_TI two_x)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- The public data of a run: `vg_ffdh_derive_public`'s, and y's address. -/
structure CD where
  d : DD
  Yc : Addr

def kdOf (s : State) : CD := ⟨⟨cxOf s, inRange (cxOf s) s.mem⟩, s.gpr .a3⟩

/-- `Φ` of `vg_ffdh_derive_public`'s data, with y's facts. -/
def V (Φ : DD → State → Prop) (c : CD) (s : State) : Prop := Φ c.d s ∧ YE c.d.x c.Yc s

theorem pins_V {Φ : DD → State → Prop} {rs : List Reg} (h : Pins Φ rs) : Pins (V Φ) rs :=
  fun c _ _ h₁ h₂ => h c.d _ _ h₁.1 h₂.1

/-! ## The predicates -/

def Q0 (c : CD) (s : State) : Prop := kpContract.pre s ∧ kdOf s = c

/-- Before the comparison's load of y's address. -/
def K8 (a : XD × Addr) (s : State) : Prop :=
  (RW a.1 s ∧ s.gpr .s7 = a.2) ∧ WP isa (.seq loadY (.seq (eqMask 4 8) (.block both))) s (CF a.1)

/-- After `zMask`. -/
def K7 (a : XD × Addr) (s : State) : Prop := RW a.1 s ∧ WP isa (.block ldY) s (K8 a)

/-- After the power. -/
def K6 (a : XD × Addr) (s : State) : Prop := RW a.1 s ∧ WP isa zMask s (K7 a)

/-- Before the power. -/
def K5 (a : XD × Addr) (s : State) : Prop := R5 a.1 s ∧ WP isa ModExp.powWin s (K6 a)

/-- After the peer's address. -/
def K1 (a : XD × Addr) (s : State) : Prop :=
  R1 a.1 s ∧ WP isa (.seq PublicChecked.loadX (.seq r2 (.block [.load .d .s9 .s6 8, .load .d .s10 .s6 16]))) s
    (K5 a)

/-! ## Pins -/

theorem pins_Q0 : Pins Q0 [.a7] := by
  rintro c s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact (congrArg (fun c => c.d.x.S) h₁).trans (congrArg (fun c => c.d.x.S) h₂).symm

theorem pins_K1 : Pins K1 [.a6, .s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun a s h r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr
  · exact h.1.1
  · exact rw_vals h.1.2 r (by simpa using hr)

theorem pins_K5 : Pins K5 [.s9, .s10, .s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun a s h r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · exact h.1.1
  · exact h.1.2.1
  · exact rw_vals h.1.2.2 r (by simpa using hr)

theorem pins_K6 : Pins K6 [.s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun _ _ h => rw_vals h.1

theorem pins_K7 : Pins K7 [.s6, .a7, .s5, .t0, .s11] := pins_of (fun a => rwVal a.1) fun _ _ h => rw_vals h.1

theorem pins_K8 : Pins K8 [.s7, .s6, .a7, .s5, .t0, .s11] :=
  pins_of (fun a r => if r = .s7 then a.2 else rwVal a.1 r) fun a s h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · exact h.1.2
    · have hne : r ≠ .s7 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
      exact rw_vals h.1.1 r (by simpa using hr)

theorem pins_CF2 : Pins (fun (a : XD × Addr) s => CF a.1 s) [.s6] := fun a s₁ s₂ h₁ h₂ => pins_CF a.1 s₁ s₂ h₁ h₂

/-! ## The steps, by correctness -/

theorem front_V {c : CD} {s : State} (h : Q0 c s) : WP isa (.block cpFront) s (V (W Base) c) := by
  obtain ⟨hpre, rfl⟩ := h
  have hpre' := hpre
  obtain ⟨hrd, -, -, dYS, -, -, -, -, -, -, ⟨hk, -⟩, -, hyl, -, -, hsl, -, -⟩ := hpre'
  simp only [Spec.Rsa.scratchWords] at hsl
  have hwd : ((s.gpr .a2).toNat + 7) / 8 * 8 ≤ (s.gpr .a2).toNat + 7 := Nat.div_mul_le_self _ _
  have hcz : cpZ (s.gpr .a2).toNat ≤ (stackArg s 0).toNat * 8 := by unfold cpZ slot hdrBytes; omega_arith
  refine WP.mono (WP.rdwr (cpFront_ok hpre)) fun t ⟨⟨hb, ha, hw32, _, _, o⟩, r, w, _⟩ =>
    ⟨⟨hb, ha, ?_⟩, hw32, fun i hi => ?_, fun i hi y hy => Pub.ne_of_disjoint dYS (Nat.le_of_lt (s.gpr .a4).isLt) i
      (by change i < (s.gpr .a2).toNat at hi; omega_arith) y (Nat.lt_of_lt_of_le hy hcz)⟩
  · have hZ := hb.ctx.hZ
    unfold slot hdrBytes at hZ
    have hn : 0 + 256 ≤ (cxOf s).Z := by omega_arith
    have hi : Derive.Inv (kdOf s).d s := by unfold Derive.Inv kdOf; dsimp only
    exact Derive.Inv.keep (s := s) (t := t) hi hb.ctx o hn
  · change i < (s.gpr .a2).toNat at hi
    change InRegions _ (off (s.gpr .a3) i) 1
    rw [r, w]
    exact rd_of_mem (L := (s.gpr .a4).toNat) (by rw [hrd]; simp) (by omega_arith) (BitVec.isLt _) i hi

/-- A piece of `loadP`, which writes only `a0`, `s0`, `t3`–`t5` and arrays. -/
theorem lp_V {Φ Ψ : XD → State → Prop} {c : Prog isa} {cd : CD} {s : State}
    (hc : ∀ x s, Φ x s → Ctx x s) (h : V (W Φ) cd s)
    (hw : WP isa c s fun t => (Ψ cd.d.x t ∧ Arr cd.d.x s.mem t.mem) ∧ Keep [.a0, .s0, .t3, .t4, .t5] s t) :
    WP isa c s (V (W Ψ) cd) :=
  WP.mono (WP.and (lp_W hc h.1 hw) (WP.rdwr hw)) fun _ ⟨h', ⟨⟨_, a⟩, _⟩, r, w, _⟩ =>
    ⟨h', h.2.keep (hc _ _ h.1.1) r w a⟩

theorem TVc {a : XD × Addr} {s : State} (h : (X4 a.1 s ∧ s.gpr .s0 = 0) ∧ YE a.1 a.2 s) :
    WP isa (.block [.load .d .a6 .s6 24]) s (K1 a) := by
  obtain ⟨⟨h4, hz⟩, hy⟩ := h
  have hv := h4.2.2.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv h4.1.ctx.k64
  refine WP.mono (WP.rdwr (exPre_split h4 hz)) fun s₁ ⟨⟨r1, w1⟩, rd1, wr1, _⟩ => ⟨r1,
    WP.mono (WP.rdwr w1) fun s₅ ⟨⟨r5, w5⟩, rd5, wr5, _⟩ => ⟨r5,
      WP.mono (WP.rdwr w5) fun s₆ ⟨pp, rd6, wr6, _⟩ => ⟨pp.regs, ?_⟩⟩⟩
  have hy6 : YE a.1 a.2 s₆ := hy.keep h4.1.ctx (by rw [rd6, rd5, rd1]) (by rw [wr6, wr5, wr1]) pp.arr
  exact WP.mono (cmp_split pp.ctx pp.regs hy6 pp.p hf.1 (by rw [pp.z]; exact Nat.mod_lt _ (by omega_arith)))
    fun s₇ ⟨r7, w7⟩ => ⟨r7, WP.mono w7 fun s₈ ⟨r8, w8⟩ => ⟨r8, WP.mono w8 fun t op => op.2.1⟩⟩

/-! ## Constant time -/

/-- x in range: the exchange's power, then the comparison. -/
theorem good_rel : RelCT isa (Two fun (a : XD × Addr) s => (X4 a.1 s ∧ s.gpr .s0 = 0) ∧ YE a.1 a.2 s) cpGood
    (Two fun (a : XD × Addr) s => CF a.1 s) := by
  unfold cpGood exPre cpCmp
  exact RelCT.seq (RelCT.seq (two_post (two_taint _ (fun a s₁ s₂ h₁ h₂ =>
        pins_base (Φ := X4) (fun _ _ h => h.1) a.1 s₁ s₂ h₁.1.1 h₂.1.1) (by taint_decide)) fun _ _ h => TVc h)
    (two_post (two_taint _ pins_K1 (by taint_decide)) fun _ _ h => h.2))
    (RelCT.seq (two_post (two_taint _ pins_K5 (by taint_decide)) fun _ _ h => h.2)
      (RelCT.seq (two_post (two_taint _ pins_K6 (by taint_decide)) fun _ _ h => h.2)
        (RelCT.seq (two_post (two_taint _ pins_K7 (by taint_decide)) fun _ _ h => h.2)
          (two_post (two_taint _ pins_K8 (by taint_decide)) fun _ _ h => h.2))))

theorem two_a {Φ : XD → State → Prop} {s₁ s₂ : State} (h : Two (fun (a : XD × Addr) s => Φ a.1 s) s₁ s₂) :
    Two Φ s₁ s₂ :=
  let ⟨a, h₁, h₂, hsp⟩ := h
  ⟨a.1, h₁, h₂, hsp⟩

theorem two_c {Φ : XD → State → Prop} {s₁ s₂ : State} (h : Two (fun (c : CD) s => Φ c.d.x s) s₁ s₂) :
    Two Φ s₁ s₂ :=
  let ⟨c, h₁, h₂, hsp⟩ := h
  ⟨c.d.x, h₁, h₂, hsp⟩

theorem pins_TB : Pins (fun c s => V RB c s ∧ s.gpr .s9 = 0) baseRegs :=
  fun c s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) c.d.x s₁ s₂ h₁.1.1.1 h₂.1.1.1

theorem TB {c : CD} {s : State} (h : V RB c s ∧ s.gpr .s9 = 0) : WP isa (.block [.li .a0 2]) s (CF c.d.x) :=
  WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [fin64_exec_li_lit (show 2 < 2048 by decide)]; exact ⟨_, rfl⟩)
    (by rfl) (by rfl)) fun _ ⟨_, kt⟩ => (kt.gpr (by decide)).trans h.1.1.1.1.s6

/-- After p's check, for a valid p. -/
theorem body_rel : RelCT isa (Two (V Z4)) cpBody (Two CF) := by
  unfold cpBody
  refine RelCT.seq (R := Two (V RB)) (two_post (two_taint _ (pins_V pins_Z4) (by taint_decide)) fun c s h => ?_) ?_
  rotate_left
  · refine RelCT.ite (fun s₁ s₂ ⟨c, h₁, h₂, _⟩ => ?_)
      (RelCT.mono (two_post (Φ := fun c s => V RB c s ∧ s.gpr .s9 = 0)
        (two_taint _ pins_TB (by taint_decide))
        (Ψ := fun c s => CF c.d.x s) fun _ _ h => TB h)
        (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_c h)
      (RelCT.mono good_rel (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, _⟩ =>
        ⟨(c.d.x, c.Yc), ⟨⟨h₁.1.1, h₁.1.2.1⟩, h₁.2⟩, ⟨⟨h₂.1.1, h₂.1.2.1⟩, h₂.2⟩, hsp⟩) fun _ _ h => two_a h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.2.2, h₂.1.2.2]
    · rw [Steps.eval_zero] at hc
      have h9 : s₁.gpr .s9 = 0 := by simpa using hc
      exact ⟨c, ⟨h₁, h9⟩, ⟨h₂, h₂.1.2.2.mpr (h₁.1.2.2.mp h9)⟩, hsp⟩
  · obtain ⟨⟨⟨h4, ha, hi⟩, hz⟩, hy⟩ := h
    have hv := h4.2.2.mp hz
    refine WP.mono (WP.rdwr (xRange_ok h4 hv ha)) fun t ⟨⟨t4, t0, t9, at'⟩, r, w, _⟩ =>
      ⟨⟨t4, t0, ?_⟩, hy.keep h4.1.ctx r w at'⟩
    rw [t9]
    have hi' : inRange c.d.x s.mem = c.d.v := hi
    unfold inRange at hi'
    rw [hi']
    cases c.d.v <;> decide

theorem pins_TIc : Pins (fun c s => V (W X4) c s ∧ s.gpr .s0 ≠ 0) baseRegs :=
  fun c s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) c.d.x s₁ s₂ h₁.1.1.1 h₂.1.1.1

theorem kp_rel : RelCT isa (Two Q0) checkPrivate fun _ _ => True := by
  unfold checkPrivate
  refine RelCT.seq (R := Two (V (W Base))) (two_post (two_taint _ pins_Q0 (by taint_decide)) fun _ _ h => front_V h)
    (RelCT.seq (R := Two (V (W X4))) ?_ (RelCT.seq (R := Two CF) ?_ (two_taint _ pins_CF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_V (pins_W (pins_base fun _ _ h => h))) (by taint_decide))
        fun _ _ h => lp_V (fun _ _ h => h.ctx) h (WP.keep _ (loadN_X h.1.1) (by rfl)))
      (RelCT.seq (two_post (two_taint _ (pins_V (pins_W (pins_base (Φ := X2) fun _ _ h => h.1))) (by taint_decide))
          fun _ _ h => lp_V (fun _ _ h => h.1.ctx) h (WP.keep _ (WP.mono (check1_X h.1.1) fun t ⟨h3, m⟩ =>
            ⟨h3, by rw [m]; exact Outside.refl _ _ _ _⟩) (by rfl)))
        (two_post (two_taint _ (pins_V (pins_W pins_X3)) (by taint_decide)) fun _ _ h =>
          lp_V (fun _ _ h => h.1.ctx) h
            (WP.keep _ (WP.mono (check2_X h.1.1) fun t ⟨h4, m⟩ => ⟨h4, by rw [m]; exact Outside.refl _ _ _ _⟩) (by rfl))))
  · refine RelCT.ite (fun s₁ s₂ ⟨c, h₁, h₂, _⟩ => ?_)
      (RelCT.mono body_rel (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
      (RelCT.mono (two_post (Φ := fun c s => V (W X4) c s ∧ s.gpr .s0 ≠ 0)
        (two_taint _ pins_TIc (by taint_decide)) (Ψ := fun c s => CF c.d.x s) fun _ _ h => TI ⟨h.1.1.1, h.2⟩)
        (fun s₁ s₂ ⟨⟨c, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_c h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.1.2.2, h₂.1.1.2.2]
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 = 0 := by simpa using hc
      exact ⟨c, ⟨⟨h₁.1, h0⟩, h₁.2⟩, ⟨⟨h₂.1, h₂.1.1.2.2.mpr (h₁.1.1.2.2.mp h0)⟩, h₂.2⟩, hsp⟩
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 ≠ 0 := by simpa using hc
      exact ⟨c, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.1.1.2.2.mpr (h₂.1.1.2.2.mp e))⟩, hsp⟩

/-- `inRange` as `privateValid` of the domain. -/
theorem inRange_eq {s : State} (h : kpContract.pre s) :
    inRange (cxOf s) s.mem = Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s.gpr .a2).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := h
  have hL' : (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat ∨ (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat := hL
  rw [Derive.privateValid_dom (by omega_arith) hL']
  have hp : (cxOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a2).toNat) := by
    show Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat).take (s.gpr .a2).toNat) = _
    rw [Proof.Ffdh.take_bytesAt _ _ (by rcases hL' with h | h <;> omega_arith)]
  unfold inRange
  rw [hp]
  rfl

theorem kdOf_eq {s t : State} (hs : kpContract.pre s) (ht : kpContract.pre t) (hp : kpContract.pub s t) :
    kdOf s = kdOf t := by
  obtain ⟨_, h0, h1, h2, h3, h4, h5, h6, h7, a0, hb⟩ := hp
  simp only [kpLeak] at hb
  obtain ⟨e12, e3⟩ := List.append_inj hb (by
    simp only [List.length_append, List.length_map, VG.Proof.Bignum.bytesAt_length, h1, h4])
  obtain ⟨e1, -⟩ := List.append_inj e12 (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h1])
  have eb : Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a0) (t.gpr .a1).toNat :=
    (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
  have ex : cxOf s = cxOf t := by
    simp only [cxOf]
    rw [eb]
    simp only [h0, h1, h2, h5, h6, h7]
  have ev : inRange (cxOf s) s.mem = inRange (cxOf t) t.mem := by
    rw [inRange_eq hs, inRange_eq ht]
    have ek := List.cons.inj e3 |>.1
    simp only [kpStatus] at ek
    rw [eb, h2] at ek
    rw [eb, h2]
    generalize Spec.Ffdh.domainOf (t.gpr .a2).toNat (Spec.Rsa.bytesAt t.mem (t.gpr .a0) (t.gpr .a1).toNat) = a at ek ⊢
    have := (privateStatus_two a _ _).symm.trans ((iff_of_eq (congrArg (· = 2) ek)).trans (privateStatus_two a _ _))
    cases h₁ : Spec.Ffdh.privateValid a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) <;>
      cases h₂ : Spec.Ffdh.privateValid a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (t.gpr .a5) (t.gpr .a6).toNat)) <;>
      simp_all
  unfold kdOf
  rw [ev, ex, h3]

theorem kp_ct : ConstantTime isa kpContract.pre kpContract.pub checkPrivate :=
  RelCT.constantTime (kp_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨kdOf s, ⟨hs, rfl⟩, ⟨ht, (kdOf_eq hs ht hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.RISCV64.CheckPrivate
