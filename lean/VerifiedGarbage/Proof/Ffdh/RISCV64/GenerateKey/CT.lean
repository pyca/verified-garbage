module

-- separate module: built alongside Correct

public import VerifiedGarbage.Proof.Ffdh.RISCV64.GenerateKey.Body
public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.GenerateKey.Body
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.CT
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Correct
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_generate_key` on RISC-V: constant time

The public data `GD`: `vg_ffdh_derive_public`'s (`Derive.DD`), whose range
bit is that of the cut scalar for a valid p (`cutRange`, which the status
reveals), and `rand`'s address. The predicates carry `Derive.AR`, `rand` in
`t1`, x's and `rand`'s facts (`XR`) and the range bit (`PI`) to the scalar;
`vg_ffdh_derive_public`'s body is constant time by `Derive.body_rel`, and its
correctness gives what the mask of x needs (`Q5`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.GenerateKey

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive VG.Impl.Ffdh.RISCV64.GenerateKey
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.Derive (AR bnd DD inRange Inv W Z4 pins_W lp_W two_x body_ok)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- Whether the cut scalar is within its bound. -/
def cutRange (x : XD) (R : Addr) (m : Mem) : Bool :=
  decide (0 < Spec.Rsa.os2ip (gkOct m x.D R x.k x.L) ∧ Spec.Rsa.os2ip (gkOct m x.D R x.k x.L) < bnd m x.D x.k x.L x.p)

/-- The public data of a run. -/
structure GD where
  d : DD
  R : Addr

def gdOf (s : State) : GD :=
  ⟨⟨gxOf s, Spec.Rsa.modulusValid (gxOf s).p (gxOf s).k && cutRange (gxOf s) (s.gpr .a7) s.mem⟩, s.gpr .a7⟩

/-- The range bit, as the data has it, for a valid p. -/
def PI (g : GD) (s : State) : Prop :=
  Spec.Rsa.modulusValid g.d.x.p g.d.x.k = true → cutRange g.d.x g.R s.mem = g.d.v

theorem PI.keep {g : GD} {s t u : State} {o n : Nat} (h : PI g s) (hc : Ctx g.d.x u) (hx : XR g.d.x g.R u)
    (hm : Outside g.d.x.S o n s.mem t.mem) (hn : o + n ≤ g.d.x.Z) : PI g t := by
  have hL := hc.hL
  have eR := Pub.bytes_apart hm hn hx.sepRS
  have eB : Spec.Rsa.bytesAt t.mem (bptr g.d.x.D g.d.x.k g.d.x.L) g.d.x.k =
      Spec.Rsa.bytesAt s.mem (bptr g.d.x.D g.d.x.k g.d.x.L) g.d.x.k := by
    unfold bptr
    by_cases hq : g.d.x.L = 3 * g.d.x.k
    · rw [ite_eq_left hq, Pub.bytes_apart hm hn fun i hi => by
        have h' := hc.sepD (2 * g.d.x.k + i) (by omega_arith); rw [← Derive.off_off] at h'; exact h']
    · rw [ite_eq_right hq, Pub.bytes_apart hm hn fun i hi => hc.sepD i (by omega_arith)]
  have eb : bnd t.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p = bnd s.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p := by
    unfold bnd
    by_cases hq : g.d.x.L = 3 * g.d.x.k
    · rw [ite_eq_left hq, ite_eq_left hq, Pub.bytes_apart hm hn fun i hi => by
        have h' := hc.sepD (2 * g.d.x.k + i) (by omega_arith); rw [← Derive.off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  intro hv
  unfold cutRange
  rw [gkOct_congr eR eB, eb]
  exact h hv

/-- `Φ` of the data, with the argument registers, `rand`, its facts and the
range bit. -/
def U (Φ : XD → State → Prop) (g : GD) (s : State) : Prop :=
  Φ g.d.x s ∧ AR g.d.x s ∧ s.gpr .t1 = g.R ∧ XR g.d.x g.R s ∧ PI g s

theorem U.keep {Φ Ψ : XD → State → Prop} {g : GD} {s t : State} (h : U Φ g s) (hc : ∀ x s, Φ x s → Ctx x s)
    (h' : Ψ g.d.x t) (ha : Arr g.d.x s.mem t.mem) (k : Keep [.a0, .s0, .t3, .t4, .t5] s t) : U Ψ g t := by
  have hZ := (hc _ _ h.1).hZ
  unfold slot hdrBytes at hZ
  exact ⟨h', h.2.1.keep k, (k.gpr (by decide)).trans h.2.2.1, h.2.2.2.1.keep k.2.1 k.2.2,
    h.2.2.2.2.keep (hc _ _ h.1) h.2.2.2.1 ha (by omega_arith)⟩

/-! ## The predicates -/

def P0 (g : GD) (s : State) : Prop := gkContract.pre s ∧ gdOf s = g

/-- After the working space's address. -/
def F1 (g : GD) (s : State) : Prop :=
  s.gpr .t0 = g.d.x.S ∧ WP isa (.block (PublicChecked.saveRegs ++ (gkHdr ++ PublicChecked.setup))) s (U Base g)

/-- Before the scalar: p valid. -/
def S4 (g : GD) (s : State) : Prop := U X4 g s ∧ s.gpr .s0 = 0

/-- After the scalar. -/
def Q4 (g : GD) (s : State) : Prop := Z4 g.d s ∧ XR g.d.x g.R s

/-- After `vg_ffdh_derive_public`'s body. -/
def Q5 (g : GD) (s : State) : Prop :=
  s.gpr .s6 = g.d.x.S ∧ Scr s g.d.x.S g.d.x.Z ∧ 256 ≤ g.d.x.Z ∧ 64 ≤ g.d.x.k ∧ g.d.x.k ≤ 1024 ∧
    (∃ n < 4, s.gpr .a0 = BitVec.ofNat 64 n) ∧
    word s.mem g.d.x.S 8 = off g.d.x.X 0 ∧ word s.mem g.d.x.S 16 = BitVec.ofNat 64 g.d.x.k ∧ XR g.d.x g.R s

/-- Before the mask's loop. -/
def M (g : GD) (s : State) : Prop :=
  s.gpr .s6 = g.d.x.S ∧ s.gpr .a1 = off g.d.x.X 0 ∧ s.gpr .t5 = BitVec.ofNat 64 g.d.x.k ∧
    (∃ c : Bool, s.gpr .s4 = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if c then 1 else 0)) ∧ 64 ≤ g.d.x.k ∧
    g.d.x.k ≤ 1024 ∧ XR g.d.x g.R s

/-! ## Pins -/

theorem pins_U {Φ : XD → State → Prop} {rs : List Reg} (h : Pins Φ rs) : Pins (U Φ) rs :=
  fun g _ _ h₁ h₂ => h g.d.x _ _ h₁.1 h₂.1

theorem pins_P0 : Pins P0 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_F1 : Pins F1 [.t0] := pins_of (fun g _ => g.d.x.S) fun g s h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h.1

theorem pins_S4 : Pins S4 (baseRegs ++ ([.a2, .a3, .a4, .a5, .a6, .t1] : List Reg)) := by
  intro g s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pins_base (Φ := X4) (fun _ _ h => h.1) g.d.x s₁ s₂ h₁.1.1 h₂.1.1 r hr
  · refine pins_of (Φ := S4) (fun g r => if r = .t1 then g.R else Derive.arVal g.d.x r) (fun g s h r hr => ?_)
      g s₁ s₂ h₁ h₂ r hr
    have ha := h.1.2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [ha.a2, ha.a3, ha.a4, ha.a5, ha.a6, h.1.2.2.1]

theorem pins_Q5 : Pins Q5 [.s6] := pins_of (fun g _ => g.d.x.S) fun g s h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h.1

theorem pins_M : Pins M [.s6, .a1, .t5] :=
  pins_of (fun g r => if r = .s6 then g.d.x.S else if r = .a1 then off g.d.x.X 0 else BitVec.ofNat 64 g.d.x.k)
    fun g s h r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [h.1, h.2.1, h.2.2.1]

theorem pins_CFg : Pins (fun (g : GD) s => CF g.d.x s) [.s6] := fun g s₁ s₂ h₁ h₂ => pins_CF g.d.x s₁ s₂ h₁ h₂

theorem pins_TIg : Pins (fun g s => U X4 g s ∧ s.gpr .s0 ≠ 0) baseRegs :=
  fun g s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) g.d.x s₁ s₂ h₁.1.1 h₂.1.1

/-! ## The steps, by correctness -/

theorem GL1 {g : GD} {s : State} (h : P0 g s) :
    WP isa (.block ([.addSp .t0 8, .load .d .t0 .t0 0] : List Instr)) s (F1 g) := by
  obtain ⟨hpre, rfl⟩ := h
  have hf := WP.rdwr (gkFront_ok hpre)
  unfold gkFront at hf
  simp only [List.append_assoc] at hf
  rw [WP.block_append_iff] at hf
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨gkStack s, List.mem_append_left _ (by rw [hpre.1]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * 1)) 8
    simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have alsp : s.sp.toNat % 16 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := hpre
    exact h
  refine WP.mono (WP.and (loadS1_ok s hA1 alsp) hf) fun t ⟨⟨⟨a0, _⟩, _⟩, w⟩ => ⟨a0, ?_⟩
  refine WP.mono w fun u ⟨⟨hb, ha, h1, _, k, o⟩, r, w', _⟩ => ⟨hb, ha, h1, xr_of_pre hpre r w', ?_⟩
  · have hZ := hb.ctx.hZ
    unfold slot hdrBytes at hZ
    have hn : 0 + 256 ≤ (gxOf s).Z := by omega_arith
    have hi : PI (gdOf s) s := fun hv => by
      have hv' : Spec.Rsa.modulusValid (gxOf s).p (gxOf s).k = true := hv
      show cutRange (gxOf s) (s.gpr .a7) s.mem =
        (Spec.Rsa.modulusValid (gxOf s).p (gxOf s).k && cutRange (gxOf s) (s.gpr .a7) s.mem)
      rw [hv', Bool.true_and]
    exact PI.keep (s := s) (t := u) hi hb.ctx (xr_of_pre hpre r w') o hn

theorem TSc {g : GD} {s : State} (h : S4 g s) : WP isa scalar s (Q4 g) := by
  obtain ⟨⟨h4, ha, h1, hx, hpi⟩, hz⟩ := h
  have hv := h4.2.2.mp hz
  refine WP.mono (scalarX4_ok h4 hz ha hx h1) fun t ⟨t4, t0, ta, tx, tb, to⟩ => ⟨⟨⟨t4, ta, ?_⟩, t0⟩, tx⟩
  have hc := h4.1.ctx
  have hL := hc.hL
  have eb : bnd t.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p = bnd s.mem g.d.x.D g.d.x.k g.d.x.L g.d.x.p := by
    unfold bnd
    by_cases hq : g.d.x.L = 3 * g.d.x.k
    · rw [ite_eq_left hq, ite_eq_left hq, Pub.bytes_apart (Z := g.d.x.k) to (by omega_arith) fun i hi => by
        have h' := hx.sepDX (2 * g.d.x.k + i) (by omega_arith); rw [← Derive.off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  show inRange g.d.x t.mem = g.d.v
  unfold inRange
  rw [hx.xl, tb, eb]
  exact hpi hv

/-- `vg_ffdh_derive_public`'s body, then what the mask needs. -/
theorem TB {g : GD} {s : State} (h : Q4 g s) : WP isa dpBody s (Q5 g) := by
  obtain ⟨⟨⟨h4, ha, _⟩, hz⟩, hx⟩ := h
  have hv := h4.2.2.mp hz
  have hc := h4.1.ctx
  have hn := hc.scr.nowrap
  have hZ := hc.hZ
  unfold slot hdrBytes at hZ
  refine WP.mono (WP.rdwr (body_ok h4 hz ha)) fun t ⟨⟨dp, d6, m, am, om⟩, r, w, _⟩ => ?_
  have hw : ∀ d, d + 8 ≤ 256 → word t.mem g.d.x.S d = word s.mem g.d.x.S d := fun d hd => by
    refine (Pub.Outside.word_apart om hx.sepSO (by omega_arith) (by omega_arith) hn).trans ?_
    show Mont.word m _ _ = _
    exact Outside.word am (Or.inl hd) (by omega_arith)
  refine ⟨d6, hc.scr.congr w, by omega_arith, hc.k64, hc.k1024, ?_, by rw [hw 8 (by decide)]; exact hc.hX,
    by rw [hw 16 (by decide), hc.hXL, hx.xl], hx.keep r w⟩
  rw [(dp hv).2]
  exact ⟨_, by split <;> [decide; split <;> decide], rfl⟩

theorem TM {g : GD} {s : State} (h : Q5 g s) : WP isa (.block maskPre) s (M g) := by
  obtain ⟨h6, hs, hZ, k1, k2, ⟨n, hn, h0⟩, hX, hK, hx⟩ := h
  exact WP.mono (WP.rdwr (maskPre_ok hs hZ h6 h0 hn hX hK)) fun t ⟨⟨⟨t4, t1, t5, _⟩, kt⟩, r, w, _⟩ =>
    ⟨(kt.gpr (by decide)).trans h6, t1, t5, ⟨decide (n = 1), by rw [t4]; simp⟩, k1, k2, hx.keep r w⟩

theorem TL {g : GD} {s : State} (h : M g s) : WP isa maskLoop s (CF g.d.x) := by
  obtain ⟨h6, h1, h5, ⟨c, h4⟩, k1, k2, hx⟩ := h
  exact WP.mono (masked_ok (c := c) (by omega_arith) (by omega_arith) hx.nwX hx.wX h1 h4 h5)
    fun _ ⟨_, kt⟩ => (kt.gpr (by decide)).trans h6

/-! ## Constant time -/

theorem two_g {Φ : XD → State → Prop} {s₁ s₂ : State} (h : Two (fun (g : GD) s => Φ g.d.x s) s₁ s₂) :
    Two Φ s₁ s₂ :=
  let ⟨g, h₁, h₂, hsp⟩ := h
  ⟨g.d.x, h₁, h₂, hsp⟩

/-- After p's check, for a valid p. -/
theorem body_rel : RelCT isa (Two S4) gkBody (Two fun (g : GD) s => CF g.d.x s) := by
  unfold gkBody maskX
  exact RelCT.seq (two_post (two_taint _ pins_S4 (by taint_decide)) fun _ _ h => TSc h)
    (RelCT.seq (two_post (Ψ := Q5) (RelCT.mono Derive.body_rel (fun s₁ s₂ ⟨g, h₁, h₂, hsp⟩ => ⟨g.d, h₁.1, h₂.1, hsp⟩)
        fun _ _ _ => trivial) fun _ _ h => TB h)
      (RelCT.seq (two_post (two_taint _ pins_Q5 (by taint_decide)) fun _ _ h => TM h)
        (two_post (two_taint _ pins_M (by taint_decide)) fun _ _ h => TL h)))

theorem gk_rel : RelCT isa (Two P0) generateKey fun _ _ => True := by
  unfold generateKey gkFront
  simp only [List.append_assoc]
  refine RelCT.seq (R := Two (U Base)) ?_ (RelCT.seq (R := Two (U X4)) ?_
    (RelCT.seq (R := Two CF) ?_ (two_taint _ pins_CF (by taint_decide))))
  · exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_P0 (by taint_decide)) fun _ _ h => GL1 h)
      (two_post (two_taint _ pins_F1 (by taint_decide)) fun _ _ h => h.2))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_U (pins_base fun _ _ h => h)) (by taint_decide))
        fun _ _ h => WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (loadN_X h.1) (by rfl)) fun _ ⟨⟨h', a⟩, k⟩ =>
          h.keep (fun _ _ h => h.ctx) h' a k)
      (RelCT.seq (two_post (two_taint _ (pins_U (pins_base (Φ := X2) fun _ _ h => h.1)) (by taint_decide))
          fun _ _ h => WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (check1_X h.1) (by rfl)) fun _ ⟨⟨h', m⟩, k⟩ =>
            h.keep (fun _ _ h => h.1.ctx) h' (by rw [m]; exact Outside.refl _ _ _ _) k)
        (two_post (two_taint _ (pins_U pins_X3) (by taint_decide)) fun _ _ h =>
          WP.mono (WP.keep [.a0, .s0, .t3, .t4, .t5] (check2_X h.1) (by rfl)) fun _ ⟨⟨h', m⟩, k⟩ =>
            h.keep (fun _ _ h => h.1.ctx) h' (by rw [m]; exact Outside.refl _ _ _ _) k))
  · refine RelCT.ite (fun s₁ s₂ ⟨g, h₁, h₂, _⟩ => ?_)
      (RelCT.mono body_rel (fun s₁ s₂ ⟨⟨g, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_g h)
      (RelCT.mono (two_post (Φ := fun g s => U X4 g s ∧ s.gpr .s0 ≠ 0)
        (two_taint _ pins_TIg (by taint_decide)) (Ψ := fun g s => CF g.d.x s) fun _ _ h => TI ⟨h.1.1, h.2⟩)
        (fun s₁ s₂ ⟨⟨g, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_g h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.2.2, h₂.1.2.2]
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 = 0 := by simpa using hc
      exact ⟨g, ⟨h₁, h0⟩, ⟨h₂, h₂.1.2.2.mpr (h₁.1.2.2.mp h0)⟩, hsp⟩
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 ≠ 0 := by simpa using hc
      exact ⟨g, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.1.2.2.mpr (h₂.1.2.2.mp e))⟩, hsp⟩

/-- For a valid p, `cutRange` is `privateValid` of the attempt's scalar. -/
theorem cutRange_eq {s : State} (h : gkContract.pre s) (hv : Spec.Rsa.modulusValid (gxOf s).p (gxOf s).k = true) :
    cutRange (gxOf s) (s.gpr .a7) s.mem = Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s.gpr .a6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat))
      (Spec.Ffdh.scalarOfOctets (Spec.Ffdh.domainOf (s.gpr .a6).toNat
        (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -, -, hrl, -⟩ := h
  have hL' : (s.gpr .a5).toNat = 2 * (s.gpr .a6).toNat ∨ (s.gpr .a5).toNat = 3 * (s.gpr .a6).toNat := hL
  have hp : (gxOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a6).toNat) := by
    show Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).take (s.gpr .a6).toNat) = _
    rw [Proof.Ffdh.take_bytesAt _ _ (by rcases hL' with h | h <;> omega_arith)]
  have hf := VG.Proof.Bignum.valid_facts hv (by change 64 ≤ (s.gpr .a6).toNat; omega_arith)
  rw [Derive.privateValid_dom (by omega_arith) hL', hrl,
    ← gkOct_eq s.mem (s.gpr .a4) (s.gpr .a7) (by omega_arith) hL' (fun _ => by rw [← hp]; exact ⟨hf.1, hf.2.1⟩)]
  unfold cutRange
  rw [hp]
  rfl

theorem gdOf_eq {s t : State} (hs : gkContract.pre s) (ht : gkContract.pre t) (hp : gkContract.pub s t) :
    gdOf s = gdOf t := by
  obtain ⟨_, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, hb⟩ := hp
  simp only [gkLeak] at hb
  obtain ⟨e1, e2⟩ := List.append_inj hb (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h5])
  have eb : Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a4) (t.gpr .a5).toNat :=
    (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
  have ex : gxOf s = gxOf t := by
    simp only [gxOf]
    rw [eb]
    simp only [h0, h2, h4, h5, h6, a1, a2]
  have ev : (Spec.Rsa.modulusValid (gxOf s).p (gxOf s).k && cutRange (gxOf s) (s.gpr .a7) s.mem) =
      (Spec.Rsa.modulusValid (gxOf t).p (gxOf t).k && cutRange (gxOf t) (t.gpr .a7) t.mem) := by
    cases hv : Spec.Rsa.modulusValid (gxOf s).p (gxOf s).k
    · have hv' : Spec.Rsa.modulusValid (gxOf t).p (gxOf t).k = false := by rw [← ex]; exact hv
      rw [hv', Bool.false_and, Bool.false_and]
    · have hv' : Spec.Rsa.modulusValid (gxOf t).p (gxOf t).k = true := by rw [← ex]; exact hv
      rw [hv', Bool.true_and, Bool.true_and]
      rw [cutRange_eq hs hv, cutRange_eq ht hv']
      have ek := List.cons.inj e2 |>.1
      simp only [gkStatus] at ek
      rw [eb, h6, h7, a0] at ek
      rw [eb, h6, h7, a0]
      generalize Spec.Ffdh.domainOf (t.gpr .a6).toNat (Spec.Rsa.bytesAt t.mem (t.gpr .a4) (t.gpr .a5).toNat) = a at ek ⊢
      have := (Derive.keyStatus_two a _).symm.trans ((iff_of_eq (congrArg (· = 2) ek)).trans (Derive.keyStatus_two a _))
      cases h₁ : Spec.Ffdh.privateValid a (Spec.Ffdh.scalarOfOctets a (Spec.Rsa.bytesAt s.mem (t.gpr .a7) (stackArg t 0).toNat)) <;>
        cases h₂ : Spec.Ffdh.privateValid a (Spec.Ffdh.scalarOfOctets a (Spec.Rsa.bytesAt t.mem (t.gpr .a7) (stackArg t 0).toNat)) <;>
        simp_all
  unfold gdOf
  rw [ev, ex, h7]

theorem gk_ct : ConstantTime isa gkContract.pre gkContract.pub generateKey :=
  RelCT.constantTime (gk_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨gdOf s, ⟨hs, rfl⟩, ⟨ht, (gdOf_eq hs ht hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.RISCV64.GenerateKey
