module

-- separate module: built alongside Correct

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Derive.Body
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.CT
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.RISCV64.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.RISCV64.Li

/-!
# `vg_ffdh_derive_public` on RISC-V: constant time

As the exchange's (`Proof/Ffdh/RISCV64/CT.lean`), with the public data `DD`:
the exchange's for g as the peer and `y` as `out` (`dxOf`), and whether x is
within its bound, which the status reveals (`keyStatus_two`). The predicates
fix what the code branches on (p's validity, whether there is q, x's range)
and the registers the next piece uses as addresses or counts; where a piece
computes from memory, the next predicate follows by correctness. The
exchange's predicates cover the power and the output.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Derive

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Derive
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-- The public data of a run: the exchange's, and whether x is within its
bound. -/
structure DD where
  x : XD
  v : Bool

/-- Whether x is within its bound, in `m`. -/
def inRange (x : XD) (m : Mem) : Bool :=
  decide (0 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.X x.xl) ∧
    Spec.Rsa.os2ip (Spec.Rsa.bytesAt m x.X x.xl) < bnd m x.D x.k x.L x.p)

def ddOf (s : State) : DD := ⟨dxOf s, inRange (dxOf s) s.mem⟩

/-- x's range, as the data has it. -/
def Inv (d : DD) (s : State) : Prop := inRange d.x s.mem = d.v

theorem Inv.keep {d : DD} {s t u : State} {o n : Nat} (h : Inv d s) (hc : Ctx d.x u)
    (hm : Outside d.x.S o n s.mem t.mem) (hn : o + n ≤ d.x.Z) : Inv d t := by
  have hL := hc.hL
  have ex := Pub.bytes_apart hm hn hc.sepX
  have eb : bnd t.mem d.x.D d.x.k d.x.L d.x.p = bnd s.mem d.x.D d.x.k d.x.L d.x.p := by
    unfold bnd
    by_cases hq : d.x.L = 3 * d.x.k
    · rw [ite_eq_left hq, ite_eq_left hq, Pub.bytes_apart hm hn fun i hi => by
        have h' := hc.sepD (2 * d.x.k + i) (by omega_arith); rw [← off_off] at h'; exact h']
    · rw [ite_eq_right hq, ite_eq_right hq]
  unfold Inv inRange
  rw [ex, eb]
  exact h

/-- `Φ` of the exchange's data, with the argument registers and x's range. -/
def W (Φ : XD → State → Prop) (d : DD) (s : State) : Prop := Φ d.x s ∧ AR d.x s ∧ Inv d s

/-! ## The predicates -/

def Z0 (d : DD) (s : State) : Prop := dpContract.pre s ∧ ddOf s = d

/-- Before x's range: p valid. -/
def Z4 (d : DD) (s : State) : Prop := W X4 d s ∧ s.gpr .s0 = 0

/-- After x's range: `s9` is zero exactly when x is out of range. -/
def RB (d : DD) (s : State) : Prop := X4 d.x s ∧ s.gpr .s0 = 0 ∧ (s.gpr .s9 = 0 ↔ d.v = false)

/-! ## Pins -/

theorem pins_W {Φ : XD → State → Prop} {rs : List Reg} (h : Pins Φ rs) : Pins (W Φ) rs :=
  fun d _ _ h₁ h₂ => h d.x _ _ h₁.1 h₂.1

theorem pins_Z0 : Pins Z0 [.a7] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  rw [List.mem_singleton] at hr
  subst hr
  exact (congrArg (fun d => d.x.S) h₁).trans (congrArg (fun d => d.x.S) h₂).symm

/-- The registers `AR` fixes, as functions of the data. -/
def arVal (x : XD) : Reg → BitVec 64
  | .a2 => x.D
  | .a3 => BitVec.ofNat 64 x.L
  | .a4 => BitVec.ofNat 64 x.k
  | .a5 => x.X
  | .a6 => BitVec.ofNat 64 x.xl
  | _ => 0

theorem pins_Z4 : Pins Z4 (baseRegs ++ ([.a2, .a3, .a4, .a5, .a6] : List Reg)) := by
  intro d s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pins_base (Φ := fun x s => X4 x s) (fun _ _ h => h.1) d.x s₁ s₂ h₁.1.1 h₂.1.1 r hr
  · refine pins_of (Φ := Z4) (fun d => arVal d.x) (fun d s h r hr => ?_) d s₁ s₂ h₁ h₂ r hr
    have ha := h.1.2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [ha.a2, ha.a3, ha.a4, ha.a5, ha.a6]

/-! ## The steps, by correctness -/

theorem front_W {d : DD} {s : State} (h : Z0 d s) : WP isa (.block dpFront) s (W Base d) := by
  obtain ⟨hpre, rfl⟩ := h
  refine WP.mono (dpFront_ok hpre) fun t ⟨hb, _, k, o⟩ => ⟨hb, ⟨k.gpr (by decide), ?_, ?_, k.gpr (by decide), ?_⟩, ?_⟩
  · rw [k.gpr (by decide)]; simp [ddOf, dxOf]
  · rw [k.gpr (by decide)]; simp [ddOf, dxOf]
  · rw [k.gpr (by decide)]; simp [ddOf, dxOf]
  · have hZ := hb.ctx.hZ
    unfold slot hdrBytes at hZ
    have hn : 0 + 256 ≤ (dxOf s).Z := by omega_arith
    have hi : Inv (ddOf s) s := by unfold Inv ddOf; dsimp only
    exact Inv.keep (d := ddOf s) (s := s) (t := t) hi hb.ctx o hn

/-- A piece of `loadP`, which writes only `a0`, `s0`, `t3`–`t5` and arrays. -/
theorem lp_W {Φ Ψ : XD → State → Prop} {c : Prog isa} {d : DD} {s : State}
    (hc : ∀ x s, Φ x s → Ctx x s) (h : W Φ d s)
    (hw : WP isa c s fun t => (Ψ d.x t ∧ Arr d.x s.mem t.mem) ∧ Keep [.a0, .s0, .t3, .t4, .t5] s t) :
    WP isa c s (W Ψ d) :=
  WP.mono hw fun _ ⟨⟨h', a⟩, k⟩ =>
    ⟨h', h.2.1.keep k, h.2.2.keep (hc _ _ h.1) a (by have := (hc _ _ h.1).hZ; unfold slot hdrBytes at this; omega_arith)⟩

theorem pins_RB : Pins (fun d s => RB d s ∧ s.gpr .s9 = 0) baseRegs :=
  fun d s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) d.x s₁ s₂ h₁.1.1 h₂.1.1

theorem pins_TI : Pins (fun d s => W X4 d s ∧ s.gpr .s0 ≠ 0) baseRegs :=
  fun d s₁ s₂ h₁ h₂ => pins_base (Φ := X4) (fun _ _ h => h.1) d.x s₁ s₂ h₁.1.1 h₂.1.1

theorem TB {d : DD} {s : State} (h : RB d s ∧ s.gpr .s9 = 0) : WP isa dpBad s (CF d.x) :=
  WP.mono (bad_ok h.1.1.1 h.2) fun _ ⟨_, t6, _⟩ => t6

/-- The status. -/
theorem TS {x : XD} {s : State} (h : CF x s) : WP isa (.block status) s (CF x) := by
  refine WP.mono (WP.keep [.a0, .t2] (Q := fun _ => True) (by unfold status; brun [fin64_exec_li_lit (show 3 < 2048 by decide)]; exact ⟨_, rfl⟩) (by rfl) (by rfl))
    fun t ⟨_, kt⟩ => (kt.gpr (by decide)).trans h

/-! ## Constant time -/

/-- x in range: as the exchange, then the status. -/
theorem good_rel : RelCT isa (Two fun x s => X4 x s ∧ s.gpr .s0 = 0) dpGood (Two CF) := by
  unfold dpGood exPre exOut
  exact RelCT.seq (RelCT.seq (two_post (two_taint _ (pins_base fun _ _ h => h.1.1) (by taint_decide))
      fun _ _ h => TV h)
    (two_post (two_taint _ pins_Y1 (by taint_decide)) fun _ _ h => h.2))
    (RelCT.seq (two_post (two_taint _ pins_Y5 (by taint_decide)) fun _ _ h => h.2)
      (RelCT.seq (RelCT.seq (two_post (two_taint _ pins_Y6 (by taint_decide)) fun _ _ h => h.2)
          (RelCT.seq (two_post (two_taint _ pins_Y7 (by taint_decide)) fun _ _ h => h.2)
            (two_post (two_taint _ pins_Y8 (by taint_decide)) fun _ _ h => h.2)))
        (two_post (two_taint _ pins_CF (by taint_decide)) fun _ _ h => TS h)))

theorem two_x {Φ : XD → State → Prop} {s₁ s₂ : State} (h : Two (fun (d : DD) s => Φ d.x s) s₁ s₂) :
    Two Φ s₁ s₂ :=
  let ⟨d, h₁, h₂, hsp⟩ := h
  ⟨d.x, h₁, h₂, hsp⟩

/-- After p's check, for a valid p. -/
theorem body_rel : RelCT isa (Two Z4) dpBody (Two CF) := by
  unfold dpBody
  refine RelCT.seq (R := Two RB) (two_post (two_taint _ pins_Z4 (by taint_decide)) fun d s h => ?_) ?_
  rotate_left
  · refine RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => ?_)
      (RelCT.mono (two_post (Φ := fun d s => RB d s ∧ s.gpr .s9 = 0)
        (two_taint _ pins_RB (by taint_decide))
        (Ψ := fun d s => CF d.x s) fun _ _ h => TB h)
        (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_x h)
      (RelCT.mono good_rel (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, _⟩ => ⟨d.x, ⟨h₁.1, h₁.2.1⟩, ⟨h₂.1, h₂.2.1⟩, hsp⟩)
        fun _ _ h => h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.2.2, h₂.2.2]
    · rw [Steps.eval_zero] at hc
      have h9 : s₁.gpr .s9 = 0 := by simpa using hc
      exact ⟨d, ⟨h₁, h9⟩, ⟨h₂, h₂.2.2.mpr (h₁.2.2.mp h9)⟩, hsp⟩
  · obtain ⟨⟨h4, ha, hi⟩, hz⟩ := h
    have hv := h4.2.2.mp hz
    refine WP.mono (xRange_ok h4 hv ha) fun t ⟨t4, t0, t9, _⟩ => ⟨t4, t0, ?_⟩
    rw [t9]
    have hi' : inRange d.x s.mem = d.v := hi
    unfold inRange at hi'
    rw [hi']
    cases d.v <;> decide

theorem dp_rel : RelCT isa (Two Z0) derivePublic fun _ _ => True := by
  unfold derivePublic
  refine RelCT.seq (R := Two (W Base)) (two_post (two_taint _ pins_Z0 (by taint_decide)) fun _ _ h => front_W h)
    (RelCT.seq (R := Two (W X4)) ?_ (RelCT.seq (R := Two CF) ?_ (two_taint _ pins_CF (by taint_decide))))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_W (pins_base fun _ _ h => h)) (by taint_decide)) fun _ _ h =>
        lp_W (fun _ _ h => h.ctx) h (WP.keep _ (loadN_X h.1) (by rfl)))
      (RelCT.seq (two_post (two_taint _ (pins_W (pins_base (Φ := X2) fun _ _ h => h.1)) (by taint_decide))
          fun _ _ h => lp_W (fun _ _ h => h.1.ctx) h (WP.keep _ (WP.mono (check1_X h.1) fun t ⟨h3, m⟩ =>
            ⟨h3, by rw [m]; exact Outside.refl _ _ _ _⟩) (by rfl)))
        (two_post (two_taint _ (pins_W pins_X3) (by taint_decide)) fun _ _ h => lp_W (fun _ _ h => h.1.ctx) h
          (WP.keep _ (WP.mono (check2_X h.1) fun t ⟨h4, m⟩ => ⟨h4, by rw [m]; exact Outside.refl _ _ _ _⟩) (by rfl))))
  · refine RelCT.ite (fun s₁ s₂ ⟨d, h₁, h₂, _⟩ => ?_)
      (RelCT.mono body_rel (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
      (RelCT.mono (two_post (Φ := fun d s => W X4 d s ∧ s.gpr .s0 ≠ 0)
        (two_taint _ pins_TI (by taint_decide)) (Ψ := fun d s => CF d.x s) fun _ _ h => TI ⟨h.1.1, h.2⟩)
        (fun s₁ s₂ ⟨⟨d, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => two_x h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.1.2.2, h₂.1.2.2]
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 = 0 := by simpa using hc
      exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, h₂.1.2.2.mpr (h₁.1.2.2.mp h0)⟩, hsp⟩
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 ≠ 0 := by simpa using hc
      exact ⟨d, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.1.2.2.mpr (h₂.1.2.2.mp e))⟩, hsp⟩

/-- `inRange` as `privateValid` of the domain. -/
theorem inRange_eq {s : State} (h : dpContract.pre s) :
    inRange (dxOf s) s.mem = Spec.Ffdh.privateValid (Spec.Ffdh.domainOf (s.gpr .a4).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat))
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, -⟩, hL, -⟩ := h
  have hL' : (s.gpr .a3).toNat = 2 * (s.gpr .a4).toNat ∨ (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat := hL
  rw [privateValid_dom (by omega_arith) hL']
  have hp : (dxOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a4).toNat) := by
    show Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat).take (s.gpr .a4).toNat) = _
    rw [Proof.Ffdh.take_bytesAt _ _ (by rcases hL' with h | h <;> omega_arith)]
  unfold inRange
  rw [hp]
  rfl

theorem ddOf_eq {s t : State} (hs : dpContract.pre s) (ht : dpContract.pre t) (hp : dpContract.pub s t) :
    ddOf s = ddOf t := by
  obtain ⟨_, h0, h1, h2, h3, h4, h5, h6, h7, a0, hb⟩ := hp
  simp only [dpLeak] at hb
  obtain ⟨e1, e2⟩ := List.append_inj hb (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h3])
  have eb : Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat = Spec.Rsa.bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat :=
    (List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1
  have ex : dxOf s = dxOf t := by
    simp only [dxOf]
    rw [eb]
    simp only [h0, h2, h3, h4, h5, h6, h7, a0]
  have ev : inRange (dxOf s) s.mem = inRange (dxOf t) t.mem := by
    rw [inRange_eq hs, inRange_eq ht]
    have ek := List.cons.inj e2 |>.1
    rw [eb, h4] at ek
    rw [eb, h4]
    generalize Spec.Ffdh.domainOf (t.gpr .a4).toNat (Spec.Rsa.bytesAt t.mem (t.gpr .a2) (t.gpr .a3).toNat) = a at ek ⊢
    have := (keyStatus_two a _).symm.trans ((iff_of_eq (congrArg (· = 2) ek)).trans (keyStatus_two a _))
    cases h₁ : Spec.Ffdh.privateValid a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)) <;>
      cases h₂ : Spec.Ffdh.privateValid a (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (t.gpr .a5) (t.gpr .a6).toNat)) <;>
      simp_all
  unfold ddOf
  rw [ev, ex]

theorem dp_ct : ConstantTime isa dpContract.pre dpContract.pub derivePublic :=
  RelCT.constantTime (dp_rel.mono (fun s _ ⟨hs, ht, hp⟩ =>
    ⟨ddOf s, ⟨hs, rfl⟩, ⟨ht, (ddOf_eq hs ht hp).symm⟩, hp.1⟩) fun _ _ h => h)

end VG.Proof.Ffdh.RISCV64.Derive
