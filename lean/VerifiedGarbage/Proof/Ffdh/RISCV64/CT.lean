module

-- separate module: built alongside Correct

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Out
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Ffdh.RISCV64.Out
meta import VerifiedGarbage.Proof.Bignum.RISCV64.PreCT
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_ffdh_exchange` on RISC-V: constant time

Two runs with the same public data (`xdOf`: the pointers, the lengths and
the domain's octets, not x's) are related at each cut by `Two`, as on
PPC64LE. The predicates fix what the code branches on (p's first octet and
validity) and the registers that the code loads back from memory, which the
taint analysis treats as secret: the working space's address from the
stack, and the peer's, x's and `out`'s addresses and x's length from the
header. Where the code computes from x and the peer (from `exPre` on), each
predicate states the registers the next piece needs and that the rest of
the code reaches the next predicate.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64

open VG VG.RISCV64 VG.RISCV64.Taint VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pre (Two Pins two_post two_taint)

/-! ## The predicates -/

def X0 (x : XD) (s : State) : Prop := fnContract.pre s ∧ xdOf s = x

/-- The front after its first two instructions. -/
abbrev frontRest : List Instr :=
  PublicChecked.saveRegs ++ (([.store .d .a0 .s6 0, .store .d .a5 .s6 8, .store .d .a6 .s6 16,
    .store .d .a7 .s6 24, .addi .s7 .a2 0, .addi .s8 .a4 0, .addi .a1 .a4 0] : List Instr) ++ PublicChecked.setup)

/-- After loading the working space's address. -/
def F1 (x : XD) (s : State) : Prop := s.gpr .t0 = x.S ∧ WP isa (.block frontRest) s (Base x)

/-- After the branch. -/
def CF (x : XD) (s : State) : Prop := s.gpr .s6 = x.S

/-- Before the output. -/
def Y8 (x : XD) (s : State) : Prop := R8 x s ∧ WP isa PublicChecked.output s (CF x)

/-- Before `out`'s load. -/
def Y7 (x : XD) (s : State) : Prop := RW x s ∧ WP isa (.block [.load .d .s10 .s6 0]) s (Y8 x)

/-- After the power. -/
def Y6 (x : XD) (s : State) : Prop := RW x s ∧ WP isa zMask s (Y7 x)

/-- Before the power. -/
def Y5 (x : XD) (s : State) : Prop := R5 x s ∧ WP isa ModExp.powWin s (Y6 x)

/-- After the peer's address. -/
def Y1 (x : XD) (s : State) : Prop :=
  R1 x s ∧ WP isa (.seq PublicChecked.loadX (.seq r2 (.block [.load .d .s9 .s6 8, .load .d .s10 .s6 16]))) s (Y5 x)

/-- `Pins` from registers that the predicate fixes as functions of the data. -/
theorem pins_of {α : Type} {Φ : α → State → Prop} {rs : List Reg} (f : α → Reg → BitVec 64)
    (h : ∀ a s, Φ a s → ∀ r ∈ rs, s.gpr r = f a r) : Pins Φ rs :=
  fun a _ _ h₁ h₂ r hr => (h a _ h₁ r hr).trans (h a _ h₂ r hr).symm

/-- The registers `RW` fixes, as functions of the data. -/
def rwVal (x : XD) : Reg → BitVec 64
  | .s6 => x.S
  | .a7 => off x.S (slot x.w 0)
  | .s5 => BitVec.ofNat 64 (8 * (x.w + 2))
  | .t0 => BitVec.ofNat 64 x.w
  | .s11 => BitVec.ofNat 64 x.k
  | .a6 => x.Y
  | .s9 => off x.X 0
  | .s10 => BitVec.ofNat 64 x.xl
  | _ => 0

theorem rw_vals {x : XD} {s : State} (h : RW x s) : ∀ r ∈ ([.s6, .a7, .s5, .t0, .s11] : List Reg),
    s.gpr r = rwVal x r := by
  obtain ⟨a, b, c, d, e⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  exacts [a, b, c, d, e]

theorem pins_base {Φ : XD → State → Prop} (h : ∀ x s, Φ x s → Base x s) : Pins Φ baseRegs := by
  intro x s₁ s₂ h₁ h₂ r hr
  have h₁ := h _ _ h₁
  have h₂ := h _ _ h₂
  simp only [baseRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.s6, h₂.s6]
  · rw [h₁.a7, h₂.a7]
  · rw [h₁.s5, h₂.s5]
  · rw [h₁.t0, h₂.t0]
  · rw [h₁.s7, h₂.s7]
  · rw [h₁.s8, h₂.s8]
  · rw [h₁.s10, h₂.s10]
  · rw [h₁.s11, h₂.s11]

theorem pins_X0 : Pins X0 ([] : List Reg) := fun _ _ _ _ _ _ hr => absurd hr List.not_mem_nil

theorem pins_F1 : Pins F1 [.t0] := pins_of (fun x _ => x.S) fun x s h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h.1

theorem pins_X3 : Pins X3 (baseRegs ++ ([.t4] : List Reg)) := by
  intro x s₁ s₂ h₁ h₂ r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact pins_base (Φ := X3) (fun _ _ h => h.1) x s₁ s₂ h₁ h₂ r hr
  · rw [List.mem_singleton] at hr; subst hr; rw [h₁.2.2.1, h₂.2.2.1]

theorem pins_Y1 : Pins Y1 [.a6, .s6, .a7, .s5, .t0, .s11] := pins_of rwVal fun x s h r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | hr
  · exact h.1.1
  · exact rw_vals h.1.2 r (by simpa using hr)

theorem pins_Y5 : Pins Y5 [.s9, .s10, .s6, .a7, .s5, .t0, .s11] := pins_of rwVal fun x s h r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | hr
  · exact h.1.1
  · exact h.1.2.1
  · exact rw_vals h.1.2.2 r (by simpa using hr)

theorem pins_Y6 : Pins Y6 [.s6, .a7, .s5, .t0, .s11] := pins_of rwVal fun _ _ h => rw_vals h.1

theorem pins_Y7 : Pins Y7 [.s6, .a7, .s5, .t0, .s11] := pins_of rwVal fun _ _ h => rw_vals h.1

theorem pins_Y8 : Pins Y8 [.s10, .s6, .a7, .s5, .t0, .s11] :=
  pins_of (fun x r => if r = .s10 then off x.O 0 else rwVal x r) fun x s h r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | hr
    · exact h.1.1
    · have hne : r ≠ .s10 := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [ite_eq_right_of_eq_false _ _ (eq_false hne)]
      exact rw_vals h.1.2 r (by simpa using hr)

theorem pins_CF : Pins CF [.s6] := pins_of (fun x _ => x.S) fun x s h r hr => by
  rw [List.mem_singleton] at hr; subst hr; exact h

/-! ## The steps, by correctness -/

theorem XL1 {x : XD} {s : State} (h : X0 x s) :
    WP isa (.block ([.addSp .t0 8, .load .d .t0 .t0 0] : List Instr)) s (F1 x) := by
  obtain ⟨hpre, rfl⟩ := h
  have hf := front_ok hpre
  unfold exFront at hf
  simp only [List.append_assoc] at hf
  rw [WP.block_append_iff] at hf
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨stackArgs s, List.mem_append_left _ (by rw [hpre.1]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * 1)) 8
    simp only [Nat.mul_zero, Nat.mul_one, add_ofNat_zero]
    exact Offset.contains_base _ (by omega) (by omega)
  have alsp : s.sp.toNat % 16 = 0 := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact WP.mono (WP.and (loadS1_ok s hA1 alsp) hf) fun t ⟨⟨⟨a0, _⟩, _⟩, w⟩ =>
    ⟨a0, WP.mono w fun _ h => h.1⟩

theorem TV {x : XD} {s : State} (h : X4 x s ∧ s.gpr .s0 = 0) : WP isa (.block [.load .d .a6 .s6 24]) s (Y1 x) := by
  obtain ⟨h4, hz⟩ := h
  have hv := h4.2.2.mp hz
  have hf := VG.Proof.Bignum.valid_facts hv h4.1.ctx.k64
  have hpk : x.p < 256 ^ x.k := by
    have := VG.Proof.Bignum.os2ip_lt (x.db.take x.k)
    rwa [take_len h4.1.ctx.hL.1 h4.1.ctx] at this
  refine WP.mono (exPre_split h4 hz) fun s₁ ⟨r1, w1⟩ => ⟨r1, WP.mono w1 fun s₅ ⟨r5, w5⟩ =>
    ⟨r5, WP.mono w5 fun s₆ pp => ⟨pp.regs, ?_⟩⟩⟩
  refine WP.mono (exOut_split pp.ctx pp.regs pp.p hf.1 (by rw [pp.z]; exact Nat.mod_lt _ (by omega)) hpk)
    fun s₇ ⟨r7, w7⟩ => ⟨r7, WP.mono w7 fun s₈ ⟨r8, w8⟩ => ⟨r8, WP.mono w8 fun t op => op.s6⟩⟩

theorem TI {x : XD} {s : State} (h : X4 x s ∧ s.gpr .s0 ≠ 0) : WP isa (.block [.li .a0 0]) s (CF x) := by
  refine WP.mono (WP.keep [.a0] (Q := fun _ => True) (by brun [exec_li]; exact ⟨_, rfl⟩) (by rfl) (by rfl)) fun t ⟨_, kt⟩ => ?_
  exact (kt.gpr (by decide)).trans h.1.1.s6

/-! ## Constant time -/

theorem ex_rel : RelCT isa (Two X0) exchange fun _ _ => True := by
  unfold exchange exFront
  simp only [List.append_assoc]
  refine RelCT.seq (R := Two Base) ?_ (RelCT.seq (R := Two X4) ?_
    (RelCT.seq (R := Two CF) ?_ (two_taint _ pins_CF (by taint_decide))))
  · exact RelCT.block_append (RelCT.seq (two_post (two_taint _ pins_X0 (by taint_decide)) fun _ _ h => XL1 h)
      (two_post (two_taint _ pins_F1 (by taint_decide)) fun _ _ h => h.2))
  · unfold loadP Precompute.check
    exact RelCT.seq (two_post (two_taint _ (pins_base fun _ _ h => h) (by taint_decide)) fun _ _ h =>
        WP.mono (loadN_X h) fun _ h => h.1)
      (RelCT.seq (two_post (two_taint _ (pins_base (Φ := X2) fun _ _ h => h.1) (by taint_decide))
          fun _ _ h => WP.mono (check1_X h) fun _ h => h.1)
        (two_post (two_taint _ pins_X3 (by taint_decide)) fun _ _ h => WP.mono (check2_X h) fun _ h => h.1))
  · refine RelCT.ite (fun s₁ s₂ ⟨x, h₁, h₂, _⟩ => ?_)
      (RelCT.mono (P := Two fun x s => X4 x s ∧ s.gpr .s0 = 0) ?_
        (fun s₁ s₂ ⟨⟨x, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
      (RelCT.mono (two_post (Φ := fun x s => X4 x s ∧ s.gpr .s0 ≠ 0)
        (two_taint _ (pins_base fun _ _ h => h.1.1) (by taint_decide)) fun _ _ h => TI h)
        (fun s₁ s₂ ⟨⟨x, h₁, h₂, hsp⟩, hc⟩ => ?_) fun _ _ h => h)
    · rw [Steps.eval_zero, Steps.eval_zero]
      congr 1
      rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, h₁.2.2, h₂.2.2]
    · unfold exPre exOut
      exact RelCT.seq (RelCT.seq (two_post (two_taint _ (pins_base fun _ _ h => h.1.1) (by taint_decide))
          fun _ _ h => TV h)
        (two_post (two_taint _ pins_Y1 (by taint_decide)) fun _ _ h => h.2))
        (RelCT.seq (two_post (two_taint _ pins_Y5 (by taint_decide)) fun _ _ h => h.2)
          (RelCT.seq (two_post (two_taint _ pins_Y6 (by taint_decide)) fun _ _ h => h.2)
            (RelCT.seq (two_post (two_taint _ pins_Y7 (by taint_decide)) fun _ _ h => h.2)
              (two_post (two_taint _ pins_Y8 (by taint_decide)) fun _ _ h => h.2))))
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 ≠ 0 := by simpa using hc
      exact ⟨x, ⟨h₁, h0⟩, ⟨h₂, fun e => h0 (h₁.2.2.mpr (h₂.2.2.mp e))⟩, hsp⟩
    · rw [Steps.eval_zero] at hc
      have h0 : s₁.gpr .s0 = 0 := by simpa using hc
      exact ⟨x, ⟨h₁, h0⟩, ⟨h₂, h₂.2.2.mpr (h₁.2.2.mp h0)⟩, hsp⟩

theorem ex_ct : ConstantTime isa fnContract.pre fnContract.pub exchange :=
  RelCT.constantTime (ex_rel.mono (fun s t ⟨hs, ht, hsp, h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, hb⟩ =>
    ⟨xdOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [exLeak] at hb
      obtain ⟨e12, -⟩ := List.append_inj hb (by
        simp only [List.length_append, List.length_map, VG.Proof.Bignum.bytesAt_length, h3, a0])
      obtain ⟨e1, -⟩ := List.append_inj e12 (by simp only [List.length_map, VG.Proof.Bignum.bytesAt_length, h3])
      simp only [xdOf]
      rw [(List.map_inj_right (fun _ _ h => BitVec.eq_of_toNat_eq h)).mp e1]
      simp only [h0, h2, h3, h4, h5, h6, h7, a1, a2]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Ffdh.RISCV64
