module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.InitCT
public import VerifiedGarbage.Proof.CmacTripleDes.StreamScratch
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Impl.StackScratch.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.StackScratch
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Common
meta import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Finish
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Proof.TripleDes.Schedule
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Finish
meta import VerifiedGarbage.Proof.Cmac.Frame
meta import VerifiedGarbage.Proof.Cmac.Spec
meta import VerifiedGarbage.Proof.Cmac.Stream
meta import VerifiedGarbage.Proof.TripleDes.Schedule

/-! ### `CmacTripleDes.Stream.RISCV64.FinishCT`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on RISC-V: `finish` in constant time

As `stream_init` (`InitCT.lean`): the code around the call is constant time
by the taint analysis, from the registers that hold public values there
(`count`, the number of bytes held back computed from it, and the
pointers), and the call by its own proof (`ecb_rel`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.Proof.CmacTripleDes.Stream (held)

/-- The public registers after the number of bytes held back is computed. -/
structure HB (s₀ : State) (St O S : Addr) (n : Nat) (s : State) : Prop where
  t0 : s.gpr .t0 = BitVec.ofNat 64 (held n)
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = O
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- …and the branch's condition. -/
structure HC (s₀ : State) (St O S : Addr) (n : Nat) (s : State) : Prop extends HB s₀ St O S n s where
  t1 : s.gpr .t1 = BitVec.ofNat 64 (held n) - BitVec.ofNat 64 8

theorem hb_wp {s₀ s : State} {St O S : Addr} {n : Nat} (hp : FPre s₀ St O S n) (h : FMid₁ s₀ St O S n s) :
    WP isa heldCode s (HB s₀ St O S n) :=
  WP.mono (heldCode_wp hp.hn h.a1) fun _ ⟨t0, g, _, rd, wr, sp⟩ =>
    ⟨t0, by rw [g _ (by decide), h.s1], by rw [g _ (by decide), h.s2], by rw [g _ (by decide), h.s3],
      by rw [rd, h.rd], by rw [wr, h.wr], by rw [sp, h.sp]⟩

theorem hc_wp {s₀ s : State} {St O S : Addr} {n : Nat} (h : HB s₀ St O S n s) :
    WP isa (.block [.addi .t1 .t0 (-8)]) s (HC s₀ St O S n) :=
  wp_subi (imm := 8) (by decide) fun s' u => WP.block_nil
    ⟨⟨by rw [u.other _ (by decide), h.t0], by rw [u.other _ (by decide), h.s1], by rw [u.other _ (by decide), h.s2],
      by rw [u.other _ (by decide), h.s3], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.sp, h.sp]⟩,
      by rw [u.gpr, h.t0]⟩

/-- What the branch leaves, for `finXor`. -/
structure HD (s₀ : State) (St O S : Addr) (n : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = O
  t5 : s.gpr .t5 = mpOf St S (held n)
  t6 : s.gpr .t6 = kpOf St (held n)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem hd_wp {s₀ s : State} {St O S : Addr} {n : Nat} (hp : FPre s₀ St O S n) (h : HC s₀ St O S n s) :
    WP isa (.ite (.zero .t1) (.block complete) padded) s (HD s₀ St O S n) := by
  have stW : (⟨St, 416⟩ : Region) ∈ s.wr := by rw [h.wr, hp.wr]; simp
  have sW : (⟨S, 640⟩ : Region) ∈ s.wr := by rw [h.wr, hp.wr]; simp
  exact WP.mono (branch_wp (Proof.CmacTripleDes.Stream.held_le n) h.s1 h.s2 h.t0 h.t1 stW sW hp.st_s)
    fun _ b => ⟨by rw [b.keep _ (by decide), h.s1], by rw [b.keep _ (by decide), h.s2],
      by rw [b.keep _ (by decide), h.s3], b.t5, b.t6, by rw [b.rd, h.rd], by rw [b.wr, h.wr], by rw [b.sp, h.sp]⟩

/-- What `finXor` leaves, for ECB's call. -/
structure HE (s₀ : State) (St O S : Addr) (s : State) : Prop where
  args : EArgs s St 400
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = O
  sp : s.sp = s₀.sp

theorem he_wp {s₀ s : State} {St O S : Addr} {n : Nat} (hp : FPre s₀ St O S n) (h : HD s₀ St O S n s) :
    WP isa (.block finXor) s (HE s₀ St O S) :=
  WP.mono (finXor_wp hp h.s1 h.wr h.rd h.sp h.t5 h.t6) fun _ x =>
    ⟨x.args, by rw [x.keep _ (by decide), h.s1], by rw [x.keep _ (by decide), h.s2],
      by rw [x.keep _ (by decide), h.s3], by rw [x.sp, h.sp]⟩

theorem finish_rel {s₀ s₀' : State} (h0 : finishRISCV64.pre s₀) (h0' : finishRISCV64.pre s₀')
    (hq : finishRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') finish fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a3) (s₀.gpr .a1).toNat := by
    rw [q3, q4, q5, q6]; exact FPre.of h0'
  generalize s₀.gpr .a0 = St at hp hp'
  generalize s₀.gpr .a2 = O at hp hp'
  generalize s₀.gpr .a3 = S at hp hp'
  generalize (s₀.gpr .a1).toNat = n at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block finSave) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.a1]) heldCode h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.t0]) (.block [.addi .t1 .t0 (-8)]) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hD⟩ : ∃ h, (taint.check (Taint.ofRegs [.t0, .t1, .s1, .s2])
      (.ite (.zero .t1) (.block complete) padded) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hE⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .t5, .t6]) (.block finXor) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hG⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2, .s3]) (.block finOut) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMid₁ s₀ St O S n) (F₂ := FMid₁ s₀' St O S n) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finSave_wp hp, finSave_wp hp'⟩
  have b := (taintRegs (P := fun a b => FMid₁ s₀ St O S n a ∧ FMid₁ s₀' St O S n b) [.a1]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h.1.a1, h.2.a1]⟩) hB).wp
    (F₁ := HB s₀ St O S n) (F₂ := HB s₀' St O S n) fun a b h => ⟨hb_wp hp h.1, hb_wp hp' h.2⟩
  have c := (taintRegs (P := fun a b => HB s₀ St O S n a ∧ HB s₀' St O S n b) [.t0]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h.1.t0, h.2.t0]⟩) hC).wp
    (F₁ := HC s₀ St O S n) (F₂ := HC s₀' St O S n) fun a b h => ⟨hc_wp h.1, hc_wp h.2⟩
  have d := (taintRegs (P := fun a b => HC s₀ St O S n a ∧ HC s₀' St O S n b) [.t0, .t1, .s1, .s2]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.t0, h.2.t0]
      · rw [h.1.t1, h.2.t1]
      · rw [h.1.s1, h.2.s1]
      · rw [h.1.s2, h.2.s2]⟩) hD).wp
    (F₁ := HD s₀ St O S n) (F₂ := HD s₀' St O S n) fun a b h => ⟨hd_wp hp h.1, hd_wp hp' h.2⟩
  have e := (taintRegs (P := fun a b => HD s₀ St O S n a ∧ HD s₀' St O S n b) [.s1, .t5, .t6]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.s1, h.2.s1]
      · rw [h.1.t5, h.2.t5]
      · rw [h.1.t6, h.2.t6]⟩) hE).wp
    (F₁ := HE s₀ St O S) (F₂ := HE s₀' St O S) fun a b h => ⟨he_wp hp h.1, he_wp hp' h.2⟩
  have f := (ecb_rel (P := fun a b => HE s₀ St O S a ∧ HE s₀' St O S b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.gpr .s3 = O ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.gpr .s3 = O ∧ s.sp = s₀'.sp)
    fun a b h => ⟨WP.mono (ecb_call h.1.args) fun _ x => ⟨by rw [x.saved _ (by decide), h.1.s1],
        by rw [x.saved _ (by decide), h.1.s2], by rw [x.saved _ (by decide), h.1.s3], by rw [x.sp, h.1.sp]⟩,
      WP.mono (ecb_call h.2.args) fun _ x => ⟨by rw [x.saved _ (by decide), h.2.s1],
        by rw [x.saved _ (by decide), h.2.s2], by rw [x.saved _ (by decide), h.2.s3], by rw [x.sp, h.2.sp]⟩⟩
  have g := taintRegs
    (P := fun a b => (a.gpr .s1 = St ∧ a.gpr .s2 = S ∧ a.gpr .s3 = O ∧ a.sp = s₀.sp) ∧
      b.gpr .s1 = St ∧ b.gpr .s2 = S ∧ b.gpr .s3 = O ∧ b.sp = s₀'.sp) [.s1, .s2, .s3]
    (fun a b h => by
      refine ⟨by rw [h.1.2.2.2, h.2.2.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]
      · rw [h.1.2.2.1, h.2.2.2.1]) hG
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((b.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((d.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((f.mono (fun _ _ h => h) fun _ _ h => h.2).seq g)))))

theorem finish_ct : ConstantTime isa finishRISCV64.pre finishRISCV64.pub finish :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finish_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end

/-! ### `CmacTripleDes.Stream.RISCV64.AbsorbCT`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.RISCV64.Absorb`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.RISCV64.AbsorbChain`, which only this module used -/

section

/-! ### `CmacTripleDes.Stream.RISCV64.AbsorbParts`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on RISC-V: `absorb`, before the paths

The precondition by name (`APre`), the registers saved (`absSave_wp`), and
the number `h` of bytes held back with the room `8 - h` after them and
whether the data fit there (`flag_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.Proof.CmacTripleDes.Stream (held)

/-- The precondition, by name: the state `St`, `count = n`, the `L` bytes of
data at `D` and the scratch buffer `S`. -/
structure APre (s₀ : State) (St D S : Addr) (n L : Nat) : Prop where
  a0 : s₀.gpr .a0 = St
  a1 : s₀.gpr .a1 = BitVec.ofNat 64 n
  a2 : s₀.gpr .a2 = D
  a3 : s₀.gpr .a3 = BitVec.ofNat 64 L
  a4 : s₀.gpr .a4 = S
  hn : n < 2 ^ 64
  hL : L < 2 ^ 64
  rd : s₀.rd = [⟨D, L⟩]
  wr : s₀.wr = [⟨St, 416⟩, ⟨S, 688⟩]
  st_d : (⟨St, 416⟩ : Region).Disjoint ⟨D, L⟩
  st_s : (⟨St, 416⟩ : Region).Disjoint ⟨S, 688⟩
  d_s : (⟨D, L⟩ : Region).Disjoint ⟨S, 688⟩
  stk_st : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨St, 416⟩
  stk_d : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨D, L⟩
  stk_s : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨S, 688⟩
  wSt : St.toNat + 416 ≤ 2 ^ 64
  wD : D.toNat + L ≤ 2 ^ 64
  wS : S.toNat + 688 ≤ 2 ^ 64
  al : s₀.sp.toNat % 16 = 0
  sp : 944 ≤ s₀.sp.toNat

theorem APre.of {s₀ : State} (h : absorbRISCV64.pre s₀) :
    APre s₀ (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a4) (s₀.gpr .a1).toNat (s₀.gpr .a3).toNat :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := h
  ⟨rfl, ofNat_toNat_eq rfl, rfl, ofNat_toNat_eq rfl, rfl, (s₀.gpr .a1).isLt, (s₀.gpr .a3).isLt,
    a, b, c, d, e, f, g, h, i, j, k, l, m⟩

/-- What the code saves: the registers, with `t0` the slots' base. -/
abbrev absG (s₀ : State) (S : Addr) : Reg → BitVec 64 := (s₀.write .t0 (sv S)).gpr

theorem abs_bound : ∀ p ∈ absSaved, p.2 + 8 ≤ 48 := by decide

/-- What `absSave` leaves. -/
structure AMid (s₀ : State) (St D S : Addr) (n L : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D
  a1 : s.gpr .a1 = BitVec.ofNat 64 n
  a3 : s.gpr .a3 = BitVec.ofNat 64 L
  other : ∀ r ∈ preserved, r ≠ .s1 → r ≠ .s2 → r ≠ .s3 → s.gpr r = s₀.gpr r
  mem : s.mem = Spill.saveMem s₀.mem (sv S) (absG s₀ S) absSaved
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem absSave_wp {s₀ : State} {St D S : Addr} {n L : Nat} (hp : APre s₀ St D S n L) :
    WP isa (.block absSave) s₀ (AMid s₀ St D S n L) := by
  rw [absSave, saveRegs, List.append_assoc, WP.block_append_iff]
  refine WP.mono (savePtr_ok .a4) fun s₁ e => ?_
  subst e
  rw [hp.a4, show absSaved.map (fun (r, d) => Instr.store .d r .t0 d) = Spill.saveCode .t0 absSaved from rfl]
  obtain t₀ : (s₀.write .t0 (sv S)).gpr .t0 = sv S := RegUpd.gpr_write_self _ _ _
  have g₀ (r : Reg) (hr : r ≠ .t0) : (s₀.write .t0 (sv S)).gpr r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine Spill.save_ok (b := .t0) (l := absSaved) (by rw [t₀]; exact Align.align_al _) (by decide)
    (fun p hp' => ?_) ?_
  · have := abs_bound p hp'
    rw [t₀]
    show InRegions s₀.wr _ 8
    rw [hp.wr]
    exact ⟨⟨S, 688⟩, by simp, sv_contains S (by omega_using [this]) (by decide)⟩
  generalize ht : ({ (s₀.write .t0 (sv S)) with
    mem := Spill.saveMem (s₀.write .t0 (sv S)).mem ((s₀.write .t0 (sv S)).gpr .t0)
      (s₀.write .t0 (sv S)).gpr absSaved } : State) = t
  have gt (r : Reg) (hr : r ≠ .t0) : t.gpr r = s₀.gpr r := by rw [← ht]; exact g₀ r hr
  obtain memt : t.mem = Spill.saveMem s₀.mem (sv S) (absG s₀ S) absSaved := by
    rw [← ht]; show Spill.saveMem _ _ _ _ = _; rw [t₀, RegUpd.mem_write]
  obtain rdt : t.rd = s₀.rd := by rw [← ht]; rfl
  obtain wrt : t.wr = s₀.wr := by rw [← ht]; rfl
  obtain spt : t.sp = s₀.sp := by rw [← ht]; rfl
  unfold mov
  refine wp_mv fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr h1 h2 h3 => ?_, ?_, by rw [u₃.rd, u₂.rd, u₁.rd, rdt],
    by rw [u₃.wr, u₂.wr, u₁.wr, wrt], by rw [u₃.sp, u₂.sp, u₁.sp, spt]⟩
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.gpr, gt, hp.a0]
  · simp (disch := decide) only [u₃.other, u₂.gpr, u₁.other, gt, hp.a4]
  · simp (disch := decide) only [u₃.gpr, u₂.other, u₁.other, gt, hp.a2]
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.other, gt, hp.a1]
  · simp (disch := decide) only [u₃.other, u₂.other, u₁.other, gt, hp.a3]
  · obtain ⟨h0, -⟩ := preserved_ne r hr
    rw [u₃.other _ h3, u₂.other _ h2, u₁.other _ h1, gt _ h0]
  · rw [u₃.mem, u₂.mem, u₁.mem, memt]

/-- What `heldCode` and `absFlag` leave: the number `h` of bytes held back,
the room after them, and whether the data do not fit there. -/
structure AFl (St D S : Addr) (n L : Nat) (u s : State) : Prop where
  t0 : s.gpr .t0 = BitVec.ofNat 64 (held n)
  t1 : s.gpr .t1 = BitVec.ofNat 64 (8 - held n)
  t2 : s.gpr .t2 = if 8 - held n < L then 1 else 0
  keep : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t2 → s.gpr r = u.gpr r
  mem : s.mem = u.mem
  rd : s.rd = u.rd
  wr : s.wr = u.wr
  sp : s.sp = u.sp

theorem absFlag_wp {u t : State} {n L : Nat} {St D S : Addr} (hL : L < 2 ^ 64)
    (h3 : u.gpr .a3 = BitVec.ofNat 64 L) (t0 : t.gpr .t0 = BitVec.ofNat 64 (held n))
    (g : ∀ r, r ≠ .t0 → t.gpr r = u.gpr r) (m : t.mem = u.mem) (rd : t.rd = u.rd) (wr : t.wr = u.wr)
    (sp : t.sp = u.sp) : WP isa (.block absFlag) t (AFl St D S n L u) := by
  obtain hl := Proof.CmacTripleDes.Stream.held_le n
  unfold absFlag
  refine wp_li (imm := 8) (by decide) fun s₁ u₁ => wp_sub fun s₂ u₂ => wp_sltu fun s₃ u₃ => WP.block_nil ?_
  obtain t1₂ : s₂.gpr .t1 = BitVec.ofNat 64 (8 - held n) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), t0]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hl]
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), t0],
    by rw [u₃.other _ (by decide), t1₂], ?_, fun r a b c => ?_, by rw [u₃.mem, u₂.mem, u₁.mem, m],
    by rw [u₃.rd, u₂.rd, u₁.rd, rd], by rw [u₃.wr, u₂.wr, u₁.wr, wr], by rw [u₃.sp, u₂.sp, u₁.sp, sp]⟩
  · rw [u₃.gpr, t1₂, u₂.other _ (by decide), u₁.other _ (by decide), g _ (by decide), h3]
    congr 1
    simp only [BitVec.lt_def, toNat_ofNat (show 8 - held n < 2 ^ 64 by omega_using []), toNat_ofNat hL]
  · rw [u₃.other _ c, u₂.other _ b, u₁.other _ b, g _ a]

theorem flag_wp {u : State} {n L : Nat} {St D S : Addr} (hn : n < 2 ^ 64) (hL : L < 2 ^ 64)
    (h1 : u.gpr .a1 = BitVec.ofNat 64 n) (h3 : u.gpr .a3 = BitVec.ofNat 64 L) {rest : Prog isa}
    {Q : State → Prop} (k : ∀ s, AFl St D S n L u s → WP isa rest s Q) :
    WP isa (.seq heldCode (.seq (.block absFlag) rest)) u Q :=
  WP.seq (WP.mono (heldCode_wp hn h1) fun _ ⟨t0, g, m, rd, wr, sp⟩ =>
    WP.seq (WP.mono (absFlag_wp hL h3 t0 g m rd wr sp) k))

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end


/-!
# Streaming TDEA-CMAC on RISC-V: `absorb`'s chaining path

When the data do not fit in the `r = 8 - h` bytes after the `h` bytes held
back, the code copies their first `r` bytes there (`chainCopy_wp`), XORs the
completed block into the chaining value and enciphers it in place
(`setup_wp`, `ecb_call`), then each of the `nb` whole blocks of the rest but
its last 1 to 8 bytes (`loop_ok`, with `CInv`), and copies those to the
start of the bytes held back (`chain_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.WriteBytes (writeBytes)

/-- The whole blocks chained after the completed one. -/
abbrev nbOf (L r : Nat) : Nat := (L - r - 1) / 8

/-- The bytes held back after them. -/
abbrev tailOf (L r : Nat) : Nat := L - r - 8 * nbOf L r

/-- Where the chaining path starts, by name: the state `St`, the data `D` of
`L` bytes, the scratch buffer `S`, `h` bytes held back and `r = 8 - h` after
them, fewer than `L`. -/
structure CPre (s₀ : State) (St D S : Addr) (h L : Nat) (u : State) : Prop where
  s1 : u.gpr .s1 = St
  s2 : u.gpr .s2 = S
  s3 : u.gpr .s3 = D
  a3 : u.gpr .a3 = BitVec.ofNat 64 L
  t0 : u.gpr .t0 = BitVec.ofNat 64 h
  t1 : u.gpr .t1 = BitVec.ofNat 64 (8 - h)
  hh : h ≤ 8
  lt : 8 - h < L
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp

/-- After the first copy: the block held back completed. -/
structure CCopy (s₀ : State) (St D S : Addr) (h L : Nat) (u s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D
  s4 : s.gpr .s4 = BitVec.ofNat 64 (L - (8 - h))
  t1 : s.gpr .t1 = BitVec.ofNat 64 (8 - h)
  keep : ∀ r ∈ preserved, r ≠ .s4 → s.gpr r = u.gpr r
  mem : s.mem = writeBytes u.mem (St + BitVec.ofNat 64 408 + BitVec.ofNat 64 h)
    (Spec.Aes.bytesAt u.mem D (8 - h))
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

/-- After the first block of the chaining path: the copy's arguments. -/
structure C1 (s₀ : State) (St D S : Addr) (h L : Nat) (u s : State) : Prop where
  s4 : s.gpr .s4 = BitVec.ofNat 64 (L - (8 - h))
  t3 : s.gpr .t3 = St + BitVec.ofNat 64 408 + BitVec.ofNat 64 h
  t4 : s.gpr .t4 = D
  t5 : s.gpr .t5 = BitVec.ofNat 64 (8 - h)
  keep : ∀ r, r ≠ .s4 → r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s.gpr r = u.gpr r
  mem : s.mem = u.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem pre1_wp {s₀ u : State} {St D S : Addr} {h L : Nat} (hc : CPre s₀ St D S h L u) :
    WP isa (.block (([.sub .s4 .a3 .t1] : List Instr) ++ toHeld .t1)) u (C1 s₀ St D S h L u) := by
  have hl := hc.lt
  have hh := hc.hh
  unfold toHeld mov
  simp only [List.cons_append, List.nil_append]
  refine wp_sub fun s₁ u₁ => wp_addi (imm := 408) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => wp_mv fun s₄ u₄ =>
    wp_mv fun s₅ u₅ => WP.block_nil ?_
  refine ⟨?_, ?_, ?_, ?_, fun r a b c d => ?_, by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hc.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hc.wr],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hc.sp]⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hc.a3, hc.t1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hl]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), u₁.other _ (by decide), hc.s1, hc.t0]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.s3]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hc.t1]
  · rw [u₅.other _ d, u₄.other _ c, u₃.other _ b, u₂.other _ b, u₁.other _ a]

theorem copy1_wp {s₀ u s₅ : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) (h₅ : C1 s₀ St D S h L u s₅) :
    WP isa (copy .t6 .t4 .t3 .t5) s₅ (CCopy s₀ St D S h L u) := by
  have hl := hc.lt
  have hh := hc.hh
  have hL := hp.hL
  have hw := hp.wSt
  obtain stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s₅ (P := D)
    (C := St + BitVec.ofNat 64 408 + BitVec.ofNat 64 h) (L := 8 - h) (by omega_using []) h₅.t4 h₅.t3 h₅.t5
    (fun i hi => by
      rw [h₅.rd, h₅.wr]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hl, hi]) (by omega_using [hi])⟩)
    (fun i hi => by
      rw [h₅.wr, Offset.add_add, Offset.add_add]
      exact ⟨_, stW, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (by
      rw [Offset.add_add]
      exact (hp.st_d.sub_left (Offset.sub_base St (by omega_using [hh]))).symm.sub_left
        (Region.sub_prefix (by omega_using [hl]))))) fun s₆ ⟨c, sp₆⟩ => ?_
  refine ⟨by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.s1],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.s2],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.s3],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.s4],
    by rw [c.other _ (by decide) (by decide) (by decide) (by decide), h₅.keep _ (by decide) (by decide)
      (by decide) (by decide), hc.t1],
    fun r hr h4 => ?_, by rw [c.mem, h₅.mem], by rw [c.rd, h₅.rd], by rw [c.wr, h₅.wr], by rw [sp₆, h₅.sp]⟩
  obtain ⟨-, -, -, h3, h4', h5, h6, -⟩ := preserved_ne r hr
  rw [c.other r h6 h4' h3 h5, h₅.keep r h4 h3 h4' h5]

theorem chainCopy_wp {s₀ u : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) {rest : Prog isa} {Q : State → Prop}
    (k : ∀ c, CCopy s₀ St D S h L u c → WP isa rest c Q) :
    WP isa (.seq (.block (([.sub .s4 .a3 .t1] : List Instr) ++ toHeld .t1)) (.seq (copy .t6 .t4 .t3 .t5) rest)) u Q :=
  WP.seq (WP.mono (pre1_wp hc) fun _ h₅ => WP.seq (WP.mono (copy1_wp hp hc h₅) k))

theorem shr3_ofNat {x : Nat} (hx : x < 2 ^ 64) : BitVec.ofNat 64 x >>> 3 = BitVec.ofNat 64 (x / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by have := Nat.div_le_self x 8; omega_using [hx])]

theorem shl3_ofNat {x : Nat} (hx : 8 * x < 2 ^ 64) : BitVec.ofNat 64 x <<< 3 = BitVec.ofNat 64 (8 * x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega_using [hx] : x < 2 ^ 64)]
  omega_using []

/-- After `chainSetup`: the completed block XORed into the chaining value,
the data pointer past the bytes that completed it, the blocks to chain and
the bytes to hold back after them, and ECB's arguments. -/
structure CSet (s₀ : State) (St D S : Addr) (h L : Nat) (c s : State) : Prop where
  args : EArgs s St 400
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (8 - h)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (tailOf L (8 - h))
  s5 : s.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h))
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s.gpr r = c.gpr r
  frame : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] c.mem s.mem
  out : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.xor (Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 400) 8)
      (Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 408) 8)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem setup_wp {s₀ u c : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) (hcc : CCopy s₀ St D S h L u c) :
    WP isa (.block chainSetup) c (CSet s₀ St D S h L c) := by
  have hl := hc.lt
  have hh := hc.hh
  have hL := hp.hL
  have hw := hp.wSt
  obtain stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  unfold chainSetup
  simp only [List.cons_append, List.nil_append]
  refine wp_add fun s₁ u₁ => wp_subi (imm := 1) (by decide) fun s₂ u₂ => wp_srl (by decide) fun s₃ u₃ =>
    wp_sll (by decide) fun s₄ u₄ => wp_sub fun s₅ u₅ => wp_addi (imm := 400) (by decide) fun s₆ u₆ =>
    wp_addi (imm := 408) (by decide) fun s₇ u₇ => ?_
  obtain g₇ : ∀ r, r ≠ .s3 → r ≠ .t2 → r ≠ .s5 → r ≠ .s4 → r ≠ .a0 → r ≠ .a1 → s₇.gpr r = c.gpr r :=
    fun r a b d e f g => by
      rw [u₇.other _ g, u₆.other _ f, u₅.other _ e, u₄.other _ b, u₃.other _ d, u₂.other _ b, u₁.other _ a]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hcc.rd]
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hcc.wr]
  obtain sp₇ : s₇.sp = s₀.sp := by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hcc.sp]
  obtain m₇ : s₇.mem = c.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain t2₂ : s₂.gpr .t2 = BitVec.ofNat 64 (L - (8 - h) - 1) := by
    rw [u₂.gpr, u₁.other _ (by decide), hcc.s4]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hl]
  obtain s5₃ : s₃.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h)) := by
    rw [u₃.gpr, t2₂, shr3_ofNat (by omega_using [hL])]
  obtain t2₄ : s₄.gpr .t2 = BitVec.ofNat 64 (8 * nbOf L (8 - h)) := by
    rw [u₄.gpr, s5₃, shl3_ofNat (by unfold nbOf; omega_using [hL])]
  obtain s4₅ : s₅.gpr .s4 = BitVec.ofNat 64 (tailOf L (8 - h)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      hcc.s4, t2₄]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold tailOf nbOf; omega_using []
  obtain s1₇ : s₇.gpr .s1 = St := by rw [g₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    hcc.s1]
  obtain a0₇ : s₇.gpr .a0 = St + BitVec.ofNat 64 400 := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hcc.s1]
  obtain a1₇ : s₇.gpr .a1 = St + BitVec.ofNat 64 408 := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hcc.s1]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.xorBytes_ok (t := .t0) (u := .t1) (dst := .a0) (src := .a1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi => by rw [a1₇, rd₇, wr₇, Offset.add_add]; exact in_wr ⟨_, stW, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (fun i hi => by rw [a0₇, wr₇, Offset.add_add]; exact ⟨_, stW, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    (by rw [a0₇, a1₇]; exact nsep (Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [])))) fun s₈ x₈ => ?_
  unfold ecbArgs mov
  refine wp_mv fun s₉ u₉ => wp_addi (imm := 400) (by decide) fun s₁₀ u₁₀ => ?_
  refine WP.cons (exec_li (show imm12 1 by decide)) (WP.block_nil ?_)
  obtain g₁₀ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .a0 → r ≠ .a1 → s₁₀.gpr r = s₇.gpr r := fun r a b d e => by
    rw [u₁₀.other _ e, u₉.other _ d, x₈.gpr _ a b]
  obtain s1₁₀ : s₁₀.gpr .s1 = St := by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), s1₇]
  obtain sp₁₀ : s₁₀.sp = s₀.sp := by rw [u₁₀.sp, u₉.sp, x₈.sp, sp₇]
  obtain fx : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] c.mem s₁₀.mem := by
    have := x₈.frame; rw [a0₇, m₇] at this; rw [u₁₀.mem, u₉.mem]; exact this
  refine ⟨⟨?_, ?_, by simp [RegUpd.gpr_write], by decide, by decide, hw,
      by simp only [RegUpd.sp_write]; rw [sp₁₀]; exact hp.al, by simp only [RegUpd.sp_write]; rw [sp₁₀]; exact hp.sp,
      by simp only [RegUpd.sp_write]; rw [sp₁₀]; exact hp.stk_st,
      by simp only [RegUpd.wr_write]; rw [u₁₀.wr, u₉.wr, x₈.wr, wr₇]; exact stW⟩,
    ?_, ?_, ?_, ?_, ?_, fun r hr a b d => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a0 ≠ .a2 by decide)]; rw [u₁₀.other _ (by decide), u₉.gpr,
      x₈.gpr _ (by decide) (by decide), s1₇]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .a2 by decide)]; rw [u₁₀.gpr, u₉.other _ (by decide),
      x₈.gpr _ (by decide) (by decide), s1₇]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s1 ≠ .a2 by decide)]; exact s1₁₀
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s2 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), g₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hcc.s2]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s3 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
      hcc.s3, hcc.t1]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s4 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide), s4₅]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s5 ≠ .a2 by decide)]
    rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), s5₃]
  · obtain ⟨h0, h1, h2, -, -, -, -, -, ha0, ha1, ha2, -⟩ := preserved_ne r hr
    simp only [RegUpd.gpr_write_of_ne _ _ ha2]
    rw [g₁₀ r h0 h1 ha0 ha1, g₇ r a h2 d b ha0 ha1]
  · simp only [RegUpd.mem_write]; exact fx
  · simp only [RegUpd.mem_write]
    obtain e := xorBytes_bytes x₈
    rw [a0₇, a1₇, m₇] at e
    rw [u₁₀.mem, u₉.mem, e]
  · simp only [RegUpd.rd_write]; rw [u₁₀.rd, u₉.rd, x₈.rd, rd₇]
  · simp only [RegUpd.wr_write]; rw [u₁₀.wr, u₉.wr, x₈.wr, wr₇]
  · simp only [RegUpd.sp_write]; exact sp₁₀


/-! ## The loop -/

/-- After `k` whole blocks chained, from the state `e` after the completed
block's. -/
structure CInv (s₀ : State) (St D S : Addr) (h L : Nat) (e : State) (k : Nat) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  s3 : s.gpr .s3 = D + BitVec.ofNat 64 (8 - h + 8 * k)
  s4 : s.gpr .s4 = BitVec.ofNat 64 (tailOf L (8 - h))
  s5 : s.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h) - k)
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s5 → s.gpr r = e.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩] e.mem s.mem
  cv : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt e.mem St))
      (Spec.Aes.bytesAt e.mem (St + BitVec.ofNat 64 400) 8)
      (Spec.Cmac.blocksAt e.mem (D + BitVec.ofNat 64 (8 - h)) 8 k)

/-- What the block of the loop's body leaves: one more block XORed into the
chaining value, and ECB's arguments. -/
structure BMid (s₀ : State) (St D S : Addr) (h L : Nat) (e : State) (k : Nat) (s s' : State) : Prop where
  args : EArgs s' St 400
  s1 : s'.gpr .s1 = St
  s3 : s'.gpr .s3 = D + BitVec.ofNat 64 (8 - h + 8 * (k + 1))
  s5 : s'.gpr .s5 = BitVec.ofNat 64 (nbOf L (8 - h) - (k + 1))
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s5 → s'.gpr r = s.gpr r
  rd : s'.rd = s₀.rd
  wr : s'.wr = s₀.wr
  sp : s'.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 8⟩] s.mem s'.mem
  cv : Spec.Aes.bytesAt s'.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.xor (Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8)
      (Spec.Aes.bytesAt s.mem (D + BitVec.ofNat 64 (8 - h + 8 * k)) 8)

theorem bodyBlk_wp {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {k : Nat}
    (hk : k < nbOf L (8 - h)) {s : State} (hi : CInv s₀ St D S h L e k s) :
    WP isa (.block (([.addi .t3 .s1 400] : List Instr) ++ Impl.Words.RISCV64.xorBytes .t0 .t1 .t3 .s3 8 ++
      ([.addi .s3 .s3 8, .addi .s5 .s5 (-1)] : List Instr) ++ ecbArgs 400)) s (BMid s₀ St D S h L e k s) := by
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  obtain stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  obtain hb : 8 - h + 8 * k + 8 ≤ L := by unfold nbOf at hk; omega_using [hk]
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_addi (imm := 400) (by decide) fun s₁ u₁ => ?_
  obtain t3₁ : s₁.gpr .t3 = St + BitVec.ofNat 64 400 := by rw [u₁.gpr, hi.s1]
  rw [WP.block_append_iff]
  refine WP.mono (Bytes.xorBytes_ok (t := .t0) (u := .t1) (dst := .t3) (src := .s3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi' => by
      rw [u₁.other _ (by decide), hi.s3, u₁.rd, u₁.wr, hi.rd, hi.wr, Offset.add_add]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hb, hi']) (by omega_using [hL, hb, hi'])⟩)
    (fun i hi' => by rw [t3₁, u₁.wr, hi.wr, Offset.add_add]; exact ⟨_, stW, Offset.contains_base _ (by omega_using [hi']) (by omega_using [hi'])⟩)
    (by
      rw [t3₁, u₁.other _ (by decide), hi.s3]
      exact nsep ((hp.st_d.sub_left (Offset.sub_base St (by decide))).sub_right (Offset.sub_base D (by omega_using [hb])))))
    fun s₂ x₂ => ?_
  refine wp_addi (imm := 8) (by decide) fun s₃ u₃ => wp_subi (imm := 1) (by decide) fun s₄ u₄ => ?_
  unfold ecbArgs mov
  refine wp_mv fun s₅ u₅ => wp_addi (imm := 400) (by decide) fun s₆ u₆ => ?_
  refine WP.cons (exec_li (show imm12 1 by decide)) (WP.block_nil ?_)
  obtain g₆ : ∀ r, r ≠ .t0 → r ≠ .t1 → r ≠ .t3 → r ≠ .s3 → r ≠ .s5 → r ≠ .a0 → r ≠ .a1 →
      s₆.gpr r = s.gpr r := fun r a b c d f g i => by
    rw [u₆.other _ i, u₅.other _ g, u₄.other _ f, u₃.other _ d, x₂.gpr _ a b, u₁.other _ c]
  obtain sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, x₂.sp, u₁.sp, hi.sp]
  obtain wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, x₂.wr, u₁.wr, hi.wr]
  obtain rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, x₂.rd, u₁.rd, hi.rd]
  obtain s1₆ : s₆.gpr .s1 = St := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hi.s1]
  obtain m₆ : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a0 ≠ .a2 by decide)]; rw [u₆.other _ (by decide), u₅.gpr,
        u₄.other _ (by decide), u₃.other _ (by decide), x₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), hi.s1],
      by simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.a1 ≠ .a2 by decide)]; rw [u₆.gpr, s1₆.symm.trans
        (by rw [u₆.other _ (by decide)])], by simp [RegUpd.gpr_write], by decide, by decide, hw,
      by simp only [RegUpd.sp_write]; rw [sp₆]; exact hp.al, by simp only [RegUpd.sp_write]; rw [sp₆]; exact hp.sp,
      by simp only [RegUpd.sp_write]; rw [sp₆]; exact hp.stk_st,
      by simp only [RegUpd.wr_write]; rw [wr₆]; exact stW⟩, ?_, ?_, ?_, fun r hr a b => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s1 ≠ .a2 by decide)]; exact s1₆
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s3 ≠ .a2 by decide)]
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, x₂.gpr _ (by decide) (by decide),
      u₁.other _ (by decide), hi.s3, Offset.add_add, show 8 - h + 8 * k + 8 = 8 - h + 8 * (k + 1) by omega_using []]
  · simp only [RegUpd.gpr_write_of_ne _ _ (show Reg.s5 ≠ .a2 by decide)]
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), x₂.gpr _ (by decide) (by decide),
      u₁.other _ (by decide), hi.s5]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    unfold nbOf at hk ⊢; omega_using [hk]
  · obtain ⟨h0, h1, -, h3, -, -, -, -, ha0, ha1, ha2, -⟩ := preserved_ne r hr
    simp only [RegUpd.gpr_write_of_ne _ _ ha2]
    rw [g₆ r h0 h1 h3 a b ha0 ha1]
  · simp only [RegUpd.rd_write]; exact rd₆
  · simp only [RegUpd.wr_write]; exact wr₆
  · simp only [RegUpd.sp_write]; exact sp₆
  · simp only [RegUpd.mem_write, m₆]
    have := x₂.frame; rwa [t3₁, u₁.mem] at this
  · simp only [RegUpd.mem_write, m₆]
    obtain e₂ := xorBytes_bytes x₂
    rw [t3₁, u₁.other _ (by decide), hi.s3, u₁.mem] at e₂
    exact e₂

theorem body_ok {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {k : Nat}
    (hk : k < nbOf L (8 - h)) {s : State} (hi : CInv s₀ St D S h L e k s) :
    WP isa chainBody s (CInv s₀ St D S h L e (k + 1)) := by
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  obtain hb : 8 - h + 8 * k + 8 ≤ L := by unfold nbOf at hk; omega_using [hk]
  unfold chainBody
  refine WP.seq (WP.mono (bodyBlk_wp hp hk hi) fun s₆ hm => ?_)
  refine WP.mono (ecb_call hm.args) fun s₇ h₇ => ?_
  -- The memory.
  obtain f₇ : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩] s₆.mem s₇.mem := by
    have := h₇.frame; rwa [hm.sp] at this
  obtain big : Frame [⟨St + BitVec.ofNat 64 400, 8⟩, ⟨s₀.sp - 944, 944⟩] e.mem s₇.mem :=
    (hi.frame.trans (hm.frame.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)).trans f₇
  obtain dSch : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 8⟩ : Region), ⟨s₀.sp - 944, 944⟩], (⟨St, 384⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint St (by decide) (by omega_using [])
      · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
  obtain sch : Spec.TripleDes.scheduleAt s₆.mem St = Spec.TripleDes.scheduleAt e.mem St := by
    rw [Proof.TripleDes.scheduleAt_eq_of_frame St hm.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dSch _ (by simp)),
      Proof.TripleDes.scheduleAt_eq_of_frame St hi.frame dSch]
  obtain blk : Spec.Aes.bytesAt s.mem (D + BitVec.ofNat 64 (8 - h + 8 * k)) 8 =
      Spec.Aes.bytesAt e.mem (D + BitVec.ofNat 64 (8 - h + 8 * k)) 8 :=
    Proof.Cmac.bytesAt_frame hi.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.st_d.sub_left (Offset.sub_base St (by decide))).symm.sub_left (Offset.sub_base D (by omega_using [hb]))
      · exact hp.stk_d.symm.sub_left (Offset.sub_base D (by omega_using [hb]))) (by decide)
  refine ⟨by rw [h₇.saved _ (by decide), hm.s1], by rw [h₇.saved _ (by decide), hm.keep _ (by decide) (by decide)
      (by decide), hi.s2], by rw [h₇.saved _ (by decide), hm.s3],
    by rw [h₇.saved _ (by decide), hm.keep _ (by decide) (by decide) (by decide), hi.s4],
    by rw [h₇.saved _ (by decide), hm.s5], fun r hr a b => by rw [h₇.saved r hr, hm.keep r hr a b, hi.keep r hr a b],
    by rw [h₇.rd, hm.rd], by rw [h₇.wr, hm.wr], by rw [h₇.sp, hm.sp], big, ?_⟩
  rw [h₇.out, hm.cv, sch, hi.cv, blk, blocksAt_succ, Proof.Cmac.chain_append, Proof.Cmac.chain_single,
    Offset.add_add]

theorem loop_ok {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {k : Nat} (hk : k < nbOf L (8 - h)) {s : State} (hi : CInv s₀ St D S h L e k s) :
    WP isa (.loop chainBody (.nonzero .s5)) s (CInv s₀ St D S h L e (nbOf L (8 - h))) := by
  obtain hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega_using [this]
  refine WP.loop (M := isa) (body := chainBody) (c := .nonzero .s5) (Q := CInv s₀ St D S h L e (nbOf L (8 - h)))
    (fun (m : Nat) (t : State) => ∃ j, m = nbOf L (8 - h) - j ∧ j < nbOf L (8 - h) ∧ CInv s₀ St D S h L e j t) ?_
    (nbOf L (8 - h) - k) s ⟨k, rfl, hk, hi⟩
  rintro m t ⟨j, rfl, hj, h'⟩
  refine WP.mono (body_ok hp hj h') fun t' h'' => ?_
  obtain ev := eval_nonzero_ofNat t' .s5 (k := nbOf L (8 - h) - (j + 1)) (by omega_using [hN]) h''.s5
  by_cases hz : nbOf L (8 - h) - (j + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [show nbOf L (8 - h) = j + 1 by omega_using [hj, hz]]
  · right
    refine ⟨by rw [ev]; simp [hz], nbOf L (8 - h) - (j + 1), by omega_using [hj], j + 1, rfl, by omega_using [hz], h''⟩

theorem chainLoop_wp {s₀ e : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L) {s : State} (hi : CInv s₀ St D S h L e 0 s) :
    WP isa chainLoop s (CInv s₀ St D S h L e (nbOf L (8 - h))) := by
  obtain hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega_using [this]
  obtain ev := eval_zero_ofNat s .s5 (k := nbOf L (8 - h) - 0) (by omega_using [hN]) hi.s5
  rw [Nat.sub_zero] at ev
  unfold chainLoop
  by_cases hn : nbOf L (8 - h) = 0
  · refine WP.ite true (by rw [ev, hn]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    rw [hn]; exact hi
  · refine WP.ite false (by rw [ev]; simp [hn]) (fun h => by cases h) fun _ => ?_
    exact loop_ok hp (by omega_using [hn]) hi


/-! ## The whole path -/

theorem blocksAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, (⟨p, 8 * n⟩ : Region).Disjoint r) (hn : 8 * n ≤ 2 ^ 64) :
    Spec.Cmac.blocksAt m' p 8 n = Spec.Cmac.blocksAt m p 8 n := by
  rw [Proof.CmacTripleDes.Stream.blocksAt_eq, Proof.CmacTripleDes.Stream.blocksAt_eq,
    Proof.Cmac.bytesAt_frame hf hd hn]

/-- What the chaining path leaves, from the state `u` it starts in. -/
structure CDone (s₀ : State) (St D S : Addr) (h L : Nat) (u s : State) : Prop where
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s.gpr r = u.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem
  cv : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 400) 8 =
    Spec.Cmac.chain (Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt u.mem St))
      (Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 400) 8)
      ([Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt u.mem D (8 - h)] ++
        Spec.Cmac.blocksAt u.mem (D + BitVec.ofNat 64 (8 - h)) 8 (nbOf L (8 - h)))
  held : Spec.Aes.bytesAt s.mem (St + BitVec.ofNat 64 408) (tailOf L (8 - h)) =
    Spec.Aes.bytesAt u.mem (D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h))) (tailOf L (8 - h))

theorem chain_wp {s₀ u : State} {St D S : Addr} {h L n : Nat} (hp : APre s₀ St D S n L)
    (hc : CPre s₀ St D S h L u) : WP isa chainPath u (CDone s₀ St D S h L u) := by
  have hl := hc.lt
  have hh := hc.hh
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  obtain stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  unfold chainPath
  refine chainCopy_wp hp hc fun c hcc => ?_
  refine WP.seq (WP.mono (setup_wp hp hc hcc) fun z hz => ?_)
  refine WP.seq (WP.mono (ecb_call hz.args) fun e he => ?_)
  obtain spe : e.sp = s₀.sp := by rw [he.sp, hz.sp]
  obtain ie : CInv s₀ St D S h L e 0 e := by
    refine ⟨by rw [he.saved _ (by decide), hz.s1], by rw [he.saved _ (by decide), hz.s2],
      by rw [he.saved _ (by decide), hz.s3, Nat.mul_zero, Nat.add_zero], by rw [he.saved _ (by decide), hz.s4],
      by rw [he.saved _ (by decide), hz.s5, Nat.sub_zero], fun _ _ _ _ => rfl, by rw [he.rd, hz.rd], by rw [he.wr, hz.wr], spe,
      Frame.refl _ _, rfl⟩
  refine WP.seq (WP.mono (chainLoop_wp hp ie) fun l hi => ?_)
  refine WP.seq ?_
  unfold mov
  refine wp_addi (imm := 408) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  obtain g₃ : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s₃.gpr r = l.gpr r := fun r a b c => by
    rw [u₃.other _ c, u₂.other _ b, u₁.other _ a]
  obtain hnb : 8 - h + 8 * nbOf L (8 - h) + tailOf L (8 - h) = L := by unfold tailOf nbOf; omega_using [hl]
  obtain htl : 0 < tailOf L (8 - h) ∧ tailOf L (8 - h) ≤ 8 := by unfold tailOf nbOf; omega_using [hl]
  refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) s₃ (P := D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h)))
    (C := St + BitVec.ofNat 64 408) (L := tailOf L (8 - h)) (by omega_using [htl])
    (by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.s3])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hi.s1])
    (by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hi.s4])
    (fun i hi' => by
      rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hi.rd, hi.wr, Offset.add_add]
      exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hnb, hi']) (by omega_using [hL, hnb, hi'])⟩)
    (fun i hi' => by
      rw [u₃.wr, u₂.wr, u₁.wr, hi.wr, Offset.add_add]
      exact ⟨_, stW, Offset.contains_base _ (by omega_using [htl, hi']) (by omega_using [htl, hi'])⟩)
    ((hp.st_d.sub_left (Offset.sub_base St (by omega_using [htl]))).symm.sub_left (Offset.sub_base D (by omega_using [hnb])))))
    fun f ⟨cf, spf⟩ => ?_
  -- The memory, step by step.
  obtain reg16 : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩], r ∈
      [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩] := fun _ h => h
  obtain s8 : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 8⟩ : Region), ⟨s₀.sp - 944, 944⟩],
      ∃ r' ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩], Region.Sub r r' := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨St + BitVec.ofNat 64 400, 16⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨⟨s₀.sp - 944, 944⟩, by simp, fun _ h => h⟩
  obtain Fc : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem c.mem := by
    rw [hcc.mem]
    exact (WriteBytes.writeBytes_frame u.mem _ _ (R := ⟨St + BitVec.ofNat 64 400, 16⟩) (by
      rw [Proof.Cmac.bytesAt_length, Offset.add_add]
      exact Offset.contains St (by omega_using []) (by omega_using [hh]) (by omega_using []))).mono (by simp)
  obtain Fz : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] c.mem z.mem :=
    hz.frame.sub fun r hr => ⟨⟨St + BitVec.ofNat 64 400, 16⟩, by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by decide)⟩
  obtain Fe : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] z.mem e.mem := by
    have := he.frame; rw [hz.sp] at this; exact this.sub s8
  obtain Fl : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] e.mem l.mem := hi.frame.sub s8
  obtain Ful := ((Fc.trans Fz).trans Fe).trans Fl
  obtain m₃ : s₃.mem = l.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain Ff : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] l.mem f.mem := by
    rw [cf.mem, m₃]
    exact (WriteBytes.writeBytes_frame l.mem _ _ (R := ⟨St + BitVec.ofNat 64 400, 16⟩) (by
      rw [Proof.Cmac.bytesAt_length]
      exact Offset.contains St (by omega_using []) (by omega_using [htl]) (by omega_using []))).mono (by simp)
  -- What the data and the schedule are, from `u` on.
  obtain dD : ∀ a k, a + k ≤ L → ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩],
      (⟨D + BitVec.ofNat 64 a, k⟩ : Region).Disjoint r := fun a k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.st_d.sub_left (Offset.sub_base St (by decide))).symm.sub_left (Offset.sub_base D hk)
    · exact hp.stk_d.symm.sub_left (Offset.sub_base D hk)
  obtain dSch : ∀ r ∈ [(⟨St + BitVec.ofNat 64 400, 16⟩ : Region), ⟨s₀.sp - 944, 944⟩], (⟨St, 384⟩ : Region).Disjoint r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.base_disjoint St (by decide) (by omega_using [])
      · exact (hp.stk_st.sub_right (Region.sub_prefix (by decide))).symm
  refine ⟨fun r hr a b d => ?_, ?_, ?_, ?_, Ful.trans Ff, ?_, ?_⟩
  · obtain ⟨-, -, -, h3, h4, h5, h6, -⟩ := preserved_ne r hr
    rw [cf.other r h6 h4 h3 h5, g₃ r h3 h4 h5, hi.keep r hr a d, he.saved r hr, hz.keep r hr a b d, hcc.keep r hr b]
  · rw [cf.rd, u₃.rd, u₂.rd, u₁.rd, hi.rd]
  · rw [cf.wr, u₃.wr, u₂.wr, u₁.wr, hi.wr]
  · rw [spf, u₃.sp, u₂.sp, u₁.sp, hi.sp]
  · have e₁ : Spec.Aes.bytesAt f.mem (St + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt l.mem (St + BitVec.ofNat 64 400) 8 := by
      obtain Fw : Frame [⟨St + BitVec.ofNat 64 408, tailOf L (8 - h)⟩] l.mem f.mem := by
        rw [cf.mem, m₃]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
      exact Proof.Cmac.bytesAt_frame Fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [htl])) (by decide)
    obtain sch : Spec.TripleDes.scheduleAt z.mem St = Spec.TripleDes.scheduleAt u.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St (Fc.trans Fz) dSch
    obtain sche : Spec.TripleDes.scheduleAt e.mem St = Spec.TripleDes.scheduleAt u.mem St :=
      Proof.TripleDes.scheduleAt_eq_of_frame St ((Fc.trans Fz).trans Fe) dSch
    obtain cvc : Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 400) 8 = Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 400) 8 := by
      obtain Fw : Frame [⟨St + BitVec.ofNat 64 (408 + h), 8 - h⟩] u.mem c.mem := by
        rw [hcc.mem, Offset.add_add]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
      exact Proof.Cmac.bytesAt_frame Fw (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [hh])) (by decide)
    obtain blkc : Spec.Aes.bytesAt c.mem (St + BitVec.ofNat 64 408) 8 =
        Spec.Aes.bytesAt u.mem (St + BitVec.ofNat 64 408) h ++ Spec.Aes.bytesAt u.mem D (8 - h) := by
      rw [hcc.mem]
      have := bytesAt_writeBytes u.mem (St + BitVec.ofNat 64 408) h (Spec.Aes.bytesAt u.mem D (8 - h))
        (by rw [Proof.Cmac.bytesAt_length]; omega_using [hh])
      rwa [Proof.Cmac.bytesAt_length, show h + (8 - h) = 8 by omega_using [hh]] at this
    rw [e₁, hi.cv, he.out, hz.out, cvc, blkc, sch, sche,
      blocksAt_frame ((Fc.trans Fz).trans Fe) (dD (8 - h) (8 * nbOf L (8 - h)) (by omega_using [hnb])) (by omega_using [hL, hnb]),
      Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [cf.mem, m₃]
    have := bytesAt_writeBytes_self l.mem (St + BitVec.ofNat 64 408)
      (xs := Spec.Aes.bytesAt l.mem (D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h))) (tailOf L (8 - h)))
      (by rw [Proof.Cmac.bytesAt_length]; omega_using [htl])
    rw [Proof.Cmac.bytesAt_length] at this
    rw [this, Proof.Cmac.bytesAt_frame Ful (dD _ _ (by omega_using [hnb])) (by omega_using [htl])]

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end


/-!
# Streaming TDEA-CMAC on RISC-V: `absorb`

The code saves the registers (`absSave_wp`), computes the number `h` of
bytes held back and whether the data fit in the `8 - h` bytes after them
(`flag_wp`); if they do, it copies them there (`Proof.CmacTripleDes.Stream.repr_fill`),
else it takes the chaining path (`chain_wp`, `repr_chain`); then it restores
the registers (`absorb_wp`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.WriteBytes (writeBytes)
open VG.Proof.CmacTripleDes.Stream (held)

/-- What the paths leave, from the state `u` after the flag: the state then
represents the message followed by the data. -/
structure PDone (s₀ : State) (St D : Addr) (n L : Nat) (u s : State) : Prop where
  keep : ∀ r ∈ preserved, r ≠ .s3 → r ≠ .s4 → r ≠ .s5 → s.gpr r = u.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem
  repr : ∀ key msg, Spec.Cmac.tdesRepr u.mem St key msg → msg.length = n →
    Spec.Cmac.tdesRepr s.mem St key (msg ++ Spec.Aes.bytesAt u.mem D L)

/-- The first 400 bytes of the state, apart from what the paths write. -/
theorem keep400 {s₀ : State} {St : Addr} {m m' : Mem}
    (hstk : (⟨s₀.sp - 944, 944⟩ : Region).Disjoint ⟨St, 416⟩)
    (hf : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] m m') :
    ∀ i < 400, m' (St + BitVec.ofNat 64 i) = m (St + BitVec.ofNat 64 i) := fun i hi =>
  hf _ fun r hr hc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint St (d := i) (n := 1) (.inl (by omega_using [hi])) (by omega_using [hi]) (by omega_using []) _
        (Region.contains_self _ _) hc
    · exact hstk _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi]))

theorem paths_wp {s₀ s₁ u : State} {St D S : Addr} {n L : Nat} (hp : APre s₀ St D S n L)
    (h₁ : AMid s₀ St D S n L s₁) (hu : AFl St D S n L s₁ u) :
    WP isa (.ite (.nonzero .t2) chainPath fillPath) u (PDone s₀ St D n L u) := by
  have hL := hp.hL
  have hw := hp.wSt
  have hwd := hp.wD
  obtain hl := Proof.CmacTripleDes.Stream.held_le n
  obtain stW : (⟨St, 416⟩ : Region) ∈ s₀.wr := by rw [hp.wr]; simp
  obtain dR : (⟨D, L⟩ : Region) ∈ s₀.rd := by rw [hp.rd]; simp
  obtain s1u : u.gpr .s1 = St := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s1]
  obtain s2u : u.gpr .s2 = S := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s2]
  obtain s3u : u.gpr .s3 = D := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s3]
  obtain a3u : u.gpr .a3 = BitVec.ofNat 64 L := by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.a3]
  obtain rdu : u.rd = s₀.rd := by rw [hu.rd, h₁.rd]
  obtain wru : u.wr = s₀.wr := by rw [hu.wr, h₁.wr]
  obtain spu : u.sp = s₀.sp := by rw [hu.sp, h₁.sp]
  obtain ev : isa.eval (.nonzero .t2) u = some (decide (8 - held n < L)) := by
    rw [eval_nonzero, hu.t2]; split <;> simp_all
  by_cases hc : 8 - held n < L
  · -- The data do not fit: chain.
    refine WP.ite true (by rw [ev]; simp [hc]) (fun _ => ?_) (fun h => by cases h)
    refine WP.mono (chain_wp hp ⟨s1u, s2u, s3u, a3u, hu.t0, hu.t1, hl, hc, rdu, wru, spu⟩) fun s hs => ?_
    refine ⟨hs.keep, hs.rd, hs.wr, hs.sp, hs.frame, fun key msg hr hn => ?_⟩
    subst hn
    have hsch : Spec.TripleDes.scheduleAt u.mem St = Spec.TripleDes.expandKey key := hr.2.1
    obtain dl : (Spec.Aes.bytesAt u.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    obtain hnb := Proof.CmacTripleDes.Stream.held_chain_pos (n := msg.length) (l := L) hc
    refine Proof.CmacTripleDes.Stream.repr_chain hr (keep400 hp.stk_st hs.frame) (by rw [dl]; exact hc) ?_ ?_
    · rw [dl, show St + 400 = St + BitVec.ofNat 64 400 from rfl, show St + 408 = St + BitVec.ofNat 64 408 from rfl,
        hs.cv, hsch, bytesAt_take u.mem D (by omega_using [hc]), bytesAt_drop_take u.mem D (by unfold Proof.CmacTripleDes.Stream.nblocks; omega_using [hc]),
        ← Proof.CmacTripleDes.Stream.blocksAt_eq]
      rfl
    · rw [dl, show St + 408 = St + BitVec.ofNat 64 408 from rfl, List.drop_drop,
        bytesAt_drop u.mem D (by unfold Proof.CmacTripleDes.Stream.nblocks; omega_using [hc])]
      have e : L - (8 - held msg.length) - 8 * Proof.CmacTripleDes.Stream.nblocks msg.length L =
          tailOf L (8 - held msg.length) := rfl
      rw [e, hs.held]
      unfold tailOf nbOf Proof.CmacTripleDes.Stream.nblocks
      congr 1; omega_using []
  · -- The data fit: copy them after the bytes held back.
    refine WP.ite false (by rw [ev]; simp [hc]) (fun h => by cases h) fun _ => ?_
    unfold fillPath toHeld mov
    refine WP.seq ?_
    refine wp_addi (imm := 408) (by decide) fun s₂ u₂ => wp_add fun s₃ u₃ => wp_mv fun s₄ u₄ =>
      wp_mv fun s₅ u₅ => WP.block_nil ?_
    obtain g₅ : ∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s₅.gpr r = u.gpr r := fun r a b c => by
      rw [u₅.other _ c, u₄.other _ b, u₃.other _ a, u₂.other _ a]
    refine WP.mono (wp_sp (copy_ok (tmp := .t6) (src := .t4) (dst := .t3) (cnt := .t5) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) s₅ (P := D)
      (C := St + BitVec.ofNat 64 408 + BitVec.ofNat 64 (held n)) (L := L) hL
      (by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), s3u])
      (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), s1u, hu.t0])
      (by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), a3u])
      (fun i hi => by
        rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rdu, wru]
        exact ⟨_, List.mem_append_left _ dR, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hL, hi])⟩)
      (fun i hi => by
        rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wru, Offset.add_add, Offset.add_add]
        exact ⟨_, stW, Offset.contains_base _ (by omega_using [hc, hi]) (by omega_using [hc, hi])⟩)
      (by
        rw [Offset.add_add]
        exact (hp.st_d.sub_left (Offset.sub_base St (by omega_using [hl, hc]))).symm))) fun s ⟨cs, sps⟩ => ?_
    obtain m₅ : s₅.mem = u.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
    obtain Fw : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] u.mem s.mem := by
      rw [cs.mem, m₅]
      exact (WriteBytes.writeBytes_frame u.mem _ _ (R := ⟨St + BitVec.ofNat 64 400, 16⟩) (by
        rw [Proof.Cmac.bytesAt_length, Offset.add_add]
        exact Offset.contains St (by omega_using []) (by omega_using [hl, hc]) (by omega_using []))).mono (by simp)
    refine ⟨fun r hr _ _ _ => ?_, by rw [cs.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rdu],
      by rw [cs.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wru], by rw [sps, u₅.sp, u₄.sp, u₃.sp, u₂.sp, spu], Fw,
      fun key msg hr hn => ?_⟩
    · obtain ⟨-, -, -, h3, h4, h5, h6, -⟩ := preserved_ne r hr
      rw [cs.other r h6 h4 h3 h5, g₅ r h3 h4 h5]
    subst hn
    obtain dl : (Spec.Aes.bytesAt u.mem D L).length = L := Proof.Cmac.bytesAt_length _ _ _
    refine Proof.CmacTripleDes.Stream.repr_fill hr (keep400 hp.stk_st Fw) (by rw [dl]; omega_using [hc]) ?_ ?_
    · rw [show St + 400 = St + BitVec.ofNat 64 400 from rfl]
      obtain Fw2 : Frame [⟨St + BitVec.ofNat 64 (408 + held msg.length), L⟩] u.mem s.mem := by
        rw [cs.mem, m₅, Offset.add_add]
        exact WriteBytes.writeBytes_frame _ _ _ (by
          rw [Proof.Cmac.bytesAt_length]; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using [])
      exact Proof.Cmac.bytesAt_frame Fw2 (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint St (.inl (by omega_using [])) (by omega_using []) (by omega_using [hl, hc])) (by decide)
    · rw [show St + 408 = St + BitVec.ofNat 64 408 from rfl, cs.mem, m₅]
      have := bytesAt_writeBytes u.mem (St + BitVec.ofNat 64 408) (held msg.length) (Spec.Aes.bytesAt u.mem D L)
        (by rw [dl]; omega_using [hl, hc])
      rw [dl] at this ⊢
      exact this


theorem absorb_wp {s₀ : State} (h0 : absorbRISCV64.pre s₀) :
    WP isa absorb s₀ fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.sp = s₀.sp ∧ absorbRISCV64.post s₀ s' := by
  obtain hp := APre.of h0
  generalize s₀.gpr .a0 = St at hp
  generalize s₀.gpr .a2 = D at hp
  generalize s₀.gpr .a4 = S at hp
  generalize (s₀.gpr .a1).toNat = n at hp
  generalize (s₀.gpr .a3).toNat = L at hp
  have hsw := hp.wS
  unfold absorb
  refine WP.seq (WP.mono (absSave_wp hp) fun s₁ h₁ => ?_)
  refine flag_wp (St := St) (D := D) (S := S) hp.hn hp.hL h₁.a1 h₁.a3 fun u hu => ?_
  refine WP.seq (WP.mono (paths_wp hp h₁ hu) fun s₂ h₂ => ?_)
  obtain s2₂ : s₂.gpr .s2 = S := by
    rw [h₂.keep _ (by decide) (by decide) (by decide) (by decide), hu.keep _ (by decide) (by decide) (by decide), h₁.s2]
  rw [restoreRegs, WP.block_append_iff]
  refine WP.mono (savePtr_ok .s2) fun s₃ e => ?_
  subst e
  rw [s2₂]
  have dSv (p : Reg × Nat) (hp' : p ∈ absSaved) (r : Region) (hr : r ∈ [⟨St + BitVec.ofNat 64 400, 16⟩,
      ⟨s₀.sp - 944, 944⟩]) : (⟨sv S + BitVec.ofNat 64 p.2, 8⟩ : Region).Disjoint r := by
    obtain hb := abs_bound p hp'
    obtain sub : Region.Sub ⟨sv S + BitVec.ofNat 64 p.2, 8⟩ ⟨S, 688⟩ := fun a ha =>
      Region.sub_prefix (by decide) a (sv_sub S (d := p.2) (n := 8) (by omega_using [hb]) a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.st_s.sub_left (Offset.sub_base St (by decide))).symm.sub_left sub
    · exact hp.stk_s.symm.sub_left sub
  obtain F₂ : Frame [⟨St + BitVec.ofNat 64 400, 16⟩, ⟨s₀.sp - 944, 944⟩] s₁.mem s₂.mem := by
    have := h₂.frame; rwa [hu.mem] at this
  obtain sv₂ : Spill.Saved (sv S) (absG s₀ S) absSaved s₂.mem := by
    obtain sv₁ : Spill.Saved (sv S) (absG s₀ S) absSaved s₁.mem := by
      rw [h₁.mem]; exact Spill.saveMem_saved (by decide) s₀.mem (sv S) _
    exact sv₁.frame F₂ fun p hp' r hr => dSv p hp' r hr
  rw [show absSaved.map (fun (r, d) => Instr.load .d r .t0 d) = Spill.restoreCode .t0 absSaved from rfl]
  refine WP.mono (Spill.restore_wp (b := .t0) (l := absSaved) (B := sv S) (Align.align_al _)
    (RegUpd.gpr_write_self _ _ _) (by decide) (by decide) (fun p hp' => ?_) sv₂) fun s₄ r₄ => ?_
  · have := abs_bound p hp'
    show InRegions (s₂.rd ++ s₂.wr) _ 8
    rw [h₂.rd, h₂.wr, hp.rd, hp.wr]
    exact ⟨⟨S, 688⟩, by simp, sv_contains S (by omega_using [this]) (by decide)⟩
  have g₀ (r : Reg) (hr : r ≠ .t0) : absG s₀ S r = s₀.gpr r := RegUpd.gpr_write_of_ne _ _ hr
  refine ⟨fun r hr => ?_, ?_, ?_, ?_⟩
  · have h0 := (preserved_ne r hr).1
    rw [r₄.gpr_of (r := r) ?_, g₀ r h0]
    by_cases hv : r = .s1 ∨ r = .s2 ∨ r = .s3 ∨ r = .s4 ∨ r = .s5
    · left; rcases hv with rfl | rfl | rfl | rfl | rfl <;> decide
    · right
      obtain ⟨-, h1, h2, -⟩ := preserved_ne r hr
      rw [RegUpd.gpr_write_of_ne _ _ h0, h₂.keep r hr (fun e => hv (.inr (.inr (.inl e))))
        (fun e => hv (.inr (.inr (.inr (.inl e))))) (fun e => hv (.inr (.inr (.inr (.inr e))))),
        hu.keep r h0 h1 h2, h₁.other r hr (fun e => hv (.inl e)) (fun e => hv (.inr (.inl e)))
          (fun e => hv (.inr (.inr (.inl e)))), g₀ r h0]
  · rw [r₄.gpr (.ra, 0) (by decide), g₀ .ra (by decide)]
  · rw [r₄.sp, RegUpd.sp_write, h₂.sp]
  · intro key msg hr ha1 hlen
    rw [hp.a0] at hr ⊢
    rw [hp.a2] at ⊢
    rw [r₄.mem, RegUpd.mem_write]
    obtain hn : n = msg.length := by
      have := congrArg BitVec.toNat (hp.a1.symm.trans ha1)
      rwa [toNat_ofNat hp.hn, toNat_ofNat (by omega_using [hlen])] at this
    obtain hL : (s₀.gpr .a3).toNat = L := by rw [hp.a3, toNat_ofNat hp.hL]
    rw [hL]
    -- The state and the data on entry, through the saves.
    obtain f₁ : Frame [⟨sv S, 48⟩] s₀.mem u.mem := by
      rw [hu.mem, h₁.mem]
      exact Spill.saveMem_frame_base (l := absSaved) (n := 48) abs_bound (by decide) s₀.mem (sv S) (absG s₀ S)
    obtain dS : Region.Sub ⟨sv S, 48⟩ ⟨S, 688⟩ := by
      have := sv_sub S (d := 0) (n := 48) (by decide)
      rw [BitVec.add_zero] at this
      exact fun a ha => Region.sub_prefix (by decide) a (this a ha)
    obtain hru : Spec.Cmac.tdesRepr u.mem St key msg :=
      Proof.CmacTripleDes.Stream.repr_congr_416 (fun i hi => f₁ _ fun r hr hc => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.st_s _ (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])) (dS _ hc)) hr
    obtain hd : Spec.Aes.bytesAt u.mem D L = Spec.Aes.bytesAt s₀.mem D L :=
      Proof.Cmac.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.d_s.sub_right dS) (by have := hp.wD; omega_using [hL])
    rw [← hd]
    exact h₂.repr key msg hru hn.symm

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end

/-!
# Streaming TDEA-CMAC on RISC-V: `absorb` in constant time

As `stream_init` (`InitCT.lean`): the code between the calls is constant
time by the taint analysis, from the registers that hold public values there
(`count`, `len`, the pointers, and what the code computes from them: the
bytes held back, the room after them, the blocks and the bytes left), pinned
by what the code before each piece leaves, and the calls by their own proof
(`ecb_rel`); the loop by `RelCT.loop`, with the blocks chained in both runs.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.CmacTripleDes.Stream.RISCV64
open VG.Proof.CmacTripleDes.Stream (held)

section
variable {s₀ s₀' : State} {St D S : Addr} {n L : Nat}

/-- What `heldCode` leaves. -/
def HH (s₀ : State) (St D S : Addr) (n L : Nat) (s : State) : Prop :=
  ∃ s₁, AMid s₀ St D S n L s₁ ∧ s.gpr .t0 = BitVec.ofNat 64 (held n) ∧ (∀ r, r ≠ .t0 → s.gpr r = s₁.gpr r) ∧
    s.mem = s₁.mem ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.sp = s₁.sp

/-- What `absFlag` leaves. -/
def HF (s₀ : State) (St D S : Addr) (n L : Nat) (s : State) : Prop :=
  ∃ s₁, AMid s₀ St D S n L s₁ ∧ AFl St D S n L s₁ s

theorem HF.cpre {s : State} (h : HF s₀ St D S n L s) (hc : 8 - held n < L) : CPre s₀ St D S (held n) L s := by
  obtain ⟨s₁, h₁, hu⟩ := h
  exact ⟨by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s1],
    by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s2],
    by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.s3],
    by rw [hu.keep _ (by decide) (by decide) (by decide), h₁.a3], hu.t0, hu.t1,
    Proof.CmacTripleDes.Stream.held_le n, hc, by rw [hu.rd, h₁.rd], by rw [hu.wr, h₁.wr], by rw [hu.sp, h₁.sp]⟩

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (St D S : Addr) (h L : Nat) (m : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, m = nbOf L (8 - h) - k ∧ k < nbOf L (8 - h) ∧ (∃ e, CInv s₀ St D S h L e k s₁) ∧
    ∃ e, CInv s₀' St D S h L e k s₂

theorem body_ct (hp : APre s₀ St D S n L) (hp' : APre s₀' St D S n L) (qsp : s₀.sp = s₀'.sp) {h : Nat}
    (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < nbOf L (8 - h) ∧ (∃ e, CInv s₀ St D S h L e k s₁) ∧
      ∃ e, CInv s₀' St D S h L e k s₂) chainBody
      fun s₁ s₂ => (∃ e, CInv s₀ St D S h L e (k + 1) s₁) ∧ ∃ e, CInv s₀' St D S h L e (k + 1) s₂ := by
  obtain ⟨_, hA⟩ : ∃ hh, (taint.check (Taint.ofRegs [.s1, .s3, .s5])
      (.block (([.addi .t3 .s1 400] : List Instr) ++ Impl.Words.RISCV64.xorBytes .t0 .t1 .t3 .s3 8 ++
        ([.addi .s3 .s3 8, .addi .s5 .s5 (-1)] : List Instr) ++ ecbArgs 400)) hh).isSome = true := ⟨_, by taint_decide⟩
  refine (RelCT.exists_ (P := fun (hk : k < nbOf L (8 - h)) s₁ s₂ =>
      (∃ e, CInv s₀ St D S h L e k s₁) ∧ ∃ e, CInv s₀' St D S h L e k s₂) fun hk => ?_).mono
    (fun _ _ h => ⟨h.1, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ (P := fun e s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ ∃ e, CInv s₀' St D S h L e k s₂)
    fun e => ?_).mono (fun _ _ h => let ⟨e, he⟩ := h.1; ⟨e, he, h.2⟩) fun _ _ h => h
  refine (RelCT.exists_ (P := fun e' s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ CInv s₀' St D S h L e' k s₂)
    fun e' => ?_).mono (fun _ _ h => let ⟨e', he'⟩ := h.2; ⟨e', h.1, he'⟩) fun _ _ h => h
  have a := (taintRegs (P := fun s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ CInv s₀' St D S h L e' k s₂) [.s1, .s3, .s5]
    (fun s₁ s₂ hh => ⟨by rw [hh.1.sp, hh.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hh.1.s1, hh.2.s1]
      · rw [hh.1.s3, hh.2.s3]
      · rw [hh.1.s5, hh.2.s5]⟩) hA).wp
    (F₁ := fun s => ∃ s₁, CInv s₀ St D S h L e k s₁ ∧ BMid s₀ St D S h L e k s₁ s)
    (F₂ := fun s => ∃ s₁, CInv s₀' St D S h L e' k s₁ ∧ BMid s₀' St D S h L e' k s₁ s)
    fun s₁ s₂ hh => ⟨WP.mono (bodyBlk_wp hp hk hh.1) fun _ b => ⟨_, hh.1, b⟩,
      WP.mono (bodyBlk_wp hp' hk hh.2) fun _ b => ⟨_, hh.2, b⟩⟩
  have c := (ecb_rel (P := fun s₁ s₂ => (∃ x, CInv s₀ St D S h L e k x ∧ BMid s₀ St D S h L e k x s₁) ∧
      ∃ x, CInv s₀' St D S h L e' k x ∧ BMid s₀' St D S h L e' k x s₂)
    fun s₁ s₂ ⟨⟨_, _, b₁⟩, ⟨_, _, b₂⟩⟩ => ⟨b₁.args, b₂.args, by rw [b₁.sp, b₂.sp, qsp]⟩)
  have whole : RelCT isa (fun s₁ s₂ => CInv s₀ St D S h L e k s₁ ∧ CInv s₀' St D S h L e' k s₂) chainBody
      fun _ _ => True :=
    (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c
  exact (whole.wp (F₁ := fun s => ∃ e, CInv s₀ St D S h L e (k + 1) s)
    (F₂ := fun s => ∃ e, CInv s₀' St D S h L e (k + 1) s)
    fun s₁ s₂ hh => ⟨WP.mono (body_ok hp hk hh.1) fun _ x => ⟨e, x⟩,
      WP.mono (body_ok hp' hk hh.2) fun _ x => ⟨e', x⟩⟩).mono (fun _ _ h => h) fun _ _ h => h.2

theorem loop_ct (hp : APre s₀ St D S n L) (hp' : APre s₀' St D S n L) (qsp : s₀.sp = s₀'.sp) {h : Nat}
    (m : Nat) :
    RelCT isa (LRel s₀ s₀' St D S h L m) (.loop chainBody (.nonzero .s5))
      fun s₁ s₂ => (∃ e, CInv s₀ St D S h L e (nbOf L (8 - h)) s₁) ∧
        ∃ e, CInv s₀' St D S h L e (nbOf L (8 - h)) s₂ := by
  have hN : nbOf L (8 - h) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega_using [this]
  refine RelCT.loop (M := isa) (LRel s₀ s₀' St D S h L) (fun m => ?_) m
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (hh : LRel s₀ s₀' St D S h L m s₁ s₂) => hh) fun _ _ h => h
  by_cases hm : m = nbOf L (8 - h) - k
  swap
  · exact RelCT.of_false fun _ _ h => hm h.1
  subst hm
  by_cases hk : k < nbOf L (8 - h)
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  refine (body_ct hp hp' qsp k).mono (fun _ _ h => h.2) fun s₁ s₂ ⟨⟨e₁, l₁⟩, ⟨e₂, l₂⟩⟩ => ?_
  have bd : nbOf L (8 - h) - (k + 1) < 2 ^ 64 := by omega_using [hN]
  have v₁ := Steps.eval_nonzero_ofNat s₁ .s5 bd l₁.s5
  have v₂ := Steps.eval_nonzero_ofNat s₂ .s5 bd l₂.s5
  refine ⟨by rw [v₁, v₂], fun hf => ?_, fun ht => ?_⟩
  · rw [v₁] at hf
    have h0 : nbOf L (8 - h) = k + 1 := by
      have : nbOf L (8 - h) - (k + 1) = 0 := by simpa using hf
      omega_using [hk, this]
    exact ⟨⟨e₁, h0 ▸ l₁⟩, ⟨e₂, h0 ▸ l₂⟩⟩
  · rw [v₁] at ht
    have h0 : nbOf L (8 - h) - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨nbOf L (8 - h) - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [h0], ⟨e₁, l₁⟩, ⟨e₂, l₂⟩⟩

end


/-! ## The chaining path -/

/-- What the block before the last copy leaves. -/
theorem tailBlk_wp {s₀ e s : State} {St D S : Addr} {h L : Nat} (hi : CInv s₀ St D S h L e (nbOf L (8 - h)) s) :
    WP isa (.block [.addi .t3 .s1 408, mov .t4 .s3, mov .t5 .s4]) s fun s' =>
      s'.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      s'.gpr .t4 = D + BitVec.ofNat 64 (8 - h + 8 * nbOf L (8 - h)) ∧
      s'.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - h)) ∧ s'.sp = s₀.sp := by
  unfold mov
  refine wp_addi (imm := 408) (by decide) fun s₁ u₁ => wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => WP.block_nil ?_
  exact ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hi.s1],
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hi.s3],
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hi.s4], by rw [u₃.sp, u₂.sp, u₁.sp, hi.sp]⟩

theorem chain_ct {s₀ s₀' : State} {St D S : Addr} {n L : Nat} (hp : APre s₀ St D S n L)
    (hp' : APre s₀' St D S n L) (qsp : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => (HF s₀ St D S n L a ∧ HF s₀' St D S n L b) ∧ isa.eval (.nonzero .t2) a = some true)
      chainPath fun _ _ => True := by
  have hN : nbOf L (8 - held n) < 2 ^ 64 := by have := hp.hL; unfold nbOf; omega_using [this]
  have hl : ∀ {a : State}, HF s₀ St D S n L a → isa.eval (.nonzero .t2) a = some true → 8 - held n < L :=
    fun {a} ⟨_, _, hu⟩ he => by
      rw [eval_nonzero, hu.t2] at he; split at he <;> simp_all
  -- The relations, by the pieces' correctness.
  obtain ⟨_, h1⟩ : ∃ hh, (taint.check (Taint.ofRegs [.a3, .t1, .s1, .t0, .s3])
      (.block (([.sub .s4 .a3 .t1] : List Instr) ++ toHeld .t1)) hh).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, h2⟩ : ∃ hh, (taint.check (Taint.ofRegs [.t3, .t4, .t5]) (copy .t6 .t4 .t3 .t5) hh).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, h3⟩ : ∃ hh, (taint.check (Taint.ofRegs [.s1, .s3, .s4, .t1]) (.block chainSetup) hh).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, h6⟩ : ∃ hh, (taint.check (Taint.ofRegs [.s1, .s3, .s4])
      (.block [.addi .t3 .s1 408, mov .t4 .s3, mov .t5 .s4]) hh).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ hh, (taint.check (Taint.ofRegs []) (.block []) hh).isSome = true := ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => (HF s₀ St D S n L a ∧ HF s₀' St D S n L b) ∧
      isa.eval (.nonzero .t2) a = some true) [.a3, .t1, .s1, .t0, .s3]
    (fun a b hh => by
      have c₁ := hh.1.1.cpre (hl hh.1.1 hh.2)
      have c₂ := hh.1.2.cpre (hl hh.1.1 hh.2)
      refine ⟨by rw [c₁.sp, c₂.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [c₁.a3, c₂.a3]
      · rw [c₁.t1, c₂.t1]
      · rw [c₁.s1, c₂.s1]
      · rw [c₁.t0, c₂.t0]
      · rw [c₁.s3, c₂.s3]) h1).wp
    (F₁ := fun s => ∃ u, CPre s₀ St D S (held n) L u ∧ C1 s₀ St D S (held n) L u s)
    (F₂ := fun s => ∃ u, CPre s₀' St D S (held n) L u ∧ C1 s₀' St D S (held n) L u s)
    fun a b hh => ⟨WP.mono (pre1_wp (hh.1.1.cpre (hl hh.1.1 hh.2))) fun _ x => ⟨_, hh.1.1.cpre (hl hh.1.1 hh.2), x⟩,
      WP.mono (pre1_wp (hh.1.2.cpre (hl hh.1.1 hh.2))) fun _ x => ⟨_, hh.1.2.cpre (hl hh.1.1 hh.2), x⟩⟩
  have b := (taintRegs (P := fun a b => (∃ u, CPre s₀ St D S (held n) L u ∧ C1 s₀ St D S (held n) L u a) ∧
      ∃ u, CPre s₀' St D S (held n) L u ∧ C1 s₀' St D S (held n) L u b) [.t3, .t4, .t5]
    (fun a b ⟨⟨_, _, x₁⟩, ⟨_, _, x₂⟩⟩ => ⟨by rw [x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [x₁.t3, x₂.t3]
      · rw [x₁.t4, x₂.t4]
      · rw [x₁.t5, x₂.t5]⟩) h2).wp
    (F₁ := fun s => ∃ u, CPre s₀ St D S (held n) L u ∧ CCopy s₀ St D S (held n) L u s)
    (F₂ := fun s => ∃ u, CPre s₀' St D S (held n) L u ∧ CCopy s₀' St D S (held n) L u s)
    fun a b ⟨⟨_, c₁, x₁⟩, ⟨_, c₂, x₂⟩⟩ => ⟨WP.mono (copy1_wp hp c₁ x₁) fun _ y => ⟨_, c₁, y⟩,
      WP.mono (copy1_wp hp' c₂ x₂) fun _ y => ⟨_, c₂, y⟩⟩
  have c := (taintRegs (P := fun a b => (∃ u, CPre s₀ St D S (held n) L u ∧ CCopy s₀ St D S (held n) L u a) ∧
      ∃ u, CPre s₀' St D S (held n) L u ∧ CCopy s₀' St D S (held n) L u b) [.s1, .s3, .s4, .t1]
    (fun a b ⟨⟨_, _, x₁⟩, ⟨_, _, x₂⟩⟩ => ⟨by rw [x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [x₁.s1, x₂.s1]
      · rw [x₁.s3, x₂.s3]
      · rw [x₁.s4, x₂.s4]
      · rw [x₁.t1, x₂.t1]⟩) h3).wp
    (F₁ := fun s => ∃ c, CSet s₀ St D S (held n) L c s) (F₂ := fun s => ∃ c, CSet s₀' St D S (held n) L c s)
    fun a b ⟨⟨_, c₁, x₁⟩, ⟨_, c₂, x₂⟩⟩ => ⟨WP.mono (setup_wp hp c₁ x₁) fun _ y => ⟨_, y⟩,
      WP.mono (setup_wp hp' c₂ x₂) fun _ y => ⟨_, y⟩⟩
  have ie {s₀ : State} {z e : State} {c : State} (hz : CSet s₀ St D S (held n) L c z) (he : EPost z St 400 e) :
      CInv s₀ St D S (held n) L e 0 e :=
    ⟨by rw [he.saved _ (by decide), hz.s1], by rw [he.saved _ (by decide), hz.s2],
      by rw [he.saved _ (by decide), hz.s3, Nat.mul_zero, Nat.add_zero], by rw [he.saved _ (by decide), hz.s4],
      by rw [he.saved _ (by decide), hz.s5, Nat.sub_zero], fun _ _ _ _ => rfl, by rw [he.rd, hz.rd],
      by rw [he.wr, hz.wr], by rw [he.sp, hz.sp], Frame.refl _ _, rfl⟩
  have d := (ecb_rel (P := fun a b => (∃ c, CSet s₀ St D S (held n) L c a) ∧ ∃ c, CSet s₀' St D S (held n) L c b)
    fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨x₁.args, x₂.args, by rw [x₁.sp, x₂.sp, qsp]⟩).wp
    (F₁ := fun s => CInv s₀ St D S (held n) L s 0 s) (F₂ := fun s => CInv s₀' St D S (held n) L s 0 s)
    fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨WP.mono (ecb_call x₁.args) fun _ y => ie x₁ y,
      WP.mono (ecb_call x₂.args) fun _ y => ie x₂ y⟩
  have ev {t e s : State} (hi : CInv t St D S (held n) L e 0 s) :
      isa.eval (.zero .s5) s = some (decide (nbOf L (8 - held n) = 0)) := by
    have := Steps.eval_zero_ofNat s .s5 (k := nbOf L (8 - held n) - 0) (by omega_using [hN]) hi.s5
    rwa [Nat.sub_zero] at this
  have e : RelCT isa (fun a b => CInv s₀ St D S (held n) L a 0 a ∧ CInv s₀' St D S (held n) L b 0 b) chainLoop
      fun a b => (∃ e, CInv s₀ St D S (held n) L e (nbOf L (8 - held n)) a) ∧
        ∃ e, CInv s₀' St D S (held n) L e (nbOf L (8 - held n)) b := by
    refine RelCT.ite (fun a b hh => by rw [ev hh.1, ev hh.2]) ?_ ?_
    · refine ((taintRegs (P := fun a b => (CInv s₀ St D S (held n) L a 0 a ∧ CInv s₀' St D S (held n) L b 0 b) ∧
          isa.eval (.zero .s5) a = some true) [] (fun _ _ hh => ⟨by rw [hh.1.1.sp, hh.1.2.sp, qsp], fun r hr => by
            simp at hr⟩) hnil).wp
        (F₁ := fun s => ∃ e, CInv s₀ St D S (held n) L e (nbOf L (8 - held n)) s)
        (F₂ := fun s => ∃ e, CInv s₀' St D S (held n) L e (nbOf L (8 - held n)) s) fun a b hh => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : nbOf L (8 - held n) = 0 := by
        have := hh.2; rw [ev hh.1.1] at this; simpa using this
      exact ⟨WP.block_nil ⟨a, h0 ▸ hh.1.1⟩, WP.block_nil ⟨b, h0 ▸ hh.1.2⟩⟩
    · refine ((loop_ct (h := held n) hp hp' qsp (nbOf L (8 - held n) - 0)).mono
        (fun a b hh => ⟨0, rfl, ?_, ⟨a, hh.1.1⟩, ⟨b, hh.1.2⟩⟩) fun _ _ h => h)
      have := hh.2; rw [ev hh.1.1] at this
      have : nbOf L (8 - held n) ≠ 0 := by simpa using this
      omega_using [this]
  have f := (taintRegs (P := fun a b => (∃ e, CInv s₀ St D S (held n) L e (nbOf L (8 - held n)) a) ∧
      ∃ e, CInv s₀' St D S (held n) L e (nbOf L (8 - held n)) b) [.s1, .s3, .s4]
    (fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨by rw [x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [x₁.s1, x₂.s1]
      · rw [x₁.s3, x₂.s3]
      · rw [x₁.s4, x₂.s4]⟩) h6).wp
    (F₁ := fun (s : State) => s.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      s.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      s.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      s.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      s.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨_, x₁⟩, ⟨_, x₂⟩⟩ => ⟨tailBlk_wp x₁, tailBlk_wp x₂⟩
  have g := taintRegs (P := fun a b => (a.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      a.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      a.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ a.sp = s₀.sp) ∧
      b.gpr .t3 = St + BitVec.ofNat 64 408 ∧
      b.gpr .t4 = D + BitVec.ofNat 64 (8 - held n + 8 * nbOf L (8 - held n)) ∧
      b.gpr .t5 = BitVec.ofNat 64 (tailOf L (8 - held n)) ∧ b.sp = s₀'.sp) [.t3, .t4, .t5]
    (fun a b hh => ⟨by rw [hh.1.2.2.2, hh.2.2.2.2, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [hh.1.1, hh.2.1]
      · rw [hh.1.2.1, hh.2.2.1]
      · rw [hh.1.2.2.1, hh.2.2.2.1]⟩) h2
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((b.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((d.mono (fun _ _ h => h) fun _ _ h => h.2).seq
      (e.seq ((f.mono (fun _ _ h => h) fun _ _ h => h.2).seq g)))))


/-! ## The whole function -/

theorem absorb_rel {s₀ s₀' : State} (h0 : absorbRISCV64.pre s₀) (h0' : absorbRISCV64.pre s₀')
    (hq : absorbRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') absorb fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, q7, qsp⟩ := hq
  have hp := APre.of h0
  have hp' : APre s₀' (s₀.gpr .a0) (s₀.gpr .a2) (s₀.gpr .a4) (s₀.gpr .a1).toNat (s₀.gpr .a3).toNat := by
    rw [q3, q4, q5, q6, q7]; exact APre.of h0'
  generalize s₀.gpr .a0 = St at hp hp'
  generalize s₀.gpr .a2 = D at hp hp'
  generalize s₀.gpr .a4 = S at hp hp'
  generalize (s₀.gpr .a1).toNat = n at hp hp'
  generalize (s₀.gpr .a3).toNat = L at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4]) (.block absSave) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.a1]) heldCode h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.t0, .a3]) (.block absFlag) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hF⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .t0, .s3, .a3]) fillPath h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hE⟩ : ∃ h, (taint.check (Taint.ofRegs [.s2]) (.block (restoreRegs absSaved)) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := AMid s₀ St D S n L) (F₂ := AMid s₀' St D S n L) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨absSave_wp hp, absSave_wp hp'⟩
  have b := (taintRegs (P := fun a b => AMid s₀ St D S n L a ∧ AMid s₀' St D S n L b) [.a1]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h.1.a1, h.2.a1]⟩) hB).wp
    (F₁ := HH s₀ St D S n L) (F₂ := HH s₀' St D S n L) fun a b h =>
      ⟨WP.mono (heldCode_wp hp.hn h.1.a1) fun _ ⟨t0, g, m, rd, wr, sp⟩ => ⟨a, h.1, t0, g, m, rd, wr, sp⟩,
       WP.mono (heldCode_wp hp.hn h.2.a1) fun _ ⟨t0, g, m, rd, wr, sp⟩ => ⟨b, h.2, t0, g, m, rd, wr, sp⟩⟩
  have c := (taintRegs (P := fun a b => HH s₀ St D S n L a ∧ HH s₀' St D S n L b) [.t0, .a3]
    (fun a b ⟨⟨_, x₁, t₁, g₁, _, _, _, sp₁⟩, ⟨_, x₂, t₂, g₂, _, _, _, sp₂⟩⟩ =>
      ⟨by rw [sp₁, sp₂, x₁.sp, x₂.sp, qsp], fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [t₁, t₂]
        · rw [g₁ _ (by decide), g₂ _ (by decide), x₁.a3, x₂.a3]⟩) hC).wp
    (F₁ := HF s₀ St D S n L) (F₂ := HF s₀' St D S n L)
    fun a b ⟨⟨s₁, x₁, t₁, g₁, m₁, rd₁, wr₁, sp₁⟩, ⟨s₂, x₂, t₂, g₂, m₂, rd₂, wr₂, sp₂⟩⟩ =>
      ⟨WP.mono (absFlag_wp hp.hL x₁.a3 t₁ g₁ m₁ rd₁ wr₁ sp₁) fun _ y => ⟨s₁, x₁, y⟩,
       WP.mono (absFlag_wp hp.hL x₂.a3 t₂ g₂ m₂ rd₂ wr₂ sp₂) fun _ y => ⟨s₂, x₂, y⟩⟩
  have t2eq : ∀ {t : State} {s : State}, HF t St D S n L s → s.gpr .t2 = if 8 - held n < L then 1 else 0 :=
    fun {_ _} ⟨_, _, hu⟩ => hu.t2
  have fill := taintRegs (P := fun a b => (HF s₀ St D S n L a ∧ HF s₀' St D S n L b) ∧
      isa.eval (.nonzero .t2) a = some false) [.s1, .t0, .s3, .a3]
    (fun a b ⟨⟨⟨_, x₁, y₁⟩, ⟨_, x₂, y₂⟩⟩, _⟩ => ⟨by rw [y₁.sp, y₂.sp, x₁.sp, x₂.sp, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [y₁.keep _ (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide), x₁.s1, x₂.s1]
      · rw [y₁.t0, y₂.t0]
      · rw [y₁.keep _ (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide), x₁.s3, x₂.s3]
      · rw [y₁.keep _ (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide), x₁.a3,
          x₂.a3]⟩) hF
  have d : RelCT isa (fun a b => HF s₀ St D S n L a ∧ HF s₀' St D S n L b) (.ite (.nonzero .t2) chainPath fillPath)
      fun _ _ => True :=
    RelCT.ite (fun a b h => by rw [eval_nonzero, eval_nonzero, t2eq h.1, t2eq h.2]) (chain_ct hp hp' qsp) fill
  have d' := d.wp (F₁ := fun (s : State) => s.gpr .s2 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s2 = S ∧ s.sp = s₀'.sp)
    fun a b ⟨⟨s₁, x₁, y₁⟩, ⟨s₂, x₂, y₂⟩⟩ =>
      ⟨WP.mono (paths_wp hp x₁ y₁) fun _ z => ⟨by
          rw [z.keep _ (by decide) (by decide) (by decide) (by decide), y₁.keep _ (by decide) (by decide) (by decide),
            x₁.s2], z.sp⟩,
       WP.mono (paths_wp hp' x₂ y₂) fun _ z => ⟨by
          rw [z.keep _ (by decide) (by decide) (by decide) (by decide), y₂.keep _ (by decide) (by decide) (by decide),
            x₂.s2], z.sp⟩⟩
  have e := taintRegs (P := fun a b => (a.gpr .s2 = S ∧ a.sp = s₀.sp) ∧ b.gpr .s2 = S ∧ b.sp = s₀'.sp) [.s2]
    (fun a b h => ⟨by rw [h.1.2, h.2.2, qsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr; rw [h.1.1, h.2.1]⟩) hE
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((b.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((d'.mono (fun _ _ h => h) fun _ _ h => h.2).seq e)))

theorem absorb_ct : ConstantTime isa absorbRISCV64.pre absorbRISCV64.pub absorb :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (absorb_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end

/-! ### `CmacTripleDes.Stream.RISCV64.Verified`, which only this module used -/

section

/-!
# Streaming TDEA-CMAC on RISC-V: `Verified`

The contracts the proofs are written against (`initRISCV64`,
`absorbRISCV64`, `finishRISCV64`, `Common.lean`), with the working space as
the last argument, which the shared contracts with the working space as an
argument (`Proof/CmacTripleDes/StreamScratch.lean`) imply, with the 944
bytes of stack below the stack pointer that ECB's frame uses: the functions
keep the return address in the working space, and their calls store nothing
in memory.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacTripleDes.Stream.RISCV64

theorem init_correct (s : State) (hs : initRISCV64.pre s) :
    ∃ t s', Exec isa streamInit s t s' ∧ abiPreserved s s' ∧ initRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := init_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem absorb_correct (s : State) (hs : absorbRISCV64.pre s) :
    ∃ t s', Exec isa absorb s t s' ∧ abiPreserved s s' ∧ absorbRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := absorb_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

theorem finish_correct (s : State) (hs : finishRISCV64.pre s) :
    ∃ t s', Exec isa finish s t s' ∧ abiPreserved s s' ∧ finishRISCV64.post s s' := by
  obtain ⟨t, s', he, hg, hra, hsp, hp⟩ := finish_wp hs
  exact ⟨t, s', he, ⟨hg, hsp, hra⟩, hp⟩

/-! ## The contracts -/

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition. -/
def initSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x3000 | .a2 => 16 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 16⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 640⟩]

theorem init_implies : initRISCV64.Implies (streamInitScratchContract RISCV64.abi 944) := by
  sig_implies [streamInitScratchContract, streamInitScratchSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, initRISCV64, RISCV64.abi, RISCV64.argRegs] [initSat] using initSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition (with no data). -/
def absorbSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x3000 | .a4 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x3000, 0⟩]
  wr := [⟨0x1000, 416⟩, ⟨0x4000, 688⟩]

theorem absorb_implies : absorbRISCV64.Implies (absorbScratchContract RISCV64.abi 944) := by
  sig_implies [absorbScratchContract, absorbScratchSig, Spec.Cmac.tdesAbsorbPost, absorbRISCV64,
    RISCV64.abi, RISCV64.argRegs] [absorbSat] using absorbSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition. -/
def finishSat : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a2 => 0x2000 | .a3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩, ⟨0x4000, 640⟩]

theorem finish_implies : finishRISCV64.Implies (finishScratchContract RISCV64.abi 944) := by
  sig_implies [finishScratchContract, finishScratchSig, Spec.Cmac.tdesFinishPost, finishRISCV64,
    RISCV64.abi, RISCV64.argRegs] [finishSat] using finishSat

theorem init_verified : Verified RISCV64.target streamInit (streamInitScratchContract RISCV64.abi 944) :=
  Verified.of_correct init_correct init_ct init_implies

theorem absorb_verified : Verified RISCV64.target absorb (absorbScratchContract RISCV64.abi 944) :=
  Verified.of_correct absorb_correct absorb_ct absorb_implies

theorem finish_verified : Verified RISCV64.target finish (finishScratchContract RISCV64.abi 944) :=
  Verified.of_correct finish_correct finish_ct finish_implies

end VG.Proof.CmacTripleDes.Stream.RISCV64

end

end


/-!
# Streaming TDEA-CMAC on RISC-V, with its working space on the stack

The streaming functions run their code, proved with the working space as an
argument and the 944 bytes of stack below it that ECB uses (`Verified.lean`),
in a frame that allocates the working space (`Verified.stackScratchL`): 640
bytes for `stream_init` and `finish`, 688 for `absorb`, so 1584 and 1632
bytes of stack in all.
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacTripleDes.Stream.RISCV64

/-- A state satisfying `vg_cmac_triple_des_stream_init`'s precondition,
without the working space. -/
def initFrameSat : State := { initSat with wr := [⟨0x1000, 416⟩] }

theorem initFrameSat_pre : ∃ s, (Spec.Cmac.tdesStreamInitContract RISCV64.abi 1584).pre s := by
  implies_sat [Spec.Cmac.tdesStreamInitContract, Spec.Cmac.tdesStreamInitSig, Spec.Cmac.tdesStreamInitPre,
    Spec.Cmac.tdesStreamInitPost, RISCV64.abi, RISCV64.argRegs] [initFrameSat, initSat] using initFrameSat

/-- A state satisfying `vg_cmac_triple_des_absorb`'s precondition, without
the working space (and with no data). -/
def absorbFrameSat : State := { absorbSat with wr := [⟨0x1000, 416⟩] }

theorem absorbFrameSat_pre : ∃ s, (Spec.Cmac.tdesAbsorbContract RISCV64.abi 1632).pre s := by
  implies_sat [Spec.Cmac.tdesAbsorbContract, Spec.Cmac.tdesAbsorbSig, Spec.Cmac.tdesAbsorbPost,
    RISCV64.abi, RISCV64.argRegs] [absorbFrameSat, absorbSat] using absorbFrameSat

/-- A state satisfying `vg_cmac_triple_des_finish`'s precondition, without
the working space. -/
def finishFrameSat : State := { finishSat with wr := [⟨0x1000, 416⟩, ⟨0x2000, 8⟩] }

theorem finishFrameSat_pre : ∃ s, (Spec.Cmac.tdesFinishContract RISCV64.abi 1584).pre s := by
  implies_sat [Spec.Cmac.tdesFinishContract, Spec.Cmac.tdesFinishSig, Spec.Cmac.tdesFinishPost,
    RISCV64.abi, RISCV64.argRegs] [finishFrameSat, finishSat] using finishFrameSat

theorem init_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 640 .a3 streamInit)
      (Spec.Cmac.tdesStreamInitContract RISCV64.abi 1584) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.tdesStreamInitSig) (nm := "scratch") (e := .u64)
    (n := 80) (pre := Spec.Cmac.tdesStreamInitPre RISCV64.abi.ptrBits)
    (post := Spec.Cmac.tdesStreamInitPost RISCV64.abi.ptrBits) (wa := false) (stack := 944)
    (bytes := 640) init_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacTripleDes.Stream.streamInitPostOut_local _ vs m m₁ m₂ r hl)
    initFrameSat_pre

theorem absorb_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 688 .a4 absorb)
      (Spec.Cmac.tdesAbsorbContract RISCV64.abi 1632) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.tdesAbsorbSig) (nm := "scratch") (e := .u64)
    (n := 86) (post := Spec.Cmac.tdesAbsorbPost RISCV64.abi.ptrBits) (wa := false) (stack := 944)
    (bytes := 688) absorb_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacTripleDes.Stream.absorbPostOut_local _ vs m m₁ m₂ r hl)
    absorbFrameSat_pre

theorem finish_framed :
    Verified RISCV64.target (Impl.StackScratch.RISCV64.withStackScratch 640 .a3 finish)
      (Spec.Cmac.tdesFinishContract RISCV64.abi 1584) :=
  RISCV64.Verified.stackScratchL (sig := Spec.Cmac.tdesFinishSig) (nm := "scratch") (e := .u64)
    (n := 80) (post := Spec.Cmac.tdesFinishPost RISCV64.abi.ptrBits) (wa := false) (stack := 944)
    (bytes := 640) finish_verified (by decide) (by decide)
    (fun vs m m₁ m₂ r hl _ => Proof.CmacTripleDes.Stream.finishPostOut_local _ vs m m₁ m₂ r hl)
    finishFrameSat_pre

end VG.Proof.CmacTripleDes.Stream.RISCV64
