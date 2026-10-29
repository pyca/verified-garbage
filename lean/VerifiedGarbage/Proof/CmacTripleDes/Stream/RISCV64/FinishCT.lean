module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Finish
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.InitCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Finish
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls

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
