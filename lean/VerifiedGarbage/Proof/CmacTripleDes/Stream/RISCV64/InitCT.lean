module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Init
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Init
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls
meta import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Calls

/-!
# Streaming TDEA-CMAC on RISC-V: `stream_init` in constant time

The code between the calls is constant time by the taint analysis
(`taintRegs`), from the registers that hold public values there, and the
calls by their own proofs (`key_rel`, `ecb_rel`), their arguments pinned by
what the code before them leaves (`IMid₁`, `IAfter`, `IZero`).
-/

@[expose] public section

namespace VG.Proof.CmacTripleDes.Stream.RISCV64

open VG VG.RISCV64 VG.Impl.CmacTripleDes.Stream.RISCV64

/-- Code the taint analysis proves constant time from the registers `rs`
(and the stack pointer). -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h' => (hr x y hp).2 r (Taint.mem_ofRegs.mp h')⟩) h

/-- What the key expansion's call leaves, for `initZero`. -/
structure IAfter (s₀ : State) (St S : Addr) (s : State) : Prop where
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem key_after {s₀ s : State} {St Kp S : Addr} {KL : Nat} (h : IMid₁ s₀ St Kp S KL s) :
    WP isa keyCall s (IAfter s₀ St S) :=
  WP.mono (key_call h.args) fun _ h₂ =>
    ⟨by rw [h₂.saved _ (by decide), h.s1], by rw [h₂.saved _ (by decide), h.s2], by rw [h₂.wr, h.wr],
      by rw [h₂.sp, h.sp]⟩

/-- What `initZero` leaves, for ECB's call. -/
structure IZero (s₀ : State) (St S : Addr) (s : State) : Prop where
  args : EArgs s St 384
  s1 : s.gpr .s1 = St
  s2 : s.gpr .s2 = S
  sp : s.sp = s₀.sp

theorem zero_after {s₀ s : State} {St Kp S : Addr} {KL : Nat} (hp : IPre s₀ St Kp S KL)
    (h : IAfter s₀ St S s) : WP isa (.block initZero) s (IZero s₀ St S) := by
  have stW : (⟨St, 416⟩ : Region) ∈ s.wr := by rw [h.wr, hp.wr]; simp
  refine WP.mono (initZero_wp h.s1 stW) fun s' h' => ?_
  obtain ⟨a0, a1, a2, g, -, -, -, wr, sp⟩ := h'
  have sp' : s'.sp = s₀.sp := by rw [sp, h.sp]
  exact ⟨⟨a0, a1, a2, by decide, by decide, hp.wSt, by rw [sp']; exact hp.al, by rw [sp']; exact hp.sp,
    by rw [sp']; exact hp.stk_st, by rw [wr]; exact stW⟩, by rw [g _ (by decide), h.s1],
    by rw [g _ (by decide), h.s2], sp'⟩

theorem init_rel {s₀ s₀' : State} (h0 : initRISCV64.pre s₀) (h0' : initRISCV64.pre s₀')
    (hq : initRISCV64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') streamInit fun _ _ => True := by
  obtain ⟨q3, q4, q5, q6, qsp⟩ := hq
  have hp := IPre.of h0
  have hp' : IPre s₀' (s₀.gpr .a0) (s₀.gpr .a1) (s₀.gpr .a3) (s₀.gpr .a2).toNat := by
    rw [q3, q4, q5, q6]; exact IPre.of h0'
  generalize s₀.gpr .a0 = St at hp hp'
  generalize s₀.gpr .a1 = Kp at hp hp'
  generalize s₀.gpr .a3 = S at hp hp'
  generalize (s₀.gpr .a2).toNat = KL at hp hp'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3]) (.block initSave) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2]) (.block initZero) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hC⟩ : ∃ h, (taint.check (Taint.ofRegs [.s1, .s2]) (.block initTail) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨qsp, fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := IMid₁ s₀ St Kp S KL) (F₂ := IMid₁ s₀' St Kp S KL) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨initSave_wp hp, initSave_wp hp'⟩
  have e := (key_rel (P := fun a b => IMid₁ s₀ St Kp S KL a ∧ IMid₁ s₀' St Kp S KL b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := IAfter s₀ St S) (F₂ := IAfter s₀' St S) fun a b h => ⟨key_after h.1, key_after h.2⟩
  have z := (taintRegs (P := fun a b => IAfter s₀ St S a ∧ IAfter s₀' St S b) [.s1, .s2]
    (fun a b h => by
      refine ⟨by rw [h.1.sp, h.2.sp, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.s1, h.2.s1]
      · rw [h.1.s2, h.2.s2]) hB).wp
    (F₁ := IZero s₀ St S) (F₂ := IZero s₀' St S) fun a b h => ⟨zero_after hp h.1, zero_after hp' h.2⟩
  have c := (ecb_rel (P := fun a b => IZero s₀ St S a ∧ IZero s₀' St S b)
    fun a b h => ⟨h.1.args, h.2.args, by rw [h.1.sp, h.2.sp, qsp]⟩).wp
    (F₁ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.sp = s₀.sp)
    (F₂ := fun (s : State) => s.gpr .s1 = St ∧ s.gpr .s2 = S ∧ s.sp = s₀'.sp)
    fun a b h => ⟨WP.mono (ecb_call h.1.args) fun _ e => ⟨by rw [e.saved _ (by decide), h.1.s1],
        by rw [e.saved _ (by decide), h.1.s2], by rw [e.sp, h.1.sp]⟩,
      WP.mono (ecb_call h.2.args) fun _ e => ⟨by rw [e.saved _ (by decide), h.2.s1],
        by rw [e.saved _ (by decide), h.2.s2], by rw [e.sp, h.2.sp]⟩⟩
  have p := taintRegs
    (P := fun a b => (a.gpr .s1 = St ∧ a.gpr .s2 = S ∧ a.sp = s₀.sp) ∧
      b.gpr .s1 = St ∧ b.gpr .s2 = S ∧ b.sp = s₀'.sp) [.s1, .s2]
    (fun a b h => by
      refine ⟨by rw [h.1.2.2, h.2.2.2, qsp], fun r hr => ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2.1, h.2.2.1]) hC
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((e.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((z.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq p)))

theorem init_ct : ConstantTime isa initRISCV64.pre initRISCV64.pub streamInit :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (init_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacTripleDes.Stream.RISCV64
