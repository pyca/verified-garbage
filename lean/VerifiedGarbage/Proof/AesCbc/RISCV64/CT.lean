module

public import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Framework.RISCV64.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.Body
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified

/-!
# AES-CBC on RISC-V: constant time

As on PPC64LE (`Proof/AesCbc/PPC64LE/CT.lean`): two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proof pins to the public arguments (`LInv`) and the stack
pointer, and each call of a block function is constant time by its own
proof (`blk_rel`). (The taint analysis alone cannot see through the calls:
the block functions reload the callee-saved registers from memory, which it
counts as secret.) What AES-CTR's, CMAC's and AES-SIV's proofs share:
`blk_rel`, `taintRegs`, `wp_sp`, the public arguments of the two runs, and
`ends_rel`, `whole`'s code around its loop.
-/

@[expose] public section

namespace VG.Proof.AesCbc.RISCV64

open VG VG.RISCV64 VG.Impl.AesCbc.RISCV64

/-- Calls of a block function on one block, with the same arguments in both
runs, are constant time. -/
theorem blk_rel {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {name : String} {c : Prog isa}
    (ok : ∀ s, (Proof.Aes.blocksRISCV64 f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksRISCV64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksRISCV64 f).pre (Proof.Aes.blocksRISCV64 f).pub c)
    {P : State → State → Prop} {W D S : Addr} {R : Nat}
    (h : ∀ s₁ s₂, P s₁ s₂ → CallPre s₁ W D S R ∧ CallPre s₂ W D S R ∧ s₁.sp = s₂.sp) :
    RelCT isa P (.call name c) fun _ _ => True := by
  refine RelCT.call ok ct [⟨W, 240⟩] [⟨D, 16⟩, ⟨S, 2048⟩] fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, hsp⟩ := h s₁ s₂ hp
  refine ⟨h₁.blk_pre, h₂.blk_pre, ?_, h₁.reads, h₁.writes, h₂.reads, h₂.writes⟩
  simp only [Proof.Aes.blocksRISCV64, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.a0 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a2 ∉ linkRegs), State.callEntry_gpr _ (by decide : Reg.a3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.a4 ∉ linkRegs),
    h₁.a0, h₁.a1, h₁.a2, h₁.a3, h₁.a4, h₂.a0, h₂.a1, h₂.a2, h₂.a3, h₂.a4, hsp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- Code the taint analysis proves constant time from the registers `rs`
(and the stack pointer). -/
theorem taintRegs {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    (hr : ∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ rs, x.gpr r = y.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs)
    (fun x y hp => ⟨(hr x y hp).1, fun r h' => (hr x y hp).2 r (Taint.mem_ofRegs.mp h')⟩) h

/-- Code keeps the stack pointer. -/
theorem wp_sp {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) :
    WP isa c s fun s' => Q s' ∧ s'.sp = s.sp := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.sp he⟩

section
variable {M : Mode} {s₀ s₀' : State} (hq : (modeRISCV64 M).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_a1 : s₀.gpr .a1 = s₀'.gpr .a1 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_a1 hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem pub_blk (k : Nat) : blk s₀ k = blk s₀' k := by rw [blk, blk, pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv M s₀ k s₁) (h₂ : LInv M s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.s1, h₂.s1, pub_W hq]
  · rw [h₁.s2, h₂.s2, pub_a1 hq]
  · rw [h₁.s3, h₂.s3, pub_Iv hq]
  · rw [h₁.s4, h₂.s4, pub_blk hq]
  · rw [h₁.s5, h₂.s5, pub_N hq]
  · rw [h₁.s6, h₂.s6, pub_S hq]

end

/-! ## The code around the loop -/

theorem prologue_taint : ∃ h, (taint.check (Taint.ofRegs [.a0, .a1, .a2, .a3, .a4, .a5])
    (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩

theorem epilogue_taint : ∃ h, (taint.check (Taint.ofRegs [.s6]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The registers saved and the arguments set up, `mid` run unless there are
no blocks, and the registers restored, constant time when two runs of `mid`
from the invariant after no blocks are (AES-CTR's loop). -/
theorem ends_rel {M : Mode} {mid : Prog isa}
    {s₀ s₀' : State} (h0 : (modeRISCV64 M).pre s₀) (h0' : (modeRISCV64 M).pre s₀')
    (hq : (modeRISCV64 M).pub s₀ s₀')
    (hm : UPre s₀ → UPre s₀' → 0 < N s₀ →
      RelCT isa (fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) mid
        fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (save ++ setup)) (.seq (.ite (.zero .s5) (.block []) mid) (.block restore)))
      fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  obtain ⟨_, hpro⟩ := prologue_taint
  obtain ⟨_, hepi⟩ := epilogue_taint
  obtain ⟨_, hnil⟩ := nil_taint
  have pro := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.a0, .a1, .a2, .a3, .a4, .a5]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨pub_sp hq, fun r hr => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [h1, h2, h3, h4, h5, h6]) hpro).wp
    (F₁ := LInv M s₀ 0) (F₂ := LInv M s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {t : State} {s : State} (h : LInv M t 0 s) : isa.eval (.zero .s5) s = some (decide (N t = 0)) := by
    have := Steps.eval_zero_ofNat s .s5 (k := N t - 0)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .a4).isLt) h.s5
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (LInv M s₀ 0 a ∧ LInv M s₀' 0 b) ∧
      isa.eval (.zero .s5) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.sp, h.1.2.sp, pub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => LInv M s₀ 0 a ∧ LInv M s₀' 0 b) (.ite (.zero .s5) (.block []) mid)
      (fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := LInv M s₀ (N s₀)) (F₂ := LInv M s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (RelCT.exists_ fun (hn : 0 < N s₀) => hm hp hp' hn).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := taintRegs (P := fun a b => LInv M s₀ (N s₀) a ∧ LInv M s₀' (N s₀') b) [.s6]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.s6, h.2.s6, pub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

end VG.Proof.AesCbc.RISCV64
