module

public import VerifiedGarbage.Proof.AesCfb8.RISCV64.Body
import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.AesCfb8.RISCV64.Lit
import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified
meta import VerifiedGarbage.Proof.AesCfb8.RISCV64.Body
meta import VerifiedGarbage.Proof.AesCbc.RISCV64.CT
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.AesCfb8.RISCV64.Lit
meta import VerifiedGarbage.Proof.Aes.RISCV64.BlocksVerified

/-!
# AES-CFB8 on RISC-V: constant time

As AES-CBC's (`Proof/AesCbc/RISCV64/CT.lean`), for the byte loop, as on
PPC64LE (`Proof/AesCfb8/PPC64LE/CT.lean`): two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from the registers the
correctness proof pins to the public arguments and the stack pointer, and
each call of the block function, on the copy of the input block, is
constant time by its own proof (`blk_rel`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.RISCV64

open VG VG.RISCV64 VG.Impl.AesCbc.RISCV64 VG.Impl.AesCfb8.RISCV64
open VG.Proof.AesCbc.RISCV64 (W R Iv Dp N S sv vars taintRegs blk_rel blk_call CallPost
  encryptBlocks_noFrames prologue_taint epilogue_taint nil_taint)

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (cfb8RISCV64 enc).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_a1 : s₀.gpr .a1 = s₀'.gpr .a1 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_a1 hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem pub_byt (k : Nat) : byt s₀ k = byt s₀' k := by rw [byt, byt, pub_Dp hq]
theorem pub_sv : sv s₀ = sv s₀' := by
  simp only [sv, AesCbc.RISCV64.q, pub_S hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv enc s₀ k s₁) (h₂ : LInv enc s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.s1, h₂.s1, pub_W hq]
  · rw [h₁.s2, h₂.s2, pub_a1 hq]
  · rw [h₁.s3, h₂.s3, pub_Iv hq]
  · rw [h₁.s4, h₂.s4, pub_byt hq]
  · rw [h₁.s5, h₂.s5, pub_N hq]
  · rw [h₁.s6, h₂.s6, pub_S hq]

end

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : AesCbc.RISCV64.CallPre s (W s₀) (sv s₀) (S s₀) (R s₀)
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = byt s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  s3 : s.gpr .s3 = Iv s₀
  s4 : s.gpr .s4 = byt s₀ k
  s5 : s.gpr .s5 = BitVec.ofNat 64 (N s₀ - k)
  s6 : s.gpr .s6 = S s₀
  sp : s.sp = s₀.sp

theorem Mid.of {enc : Bool} {s₀ : State} {k : Nat} {s s₁ : State} (h : LInv enc s₀ k s)
    (a : PreA s₀ s s₁) : Mid s₀ k s₁ :=
  ⟨a.pre, by rw [a.saved .s3 (by decide), h.s3], by rw [a.saved .s4 (by decide), h.s4],
    by rw [a.saved .s5 (by decide), h.s5], by rw [a.saved .s6 (by decide), h.s6], a.sp.trans h.sp⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat}
    {s s' : State} (h : Mid s₀ k s) (hc : CallPost f s (W s₀) (sv s₀) (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .s3 (by decide), h.s3], by rw [hc.saved .s4 (by decide), h.s4],
    by rw [hc.saved .s5 (by decide), h.s5], by rw [hc.saved .s6 (by decide), h.s6],
    hc.sp.trans h.sp⟩

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block encPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block decPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- One byte, in two runs: the code before the call, the call on the copy
of the input block, and `post`. -/
theorem body_ct {enc : Bool} {post : List Instr}
    (hB : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block post) h).isSome = true)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8RISCV64 enc).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) (body post)
      fun _ _ => True := by
  obtain ⟨_, hA⟩ := pre_taint
  obtain ⟨_, hB⟩ := hB
  have a := (taintRegs (P := fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.sp, h.2.2.sp, pub_sp hq], LInv.agree hq h.2.1 h.2.2⟩) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨WP.mono (pre_wp hp h.2.1) fun _ a => Mid.of h.2.1 a,
       WP.mono (pre_wp hp' h.2.2) fun _ a => Mid.of h.2.2 a⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
    Proof.Aes.RISCV64.encryptBlocks_ct (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pub_sv hq, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
          encryptBlocks_noFrames h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.RISCV64.encryptBlocks_correct
          encryptBlocks_noFrames h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := taintRegs (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) [.s3, .s4, .s5, .s6]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.s3, h.2.s3, pub_Iv hq]
      · rw [h.1.s4, h.2.s4, pub_byt hq]
      · rw [h.1.s5, h.2.s5, pub_N hq]
      · rw [h.1.s6, h.2.s6, pub_S hq]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (enc : Bool) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂

theorem loop_ct {enc : Bool} {post : List Instr} (hb : BodyOk enc (body post))
    (hB : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block post) h).isSome = true)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8RISCV64 enc).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel enc s₀ s₀' n) (.loop (body post) (.nonzero .s5))
      fun s₁ s₂ => LInv enc s₀ (N s₀) s₁ ∧ LInv enc s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel enc s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .a4).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel enc s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (body_ct hB hp hp' hq k).wp (F₁ := LInv enc s₀ (k + 1)) (F₂ := LInv enc s₀' (k + 1))
    fun _ _ h => ⟨hb hp h.1 h.2.1, hb hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have bd : N s₀ - (k + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := Steps.eval_nonzero_ofNat s₁ .s5 bd l₁.s5
  have e₂ := Steps.eval_nonzero_ofNat s₂ .s5 (k := N s₀ - (k + 1)) bd (by rw [l₂.s5, hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

/-! ## The whole function -/

theorem whole_rel {enc : Bool} {post : List Instr} (hb : BodyOk enc (body post))
    (hB : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block post) h).isSome = true)
    {s₀ s₀' : State} (h0 : (cfb8RISCV64 enc).pre s₀) (h0' : (cfb8RISCV64 enc).pre s₀')
    (hq : (cfb8RISCV64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole (body post)) fun _ _ => True := by
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
    (F₁ := LInv enc s₀ 0) (F₂ := LInv enc s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {t : State} {s : State} (h : LInv enc t 0 s) : isa.eval (.zero .s5) s = some (decide (N t = 0)) := by
    have := Steps.eval_zero_ofNat s .s5 (k := N t - 0)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .a4).isLt) h.s5
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (LInv enc s₀ 0 a ∧ LInv enc s₀' 0 b) ∧
      isa.eval (.zero .s5) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.sp, h.1.2.sp, pub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => LInv enc s₀ 0 a ∧ LInv enc s₀' 0 b)
      (.ite (.zero .s5) (.block []) (.loop (body post) (.nonzero .s5)))
      (fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := LInv enc s₀ (N s₀)) (F₂ := LInv enc s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · have lp : ∀ hn : 0 < N s₀, RelCT isa (fun a b => LInv enc s₀ 0 a ∧ LInv enc s₀' 0 b)
          (.loop (body post) (.nonzero .s5)) (fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) :=
        fun hn => (loop_ct hb hB hp hp' hq (N s₀ - 0)).mono
          (fun _ _ (h : LInv enc s₀ 0 _ ∧ LInv enc s₀' 0 _) => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h
      refine (RelCT.exists_ lp).mono (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := taintRegs (P := fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) [.s6]
    (fun a b h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.s6, h.2.s6, pub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_ct {enc : Bool} {post : List Instr} (hb : BodyOk enc (body post))
    (hB : ∃ h, (taint.check (Taint.ofRegs [.s3, .s4, .s5, .s6]) (.block post) h).isSome = true) :
    ConstantTime isa (cfb8RISCV64 enc).pre (cfb8RISCV64 enc).pub (whole (body post)) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hB h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCfb8.RISCV64
