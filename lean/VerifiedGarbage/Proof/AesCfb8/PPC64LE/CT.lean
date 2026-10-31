module

public import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Body
import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.AesCfb8.PPC64LE.Body
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.CT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-CFB8 on PPC64LE: constant time

As AES-CBC's (`Proof/AesCbc/PPC64LE/CT.lean`), for the byte loop: two runs
from states that agree on the public arguments are related piece by piece
(`RelCT`): the taint analysis covers the code between the calls, from the
registers the correctness proof pins to the public arguments and the stack
pointer (`LS`), and each call of the block function, on the copy of the
input block, is constant time by its own proof (`blk_rel`).
-/

@[expose] public section

namespace VG.Proof.AesCfb8.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE VG.Impl.AesCfb8.PPC64LE
open VG.Proof.AesCbc.PPC64LE (W R Iv Dp N S vars Sv taintRegs wp_sp blk_rel blk_call CallPost
  encryptBlocks_noFrames prologue_taint epilogue_taint nil_taint)

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (cfb8PPC64LE enc).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_r4 : s₀.gpr .r4 = s₀'.gpr .r4 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r4 hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem pub_byt (k : Nat) : byt s₀ k = byt s₀' k := by rw [byt, byt, pub_Dp hq]
theorem pub_Sv : Sv s₀ = Sv s₀' := by rw [Sv, Sv, pub_S hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv enc s₀ k s₁) (h₂ : LInv enc s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r14, h₂.r14, pub_W hq]
  · rw [h₁.r15, h₂.r15, pub_r4 hq]
  · rw [h₁.r16, h₂.r16, pub_Iv hq]
  · rw [h₁.r17, h₂.r17, pub_byt hq]
  · rw [h₁.r18, h₂.r18, pub_N hq]
  · rw [h₁.r19, h₂.r19, pub_S hq]

end

/-- The invariant, and the stack pointer on entry. -/
def LS (enc : Bool) (s₀ : State) (k : Nat) (s : State) : Prop := LInv enc s₀ k s ∧ s.sp = s₀.sp

theorem bodyS {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LS enc s₀ k s) : WP isa body s (LS enc s₀ (k + 1)) :=
  WP.mono (wp_sp (hb hp hk h.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2⟩

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : AesCbc.PPC64LE.CallPre s (W s₀) (Sv s₀) (S s₀) (R s₀)
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = byt s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = byt s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  sp : s.sp = s₀.sp

theorem Mid.of {enc : Bool} {s₀ : State} {k : Nat} {s s₁ : State} (h : LS enc s₀ k s)
    (a : PreA s₀ s s₁) (hs : s₁.sp = s.sp) : Mid s₀ k s₁ :=
  ⟨a.pre, by rw [a.saved .r16 (by decide), h.1.r16], by rw [a.saved .r17 (by decide), h.1.r17],
    by rw [a.saved .r18 (by decide), h.1.r18], by rw [a.saved .r19 (by decide), h.1.r19],
    hs.trans h.2⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat}
    {s s' : State} (h : Mid s₀ k s) (hc : CallPost f s (W s₀) (Sv s₀) (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .r16 (by decide), h.r16], by rw [hc.saved .r17 (by decide), h.r17],
    by rw [hc.saved .r18 (by decide), h.r18], by rw [hc.saved .r19 (by decide), h.r19],
    hc.sp.trans h.sp⟩

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block encPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block decPost) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- One byte, in two runs: the code before the call, the call on the copy
of the input block, and `post`. -/
theorem body_ct {enc : Bool} {post : List Instr}
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block post) h).isSome = true)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8PPC64LE enc).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LS enc s₀ k s₁ ∧ LS enc s₀' k s₂) (body post) fun _ _ => True := by
  obtain ⟨_, hA⟩ := pre_taint
  obtain ⟨_, hB⟩ := hB
  have a := (taintRegs (P := fun s₁ s₂ => k < N s₀ ∧ LS enc s₀ k s₁ ∧ LS enc s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.2, h.2.2.2, pub_sp hq], LInv.agree hq h.2.1.1 h.2.2.1⟩) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨WP.mono (wp_sp (pre_wp hp h.2.1.1)) fun _ ⟨a, e⟩ => Mid.of h.2.1 a e,
       WP.mono (wp_sp (pre_wp hp' h.2.2.1)) fun _ ⟨a, e⟩ => Mid.of h.2.2 a e⟩
  have c := (blk_rel (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
    Proof.Aes.PPC64LE.encryptBlocks_ct (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pub_Sv hq, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
          encryptBlocks_noFrames h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call (name := "vg_aes_encrypt_blocks") Proof.Aes.PPC64LE.encryptBlocks_correct
          encryptBlocks_noFrames h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := taintRegs (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) [.r16, .r17, .r18, .r19]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r16, h.2.r16, pub_Iv hq]
      · rw [h.1.r17, h.2.r17, pub_byt hq]
      · rw [h.1.r18, h.2.r18, pub_N hq]
      · rw [h.1.r19, h.2.r19, pub_S hq]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (enc : Bool) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LS enc s₀ k s₁ ∧ LS enc s₀' k s₂

theorem loop_ct {enc : Bool} {post : List Instr} (hb : BodyOk enc (body post))
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block post) h).isSome = true)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8PPC64LE enc).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel enc s₀ s₀' n) (.loop (body post) (.nonzero .d .r18))
      fun s₁ s₂ => LS enc s₀ (N s₀) s₁ ∧ LS enc s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel enc s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .r7).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel enc s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (body_ct hB hp hp' hq k).wp (F₁ := LS enc s₀ (k + 1)) (F₂ := LS enc s₀' (k + 1))
    fun _ _ h => ⟨bodyS hb hp h.1 h.2.1, bodyS hb hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have bd : N s₀ - (k + 1) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hb₀
  have e₁ := eval_nonzero_ofNat' s₁ .r18 bd l₁.1.r18
  have e₂ := eval_nonzero_ofNat' s₂ .r18 (k := N s₀ - (k + 1)) bd (by rw [l₂.1.r18, hN])
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
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block post) h).isSome = true)
    {s₀ s₀' : State} (h0 : (cfb8PPC64LE enc).pre s₀) (h0' : (cfb8PPC64LE enc).pre s₀')
    (hq : (cfb8PPC64LE enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole (body post)) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  obtain ⟨_, hpro⟩ := prologue_taint
  obtain ⟨_, hepi⟩ := epilogue_taint
  obtain ⟨_, hnil⟩ := nil_taint
  have pro := (taintRegs (P := fun a b => a = s₀ ∧ b = s₀') [.r3, .r4, .r5, .r6, .r7, .r8]
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨pub_sp hq, fun r hr => ?_⟩
      obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := LS enc s₀ 0) (F₂ := LS enc s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wp_sp (prologue_wp hp), wp_sp (prologue_wp hp')⟩
  have ev {t : State} {s : State} (h : LS enc t 0 s) : isa.eval (.zero .d .r18) s = some (decide (N t = 0)) := by
    have := eval_zero_ofNat s .r18 (k := N t - 0) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .r7).isLt)
      h.1.r18
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (LS enc s₀ 0 a ∧ LS enc s₀' 0 b) ∧
      isa.eval (.zero .d .r18) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.2, h.1.2.2, pub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => LS enc s₀ 0 a ∧ LS enc s₀' 0 b)
      (.ite (.zero .d .r18) (.block []) (.loop (body post) (.nonzero .d .r18)))
      (fun a b => LS enc s₀ (N s₀) a ∧ LS enc s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := LS enc s₀ (N s₀)) (F₂ := LS enc s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · have lp : ∀ hn : 0 < N s₀, RelCT isa (fun a b => LS enc s₀ 0 a ∧ LS enc s₀' 0 b)
          (.loop (body post) (.nonzero .d .r18)) (fun a b => LS enc s₀ (N s₀) a ∧ LS enc s₀' (N s₀') b) :=
        fun hn => (loop_ct hb hB hp hp' hq (N s₀ - 0)).mono
          (fun _ _ (h : LS enc s₀ 0 _ ∧ LS enc s₀' 0 _) => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h
      refine (RelCT.exists_ lp).mono (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := taintRegs (P := fun a b => LS enc s₀ (N s₀) a ∧ LS enc s₀' (N s₀') b) [.r19]
    (fun a b h => ⟨by rw [h.1.2, h.2.2, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1.r19, h.2.1.r19, pub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_ct {enc : Bool} {post : List Instr} (hb : BodyOk enc (body post))
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block post) h).isSome = true) :
    ConstantTime isa (cfb8PPC64LE enc).pre (cfb8PPC64LE enc).pub (whole (body post)) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hB h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCfb8.PPC64LE
