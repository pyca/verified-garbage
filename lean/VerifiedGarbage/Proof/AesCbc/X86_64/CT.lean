import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-CBC on x86-64: constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`),
and each call of a block function is constant time by its own proof
(`blk_rel`). `whole_ct`: if one run of `body` is (`BodyCt`), `whole body` is.
-/

namespace VG.Proof.AesCbc.X86_64

open VG VG.X86_64 VG.Impl.AesCbc.X86_64
open VG.Proof.Aes.X86_64 (BlocksImpl)

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (cbcX86_64 enc).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_rsi : s₀.gpr .rsi = s₀'.gpr .rsi := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rsi hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2
theorem pub_blk (k : Nat) : blk s₀ k = blk s₀' k := by rw [blk, blk, pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv enc s₀ k s₁) (h₂ : LInv enc s₀' k s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rsi hq]
  · rw [h₁.r12, h₂.r12, pub_Iv hq]
  · rw [h₁.r13, h₂.r13, pub_blk hq]
  · rw [h₁.r14, h₂.r14, pub_N hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]
  · rw [h₁.rsp, h₂.rsp, pub_rsp hq]

end

/-- One run of `body` from `k` blocks is constant time. -/
def BodyCt (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (cbcX86_64 enc).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) body fun _ _ => True

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (blk s₀ k) (S s₀) (R s₀)
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r12 : s.gpr .r12 = Iv s₀
  r13 : s.gpr .r13 = blk s₀ k
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  r15 : s.gpr .r15 = S s₀

theorem Mid.of {s₀ : State} {k : Nat} {s s₁ : State} {enc : Bool} (h : LInv enc s₀ k s)
    (pre : CallPre s₁ (W s₀) (blk s₀ k) (S s₀) (R s₀)) (saved : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r) :
    Mid s₀ k s₁ :=
  ⟨pre, by rw [saved .r12 (by simp [calleeSaved]), h.r12], by rw [saved .r13 (by simp [calleeSaved]), h.r13],
    by rw [saved .r14 (by simp [calleeSaved]), h.r14], by rw [saved .r15 (by simp [calleeSaved]), h.r15],
    by rw [saved .rsp (by simp [calleeSaved]), h.rsp]⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat} {s s' : State}
    (h : Mid s₀ k s) (hc : CallPost f s (W s₀) (blk s₀ k) (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .r12 (by simp [calleeSaved]), h.r12], by rw [hc.saved .r13 (by simp [calleeSaved]), h.r13],
    by rw [hc.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hc.saved .r15 (by simp [calleeSaved]), h.r15]⟩

/-- A body: code before the call (`pre`), the call of `b`, and code after it
(`post`), constant time when `pre`'s addresses and branches depend only on
the registers the invariant pins and `post`'s on `r12` to `r15`. -/
theorem body_ct {enc : Bool} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {b : Impl.Aes.X86_64.Blocks} {pre post : List Instr}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksX86_64 f).pre (Proof.Aes.blocksX86_64 f).pub b.code)
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    (hA : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
      WP isa (.block pre) s (Mid s₀ k))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cbcX86_64 enc).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂)
      (.seq (.block pre) (.seq (.call b.name b.code) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1 h.2.2)) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨wpA hp h.1 h.2.1, wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (blk_rel ok ct (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, h.1.pre, by
        rw [pub_W hq, pub_S hq, pub_blk hq, pub_R hq]; exact h.2.pre,
        by rw [h.1.rsp, h.2.rsp, pub_rsp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call ok nosp depth h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call ok nosp depth h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r12, h.2.r12, pub_Iv hq]
      · rw [h.1.r13, h.2.r13, pub_blk hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]
      · rw [h.1.r15, h.2.r15, pub_S hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem encPre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block (xorInto .r13 .r12 ++ callArgs)) h).isSome = true := ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block (copy .r12 0 .r13 0 ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPre_taint : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
    (.block (copy .r15 cOff .r13 0 ++ callArgs)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r12, .r13, .r14, .r15])
    (.block (xorInto .r13 .r12 ++ copy .r12 0 .r15 cOff ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem encBody_ct (v : BlocksImpl) : BodyCt true (encBody v.enc) :=
  fun hp hp' hq k => body_ct v.encOk v.encCt v.encNosp v.encDepth encPre_taint encPost_taint
    (@fun _ hp _ hk _ h => WP.mono (encA_wp hp hk h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt false (decBody v.dec) :=
  fun hp hp' hq k => body_ct v.decOk v.decCt v.decNosp v.decDepth decPre_taint decPost_taint
    (@fun _ hp _ hk _ h => WP.mono (decA_wp hp hk h) fun _ a => Mid.of h a.pre a.saved) hp hp' hq k

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (enc : Bool) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂

theorem loop_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cbcX86_64 enc).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel enc s₀ s₀' n) (.loop body .ne)
      fun s₁ s₂ => LInv enc s₀ (N s₀) s₁ ∧ LInv enc s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel enc s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel enc s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (hc hp hp' hq k).wp
    (F₁ := fun (s' : State) => LInv enc s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)))
    (F₂ := fun (s' : State) => LInv enc s₀' (k + 1) s' ∧ s'.zf = some (decide (N s₀' - (k + 1) = 0)))
    fun _ _ h => ⟨hb hp h.1 h.2.1, hb hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₁.zf.map _ = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₂.zf.map _ = _; rw [z₂]; rfl
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

theorem whole_rel {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (h0 : (cbcX86_64 enc).pre s₀) (h0' : (cbcX86_64 enc).pre s₀')
    (hq : (cbcX86_64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := fun (s : State) => LInv enc s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv enc s₀' 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv enc s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv enc s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) _
    (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv enc s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv enc s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop body .ne))
      (fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
    · refine (nil.wp (F₁ := LInv enc s₀ (N s₀)) (F₂ := LInv enc s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1.1, h.1.2.1⟩)
        fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r15, h.2.r15, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body) :
    ConstantTime isa (cbcX86_64 enc).pre (cbcX86_64 enc).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCbc.X86_64
