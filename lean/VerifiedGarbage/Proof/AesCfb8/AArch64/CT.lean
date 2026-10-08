import VerifiedGarbage.Proof.AesCfb8.AArch64.Body
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# AES-CFB8 on AArch64: constant time

AES-CBC's argument (`Proof/AesCbc/AArch64/CT.lean`) for the CFB8 loop: two
runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`),
and each call of a block function is constant time by its own proof
(`blk_rel`). `whole_ct`: if one run of `body` is (`BodyCt`), `whole body` is.
-/

namespace VG.Proof.AesCfb8.AArch64

open VG VG.AArch64 VG.Impl.AesCbc.AArch64 VG.Impl.AesCfb8.AArch64
open VG.Proof.AesCbc.AArch64 (W R Iv Dp N S Sv CallPre CallPost blk_call blk_rel eval_x23 eval_zero_x23)
open VG.Proof.Aes.AArch64 (BlocksImpl)

/-- States agree on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

section
variable {enc : Bool} {s₀ s₀' : State} (hq : (cfb8AArch64 enc).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_x1 : s₀.gpr .x1 = s₀'.gpr .x1 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_x1 hq]
theorem pub_Iv : Iv s₀ = Iv s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2
theorem pub_byt (k : Nat) : byt s₀ k = byt s₀' k := by rw [byt, byt, pub_Dp hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv enc s₀ k s₁) (h₂ : LInv enc s₀' k s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) s₁ s₂ := by
  refine agree_of (by rw [h₁.sp, h₂.sp, pub_sp hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.x19, h₂.x19, pub_W hq]
  · rw [h₁.x20, h₂.x20, pub_x1 hq]
  · rw [h₁.x21, h₂.x21, pub_Iv hq]
  · rw [h₁.x22, h₂.x22, pub_byt hq]
  · rw [h₁.x23, h₂.x23, pub_N hq]
  · rw [h₁.x24, h₂.x24, pub_S hq]

end

/-- One run of `body` from `k` bytes is constant time. -/
def BodyCt (enc : Bool) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (cfb8AArch64 enc).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) body fun _ _ => True

/-! ## One byte -/

/-- What is known between the code before the call and the call, on the
block at `D`. -/
structure Mid (s₀ : State) (k : Nat) (D : Addr) (s : State) : Prop where
  pre : CallPre s (W s₀) D (S s₀) (R s₀)
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = byt s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  x21 : s.gpr .x21 = Iv s₀
  x22 : s.gpr .x22 = byt s₀ k
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  x24 : s.gpr .x24 = S s₀
  sp : s.sp = s₀.sp

theorem Mid.of {s₀ : State} {k : Nat} {D : Addr} {s s₁ : State} {enc : Bool} (h : LInv enc s₀ k s)
    (pre : CallPre s₁ (W s₀) D (S s₀) (R s₀)) (saved : ∀ r ∈ preserved, s₁.gpr r = s.gpr r)
    (sp : s₁.sp = s.sp) : Mid s₀ k D s₁ :=
  ⟨pre, by rw [saved .x21 (by simp [preserved]), h.x21], by rw [saved .x22 (by simp [preserved]), h.x22],
    by rw [saved .x23 (by simp [preserved]), h.x23], by rw [saved .x24 (by simp [preserved]), h.x24],
    by rw [sp, h.sp]⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat} {D : Addr}
    {s s' : State} (h : Mid s₀ k D s) (hc : CallPost f s (W s₀) D (S s₀) (R s₀) s') : After s₀ k s' :=
  ⟨by rw [hc.saved .x21 (by simp [preserved]) (by decide), h.x21],
    by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.x22],
    by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.x23],
    by rw [hc.saved .x24 (by simp [preserved]) (by decide), h.x24], by rw [hc.sp, h.sp]⟩

/-- A body: code before the call (`pre`), the call of `b` on the block at
`D s₀ k` (public), and code after it (`post`), constant time when `pre`'s
addresses and branches depend only on the registers the invariant pins and
`post`'s on `x21` to `x24`. -/
theorem body_ct {enc : Bool} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {D : State → Nat → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (cfb8AArch64 enc).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    {b : Impl.Aes.AArch64.Blocks} {pre post : List Instr}
    (ok : ∀ s, (Proof.Aes.blocksAArch64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksAArch64 f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksAArch64 f).pre (Proof.Aes.blocksAArch64 f).pub b.code)
    (nf : b.code.noFrames = true)
    (hA : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv enc s₀ k s →
      WP isa (.block pre) s (Mid s₀ k (D s₀ k)))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8AArch64 enc).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂)
      (.seq (.block pre) (.seq (.call b.name b.code) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (RelCT.taint (A := taint)
    (P := fun s₁ s₂ => k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂) _
    (fun _ _ h => LInv.agree hq h.2.1 h.2.2) hA).wp
    (F₁ := Mid s₀ k (D s₀ k)) (F₂ := Mid s₀' k (D s₀' k)) fun _ _ h =>
      ⟨wpA hp h.1 h.2.1, wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (blk_rel ok ct (P := fun s₁ s₂ => Mid s₀ k (D s₀ k) s₁ ∧ Mid s₀' k (D s₀' k) s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call ok nf h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call ok nf h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.x21, h.2.x21, pub_Iv hq]
      · rw [h.1.x22, h.2.x22, pub_byt hq]
      · rw [h.1.x23, h.2.x23, pub_N hq]
      · rw [h.1.x24, h.2.x24, pub_S hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem pre_taint : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
    (.block pre) h).isSome = true := ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block encPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.x21, .x22, .x23, .x24])
    (.block decPost) h).isSome = true := ⟨_, by taint_decide⟩

theorem pub_Sv {enc : Bool} {s₀ s₀' : State} (hq : (cfb8AArch64 enc).pub s₀ s₀') : Sv s₀ = Sv s₀' := by
  rw [Sv, Sv, pub_S hq]

theorem encBody_ct (v : BlocksImpl) : BodyCt true (body v.enc encPost) :=
  fun hp hp' hq k => body_ct (D := fun s₀ _ => Sv s₀) (fun hq _ => pub_Sv hq) v.encOk v.encCt v.encNoFrames
    pre_taint encPost_taint
    (@fun _ hp _ _ _ h => WP.mono (pre_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

theorem decBody_ct (v : BlocksImpl) : BodyCt false (body v.enc decPost) :=
  fun hp hp' hq k => body_ct (D := fun s₀ _ => Sv s₀) (fun hq _ => pub_Sv hq) v.encOk v.encCt v.encNoFrames
    pre_taint decPost_taint
    (@fun _ hp _ _ _ h => WP.mono (pre_wp hp h) fun _ a => Mid.of h a.pre a.saved a.sp) hp hp' hq k

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (enc : Bool) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv enc s₀ k s₁ ∧ LInv enc s₀' k s₂

theorem loop_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (cfb8AArch64 enc).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel enc s₀ s₀' n) (.loop body (.nonzero .x .x23))
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
    (F₁ := LInv enc s₀ (k + 1)) (F₂ := LInv enc s₀' (k + 1))
    fun _ _ h => ⟨hb hp h.1 h.2.1, hb hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have hbd : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have e₁ := eval_x23 (x := N s₀ - (k + 1)) (by omega) l₁.x23
  have e₂ := eval_x23 (x := N s₀ - (k + 1)) (by omega) (by rw [l₂.x23, ← hN])
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
    {s₀ s₀' : State} (h0 : (cfb8AArch64 enc).pre s₀) (h0' : (cfb8AArch64 enc).pre s₀')
    (hq : (cfb8AArch64 enc).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  have hbd : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.x24]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      refine agree_of h7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hpro).wp
    (F₁ := LInv enc s₀ 0) (F₂ := LInv enc s₀' 0)
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {s : State} (h : LInv enc s₀ 0 s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hbd (by rw [h.x23]; rfl)
  have ev' {s : State} (h : LInv enc s₀' 0 s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hbd (by rw [h.x23, ← hN]; rfl)
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (LInv enc s₀ 0 a ∧ LInv enc s₀' 0 b) ∧ isa.eval (.zero .x .x23) a = some true) _
    (fun a b h => agree_of (by rw [h.1.1.sp, h.1.2.sp, pub_sp hq]) fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => LInv enc s₀ 0 a ∧ LInv enc s₀' 0 b)
      (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23)))
      (fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev' h.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv enc s₀ (N s₀)) (F₂ := LInv enc s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1, h.1.2⟩)
        fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv enc s₀ (N s₀) a ∧ LInv enc s₀' (N s₀') b) _
    (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.x24, h.2.x24, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_ct {enc : Bool} {body : Prog isa} (hb : BodyOk enc body) (hc : BodyCt enc body) :
    ConstantTime isa (cfb8AArch64 enc).pre (cfb8AArch64 enc).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCfb8.AArch64
