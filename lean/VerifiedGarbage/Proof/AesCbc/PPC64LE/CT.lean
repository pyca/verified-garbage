module

public import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.AesCbc.PPC64LE.Body
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# AES-CBC on PPC64LE: constant time

As on x86-64 (`Proof/AesCbc/X86_64/CT.lean`): two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proof pins to the public arguments (`LInv`) and the stack
pointer, which no code changes (`LS`), and each call of a block function is
constant time by its own proof (`blk_rel`). `whole_ct`: if one run of
`body` is (`BodyCt`), `whole body` is.
-/

@[expose] public section

namespace VG.Proof.AesCbc.PPC64LE

open VG VG.PPC64LE VG.Impl.AesCbc.PPC64LE

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
variable {M : Mode} {s₀ s₀' : State} (hq : (modePPC64LE M).pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_r4 : s₀.gpr .r4 = s₀'.gpr .r4 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r4 hq]
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
  · rw [h₁.r14, h₂.r14, pub_W hq]
  · rw [h₁.r15, h₂.r15, pub_r4 hq]
  · rw [h₁.r16, h₂.r16, pub_Iv hq]
  · rw [h₁.r17, h₂.r17, pub_blk hq]
  · rw [h₁.r18, h₂.r18, pub_N hq]
  · rw [h₁.r19, h₂.r19, pub_S hq]

end

/-- The invariant, and the stack pointer on entry. -/
def LS (M : Mode) (s₀ : State) (k : Nat) (s : State) : Prop := LInv M s₀ k s ∧ s.sp = s₀.sp

theorem bodyS {M : Mode} {body : Prog isa} (hb : BodyOk M body) {s₀ : State} (hp : UPre s₀) {k : Nat}
    (hk : k < N s₀) {s : State} (h : LS M s₀ k s) : WP isa body s (LS M s₀ (k + 1)) :=
  WP.mono (wp_sp (hb hp hk h.1)) fun _ ⟨l, e⟩ => ⟨l, e.trans h.2⟩

/-- One run of `body` from `k` blocks is constant time. -/
def BodyCt (M : Mode) (body : Prog isa) : Prop :=
  ∀ {s₀ s₀' : State}, UPre s₀ → UPre s₀' → (modePPC64LE M).pub s₀ s₀' → ∀ k : Nat,
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂) body fun _ _ => True

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (D : Addr) (s : State) : Prop where
  pre : CallPre s (W s₀) D (S s₀) (R s₀)
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  sp : s.sp = s₀.sp

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r16 : s.gpr .r16 = Iv s₀
  r17 : s.gpr .r17 = blk s₀ k
  r18 : s.gpr .r18 = BitVec.ofNat 64 (N s₀ - k)
  r19 : s.gpr .r19 = S s₀
  sp : s.sp = s₀.sp

theorem Mid.of {s₀ : State} {k : Nat} {D : Addr} {m : Mem} {s s₁ : State} {M : Mode} (h : LS M s₀ k s)
    (a : Pre s₀ D m s s₁) (hs : s₁.sp = s.sp) : Mid s₀ k D s₁ :=
  ⟨a.pre, by rw [a.saved .r16 (by decide), h.1.r16], by rw [a.saved .r17 (by decide), h.1.r17],
    by rw [a.saved .r18 (by decide), h.1.r18], by rw [a.saved .r19 (by decide), h.1.r19],
    hs.trans h.2⟩

theorem After.of {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ : State} {k : Nat}
    {D : Addr} {s s' : State} (h : Mid s₀ k D s) (hc : CallPost f s (W s₀) D (S s₀) (R s₀) s') :
    After s₀ k s' :=
  ⟨by rw [hc.saved .r16 (by decide), h.r16], by rw [hc.saved .r17 (by decide), h.r17],
    by rw [hc.saved .r18 (by decide), h.r18], by rw [hc.saved .r19 (by decide), h.r19],
    hc.sp.trans h.sp⟩

/-- A body: code before the call (`pre`), the call of a block function on
the block at `D s₀ k` (public), and code after it (`post`), constant time when `pre`'s addresses
and branches depend only on the registers the invariant pins and `post`'s on
`r16` to `r19`. -/
theorem body_ct {M : Mode} {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State}
    {name : String} {c : Prog isa} {pre post : List Instr} {m : State → Nat → State → Mem}
    {D : State → Nat → Addr}
    (pubD : ∀ {s₀ s₀' : State}, (modePPC64LE M).pub s₀ s₀' → ∀ k, D s₀ k = D s₀' k)
    (ok : ∀ s, (Proof.Aes.blocksPPC64LE f).pre s →
      ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksPPC64LE f).post s s')
    (ct : ConstantTime isa (Proof.Aes.blocksPPC64LE f).pre (Proof.Aes.blocksPPC64LE f).pub c)
    (nf : c.noFrames = true)
    (hA : ∃ h, (taint.check (Taint.ofRegs vars) (.block pre) h).isSome = true)
    (hB : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19]) (.block post) h).isSome = true)
    (wpA : ∀ {s₀ : State}, UPre s₀ → ∀ {k : Nat}, k < N s₀ → ∀ {s : State}, LInv M s₀ k s →
      WP isa (.block pre) s (Pre s₀ (D s₀ k) (m s₀ k s) s))
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modePPC64LE M).pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂)
      (.seq (.block pre) (.seq (.call name c) (.block post))) fun _ _ => True := by
  obtain ⟨_, hA⟩ := hA
  obtain ⟨_, hB⟩ := hB
  have a := (taintRegs (P := fun s₁ s₂ => k < N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂) vars
    (fun _ _ h => ⟨by rw [h.2.1.2, h.2.2.2, pub_sp hq], LInv.agree hq h.2.1.1 h.2.2.1⟩) hA).wp
    (F₁ := Mid s₀ k (D s₀ k)) (F₂ := Mid s₀' k (D s₀' k)) fun _ _ h =>
      ⟨WP.mono (wp_sp (wpA hp h.1 h.2.1.1)) fun _ ⟨a, e⟩ => Mid.of h.2.1 a e,
       WP.mono (wp_sp (wpA hp' (by rw [← pub_N hq]; exact h.1) h.2.2.1)) fun _ ⟨a, e⟩ => Mid.of h.2.2 a e⟩
  have c := (blk_rel (name := name) ok ct (P := fun s₁ s₂ => Mid s₀ k (D s₀ k) s₁ ∧ Mid s₀' k (D s₀' k) s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pubD hq k, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (blk_call (name := name) ok nf h.1.pre) fun _ hc => After.of h.1 hc,
       WP.mono (blk_call (name := name) ok nf h.2.pre) fun _ hc => After.of h.2 hc⟩
  have b := taintRegs (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) [.r16, .r17, .r18, .r19]
    (fun s₁ s₂ h => ⟨by rw [h.1.sp, h.2.sp, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h.1.r16, h.2.r16, pub_Iv hq]
      · rw [h.1.r17, h.2.r17, pub_blk hq]
      · rw [h.1.r18, h.2.r18, pub_N hq]
      · rw [h.1.r19, h.2.r19, pub_S hq]⟩) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem encPre_taint : ∃ h, (taint.check (Taint.ofRegs vars)
    (.block (xorInto .r17 .r16 ++ callArgs)) h).isSome = true := ⟨_, by taint_decide⟩

theorem encPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block (copy .r16 0 .r17 0 ++ advance)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPre_taint : ∃ h, (taint.check (Taint.ofRegs vars)
    (.block (copy .r19 cOff .r17 0 ++ callArgs)) h).isSome = true := ⟨_, by taint_decide⟩

theorem decPost_taint : ∃ h, (taint.check (Taint.ofRegs [.r16, .r17, .r18, .r19])
    (.block (xorInto .r17 .r16 ++ copy .r16 0 .r19 cOff ++ advance)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem encBody_ct : BodyCt (cbcMode true) encBody :=
  fun hp hp' hq k => body_ct (m := fun s₀ k s => xorMem s.mem (blk s₀ k) (Iv s₀)) (fun hq k => pub_blk hq k)
    Proof.Aes.PPC64LE.encryptBlocks_correct Proof.Aes.PPC64LE.encryptBlocks_ct encryptBlocks_noFrames
    encPre_taint encPost_taint (@fun _ hp _ hk _ h => encA_wp hp hk h) hp hp' hq k

theorem decBody_ct : BodyCt (cbcMode false) decBody :=
  fun hp hp' hq k => body_ct (m := fun s₀ k s => copyMem s.mem (Sv s₀) (blk s₀ k)) (fun hq k => pub_blk hq k)
    Proof.Aes.PPC64LE.decryptBlocks_correct Proof.Aes.PPC64LE.decryptBlocks_ct decryptBlocks_noFrames
    decPre_taint decPost_taint (@fun _ hp _ hk _ h => decA_wp hp hk h) hp hp' hq k

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (M : Mode) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LS M s₀ k s₁ ∧ LS M s₀' k s₂

theorem loop_ct {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body)
    {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : (modePPC64LE M).pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel M s₀ s₀' n) (.loop body (.nonzero .d .r18))
      fun s₁ s₂ => LS M s₀ (N s₀) s₁ ∧ LS M s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel M s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .r7).isLt
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel M s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (hc hp hp' hq k).wp (F₁ := LS M s₀ (k + 1)) (F₂ := LS M s₀' (k + 1))
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

theorem prologue_taint : ∃ h, (taint.check (Taint.ofRegs [.r3, .r4, .r5, .r6, .r7, .r8])
    (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩

theorem epilogue_taint : ∃ h, (taint.check (Taint.ofRegs [.r19]) (.block restore) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem nil_taint : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
  ⟨_, by taint_decide⟩

/-- The registers saved and the arguments set up, `mid` run unless there are
no blocks, and the registers restored, constant time when two runs of `mid`
from the invariant after no blocks are (`whole_rel`: `body`'s loop). -/
theorem ends_rel {M : Mode} {mid : Prog isa}
    {s₀ s₀' : State} (h0 : (modePPC64LE M).pre s₀) (h0' : (modePPC64LE M).pre s₀')
    (hq : (modePPC64LE M).pub s₀ s₀')
    (hm : UPre s₀ → UPre s₀' → 0 < N s₀ →
      RelCT isa (fun a b => LS M s₀ 0 a ∧ LS M s₀' 0 b) mid
        fun a b => LS M s₀ (N s₀) a ∧ LS M s₀' (N s₀') b) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀')
      (.seq (.block (save ++ setup)) (.seq (.ite (.zero .d .r18) (.block []) mid) (.block restore)))
      fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  have hb₀ := (s₀.gpr .r7).isLt
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
    (F₁ := LS M s₀ 0) (F₂ := LS M s₀' 0)
    fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨wp_sp (prologue_wp hp), wp_sp (prologue_wp hp')⟩
  have ev {t : State} {s : State} (h : LS M t 0 s) : isa.eval (.zero .d .r18) s = some (decide (N t = 0)) := by
    have := eval_zero_ofNat s .r18 (k := N t - 0) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t.gpr .r7).isLt)
      h.1.r18
    rwa [Nat.sub_zero] at this
  have nil := taintRegs (P := fun a b => (LS M s₀ 0 a ∧ LS M s₀' 0 b) ∧
      isa.eval (.zero .d .r18) a = some true) []
    (fun _ _ h => ⟨by rw [h.1.1.2, h.1.2.2, pub_sp hq], fun r hr => by simp at hr⟩) hnil
  have mid : RelCT isa (fun a b => LS M s₀ 0 a ∧ LS M s₀' 0 b) (.ite (.zero .d .r18) (.block []) mid)
      (fun a b => LS M s₀ (N s₀) a ∧ LS M s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1, ev h.2, hN]) ?_ ?_
    · refine (nil.wp (F₁ := LS M s₀ (N s₀)) (F₂ := LS M s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (RelCT.exists_ fun (hn : 0 < N s₀) => hm hp hp' hn).mono
        (fun a b h => ⟨?_, h.1.1, h.1.2⟩) fun _ _ h => h
      have := h.2; rw [ev h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := taintRegs (P := fun a b => LS M s₀ (N s₀) a ∧ LS M s₀' (N s₀') b) [.r19]
    (fun a b h => ⟨by rw [h.1.2, h.2.2, pub_sp hq], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.1.r19, h.2.1.r19, pub_S hq]⟩) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem whole_rel {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body)
    {s₀ s₀' : State} (h0 : (modePPC64LE M).pre s₀) (h0' : (modePPC64LE M).pre s₀')
    (hq : (modePPC64LE M).pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (whole body) fun _ _ => True :=
  ends_rel h0 h0' hq fun hp hp' hn =>
    (loop_ct hb hc hp hp' hq (N s₀ - 0)).mono (fun _ _ h => ⟨0, rfl, hn, h.1, h.2⟩) fun _ _ h => h

theorem whole_ct {M : Mode} {body : Prog isa} (hb : BodyOk M body) (hc : BodyCt M body) :
    ConstantTime isa (modePPC64LE M).pre (modePPC64LE M).pub (whole body) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (whole_rel hb hc h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.AesCbc.PPC64LE
