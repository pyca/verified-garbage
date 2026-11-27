module

import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.CalleeSide
import VerifiedGarbage.Proof.Framework.X86_64.ScrubCall
public import VerifiedGarbage.Impl.CmacAes.X86_64.Callee
public import VerifiedGarbage.Proof.CmacAes.X86_64.AesNi
public import VerifiedGarbage.Spec.Cmac.Contract
public import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
public import VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Spec.Cmac.Contract
meta import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
meta import VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys
meta import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
meta import VerifiedGarbage.Proof.Aes.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `CmacAes.X86_64.Verified`, which this module and modules that import it used -/

section

@[expose] public section

section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`), and
each call of `vg_aes_ctr32` is constant time by its own proof (`AesCall.rel`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

section
variable {s₀ s₀' : State} (hq : updateX86_64.pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_rsi : s₀.gpr .rsi = s₀'.gpr .rsi := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rsi hq]
theorem pub_St : St s₀ = St s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {X X' : Region} {k : Nat} {s₁ s₂ : State} (h₁ : LInv s₀ X k s₁) (h₂ : LInv s₀' X' k s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rsi hq]
  · rw [h₁.r12, h₂.r12, pub_St hq]
  · rw [h₁.r13, h₂.r13, pub_Dp hq]
  · rw [h₁.r14, h₂.r14, pub_N hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]
  · rw [h₁.rsp, h₂.rsp, pub_rsp hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPreF s (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  rsp : s.gpr .rsp = s₀.gpr .rsp
  wr : s.wr = s₀.wr

theorem bodyMid_wp {s₀ : State} {Z X : Region} (hp : UPre s₀ Z) {k : Nat} (hk : k < N s₀) {s : State}
    (h : LInv s₀ X k s) : WP isa (.block (chainIn ++ updArgs)) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.saved .r13 (by simp [calleeSaved]), h.r13],
      by rw [hb.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hb.saved .rsp (by simp [calleeSaved]), h.rsp],
      by rw [hb.wr, h.wr]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)

theorem body_ct {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ s₀' : State}
    (hp : UPre s₀ (Z (S s₀))) (hp' : UPre s₀' (Z (S s₀'))) (hq : updateX86_64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv s₀ (X (S s₀)) k s₁ ∧ LInv s₀' (X (S s₀')) k s₂) (body c)
      fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13, .r14]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < N s₀ ∧ LInv s₀ (X (S s₀)) k s₁ ∧ LInv s₀' (X (S s₀')) k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1 h.2.2)) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨bodyMid_wp hp h.1 h.2.1, bodyMid_wp hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (T.rel (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨W s₀, St s₀, S s₀, R s₀, ⟨h.1.pre, hp.scrPre h.1.rsp h.1.wr⟩, by
        rw [pub_W hq, pub_S hq, pub_St hq, pub_R hq]; exact ⟨h.2.pre, hp'.scrPre h.2.rsp h.2.wr⟩,
        by rw [h.1.rsp, h.2.rsp, pub_rsp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (T.ok h.1.pre (hp.scrPre h.1.rsp h.1.wr)) fun _ hc =>
        ⟨by rw [hc.saved .r13 (by simp [calleeSaved]), h.1.r13],
          by rw [hc.saved .r14 (by simp [calleeSaved]), h.1.r14]⟩,
       WP.mono (T.ok h.2.pre (hp'.scrPre h.2.rsp h.2.wr)) fun _ hc =>
        ⟨by rw [hc.saved .r13 (by simp [calleeSaved]), h.2.r13],
          by rw [hc.saved .r14 (by simp [calleeSaved]), h.2.r14]⟩⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r13, h.2.r13, pub_Dp hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (X : Addr → Region) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv s₀ (X (S s₀)) k s₁ ∧ LInv s₀' (X (S s₀')) k s₂

theorem loop_ct {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ s₀' : State}
    (hp : UPre s₀ (Z (S s₀))) (hp' : UPre s₀' (Z (S s₀'))) (hq : updateX86_64.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel X s₀ s₀' n) (.loop (body c) .ne)
      fun s₁ s₂ => LInv s₀ (X (S s₀)) (N s₀) s₁ ∧ LInv s₀' (X (S s₀')) (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel X s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel X s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (body_ct T hp hp' hq k).wp
    (F₁ := fun (s' : State) => LInv s₀ (X (S s₀)) (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)))
    (F₂ := fun (s' : State) => LInv s₀' (X (S s₀')) (k + 1) s' ∧ s'.zf = some (decide (N s₀' - (k + 1) = 0)))
    fun _ _ h => ⟨body_ok T hp h.1 h.2.1, body_ok T hp' (by rw [← hN]; exact h.1) h.2.2⟩
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
      omega_using [hk, this]
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_using [hk], k + 1, rfl, by omega_using [h0], l₁, l₂⟩

/-! ## The whole function -/

theorem update_relG {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ s₀' : State}
    (hp : UPre s₀ (Z (S s₀))) (hp' : UPre s₀' (Z (S s₀'))) (hq : updateX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update c) fun _ _ => True := by
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
    (F₁ := fun (s : State) => LInv s₀ (X (S s₀)) 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv s₀' (X (S s₀')) 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv s₀ (X (S s₀)) 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' (X (S s₀')) 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) _
    (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv s₀ (X (S s₀)) 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' (X (S s₀')) 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop (body c) .ne))
      (fun a b => LInv s₀ (X (S s₀)) (N s₀) a ∧ LInv s₀' (X (S s₀')) (N s₀') b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
    · refine (nil.wp (F₁ := LInv s₀ (X (S s₀)) (N s₀)) (F₂ := LInv s₀' (X (S s₀')) (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct T hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1.1, h.1.2.1⟩)
        fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega_using [this]
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (X (S s₀)) (N s₀) a ∧ LInv s₀' (X (S s₀')) (N s₀') b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r15, h.2.r15, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : updateX86_64.pre s₀) (h0' : updateX86_64.pre s₀')
    (hq : updateX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True :=
  update_relG (AesCall.base v) (UPre.of h0) (UPre.of h0') hq

theorem updateS_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    ConstantTime isa updateX86_64S.pre updateX86_64S.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ =>
    (update_relG (AesCall.small v f) (UPre.ofS h₁) (UPre.ofS h₂) hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem update_ct (v : Ctr32Impl) :
    ConstantTime isa updateX86_64.pre updateX86_64.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64

end

section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_subkeys` is constant time

The code before the call and after it is checked by the taint analysis, from
the registers the correctness proof pins (the arguments, then `rbx` and
`rbp`); the call of `vg_aes_ctr32` is constant time by its own proof
(`AesCall.rel`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem subkeys_relG {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ s₀' : State}
    {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R (Z S)) (hp' : SPre s₀' W K S R (Z S))
    (q : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys c) fun _ _ => True := by
  have q1 : s₀.gpr .rdi = s₀'.gpr .rdi := by rw [hp.rdi, hp'.rdi]
  have q2 : s₀.gpr .rsi = s₀'.gpr .rsi := BitVec.eq_of_toNat_eq (by rw [hp.rsi, hp'.rsi])
  have q3 : s₀.gpr .rdx = s₀'.gpr .rdx := by rw [hp.rdx, hp'.rdx]
  have q4 : s₀.gpr .rcx = s₀'.gpr .rcx := by rw [hp.rcx, hp'.rcx]
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (.block subkeysPre) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp]) (.block subkeysPost) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := SMid s₀ W K S R) (F₂ := SMid s₀' W K S R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨smid_wp hp, smid_wp hp'⟩
  have c := (T.rel (P := fun s₁ s₂ => SMid s₀ W K S R s₁ ∧ SMid s₀' W K S R s₂) fun _ _ h =>
      ⟨W, K, S, R, ⟨h.1.pre, hp.scrPre h.1⟩, ⟨h.2.pre, hp'.scrPre h.2⟩, by rw [h.1.rsp, h.2.rsp, q]⟩).wp
    (F₁ := fun (s : State) => s.gpr .rbx = K ∧ s.gpr .rbp = S)
    (F₂ := fun (s : State) => s.gpr .rbx = K ∧ s.gpr .rbp = S) fun s₁ s₂ h =>
      ⟨WP.mono (T.ok h.1.pre (hp.scrPre h.1)) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.1.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.1.rbp]⟩,
       WP.mono (T.ok h.2.pre (hp'.scrPre h.2)) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.2.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.2.rbp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .rbx = K ∧ s₁.gpr .rbp = S) ∧ (s₂.gpr .rbx = K ∧ s₂.gpr .rbp = S)) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysX86_64.pre s₀)
    (h0' : subkeysX86_64.pre s₀') (hq : subkeysX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp' : SPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat ⟨s₀.gpr .rcx, 2176⟩ := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
  exact subkeys_relG (AesCall.base v) (SPre.of h0) hp' q5

theorem subkeysF_rel (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ s₀' : State}
    (h0 : subkeysX86_64F.pre s₀) (h0' : subkeysX86_64F.pre s₀') (hq : subkeysX86_64F.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp' : SPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat
      ⟨s₀.gpr .rcx + BitVec.ofNat 64 2048, 32⟩ := by
    rw [q1, q2, q3, q4]; exact SPre.ofF h0'
  exact subkeys_relG (AesCall.free v f fun S => ⟨S + BitVec.ofNat 64 2048, 32⟩) (SPre.ofF h0) hp' q5

theorem subkeysS_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    ConstantTime isa subkeysX86_64S.pre subkeysX86_64S.pub (subkeys v.callee) := by
  intro s₀ s₀' _ _ _ _ h0 h0' hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp' : SPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat
      ⟨s₀.gpr .rcx + BitVec.ofNat 64 512, 1664⟩ := by
    rw [q1, q2, q3, q4]; exact SPre.ofS h0'
  exact (subkeys_relG (AesCall.small v f) (SPre.ofS h0) hp' q5 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem subkeysF_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ConstantTime isa subkeysX86_64F.pre subkeysX86_64F.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeysF_rel v f h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem subkeys_ct (v : Ctr32Impl) :
    ConstantTime isa subkeysX86_64.pre subkeysX86_64.pub (subkeys v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (subkeys_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64

end

section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_finalize` is constant time

The code before the call is checked by the taint analysis (its branches and
the copy loop depend only on `last_len`), and the call of `vg_aes_ctr32` is
constant time by its own proof (`ctrCall_rel`, or `AesCall.rel` with less of
the scratch buffer), its arguments pinned by the correctness proof (`FMid`,
`FMidF`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeX86_64.pre s₀)
    (h0' : finalizeX86_64.pre s₀') (hq : finalizeX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have sw := FPre.scr_wrap_of h0
  have hp' : FPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat ⟨s₀.gpr .r9, 2176⟩ := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  have sw' : (s₀.gpr .r9).toNat + 2176 ≤ 2 ^ 64 := by rw [q6]; exact FPre.scr_wrap_of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMid s₀ _ _ _ _ _ _) (F₂ := FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp sw, finPre_wp hp' sw'⟩
  have c := ctrCall_rel v (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₁ ∧
      FMid s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, h.1.pre, h.2.pre, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q7]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

/-- `finalize` over the call `T` of `vg_aes_ctr32` is constant time, for
runs from two states with the same public arguments. -/
theorem finalize_relG {c : Impl.Aes.X86_64.Ctr32} {Z X : Addr → Region} (T : AesCall c Z X) {s₀ s₀' : State}
    {W St P S : Addr} {L R : Nat} (hp : FPre s₀ W St P S L R (Z S)) (hp' : FPre s₀' W St P S L R (Z S))
    (q : s₀.gpr .rsp = s₀'.gpr .rsp) :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize c) fun _ _ => True := by
  have q1 : s₀.gpr .rdi = s₀'.gpr .rdi := by rw [hp.rdi, hp'.rdi]
  have q2 : s₀.gpr .rsi = s₀'.gpr .rsi := BitVec.eq_of_toNat_eq (by rw [hp.rsi, hp'.rsi])
  have q3 : s₀.gpr .rdx = s₀'.gpr .rdx := by rw [hp.rdx, hp'.rdx]
  have q4 : s₀.gpr .rcx = s₀'.gpr .rcx := by rw [hp.rcx, hp'.rcx]
  have q5 : s₀.gpr .r8 = s₀'.gpr .r8 := BitVec.eq_of_toNat_eq (by rw [hp.r8, hp'.r8])
  have q6 : s₀.gpr .r9 = s₀'.gpr .r9 := by rw [hp.r9, hp'.r9]
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have scr {t₀ s : State} (hq : FPre t₀ W St P S L R (Z S)) (h : FMidF t₀ W St P S L R s) :
      ScrPre s W St (Z S) :=
    ⟨hq.key_scr.sub_left (Region.sub_prefix (by decide)), hq.st_scr, by
      rw [h.saved _ (by simp [calleeSaved])]; exact hq.stk_scr, by
      rw [h.wr, hq.wr]; exact Covers.of_mem fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMidF s₀ W St P S L R) (F₂ := FMidF s₀' W St P S L R) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPreF_wp hp, finPreF_wp hp'⟩
  have c := T.rel (P := fun s₁ s₂ => FMidF s₀ W St P S L R s₁ ∧ FMidF s₀' W St P S L R s₂)
    fun s₁ s₂ h => ⟨W, St, S, R, ⟨h.1.pre, scr hp h.1⟩, ⟨h.2.pre, scr hp' h.2⟩, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

theorem finalizeF_rel (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) {s₀ s₀' : State}
    (h0 : finalizeX86_64F.pre s₀) (h0' : finalizeX86_64F.pre s₀') (hq : finalizeX86_64F.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp' : FPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat ⟨s₀.gpr .r9 + BitVec.ofNat 64 2048, 16⟩ := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.ofF h0'
  exact finalize_relG (AesCall.free v f fun S => ⟨S + BitVec.ofNat 64 2048, 16⟩) (FPre.ofF h0) hp' q7

theorem finalizeS_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) :
    ConstantTime isa finalizeX86_64S.pre finalizeX86_64S.pub (finalize v.callee) := by
  intro s₀ s₀' _ _ _ _ h0 h0' hq e₁ e₂
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp' : FPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat ⟨s₀.gpr .r9 + BitVec.ofNat 64 512, 1664⟩ := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.ofS h0'
  exact (finalize_relG (AesCall.small v f) (FPre.ofS h0) hp' q7 _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem finalizeF_ct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) :
    ConstantTime isa finalizeX86_64F.pre finalizeX86_64F.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalizeF_rel v f h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem finalize_ct (v : Ctr32Impl) :
    ConstantTime isa finalizeX86_64.pre finalizeX86_64.pub (finalize v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (finalize_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64

end

/-!
# AES-CMAC on x86-64: `Verified`

Correctness and constant time (for any implementation `v` of `vg_aes_ctr32`),
a state satisfying each precondition, and the shared contracts of
`Spec/Cmac/Contract.lean` (with 8 bytes of stack, for the return address of
the call of `vg_aes_ctr32`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem update_mx (v : Ctr32Impl) : (update v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [update, body, Code.allInstrs,
    ctrCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) v.mxcsr]
  decide +kernel

theorem subkeys_mx (v : Ctr32Impl) : (subkeys v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [subkeys, Code.allInstrs,
    ctrCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) v.mxcsr]
  decide +kernel

theorem finalize_mx (v : Ctr32Impl) : (finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finalize, Code.allInstrs,
    ctrCall_allInstrs (p := fun i => !loadsMxcsr i) (fun _ => rfl) v.mxcsr]
  decide +kernel

theorem update_spSafe (v : Ctr32Impl) : (update v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [update, body, Code.all,
    ctrCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) v.spSafe]
  decide +kernel

theorem subkeys_spSafe (v : Ctr32Impl) : (subkeys v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [subkeys, Code.all,
    ctrCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) v.spSafe]
  decide +kernel

theorem finalize_spSafe (v : Ctr32Impl) : (finalize v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finalize, Code.all,
    ctrCall_all (p := fun i => !X86_64.isa.writesSp i) (fun _ => rfl) v.spSafe]
  decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := update_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (update_mx v) he hg, hp⟩

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysX86_64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := subkeys_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (subkeys_mx v) he hg, hp⟩

theorem subkeysF_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : subkeysX86_64F.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := subkeysF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (subkeys_mx v) he hg, hp⟩

theorem finalizeF_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Free v.callee) (s : State)
    (hs : finalizeX86_64F.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeX86_64F.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalizeF_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

theorem updateS_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : updateX86_64S.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := updateS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (update_mx v) he hg, hp⟩

theorem subkeysS_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : subkeysX86_64S.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := subkeysS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (subkeys_mx v) he hg, hp⟩

theorem finalizeS_correct (v : Ctr32Impl) (f : Proof.Aes.X86_64.Ctr32Small v.callee) (s : State)
    (hs : finalizeX86_64S.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeX86_64S.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalizeS_wp v f hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

end VG.Proof.CmacAes.X86_64

end

end

/-!
# Implementations of `vg_cmac_aes_update` on x86-64

An `UpdateImpl` is what a function that calls `vg_cmac_aes_update` needs of
it, so that its proof holds for every implementation: each is a variant of
the interface `CmacAesUpdate` on x86-64 (`Variants/CmacAesUpdate/X86_64/`),
and each caller (in `Generic/CmacAesUpdate/X86_64/`) is emitted once for
each of them (see `TCB/Emit.lean`). Every implementation is proven against
the same contract, `updateX86_64`, makes at most one level of calls, and
uses at most 8 bytes of stack (the return address of its call of
`vg_aes_ctr32`). One that never touches its scratch buffer also gives its
contract without one (`free`), and one that never touches its first 512
bytes, its contract without those (`small`: the chaining by calls of an
implementation of `vg_aes_ctr32` that uses 1480 bytes of working space),
so that a caller of it alone sets aside no more.

There are two: the chaining by calls of the bitsliced `vg_aes_ctr32` on one
block at a time (`UpdateImpl.ctr32 .scalar`, `vg_cmac_aes_update`), and the
chaining in AES-NI registers (`UpdateImpl.aesniCbc`,
`vg_cmac_aes_update_aesni`), faster than the chaining by calls of an
AES-NI or VAES `vg_aes_ctr32` for any number of blocks. Each comes with the
implementation of `vg_aes_ctr32` that goes with it (`ctr`), for the callers
that also run counter mode or call the other CMAC functions (AES-CCM,
AES-SIV): the one it is built on, or for the chaining in registers,
`vg_aes_ctr32_aesni`, which needs no CPU features the AES-NI CPUs it is
chosen for lack.
-/

@[expose] public section

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- `updateX86_64` without the scratch buffer, for an implementation that
never touches it: its callers then need not set one aside. -/
def updateX86_64F : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched, data] ∧ s.wr = [state] ∧
      sched.Disjoint state ∧ data.Disjoint state ∧ ret.Disjoint state ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint state ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post := updateX86_64.post
  pub := updateX86_64.pub

/-- What an implementation of `vg_cmac_aes_update` that never touches its
scratch buffer gives: its contract without one (`updateX86_64F`). -/
structure UpdateFree (callee : Impl.CmacAes.X86_64.Update) : Type where
  ok : ∀ s, updateX86_64F.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ updateX86_64F.post s s'
  ct : ConstantTime isa updateX86_64F.pre updateX86_64F.pub callee.code

/-- What an implementation of `vg_cmac_aes_update` that never touches the
first 512 bytes of its scratch buffer gives: its contract without them
(`updateX86_64S`). -/
structure UpdateSmall (callee : Impl.CmacAes.X86_64.Update) : Type where
  ok : ∀ s, updateX86_64S.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ updateX86_64S.post s s'
  ct : ConstantTime isa updateX86_64S.pre updateX86_64S.pub callee.code

/-- An implementation of `vg_cmac_aes_update` on x86-64. -/
structure UpdateImpl where
  /-- Its symbol and code. -/
  callee : Impl.CmacAes.X86_64.Update
  /-- It makes at most one level of calls. -/
  depth : callee.code.depth ≤ 1
  ok : ∀ s, updateX86_64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s'
  ct : ConstantTime isa updateX86_64.pre updateX86_64.pub callee.code
  /-- It never writes the stack pointer. -/
  nosp : NoSp callee.code
  /-- It never loads MXCSR. -/
  mxcsr : callee.code.allInstrs (fun i => !loadsMxcsr i) = true
  spSafe : callee.code.all (fun i => !isa.writesSp i) = true
  /-- It uses at most 8 bytes of stack. -/
  xdepth : callee.code.x86_64Depth ≤ 8
  /-- What the names of its callers' instances end with (e.g. `_aesni`;
  nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its code requires, which its callers require too. -/
  features : List String
  /-- The implementation of `vg_aes_ctr32` that goes with it, for callers
  that also call it or the other CMAC functions made with it. -/
  ctr : Ctr32Impl
  /-- Its contract without a scratch buffer, if it never touches one. -/
  free : Option (UpdateFree callee) := none
  /-- Its contract without the first 512 bytes of its scratch buffer, if it
  never touches them. -/
  small : Option (UpdateSmall callee) := none
  /-- The level of its vector instructions. -/
  level : Impl.Scrub.X86_64.VecLevel
  /-- What the cleanup of a function that calls it needs of its code, at
  that level (`X86_64.Scrub.calleeSide`). -/
  side : X86_64.Scrub.calleeSide callee.code level.level 8 = true

/-- How much working space it needs, which picks the code and frame of its
callers (`Impl.Aes.X86_64.Space`). -/
def UpdateImpl.space (v : UpdateImpl) : Impl.Aes.X86_64.Space :=
  match v.free, v.small with
  | some _, _ => .free
  | none, some _ => .small
  | none, none => .full

theorem update_nosp (v : Ctr32Impl) : NoSp (Impl.CmacAes.X86_64.update v.callee) := by
  have h : (Impl.CmacAes.X86_64.update v.callee).allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
    have hv : v.callee.code.allInstrs (fun i => !Taint.clobbers i .rsp) = true := by
      rw [Code.allInstrs_eq, List.all_eq_true]
      exact fun i hi => by simp [v.nosp i hi]
    simp only [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.allInstrs,
      ctrCall_allInstrs (p := fun i => !Taint.clobbers i .rsp) (fun _ => rfl) hv]
    decide +kernel
  rw [Code.allInstrs_eq] at h
  exact fun i hi => by simpa using List.all_eq_true.mp h i hi

theorem update_depth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.update v.callee).depth = 1 := by
  show max 0 (max (max 0 (max 0 (max (Impl.CmacAes.X86_64.ctrCall v.callee).depth 0))) 0) = 1
  rw [ctrCall_depth, v.depth]; rfl

theorem update_xdepth (v : Ctr32Impl) : (Impl.CmacAes.X86_64.update v.callee).x86_64Depth = 8 := by
  simp [Impl.CmacAes.X86_64.update, Impl.CmacAes.X86_64.body, Code.x86_64Depth, ctrCall_xdepth, v.noStack]

/-- `vg_cmac_aes_update` over `v` meets what the cleanup of its callers needs:
from its code over a stub, and `v`'s (`X86_64.Scrub.calleeSide_of_fill`). -/
theorem update_side (v : Ctr32Impl) :
    X86_64.Scrub.calleeSide (Impl.CmacAes.X86_64.update v.callee) v.level.level 8 = true :=
  X86_64.Scrub.calleeSide_of_fill (n := fun _ => 0)
    (a := Impl.CmacAes.X86_64.update ⟨"", .block [], v.callee.scrOff⟩) (by have := v.side; fill_calls) (Nat.zero_le _)
    (by rcases v.scrOk with h | h <;> rw [h] <;> lit_decide)

/-- The chaining by calls of `v` on one block at a time,
`vg_cmac_aes_update` with `v`'s suffix. -/
def UpdateImpl.ctr32 (v : Ctr32Impl) : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update" ++ v.suffix, Impl.CmacAes.X86_64.update v.callee⟩
  depth := by rw [update_depth]
  ok := update_correct v
  ct := update_ct v
  nosp := update_nosp v
  mxcsr := update_mx v
  spSafe := update_spSafe v
  xdepth := by rw [update_xdepth]
  suffix := v.suffix
  features := v.features
  ctr := v
  small := v.small.map fun f => ⟨updateS_correct v f, updateS_ct v f⟩
  level := v.level
  side := update_side v

theorem aesniCbc_nosp : NoSp Impl.CmacAes.X86_64.AesNi.update := by
  have : ((instrs Impl.CmacAes.X86_64.AesNi.update).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  exact fun i hi => by simpa using List.all_eq_true.mp this i hi

theorem aesniCbc_pre {s : State} (h : updateX86_64F.pre s) : AesNi.cbcX86_64.pre s :=
  let ⟨a, b, _, _, c, _, _, _, _, d, e⟩ := h
  ⟨a, by rw [b]; exact List.mem_singleton_self _, c, d, e⟩

/-- The chaining in AES-NI registers, `vg_cmac_aes_update_aesni`, which goes
with `vg_aes_ctr32_aesni`. -/
def UpdateImpl.aesniCbc : UpdateImpl where
  callee := ⟨"vg_cmac_aes_update" ++ "_aesni", Impl.CmacAes.X86_64.AesNi.update⟩
  depth := by decide +kernel
  ok := AesNi.update_ok
  ct := AesNi.update_ct
  nosp := aesniCbc_nosp
  mxcsr := by decide +kernel
  spSafe := Code.all_of_spTest (by decide +kernel)
  xdepth := by decide +kernel
  suffix := "_aesni"
  features := ["aes"]
  ctr := .aesni
  level := .sse
  side := by lit_decide
  free := some ⟨fun s hs => AesNi.correct s (aesniCbc_pre hs),
    fun _ _ _ _ _ _ h₁ h₂ hq => AesNi.ct _ _ _ _ _ _ (aesniCbc_pre h₁) (aesniCbc_pre h₂) hq⟩

end VG.Proof.CmacAes.X86_64
