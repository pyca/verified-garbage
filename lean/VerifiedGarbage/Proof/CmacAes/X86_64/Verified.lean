import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.CmacAes.X86_64.Subkeys
import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect

section

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` is constant time

Two runs from states that agree on the public arguments are related piece by
piece (`RelCT`): the taint analysis covers the code between the calls, from
the registers the correctness proof pins to the public arguments (`LInv`), and
each call of `vg_aes_ctr32` is constant time by its own proof (`ctr_rel`).
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
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv s₀ k s₁) (h₂ : LInv s₀' k s₂) :
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
  pre : CallPre s (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem bodyMid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.saved .r13 (by simp [calleeSaved]), h.r13],
      by rw [hb.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hb.saved .rsp (by simp [calleeSaved]), h.rsp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)

theorem body_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateX86_64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) (body v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13, .r14]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1 h.2.2)) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨bodyMid_wp hp h.1 h.2.1, bodyMid_wp hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (ctr_rel v (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.pre, by
        rw [pub_W hq, pub_S hq, pub_St hq, pub_R hq]; exact h.2.pre,
        by rw [h.1.rsp, h.2.rsp, pub_rsp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .r13 (by simp [calleeSaved]), h.1.r13],
          by rw [hc.saved .r14 (by simp [calleeSaved]), h.1.r14]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
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
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂

theorem loop_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateX86_64.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop (body v.callee) .ne)
      fun s₁ s₂ => LInv s₀ (N s₀) s₁ ∧ LInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (body_ct v hp hp' hq k).wp
    (F₁ := fun (s' : State) => LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)))
    (F₂ := fun (s' : State) => LInv s₀' (k + 1) s' ∧ s'.zf = some (decide (N s₀' - (k + 1) = 0)))
    fun _ _ h => ⟨body_ok v hp h.1 h.2.1, body_ok v hp' (by rw [← hN]; exact h.1) h.2.2⟩
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
      omega_arith
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega_arith, k + 1, rfl, by omega_arith, l₁, l₂⟩

/-! ## The whole function -/

theorem update_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : updateX86_64.pre s₀) (h0' : updateX86_64.pre s₀')
    (hq : updateX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True := by
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
    (F₁ := fun (s : State) => LInv s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv s₀' 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) _
    (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop (body v.callee) .ne))
      (fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
    · refine (nil.wp (F₁ := LInv s₀ (N s₀)) (F₂ := LInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct v hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1.1, h.1.2.1⟩)
        fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega_arith
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r15, h.2.r15, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

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
(`ctr_rel`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What is known between the code before the call and the call. -/
structure SMid (s₀ : State) (W K S : Addr) (R : Nat) (s : State) : Prop where
  pre : CallPre s W (S + BitVec.ofNat 64 2048) K S R
  rbx : s.gpr .rbx = K
  rbp : s.gpr .rbp = S
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem smid_wp {s₀ : State} {W K S : Addr} {R : Nat} (hp : SPre s₀ W K S R) :
    WP isa (.block subkeysPre) s₀ (SMid s₀ W K S R) := by
  have sw := hp.scr_wrap
  have kw := hp.k_wrap
  have inS (d : Nat) (h : d + 8 ≤ 2176) : InRegions s₀.wr (s₀.gpr .rcx + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.rcx]; exact in_rw (r := ⟨S, 2176⟩) (by simp) (Offset.contains_base _ h (by omega_arith))
  have inK (d : Nat) (h : d + 8 ≤ 32) : InRegions s₀.wr (s₀.gpr .rdx + BitVec.ofNat 64 d) 8 := by
    rw [hp.wr, hp.rdx]; exact in_rw (r := ⟨K, 32⟩) (by simp) (Offset.contains_base _ h (by omega_arith))
  obtain ⟨s₁, run₁, rdi₁, rsi₁, rdx₁, rcx₁, r8₁, r9₁, rbx₁, rbp₁, cs₁, mem₁, rd₁, wr₁⟩ :=
    subkeysPre_ok s₀ (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide)) (inS _ (by decide))
      (inK _ (by decide)) (inK _ (by decide))
  have rsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := cs₁ .rsp (by simp [calleeSaved]) (by decide) (by decide)
  exact WP.of_runBlock ⟨s₁, run₁,
    callPre_of hp rdi₁ rsi₁ rdx₁ rcx₁ r8₁ r9₁ rsp₁ mem₁ rd₁ wr₁, by rw [rbx₁, hp.rdx], by rw [rbp₁, hp.rcx], rsp₁⟩

theorem subkeys_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : subkeysX86_64.pre s₀)
    (h0' : subkeysX86_64.pre s₀') (hq : subkeysX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (subkeys v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := hq
  have hp := SPre.of h0
  have hp' : SPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat := by
    rw [q1, q2, q3, q4]; exact SPre.of h0'
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
    (F₁ := SMid s₀ _ _ _ _) (F₂ := SMid s₀' _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨smid_wp hp, smid_wp hp'⟩
  have c := (ctr_rel v (P := fun s₁ s₂ =>
      SMid s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat s₁ ∧
      SMid s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .rsi).toNat s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.pre, h.2.pre, by rw [h.1.rsp, h.2.rsp, q5]⟩).wp
    (F₁ := fun (s : State) => s.gpr .rbx = s₀.gpr .rdx ∧ s.gpr .rbp = s₀.gpr .rcx)
    (F₂ := fun (s : State) => s.gpr .rbx = s₀.gpr .rdx ∧ s.gpr .rbp = s₀.gpr .rcx) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.1.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.1.rbp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .rbx (by simp [calleeSaved]), h.2.rbx],
          by rw [hc.saved .rbp (by simp [calleeSaved]), h.2.rbp]⟩⟩
  have b := RelCT.taint (A := taint)
    (P := fun s₁ s₂ => (s₁.gpr .rbx = s₀.gpr .rdx ∧ s₁.gpr .rbp = s₀.gpr .rcx) ∧
      (s₂.gpr .rbx = s₀.gpr .rdx ∧ s₂.gpr .rbp = s₀.gpr .rcx)) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1, h.2.1]
      · rw [h.1.2, h.2.2]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

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
constant time by its own proof (`ctr_rel`), its arguments pinned by the
correctness proof (`FMid`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

theorem finalize_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : finalizeX86_64.pre s₀)
    (h0' : finalizeX86_64.pre s₀') (hq : finalizeX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (finalize v.callee) fun _ _ => True := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := hq
  have hp := FPre.of h0
  have hp' : FPre s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat
      (s₀.gpr .rsi).toNat := by
    rw [q1, q2, q3, q4, q5, q6]; exact FPre.of h0'
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]) finPre h).isSome =
      true := ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> with_reducible assumption) hA).wp
    (F₁ := FMid s₀ _ _ _ _ _ _) (F₂ := FMid s₀' _ _ _ _ _ _) fun a b h => by
      obtain ⟨rfl, rfl⟩ := h; exact ⟨finPre_wp hp, finPre_wp hp'⟩
  have c := ctr_rel v (P := fun s₁ s₂ =>
      FMid s₀ (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₁ ∧
      FMid s₀' (s₀.gpr .rdi) (s₀.gpr .rdx) (s₀.gpr .rcx) (s₀.gpr .r9) (s₀.gpr .r8).toNat (s₀.gpr .rsi).toNat s₂)
    fun s₁ s₂ h => ⟨_, _, _, _, _, h.1.pre, h.2.pre, by
      rw [h.1.saved _ (by simp [calleeSaved]), h.2.saved _ (by simp [calleeSaved]), q7]⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq c

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
  simp only [update, body, Code.allInstrs, v.mxcsr]; decide +kernel

theorem subkeys_mx (v : Ctr32Impl) : (subkeys v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [subkeys, Code.allInstrs, v.mxcsr]; decide +kernel

theorem finalize_mx (v : Ctr32Impl) : (finalize v.callee).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [finalize, Code.allInstrs, v.mxcsr]; decide +kernel

theorem update_spSafe (v : Ctr32Impl) : (update v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [update, body, Code.all, v.spSafe]; decide +kernel

theorem subkeys_spSafe (v : Ctr32Impl) : (subkeys v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [subkeys, Code.all, v.spSafe]; decide +kernel

theorem finalize_spSafe (v : Ctr32Impl) : (finalize v.callee).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [finalize, Code.all, v.spSafe]; decide +kernel

theorem update_correct (v : Ctr32Impl) (s : State) (hs : updateX86_64.pre s) :
    ∃ t s', Exec isa (update v.callee) s t s' ∧ abiPreserved s s' ∧ updateX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := update_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (update_mx v) he hg, hp⟩

theorem subkeys_correct (v : Ctr32Impl) (s : State) (hs : subkeysX86_64.pre s) :
    ∃ t s', Exec isa (subkeys v.callee) s t s' ∧ abiPreserved s s' ∧ subkeysX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := subkeys_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (subkeys_mx v) he hg, hp⟩

theorem finalize_correct (v : Ctr32Impl) (s : State) (hs : finalizeX86_64.pre s) :
    ∃ t s', Exec isa (finalize v.callee) s t s' ∧ abiPreserved s s' ∧ finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, hg, hp⟩ := finalize_wp v hs
  exact ⟨t, s', he, abiPreserved_of_exec (finalize_mx v) he hg, hp⟩

/-- A state satisfying `vg_cmac_aes_update`'s precondition (with no blocks). -/
def updSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem update_verified (v : Ctr32Impl) :
    Verified X86_64.target (update v.callee) (Spec.Cmac.aesUpdateContract X86_64.abi 8) :=
  Verified.of_correct (update_correct v) (update_ct v) (by
    sig_implies [Spec.Cmac.aesUpdateContract, Spec.Cmac.aesUpdateSig, updateX86_64, X86_64.abi,
      X86_64.argRegs] [updSat] using updSat)

/-- A state satisfying `vg_cmac_aes_subkeys`'s precondition. -/
def subSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 240⟩]
  wr := [⟨0x2000, 32⟩, ⟨0x4000, 2176⟩]

theorem subkeys_verified (v : Ctr32Impl) :
    Verified X86_64.target (subkeys v.callee) (Spec.Cmac.aesSubkeysContract X86_64.abi 8) :=
  Verified.of_correct (subkeys_correct v) (subkeys_ct v) (by
    sig_implies [Spec.Cmac.aesSubkeysContract, Spec.Cmac.aesSubkeysSig, subkeysX86_64, X86_64.abi,
      X86_64.argRegs] [subSat] using subSat)

/-- A state satisfying `vg_cmac_aes_finalize`'s precondition (with no last bytes). -/
def finSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 10 | .rdx => 0x2000 | .rcx => 0x3000 | .r9 => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 272⟩, ⟨0x3000, 0⟩]
  wr := [⟨0x2000, 16⟩, ⟨0x4000, 2176⟩]

theorem finalize_verified (v : Ctr32Impl) :
    Verified X86_64.target (finalize v.callee) (Spec.Cmac.aesFinalizeContract X86_64.abi 8) :=
  Verified.of_correct (finalize_correct v) (finalize_ct v) (by
    sig_implies [Spec.Cmac.aesFinalizeContract, Spec.Cmac.aesFinalizeSig, finalizeX86_64, X86_64.abi,
      X86_64.argRegs] [finSat] using finSat)

end VG.Proof.CmacAes.X86_64
