import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Gather.Loop
import VerifiedGarbage.Proof.AesGcm.X86_64.CTBase
import VerifiedGarbage.Proof.Framework.Scratch

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: gathering in constant time

Untrusted: everything here is checked by Lean. Runs are related piece by
piece from given states (`Eq2`), as on x86 (`Proof/AesGcm/X86/Gather/LoopCT.lean`).
Two runs of `gather` whose descriptors agree, from states the correctness
proof describes with the same arguments (`GatherPre`), leak the same trace
(`gather_rel`): the gathering loads the descriptors from where they are
(`r11`), and copies each slice from and to the addresses they give
(`rsi`, `rdi`), with branches on the number of slices and their lengths
(`rcx`, `r9`), registers the correctness proof pins to the same values in
both runs, from which the taint analysis checks each block.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (copyBytes next advance gatherLoop gather)
open VG.Proof.AesGcm.X86_64 (rel_taint)
open VG.Spec.Gcm (gathered gatheredLen)

/-! ## Relating two runs -/

/-- Two runs from `σ₁` and `σ₂`. -/
abbrev Eq2 (σ₁ σ₂ : State) (a b : State) : Prop := a = σ₁ ∧ b = σ₂

/-- Nothing is required of the final states. -/
abbrev TT (_ _ : State) : Prop := True

/-- Then: the next piece, from the states the correctness proofs describe. -/
theorem rel_seq {c₁ c₂ : Prog isa} {σ₁ σ₂ : State} {F₁ F₂ : State → Prop}
    (h₁ : RelCT isa (Eq2 σ₁ σ₂) c₁ TT) (w₁ : WP isa c₁ σ₁ F₁) (w₂ : WP isa c₁ σ₂ F₂)
    (h₂ : ∀ τ₁ τ₂, F₁ τ₁ → F₂ τ₂ → RelCT isa (Eq2 τ₁ τ₂) c₂ TT) :
    RelCT isa (Eq2 σ₁ σ₂) (.seq c₁ c₂) TT := by
  refine RelCT.seq (R := fun a b => F₁ a ∧ F₂ b) ((h₁.wp (F₁ := F₁) (F₂ := F₂) fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab; exact ⟨w₁, w₂⟩).mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  exact h₂ s₁ s₂ hp.1 hp.2 s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

/-- Code the taint analysis checks, from registers the two runs agree on. -/
theorem rel_regs {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r)
    (hc : ∃ hc, (taint.check (Taint.ofRegs rs) c hc).isSome = true) : RelCT isa (Eq2 σ₁ σ₂) c TT :=
  rel_taint rs (fun _ _ hab => by obtain ⟨rfl, rfl⟩ := hab; exact hr) hc

/-- An empty block. -/
theorem rel_skip {σ₁ σ₂ : State} : RelCT isa (Eq2 σ₁ σ₂) (.block []) TT := by
  intro x y t₁ t₂ x' y' _ e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂
      exact ⟨rfl, trivial⟩

/-- A branch both runs take the same way. -/
theorem rel_ite {c : Cond} {t e : Prog isa} {σ₁ σ₂ : State} {b : Bool} (e₁ : isa.eval c σ₁ = some b)
    (e₂ : isa.eval c σ₂ = some b) (ht : b = true → RelCT isa (Eq2 σ₁ σ₂) t TT)
    (hf : b = false → RelCT isa (Eq2 σ₁ σ₂) e TT) : RelCT isa (Eq2 σ₁ σ₂) (.ite c t e) TT := by
  refine RelCT.ite (fun a b' hab => by obtain ⟨rfl, rfl⟩ := hab; rw [e₁, e₂]) ?_ ?_
  · cases b
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h
    · exact (ht rfl).mono (fun _ _ h => h.1) fun _ _ h => h
  · cases b
    · exact (hf rfl).mono (fun _ _ h => h.1) fun _ _ h => h
    · exact RelCT.of_false fun a b' h => by obtain ⟨⟨rfl, -⟩, h⟩ := h; rw [e₁] at h; cases h

/-- Constant time, from related runs from every pair of states. -/
theorem ct_of {pre : State → Prop} {pub : State → State → Prop} {c : Prog isa}
    (h : ∀ σ₁ σ₂, pre σ₁ → pre σ₂ → pub σ₁ σ₂ → RelCT isa (Eq2 σ₁ σ₂) c TT) : ConstantTime isa pre pub c :=
  fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## The descriptors -/

/-- The descriptors agree in two memories: so do the slices they list. -/
theorem desc_agree {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
    (hd : ∀ j < cnt * 16, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j)) {i : Nat} (hi : i ≤ cnt) :
    ∀ a, (Sig.descRegion 64 Src i).Contains a 1 → m₁ a = m₂ a := by
  intro a ha
  simp only [Sig.descRegion, Region.Contains] at ha
  have e : Src + BitVec.ofNat 64 (a - Src).toNat = a := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [← e]
  exact hd _ (by have := Nat.mul_le_mul_right 16 hi; simp only [show 2 * (64 / 8) = 16 from rfl] at ha; omega)

section
variable {m₁ m₂ : Mem} {Src : Addr} {cnt : Nat}
  (hd : ∀ j < cnt * 16, m₁ (Src + BitVec.ofNat 64 j) = m₂ (Src + BitVec.ofNat 64 j))
include hd

theorem gl_agree {i : Nat} (hi : i ≤ cnt) : gatheredLen 64 m₁ Src i = gatheredLen 64 m₂ Src i := by
  simp only [gatheredLen]
  rw [Sig.listed_congr 64 .u8 Src i (desc_agree hd hi)]

theorem desc_word {d : Nat} (h : d + 8 ≤ cnt * 16) :
    m₁.readW (Src + BitVec.ofNat 64 d) 64 = m₂.readW (Src + BitVec.ofNat 64 d) 64 :=
  Mem.readW_congr fun k hk => by
    rw [Offset.add_ofNat_add_ofNat]; exact hd _ (by simp at hk; omega)

theorem sb_agree {i : Nat} (hi : i < cnt) : sb m₁ Src i = sb m₂ Src i :=
  desc_word hd (by omega)

theorem sl_agree {i : Nat} (hi : i < cnt) : sl m₁ Src i = sl m₂ Src i := by
  simp only [sl]
  rw [Offset.add_ofNat_add_ofNat, desc_word hd (by omega)]

end

/-! ## Gathering -/

section
variable {t₁ t₂ : State} {Src Dst : Addr} {cnt L : Nat}
  (hd : ∀ j < cnt * 16, t₁.mem (Src + BitVec.ofNat 64 j) = t₂.mem (Src + BitVec.ofNat 64 j))
  (h₁ : GatherPre t₁ Src Dst cnt L) (h₂ : GatherPre t₂ Src Dst cnt L)
include hd h₁ h₂

/-- One iteration of the loop, in two runs. -/
theorem body_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copyBytes (.block advance)))
      (fun u₁ u₂ => (GInv t₁ u₁ Src Dst cnt (i + 1) ∧ u₁.zf = some (decide (i + 1 = cnt))) ∧
        (GInv t₂ u₂ Src Dst cnt (i + 1) ∧ u₂.zf = some (decide (i + 1 = cnt)))) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copyBytes (.block advance))) TT := by
    intro σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨g₁, g₂⟩ e₁ e₂
    refine rel_seq (rel_regs [.r11] (by simp [g₁.r11, g₂.r11]) ⟨_, by taint_decide⟩)
      (next_wp h₁ hi g₁) (next_wp h₂ hi g₂) (fun τ₁ τ₂ n₁ n₂ => ?_) σ₁ σ₂ x₁ x₂ σ₁' σ₂' ⟨rfl, rfl⟩ e₁ e₂
    have p₁ := copyPre_of h₁ hi n₁
    have p₂ := copyPre_of h₂ hi n₂
    rw [← sb_agree hd hi, ← sl_agree hd hi, ← gl_agree hd (Nat.le_of_lt hi)] at p₂
    refine rel_seq (rel_regs [.rsi, .rdi, .rcx] (by simp [p₁.rsi, p₂.rsi, p₁.rdi, p₂.rdi, p₁.rcx, p₂.rcx])
      ⟨_, by taint_decide⟩) (copyBytes_ok τ₁ p₁) (copyBytes_ok τ₂ p₂) fun v₁ v₂ c₁ c₂ => ?_
    refine rel_regs [.rdi, .rcx, .r9] ?_ ⟨_, by taint_decide⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨by rw [c₁.2.1 _ (by decide) (by decide) (by decide), c₂.2.1 _ (by decide) (by decide) (by decide),
        p₁.rdi, p₂.rdi], by rw [c₁.2.1 _ (by decide) (by decide) (by decide),
        c₂.2.1 _ (by decide) (by decide) (by decide), p₁.rcx, p₂.rcx], ?_⟩
    rw [c₁.2.1 _ (by decide) (by decide) (by decide), c₂.2.1 _ (by decide) (by decide) (by decide), n₁.r9, n₂.r9]
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ => ⟨body_wp h₁ hi g₁, body_wp h₂ hi g₂⟩).mono (fun _ _ h => h)
    fun _ _ h => h.2

/-- `gatherLoop`, in two runs. -/
theorem gatherLoop_rel (hpos : cnt ≠ 0) : RelCT isa (Eq2 t₁ t₂) gatherLoop TT := by
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv t₁ u₁ Src Dst cnt i ∧ GInv t₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega, GInv.init h₁, GInv.init h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (body_rel hd h₁ h₂ hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨⟨g₁, z₁⟩, ⟨g₂, z₂⟩⟩
    have ev₁ : isa.eval .ne u₁ = some !decide (i + 1 = cnt) := by show u₁.zf.map (!·) = _; rw [z₁]; rfl
    have ev₂ : isa.eval .ne u₂ = some !decide (i + 1 = cnt) := by show u₂.zf.map (!·) = _; rw [z₂]; rfl
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega
    exact ⟨cnt - (i + 1), by omega, i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

/-- `gather`, in two runs. -/
theorem gather_rel : RelCT isa (Eq2 t₁ t₂) gather TT := by
  refine rel_seq (rel_regs [.r9] (by simp [h₁.r9, h₂.r9]) ⟨_, by taint_decide⟩)
    (cmp_ok t₁ h₁.r9 h₁.hcnt) (cmp_ok t₂ h₂.r9 h₂.hcnt) fun τ₁ τ₂ ⟨z₁, g₁, m₁, rd₁, wr₁⟩ ⟨z₂, g₂, m₂, rd₂, wr₂⟩ => ?_
  refine rel_ite (b := decide (cnt = 0)) z₁ z₂ (fun _ => rel_skip) fun hf => ?_
  exact gatherLoop_rel (by rw [m₁, m₂]; exact hd) (h₁.of_eq g₁ m₁ rd₁ wr₁) (h₂.of_eq g₂ m₂ rd₂ wr₂)
    (by simpa using hf)

end

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
