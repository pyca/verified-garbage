module

public import VerifiedGarbage.Proof.Gather.PPC64LE.Loop
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Scratch
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Proof.Gather.PPC64LE.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Scratch
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Gathering a list of slices, PPC64LE: constant time

Two runs of `gather` whose descriptors agree, from states the correctness
proof describes with the same arguments (`GatherPre`), leak the same trace
(`gather_rel`): the gathering loads the descriptors from where they are, and
copies each slice from and to the addresses they give, with branches on the
number of slices and their lengths (by the taint analysis from the registers
the correctness proof pins to the same values in both runs). As on AArch64
(`Proof/AesGcm/AArch64/Gather/LoopCT.lean`), with the pieces that relate two
runs (`rel_seq`, `rel_taint`, `rel_ite`) for PPC64LE.
-/

@[expose] public section

namespace VG.Proof.Gather.PPC64LE

open VG VG.PPC64LE VG.Impl.Gather.PPC64LE
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
theorem rel_taint {c : Prog isa} {σ₁ σ₂ : State} (rs : List Reg) (hsp : σ₁.sp = σ₂.sp)
    (hr : ∀ r ∈ rs, σ₁.gpr r = σ₂.gpr r) {hc : VG.Taint.Hint taint.T}
    (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true) :
    RelCT isa (Eq2 σ₁ σ₂) c TT :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hab => by
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨hsp, fun r h' => hr r (Taint.mem_ofRegs.mp h')⟩) h

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
  exact hd _ (by have := Nat.mul_le_mul_right 16 hi; omega)

section
variable {e₁ e₂ : State} {Src Dst : Addr} {cnt L : Nat}
  (hd : ∀ j < cnt * 16, e₁.mem (Src + BitVec.ofNat 64 j) = e₂.mem (Src + BitVec.ofNat 64 j))
include hd

theorem gl_agree {i : Nat} (hi : i ≤ cnt) : gatheredLen 64 e₁.mem Src i = gatheredLen 64 e₂.mem Src i := by
  simp only [gatheredLen]
  rw [Sig.listed_congr 64 .u8 Src i (desc_agree hd hi)]

theorem desc_word {d : Nat} (h : d + 8 ≤ cnt * 16) :
    e₁.mem.readW (Src + BitVec.ofNat 64 d) 64 = e₂.mem.readW (Src + BitVec.ofNat 64 d) 64 :=
  Mem.readW_congr fun k hk => by
    rw [Offset.add_ofNat_add_ofNat]; exact hd _ (by simp at hk; omega)

theorem sb_agree {i : Nat} (hi : i < cnt) : sb e₁.mem Src i = sb e₂.mem Src i := desc_word hd (by omega)

theorem sl_agree {i : Nat} (hi : i < cnt) : sl e₁.mem Src i = sl e₂.mem Src i := by
  simp only [sl, Offset.add_ofNat_add_ofNat]
  rw [desc_word hd (by omega)]

variable (h₁ : GatherPre e₁ Src Dst cnt L) (h₂ : GatherPre e₂ Src Dst cnt L) (hsp : e₁.sp = e₂.sp)
include h₁ h₂ hsp

/-- One iteration of the loop, in two runs. -/
theorem body_rel {i : Nat} (hi : i < cnt) :
    RelCT isa (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copySlice (.block [.subi .r8 .r8 1])))
      (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt (i + 1) ∧ GInv e₂ u₂ Src Dst cnt (i + 1)) := by
  have hT : RelCT isa (fun u₁ u₂ => GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i)
      (.seq (.block next) (.seq copySlice (.block [.subi .r8 .r8 1]))) TT := by
    intro σ₁ σ₂ t₁ t₂ σ₁' σ₂' ⟨g₁, g₂⟩ x₁ x₂
    refine rel_seq (rel_taint [.r7, .r8, .r9] (by rw [g₁.keep.sp, g₂.keep.sp, hsp])
      (by
        simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        exact ⟨by rw [g₁.r7, g₂.r7], by rw [g₁.r8, g₂.r8], by rw [g₁.r9, g₂.r9, gl_agree hd (Nat.le_of_lt hi)]⟩)
      (by taint_decide)) (next_wp h₁ hi g₁) (next_wp h₂ hi g₂) (fun τ₁ τ₂ n₁ n₂ => ?_)
      σ₁ σ₂ t₁ t₂ σ₁' σ₂' ⟨rfl, rfl⟩ x₁ x₂
    exact rel_taint [.r3, .r4, .r7, .r8, .r9] (by rw [n₁.keep.sp, n₂.keep.sp, hsp])
      (by
        simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
        exact ⟨by rw [n₁.r3, n₂.r3, sb_agree hd hi], by rw [n₁.r4, n₂.r4, sl_agree hd hi],
          by rw [n₁.r7, n₂.r7], by rw [n₁.r8, n₂.r8],
          by rw [n₁.r9, n₂.r9, gl_agree hd (Nat.le_of_lt hi)]⟩)
      (by taint_decide)
  exact (hT.wp fun u₁ u₂ ⟨g₁, g₂⟩ =>
    ⟨WP.seq (WP.mono (next_wp h₁ hi g₁) fun _ n => rest_wp h₁ hi n),
      WP.seq (WP.mono (next_wp h₂ hi g₂) fun _ n => rest_wp h₂ hi n)⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `gather`, in two runs. -/
theorem gather_rel : RelCT isa (Eq2 e₁ e₂) gather TT := by
  have hc := h₁.hcnt
  refine rel_ite (eval_zero h₁.r8 h₁.hcnt) (eval_zero h₂.r8 h₂.hcnt)
    (fun _ => by exact rel_taint [] hsp (by simp) (by taint_decide)) (fun hf => ?_)
  have hpos : cnt ≠ 0 := by simpa using hf
  refine (RelCT.loop (Q := TT) (fun n u₁ u₂ => ∃ i, n = cnt - i ∧ i < cnt ∧
      GInv e₁ u₁ Src Dst cnt i ∧ GInv e₂ u₂ Src Dst cnt i) (fun n => ?_) (cnt - 0)).mono
    (fun a b ⟨ha, hb⟩ => by subst ha hb; exact ⟨0, rfl, by omega, GInv.init h₁, GInv.init h₂⟩) fun _ _ h => h
  refine RelCT.exists_ fun i => ?_
  by_cases hin : n = cnt - i ∧ i < cnt
  · obtain ⟨rfl, hi⟩ := hin
    refine (body_rel hd h₁ h₂ hsp hi).mono (fun _ _ h => h.2.2) ?_
    rintro u₁ u₂ ⟨g₁, g₂⟩
    have ev₁ := eval_nonzero (r := .r8) (a := cnt - (i + 1)) g₁.r8 (by omega)
    have ev₂ := eval_nonzero (r := .r8) (a := cnt - (i + 1)) g₂.r8 (by omega)
    refine ⟨by rw [ev₁, ev₂], fun _ => trivial, fun ht => ?_⟩
    rw [ev₁] at ht
    have : i + 1 < cnt := by simp at ht; omega
    exact ⟨cnt - (i + 1), by omega, i + 1, rfl, this, g₁, g₂⟩
  · exact RelCT.of_false fun _ _ h => hin ⟨h.1, h.2.1⟩

end

end VG.Proof.Gather.PPC64LE
