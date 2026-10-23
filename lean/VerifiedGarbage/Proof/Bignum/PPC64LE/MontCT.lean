module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFn
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint

/-!
# Montgomery multiplication on PPC64LE: constant time

The taint analysis treats memory as secret, so the bases loaded from the
header are secret to it although they are public. Two runs are related by
`Two Φ` when both satisfy `Φ d` for the same public data `d`, with the same
stack pointer; each piece of `mul` is checked by the taint analysis from the
registers that `Φ d` fixes (`two_taint`), and what each run satisfies after
it follows from correctness (`two_post`): after `args` the addresses of the
header's words, after `loads` the bases, `w` and the counter, and the scratch
buffer's address throughout.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Impl.Bignum.PPC64LE VG.Impl.Bignum

/-- Both runs satisfy `Φ a`, for the same `a`, with the same stack pointer. -/
def Two {α : Type} (Φ : α → State → Prop) (s₁ s₂ : State) : Prop := ∃ a, Φ a s₁ ∧ Φ a s₂ ∧ s₁.sp = s₂.sp

theorem two_post {α : Type} {Φ Ψ : α → State → Prop} {c : Prog isa}
    (hct : RelCT isa (Two Φ) c fun _ _ => True) (hw : ∀ a s, Φ a s → WP isa c s (Ψ a)) :
    RelCT isa (Two Φ) c (Two Ψ) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, -⟩ := hct _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨a, h₁, h₂, hsp⟩ := hp
  obtain ⟨_, u₁, x₁, y₁⟩ := hw a s₁ h₁
  obtain ⟨_, u₂, x₂, y₂⟩ := hw a s₂ h₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ x₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ x₂
  exact ⟨ht, a, y₁, y₂, by rw [(Exec.rdwr e₁).2.2, (Exec.rdwr e₂).2.2, hsp]⟩

/-- `Φ a` fixes the registers `rs`. -/
def Pins {α : Type} (Φ : α → State → Prop) (rs : List Reg) : Prop :=
  ∀ a s₁ s₂, Φ a s₁ → Φ a s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r

theorem two_taint {α : Type} {Φ : α → State → Prop} {c : Prog isa} (rs : List Reg) (hpin : Pins Φ rs)
    {hc : VG.Taint.Hint T} (h : (taint.check (ofRegs rs) c hc).isSome = true) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  RelCT.taint (A := taint) (ofRegs rs)
    (fun _ _ ⟨a, h₁, h₂, hsp⟩ => ⟨hsp, fun r hr => hpin a _ _ h₁ h₂ r (RegSet.mem_ofList.mp hr)⟩) h

/-- On entry, with the public data `d`. -/
def P0 (d : FnData) (s : State) : Prop := fnContract.pre s ∧ dataOf s = d

/-- After the arithmetic. -/
def P4 (d : FnData) (s : State) : Prop := s.gpr .r21 = d.S

theorem pins_P0 : Pins P0 [.r8] := by
  rintro d s₁ s₂ ⟨-, h₁⟩ ⟨-, h₂⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  have e₁ := congrArg FnData.S h₁
  have e₂ := congrArg FnData.S h₂
  simp only [dataOf] at e₁ e₂
  rw [e₁, e₂]

theorem pins_P1 : Pins P1 [] := by
  intro _ _ _ _ _ r hr; simp at hr

theorem pins_P2 : Pins P2 [.r3, .r5, .r6, .r7, .r21] := by
  rintro d s₁ s₂ ⟨-, a3, a5, a6, a7, a21⟩ ⟨-, b3, b5, b6, b7, b21⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [a3, b3]
  · rw [a5, b5]
  · rw [a6, b6]
  · rw [a7, b7]
  · rw [a21, b21]

theorem pins_P3 : Pins P3 [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r21] := by
  rintro d s₁ s₂ ⟨-, a5, a6, a7, a8, a9, a10, a11, a4, -, a21⟩ ⟨-, b5, b6, b7, b8, b9, b10, b11, b4, -, b21⟩
    r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a4, b4]
  · rw [a5, b5]
  · rw [a6, b6]
  · rw [a7, b7]
  · rw [a8, b8]
  · rw [a9, b9]
  · rw [a10, b10]
  · rw [a11, b11]
  · rw [a21, b21]

theorem pins_P4 : Pins P4 [.r21] := by
  rintro d s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [h₁, h₂]

theorem save_P {d : FnData} {s : State} (h : P0 d s) : WP isa (.block save) s (P1 d) := by
  obtain ⟨hp, rfl⟩ := h
  exact WP.mono (save_ok s (by rw [hp.2.1]; simp)) fun t hS => (pre_saved hp hS).1

theorem tail_P4 {d : FnData} {s : State} (h : P3 d s) : WP isa tail s (P4 d) :=
  WP.mono (tail_P h) fun _ ⟨_, k⟩ => by
    show _ = _
    rw [k.gpr _ (by decide)]; exact h.2.2.2.2.2.2.2.2.2.2

theorem fn_rel : RelCT isa (Two P0) mul fun _ _ => True := by
  unfold mul
  refine RelCT.seq (two_post (two_taint _ pins_P0 (by taint_decide)) fun _ _ h => save_P h)
    (RelCT.seq (RelCT.seq (two_post (two_taint _ pins_P1 (by taint_decide))
      fun _ _ h => WP.mono (args_P h) fun _ h => h.1)
      (RelCT.seq (two_post (two_taint _ pins_P2 (by taint_decide)) fun _ _ h => WP.mono (loads_P h)
        fun _ h => h.1)
      (two_post (two_taint _ pins_P3 (by taint_decide)) fun _ _ h => tail_P4 h)))
    (two_taint _ pins_P4 (by taint_decide)))

theorem fn_ct : ConstantTime isa fnContract.pre fnContract.pub mul :=
  RelCT.constantTime (fn_rel.mono (fun s t ⟨hs, ht, hsp, h3, h4, h5, h6, h7, h8, hw⟩ =>
    ⟨dataOf s, ⟨hs, rfl⟩, ⟨ht, by
      simp only [dataOf, idx]
      rw [← hw, ← h3, ← h4, ← h5, ← h6, ← h7, ← h8]⟩, hsp⟩) fun _ _ h => h)

end VG.Proof.Bignum.PPC64LE
