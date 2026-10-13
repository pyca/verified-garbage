module

public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Tail
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# One-pass XTS-AES on x86-64: the loops

`constK_ok`: `0x87` into both lanes of `ymm11`. `groups_wp`: from `GInv 0 0`,
the sixteen-block loop (if sixteen blocks are left) reaches `GInv c c` with
fewer than sixteen blocks left.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (constK group)

theorem constK_ok (s : State) : WP isa (.block constK) s fun s' =>
    (∀ l < 2, qword (s'.lane .xmm11 l) 0 = 0x87) ∧ (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [constK, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, fun r h => by simp [State.setReg, State.setV, h], by simp [State.setReg, State.setV],
    by simp [State.setReg, State.setV], by simp [State.setReg, State.setV]⟩
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl <;> simp [State.lane, State.setV, State.setReg, qword] <;> rfl

/-- `GInv` is kept by any change of registers it does not name. -/
theorem GInv.congr {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {b c : Nat} {s s' : State}
    (h : GInv enc KP s₀ b c s) (hg : ∀ r, r ≠ .rax → r ≠ .rcx → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : GInv enc KP s₀ b c s' where
  kp := hst s s' h.kp (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide))
    (hg _ (by decide) (by decide)) (hg _ (by decide) (by decide)) hrd hwr
    (by rw [hm]; exact Frame.refl _ _)
  le := h.le
  r8 := by rw [hg _ (by decide) (by decide), h.r8]
  r9 := by rw [hg _ (by decide) (by decide), h.r9]
  r11 := by rw [hg _ (by decide) (by decide), h.r11]
  r10 := by rw [hg _ (by decide) (by decide), h.r10]
  keep := fun r h1 h2 h3 h4 h5 h6 h7 => by rw [hg r h1 h2, h.keep r h1 h2 h3 h4 h5 h6 h7]
  rd := by rw [hrd, h.rd]
  wr := by rw [hwr, h.wr]
  frame := by rw [hm]; exact h.frame
  data := by rw [hm]; exact h.data
  buf := by rw [hm]; exact h.buf
  rdx := by rw [hg _ (by decide) (by decide), h.rdx]

/-- `cmp r9, 16`. -/
theorem cmp16_ok {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {c : Nat} {s : State}
    (h : GInv enc KP s₀ c c s) :
    WP isa (.block [.alu .cmp .r9 (.imm 16)]) s fun s' =>
      GInv enc KP s₀ c c s' ∧ s'.cf = some (decide (N s₀ - c < 16)) := by
  have e16 : BitVec.signExtend 64 (16 : BitVec 32) = 16 := by decide
  have hr9 := h.r9
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, e16, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨h.congr hst (fun _ _ _ => rfl) rfl rfl rfl, ?_⟩
  simp only [arithFlags, State.setFlags, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - c < 2 ^ 64 by omega),
    show (16 : BitVec 64).toNat = 16 from rfl]

/-- The sixteen-block loop, if sixteen blocks are left. -/
theorem groups_wp {enc : Bool} {KP : State → Prop} {f16 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk16 enc f16 KP s₀) {s : State} (h : GInv enc KP s₀ 0 0 s)
    (hcf : s.cf = some (decide (N s₀ < 16))) :
    WP isa (.ite .b (.block []) (.seq (.block constK) (.seq (.loop (group f16) .ae) (.block [.vop .vzeroupper])))) s
      fun s' => ∃ c, N s₀ - c < 16 ∧ GInv enc KP s₀ c c s' := by
  refine WP.ite (decide (N s₀ < 16)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨0, by simpa using hb, h⟩
  · simp at hb
    refine WP.seq (WP.mono (constK_ok s) fun s₁ ⟨k₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
    have h₁ : GInv enc KP s₀ 0 0 s₁ := h.congr hst (fun r h1 _ => g₁ r h1) m₁ rd₁ wr₁
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 16 ≤ N s₀ ∧ GInv enc KP s₀ c c t ∧
      ∀ l < 2, qword (t.lane .xmm11 l) 0 = 0x87
    have hstep : ∀ m t, I m t → WP isa (group f16) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 16 ∧ GInv enc KP s₀ c c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI, hK⟩
      refine WP.mono (group_wp hp hst hf hc hI hK) fun t' ⟨⟨hI', hK'⟩, hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 16) < 16
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 16, hlt, hI'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 16), by omega, c + 16, rfl, by omega, hI', hK'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I hstep (N s₀) s₁ ⟨0, by simp, by omega, h₁, k₁⟩)
      fun s₂ ⟨c, hc, h₂⟩ => ?_)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
    exact ⟨c, hc, h₂.congr hst (fun _ _ _ => rfl) rfl rfl rfl⟩

end VG.Proof.AesXts.X86_64.Vaes
