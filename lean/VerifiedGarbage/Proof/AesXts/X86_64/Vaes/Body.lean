module
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Loop

import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.PrePost
import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Ctr32
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# One-pass XTS-AES on x86-64: the loops

`constK_ok`: `0x87` into both lanes of `ymm11`. `groups_wp`: from `GInv 0 0`,
if eight blocks are left, the tweaks loaded into `ymm4`–`ymm7` (`TwR 0`),
the eight-block loop, and the tweaks stored back reach `GInv c c` with fewer
than eight blocks left.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.Vaes

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Impl.AesXts.X86_64Vaes (constK group ldT stT tws bufOff)
open VG.Proof.AesXts (b16)
open VG.Proof.Aes.X86_64.AesNi (inRegions_wr ofInt_natCast)

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

/-- `cmp r9, 8`. -/
theorem cmp8_ok {enc : Bool} {KP : State → Prop} {s₀ : State} (hst : Stable KP s₀) {c : Nat} {s : State}
    (h : GInv enc KP s₀ c c s) :
    WP isa (.block [.alu .cmp .r9 (.imm 8)]) s fun s' =>
      GInv enc KP s₀ c c s' ∧ s'.cf = some (decide (N s₀ - c < 8)) := by
  have e16 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr9 := h.r9
  have hn : N s₀ < 2 ^ 64 := (s₀.gpr .r8).isLt
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, e16, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨h.congr hst (fun _ _ _ => rfl) rfl rfl rfl, ?_⟩
  simp only [arithFlags, State.setFlags, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - c < 2 ^ 64 by omega),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The tweak registers from the buffer: `TwR 0`. -/
theorem ldT_twr {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) (hst : Stable KP s₀) {s : State}
    (h : GInv enc KP s₀ 0 0 s) (hK : ∀ l < 2, qword (s.lane .xmm11 l) 0 = 0x87) :
    WP isa (.block (ldT tws 0)) s fun s' => GInv enc KP s₀ 0 0 s' ∧ TwR s₀ 0 s' := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine WP.mono (ldT_ok tws 0 s (by decide) fun k hk => inRegions_wr ⟨scrR s₀, by rw [hW]; simp, by
      rw [h.r8, ofInt_natCast]
      rw [show tws.length = 4 from rfl] at hk
      exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩)
    fun s' ⟨e, g, m, rd, wr, x⟩ => ?_
  refine ⟨h.congr hst (fun r _ _ => by rw [g]) m rd wr, ⟨fun k hk l hl => ?_, fun l hl => by
    rw [x _ (by decide) l hl]; exact hK l hl⟩⟩
  have hk4 : k < 4 := hk
  rw [e k hk l hl, h.r8, show bufOff + 32 * (0 + k) + 16 * l = bufOff + 16 * (2 * k + l) by omega,
    ← bytesAt_b16, h.buf _ (by omega)]

/-- The tweak registers back to the buffer: `GInv c c`. -/
theorem stT_ginv {enc : Bool} {KP : State → Prop} {s₀ : State} (hp : UPre s₀) (hst : Stable KP s₀) {c : Nat}
    {s : State} (h : GInv enc KP s₀ 0 c s) (ht : TwR s₀ c s) :
    WP isa (.block (stT tws 0)) s (GInv enc KP s₀ c c) := by
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  refine WP.mono (stT_ok tws 0 s (fun k hk => ⟨scrR s₀, by rw [hW]; simp, by
      rw [h.r8, ofInt_natCast]
      rw [show tws.length = 4 from rfl] at hk
      exact Offset.contains_base _ (by simp only [bufOff]; omega) (by simp only [bufOff]; omega)⟩) (by rw [h.r8]; simp only [bufOff]; have : tws.length = 4 := rfl; omega))
    fun s' ⟨e, f, g, rd, wr, _⟩ => ?_
  rw [h.r8, Nat.mul_zero, Nat.add_zero, show 32 * tws.length = 128 from rfl] at f
  rw [h.r8] at e
  have fb : Frame [bufR s₀] s.mem s'.mem := f.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, Region.sub_prefix (by decide)⟩
  have fs : Frame [scrR s₀] s.mem s'.mem := fb.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, buf_scr⟩
  have hbd : ∀ k < N s₀, ∀ r ∈ [bufR s₀], Region.Disjoint ⟨blk s₀ k, 16⟩ r := fun k hk r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right buf_scr
  exact ⟨hst s s' h.kp (by rw [g]) (by rw [g]) (by rw [g]) (by rw [g]) rd wr (fb.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, fun _ h => h⟩),
    h.le, by rw [g, h.r8], by rw [g, h.r9], by rw [g, h.r11], by rw [g, h.r10],
    fun r h1 h2 h3 h4 h5 h6 h7 => by rw [g, h.keep r h1 h2 h3 h4 h5 h6 h7], by rw [rd, h.rd], by rw [wr, h.wr],
    h.frame.trans (fs.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => h⟩),
    fun k hk => by rw [AesCbc.X86_64.bytesAt_frame fb (hbd k hk) (by decide), h.data k hk],
    fun j hj => by
      have hk : j / 2 < tws.length := by have : tws.length = 4 := rfl; omega
      rw [bytesAt_b16, slot, show bufOff + 16 * j = bufOff + 32 * (0 + j / 2) + 16 * (j % 2) by omega,
        e _ hk _ (Nat.mod_lt _ (by decide)), ht.tw _ hk _ (Nat.mod_lt _ (by decide))]
      congr 1; omega,
    by rw [g, h.rdx]⟩

/-- The eight-block loop, if eight blocks are left. -/
theorem groups_wp {enc : Bool} {KP : State → Prop} {f8 : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : Blk8 enc f8 KP s₀) {s : State} (h : GInv enc KP s₀ 0 0 s)
    (hcf : s.cf = some (decide (N s₀ < 8))) :
    WP isa (.ite .b (.block []) (.seq (.block (constK ++ ldT tws 0))
      (.seq (.loop (group f8) .ae) (.block (stT tws 0 ++ ([.vop .vzeroupper] : List Instr)))))) s
      fun s' => ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c s' := by
  refine WP.ite (decide (N s₀ < 8)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨0, by simpa using hb, h⟩
  · simp at hb
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (constK_ok s) fun s₁ ⟨k₁, g₁, m₁, rd₁, wr₁⟩ => ?_
    have h₁ : GInv enc KP s₀ 0 0 s₁ := h.congr hst (fun r h1 _ => g₁ r h1) m₁ rd₁ wr₁
    refine WP.mono (ldT_twr hp hst h₁ k₁) fun s₂ ⟨h₂, t₂⟩ => ?_
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ GInv enc KP s₀ 0 c t ∧ TwR s₀ c t
    have hstep : ∀ m t, I m t → WP isa (group f8) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ 0 c t' ∧ TwR s₀ c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI, hT⟩
      refine WP.mono (group_wp hp hst hf hc hI hT) fun t' ⟨⟨hI', hT'⟩, hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 8) < 8
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI', hT'⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 8), by omega, c + 8, rfl, by omega, hI', hT'⟩
    refine WP.seq (WP.mono (WP.loop (M := isa) I hstep (N s₀) s₂ ⟨0, by simp, by omega, h₂, t₂⟩)
      fun s₃ ⟨c, hc, h₃, t₃⟩ => ?_)
    rw [WP.block_append_iff]
    refine WP.mono (stT_ginv hp hst h₃ t₃) fun s₄ h₄ => ?_
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
    exact ⟨c, hc, h₄.congr hst (fun _ _ _ => rfl) rfl rfl rfl⟩

end VG.Proof.AesXts.X86_64.Vaes
