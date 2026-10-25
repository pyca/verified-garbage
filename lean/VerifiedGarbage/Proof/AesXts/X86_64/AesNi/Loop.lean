module

import VerifiedGarbage.Proof.AesXts.X86_64.AesNi.Step
public import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Top
public import VerifiedGarbage.Impl.AesXts.X86_64AesNi
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.TailOps
import VerifiedGarbage.Proof.AesXts.X86_64.Vaes.Body
import VerifiedGarbage.Proof.AesCbc.X86_64.Body
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Aes.X86_64.CodeLit
import VerifiedGarbage.Proof.Aes.X86_64.Lit
import VerifiedGarbage.Proof.Framework.Contract

/-!
# One-pass XTS-AES with AES-NI on x86-64: eight blocks at a time

The loop keeps `GInv c c` (`Vaes/Loop.lean`: the tweaks of blocks `c … c + 7`
at `scratch + 256`), with `rax` at the first of them and `0x87` in `xmm11`
(`NInv`). `group_wp`: one group of eight blocks through the AES-NI round code
`f` on `xmm0`–`xmm7` (`BlkN`) takes it from `c` to `c + 8`; `loop8_ok`: the
loop meets `LoopOk`, so `crypt_wp` applies.
-/

@[expose] public section

namespace VG.Proof.AesXts.X86_64.OnePassNi

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCbc.X86_64 (W R Iv Dp N S schR ivR dataR scrR stkR UPre blk wK iv0)
open VG.Proof.AesXts.X86_64.Vaes
open VG.Impl.AesXts.X86_64AesNi (stepT steps group loop8 constK)
open VG.Impl.AesXts.X86_64Vaes (bufOff tPre tPost)
open VG.Impl.Aes.X86_64.AesNi (regs8)
open VG.Proof.AesXts (b16 next_b8)
open VG.Proof.Aes.X86_64.AesNi (st inRegions_wr ofInt_natCast XFrame)

/-- `f` computes the cipher (or its inverse) on `xmm0`–`xmm7`. -/
def BlkN (enc : Bool) (f : List XReg → Prog isa) (KP : State → Prop) (s₀ : State) : Prop :=
  ∀ s, KP s → WP isa (f regs8) s fun s' =>
    (∀ b ∈ regs8, st (s'.xmm b) = stF enc (R s₀) (wK s₀) (st (s.xmm b))) ∧ XFrame (.xmm8 :: regs8) s s'

/-- In the loop: the tweaks of the group at `rax`, and `0x87` in `xmm11`. -/
structure NInv (enc : Bool) (KP : State → Prop) (s₀ : State) (c : Nat) (s : State) : Prop where
  g : GInv enc KP s₀ c c s
  rax : s.gpr .rax = slot s₀ 0
  k87 : qword (s.xmm .xmm11) 0 = 0x87

/-- The first `n` tweaks at `rax` times `α⁸`. -/
theorem stepsN_ok (s : State) (hK : qword (s.xmm .xmm11) 0 = 0x87)
    (hin : ∀ k < 8, InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * k : Nat) : Int)) 16)
    (hw : (s.gpr .rax).toNat + 128 ≤ 2 ^ 64) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap stepT)) s fun s' =>
      (∀ j < 8, s'.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * j)) 128 =
        if j < n then stepW (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * j)) 128)
        else s.mem.readW (s.gpr .rax + BitVec.ofNat 64 (16 * j)) 128) ∧
      Frame [⟨s.gpr .rax, 128⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .xmm9 → r ≠ .xmm10 → s'.xmm r = s.xmm r)
  | 0, _ => WP.block_nil ⟨fun j _ => by simp, Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (stepsN_ok s hK hin hw n (by omega_arith)) fun s₁ ⟨v₁, f₁, g₁, rd₁, wr₁, x₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hK₁ : qword (s₁.xmm .xmm11) 0 = 0x87 := by rw [x₁ _ (by decide) (by decide)]; exact hK
    refine WP.mono (stepT_ok n s₁ hK₁ (by rw [g₁, wr₁]; exact hin n (by omega_arith)))
      fun s' ⟨m', g', rd', wr', x'⟩ => ?_
    rw [g₁, ofInt_natCast] at m'
    refine ⟨fun j hj => ?_, ?_, g'.trans g₁, rd'.trans rd₁, wr'.trans wr₁,
      fun r h1 h2 => (x' r h1 h2).trans (x₁ r h1 h2)⟩
    · rw [m']
      by_cases hjn : j = n
      · subst hjn
        rw [Mem.readW_writeW_self _ _ 16 _ (by decide), v₁ _ hj]
        simp only [Nat.lt_irrefl, ite_false, Nat.lt_succ_self, ite_true]
      · rw [Mem.readW_writeW_sep ?_ (by decide), v₁ j hj]
        · by_cases hlt : j < n
          · simp only [hlt, ite_true, show j < n + 1 by omega_arith]
          · simp only [hlt, ite_false, show ¬ j < n + 1 by omega_arith]
        · have := Offset.sep (s.gpr .rax) (d := 16 * j) (n := 16) (e := 16 * n) (k := 16)
            (by omega_arith) (by omega_arith) (by omega_arith)
          simpa using this
    · rw [m']
      exact f₁.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains_base _ (d := 16 * n) (n := 16) (k := 128) (by omega_arith) (by omega_arith)))

/-- One group of eight blocks. -/
theorem group_wp {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : BlkN enc f KP s₀) {c : Nat} (hc : c + 8 ≤ N s₀) {s : State}
    (h : NInv enc KP s₀ c s) :
    WP isa (group f) s fun s' => NInv enc KP s₀ (c + 8) s' ∧ s'.cf = some (decide (N s₀ - (c + 8) < 8)) := by
  have hg := h.g
  have hw := hp.data_wrap
  have hsw := hp.scr_wrap
  have hW : s.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [hg.wr, hp.wr]
  have inD : ∀ k < 8, InRegions s.wr (s.gpr .r11 + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨dataR s₀, by rw [hW]; simp, ?_⟩
    rw [hg.r11, ofInt_natCast, blk, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have inT : ∀ k < 8, InRegions s.wr (s.gpr .rax + BitVec.ofInt 64 ((16 * (0 + k) : Nat) : Int)) 16 := by
    intro k hk
    refine ⟨scrR s₀, by rw [hW]; simp, ?_⟩
    rw [h.rax, ofInt_natCast, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Offset.contains_base _ (by simp only [bufOff]; omega_arith) (by simp only [bufOff]; omega_arith)
  -- The tweaks XORed in.
  refine WP.seq (WP.mono (tPreList_ok regs8 0 s (by decide) (fun k hk => inRegions_wr (inD k hk))
    (fun k hk => inRegions_wr (inT k hk))) fun s₁ ⟨e₁, g₁, m₁, rd₁, wr₁, x₁⟩ => ?_)
  have kp₁ : KP s₁ := hst s s₁ hg.kp (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) (by rw [g₁]) rd₁ wr₁
    (by rw [m₁]; exact Frame.refl _ _)
  -- The rounds.
  refine WP.seq (WP.mono (hf s₁ kp₁) fun s₂ ⟨e₂, f₂⟩ => ?_)
  have g₂ : s₂.gpr = s.gpr := f₂.gpr.trans g₁
  have m₂ : s₂.mem = s.mem := f₂.mem.trans m₁
  have wr₂ : s₂.wr = s.wr := f₂.wr.trans wr₁
  have rd₂ : s₂.rd = s.rd := f₂.rd.trans rd₁
  have kp₂ : KP s₂ := hst s₁ s₂ kp₁ (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr]) (by rw [f₂.gpr])
    f₂.rd f₂.wr (by rw [f₂.mem]; exact Frame.refl _ _)
  -- The tweaks XORed in again, and the blocks stored.
  rw [List.append_assoc, WP.block_append_iff]
  have hr11N : (s.gpr .r11).toNat = (Dp s₀).toNat + 16 * c := by rw [hg.r11]; exact hp.blk_toNat (by omega_arith)
  refine WP.mono (tPostList_ok regs8 0 s₂ (by decide) (fun k hk => by rw [wr₂, g₂]; exact inD k hk)
    (fun k hk => by rw [rd₂, wr₂, g₂]; exact inRegions_wr (inT k hk)) (by rw [g₂, hr11N]; show _ + 16 * (0 + 8) ≤ _; omega_arith)
    (fun k hk => by
      rw [g₂, h.rax, hg.r11, Nat.mul_zero, BitVec.add_zero, slot, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact ((hp.data_scr.sub_left (group_data hc)).sub_right
        (UPre.scr_sub (by simp only [bufOff]; have : regs8.length = 8 := rfl; omega_arith))).symm))
    fun s₃ ⟨e₃, f₃, g₃, rd₃, wr₃, x₃⟩ => ?_
  rw [g₂, hg.r11, Nat.mul_zero, BitVec.add_zero, m₂, show 16 * regs8.length = 128 from rfl] at f₃
  rw [g₂, m₂] at e₃
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have kp₃ : KP s₃ := hst s₂ s₃ kp₂ (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) (by rw [g₃]) rd₃ wr₃ (by
    rw [m₂]; exact f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩)
  have hK₃ : qword (s₃.xmm .xmm11) 0 = 0x87 := by
    rw [x₃ _ (by decide), f₂.xmm _ (by decide), x₁ _ (by decide)]; exact h.k87
  -- The tweaks times `α⁸`.
  rw [WP.block_append_iff]
  refine WP.mono (stepsN_ok s₃ hK₃ (fun k hk => by rw [wr₃, wr₂, g₃']; simpa using inT k hk)
      (by rw [g₃', h.rax, slot]; simp only [bufOff]; rw [BitVec.toNat_add_of_lt (by simp; omega_arith)]; simp; omega_arith)
      8 (Nat.le_refl _)) fun s₄ ⟨e₄, f₄, g₄, rd₄, wr₄, x₄⟩ => ?_
  rw [g₃', h.rax] at e₄ f₄
  have g₄' : s₄.gpr = s.gpr := g₄.trans g₃'
  have hTb : Region.Sub ⟨slot s₀ 0, 128⟩ (bufR s₀) := by
    rw [slot, Nat.mul_zero, Nat.add_zero]; exact Region.sub_prefix (by decide)
  have kp₄ : KP s₄ := hst s₃ s₄ kp₃ (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) (by rw [g₄]) rd₄ wr₄ (f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨bufR s₀, by simp, hTb⟩)
  have hK₄ : qword (s₄.xmm .xmm11) 0 = 0x87 := by rw [x₄ _ (by decide) (by decide)]; exact hK₃
  -- The memory after the group.
  have fr : Frame [dataR s₀, scrR s₀] s₀.mem s₄.mem :=
    hg.frame.trans ((f₃.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, group_data hc⟩).trans
      (f₄.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, fun _ h => buf_scr _ (hTb _ h)⟩))
  have slotE : ∀ j, slot s₀ j = slot s₀ 0 + BitVec.ofNat 64 (16 * j) := fun j => by
    rw [slot, slot, Nat.mul_zero, Nat.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hdata : ∀ k < N s₀, bytesAt s₄.mem (blk s₀ k) 16 = if k < c + 8 then outBlk enc s₀ k
      else bytesAt s₀.mem (blk s₀ k) 16 := by
    intro k hk
    rw [AesCbc.X86_64.bytesAt_frame f₄ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (fun _ h => buf_scr _ (hTb _ h))) (by decide)]
    by_cases hin : c ≤ k ∧ k < c + 8
    · obtain ⟨i, rfl⟩ : ∃ i, k = c + i := ⟨k - c, by omega_arith⟩
      have hi : i < regs8.length := by have : regs8.length = 8 := rfl; omega_arith
      have ab : blk s₀ (c + i) = s.gpr .r11 + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [hg.r11, blk, blk, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega_arith
      have sl : slot s₀ i = s.gpr .rax + BitVec.ofNat 64 (16 * (0 + i)) := by
        rw [h.rax, slotE, Nat.zero_add]
      rw [bytesAt_b16, ab, e₃ _ hi, ← sl, ← ab]
      have e1 := e₁ _ hi
      rw [← ab, ← sl] at e1
      have hc' : st (s₂.xmm regs8[i]) = stF enc (R s₀) (wK s₀)
          (st (s.mem.readW (blk s₀ (c + i)) 128 ^^^ s.mem.readW (slot s₀ i) 128)) :=
        (e₂ _ (List.getElem_mem hi)).trans (congrArg (fun v => stF enc (R s₀) (wK s₀) (st v)) e1)
      refine (xts_word enc (R s₀) (wK s₀) _ _ _ hc').trans ?_
      rw [← bytesAt_b16, ← bytesAt_b16, hg.buf i (by omega_arith), hg.data _ hk]
      simp only [show ¬ c + i < c by omega_arith, ite_false, show c + i < c + 8 by omega_arith, ite_true]
    · rw [AesCbc.X86_64.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rw [blk, blk]
          exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hg.data k hk]
      by_cases hlt' : k < c
      · simp only [hlt', ite_true, show k < c + 8 by omega_arith]
      · simp only [hlt', ite_false, show ¬ k < c + 8 by omega_arith]
  have hbuf : ∀ j < 8, bytesAt s₄.mem (slot s₀ j) 16 = Spec.Xts.next (iv0 s₀) (c + 8 + j) := by
    intro j hj
    rw [bytesAt_b16, slotE, e₄ j hj]
    simp only [hj, ite_true]
    rw [← slotE, f₃.readW (r := ⟨slot s₀ j, 16⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ((hp.data_scr.sub_left (group_data hc)).sub_right (slot_scr (j := j) (by omega_arith))).symm) (by decide)]
    rw [stepW, ← next_b8, ← bytesAt_b16, hg.buf j hj, ← next_add]
    congr 1; omega_arith
  have hrd : s₄.rd = s₀.rd := by rw [rd₄, rd₃, rd₂, hg.rd]
  have hwr : s₄.wr = s₀.wr := by rw [wr₄, wr₃, wr₂, hg.wr]
  -- `add r11, 128`, `sub r9, 8` and `cmp r9, 8`.
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hr11 : s₄.gpr .r11 = blk s₀ c := by rw [g₄', hg.r11]
  have hr9 : s₄.gpr .r9 = BitVec.ofNat 64 (N s₀ - c) := by rw [g₄', hg.r9]
  have hsub : BitVec.ofNat 64 (N s₀ - c) - 8 = BitVec.ofNat 64 (N s₀ - (c + 8)) := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, Offset.ofNat_sub_ofNat (by omega_arith), Nat.sub_sub]
  have hadd : blk s₀ c + 128 = blk s₀ (c + 8) := by
    rw [blk, blk, show (128 : BitVec 64) = BitVec.ofNat 64 128 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * c + 128 = 16 * (c + 8) by omega_arith]
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, arithFlags, State.setFlags, isa, State.setReg, e128, e8, hr11, hr9,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨⟨hst s₄ _ kp₄ (by simp) (by simp) (by simp) (by simp) rfl rfl (Frame.refl _ _), hc,
      by simp [g₄', hg.r8], by simp; exact hsub, by simp; exact hadd, by simp [g₄', hg.r10],
      fun r h1 h2 h3 h4 h5 h6 h7 => by simp [h5, h7, g₄', hg.keep r h1 h2 h3 h4 h5 h6 h7],
      hrd, hwr, fr, hdata, fun j hj => by rw [hbuf j hj], by simp [g₄', hg.rdx]⟩,
    by simp [g₄', h.rax], by simpa using hK₄⟩, ?_⟩
  simp only [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N s₀ - (c + 8) < 2 ^ 64 by omega_arith),
    show (8 : BitVec 64).toNat = 8 from rfl]

/-- The eight-block loop meets `LoopOk`. -/
theorem loop8_ok {enc : Bool} {KP : State → Prop} {f : List XReg → Prog isa} {s₀ : State} (hp : UPre s₀)
    (hst : Stable KP s₀) (hf : BlkN enc f KP s₀) : LoopOk enc (loop8 f) KP s₀ := by
  intro s h hcf
  refine WP.ite (decide (N s₀ < 8)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · exact WP.block_nil ⟨0, by simpa using hb, h⟩
  · simp at hb
    have e256 : BitVec.signExtend 64 (256 : BitVec 32) = 256 := by decide
    have hr8 := h.r8
    have st₁ : WP isa (.block (constK ++ ([.mov .rax (.reg .r8), .alu .add .rax (.imm 256)] : List Instr))) s
        (NInv enc KP s₀ 0) := by
      apply WP.of_runBlock
      simp only [constK, List.cons_append, List.nil_append, ↓reduceIte, runBlock_cons, runStep_some,
        runBlock_nil, exec, readSrc, execAlu, VOp.exec, arithFlags, State.setFlags, State.setReg, e256,
        Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
      refine ⟨h.congr hst (fun r h1 _ => by simp [h1]) (by simp [State.setV]) (by simp [State.setV])
        (by simp [State.setV]), ?_, ?_⟩
      · simp [State.setV, hr8, slot, bufOff]
      · simp [State.setV, qword]
    refine WP.seq (WP.mono st₁ fun s₁ h₁ => ?_)
    let I : Nat → State → Prop := fun m t => ∃ c, m = N s₀ - c ∧ c + 8 ≤ N s₀ ∧ NInv enc KP s₀ c t
    have hstep : ∀ m t, I m t → WP isa (group f) t (fun t' =>
        (eval .ae t' = some false ∧ ∃ c, N s₀ - c < 8 ∧ GInv enc KP s₀ c c t') ∨
        (eval .ae t' = some true ∧ ∃ m' < m, I m' t')) := by
      rintro m t ⟨c, rfl, hc, hI⟩
      refine WP.mono (group_wp hp hst hf hc hI) fun t' ⟨hI', hcf'⟩ => ?_
      by_cases hlt : N s₀ - (c + 8) < 8
      · exact .inl ⟨by simp [eval, hcf', hlt], c + 8, hlt, hI'.g⟩
      · exact .inr ⟨by simp [eval, hcf', hlt], N s₀ - (c + 8), by omega_arith, c + 8, rfl, by omega_arith, hI'⟩
    exact WP.loop (M := isa) I hstep (N s₀) s₁ ⟨0, by simp, by omega_arith, h₁⟩

end VG.Proof.AesXts.X86_64.OnePassNi
