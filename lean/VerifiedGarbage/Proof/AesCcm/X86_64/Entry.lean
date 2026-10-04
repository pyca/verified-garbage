import VerifiedGarbage.Proof.AesCcm.X86_64.Run

/-!
# AES-CCM on x86-64: the entry and the exit (`entry`, `restore`)

Untrusted: everything here is checked by Lean. `entry` reads the stack
arguments but `tag`, saves our caller's registers at `W + 112` and keeps the arguments
in `W` (`entry_ok`); `restore` reads the registers back (`restore_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)

/-- Our caller's registers, saved at `W + 112`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The save area and the slots, which `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 112, 128⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {s : State} (P : Perm K W s) {R : Nat} {N A D : Addr}
    {nl al n tl : Nat} (hsp : s.gpr .rsp = SP) (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 40⟩] (s.rd ++ s.wr))
    (hargsW : (⟨SP + BitVec.ofNat 64 8, 40⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hD : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = D) (hn : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 40) 64 = W)
    (htl : s.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 nl) (hr8 : s.gpr .r8 = A) (hr9 : s.gpr .r9 = BitVec.ofNat 64 al) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ Env K W SP s₁ ∧ Slots W R N A D nl al n tl s₁.mem ∧
      Saved s₁.mem W s.gpr ∧ Frame [entryR W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₁₆ := in_off (d := 8) (n := 8) hargs (by decide) (by decide)
  have a₃₂ := in_off (d := 24) (n := 8) hargs (by decide) (by decide)
  have a₄₀ := in_off (d := 32) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₁₆ a₃₂ a₄₀
  have w₁ := P.wW (show 112 + 8 ≤ 2560 by decide)
  have w₂ := P.wW (show 120 + 8 ≤ 2560 by decide)
  have w₃ := P.wW (show 128 + 8 ≤ 2560 by decide)
  have w₄ := P.wW (show 136 + 8 ≤ 2560 by decide)
  have w₅ := P.wW (show 144 + 8 ≤ 2560 by decide)
  have w₆ := P.wW (show 152 + 8 ≤ 2560 by decide)
  have w₇ := P.wW (show 160 + 8 ≤ 2560 by decide)
  have w₈ := P.wW (show 168 + 8 ≤ 2560 by decide)
  have w₉ := P.wW (show 176 + 8 ≤ 2560 by decide)
  have w₁₀ := P.wW (show 184 + 8 ≤ 2560 by decide)
  have w₁₁ := P.wW (show 192 + 8 ≤ 2560 by decide)
  have w₁₂ := P.wW (show 200 + 8 ≤ 2560 by decide)
  have w₁₃ := P.wW (show 208 + 8 ≤ 2560 by decide)
  have w₁₄ := P.wW (show 232 + 8 ≤ 2560 by decide)
  obtain ⟨s₁, run₁, h⟩ : ∃ s₁, runBlock isa
      ([.mov .rax (.mem (at_ .rsp 40)), .mov .r10 (.mem (at_ .rsp 8)), .mov .r11 (.mem (at_ .rsp 16))] ++ save .rax ++
        [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
          .store (at_ .r15 nonceO) .rdx, .store (at_ .r15 nlenO) .rcx, .store (at_ .r15 aadO) .r8,
          .store (at_ .r15 alenO) .r9, .store (at_ .r15 dataO) .r10, .store (at_ .r15 lenO) .r11]) s = some s₁ ∧
      s₁.gpr .rsp = SP ∧ s₁.gpr .r15 = W ∧ s₁.gpr .r13 = K ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr ∧
      Frame [entryR W] s.mem s₁.mem ∧ Saved s₁.mem W s.gpr ∧
      s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R ∧ s₁.mem.readW (W + BitVec.ofNat 64 160) 64 = N ∧
      s₁.mem.readW (W + BitVec.ofNat 64 168) 64 = BitVec.ofNat 64 nl ∧
      s₁.mem.readW (W + BitVec.ofNat 64 176) 64 = A ∧
      s₁.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al ∧
      s₁.mem.readW (W + BitVec.ofNat 64 192) 64 = D ∧
      s₁.mem.readW (W + BitVec.ofNat 64 200) 64 = BitVec.ofNat 64 n := by
    have cE : ∀ d, 112 ≤ d → d + 8 ≤ 240 → (entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
      fun d h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
    refine ⟨_, by crun [save, saved, List.map_cons, List.map_nil, hW, hsp, hD, hn, a₈, a₁₆, a₄₀, w₁, w₂, w₃, w₄,
      w₅, w₆, w₇, w₈, w₉, w₁₀, w₁₁, w₁₂, w₁₄], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
    · rfl
    · rfl
    · simp only [mem_setReg]
      repeat (first | exact Frame.refl _ _ |
        refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
    · intro p hp
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64]
    all_goals simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
      ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9]
  obtain ⟨hsp₁, h15, h13, hrd₁, hwr₁, f₁, sv₁, s232, s160, s168, s176, s184, s192, s200⟩ := h
  have htl₁ : s₁.mem.readW (SP + BitVec.ofNat 64 32) 64 = BitVec.ofNat 64 tl := by
    rw [f₁.readW (r := ⟨SP + BitVec.ofNat 64 32, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      have e : SP + BitVec.ofNat 64 32 = SP + BitVec.ofNat 64 8 + BitVec.ofNat 64 24 := by rw [add_ofNat_assoc]
      rw [e]
      exact (hargsW.sub_left (Offset.sub_base _ (by decide))).sub_right (Lay.wSub (by decide))) (by decide), htl]
  have a₃₂' : InRegions (s₁.rd ++ s₁.wr) (SP + BitVec.ofNat 64 32) 8 := by rw [hrd₁, hwr₁]; exact a₃₂
  have w₁₃' : InRegions s₁.wr (W + BitVec.ofNat 64 208) 8 := by rw [hwr₁]; exact w₁₃
  obtain ⟨s₂, run₂, hm₂, hg₂, hrd₂, hwr₂⟩ : ∃ s₂, runBlock isa
      [.mov .rax (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rax] s₁ = some s₂ ∧
      s₂.mem = s₁.mem.writeW (W + BitVec.ofNat 64 208) (BitVec.ofNat 64 tl) ∧
      (∀ r, r ≠ .rax → s₂.gpr r = s₁.gpr r) ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
    refine ⟨_, by crun [hsp₁, h15, htl₁, a₃₂', w₁₃'], ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg]
    · intro r h; simp only [gpr_setReg, h, ite_false]
    all_goals rfl
  have k : ∀ {d}, (d + 8 ≤ 208 ∨ 216 ≤ d) → d + 8 ≤ 2 ^ 64 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 := fun h₁ h₂ => by
    rw [hm₂, readW_writeW_off _ (by omega) h₂ (by decide)]
  refine ⟨s₂, ?_, ⟨by rw [hg₂ _ (by decide), h13], by rw [hg₂ _ (by decide), h15], by rw [hg₂ _ (by decide), hsp₁],
    P.of_eq (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁])⟩,
    ⟨by rw [k (by omega) (by decide), s232], by rw [k (by omega) (by decide), s160],
      by rw [k (by omega) (by decide), s168], by rw [k (by omega) (by decide), s176],
      by rw [k (by omega) (by decide), s184], by rw [k (by omega) (by decide), s192],
      by rw [k (by omega) (by decide), s200], by rw [hm₂, Mem.readW_writeW_self64]⟩,
    fun p hp => ?_, ?_, by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁]⟩
  · rw [show entry = ([.mov .rax (.mem (at_ .rsp 40)), .mov .r10 (.mem (at_ .rsp 8)),
        .mov .r11 (.mem (at_ .rsp 16))] ++ save .rax ++
        [.mov .r15 (.reg .rax), .mov .r13 (.reg .rdi), .store (at_ .r15 roundsO) .rsi,
          .store (at_ .r15 nonceO) .rdx, .store (at_ .r15 nlenO) .rcx, .store (at_ .r15 aadO) .r8,
          .store (at_ .r15 alenO) .r9, .store (at_ .r15 dataO) .r10, .store (at_ .r15 lenO) .r11]) ++
        [.mov .rax (.mem (at_ .rsp 32)), .store (at_ .r15 tlO) .rax] by
      simp only [entry, List.append_assoc, List.cons_append, List.nil_append],
      runBlock_append, run₁, Option.bind_some, run₂]
  · have hp' := hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rw [← sv₁ p hp]
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k (by decide) (by decide)
  · rw [hm₂]
    exact f₁.writeW (List.mem_singleton_self _) _ (Offset.contains W (d := 208) (n := 8) (e := 112) (k := 128)
      (by decide) (by decide) (by decide))

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {g : Reg → BitVec 64} (hs : Saved s.mem W g) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 112 + 8 ≤ 2560 by decide)
  have r₂ := E.perm.wR (show 120 + 8 ≤ 2560 by decide)
  have r₃ := E.perm.wR (show 128 + 8 ≤ 2560 by decide)
  have r₄ := E.perm.wR (show 136 + 8 ≤ 2560 by decide)
  have r₅ := E.perm.wR (show 144 + 8 ≤ 2560 by decide)
  have r₆ := E.perm.wR (show 152 + 8 ≤ 2560 by decide)
  have v₁ := hs (.rbx, 112) (by decide)
  have v₂ := hs (.rbp, 120) (by decide)
  have v₃ := hs (.r12, 128) (by decide)
  have v₄ := hs (.r13, 136) (by decide)
  have v₅ := hs (.r14, 144) (by decide)
  have v₆ := hs (.r15, 152) (by decide)
  refine ⟨_, by crun [restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesCcm.X86_64
