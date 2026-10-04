import VerifiedGarbage.Proof.AesGcmSiv.X86_64.Run

/-!
# AES-GCM-SIV on x86-64: the entry and the exit (`entry`, `restore`)

Untrusted: everything here is checked by Lean. `entry` reads the stack
arguments, saves our caller's registers at `W + 160` and keeps the arguments
in `W` (`entry_ok`); `restore` reads the registers back (`restore_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcmSiv.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcmSiv.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Proof.AesGcm.X86_64 (in_off)
open VG.Spec.Aes (bytesAt)

/-- Our caller's registers, saved at `W + 160`. -/
def Saved (m : Mem) (W : Addr) (g : Reg → BitVec 64) : Prop :=
  ∀ p ∈ saved, m.readW (W + BitVec.ofNat 64 p.2) 64 = g p.1

/-- The save area and the slots, which `entry` writes. -/
abbrev entryR (W : Addr) : Region := ⟨W + BitVec.ofNat 64 160, 160⟩

theorem readW_writeW_off {m : Mem} {W : Addr} {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (W + BitVec.ofNat 64 e) v).readW (W + BitVec.ofNat 64 d) 64 = m.readW (W + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep W h hd he) (by decide)

/-- `entry`. -/
theorem entry_ok {K W SP : Addr} {s : State} (P : Perm K W s) {R : Nat} {N A D : Addr} {al n : Nat}
    (hsp : s.gpr .rsp = SP) (hargs : Covers [⟨SP + BitVec.ofNat 64 8, 16⟩] (s.rd ++ s.wr))
    (hn : s.mem.readW (SP + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 n)
    (hW : s.mem.readW (SP + BitVec.ofNat 64 16) 64 = W)
    (hdi : s.gpr .rdi = K) (hsi : s.gpr .rsi = BitVec.ofNat 64 R) (hdx : s.gpr .rdx = N)
    (hcx : s.gpr .rcx = A) (hr8 : s.gpr .r8 = BitVec.ofNat 64 al) (hr9 : s.gpr .r9 = D) :
    ∃ s₁, runBlock isa entry s = some s₁ ∧ Env K W SP s₁ ∧ Slots W R N A D al n s₁.mem ∧
      Saved s₁.mem W s.gpr ∧ Frame [entryR W] s.mem s₁.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  have a₈ := in_off (d := 0) (n := 8) hargs (by decide) (by decide)
  have a₁₆ := in_off (d := 8) (n := 8) hargs (by decide) (by decide)
  rw [add_ofNat_assoc, show 8 + 0 = 8 from rfl] at a₈
  rw [add_ofNat_assoc] at a₁₆
  simp only [Nat.reduceAdd] at a₁₆
  have w₁ := P.wW (show 160 + 8 ≤ 4096 by decide)
  have w₂ := P.wW (show 168 + 8 ≤ 4096 by decide)
  have w₃ := P.wW (show 176 + 8 ≤ 4096 by decide)
  have w₄ := P.wW (show 184 + 8 ≤ 4096 by decide)
  have w₅ := P.wW (show 192 + 8 ≤ 4096 by decide)
  have w₆ := P.wW (show 200 + 8 ≤ 4096 by decide)
  have w₇ := P.wW (show 272 + 8 ≤ 4096 by decide)
  have w₈ := P.wW (show 280 + 8 ≤ 4096 by decide)
  have w₉ := P.wW (show 288 + 8 ≤ 4096 by decide)
  have w₁₀ := P.wW (show 296 + 8 ≤ 4096 by decide)
  have w₁₁ := P.wW (show 304 + 8 ≤ 4096 by decide)
  have w₁₂ := P.wW (show 312 + 8 ≤ 4096 by decide)
  have cE : ∀ d, 160 ≤ d → d + 8 ≤ 320 → (entryR W).Contains (W + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₁ h₂ => Offset.contains W h₁ (by omega) (by decide)
  refine ⟨_, by srun [entry, save, saved, List.map_cons, List.map_nil, hW, hsp, hn, a₈, a₁₆, w₁, w₂, w₃, w₄,
      w₅, w₆, w₇, w₈, w₉, w₁₀, w₁₁, w₁₂], ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hdi]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hsp]
  · exact P.of_eq rfl rfl
  iterate 6
    · simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64, gpr_setReg,
        ite_true, ite_false, reduceCtorEq, hsi, hdx, hcx, hr8, hr9, hn]
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [mem_setReg, readW_writeW_off, Mem.readW_writeW_self64]
  · simp only [mem_setReg]
    repeat (first | exact Frame.refl _ _ |
      refine Frame.writeW ?_ (List.mem_singleton_self _) _ (cE _ (by decide) (by decide)))
  all_goals rfl

/-- `restore`: our caller's registers back. -/
theorem restore_ok {K W SP : Addr} {s : State} (E : Env K W SP s) {g : Reg → BitVec 64} (hs : Saved s.mem W g) :
    ∃ s', runBlock isa restore s = some s' ∧ (∀ p ∈ saved, s'.gpr p.1 = g p.1) ∧ s'.mem = s.mem ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rax = s.gpr .rax := by
  have h15 := E.r15
  have r₁ := E.perm.wR (show 160 + 8 ≤ 4096 by decide)
  have r₂ := E.perm.wR (show 168 + 8 ≤ 4096 by decide)
  have r₃ := E.perm.wR (show 176 + 8 ≤ 4096 by decide)
  have r₄ := E.perm.wR (show 184 + 8 ≤ 4096 by decide)
  have r₅ := E.perm.wR (show 192 + 8 ≤ 4096 by decide)
  have r₆ := E.perm.wR (show 200 + 8 ≤ 4096 by decide)
  have v₁ := hs (.rbx, 160) (by decide)
  have v₂ := hs (.rbp, 168) (by decide)
  have v₃ := hs (.r12, 176) (by decide)
  have v₄ := hs (.r13, 184) (by decide)
  have v₅ := hs (.r14, 192) (by decide)
  have v₆ := hs (.r15, 200) (by decide)
  refine ⟨_, by srun [restore, saved, List.map_cons, List.map_nil, h15, r₁, r₂, r₃, r₄, r₅, r₆], ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, v₁, v₂, v₃, v₄, v₅, v₆]
  · rfl
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]

end VG.Proof.AesGcmSiv.X86_64
