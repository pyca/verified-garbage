import VerifiedGarbage.Proof.Sm4.X86.Keys
import VerifiedGarbage.Proof.Sm4.Common

/-!
# Copying blocks on x86 (32-bit)

As on ARMv7: `copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks
of 16 bytes from `edx` to `ebx` (areas that do not overlap), a word at a
time through `eax`, counting down `ecx`, and changes nothing else in memory.
-/

namespace VG.Proof.Sm4.X86

open VG VG.X86 VG.Impl.Sm4.X86
open VG.Impl.Aes.X86 (at_ addI subI)
open VG.Proof.Sm4 (off_sub_toNat off_sub_not writeW_readW32_apply)

/-- What a copy keeps, after its first `k` bytes. -/
structure Copied (A B : Addr) (c : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  copied : ∀ t < k, s.mem (B + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem

/-- `mov eax, [edx + d]; mov [ebx + d], eax`: the copy's next word. -/
theorem copyWord_ok {A B : BitVec 32} {c : Nat} {s₀ s : State} {j d : Nat} (hd : d < 16) (hd4 : d % 4 = 0)
    (hj : j < c) (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hsep : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨B.setWidth 64, 16 * c⟩)
    (hr : InRegions (s.rd ++ s.wr) (A.setWidth 64 + BitVec.ofNat 64 (16 * j + d)) 4)
    (hw : InRegions s.wr (B.setWidth 64 + BitVec.ofNat 64 (16 * j + d)) 4)
    (h0 : s.gpr .edx = A + BitVec.ofNat 32 (16 * j)) (h1 : s.gpr .ebx = B + BitVec.ofNat 32 (16 * j))
    (hi : Copied (A.setWidth 64) (B.setWidth 64) c s₀ (16 * j + d) s) :
    ∃ s', runBlock isa [.mov .eax (.mem (at_ .edx d)), .store (at_ .ebx d) .eax] s = some s' ∧
      Copied (A.setWidth 64) (B.setWidth 64) c s₀ (16 * j + d + 4) s' ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have eA : s.ea (at_ .edx d) = A.setWidth 64 + BitVec.ofNat 64 (16 * j + d) := by
    rw [at_, ea_mk, h0, addr, VG.Offset.add_add, ← addr, addr_eq (by omega)]
  let s₁ := s.setReg .eax (s.mem.readW (A.setWidth 64 + BitVec.ofNat 64 (16 * j + d)) 32)
  have eB : s₁.ea (at_ .ebx d) = B.setWidth 64 + BitVec.ofNat 64 (16 * j + d) := by
    rw [at_, ea_mk, show s₁.gpr .ebx = s.gpr .ebx from RegUpd.gpr_setReg_of_ne _ _ (by decide), h1, addr,
      VG.Offset.add_add, ← addr, addr_eq (by omega)]
  let m' := s.mem.writeW (B.setWidth 64 + BitVec.ofNat 64 (16 * j + d))
    (s.mem.readW (A.setWidth 64 + BitVec.ofNat 64 (16 * j + d)) 32)
  refine ⟨{ s₁ with mem := m' }, ?_,
    ⟨fun t ht' => ?_, hi.frame.trans fun x hx => ?_⟩, fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr, rfl, rfl⟩
  · rw [runBlock_cons, show exec (.mov .eax (.mem (at_ .edx d))) s = some s₁ by
        simp [exec, readSrc, State.load32, eA, hr, s₁], runStep_some, runBlock_cons]
    simp only [exec, State.store32, eB, show s₁.wr = s.wr from rfl, hw, ↓reduceIte, runStep_some, runBlock_nil,
      s₁, RegUpd.gpr_setReg_self]
    rfl
  · have hn : 16 * c < 2 ^ 64 := by omega
    have hAs : ∀ t < 16 * c, s.mem (A.setWidth 64 + BitVec.ofNat 64 t) = s₀.mem (A.setWidth 64 + BitVec.ofNat 64 t) :=
      fun t ht => hi.frame.bytes (R := ⟨A.setWidth 64, 16 * c⟩)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep) (by simp only; omega) ht
    show (s.mem.writeW _ _) _ = _
    rw [writeW_readW32_apply]
    by_cases h8 : 16 * j + d ≤ t
    · rw [ite_eq_left (by rw [off_sub_toNat _ h8 (by omega)]; omega), off_sub_toNat _ h8 (by omega),
        VG.Offset.add_add, show 16 * j + d + (t - (16 * j + d)) = t by omega, hAs t (by omega)]
    · rw [ite_eq_right (off_sub_not _ (Or.inl (by omega)) (by omega) (by omega) (by omega))]
      exact hi.copied t (by omega)
  · show (s.mem.writeW _ _) x = s.mem x
    rw [writeW_readW32_apply, ite_eq_right fun h =>
      hx _ (List.mem_singleton_self _) (VG.Offset.sub_base _ (show 16 * j + d + 4 ≤ 16 * c by omega) _
        (by simp only [Region.Contains]; omega))]

/-- Copying, after `j` of `c` blocks. -/
structure CopyInv (A B : BitVec 32) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  src : s.gpr .edx = A + BitVec.ofNat 32 (16 * j)
  dst : s.gpr .ebx = B + BitVec.ofNat 32 (16 * j)
  cnt : s.gpr .ecx = BitVec.ofNat 32 (c - j)
  cp : Copied (A.setWidth 64) (B.setWidth 64) c s₀ (16 * j) s
  regs : ∀ r, r ≠ .edx → r ≠ .ebx → r ≠ .ecx → r ≠ .eax → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {A B : BitVec 32} {c : Nat} {s₀ : State} (hc : 0 < c) (hc8 : c ≤ 8)
    (hfA : A.toNat + 16 * c ≤ 2 ^ 32) (hfB : B.toNat + 16 * c ≤ 2 ^ 32)
    (hA : ∀ t < 16 * c, t % 4 = 0 → InRegions (s₀.rd ++ s₀.wr) (A.setWidth 64 + BitVec.ofNat 64 t) 4)
    (hB : ∀ t < 16 * c, t % 4 = 0 → InRegions s₀.wr (B.setWidth 64 + BitVec.ofNat 64 t) 4)
    (hsep : Region.Disjoint ⟨A.setWidth 64, 16 * c⟩ ⟨B.setWidth 64, 16 * c⟩) (hs : CopyInv A B c s₀ 0 s₀) :
    WP isa copyBlocks s₀ (CopyInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have rA : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.rd = s₀.rd → s.wr = s₀.wr →
      InRegions (s.rd ++ s.wr) (A.setWidth 64 + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h1 h2 => by
    rw [h1, h2]; exact hA _ (by omega) (by omega)
  have rB : ∀ d < 16, d % 4 = 0 → ∀ s : State, s.wr = s₀.wr →
      InRegions s.wr (B.setWidth 64 + BitVec.ofNat 64 (16 * j + d)) 4 := fun d hd hd4 s h2 => by
    rw [h2]; exact hB _ (by omega) (by omega)
  obtain ⟨s₁, e₁, c₁, g₁, rd₁, wr₁⟩ := copyWord_ok (d := 0) (by decide) (by decide) hj hfA hfB hsep
    (rA 0 (by decide) (by decide) s hi.rd hi.wr) (rB 0 (by decide) (by decide) s hi.wr) hi.src hi.dst
    (by simpa using hi.cp)
  obtain ⟨s₂, e₂, c₂, g₂, rd₂, wr₂⟩ := copyWord_ok (d := 4) (by decide) (by decide) hj hfA hfB hsep
    (rA 4 (by decide) (by decide) s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr))
    (rB 4 (by decide) (by decide) s₁ (wr₁.trans hi.wr))
    (by rw [g₁ _ (by decide), hi.src]) (by rw [g₁ _ (by decide), hi.dst]) (by simpa using c₁)
  obtain ⟨s₃, e₃, c₃, g₃, rd₃, wr₃⟩ := copyWord_ok (d := 8) (by decide) (by decide) hj hfA hfB hsep
    (rA 8 (by decide) (by decide) s₂ (rd₂.trans (rd₁.trans hi.rd)) (wr₂.trans (wr₁.trans hi.wr)))
    (rB 8 (by decide) (by decide) s₂ (wr₂.trans (wr₁.trans hi.wr)))
    (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.src]) (by rw [g₂ _ (by decide), g₁ _ (by decide), hi.dst])
    c₂
  obtain ⟨s₄, e₄, c₄, g₄, rd₄, wr₄⟩ := copyWord_ok (d := 12) (by decide) (by decide) hj hfA hfB hsep
    (rA 12 (by decide) (by decide) s₃ (rd₃.trans (rd₂.trans (rd₁.trans hi.rd)))
      (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (rB 12 (by decide) (by decide) s₃ (wr₃.trans (wr₂.trans (wr₁.trans hi.wr))))
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.src])
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.dst]) c₃
  have g₄' : ∀ r, r ≠ .eax → s₄.gpr r = s.gpr r := fun r hr => by rw [g₄ r hr, g₃ r hr, g₂ r hr, g₁ r hr]
  obtain ⟨s₅, e₅, a₅, -, o₅, m₅, rd₅, wr₅⟩ := addI_ok s₄ .edx 16
  obtain ⟨s₆, e₆, a₆, -, o₆, m₆, rd₆, wr₆⟩ := addI_ok s₅ .ebx 16
  obtain ⟨s₇, e₇, c₇, z₇, o₇, m₇, rd₇, wr₇⟩ := subI_ok s₆ .ecx 1
  refine WP.of_runBlock ⟨s₇, by
    rw [show ([.mov .eax (.mem (at_ .edx 0)), .store (at_ .ebx 0) .eax, .mov .eax (.mem (at_ .edx 4)),
      .store (at_ .ebx 4) .eax, .mov .eax (.mem (at_ .edx 8)), .store (at_ .ebx 8) .eax,
      .mov .eax (.mem (at_ .edx 12)), .store (at_ .ebx 12) .eax, addI .edx 16, addI .ebx 16, subI .ecx 1] :
        List Instr) =
      [.mov .eax (.mem (at_ .edx 0)), .store (at_ .ebx 0) .eax] ++ ([.mov .eax (.mem (at_ .edx 4)),
      .store (at_ .ebx 4) .eax] ++ ([.mov .eax (.mem (at_ .edx 8)), .store (at_ .ebx 8) .eax] ++
      ([.mov .eax (.mem (at_ .edx 12)), .store (at_ .ebx 12) .eax] ++ ([addI .edx 16] ++
      ([addI .ebx 16] ++ [subI .ecx 1]))))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, runBlock_app, e₅, Option.bind_some,
      runBlock_app, e₆, Option.bind_some, e₇], ?_⟩
  have hc₇ : s₇.gpr .ecx = BitVec.ofNat 32 (c - (j + 1)) := by
    rw [c₇, o₆ _ (by decide), o₅ _ (by decide), g₄' _ (by decide), hi.cnt,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega),
      show c - j - 1 = c - (j + 1) by omega]
  have hm : s₇.mem = s₄.mem := by rw [m₇, m₆, m₅]
  have hinv : CopyInv A B c s₀ (j + 1) s₇ := by
    refine ⟨?_, ?_, hc₇, ⟨fun t ht => ?_, by rw [hm]; exact c₄.frame⟩, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₇, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₇, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₇ _ (by decide), o₆ _ (by decide), a₅, g₄' _ (by decide), hi.src,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, VG.Offset.add_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₇ _ (by decide), a₆, o₅ _ (by decide), g₄' _ (by decide), hi.dst,
        show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, VG.Offset.add_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [hm]; exact c₄.copied t (by omega)
    · rw [o₇ r h3, o₆ r h2, o₅ r h1, g₄' r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₇.zf = some (decide (c - (j + 1) = 0)) := by
    rw [z₇, ← c₇, hc₇, ofNat32_beq_zero (by omega)]
  by_cases hl : j + 1 = c
  · refine .inl ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega),
      by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨(eval_ne s₇).trans (by rw [hz]; simp; omega), c - (j + 1), by omega, j + 1, rfl,
      by omega, hinv⟩

end VG.Proof.Sm4.X86
