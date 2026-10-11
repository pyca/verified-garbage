import VerifiedGarbage.Proof.Modes.AArch64.Steps
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Framework.Range

/-!
# Copying and XORing blocks a word at a time, on AArch64

As on x86-64 (`Proof/Modes/X86_64/Words.lean`). `copyN_wp`: `k` words
(`copyW`) copy the block at `Q` (`rs + os`) to `P` (`rd + od`); `xorN_wp`:
`k` words (`xorW`) XOR it into `P`'s. Both change only their temporaries,
and leave memory `over` the `8 k` bytes at `P`.
-/

namespace VG.Proof.Modes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.Modes.AArch64
open VG.Impl.Aes.AArch64 (eorR)

/-- What the `k` word steps from `s` keep, and their memory. -/
structure NInv (t u : Reg) (s : State) (m : Mem) (s' : State) : Prop where
  regs : ∀ x, x ≠ t → x ≠ u → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : s'.mem = m

/-- The hypotheses of both, with `P = rd + od` and `Q = rs + os`: the words
of `P` writable, `Q`'s readable, the blocks apart, the offsets within a
load's reach, and the temporaries neither base register. -/
structure NPre (k : Nat) (s : State) (t u rd rs : Reg) (od os : Nat) (P Q : Addr) : Prop where
  hP : s.gpr rd + BitVec.ofNat 64 od = P
  hQ : s.gpr rs + BitVec.ofNat 64 os = Q
  td : t ≠ rd
  ts : t ≠ rs
  ud : u ≠ rd
  us : u ≠ rs
  od8 : od % 8 = 0
  os8 : os % 8 = 0
  odk : od + 8 * k ≤ 32768
  osk : os + 8 * k ≤ 32768
  wP : ∀ w < k, InRegions s.wr (P + BitVec.ofNat 64 (8 * w)) 8
  rQ : ∀ w < k, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 (8 * w)) 8
  sep : Region.Disjoint ⟨P, 8 * k⟩ ⟨Q, 8 * k⟩
  fit : 8 * k ≤ 2 ^ 64

theorem copyN_wp {k : Nat} {s : State} {t u rd rs : Reg} {od os : Nat} {P Q : Addr}
    (h : NPre k s t u rd rs od os P Q) :
    WP isa (.block ((List.range k).flatMap (copyW t rd rs od os))) s
      (NInv t u s (over s.mem P (8 * k) fun i => s.mem (Q + BitVec.ofNat 64 i))) := by
  have hfit := h.fit
  have := h.od8; have := h.os8; have := h.odk; have := h.osk
  refine wp_range_flatMap (M := isa) (N := k) (fun w s' => NInv t u s (over s.mem P (8 * w) fun i =>
      s.mem (Q + BitVec.ofNat 64 i)) s')
    (fun w s' hw hi => ?_) k (Nat.le_refl _) s ⟨fun _ _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero, over_zero]⟩
  have hP' : s'.gpr rd + BitVec.ofNat 64 (od + 8 * w) = P + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.td) (Ne.symm h.ud), ← addr_add, h.hP]
  have hQ' : s'.gpr rs + BitVec.ofNat 64 (os + 8 * w) = Q + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.ts) (Ne.symm h.us), ← addr_add, h.hQ]
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldr_ok s' t rs (off := os + 8 * w) ⟨by omega, by omega⟩
    (by rw [hi.rd, hi.wr, hQ']; exact h.rQ w hw)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := str_ok s₁ t rd (off := od + 8 * w) ⟨by omega, by omega⟩
    (by rw [wr₁, hi.wr, o₁ _ (Ne.symm h.td), hP']; exact h.wP w hw)
  refine WP.of_runBlock ⟨s₂, by
    rw [copyW, show ([.ldr .x t rs (os + 8 * w), .str .x t rd (od + 8 * w)] : List Instr) =
      [.ldr .x t rs (os + 8 * w)] ++ [.str .x t rd (od + 8 * w)] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂],
    fun x hx hx' => by rw [g₂, o₁ x hx, hi.regs x hx hx'], by rw [rd₂, rd₁, hi.rd], by rw [wr₂, wr₁, hi.wr], ?_⟩
  rw [m₂, v₁, m₁, o₁ _ (Ne.symm h.td), hP', hQ', hi.mem]
  refine over_step (by omega) fun x => ?_
  rw [writeW_readW_apply]
  split
  · rw [addr_add, over_sep (h.sep.sub_left (Region.sub_prefix (by omega))) (by omega) (by omega)]
  · rfl

theorem xorN_wp {k : Nat} {s : State} {t u rd rs : Reg} {od os : Nat} {P Q : Addr}
    (h : NPre k s t u rd rs od os P Q) (htu : t ≠ u) :
    WP isa (.block ((List.range k).flatMap (xorW t u rd rs od os))) s
      (NInv t u s (over s.mem P (8 * k) fun i => s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (Q + BitVec.ofNat 64 i))) := by
  have hfit := h.fit
  have := h.od8; have := h.os8; have := h.odk; have := h.osk
  refine wp_range_flatMap (M := isa) (N := k) (fun w s' => NInv t u s (over s.mem P (8 * w) fun i =>
      s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (Q + BitVec.ofNat 64 i)) s')
    (fun w s' hw hi => ?_) k (Nat.le_refl _) s ⟨fun _ _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero, over_zero]⟩
  have hP' : s'.gpr rd + BitVec.ofNat 64 (od + 8 * w) = P + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.td) (Ne.symm h.ud), ← addr_add, h.hP]
  have hQ' : s'.gpr rs + BitVec.ofNat 64 (os + 8 * w) = Q + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.ts) (Ne.symm h.us), ← addr_add, h.hQ]
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ldr_ok s' t rd (off := od + 8 * w) ⟨by omega, by omega⟩
    (by rw [hi.rd, hi.wr, hP']; exact inRd (h.wP w hw))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := ldr_ok s₁ u rs (off := os + 8 * w) ⟨by omega, by omega⟩
    (by rw [rd₁, wr₁, hi.rd, hi.wr, o₁ _ (Ne.symm h.ts), hQ']; exact h.rQ w hw)
  obtain ⟨s₃, e₃, v₃, o₃, m₃, rd₃, wr₃⟩ := eor_ok s₂ t t u
  obtain ⟨s₄, e₄, m₄, g₄, rd₄, wr₄⟩ := str_ok s₃ t rd (off := od + 8 * w) ⟨by omega, by omega⟩
    (by rw [wr₃, wr₂, wr₁, hi.wr, o₃ _ (Ne.symm h.td), o₂ _ (Ne.symm h.ud), o₁ _ (Ne.symm h.td), hP']
        exact h.wP w hw)
  refine WP.of_runBlock ⟨s₄, by
    rw [xorW, show ([.ldr .x t rd (od + 8 * w), .ldr .x u rs (os + 8 * w), eorR t t u,
      .str .x t rd (od + 8 * w)] : List Instr) = [.ldr .x t rd (od + 8 * w)] ++ ([.ldr .x u rs (os + 8 * w)] ++
      ([eorR t t u] ++ [.str .x t rd (od + 8 * w)])) from rfl, runBlock_app, e₁, Option.bind_some, runBlock_app,
      e₂, Option.bind_some, runBlock_app, e₃, Option.bind_some, e₄],
    fun x hx hx' => by rw [g₄, o₃ x hx, o₂ x hx', o₁ x hx, hi.regs x hx hx'], by rw [rd₄, rd₃, rd₂, rd₁, hi.rd],
    by rw [wr₄, wr₃, wr₂, wr₁, hi.wr], ?_⟩
  rw [m₄, v₃, v₂, o₂ _ htu, v₁, m₃, m₂, m₁, o₃ _ (Ne.symm h.td), o₂ _ (Ne.symm h.ud), o₁ _ (Ne.symm h.td),
    o₁ _ (Ne.symm h.ts), hP', hQ', hi.mem]
  refine over_step (by omega) fun x => ?_
  rw [writeW_xor_apply]
  split
  · rw [addr_add, addr_add, over_out (by rw [off_self P (by omega)]; omega),
      over_sep (h.sep.sub_left (Region.sub_prefix (by omega))) (by omega) (by omega)]
  · rfl

end VG.Proof.Modes.AArch64
