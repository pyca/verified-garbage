import VerifiedGarbage.Proof.Modes.X86_64.Setup
import VerifiedGarbage.Proof.Modes.Words
import VerifiedGarbage.Proof.Framework.Range

/-!
# Copying and XORing blocks a word at a time, on x86-64

`copyN_wp`: `k` words (`copyW`) copy the block at `Q` (`rs + os`) to `P`
(`rd + od`); `xorN_wp`: `k` words (`xorW`) XOR it into `P`'s. Both go
through the register `t`, change no other register, and leave memory
`over` the `8 k` bytes at `P`. Every block the modes move (the IV, a block
of the data or of the core's buffer) is one of these.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.Modes.X86_64

/-- `xor d, [b + o]`. -/
theorem xorMem_ok (s : State) (d b : Reg) (o : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr b + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa [.alu .xor d (.mem (at_ b o))] s = some s' ∧
      s'.gpr d = s.gpr d ^^^ s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64 ∧ (∀ r, r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨(arithFlags s (s.gpr d ^^^ s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64) false false).setReg d
    (s.gpr d ^^^ s.mem.readW (s.gpr b + BitVec.ofNat 64 o) 64), ?_, by simp only [RegUpd.gpr_setReg_self],
    fun r h => by simp only [RegUpd.gpr_setReg_of_ne _ _ h, RegUpd.gpr_arithFlags], rfl, rfl, rfl⟩
  simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, State.ea,
    ofInt_nat, hr, ite_true, Option.bind_some]

/-- What the `k` word steps from `s` keep, and their memory. -/
structure NInv (t : Reg) (s : State) (m : Mem) (s' : State) : Prop where
  regs : ∀ x, x ≠ t → s'.gpr x = s.gpr x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : s'.mem = m

/-- The hypotheses of both, with `P = rd + od` and `Q = rs + os`: the words
of `P` writable, `Q`'s readable, the blocks apart, and `t` neither base
register. -/
structure NPre (k : Nat) (s : State) (t rd rs : Reg) (od os : Nat) (P Q : Addr) : Prop where
  hP : s.gpr rd + BitVec.ofNat 64 od = P
  hQ : s.gpr rs + BitVec.ofNat 64 os = Q
  td : t ≠ rd
  ts : t ≠ rs
  wP : ∀ w < k, InRegions s.wr (P + BitVec.ofNat 64 (8 * w)) 8
  rQ : ∀ w < k, InRegions (s.rd ++ s.wr) (Q + BitVec.ofNat 64 (8 * w)) 8
  sep : Region.Disjoint ⟨P, 8 * k⟩ ⟨Q, 8 * k⟩
  fit : 8 * k ≤ 2 ^ 64

theorem copyN_wp {k : Nat} {s : State} {t rd rs : Reg} {od os : Nat} {P Q : Addr} (h : NPre k s t rd rs od os P Q) :
    WP isa (.block ((List.range k).flatMap (copyW t rd rs od os))) s
      (NInv t s (over s.mem P (8 * k) fun i => s.mem (Q + BitVec.ofNat 64 i))) := by
  have hfit := h.fit
  refine wp_range_flatMap (M := isa) (N := k) (fun w s' => NInv t s (over s.mem P (8 * w) fun i =>
      s.mem (Q + BitVec.ofNat 64 i)) s')
    (fun w s' hw hi => ?_) k (Nat.le_refl _) s ⟨fun _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero, over_zero]⟩
  have hP' : s'.gpr rd + BitVec.ofNat 64 (od + 8 * w) = P + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.td), ← addr_add, h.hP]
  have hQ' : s'.gpr rs + BitVec.ofNat 64 (os + 8 * w) = Q + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.ts), ← addr_add, h.hQ]
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ld_ok s' t rs (os + 8 * w)
    (by rw [hi.rd, hi.wr, hQ']; exact h.rQ w hw)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := stM_ok s₁ rd t (od + 8 * w)
    (by rw [wr₁, hi.wr, o₁ _ (Ne.symm h.td), hP']; exact h.wP w hw)
  refine WP.of_runBlock ⟨s₂, by
    rw [copyW, show ([.mov t (.mem (at_ rs (os + 8 * w))), .store (at_ rd (od + 8 * w)) t] : List Instr) =
      [.mov t (.mem (at_ rs (os + 8 * w)))] ++ [.store (at_ rd (od + 8 * w)) t] from rfl, runBlock_app, e₁,
      Option.bind_some, e₂],
    fun x hx => by rw [g₂, o₁ x hx, hi.regs x hx], by rw [rd₂, rd₁, hi.rd], by rw [wr₂, wr₁, hi.wr], ?_⟩
  rw [m₂, v₁, m₁, o₁ _ (Ne.symm h.td), hP', hQ', hi.mem]
  refine over_step (by omega) fun x => ?_
  rw [writeW_readW_apply]
  split
  · rename_i hx
    rw [addr_add, over_sep (h.sep.sub_left (Region.sub_prefix (by omega))) (by omega) (by omega)]
  · rfl

theorem xorN_wp {k : Nat} {s : State} {t rd rs : Reg} {od os : Nat} {P Q : Addr} (h : NPre k s t rd rs od os P Q) :
    WP isa (.block ((List.range k).flatMap (xorW t rd rs od os))) s
      (NInv t s (over s.mem P (8 * k) fun i => s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (Q + BitVec.ofNat 64 i))) := by
  have hfit := h.fit
  refine wp_range_flatMap (M := isa) (N := k) (fun w s' => NInv t s (over s.mem P (8 * w) fun i =>
      s.mem (P + BitVec.ofNat 64 i) ^^^ s.mem (Q + BitVec.ofNat 64 i)) s')
    (fun w s' hw hi => ?_) k (Nat.le_refl _) s ⟨fun _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero, over_zero]⟩
  have hP' : s'.gpr rd + BitVec.ofNat 64 (od + 8 * w) = P + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.td), ← addr_add, h.hP]
  have hQ' : s'.gpr rs + BitVec.ofNat 64 (os + 8 * w) = Q + BitVec.ofNat 64 (8 * w) := by
    rw [hi.regs _ (Ne.symm h.ts), ← addr_add, h.hQ]
  obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := ld_ok s' t rd (od + 8 * w)
    (by rw [hi.rd, hi.wr, hP']; exact inRd (h.wP w hw))
  obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := xorMem_ok s₁ t rs (os + 8 * w)
    (by rw [rd₁, wr₁, hi.rd, hi.wr, o₁ _ (Ne.symm h.ts), hQ']; exact h.rQ w hw)
  obtain ⟨s₃, e₃, m₃, g₃, rd₃, wr₃⟩ := stM_ok s₂ rd t (od + 8 * w)
    (by rw [wr₂, wr₁, hi.wr, o₂ _ (Ne.symm h.td), o₁ _ (Ne.symm h.td), hP']; exact h.wP w hw)
  refine WP.of_runBlock ⟨s₃, by
    rw [xorW, show ([.mov t (.mem (at_ rd (od + 8 * w))), .alu .xor t (.mem (at_ rs (os + 8 * w))),
      .store (at_ rd (od + 8 * w)) t] : List Instr) = [.mov t (.mem (at_ rd (od + 8 * w)))] ++
      ([.alu .xor t (.mem (at_ rs (os + 8 * w)))] ++ [.store (at_ rd (od + 8 * w)) t]) from rfl, runBlock_app, e₁,
      Option.bind_some, runBlock_app, e₂, Option.bind_some, e₃],
    fun x hx => by rw [g₃, o₂ x hx, o₁ x hx, hi.regs x hx], by rw [rd₃, rd₂, rd₁, hi.rd],
    by rw [wr₃, wr₂, wr₁, hi.wr], ?_⟩
  rw [m₃, v₂, v₁, m₂, m₁, o₂ _ (Ne.symm h.td), o₁ _ (Ne.symm h.td), o₁ _ (Ne.symm h.ts), hP', hQ', hi.mem]
  refine over_step (by omega) fun x => ?_
  rw [writeW_xor_apply]
  split
  · rename_i hx
    rw [addr_add, addr_add, over_out (by rw [off_self P (by omega)]; omega),
      over_sep (h.sep.sub_left (Region.sub_prefix (by omega))) (by omega) (by omega)]
  · rfl

end VG.Proof.Modes.X86_64
