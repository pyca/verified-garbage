import VerifiedGarbage.Proof.Modes.X86_64.Xor
import VerifiedGarbage.Impl.Modes.X86_64.Cbc

/-!
# Copying blocks on x86-64

`copyBlocks_wp`: the loop `copyBlocks` copies `c ≥ 1` blocks of 16 bytes at
`rbx` to `rax` (areas that do not overlap), through `rbp`, counting down
`rcx`, and changes nothing else in memory. `writeW_readW_apply`: the bytes
of a stored load.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64

/-- A byte of a little-endian word stored from a load. -/
theorem writeW_readW_apply (m m₁ : Mem) (a c x : Addr) :
    m.writeW a (m₁.readW c 64) x =
      if (x - a).toNat < 8 then m₁ (c + BitVec.ofNat 64 (x - a).toNat) else m x := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  split
  · rename_i h
    rw [Mem.readW, BitVec.setWidth_eq, Mem.extractLsb'_read m₁ c (n := 8) h]
  · rfl

/-- `mov rbp, [rbx + d]; mov [rax + d], rbp`. -/
theorem copyWord_ok (s : State) (d : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.mov .rbp (.mem (at_ .rbx d)), .store (at_ .rax d) .rbp] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rax + BitVec.ofNat 64 d) (s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 d) 64
  let s₁ := s.setReg .rbp v
  refine ⟨{ s₁ with mem := s.mem.writeW (s.gpr .rax + BitVec.ofNat 64 d) v }, ?_, rfl, fun r hr => ?_, rfl, rfl⟩
  · simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, State.store64,
      State.ea, ofInt_nat, hr, ite_true, Option.map_some, RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_of_ne _ _ (show Reg.rax ≠ .rbp by decide), RegUpd.wr_setReg, RegUpd.mem_setReg, hw]
    rfl
  · show s₁.gpr r = _
    simp only [s₁, RegUpd.gpr_setReg_of_ne _ _ hr]

/-- Copying, after `j` of `c` blocks from `S` to `T`. -/
structure CopyInv (S T : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  rax : s.gpr .rax = T + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = S + BitVec.ofNat 64 (16 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (c - j)
  copied : ∀ t < 16 * j, s.mem (T + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t)
  frame : Frame [⟨T, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem copyBlocks_wp {S T : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c < 2 ^ 59)
    (hS : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (S + BitVec.ofNat 64 (8 * t)) 8)
    (hT : ∀ t < 2 * c, InRegions s₀.wr (T + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨S, 16 * c⟩ ⟨T, 16 * c⟩) (hs : CopyInv S T c s₀ 0 s₀) :
    WP isa Core.copyBlocks s₀ (CopyInv S T c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ CopyInv S T c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hn : 16 * c < 2 ^ 64 := by omega
  have hSs : ∀ t < 16 * c, s.mem (S + BitVec.ofNat 64 t) = s₀.mem (S + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨S, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := copyWord_ok s 0
    (by rw [hi.rd, hi.wr, hi.rbx, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hS _ (by omega))
    (by rw [hi.wr, hi.rax, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hT _ (by omega))
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := copyWord_ok s₁ 8
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.rbx, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega]; exact hS _ (by omega))
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.rax, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega]
        exact hT _ (by omega))
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rax 16
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rbx 16
  obtain ⟨s₅, e₅, c₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .rcx 1
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.mov .rbp (.mem (at_ .rbx 0)), .store (at_ .rax 0) .rbp,
      .mov .rbp (.mem (at_ .rbx 8)), .store (at_ .rax 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr) =
      [.mov .rbp (.mem (at_ .rbx 0)), .store (at_ .rax 0) .rbp] ++
      ([.mov .rbp (.mem (at_ .rbx 8)), .store (at_ .rax 8) .rbp] ++
      ([.alu .add .rax (.imm 16)] ++ ([.alu .add .rbx (.imm 16)] ++ [.alu .sub .rcx (.imm 1)]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have r1 : s₁.gpr .rbx = S + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rbx]
  have a1 : s₁.gpr .rax = T + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rax]
  have hm : s₅.mem = s₁.mem.writeW (T + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (S + BitVec.ofNat 64 (16 * j + 8)) 64) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (T + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (S + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.rbx, hi.rax, addr_add, addr_add, Nat.add_zero]
  have hS₁ : ∀ t < 16 * c, s₁.mem (S + BitVec.ofNat 64 t) = s.mem (S + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_readW_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega) hn)]
  have hinv : CopyInv S T c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, ?_, fun t ht => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
      by rw [rd₅, rd₄, rd₃, rd₂, rd₁, hi.rd], by rw [wr₅, wr₄, wr₃, wr₂, wr₁, hi.wr]⟩
    · rw [o₅ _ (by decide), o₄ _ (by decide), a₃, g₂ _ (by decide), a1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [o₅ _ (by decide), a₄, o₃ _ (by decide), g₂ _ (by decide), r1,
        show (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 from rfl, addr_add,
        show 16 * j + 16 = 16 * (j + 1) by omega]
    · rw [c₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
        show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, VG.Offset.ofNat_sub_ofNat (by omega),
        show c - j - 1 = c - (j + 1) by omega]
    · rw [hm, writeW_readW_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat T h8 (by omega)]; omega), off_sub_toNat T h8 (by omega), addr_add,
          show 16 * j + 8 + (t - (16 * j + 8)) = t by omega, hS₁ t (by omega), hSs t (by omega)]
      · rw [ite_eq_right (off_sub_not T (Or.inl (by omega)) (by omega) (by omega) (by omega)), hm₁,
          writeW_readW_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat T h0 (by omega)]; omega), off_sub_toNat T h0 (by omega), addr_add,
            show 16 * j + (t - 16 * j) = t by omega, hSs t (by omega)]
        · rw [ite_eq_right (off_sub_not T (Or.inl (by omega)) (by omega) (by omega) (by omega))]
          exact hi.copied t (by omega)
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (T + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base T he _ (by simp only [Region.Contains]; omega))
      rw [hm, writeW_readW_apply, ite_eq_right (hout _ (by omega)), hm₁, writeW_readW_apply,
        ite_eq_right (hout _ (by omega))]
    · rw [o₅ r h3, o₄ r h2, o₃ r h1, g₂ r h4, g₁ r h4, hi.regs r h1 h2 h3 h4]
  have hz : s₅.zf = some (decide (c - (j + 1) = 0)) := by
    rw [z₅, o₄ _ (by decide), o₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), hi.rcx,
      show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl,
      VG.Offset.ofNat_sub_ofNat_beq (by omega) (by decide)]
    simp only [Option.some.injEq, decide_eq_decide]; omega
  by_cases hl : j + 1 = c
  · refine .inl ⟨by simp [X86_64.eval, hz, hl], by rw [show j + 1 = c from hl] at hinv; exact hinv⟩
  · exact .inr ⟨by simp [X86_64.eval, hz]; omega, c - (j + 1), by omega, j + 1, rfl, by omega, hinv⟩

end VG.Proof.Modes.X86_64
