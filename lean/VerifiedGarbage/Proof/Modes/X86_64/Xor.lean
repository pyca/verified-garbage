import VerifiedGarbage.Proof.Modes.X86_64.Core

/-!
# XORing blocks on x86-64

`xorBlocks_wp`: the loop `xorBlocks` XORs `c ≥ 1` blocks of 16 bytes at
`rax` into those at `rbx` (areas that do not overlap), through `rbp`,
counting down `rcx`, and changes nothing else in memory.
-/

namespace VG.Proof.Modes.X86_64

open VG VG.X86_64 VG.Impl.Modes.X86_64

/-- A byte of a little-endian word stored from the XOR of two loads. -/
theorem writeW_xor_apply (m m₁ m₂ : Mem) (a c e x : Addr) :
    m.writeW a (m₁.readW c 64 ^^^ m₂.readW e 64) x =
      if (x - a).toNat < 8 then m₁ (c + BitVec.ofNat 64 (x - a).toNat) ^^^ m₂ (e + BitVec.ofNat 64 (x - a).toNat)
      else m x := by
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq]
  split
  · rename_i h
    rw [BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read m₁ c (n := 8) h, Mem.extractLsb'_read m₂ e (n := 8) h]
  · rfl

/-- `mov rbp, [rax + d]; xor rbp, [rbx + d]; mov [rbx + d], rbp`. -/
theorem xorWord_ok (s : State) (d : Nat) (hr : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 d) 8)
    (hr' : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 d) 8)
    (hw : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa [.mov .rbp (.mem (at_ .rax d)), .alu .xor .rbp (.mem (at_ .rbx d)),
        .store (at_ .rbx d) .rbp] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d)
        (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64 ^^^ s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 d) 64) ∧
      (∀ r, r ≠ .rbp → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64 ^^^ s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 d) 64
  let s₁ := s.setReg .rbp (s.mem.readW (s.gpr .rax + BitVec.ofNat 64 d) 64)
  let s₂ := (arithFlags s₁ v false false).setReg .rbp v
  refine ⟨{ s₂ with mem := s.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 d) v }, ?_, rfl,
    fun r hr => ?_, rfl, rfl⟩
  · simp only [at_, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, State.store64,
      State.ea, ofInt_nat, hr, ite_true, Option.map_some, Option.bind_some, RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_of_ne _ _ (show Reg.rbx ≠ .rbp by decide), RegUpd.wr_setReg, RegUpd.rd_setReg,
      RegUpd.mem_setReg, hr', hw, RegUpd.wr_arithFlags, RegUpd.rd_arithFlags, RegUpd.mem_arithFlags,
      RegUpd.gpr_arithFlags]
    rfl
  · show s₂.gpr r = _
    simp only [s₂, s₁, RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- XORing, after `j` of `c` blocks. -/
structure XorInv (A B : Addr) (c : Nat) (s₀ : State) (j : Nat) (s : State) : Prop where
  rax : s.gpr .rax = A + BitVec.ofNat 64 (16 * j)
  rbx : s.gpr .rbx = B + BitVec.ofNat 64 (16 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (c - j)
  xored : ∀ t < 16 * j, s.mem (B + BitVec.ofNat 64 t) =
    s₀.mem (A + BitVec.ofNat 64 t) ^^^ s₀.mem (B + BitVec.ofNat 64 t)
  rest : ∀ t, 16 * j ≤ t → t < 16 * c → s.mem (B + BitVec.ofNat 64 t) = s₀.mem (B + BitVec.ofNat 64 t)
  frame : Frame [⟨B, 16 * c⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem xorBlocks_wp {A B : Addr} {c : Nat} {s₀ : State} (hc : 0 < c) (hc16 : c < 2 ^ 59)
    (hA : ∀ t < 2 * c, InRegions (s₀.rd ++ s₀.wr) (A + BitVec.ofNat 64 (8 * t)) 8)
    (hB : ∀ t < 2 * c, InRegions s₀.wr (B + BitVec.ofNat 64 (8 * t)) 8)
    (hsep : Region.Disjoint ⟨A, 16 * c⟩ ⟨B, 16 * c⟩) (hs : XorInv A B c s₀ 0 s₀) :
    WP isa Core.xorBlocks s₀ (XorInv A B c s₀ c) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = c - j ∧ j < c ∧ XorInv A B c s₀ j s)
    (fun n s hs => ?_) c s₀ ⟨0, by omega, hc, hs⟩
  obtain ⟨j, rfl, hj, hi⟩ := hs
  have hA0 := hA (2 * j) (by omega)
  have hA1 := hA (2 * j + 1) (by omega)
  have hB0 := hB (2 * j) (by omega)
  have hB1 := hB (2 * j + 1) (by omega)
  have hn : 16 * c < 2 ^ 64 := by omega
  have hAs : ∀ t < 16 * c, s.mem (A + BitVec.ofNat 64 t) = s₀.mem (A + BitVec.ofNat 64 t) := fun t ht =>
    hi.frame.bytes (R := ⟨A, 16 * c⟩) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hsep)
      (by simp only; omega) ht
  have rB : ∀ (st : State), st.rd = s₀.rd → st.wr = s₀.wr → ∀ e, e < 2 * c →
      InRegions (st.rd ++ st.wr) (B + BitVec.ofNat 64 (8 * e)) 8 := fun st h1 h2 e he => by
    rw [h1, h2]; exact (let ⟨r, hr, hc⟩ := hB e he; ⟨r, List.mem_append_right _ hr, hc⟩)
  obtain ⟨s₁, e₁, m₁, g₁, rd₁, wr₁⟩ := xorWord_ok s 0
    (by rw [hi.rd, hi.wr, hi.rax, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hA0)
    (by rw [hi.rbx, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact rB s hi.rd hi.wr _ (by omega))
    (by rw [hi.wr, hi.rbx, addr_add, show 16 * j + 0 = 8 * (2 * j) by omega]; exact hB0)
  obtain ⟨s₂, e₂, m₂, g₂, rd₂, wr₂⟩ := xorWord_ok s₁ 8
    (by rw [rd₁, wr₁, hi.rd, hi.wr, g₁ _ (by decide), hi.rax, addr_add,
      show 16 * j + 8 = 8 * (2 * j + 1) by omega]; exact hA1)
    (by rw [g₁ _ (by decide), hi.rbx, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega]
        exact rB s₁ (rd₁.trans hi.rd) (wr₁.trans hi.wr) _ (by omega))
    (by rw [wr₁, hi.wr, g₁ _ (by decide), hi.rbx, addr_add, show 16 * j + 8 = 8 * (2 * j + 1) by omega]; exact hB1)
  obtain ⟨s₃, e₃, a₃, o₃, m₃, rd₃, wr₃⟩ := addImm_ok s₂ .rax 16
  obtain ⟨s₄, e₄, a₄, o₄, m₄, rd₄, wr₄⟩ := addImm_ok s₃ .rbx 16
  obtain ⟨s₅, e₅, c₅, z₅, o₅, m₅, rd₅, wr₅⟩ := subImm_ok s₄ .rcx 1
  refine WP.of_runBlock ⟨s₅, by
    rw [show ([Instr.mov .rbp (.mem (at_ .rax 0)), .alu .xor .rbp (.mem (at_ .rbx 0)), .store (at_ .rbx 0) .rbp,
      .mov .rbp (.mem (at_ .rax 8)), .alu .xor .rbp (.mem (at_ .rbx 8)), .store (at_ .rbx 8) .rbp,
      .alu .add .rax (.imm 16), .alu .add .rbx (.imm 16), .alu .sub .rcx (.imm 1)] : List Instr) =
      [.mov .rbp (.mem (at_ .rax 0)), .alu .xor .rbp (.mem (at_ .rbx 0)), .store (at_ .rbx 0) .rbp] ++
      ([.mov .rbp (.mem (at_ .rax 8)), .alu .xor .rbp (.mem (at_ .rbx 8)), .store (at_ .rbx 8) .rbp] ++
      ([.alu .add .rax (.imm 16)] ++ ([.alu .add .rbx (.imm 16)] ++ [.alu .sub .rcx (.imm 1)]))) from rfl,
      runBlock_app, e₁, Option.bind_some, runBlock_app, e₂, Option.bind_some, runBlock_app, e₃,
      Option.bind_some, runBlock_app, e₄, Option.bind_some, e₅], ?_⟩
  have r1 : s₁.gpr .rbx = B + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rbx]
  have a1 : s₁.gpr .rax = A + BitVec.ofNat 64 (16 * j) := by rw [g₁ _ (by decide), hi.rax]
  have hm : s₅.mem = s₁.mem.writeW (B + BitVec.ofNat 64 (16 * j + 8))
      (s₁.mem.readW (A + BitVec.ofNat 64 (16 * j + 8)) 64 ^^^ s₁.mem.readW (B + BitVec.ofNat 64 (16 * j + 8)) 64) := by
    rw [m₅, m₄, m₃, m₂, r1, a1, addr_add, addr_add]
  have hm₁ : s₁.mem = s.mem.writeW (B + BitVec.ofNat 64 (16 * j))
      (s.mem.readW (A + BitVec.ofNat 64 (16 * j)) 64 ^^^ s.mem.readW (B + BitVec.ofNat 64 (16 * j)) 64) := by
    rw [m₁, hi.rbx, hi.rax, addr_add, addr_add, Nat.add_zero]
  -- `s₁` and `s` agree on `A`'s area, and on `B`'s beyond the first word.
  have hA₁ : ∀ t < 16 * c, s₁.mem (A + BitVec.ofNat 64 t) = s.mem (A + BitVec.ofNat 64 t) := fun t ht => by
    rw [hm₁, writeW_xor_apply, ite_eq_right (not_in_of_disjoint hsep ht (by omega) hn)]
  have hB₁ : ∀ t, 16 * j + 8 ≤ t → t < 16 * c → s₁.mem (B + BitVec.ofNat 64 t) = s.mem (B + BitVec.ofNat 64 t) :=
    fun t h1 h2 => by
      rw [hm₁, writeW_xor_apply, ite_eq_right (off_sub_not B (Or.inr (by omega)) (by omega) (by omega) (by omega))]
  have hinv : XorInv A B c s₀ (j + 1) s₅ := by
    refine ⟨?_, ?_, ?_, fun t ht => ?_, fun t h1 h2 => ?_, hi.frame.trans fun x hx => ?_, fun r h1 h2 h3 h4 => ?_,
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
    · rw [hm, writeW_xor_apply]
      by_cases h8 : 16 * j + 8 ≤ t
      · rw [ite_eq_left (by rw [off_sub_toNat B h8 (by omega)]; omega), off_sub_toNat B h8 (by omega), addr_add,
          addr_add, show 16 * j + 8 + (t - (16 * j + 8)) = t by omega, hA₁ t (by omega), hB₁ t h8 (by omega),
          hAs t (by omega), hi.rest t (by omega) (by omega)]
      · rw [ite_eq_right (off_sub_not B (Or.inl (by omega)) (by omega) (by omega) (by omega)), hm₁,
          writeW_xor_apply]
        by_cases h0 : 16 * j ≤ t
        · rw [ite_eq_left (by rw [off_sub_toNat B h0 (by omega)]; omega), off_sub_toNat B h0 (by omega), addr_add,
            addr_add, show 16 * j + (t - 16 * j) = t by omega, hAs t (by omega), hi.rest t h0 (by omega)]
        · rw [ite_eq_right (off_sub_not B (Or.inl (by omega)) (by omega) (by omega) (by omega))]
          exact hi.xored t (by omega)
    · rw [hm, writeW_xor_apply, ite_eq_right (off_sub_not B (Or.inr (by omega)) (by omega) (by omega) (by omega)),
        hB₁ t (by omega) h2, hi.rest t (by omega) h2]
    · have hout : ∀ e, e + 8 ≤ 16 * c → ¬ (x - (B + BitVec.ofNat 64 e)).toNat < 8 := fun e he h =>
        hx _ (List.mem_singleton_self _) (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))
      rw [hm, writeW_xor_apply, ite_eq_right (hout _ (by omega)), hm₁, writeW_xor_apply,
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
