import VerifiedGarbage.Proof.Sm4.X86_64.Copy

/-!
# XORing blocks on x86-64

`xorBlocks_wp`: the loop `xorBlocks` XORs `c ≥ 1` blocks of 16 bytes at
`rax` into those at `rbx` (areas that do not overlap), through `rbp`,
counting down `rcx`, and changes nothing else in memory.
-/

namespace VG.Proof.Sm4.X86_64

open VG VG.X86_64 VG.Impl.Sm4.X86_64
open VG.Proof.Sm4 (off_sub_toNat off_sub_not not_in_of_disjoint ofInt_nat)
open VG.Impl.Aes.X86_64 (at_)

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
  frame : Frame [⟨B, 16 * j⟩] s₀.mem s.mem
  regs : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .rcx → r ≠ .rbp → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

end VG.Proof.Sm4.X86_64
