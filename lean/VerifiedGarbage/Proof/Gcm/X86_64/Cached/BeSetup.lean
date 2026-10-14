module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.CtrsBe
import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The setup of the counters added to as bytes

`beSetup_ok`: `StitchZH.beSetup off` stores the constants `beFour` and
`sixteen` at `r11 + 896` and `r11 + 912`, and leaves in `r10` the 32-bit
block index read from `rsp + off`, less one, in its top byte.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_)
open VG.Impl.Gcm.X86_64.StitchZH (beSetup)
open VG.Proof.Gcm.X86_64 (beFour)
open VG.Proof.Gcm.X86_64.StitchZ (sixteen)

theorem pslldq_beFour : XShiftOp.pslldq.eval ((0 : BitVec 64) ++ (0x0400000000000000 : BitVec 64)) 8 = beFour := by
  decide

theorem sixteen_eq : (0 : BitVec 64) ++ (16 : BitVec 64) = sixteen := by decide

/-- The constants of `StitchZH.beSetup`. -/
theorem beConsts_ok (s : State)
    (h896 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 896) 16)
    (h912 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 912) 16) :
    WP isa (.block ((beSetup 0).take 7)) s fun t =>
      t.mem = (s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW
        (s.gpr .r11 + BitVec.ofNat 64 912) sixteen ∧
      (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ (∀ x, x ≠ .xmm13 → ∀ l < 4, t.zlane x l = s.zlane x l) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have ea : ∀ (t : State) (b : Reg) (d : Nat), t.ea (at_ b d) = t.gpr b + BitVec.ofNat 64 d := fun t b d => by
    rw [VG.Proof.Gcm.X86_64.Pclmul.ea_at, BitVec.ofInt_natCast]
  apply WP.of_runBlock
  simp only [beSetup, List.take, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, ea,
    State.store128_eq, State.lane, RegUpd.xmm_setV, ↓reduceIte, State.setMem_wr, State.setMem_gpr, State.setMem_mem, RegUpd.gpr_setV, RegUpd.wr_setV, RegUpd.mem_setV,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, reduceCtorEq,
    h896, h912, Option.some.injEq, exists_eq_left', pslldq_beFour, sixteen_eq]
  refine ⟨?_, fun r hr => ?_, fun x hx l hl => ?_, ?_, ?_⟩ <;> try trivial
  · simp only [hr, ↓reduceIte]
  · simp [State.zlane, State.lane, State.setMem, State.setV, State.setReg, hx]

/-- `StitchZH.beSetup off`. -/
theorem beSetup_ok (off : Nat) (s : State) {i : BitVec 32}
    (h896 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 896) 16)
    (h912 : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 912) 16)
    (hI : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 off) 4)
    (hi : ((s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW (s.gpr .r11 + BitVec.ofNat 64 912)
      sixteen).readW (s.gpr .rsp + BitVec.ofNat 64 off) 32 = i) :
    WP isa (.block (beSetup off)) s fun t =>
      t.gpr .r10 = ((i - 1) <<< 24).setWidth 64 ∧
      t.mem = (s.mem.writeW (s.gpr .r11 + BitVec.ofNat 64 896) beFour).writeW
        (s.gpr .r11 + BitVec.ofNat 64 912) sixteen ∧
      (∀ r, r ≠ .r10 → t.gpr r = s.gpr r) ∧ (∀ x, x ≠ .xmm13 → ∀ l < 4, t.zlane x l = s.zlane x l) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [show beSetup off = (beSetup 0).take 7 ++ [.mov32 .r10 (.mem (at_ .rsp off)), .alu32 .sub .r10 (.imm 1),
    .shift32 .shl .r10 24] from rfl, WP.block_append_iff]
  refine WP.mono (beConsts_ok s h896 h912) fun t ⟨m, g, z, rd, wr⟩ => ?_
  have ea : t.ea (at_ .rsp off) = s.gpr .rsp + BitVec.ofNat 64 off := by
    rw [VG.Proof.Gcm.X86_64.Pclmul.ea_at, BitVec.ofInt_natCast, g _ (by decide)]
  have hI' : InRegions (t.rd ++ t.wr) (s.gpr .rsp + BitVec.ofNat 64 off) 4 := by rw [rd, wr]; exact hI
  have h24 : 1 ≤ 24 ∧ 24 ≤ 31 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, isa, readSrc32, State.load32, ea, hI', ↓reduceIte,
    Option.map_some, execAlu32, Option.bind_some, execShift32, State.setReg32, RegUpd.gpr_setReg_self, m, hi,
    h24, and_self, RegUpd.setWidth_setWidth_32, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, fun r hr => ?_, fun x hx l hl => ?_, ?_, ?_⟩ <;> try trivial
  · simp only [RegUpd.gpr_setReg, hr, ↓reduceIte, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags]
    exact g r hr
  · exact z x hx l hl

end VG.Proof.Gcm.X86_64.StitchZH
