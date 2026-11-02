module

public import VerifiedGarbage.TCB.PPC64LE.Isa
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Reduce

/-!
# PPC64LE: register reads through writes

Untrusted: everything here is checked by Lean. The lemmas symbolic
execution reads registers with after `State.write` (`gpr_write_self`,
`gpr_write_of_ne`), without unfolding the write into a function on
registers, and the other fields a write keeps; and `exec_ld`/`exec_std`,
the doubleword load and store at an offset, with the side conditions in the
order the proofs ported from AArch64 state them, and likewise `exec_addi'`,
`exec_subi'` and `exec_or_self` (`mr`).
-/

@[expose] public section

namespace VG.PPC64LE.RegUpd

variable (s : State)

theorem gpr_write (r : Reg) (v : BitVec 64) (r' : Reg) :
    (s.write r v).gpr r' = if r' = r then v else s.gpr r' := rfl

theorem gpr_write_self (r : Reg) (v : BitVec 64) : (s.write r v).gpr r = v := by
  simp [State.write]

theorem gpr_write_of_ne {r r' : Reg} (v : BitVec 64) (h : ¬r' = r) : (s.write r v).gpr r' = s.gpr r' := by
  simp [State.write, h]

theorem mem_write (r : Reg) (v : BitVec 64) : (s.write r v).mem = s.mem := rfl
theorem rd_write (r : Reg) (v : BitVec 64) : (s.write r v).rd = s.rd := rfl
theorem wr_write (r : Reg) (v : BitVec 64) : (s.write r v).wr = s.wr := rfl
theorem sp_write (r : Reg) (v : BitVec 64) : (s.write r v).sp = s.sp := rfl
theorem lr_write (r : Reg) (v : BitVec 64) : (s.write r v).lr = s.lr := rfl

end VG.PPC64LE.RegUpd

namespace VG.PPC64LE

/-- `ld t, off(n)`. -/
theorem exec_ld {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) (hn : n ≠ .r0 := by decide) :
    exec (.load .d t n off) s = some (s.write t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) :=
  exec_load_d hn ⟨ho.2, by omega⟩ h

/-- `std t, off(n)`. -/
theorem exec_std {s : State} {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) (hn : n ≠ .r0 := by decide) :
    exec (.store .d t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } :=
  exec_store_d hn ⟨ho.2, by omega⟩ h

/-- `addi d, n, imm`. -/
theorem exec_addi' {s : State} {d n : Reg} {imm : Nat} (h : imm < 32768) (hn : n ≠ .r0 := by decide) :
    exec (.addi d n imm) s = some (s.write d (s.gpr n + BitVec.ofNat 64 imm)) :=
  exec_addi hn h

/-- `subi d, n, imm`. -/
theorem exec_subi' {s : State} {d n : Reg} {imm : Nat} (h : imm < 32768) (hn : n ≠ .r0 := by decide) :
    exec (.subi d n imm) s = some (s.write d (s.gpr n - BitVec.ofNat 64 imm)) :=
  exec_subi hn (by omega)

/-- `mr d, n` (`or d, n, n`). -/
theorem exec_or_self {s : State} {d n : Reg} :
    exec (.logic .or d n n) s = some (s.write d (s.gpr n)) := by
  rw [exec_logic]; simp only [BitVec.or_self]

end VG.PPC64LE

namespace VG.PPC64LE

/-! A symbol address may temporarily change LR, bracketed by a snapshot in
an independent GPR and its restoration. Recognize a complete three-instruction
block; all other blocks must leave LR untouched instruction by instruction. -/


def lrSafeBlock : List Instr → Bool
  | [.mflr save, .adrSym dest _, .mtlr restore] => decide (save = restore ∧ save ≠ dest)
  | is => is.all fun i => !i.writesLr

def lrSafe : Prog isa → Bool
  | .block is => lrSafeBlock is
  | .seq a b | .ite _ a b => lrSafe a && lrSafe b
  | .loop b _ => lrSafe b
  | .call .. | .frame .. | .icall .. => false

theorem execBlock_symbol_lr {save dest : Reg} {name : String} {s s' : State} {t : List Leak}
    (hd : save ≠ dest)
    (h : execBlock isa [.mflr save, .adrSym dest name, .mtlr save] s = some (s', t)) :
    s'.lr = s.lr := by
  have hw : WP isa (.block [.mflr save, .adrSym dest name, .mtlr save]) s (fun u => u = s') :=
    ⟨t, s', .block h, rfl⟩
  rw [WP.block_cons_iff] at hw
  obtain ⟨s₁, e₁, hw⟩ := hw
  simp only [isa, exec_mflr] at e₁
  cases e₁
  rw [WP.block_cons_iff] at hw
  obtain ⟨s₂, e₂, hw⟩ := hw
  simp only [isa, reduceExec] at e₂
  split at e₂ <;> [skip; cases e₂]
  cases e₂
  rw [WP.block_cons_iff] at hw
  obtain ⟨s₃, e₃, hout⟩ := hw
  rw [WP.block_nil_iff] at hout
  simp only [isa, exec_mtlr] at e₃
  cases e₃
  rw [← hout]
  simp only [RegUpd.gpr_write, hd, ite_false, ite_true]

theorem execBlock_lr_safe {is : List Instr} {s s' : State} {t : List Leak}
    (h : execBlock isa is s = some (s', t)) (hc : lrSafeBlock is = true) : s'.lr = s.lr := by
  simp only [lrSafeBlock] at hc
  split at hc
  · rename_i save dest name restore
    obtain ⟨he, hd⟩ := of_decide_eq_true hc
    subst restore
    exact execBlock_symbol_lr hd h
  · exact execBlock_lr h hc

theorem lrSafeBlock_of_all {is : List Instr}
    (h : is.all (fun i => !i.writesLr) = true) : lrSafeBlock is = true := by
  simp only [lrSafeBlock]
  split
  · simp only [List.all_cons, List.all_nil, Instr.writesLr, Bool.not_true, Bool.not_false,
      Bool.and_true, Bool.and_false, Bool.false_eq_true] at h
  · exact h

theorem Exec.lr_safe {c : Prog isa} {s s' : State} {t : List Leak}
    (h : VG.Exec isa c s t s') (hc : lrSafe c = true) : s'.lr = s.lr := by
  induction h with
  | icall hi => nomatch hi
  | icallNext hi => nomatch hi
  | block e => exact execBlock_lr_safe e hc
  | seq _ _ ih₁ ih₂ =>
    simp only [lrSafe, Bool.and_eq_true] at hc
    exact (ih₂ hc.2).trans (ih₁ hc.1)
  | iteT _ _ ih =>
    simp only [lrSafe, Bool.and_eq_true] at hc
    exact ih hc.1
  | iteF _ _ ih =>
    simp only [lrSafe, Bool.and_eq_true] at hc
    exact ih hc.2
  | loopExit _ _ ih => exact ih hc
  | loopNext _ _ _ ih₁ ih₂ => exact (ih₂ hc).trans (ih₁ hc)
  | call | frame => simp only [lrSafe, Bool.false_eq_true] at hc

theorem WP.lr_safe {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa c s Q) (hc : lrSafe c = true) :
    WP isa c s fun s' => Q s' ∧ s'.lr = s.lr := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, Exec.lr_safe he hc⟩

end VG.PPC64LE
