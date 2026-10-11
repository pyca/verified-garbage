import VerifiedGarbage.Impl.Cast5.Arm
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Offset

/-!
# CAST5 on ARMv7: running blocks

* The instructions the code uses, as rewrites for `simp` (`exec_dpI`, …):
  immediates below 256 are encodable (`encodable_lt`).
* `crun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), the state a chain of `State.setReg`s, flag updates and
  memory updates whose registers `RegUpd` reads.
* `Keep`: what a block that writes only the registers `rs` keeps.
-/

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd

/-- An immediate below 256 is encodable (no rotation). -/
theorem encodable_lt {v : BitVec 32} (h : v.toNat < 256) : encodable v = true := by
  unfold encodable
  rw [List.any_eq_true]
  exact ⟨0, by decide, by
    have hz : v.rotateLeft (2 * 0) = v := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [hi]
    rw [hz]; exact decide_eq_true h⟩

theorem toNat_ofNat_lt {j : Nat} (h : j < 256) : (BitVec.ofNat 32 j).toNat < 256 := by
  rw [BitVec.toNat_ofNat]; omega

/-- `s` with the memory `m`, kept folded in symbolic execution. -/
abbrev putMem (s : State) (m : Mem) : State := { s with mem := m }

/-- `s` with the flags of `x - y`, kept folded. -/
abbrev putSub (s : State) (x y : BitVec 32) : State := subFlags s x y

section
variable {s : State}

/-- The value a data-processing instruction computes. -/
def dpv : DpOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add, x, y => x + y | .sub, x, y => x - y | .and, x, y => x &&& y | .orr, x, y => x ||| y
  | .eor, x, y => x ^^^ y

/-- The value of a shifted register. -/
def shv : Shift → BitVec 32 → Nat → BitVec 32
  | .lsl, x, k => x <<< k | .lsr, x, k => x >>> k | .ror, x, k => x.rotateRight k

theorem exec_dpI {op : DpOp} {d n : Reg} {v : BitVec 32} (h : v.toNat < 256) :
    exec (.dp op d n (.imm v)) s = some (s.setReg d (dpv op (s.gpr n) v)) := by
  cases op <;> simp only [exec, Op2.eval, encodable_lt h, ite_true, Option.map_some, dpv]

theorem exec_dpR {op : DpOp} {d n m : Reg} :
    exec (.dp op d n (.reg m)) s = some (s.setReg d (dpv op (s.gpr n) (s.gpr m))) := by
  cases op <;> rfl

theorem exec_dpS {op : DpOp} {d n m : Reg} {sh : Shift} {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.dp op d n (.shifted m sh k)) s = some (s.setReg d (dpv op (s.gpr n) (shv sh (s.gpr m) k))) := by
  cases op <;> cases sh <;> simp only [exec, Op2.eval, h, and_self, ite_true, Option.map_some, dpv, shv]

theorem exec_movI {d : Reg} {v : BitVec 32} (h : v.toNat < 256) :
    exec (.mov d (.imm v)) s = some (s.setReg d v) := by
  simp only [exec, Op2.eval, encodable_lt h, ite_true, Option.map_some]

theorem exec_movR {d m : Reg} : exec (.mov d (.reg m)) s = some (s.setReg d (s.gpr m)) := rfl

theorem exec_movS {d m : Reg} {sh : Shift} {k : Nat} (h : 1 ≤ k ∧ k ≤ 31) :
    exec (.mov d (.shifted m sh k)) s = some (s.setReg d (shv sh (s.gpr m) k)) := by
  cases sh <;> simp only [exec, Op2.eval, h, and_self, ite_true, Option.map_some, shv]

theorem exec_movw {d : Reg} {imm : BitVec 16} :
    exec (.movw d imm) s = some (s.setReg d (imm.setWidth 32)) := rfl

theorem exec_movt {d : Reg} {imm : BitVec 16} :
    exec (.movt d imm) s = some (s.setReg d (imm ++ (s.gpr d).extractLsb' 0 16 : BitVec 32)) := rfl

theorem exec_rev {d m : Reg} : exec (.rev d m) s = some (s.setReg d (rev (s.gpr m))) := rfl

theorem exec_cmpI {n : Reg} {v : BitVec 32} (h : v.toNat < 256) :
    exec (.cmp n (.imm v)) s = some (putSub s (s.gpr n) v) := by
  simp only [exec, Op2.eval, encodable_lt h, ite_true, Option.map_some, putSub]

theorem exec_subsI {d n : Reg} {v : BitVec 32} (h : v.toNat < 256) :
    exec (.subs d n (.imm v)) s = some ((putSub s (s.gpr n) v).setReg d (s.gpr n - v)) := by
  simp only [exec, Op2.eval, encodable_lt h, ite_true, Option.map_some, putSub]

theorem exec_ldr' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4) :
    exec (.ldr t n off) s =
      some (s.setReg t (s.mem.readW (State.addr (s.gpr n + BitVec.ofNat 32 off)) 32)) := exec_ldr ho h

theorem exec_str' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 4) :
    exec (.str t n off) s =
      some (putMem s (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) (s.gpr t))) := exec_str ho h

theorem exec_ldrb' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.gpr n + BitVec.ofNat 32 off)) 1) :
    exec (.ldrb t n off) s =
      some (s.setReg t ((s.mem (State.addr (s.gpr n + BitVec.ofNat 32 off))).setWidth 32)) := by
  simp only [exec, ho, ite_true, State.load8, h, Option.map_some]

theorem exec_strb' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (State.addr (s.gpr n + BitVec.ofNat 32 off)) 1) :
    exec (.strb t n off) s =
      some (putMem s (s.mem.writeW (State.addr (s.gpr n + BitVec.ofNat 32 off)) ((s.gpr t).setWidth 8))) := by
  simp only [exec, ho, ite_true, State.store8, h, putMem]

theorem exec_ldrSp' {t : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 off)) 4) :
    exec (.ldrSp t off) s = some (s.setReg t (s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 off)) 32)) := by
  simp only [exec, ho, ite_true, State.load32, h, Option.map_some]

end

/-! ## The state after a step -/

section
variable (s : State)

theorem gpr_mem (m : Mem) (r : Reg) : (putMem s m).gpr r = s.gpr r := rfl
theorem mem_mem (m : Mem) : (putMem s m).mem = m := rfl
theorem rd_mem (m : Mem) : (putMem s m).rd = s.rd := rfl
theorem wr_mem (m : Mem) : (putMem s m).wr = s.wr := rfl
theorem sp_mem (m : Mem) : (putMem s m).sp = s.sp := rfl
theorem z_mem (m : Mem) : (putMem s m).z = s.z := rfl

theorem gpr_sub (x y : BitVec 32) (r : Reg) : (putSub s x y).gpr r = s.gpr r := rfl
theorem mem_sub (x y : BitVec 32) : (putSub s x y).mem = s.mem := rfl
theorem rd_sub (x y : BitVec 32) : (putSub s x y).rd = s.rd := rfl
theorem wr_sub (x y : BitVec 32) : (putSub s x y).wr = s.wr := rfl
theorem sp_sub (x y : BitVec 32) : (putSub s x y).sp = s.sp := rfl
theorem z_sub (x y : BitVec 32) : (putSub s x y).z = (x - y == 0) := rfl

end

/-- `crun`: symbolic execution of a block by `simp` (see the module doc),
with extra lemmas (the block's accesses, …). -/
syntax "crun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| crun) => `(tactic| crun [])
  | `(tactic| crun [$ls,*]) => `(tactic| (
      apply WP.of_runBlock
      set_option linter.unusedSimpArgs false in
      simp only [runBlock_cons, runStep_some, runBlock_nil,
        exec_dpI, exec_dpR, exec_dpS, exec_movI, exec_movR, exec_movS, exec_movw, exec_movt, exec_rev, dpv, shv,
        exec_cmpI, exec_subsI, exec_ldr', exec_str', exec_ldrb', exec_strb', exec_ldrSp',
        gpr_setReg, mem_setReg, rd_setReg, wr_setReg, sp_setReg, z_setReg,
        gpr_mem, mem_mem, rd_mem, wr_mem, sp_mem, z_mem, gpr_sub, mem_sub, rd_sub, wr_sub, sp_sub, z_sub,
        BitVec.reduceToNat, Option.some.injEq, exists_eq_left',
        ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, and_self, eq_self_iff_true,
        true_and, and_true, List.cons_append, List.nil_append, $ls,*]))

/-! ## Branches -/

theorem wp_ite_eq {th el : Prog isa} {s : State} {Q : State → Prop} (ht : s.z = true → WP isa th s Q)
    (he : s.z = false → WP isa el s Q) : WP isa (.ite .eq th el) s Q := WP.ite s.z rfl ht he

theorem wp_ite_ne {th el : Prog isa} {s : State} {Q : State → Prop} (ht : s.z = false → WP isa th s Q)
    (he : s.z = true → WP isa el s Q) : WP isa (.ite .ne th el) s Q :=
  WP.ite (!s.z) rfl (fun h => ht (by simpa using h)) (fun h => he (by simpa using h))

/-! ## What a block keeps -/

/-- `∀ r ∉ rs, (s with registers written).gpr r = s.gpr r`. -/
macro "keep_regs" : tactic => `(tactic| (
  intro r hr
  simp only [gpr_setReg, gpr_sub, gpr_mem]
  repeat' split
  all_goals first | rfl | (subst_vars; exact absurd hr (by decide))))

/-- The registers but `rs`, the regions and the stack pointer are kept. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Keep.trans {rs : List Reg} {s t u : State} (h : Keep rs s t) (h' : Keep rs t u) : Keep rs s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.rd.trans h.rd, h'.wr.trans h.wr, h'.sp.trans h.sp⟩

theorem Keep.mono {rs rs' : List Reg} {s t : State} (h : Keep rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s t :=
  ⟨fun r hr => h.gpr r fun e => hr (hs r e), h.rd, h.wr, h.sp⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Whether every instruction of `c` writes, if any register, one of `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => match dstOf i with
    | none => true
    | some d => rs.contains d

/-- A register that no instruction writes keeps its value (code without calls). -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : c.noCalls = true := by first | rfl | decide) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, (Exec.rdwr he).2.2⟩⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := hc i hi
  intro e
  rw [e] at this
  simp only [List.contains_iff_mem] at this
  exact hr (by simpa using this)

/-! ## Addresses in the working space -/

/-- The 32-bit address `c + off` within a buffer that does not wrap. -/
theorem addr_off {c : BitVec 32} {n : Nat} (h : c.toNat + n ≤ 2 ^ 32) :
    ∀ off, off < n → State.addr (c + BitVec.ofNat 32 off) = State.addr c + BitVec.ofNat 64 off :=
  fun _ ho => addr_add (by omega)

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

end VG.Proof.Cast5.Arm
