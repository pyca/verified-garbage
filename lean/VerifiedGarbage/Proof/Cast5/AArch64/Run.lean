import VerifiedGarbage.Impl.Cast5.AArch64
import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.Syms

/-!
# CAST5 on AArch64: running blocks

* `crun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), the state a chain of `State.write`s, `State.setV`s, flag
  updates and memory updates whose registers `RegUpd` reads.
* `WP.keep`: the registers no instruction of the code writes are kept
  (`writesOnly`, checked by evaluation), with ML-KEM's `Keep`.
* `wp_countdown`: a loop on `cbnz` of a counter that its body decrements.
-/

namespace VG.Proof.Cast5.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd
open VG.Proof.MlKem.AArch64 (Keep count_loop eval_nonzero eval_zero ne_zero_iff)

/-- `s` with the memory `m`, kept folded in symbolic execution. -/
def putMem (s : State) (m : Mem) : State := { s with mem := m }

/-! ## The instructions, for `simp` -/

section
variable {s : State}

theorem exec_ldrb' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.ldrb t n off) s = some (s.write .w t ((s.mem (s.gpr n + BitVec.ofNat 64 off)).setWidth 32)) := by
  simp only [exec, addr, Nat.mod_one, ho, and_self, ite_true, Option.bind_some, State.load, h,
    Option.map_some, VG.Proof.MlKem.AArch64.read_one]

theorem exec_str_w' {t n : Reg} {off : Nat} (ho : off % 4 = 0 ∧ off < 16384)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    exec (.str .w t n off) s =
      some (putMem s (s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth 32))) :=
  exec_str_w ho h

theorem exec_str_x' {t n : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.str .x t n off) s = some (putMem s (s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t))) :=
  exec_str_x ho h

theorem exec_strb' {t n : Reg} {off : Nat} (ho : off < 4096)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.strb t n off) s =
      some (putMem s (s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth 8))) := by
  simp only [exec, addr, Nat.mod_one, ho, and_self, ite_true, Option.bind_some, State.store, h,
    State.read, Size.bits, Mem.writeW]
  rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
  rfl

theorem exec_ldrq' {t : VReg} {n : Reg} {off : Nat} (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, ho, and_self, ite_true, Option.bind_some, State.load, h, Option.map_some]

theorem exec_movz_x' {d : Reg} {imm : BitVec 16} :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true]
  exact congrArg (fun v => some (s.write .x d v)) (BitVec.shiftLeft_zero _)

theorem exec_lsl_w {d n : Reg} {sh : Nat} (h : sh < 32) :
    exec (.lsl .w d n sh) s = some (s.write .w d (s.read .w n <<< sh)) := by
  simp [exec, Size.bits, h]

theorem exec_lsl_x {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsl .x d n sh) s = some (s.write .x d (s.gpr n <<< sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_lsr_x {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.lsr .x d n sh) s = some (s.write .x d (s.gpr n >>> sh)) := by
  simp [exec, Size.bits, h, State.read]

theorem exec_addImm_x' {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.addImm .x d n imm) s = some (s.write .x d (s.gpr n + BitVec.ofNat 64 imm)) := by
  simp [exec, h, State.read]

theorem exec_subImm_x' {d n : Reg} {imm : Nat} (h : imm < 4096) :
    exec (.subImm .x d n imm) s = some (s.write .x d (s.gpr n - BitVec.ofNat 64 imm)) := by
  simp [exec, h, State.read]

theorem exec_tst_w {n m : Reg} :
    exec (.tst .w n m) s = some { s with
      nf := (s.read .w n &&& s.read .w m).msb
      zf := decide ((s.read .w n &&& s.read .w m) = 0)
      c := false
      vf := false } := rfl

theorem exec_cselc {sz : Size} {d n m : Reg} {cond : CondCode} :
    exec (.cselc sz d n m cond) s =
      some (s.write sz d (if cond.holds s then s.read sz n else s.read sz m)) := rfl

theorem exec_umov_w {d : Reg} {n : VReg} {i : Nat} (h : i < 4) :
    exec (.umov .w d n i) s = some (s.write .w d (vword (s.v n) i)) := by
  simp only [exec, Size.bits, show i * 32 < 128 by omega, ite_true]
  rfl

theorem exec_sub {sz : Size} {d n m : Reg} :
    exec (.sub sz d n m) s = some (s.write sz d (s.read sz n - s.read sz m)) := rfl

theorem exec_vop {op : VOp} : exec (.vop op) s = (op.eval s).map fun (d, x) => s.setV d x := rfl

end

/-! ## The state after a step, for `simp` -/

section
variable (s : State)

theorem gpr_mem (m : Mem) : (putMem s m).gpr = s.gpr := rfl
theorem mem_mem (m : Mem) : (putMem s m).mem = m := rfl
theorem rd_mem (m : Mem) : (putMem s m).rd = s.rd := rfl
theorem wr_mem (m : Mem) : (putMem s m).wr = s.wr := rfl
theorem v_mem (m : Mem) : (putMem s m).v = s.v := rfl
theorem sp_mem (m : Mem) : (putMem s m).sp = s.sp := rfl
theorem syms_mem (m : Mem) : (putMem s m).syms = s.syms := rfl
theorem zf_mem (m : Mem) : (putMem s m).zf = s.zf := rfl

theorem syms_write (sz : Size) (r : Reg) (x : BitVec sz.bits) : (s.write sz r x).syms = s.syms := rfl
theorem syms_setV (r : VReg) (x : BitVec 128) : (s.setV r x).syms = s.syms := rfl

theorem setWidth_32_64_32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq x)

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
        exec_ldr_w, exec_str_w', exec_str_x', exec_ldrb', exec_strb', exec_ldrq', exec_movz_x', exec_movz_w,
        exec_lsl_w, exec_lsl_x, exec_lsr_w, exec_lsr_x, exec_ror_w, exec_addImm_x', exec_subImm_x',
        exec_tst_w, exec_cselc, exec_umov_w, exec_vop, exec_add, exec_sub, exec_logic, exec_rev32, exec_adrSym,
        VOp.eval, Option.map_some,
        State.read, Size.bits, gpr_write, mem_write, rd_write, wr_write, sp_write, v_write,
        gpr_setV, mem_setV, rd_setV, wr_setV, sp_setV, v_setV_self, gpr_mem, mem_mem, rd_mem, wr_mem,
        v_mem, sp_mem, syms_write, syms_setV, syms_mem, zf_write, zf_mem, setWidth_32_64_32, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left',
        ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceEqDiff, Bool.and_self, Bool.and_true, decide_true,
        and_self, eq_self_iff_true, true_and, and_true, List.cons_append, List.nil_append, $ls,*]))

/-! ## What a block keeps -/

/-- Whether every instruction of `c` writes, if any register, one of `rs`. -/
def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => match dstOf i with
    | none => true
    | some d => rs.contains d

/-- A register that no instruction writes keeps its value (code without calls). -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : c.noCalls = true := by first | rfl | decide)
    (hv : c.allInstrs keepsV = true := by decide +kernel) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, (Exec.rdwr he).2.2, Exec.preservedV he hv⟩⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := hc i hi
  intro e
  rw [e] at this
  simp only [List.contains_iff_mem] at this
  exact hr (by simpa using this)

/-! ## Loops -/

/-- A do-while loop on `cbnz cnt` whose body decrements `cnt`, from `N > 0`:
it runs `N` times. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 64) (hN0 : 0 < N)
    (Inv : Nat → State → Prop)
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 64 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1)
    {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 64 N) :
    WP isa (.loop body (.nonzero .x cnt)) s (Inv N) := by
  refine WP.mono (count_loop (cr := cnt) hN0 (fun k s => Inv k s ∧ s.gpr cnt = BitVec.ofNat 64 (N - k))
    (fun k hk s ⟨hI, hc⟩ => WP.mono (hbody k hk s hI hc) fun s' ⟨hI', hc'⟩ => ⟨⟨hI', ?_⟩, ?_⟩)
    ⟨h0, by rw [hc, Nat.sub_zero]⟩) fun _ h => h.1
  · rw [hc', hc]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [hc', hc, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

end VG.Proof.Cast5.AArch64
