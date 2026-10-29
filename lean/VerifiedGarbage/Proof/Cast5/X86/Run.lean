module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Impl.Cast5.X86
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.X86.RegUpd
public import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Framework.X86.Syms
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.SseTaint
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.SseTaint

/-!
# CAST5 on 32-bit x86: running blocks

* The instructions the code uses, as rewrites for `simp` (`exec_ld`, …), at
  the addresses `addr b d` the model computes (`[b + d]`).
* `crun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), the state a chain of `State.setReg`s, flag updates and
  memory updates whose registers `RegUpd` reads.
* `Keep`: what code that writes only the registers `rs` keeps.
-/

@[expose] public section

namespace VG.Proof.Cast5.X86

open VG VG.X86 VG.X86.RegUpd

/-- `s` with the memory `m`, kept folded in symbolic execution. -/
abbrev putMem (s : State) (m : Mem) : State := { s with mem := m }

section
variable {s : State}

theorem ea_at (b : Reg) (d : Nat) : s.ea (Impl.Cast5.X86.at_ b d) = addr (s.gpr b) d := rfl

theorem exec_ld {d b : Reg} {o : Nat} (h : InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 4) :
    exec (.mov d (.mem (Impl.Cast5.X86.at_ b o))) s = some (s.setReg d (s.mem.readW (addr (s.gpr b) o) 32)) := by
  simp only [exec, readSrc, State.load32, ea_at, h, ite_true, Option.map_some]

theorem exec_st {b r : Reg} {o : Nat} (h : InRegions s.wr (addr (s.gpr b) o) 4) :
    exec (.store (Impl.Cast5.X86.at_ b o) r) s = some (putMem s (s.mem.writeW (addr (s.gpr b) o) (s.gpr r))) := by
  simp only [exec, State.store32, ea_at, h, ite_true]

theorem exec_ldb {d b : Reg} {o : Nat} (h : InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 1) :
    exec (.movzx8 d (Impl.Cast5.X86.at_ b o)) s = some (s.setReg d ((s.mem (addr (s.gpr b) o)).setWidth 32)) := by
  simp only [exec, State.load8, ea_at, h, ite_true, Option.map_some]

theorem exec_stb {b : Reg} {r : Reg8} {o : Nat} (h : InRegions s.wr (addr (s.gpr b) o) 1) :
    exec (.store8 (Impl.Cast5.X86.at_ b o) r) s =
      some (putMem s (s.mem.writeW (addr (s.gpr b) o) ((s.gpr r.reg).setWidth 8))) := by
  simp only [exec, State.store8, ea_at, h, ite_true]

theorem exec_ld128 {d : XReg} {b : Reg} {o : Nat} (h : InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 16) :
    exec (.movdquLoad d (Impl.Cast5.X86.at_ b o)) s = some (s.setXmm d (s.mem.readW (addr (s.gpr b) o) 128)) := by
  simp only [exec, State.load128, ea_at, h, ite_true, Option.map_some]

theorem exec_st128 {b : Reg} {r : XReg} {o : Nat} (h : InRegions s.wr (addr (s.gpr b) o) 16) :
    exec (.movdquStore (Impl.Cast5.X86.at_ b o) r) s =
      some (putMem s (s.mem.writeW (addr (s.gpr b) o) (s.xmm r))) := by
  simp only [exec, State.store128, ea_at, h, ite_true]

theorem exec_aluM {op : AluOp} {d b : Reg} {o : Nat} (h : InRegions (s.rd ++ s.wr) (addr (s.gpr b) o) 4) :
    exec (.alu op d (.mem (Impl.Cast5.X86.at_ b o))) s =
      execAlu op d (.imm (s.mem.readW (addr (s.gpr b) o) 32)) s := by
  simp only [exec, execAlu, readSrc, State.load32, ea_at, h, ite_true, Option.bind_some]

end

/-! ## The state after a step -/

section
variable (s : State)

theorem gpr_mem (m : Mem) (r : Reg) : (putMem s m).gpr r = s.gpr r := rfl
theorem mem_mem (m : Mem) : (putMem s m).mem = m := rfl
theorem rd_mem (m : Mem) : (putMem s m).rd = s.rd := rfl
theorem wr_mem (m : Mem) : (putMem s m).wr = s.wr := rfl
theorem xmm_mem (m : Mem) (x : XReg) : (putMem s m).xmm x = s.xmm x := rfl
theorem zf_mem (m : Mem) : (putMem s m).zf = s.zf := rfl
theorem syms_mem (m : Mem) : (putMem s m).syms = s.syms := rfl
theorem zf_setFlags' (a b c d : Option Bool) : (s.setFlags a b c d).zf = c := rfl
theorem xmm_setFlags' (a b c d : Option Bool) (x : XReg) : (s.setFlags a b c d).xmm x = s.xmm x := rfl
theorem xmm_arithFlags' (v : BitVec 32) (c o : Bool) (x : XReg) : (arithFlags s v c o).xmm x = s.xmm x := rfl
theorem xmm_setReg' (r : Reg) (v : BitVec 32) (x : XReg) : (s.setReg r v).xmm x = s.xmm x := rfl
theorem syms_setReg' (r : Reg) (v : BitVec 32) : (s.setReg r v).syms = s.syms := rfl
theorem syms_setXmm' (r : XReg) (v : BitVec 128) : (s.setXmm r v).syms = s.syms := rfl
theorem syms_setFlags' (a b c d : Option Bool) : (s.setFlags a b c d).syms = s.syms := rfl
theorem syms_arithFlags' (v : BitVec 32) (c o : Bool) : (arithFlags s v c o).syms = s.syms := rfl
theorem zf_setXmm' (r : XReg) (v : BitVec 128) : (s.setXmm r v).zf = s.zf := rfl

end

/-- `crun`: symbolic execution of a block by `simp` (see the module doc),
with extra lemmas (the block's accesses, …). -/
tactic_template "crun" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp only [runBlock_cons, runStep_some, runBlock_nil, Impl.Cast5.X86.imm,
                         exec, readSrc, ea_at, State.load32, State.store32, State.load8, State.store8, State.load128,
                         State.store128, execAlu, execShift, XOp.exec, Option.map_some, Option.bind_some,
                         gpr_setReg, mem_setReg, rd_setReg, wr_setReg, zf_setReg, xmm_setReg', syms_setReg',
                         gpr_setFlags, mem_setFlags, rd_setFlags, wr_setFlags, zf_setFlags', xmm_setFlags', syms_setFlags',
                         gpr_arithFlags, mem_arithFlags, rd_arithFlags, wr_arithFlags, zf_arithFlags, xmm_arithFlags',
                         syms_arithFlags',
                         gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, zf_setXmm', syms_setXmm', xmm_setXmm_self,
                         xmm_setXmm_of_ne,
                         gpr_mem, mem_mem, rd_mem, wr_mem, xmm_mem, zf_mem, syms_mem,
                         Option.some.injEq, exists_eq_left',
                         ite_true, ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceMul,
                         Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff, and_self, eq_self_iff_true,
                         not_false_eq_true, true_and, and_true, List.cons_append, List.nil_append, $ls,*]))
/-- `crun` with no extra lemmas. -/
macro "crun" : tactic => `(tactic| crun [])

/-! ## What code keeps -/

/-- The registers but `rs` and the regions are kept. -/
structure Keep (rs : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ rs → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.trans {rs : List Reg} {s t u : State} (h : Keep rs s t) (h' : Keep rs t u) : Keep rs s u :=
  ⟨fun r hr => (h'.gpr r hr).trans (h.gpr r hr), h'.rd.trans h.rd, h'.wr.trans h.wr⟩

theorem Keep.mono {rs rs' : List Reg} {s t : State} (h : Keep rs s t) (hs : ∀ r ∈ rs, r ∈ rs') :
    Keep rs' s t :=
  ⟨fun r hr => h.gpr r fun e => hr (hs r e), h.rd, h.wr⟩

theorem Keep.refl (rs : List Reg) (s : State) : Keep rs s s := ⟨fun _ _ => rfl, rfl, rfl⟩

/-- Whether no instruction of `c` writes a register outside `rs`. -/
noncomputable def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => [Reg.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi].all fun r =>
    rs.contains r || !Taint.clobbers i r

/-- A register that no instruction writes keeps its value. -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) : WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he, (Exec.rdwr he).1, (Exec.rdwr he).2⟩⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have h1 := List.all_eq_true.mp (hc i hi) r (by cases r <;> simp)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · exact absurd (List.contains_iff_mem.mp h1) hr
  · exact h1

theorem bswap_eq (x : BitVec 32) : bswap x = byteRev32 x := rfl

/-! ## Loops -/

theorem ofNat_pred {k : Nat} (h0 : 0 < k) (h : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) :=
  Wp.sub_ofNat (a := k) (b := 1) (by omega)

/-- A loop whose body counts `ctr` (a register, or a slot in memory) down by
one, setting ZF as `sub` does, from `N`: the body runs `N` times. -/
theorem wp_countdownF {body : Prog isa} (ctr : State → BitVec 32) {N : Nat} (hN : N < 2 ^ 32) (hN0 : 0 < N)
    (Inv : Nat → State → Prop) {Q : State → Prop}
    (hbody : ∀ i < N, ∀ s, Inv i s → ctr s = BitVec.ofNat 32 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ ctr s' = ctr s - 1 ∧ s'.zf = some (ctr s - 1 == 0))
    (hQ : ∀ s, Inv N s → Q s) {s : State} (h0 : Inv 0 s) (hc : ctr s = BitVec.ofNat 32 N) :
    WP isa (.loop body .ne) s Q := by
  refine WP.loop (M := isa) (fun n s => ∃ i, n = N - i ∧ i < N ∧ Inv i s ∧
    ctr s = BitVec.ofNat 32 (N - i)) ?_ N s ⟨0, rfl, hN0, h0, by rw [Nat.sub_zero]; exact hc⟩
  rintro n s ⟨i, rfl, hi, hI, hcnt⟩
  refine WP.mono (hbody i hi s hI hcnt) fun s' ⟨hI', hc', hz'⟩ => ?_
  rw [hcnt, ofNat_pred (by omega) (by omega)] at hc' hz'
  have hev : isa.eval .ne s' = some (!decide (N - i - 1 = 0)) := by
    simp only [eval, hz', Wp.ofNat_beq_zero (show N - i - 1 < 2 ^ 32 by omega), Option.map_some]
  by_cases he : i + 1 = N
  · subst he
    exact .inl ⟨by rw [hev]; simp, hQ s' hI'⟩
  · exact .inr ⟨by rw [hev]; simp; omega, N - (i + 1), by omega, i + 1, rfl, by omega, hI',
      by rw [hc']; congr 1⟩

/-- `wp_countdownF` for a register. -/
theorem wp_countdown {body : Prog isa} {cnt : Reg} {N : Nat} (hN : N < 2 ^ 32) (hN0 : 0 < N)
    (Inv : Nat → State → Prop) {Q : State → Prop}
    (hbody : ∀ i < N, ∀ s, Inv i s → s.gpr cnt = BitVec.ofNat 32 (N - i) →
      WP isa body s fun s' => Inv (i + 1) s' ∧ s'.gpr cnt = s.gpr cnt - 1 ∧
        s'.zf = some (s.gpr cnt - 1 == 0))
    (hQ : ∀ s, Inv N s → Q s) {s : State} (h0 : Inv 0 s) (hc : s.gpr cnt = BitVec.ofNat 32 N) :
    WP isa (.loop body .ne) s Q :=
  wp_countdownF (fun s => s.gpr cnt) hN hN0 Inv hbody hQ h0 hc

/-! ## Addresses -/

theorem toNat_setWidth (a : BitVec 32) : (a.setWidth 64).toNat = a.toNat := by
  simp only [BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- `[c + off]` within a buffer that does not wrap. -/
theorem addr_off {c : BitVec 32} {n : Nat} (h : c.toNat + n ≤ 2 ^ 32) :
    ∀ off, off < n → addr c off = c.setWidth 64 + BitVec.ofNat 64 off :=
  fun _ ho => addr_eq (by omega)

end VG.Proof.Cast5.X86
