module

public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.X86.Exec
public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.Framework.X86.Inline
public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Impl.Mont.X86
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `R2Words` on x86 (32-bit): running blocks symbolically

A block is run with `xrun`, a `simp only` that steps it one instruction at a
time (`runBlock_cons`, `runStep_some`) and keeps the state a chain of
`State.setReg`, `State.setFlags` and memory updates, whose projections the
lemmas here evaluate, as ML-DSA's `xrun` for the same model. A block lemma
gives `xrun` the accesses it makes: a pointer register as its value
(`ptr_eq`), an address in the working space as the bytes at an offset of its
base (`addr_off`), and the permission of each access (`ws_read`,
`ws_write`). `WP.keeps` proves `Keeps` of code none of whose instructions
writes another register.
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.R2Words

open VG VG.X86 VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-! ## Projections of the state updates -/

section
variable (s : State) (d r : Reg) (v : BitVec 32) (cf o zf sf : Option Bool)

theorem setReg_gpr : (s.setReg d v).gpr r = if r = d then v else s.gpr r := rfl
theorem setReg_mem : (s.setReg d v).mem = s.mem := rfl
theorem setReg_rd : (s.setReg d v).rd = s.rd := rfl
theorem setReg_wr : (s.setReg d v).wr = s.wr := rfl
theorem setReg_cf : (s.setReg d v).cf = s.cf := rfl
theorem setReg_zf : (s.setReg d v).zf = s.zf := rfl
theorem setFlags_gpr : (s.setFlags cf o zf sf).gpr = s.gpr := rfl
theorem setFlags_mem : (s.setFlags cf o zf sf).mem = s.mem := rfl
theorem setFlags_rd : (s.setFlags cf o zf sf).rd = s.rd := rfl
theorem setFlags_wr : (s.setFlags cf o zf sf).wr = s.wr := rfl
theorem setFlags_cf : (s.setFlags cf o zf sf).cf = cf := rfl
theorem setFlags_zf : (s.setFlags cf o zf sf).zf = zf := rfl
theorem arithFlags_eq (x : BitVec 32) (c o : Bool) :
    arithFlags s x c o = s.setFlags (some c) (some o) (some (x == 0)) (some x.msb) := rfl
theorem ea_at (b : Reg) (n : Nat) : s.ea (at_ b n) = addr (s.gpr b) n := rfl

end

/-! ## Running a block -/

/-- Steps a block from a state whose accesses the hypotheses `ls` permit. -/
syntax "xrun" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| xrun) => `(tactic| xrun [])
  | `(tactic| xrun [$ls,*]) => `(tactic| plain_simp_names (
                       apply WP.of_runBlock
                       set_option linter.unusedSimpArgs false in
                       simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
                         execAlu, execShift, arithFlags_eq, ea_at, State.load32, State.store32,
                         setReg_gpr, setReg_mem, setReg_rd, setReg_wr, setReg_cf, setReg_zf,
                         setFlags_gpr, setFlags_mem, setFlags_rd, setFlags_wr, setFlags_cf, setFlags_zf,
                         Option.bind_some, Option.map_some, Option.map, Option.some.injEq, exists_eq_left', ite_true,
                         ite_false, reduceCtorEq, ↓reduceIte, Nat.reduceLeDiff, Nat.reduceEqDiff, and_self, BitVec.sub_self,
                         true_and, and_true, $ls,*]))

/-! ## What a block keeps -/

/-- Every register. -/
def allRegs : List Reg := [.eax, .ecx, .edx, .ebx, .esp, .ebp, .esi, .edi]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by cases r <;> decide

/-- Whether no instruction of `c` writes a register outside `rs`. -/
noncomputable def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => allRegs.all fun r => rs.contains r || !Taint.clobbers i r

/-- A register that no instruction writes keeps its value. -/
theorem WP.keeps {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) : WP isa c s fun s' => Q s' ∧ Keeps rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, fun r hr => Exec.gpr (fun i hi => ?_) he, (Exec.rdwr he).1, (Exec.rdwr he).2⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  have := List.all_eq_true.mp (hc i hi) r (mem_allRegs r)
  simp only [Bool.or_eq_true, List.contains_iff_mem, hr, false_or, Bool.not_eq_true'] at this
  exact this

/-! ## Pointers into the working space -/

/-- A pointer as its value. -/
theorem ptr_eq {s : State} {W : Addr} {r : Reg} {x : Nat} (hp : PtrAt s W r x) :
    s.gpr r = BitVec.ofNat 32 (W.toNat + x) :=
  BitVec.eq_of_toNat_eq (by rw [hp, BitVec.toNat_ofNat])

/-- `W + x + d`, for a working space below `2³²`, as an address. -/
theorem addr_off (W : Addr) {x d : Nat} (h : W.toNat + x + d < 2 ^ 32) :
    addr (BitVec.ofNat 32 (W.toNat + x)) d = off W (x + d) := by
  have := W.isLt
  rw [addr_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [h])]; omega_using [h])]
  apply BitVec.eq_of_toNat_eq
  simp only [off, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  repeat rw [Nat.mod_eq_of_lt (by omega_arith)]
  omega_using []

end VG.Proof.Bignum.X86.R2Words
