module

public import VerifiedGarbage.Proof.Framework.Arm.Spill
public import VerifiedGarbage.Proof.Framework.Arm.StackScratchConsts
import VerifiedGarbage.Proof.Cast5.Memory
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Proof.Framework.Arm.RegUpd
public import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Framework.Bswap
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Cast5.Rotate
public import VerifiedGarbage.Proof.Cast5.Round
public import VerifiedGarbage.Proof.Framework.ReadHalves
public import VerifiedGarbage.Proof.Scan.Arm
public import VerifiedGarbage.Proof.Cast5.Table
public import VerifiedGarbage.Impl.Cast5.Arm
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.Arm.Inline
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! ### `Cast5.Arm.Round`, which this module and modules that import it used -/

section

/-! ### `Cast5.Arm.Run`, which this module and modules that import it used -/

section

/-!
# CAST5 on ARMv7: running blocks

* The instructions the code uses, as rewrites for `simp` (`exec_dpI`, …):
  immediates below 256 are encodable (`encodable_lt`).
* `crun`: a block run by `simp`, one instruction at a time (`runBlock_cons`,
  `runStep_some`), the state a chain of `State.setReg`s, flag updates and
  memory updates whose registers `RegUpd` reads.
* `Keep`: what a block that writes only the registers `rs` keeps.
-/

@[expose] public section

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
  rw [BitVec.toNat_ofNat]; omega_using [h]

/-- `s` with the memory `m`, kept folded in symbolic execution. -/
abbrev putMem (s : State) (m : Mem) : State := { s with mem := m }

/-- `s` with the flags of `x - y`, kept folded. -/
abbrev putSub (s : State) (x y : BitVec 32) : State := subFlags s x y

section
variable {s : State}

/-- The value a data-processing instruction computes. -/
def dpv : DpOp → BitVec 32 → BitVec 32 → BitVec 32
  | .add, x, y => x + y | .sub, x, y => x - y | .and, x, y => x &&& y | .orr, x, y => x ||| y
  | .eor, x, y => x ^^^ y | .bic, x, y => x &&& ~~~y

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
tactic_template "crun" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
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
/-- `crun` with no extra lemmas. -/
tactic_template "crun" : tactic => `(tactic| crun [])

/-! ## Branches -/

theorem wp_ite_eq {th el : Prog isa} {s : State} {Q : State → Prop} (ht : s.z = true → WP isa th s Q)
    (he : s.z = false → WP isa el s Q) : WP isa (.ite .eq th el) s Q := WP.ite s.z rfl ht he

/-! ## What a block keeps -/

/-- `∀ r ∉ rs, (s with registers written).gpr r = s.gpr r`. -/
tactic_template "keep_regs" : tactic => `(tactic| (
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
noncomputable def writesOnly (rs : List Reg) (c : Prog isa) : Bool :=
  c.allInstrs fun i => (dsts i).all rs.contains

/-- A register that no instruction writes keeps its value (code without calls). -/
theorem WP.keep {c : Prog isa} {s : State} {Q : State → Prop} (rs : List Reg) (h : WP isa c s Q)
    (hc : writesOnly rs c = true) (hn : c.noCalls = true := by first | rfl | decide) :
    WP isa c s fun s' => Q s' ∧ Keep rs s s' := by
  obtain ⟨t, s', he, hq⟩ := h
  refine ⟨t, s', he, hq, ⟨fun r hr => Exec.gpr (fun i hi => ?_) he (.inl hn), (Exec.rdwr he).1,
    (Exec.rdwr he).2.1, (Exec.rdwr he).2.2⟩⟩
  unfold writesOnly at hc
  rw [Code.allInstrs_eq, List.all_eq_true] at hc
  exact clobbers_eq_false_of_contains (hc i hi) hr

/-! ## Addresses in the working space -/

/-- The 32-bit address `c + off` within a buffer that does not wrap. -/
theorem addr_off {c : BitVec 32} {n : Nat} (h : c.toNat + n ≤ 2 ^ 32) :
    ∀ off, off < n → State.addr (c + BitVec.ofNat 32 off) = State.addr c + BitVec.ofNat 64 off :=
  fun _ ho => addr_add (by omega_using [h, ho])

theorem toNat_addr (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega_using [])

end VG.Proof.Cast5.Arm

end

end

/-! ### `Cast5.Arm.Scan`, which this module and modules that import it used -/

section

/-!
# CAST5 on ARMv7: the scan of a table

`scan sym o` makes four lookups in the static `sym`, one after the other
(`look_ok`): each reads its word of the 256 entries as 32 rows of eight
(`Proof/Scan/Arm.lean`), keeps the row of its index's high five bits, and
picks among that row's words by the index's low three bits (`pick_ok`). It
leaves in `r8 + k` word `k` of the entry whose number is in `r4 + k`
(`scan_ok`); `r2`, `r3` and `lr` are saved in the scan's ten words at `o` in
the working space at `r12`, which hold its indices, counts and values
meanwhile, and restored.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Scan.Arm (mlaCol rows colReg)

/-- Word `k` of entry `e` of the table at the 32-bit address `T`. -/
def tw (m : Mem) (T : BitVec 32) (e k : Nat) : BitVec 32 :=
  m.readW (State.addr (T + BitVec.ofNat 32 (16 * e + 4 * k))) 32

/-- Word `k` of entry `e` of a table held at `T`, which does not wrap. -/
theorem tw_table {m : Mem} {T : BitVec 32} {a b c d : Byte → Spec.Cast5.Word} (hT : T.toNat + 4096 ≤ 2 ^ 32)
    (h : Held m (State.addr T) (Impl.Cast5.table a b c d)) {e k : Nat} (he : e < 256) (hk : k < 4) :
    tw m T e k = tableEnt a b c d e k := by
  rw [← ent_table h he hk, tw, ent, addr_add (by omega_arith)]

/-- Memory holding a table, later: its words are kept by writes apart from it. -/
theorem held_frame {rs : List Region} {m m' : Mem} {T : Addr} {W : List (BitVec 64)} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨T, 8 * W.length⟩ r) (hl : 8 * W.length < 2 ^ 64) (h : Held m T W) :
    Held m' T W := fun i hi => by
  rw [hf.readW (Offset.contains_base _ (by omega_arith) (by omega_arith)) hd (by decide)]
  exact h i hi

/-! ## The indices, a byte each -/

/-- The four indices `ix`, a byte each, the first the lowest. -/
def packN (ix : Nat → Nat) : Nat := ix 0 + 256 * ix 1 + 65536 * ix 2 + 16777216 * ix 3

theorem packN_lt {ix : Nat → Nat} (h : ∀ k < 4, ix k < 256) : packN ix < 2 ^ 32 := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  unfold packN
  omega_arith

theorem packN_byte {ix : Nat → Nat} (h : ∀ k < 4, ix k < 256) {k : Nat} (hk : k < 4) :
    packN ix / 256 ^ k % 256 = ix k := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  unfold packN
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [Nat.reducePow] <;> omega_arith

/-- The indices as `scanStart` packs them. -/
theorem pack_eq (a b c d : BitVec 32) :
    a + b <<< 8 + c <<< 16 + d <<< 24 =
      BitVec.ofNat 32 (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.reducePow]
  omega_arith

theorem and255 {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n &&& 255).toNat = n % 256 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, show (255 : BitVec 32).toNat = 2 ^ 8 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

theorem and7 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n &&& 7 = BitVec.ofNat 32 (n % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    show (7 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

theorem shr8 {n : Nat} (h : n < 2 ^ 32) : BitVec.ofNat 32 n >>> 8 = BitVec.ofNat 32 (n / 256) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt h]
  omega_arith

/-! ## Choosing among the row's words -/

/-- The selector of column `c`: 1 if the index's low three bits `l` are `c`. -/
theorem pickSel : ∀ l < 8, ∀ c < 8,
    ((BitVec.ofNat 32 l ^^^ BitVec.ofNat 32 c) - 1) >>> 31 = if l = c then 1 else 0 := by decide

/-- What the picks of the columns below `e` have added to `r1` (`m` false),
or to `r3` (`m` true): column `l`, if it is one of them and of that kind. -/
def pickR (a : Nat → BitVec 32) (l e : Nat) (m : Bool) : BitVec 32 := if l < e ∧ mlaCol l = m then a l else 0

theorem mul_one_add_zero (x : BitVec 32) : x * 1 + 0 = x := by
  show x * 1#32 + 0#32 = x
  rw [BitVec.mul_one, BitVec.add_zero]

theorem pickR_hit (a : Nat → BitVec 32) (l c : Nat) :
    a c * (if l = c then 1 else 0) + pickR a l c (mlaCol c) = pickR a l (c + 1) (mlaCol c) := by
  unfold pickR
  by_cases h : l = c
  · subst h
    rw [ite_eq_left rfl, ite_eq_right (fun h => Nat.lt_irrefl _ h.1), ite_eq_left ⟨Nat.lt_succ_self _, rfl⟩,
      mul_one_add_zero]
  · rw [ite_eq_right h, Scan.Arm.mul_zero_add]
    by_cases hl : l < c ∧ mlaCol l = mlaCol c
    · rw [ite_eq_left hl, ite_eq_left ⟨by omega_using [hl.1], hl.2⟩]
    · rw [ite_eq_right hl, ite_eq_right fun h' => hl ⟨by omega_using [h'.1, h], h'.2⟩]

theorem pickR_miss (a : Nat → BitVec 32) (l : Nat) {c : Nat} {m : Bool} (hm : mlaCol c ≠ m) :
    pickR a l c m = pickR a l (c + 1) m := by
  unfold pickR
  by_cases hl : l < c ∧ mlaCol l = m
  · rw [ite_eq_left hl, ite_eq_left ⟨by omega_using [hl.1], hl.2⟩]
  · rw [ite_eq_right hl, ite_eq_right fun h' => hl ⟨by
      have : l ≠ c := fun e => hm (e ▸ h'.2)
      omega_using [h'.1, this], h'.2⟩]

theorem pickR_res (W : Nat → BitVec 32) {l : Nat} (hl : l < 8) :
    pickR (fun c => Scan.Arm.val c (W c)) l 8 false - pickR (fun c => Scan.Arm.val c (W c)) l 8 true = W l := by
  show (if l < 8 ∧ mlaCol l = false then Scan.Arm.val l (W l) else 0) -
    (if l < 8 ∧ mlaCol l = true then Scan.Arm.val l (W l) else 0) = W l
  unfold Scan.Arm.val
  cases hm : mlaCol l
  · obtain e1 : l < 8 ∧ false = false := ⟨hl, rfl⟩
    obtain e2 : ¬(l < 8 ∧ false = true) := fun h => Bool.false_ne_true h.2
    rw [ite_eq_left e1, ite_eq_right e2, ite_eq_right Bool.false_ne_true]
    show W l - 0#32 = W l
    rw [BitVec.sub_zero]
  · obtain e1 : ¬(l < 8 ∧ true = false) := fun h => Bool.false_ne_true h.2.symm
    obtain e2 : l < 8 ∧ true = true := ⟨hl, rfl⟩
    rw [ite_eq_right e1, ite_eq_left e2, ite_eq_left rfl]
    show 0#32 - -W l = W l
    rw [BitVec.zero_sub, BitVec.neg_neg]

/-- Column `c`, if the index's low three bits `l` (in `lr`) are `c`. -/
theorem pick_ok (s : State) (a : Nat → BitVec 32) {l c : Nat} (hl : l < 8) (hc : c < 8)
    (hlr : s.gpr .lr = BitVec.ofNat 32 l) (ha : s.gpr (colReg c) = a c)
    (h1 : s.gpr .r1 = pickR a l c false) (h3 : s.gpr .r3 = pickR a l c true) :
    WP isa (.block (pick c)) s fun t =>
      t.gpr .r1 = pickR a l (c + 1) false ∧ t.gpr .r3 = pickR a l (c + 1) true ∧
      (∀ q, q ≠ .r0 → q ≠ .r1 → q ≠ .r3 → t.gpr q = s.gpr q) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.sp = s.sp := by
  obtain hcv := toNat_ofNat_lt (j := c) (by omega_using [hc])
  unfold pick
  cases hk : mlaCol c
  · simp only [Bool.false_eq_true, ite_false]
    crun [hcv, hlr, Scan.Arm.exec_mla, Scan.Arm.colReg_ne_r0, h1, h3]
    refine ⟨?_, pickR_miss a l (by rw [hk]; decide), fun q h0 h1' _ => by simp only [h0, h1', ite_false]⟩
    rw [pickSel l hl c hc, ← hk, ha]
    exact pickR_hit a l c
  · simp only [ite_true]
    crun [hcv, hlr, Scan.Arm.exec_mla, Scan.Arm.colReg_ne_r0, h1, h3]
    refine ⟨pickR_miss a l (by rw [hk]; decide), ?_, fun q h0 _ h3' => by simp only [h0, h3', ite_false]⟩
    rw [pickSel l hl c hc, ← hk, ha]
    exact pickR_hit a l c

/-! ## The scan -/

/-- The address of the scan's ten words, at `o` in the working space at `r12`. -/
scoped notation:max "sbase " s:max o:max => State.addr (State.gpr s Reg.r12) + BitVec.ofNat 64 o

/-- What a scan needs: the indices below 256; its ten words at `o` in the
working space at `r12`, writable and within the address space; and the
table, 4096 bytes at the static's address, readable, within the address
space and apart from those words. -/
structure ScanPre (sym : String) (o : Nat) (s : State) : Prop where
  idx : ∀ k < 4, (s.gpr (idxReg k)).toNat < 256
  cfit : (s.gpr .r12).toNat + o + 40 ≤ 2 ^ 32
  ofit : o + 40 ≤ 4096
  inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (sbase s o + BitVec.ofNat 64 off) w
  tfit : (s.syms sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  dTS : Region.Disjoint ⟨State.addr (s.syms sym), 4096⟩ ⟨sbase s o, 40⟩

theorem syms_mem (s : State) (m : Mem) : (putMem s m).syms = s.syms := rfl
theorem syms_sub (s : State) (x y : BitVec 32) : (putSub s x y).syms = s.syms := rfl

/-- The indices of a scan from `s`. -/
def ixs (s : State) (k : Nat) : Nat := (s.gpr (idxReg k)).toNat

/-- The address of a word of the table, as the rows of lookup `k` read it:
word `c` of row `r` of group `g` is word `k` of entry `8 (8 g + r) + c`. -/
theorem wordAddr_eq {T : BitVec 32} (hT : T.toNat + 4096 ≤ 2 ^ 32) {k g r c : Nat} (hk : k < 4) (hg : g < 4)
    (hr : r < 8) (hc : c < 8) :
    State.addr (T + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 (1024 * g) + BitVec.ofNat 32 (wordOff r c)) =
      State.addr T + BitVec.ofNat 64 (16 * (8 * (8 * g + r) + c) + 4 * k) := by
  unfold wordOff
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, addr_add (by omega_arith)]
  exact congrArg (fun n => State.addr T + BitVec.ofNat 64 n) (by omega_arith)

/-- A slot read past a store to another. -/
theorem slot_rw (m : Mem) (D : Addr) {i j : Nat} (x : BitVec 32) (h : j + 4 ≤ i ∨ i + 4 ≤ j) (hi : i < 4096)
    (hj : j < 4096) :
    (m.writeW (D + BitVec.ofNat 64 i) x).readW (D + BitVec.ofNat 64 j) 32 = m.readW (D + BitVec.ofNat 64 j) 32 :=
  Mem.readW_writeW_sep (Offset.sep D (d := j) (n := 4) (e := i) (k := 4) h (by omega_arith) (by omega_arith))
    (by decide)

/-- A slot of the scan past the count of `rows`, at 20. -/
theorem scanSlot_frame {m m' : Mem} {D : Addr} (h : Frame [⟨D + BitVec.ofNat 64 20, 4⟩] m m') {i : Nat}
    (hi : i + 4 ≤ 20 ∨ 24 ≤ i) (hi' : i < 4096) :
    m'.readW (D + BitVec.ofNat 64 i) 32 = m.readW (D + BitVec.ofNat 64 i) 32 :=
  h.readW (r := ⟨D + BitVec.ofNat 64 i, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint D (by omega_using [hi]) (by omega_arith) (by decide)) (by decide)

/-- The state of a scan of the table `sym` from `s` with `k` lookups made:
`r2`, `r3` and `lr` of `s`, the indices left, the count and the values in
their slots, and nothing else of memory written. -/
structure LookAt (s : State) (sym : String) (o k : Nat) (v : State) : Prop where
  r12 : v.gpr .r12 = s.gpr .r12
  fr : Frame [⟨sbase s o, 40⟩] s.mem v.mem
  s2 : v.mem.readW (sbase s o + BitVec.ofNat 64 0) 32 = s.gpr .r2
  s3 : v.mem.readW (sbase s o + BitVec.ofNat 64 4) 32 = s.gpr .r3
  slr : v.mem.readW (sbase s o + BitVec.ofNat 64 8) 32 = s.gpr .lr
  sx : v.mem.readW (sbase s o + BitVec.ofNat 64 12) 32 = BitVec.ofNat 32 (packN (ixs s) / 256 ^ k)
  sk : v.mem.readW (sbase s o + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 (4 * k)
  sv : ∀ j < k, v.mem.readW (sbase s o + BitVec.ofNat 64 (24 + 4 * j)) 32 =
    tw s.mem (s.syms sym) (ixs s (k - 1 - j)) (k - 1 - j)
  rd : v.rd = s.rd
  wr : v.wr = s.wr
  sp : v.sp = s.sp
  syms : v.syms = s.syms

theorem count_step : ∀ k < 4, BitVec.ofNat 32 (4 * k) + 4 = BitVec.ofNat 32 (4 * (k + 1)) ∧
    (BitVec.ofNat 32 (4 * k) + 4 - 16 == 0) = decide (k + 1 = 4) := by decide

/-- The end of a lookup: the values moved up one slot, the lookup's value
`r1 - r3` in the first, and the count `c` of lookups, times four, on four. -/
theorem lookEnd_ok (p : State) {o : Nat} {D : Addr}
    (aS : ∀ off, off < 40 → State.addr (p.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off)
    (hoff : ∀ off, off < 40 → o + off < 4096)
    (inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions p.wr (D + BitVec.ofNat 64 off) w) {c : BitVec 32}
    (hc : p.mem.readW (D + BitVec.ofNat 64 16) 32 = c) :
    WP isa (.block (lookEnd o)) p fun w =>
      w.mem = ((((p.mem.writeW (D + BitVec.ofNat 64 36) (p.mem.readW (D + BitVec.ofNat 64 32) 32)).writeW
        (D + BitVec.ofNat 64 32) (p.mem.readW (D + BitVec.ofNat 64 28) 32)).writeW
        (D + BitVec.ofNat 64 28) (p.mem.readW (D + BitVec.ofNat 64 24) 32)).writeW
        (D + BitVec.ofNat 64 24) (p.gpr .r1 - p.gpr .r3)).writeW (D + BitVec.ofNat 64 16) (c + 4) ∧
      w.z = (c + 4 - 16 == 0) ∧ w.gpr .r12 = p.gpr .r12 ∧ w.rd = p.rd ∧ w.wr = p.wr ∧ w.sp = p.sp := by
  have inS' : ∀ {off w : Nat}, off + w ≤ 40 → InRegions (p.rd ++ p.wr) (D + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hc⟩ := inS hw; exact ⟨g, List.mem_append_right _ hg, hc⟩
  unfold lookEnd
  crun [aS, hoff, inS, inS', slot_rw, Mem.readW_writeW_self32, or_true, true_or, hc]

/-- A lookup: the value of the next index to the first of the values' slots. -/
theorem look_ok {s v : State} {sym : String} {o k : Nat} (hp : ScanPre sym o s) (hk : k < 4)
    (hv : LookAt s sym o k v) :
    WP isa (look sym o) v fun w => LookAt s sym o (k + 1) w ∧ w.z = decide (k + 1 = 4) := by
  have hcf := hp.cfit
  have hof := hp.ofit
  have hTf := hp.tfit
  have hix : ∀ j < 4, ixs s j < 256 := hp.idx
  obtain hpl := packN_lt hix
  obtain hxk : packN (ixs s) / 256 ^ k < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hpl
  obtain hxb : BitVec.ofNat 32 (packN (ixs s) / 256 ^ k) &&& 255 = s.gpr (idxReg k) :=
    BitVec.eq_of_toNat_eq (by rw [and255 hxk, packN_byte hix hk]; rfl)
  obtain hik := hix k hk
  obtain ⟨h, hh⟩ : ∃ h, ixs s k / 8 = h := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, ixs s k % 8 = l := ⟨_, rfl⟩
  obtain hh32 : h < 32 := by omega_using [hik, hh]
  obtain hl8 : l < 8 := by omega_using [hl]
  obtain hhl : 8 * h + l = ixs s k := by omega_using [hh, hl]
  -- The slots and the table.
  have hfr := hv.fr
  have s2 := hv.s2
  have s3 := hv.s3
  have slr := hv.slr
  have sx := hv.sx
  have sk := hv.sk
  have sv := hv.sv
  have dTS := hp.dTS
  have trd := hp.trd
  obtain ⟨D, hD⟩ : ∃ D, sbase s o = D := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, s.syms sym = T := ⟨_, rfl⟩
  rw [hD] at hfr s2 s3 slr sx sk sv dTS
  rw [hT] at hTf dTS trd sv
  have aS : ∀ off, off < 40 → State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off :=
    fun off ho => by rw [addr_add (by omega_arith), ← hD, Offset.add_add]
  have hoff : ∀ off, off < 40 → o + off < 4096 := fun off ho => by omega_arith
  have inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (D + BitVec.ofNat 64 off) w :=
    fun hw => by rw [← hD]; exact hp.inS hw
  have inS' : ∀ {off w : Nat}, off + w ≤ 40 → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hc⟩ := inS hw; exact ⟨g, List.mem_append_right _ hg, hc⟩
  -- A word of the table, in a memory that differs from `s.mem` in the slots.
  have tword (m : Mem) (hm : Frame [⟨D, 40⟩] s.mem m) (e : Nat) (he : e < 256) :
      m.readW (State.addr T + BitVec.ofNat 64 (16 * e + 4 * k)) 32 = tw s.mem T e k := by
    rw [hm.readW (r := ⟨State.addr T + BitVec.ofNat 64 (16 * e + 4 * k), 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dTS.sub_left (Offset.sub_base _ (by omega_arith))) (by decide), tw, addr_add (by omega_arith)]
  have hrd := hv.rd
  have hwr := hv.wr
  have v12 := hv.r12
  unfold look
  refine WP.seq ?_
  unfold lookStart
  rw [WP.block_append_iff, WP.block_append_iff]
  -- The index.
  have hA : WP isa (.block [.ldr .r0 .r12 (o + 12), .dp .and .r0 .r0 (.imm 255)]) v fun u =>
      u.gpr .r0 = s.gpr (idxReg k) ∧ (∀ q, q ≠ .r0 → u.gpr q = v.gpr q) ∧ u.mem = v.mem ∧ u.rd = v.rd ∧
      u.wr = v.wr ∧ u.sp = v.sp := by
    crun [v12, aS, hoff, inS', hrd, hwr, sx]
    exact ⟨hxb, fun q hq => by simp only [hq, ite_false]⟩
  refine VG.Arm.WP.mono_syms hA fun u ⟨u0, uo, um, urd, uwr, usp⟩ usy => ?_
  -- Its row's one-hot word, and the columns cleared.
  refine VG.Arm.WP.mono_syms (Scan.Arm.start_ok u (by rw [u0]; exact hik))
    fun t ⟨t2, t3, tc, to, tm, trd', twr, tsp⟩ tsy => ?_
  obtain t12 : t.gpr .r12 = s.gpr .r12 := (to _ (by decide)).trans ((uo _ (by decide)).trans v12)
  -- The table's pointer.
  have hB : WP isa (.block [.adrSym .lr sym, .ldr .r0 .r12 (o + 16), .dp .add .lr .lr (.reg .r0)]) t fun x =>
      x.gpr .lr = T + BitVec.ofNat 32 (4 * k) ∧ (∀ q, q ≠ .r0 → q ≠ .lr → x.gpr q = t.gpr q) ∧ x.mem = t.mem ∧
      x.rd = t.rd ∧ x.wr = t.wr ∧ x.sp = t.sp := by
    have hsy := hv.syms
    crun [exec_adrSym, t12, aS, hoff, inS', trd', twr, urd, uwr, hrd, hwr, tm, um, sk, tsy, usy, hsy, hT]
    exact fun q h0 hl' => by simp only [h0, hl', ite_false]
  refine VG.Arm.WP.mono_syms hB fun x ⟨xl, xo, xm, xrd, xwr, xsp⟩ xsy => ?_
  obtain x12 : x.gpr .r12 = s.gpr .r12 := (xo _ (by decide) (by decide)).trans t12
  -- The rows.
  obtain pre : Scan.Arm.RowsPre wordOff 1024 (o + 20) h (T + BitVec.ofNat 32 (4 * k)) x :=
    { hh := hh32
      r2 := by rw [xo _ (by decide) (by decide), t2, u0, ← hh]; rfl
      r3 := by rw [xo _ (by decide) (by decide), t3]
      lr := xl
      cols := fun c hc => by rw [xo _ (Scan.Arm.colReg_ne_r0 c) (Scan.Arm.colReg_ne_lr c), tc c hc]
      hcnt := hoff 20 (by decide)
      slot := by rw [x12, aS 20 (by decide), xwr, twr, uwr, hwr]; exact inS (by decide)
      hstride := by decide
      hoffs := fun r hr c hc => by unfold wordOff; omega_arith
      rd := fun g hg r hr c hc => by
        rw [wordAddr_eq hTf hk hg hr hc, xrd, trd', urd, hrd, xwr, twr, uwr, hwr]
        exact ⟨_, trd, Offset.contains_base (State.addr T) (n := 4) (k := 4096) (by omega_arith) (by omega_arith)⟩
      dis := fun g hg r hr c hc => by
        rw [wordAddr_eq hTf hk hg hr hc, x12, aS 20 (by decide)]
        exact (dTS.sub_left (Offset.sub_base _ (n := 4) (by omega_arith))).sub_right (Offset.sub_base _ (by decide)) }
  refine WP.seq (VG.Arm.WP.mono_syms (Scan.Arm.rows_ok pre) fun y ⟨yc, yo, yfr, yrd, ywr, ysp⟩ ysy => ?_)
  rw [x12, aS 20 (by decide), xm, tm, um] at yfr
  obtain y12 : y.gpr .r12 = s.gpr .r12 := (yo _ (by decide)).trans x12
  -- The words of the index's row.
  obtain ⟨W, hW⟩ : ∃ W : Nat → BitVec 32, W = fun c => tw s.mem T (8 * h + c) k := ⟨_, rfl⟩
  obtain ya : ∀ c < 8, y.gpr (colReg c) = Scan.Arm.val c (W c) := by
    intro c hc
    rw [yc c hc, hW, Scan.Arm.wordAt, wordAddr_eq hTf hk (by omega_using [hh32]) (by omega_arith) hc,
      show 16 * (8 * (8 * (h / 8) + h % 8) + c) + 4 * k = 16 * (8 * h + c) + 4 * k by omega_arith, xm, tm, um]
    exact congrArg _ (tword v.mem hfr _ (by omega_using [hh32, hc]))
  -- The slots after the rows.
  have ysl {i : Nat} (hi : i + 4 ≤ 20 ∨ 24 ≤ i) (hi' : i < 4096) :
      y.mem.readW (D + BitVec.ofNat 64 i) 32 = v.mem.readW (D + BitVec.ofNat 64 i) 32 := scanSlot_frame yfr hi hi'
  obtain yrd' : y.rd = s.rd := yrd.trans (xrd.trans (trd'.trans (urd.trans hrd)))
  obtain ywr' : y.wr = s.wr := ywr.trans (xwr.trans (twr.trans (uwr.trans hwr)))
  rw [List.append_assoc, WP.block_append_iff]
  -- The index's low three bits, and the indices left.
  have hP : WP isa (.block (pickStart o)) y fun z =>
      z.gpr .lr = BitVec.ofNat 32 l ∧ z.gpr .r1 = 0 ∧ z.gpr .r3 = 0 ∧
      (∀ q, q ≠ .r1 → q ≠ .r2 → q ≠ .r3 → q ≠ .lr → z.gpr q = y.gpr q) ∧
      z.mem = y.mem.writeW (D + BitVec.ofNat 64 12) (BitVec.ofNat 32 (packN (ixs s) / 256 ^ (k + 1))) ∧
      z.rd = y.rd ∧ z.wr = y.wr ∧ z.sp = y.sp := by
    have ysx := (ysl (i := 12) (by decide) (by decide)).trans sx
    unfold pickStart
    crun [y12, aS, hoff, inS, inS', yrd', ywr', ysx]
    refine ⟨?_, fun q h1 h2 h3 hl' => by simp only [h1, h2, h3, hl', ite_false], ?_⟩
    · rw [and7 hxk, ← hl, ← packN_byte hix hk, Nat.mod_mod_of_dvd _ (by decide)]
    · rw [shr8 hxk, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  refine VG.Arm.WP.mono_syms hP fun z ⟨zl, z1, z3, zo, zm, zrd, zwr, zsp⟩ zsy => ?_
  rw [WP.block_append_iff]
  -- The picks of the columns below `e`.
  have picks : ∀ e ≤ 8, WP isa (.block ((List.range e).flatMap pick)) z fun p =>
      p.gpr .r1 = pickR (fun c => Scan.Arm.val c (W c)) l e false ∧
      p.gpr .r3 = pickR (fun c => Scan.Arm.val c (W c)) l e true ∧
      (∀ q, q ≠ .r0 → q ≠ .r1 → q ≠ .r3 → p.gpr q = z.gpr q) ∧ p.mem = z.mem ∧ p.rd = z.rd ∧ p.wr = z.wr ∧
      p.sp = z.sp := by
    intro e he
    induction e with
    | zero =>
      exact WP.block_nil ⟨by rw [z1, pickR, ite_eq_right (fun h' => Nat.not_lt_zero _ h'.1)],
        by rw [z3, pickR, ite_eq_right (fun h' => Nat.not_lt_zero _ h'.1)], fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
    | succ e ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        WP.block_append_iff]
      refine WP.mono (ih (by omega_using [he])) fun p ⟨p1, p3, po, pm, prd, pwr, psp⟩ => ?_
      obtain he8 : e < 8 := by omega_using [he]
      refine WP.mono (pick_ok p (fun c => Scan.Arm.val c (W c)) hl8 he8
        (by rw [po _ (by decide) (by decide) (by decide), zl])
        (by rw [po _ (Scan.Arm.colReg_ne_r0 e) (Scan.Arm.colReg_ne_r1 e) (Scan.Arm.colReg_ne_r3 e),
          zo _ (Scan.Arm.colReg_ne_r1 e) (Scan.Arm.colReg_ne_r2 e) (Scan.Arm.colReg_ne_r3 e)
            (Scan.Arm.colReg_ne_lr e), ya e he8]) p1 p3)
        fun q ⟨q1, q3, qo, qm, qrd, qwr, qsp⟩ => ?_
      exact ⟨q1, q3, fun r h0 h1 h3 => (qo r h0 h1 h3).trans (po r h0 h1 h3), qm.trans pm, qrd.trans prd,
        qwr.trans pwr, qsp.trans psp⟩
  refine VG.Arm.WP.mono_syms (picks 8 (Nat.le_refl _)) fun p ⟨p1, p3, po, pm, prd, pwr, psp⟩ psy => ?_
  rw [zm] at pm
  obtain p12 : p.gpr .r12 = s.gpr .r12 :=
    (po _ (by decide) (by decide) (by decide)).trans ((zo _ (by decide) (by decide) (by decide) (by decide)).trans y12)
  obtain prd' : p.rd = s.rd := prd.trans (zrd.trans yrd')
  obtain pwr' : p.wr = s.wr := pwr.trans (zwr.trans ywr')
  obtain psp' : p.sp = s.sp := psp.trans (zsp.trans (ysp.trans (xsp.trans (tsp.trans (usp.trans hv.sp)))))
  obtain psy' : p.syms = s.syms := psy.trans (zsy.trans (ysy.trans (xsy.trans (tsy.trans (usy.trans hv.syms)))))
  -- The value, and the count.
  obtain res : p.gpr .r1 - p.gpr .r3 = tw s.mem T (ixs s k) k := by
    rw [p1, p3, pickR_res W hl8, hW]
    show tw s.mem T (8 * h + l) k = _
    rw [hhl]
  have y16 := (ysl (i := 16) (by decide) (by decide)).trans sk
  have y0 := (ysl (i := 0) (by decide) (by decide)).trans s2
  have y4 := (ysl (i := 4) (by decide) (by decide)).trans s3
  have y8 := (ysl (i := 8) (by decide) (by decide)).trans slr
  obtain ⟨c1, c2⟩ := count_step k hk
  obtain yf : Frame [⟨D, 40⟩] s.mem y.mem :=
    hfr.trans (yfr.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub_base _ (by decide)⟩)
  have aSp : ∀ off, off < 40 → State.addr (p.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off :=
    fun off ho => by rw [p12]; exact aS off ho
  -- The slots after the indices left are stored.
  have psl {i : Nat} (hi : i + 4 ≤ 12 ∨ 24 ≤ i) (hi' : i < 4096) :
      p.mem.readW (D + BitVec.ofNat 64 i) 32 = v.mem.readW (D + BitVec.ofNat 64 i) 32 := by
    rw [pm, slot_rw _ _ _ (by omega_using [hi]) (by decide) hi', ysl (by omega_using [hi]) hi']
  obtain p16 : p.mem.readW (D + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 (4 * k) := by
    rw [pm, slot_rw _ _ _ (by decide) (by decide) (by decide), ysl (by decide) (by decide), sk]
  refine VG.Arm.WP.mono_syms (lookEnd_ok p aSp hoff (fun hw => by rw [pwr']; exact inS hw) p16)
    fun w ⟨wm, wz, w12, wrd, wwr, wsp⟩ wsy => ?_
  rw [res, c1] at wm
  obtain pf : Frame [⟨D, 40⟩] s.mem p.mem := by
    rw [pm]; exact yf.writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  refine ⟨⟨w12.trans p12, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, wrd.trans prd', wwr.trans pwr', wsp.trans psp',
    wsy.trans psy'⟩, by rw [wz, c2]⟩
  all_goals rw [hD, wm]
  · exact ((((pf.writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · simp (disch := decide) only [slot_rw]
    rw [psl (by decide) (by decide), s2]
  · simp (disch := decide) only [slot_rw]
    rw [psl (by decide) (by decide), s3]
  · simp (disch := decide) only [slot_rw]
    rw [psl (by decide) (by decide), slr]
  · simp (disch := decide) only [slot_rw]
    rw [pm, Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]
  · rw [hT]
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega_using [hj, hk]) with rfl | rfl | rfl | rfl
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rfl
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rw [psl (by decide) (by decide), sv 0 (by omega_using [hj])]
      rw [show k + 1 - 1 - 1 = k - 1 - 0 by omega_arith]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rw [psl (by decide) (by decide), sv 1 (by omega_using [hj])]
      rw [show k + 1 - 1 - 2 = k - 1 - 1 by omega_arith]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32, Nat.reduceMul, Nat.reduceAdd]
      rw [psl (by decide) (by decide), sv 2 (by omega_using [hj])]
      rw [show k + 1 - 1 - 3 = k - 1 - 2 by omega_arith]

/-- The scan: `r8 + k` is word `k` of the entry of the table whose number
is in `r4 + k`; only `r0`, `r1`, `r4`–`r11` and the scan's ten words are
written. -/
theorem scan_ok (s : State) (sym : String) (o : Nat) (h : ScanPre sym o s) :
    WP isa (scan sym o) s fun t =>
      (∀ k < 4, t.gpr (accReg k) = tw s.mem (s.syms sym) (s.gpr (idxReg k)).toNat k) ∧
      Keep [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      Frame [⟨sbase s o, 40⟩] s.mem t.mem := by
  have hcf := h.cfit
  have hof := h.ofit
  obtain ⟨D, hD⟩ : ∃ D, sbase s o = D := ⟨_, rfl⟩
  have aS : ∀ off, off < 40 → State.addr (s.gpr .r12 + BitVec.ofNat 32 (o + off)) = D + BitVec.ofNat 64 off :=
    fun off ho => by rw [addr_add (by omega_arith), ← hD, Offset.add_add]
  obtain a0 : State.addr (s.gpr .r12 + BitVec.ofNat 32 o) = D + BitVec.ofNat 64 0 := by
    rw [addr_add (by omega_arith), hD, BitVec.add_zero]
  have hoff : ∀ off, off < 40 → o + off < 4096 := fun off ho => by omega_arith
  obtain ho : o < 4096 := by omega_arith
  have inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (D + BitVec.ofNat 64 off) w :=
    fun hw => by rw [← hD]; exact h.inS hw
  have inS' : ∀ {off w : Nat}, off + w ≤ 40 → InRegions (s.rd ++ s.wr) (D + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hc⟩ := inS hw; exact ⟨g, List.mem_append_right _ hg, hc⟩
  unfold scan
  -- `r2`, `r3`, `lr` and the indices to their slots.
  have hS : WP isa (.block (scanStart o)) s fun u =>
      u.mem = ((((s.mem.writeW (D + BitVec.ofNat 64 0) (s.gpr .r2)).writeW (D + BitVec.ofNat 64 4) (s.gpr .r3)).writeW
        (D + BitVec.ofNat 64 8) (s.gpr .lr)).writeW (D + BitVec.ofNat 64 12)
        (s.gpr .r4 + s.gpr .r5 <<< 8 + s.gpr .r6 <<< 16 + s.gpr .r7 <<< 24)).writeW (D + BitVec.ofNat 64 16)
        (0 : BitVec 32) ∧
      u.gpr .r12 = s.gpr .r12 ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
    unfold scanStart
    crun [a0, aS, hoff, ho, inS]
  refine WP.seq (VG.Arm.WP.mono_syms hS fun u ⟨um, u12, urd, uwr, usp⟩ usy => ?_)
  obtain h₀ : LookAt s sym o 0 u := by
    refine ⟨u12, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => absurd hj (Nat.not_lt_zero j), urd, uwr, usp, usy⟩
    all_goals rw [hD, um]
    · exact (((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
        List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
    · simp (disch := decide) only [slot_rw, Mem.readW_writeW_self32]
      rw [pack_eq, Nat.pow_zero, Nat.div_one]
      rfl
    · rw [Mem.readW_writeW_self32]
      rfl
  -- The lookups.
  have loop : WP isa (.loop (look sym o) .ne) u (LookAt s sym o 4) := by
    refine WP.loop (M := isa) (fun n (v : State) => ∃ k, n = 4 - k ∧ k < 4 ∧ LookAt s sym o k v) ?_ 4 u
      ⟨0, rfl, by decide, h₀⟩
    rintro n v ⟨k, rfl, hk, hv⟩
    refine WP.mono (look_ok h hk hv) fun w ⟨hw, wz⟩ => ?_
    by_cases he : k + 1 = 4
    · exact .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, he ▸ hw⟩
    · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, 4 - (k + 1), by omega_using [hk], k + 1,
        rfl, by omega_using [hk, he], hw⟩
  refine WP.seq (WP.mono loop fun v hv => ?_)
  -- The values, and `r2`, `r3` and `lr` back.
  have s2 := hv.s2
  have s3 := hv.s3
  have slr := hv.slr
  have r36 := hv.sv 3 (by decide)
  have r32 := hv.sv 2 (by decide)
  have r28 := hv.sv 1 (by decide)
  have r24 := hv.sv 0 (by decide)
  have hfr := hv.fr
  rw [hD] at s2 s3 slr r36 r32 r28 r24
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at r36 r32 r28 r24
  have v12 := hv.r12
  have hrd := hv.rd
  have hwr := hv.wr
  have hE : WP isa (.block (scanEnd o)) v fun t =>
      t.gpr .r8 = tw s.mem (s.syms sym) (ixs s 0) 0 ∧ t.gpr .r9 = tw s.mem (s.syms sym) (ixs s 1) 1 ∧
      t.gpr .r10 = tw s.mem (s.syms sym) (ixs s 2) 2 ∧ t.gpr .r11 = tw s.mem (s.syms sym) (ixs s 3) 3 ∧
      t.gpr .r2 = s.gpr .r2 ∧ t.gpr .r3 = s.gpr .r3 ∧ t.gpr .lr = s.gpr .lr ∧ t.gpr .r12 = s.gpr .r12 ∧
      t.mem = v.mem ∧ t.rd = v.rd ∧ t.wr = v.wr ∧ t.sp = v.sp := by
    unfold scanEnd
    crun [v12, a0, aS, hoff, ho, inS', hrd, hwr, s2, s3, slr, r36, r32, r28, r24]
  refine WP.mono hE fun t ⟨t8, t9, t10, t11, t2, t3, tlr, t12, tm, trd, twr, tsp⟩ => ?_
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, trd.trans hrd, twr.trans hwr, tsp.trans hv.sp⟩, by rw [tm]; exact hfr⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl
    · exact t8
    · exact t9
    · exact t10
    · exact t11
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h0, h1, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
    cases r
    case r2 => exact t2
    case r3 => exact t3
    case r12 => exact t12
    case lr => exact tlr
    all_goals first
      | exact absurd rfl h0
      | exact absurd rfl h1
      | exact absurd rfl h4
      | exact absurd rfl h5
      | exact absurd rfl h6
      | exact absurd rfl h7
      | exact absurd rfl h8
      | exact absurd rfl h9
      | exact absurd rfl h10
      | exact absurd rfl h11

end VG.Proof.Cast5.Arm

end

end

/-!
# CAST5 on ARMv7: a round

`round up` computes `I` (`byType mix`, `rotate`), spreads its bytes over
`r4`–`r7` (`spread`), scans `VG_CAST5_S1234` and combines the four values into `f`
(`byType comb`), makes the Feistel step (`feistel`), and moves the type and
the count of rounds left on (`next`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym)

/-! ## Choosing by the type -/

/-- The address of the slot at `off` of the working space at `r12`. -/
scoped notation:max "slot " s:max off:max => State.addr (State.gpr s Reg.r12 + BitVec.ofNat 32 off)

theorem byType_ok (s : State) (f : Nat → List Instr) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3)
    (hin : InRegions (s.rd ++ s.wr) (slot s 20) 4) (hv : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    {Q : State → Prop} (hQ : ∀ u, Keep [.r0] s u → u.mem = s.mem → WP isa (.block (f t)) u Q) :
    WP isa (byType f) s Q := by
  unfold byType
  refine WP.seq ?_
  crun [typeOff, hin, hv]
  rcases ht with rfl | rfl | rfl
  · refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite true rfl (fun _ => hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
      (fun h => absurd h (by decide))
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr
  · refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ => ?_)
    refine WP.seq ?_
    crun
    refine WP.ite false rfl (fun h => absurd h (by decide)) (fun _ =>
      hQ _ ⟨fun r hr => ?_, rfl, rfl, rfl⟩ rfl)
    simp only [List.mem_singleton] at hr
    simp only [gpr_sub]; exact gpr_setReg_of_ne _ _ hr

/-! ## The pieces of a round -/

theorem mix_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {km d : Spec.Cast5.Word}
    (h3 : s.gpr .r3 = d) (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km) :
    WP isa (.block (Impl.Cast5.Arm.mix t)) s fun u => u.gpr .r1 = Proof.Cast5.mix t km d ∧ Keep [.r1] s u ∧ u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.mix
    crun [hin, hv, h3]
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem rotateStep_ok (s : State) {b : Nat} (hb : b < 5) {a kb : BitVec 32}
    (h1 : s.gpr .r1 = a) (h0 : s.gpr .r0 = kb) :
    WP isa (.block (rotateStep b)) s fun u =>
      u.gpr .r1 = Proof.Cast5.step a kb b ∧ u.gpr .r0 = (if b < 4 then kb >>> 1 else kb) ∧
      Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have hn : 1 ≤ 32 - 2 ^ b ∧ 32 - 2 ^ b ≤ 31 := by
    rcases (show b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 by omega_using [hb]) with h | h | h | h | h <;>
      subst h <;> decide
  unfold rotateStep
  by_cases h4 : b < 4
  · rw [ite_eq_left h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_left h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩
  · rw [ite_eq_right h4]
    crun [h1, h0, hn]
    exact ⟨rfl, by rw [ite_eq_right h4], ⟨by keep_regs, rfl, rfl, rfl⟩⟩

theorem rotate_ok (s : State) {a kr : BitVec 32} (h1 : s.gpr .r1 = a)
    (hin : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4)
    (hv : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr) :
    WP isa (.block rotate) s fun u =>
      u.gpr .r1 = a.rotateLeft (kr.toNat % 32) ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
  have e : rotate = [.ldr .r0 .lr 64] ++ rotateStep 0 ++ rotateStep 1 ++ rotateStep 2 ++ rotateStep 3 ++
      rotateStep 4 := rfl
  rw [e, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff]
  have k0 : WP isa (.block [.ldr .r0 .lr 64]) s fun u =>
      u.gpr .r0 = kr ∧ u.gpr .r1 = a ∧ Keep [.r0, .r1, .r4, .r5] s u ∧ u.mem = s.mem := by
    crun [hin, hv, h1]
    exact ⟨fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr; simp only [gpr_setReg, hr.1, ite_false],
      rfl, rfl, rfl⟩
  refine WP.mono k0 fun t₀ ⟨k₀, a₀, p₀, m₀⟩ => ?_
  refine WP.mono (rotateStep_ok t₀ (by decide) a₀ k₀) fun t₁ ⟨a₁, k₁, p₁, m₁⟩ => ?_
  rw [ite_eq_left (by decide)] at k₁
  refine WP.mono (rotateStep_ok t₁ (by decide) a₁ k₁) fun t₂ ⟨a₂, k₂, p₂, m₂⟩ => ?_
  rw [ite_eq_left (by decide)] at k₂
  refine WP.mono (rotateStep_ok t₂ (by decide) a₂ k₂) fun t₃ ⟨a₃, k₃, p₃, m₃⟩ => ?_
  rw [ite_eq_left (by decide)] at k₃
  refine WP.mono (rotateStep_ok t₃ (by decide) a₃ k₃) fun t₄ ⟨a₄, k₄, p₄, m₄⟩ => ?_
  rw [ite_eq_left (by decide)] at k₄
  refine WP.mono (rotateStep_ok t₄ (by decide) a₄ k₄) fun t₅ ⟨a₅, _, p₅, m₅⟩ => ?_
  refine ⟨?_, p₀.trans (p₁.trans (p₂.trans (p₃.trans (p₄.trans p₅)))), by rw [m₅, m₄, m₃, m₂, m₁, m₀]⟩
  rw [a₅, Proof.Cast5.steps_eq]

/-- Index `k` of a scan of `I`: byte `k` of `I` (from the least significant). -/
def idx (i : BitVec 32) : Nat → BitVec 32
  | 0 => i &&& 255
  | 1 => i >>> 8 &&& 255
  | 2 => i >>> 16 &&& 255
  | _ => i >>> 24

theorem idx_toNat (i : BitVec 32) {k : Nat} (hk : k < 4) :
    (idx i k).toNat = i.toNat / 2 ^ (8 * k) % 256 := by
  have := i.isLt
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;>
    simp only [idx, BitVec.toNat_ushiftRight, BitVec.toNat_and, Nat.shiftRight_eq_div_pow,
      show (255 : BitVec 32).toNat = 255 from rfl, show (255 : Nat) = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod] <;> omega_using []

theorem idx_lt (i : BitVec 32) {k : Nat} (hk : k < 4) : (idx i k).toNat < 256 := by
  rw [idx_toNat i hk]; omega_using []

theorem idx_byte (i : BitVec 32) {k : Nat} (hk : k < 4) :
    BitVec.ofNat 8 (idx i k).toNat = Spec.Cast5.byte i (3 - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, idx_toNat i hk]
  simp only [Spec.Cast5.byte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> omega_using []

theorem spread_ok (s : State) {i : BitVec 32} (h1 : s.gpr .r1 = i) :
    WP isa (.block spread) s fun u =>
      (∀ k < 4, u.gpr (idxReg k) = idx i k) ∧ Keep [.r4, .r5, .r6, .r7] s u ∧ u.mem = s.mem := by
  unfold spread
  crun [h1]
  refine ⟨fun k hk => ?_, ⟨fun r hr => ?_, rfl, rfl, rfl⟩⟩
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega_using [hk]) with rfl | rfl | rfl | rfl <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem comb_ok (s : State) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) :
    WP isa (.block (Impl.Cast5.Arm.comb t)) s fun u =>
      u.gpr .r1 = Proof.Cast5.comb t (s.gpr .r11) (s.gpr .r10) (s.gpr .r9) (s.gpr .r8) ∧ Keep [.r1] s u ∧
        u.mem = s.mem := by
  rcases ht with rfl | rfl | rfl <;>
  · unfold Impl.Cast5.Arm.comb
    crun
    exact ⟨rfl, ⟨fun r hr => by simp only [List.mem_singleton] at hr; simp only [gpr_setReg, hr, ite_false], rfl, rfl, rfl⟩⟩

theorem feistel_ok (s : State) (up : Bool) :
    WP isa (.block (feistel up)) s fun u =>
      u.gpr .r2 = s.gpr .r3 ∧ u.gpr .r3 = s.gpr .r1 ^^^ s.gpr .r2 ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧ Keep [.r1, .r2, .r3, .lr] s u ∧
      u.mem = s.mem := by
  cases up <;>
  · unfold feistel
    crun
    exact ⟨by keep_regs, rfl, rfl, rfl⟩

/-- The type after `t`. -/
def nextT (up : Bool) (t : Nat) : Nat :=
  if up then (if t = 3 then 1 else t + 1) else (if t = 1 then 3 else t - 1)

/-- The type `v` (in `r0`) to its slot, then the count of rounds left down. -/
theorem nextTail_ok (s : State) {v cnt : BitVec 32} (h0 : s.gpr .r0 = v)
    (hinT : InRegions s.wr (slot s 20) 4)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt) :
    WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1), .str .r0 .r12 cntOff]) s
      fun u => u.mem = (s.mem.writeW (slot s 20) v).writeW (slot s 16) (cnt - 1) ∧ u.z = (cnt - 1 == 0) ∧
        Keep [.r0] s u := by
  have hinC' : InRegions (s.rd ++ s.wr) (slot s 16) 4 := by
    obtain ⟨g, hg, hc⟩ := hinC; exact ⟨g, List.mem_append_right _ hg, hc⟩
  crun [typeOff, cntOff, h0, hinT, hinC, hinC', hvC]
  exact ⟨by keep_regs, rfl, rfl, rfl⟩

theorem next_ok (s : State) (up : Bool) {t : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) {cnt : BitVec 32}
    (hinT : InRegions s.wr (slot s 20) 4) (hvT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t)
    (hinC : InRegions s.wr (slot s 16) 4) (hvC : s.mem.readW (slot s 16) 32 = cnt)
    (hsep : Mem.Sep (slot s 16) 4 (slot s 20) 4) :
    WP isa (next up) s fun u =>
      u.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      u.z = (cnt - 1 == 0) ∧ Keep [.r0] s u := by
  have hinT' : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
    obtain ⟨g, hg, hc⟩ := hinT; exact ⟨g, List.mem_append_right _ hg, hc⟩
  have hvC' (v : BitVec 32) : (s.mem.writeW (slot s 20) v).readW (slot s 16) 32 = cnt := by
    rw [Mem.readW_writeW_sep hsep (by decide), hvC]
  -- The rest, from the state after the branch, which wrote only `r0` and the flags.
  have tail : ∀ u : State, Keep [.r0] s u → u.mem = s.mem → u.gpr .r0 = BitVec.ofNat 32 (nextT up t) →
      WP isa (.block [.str .r0 .r12 typeOff, .ldr .r0 .r12 cntOff, .subs .r0 .r0 (.imm 1),
        .str .r0 .r12 cntOff]) u fun w =>
      w.mem = (s.mem.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1) ∧
      w.z = (cnt - 1 == 0) ∧ Keep [.r0] s w := by
    intro u uk um u0
    have e12 : u.gpr .r12 = s.gpr .r12 := uk.gpr _ (by decide)
    have es (off : Nat) : slot u off = slot s off := by rw [e12]
    refine WP.mono (nextTail_ok u u0 (by rw [es, uk.wr]; exact hinT) (by rw [es, uk.wr]; exact hinC)
      (by rw [es, es, um]; exact hvC' _)) fun w ⟨wm, wz, wk⟩ => ⟨by rw [wm, es, es, um], wz, uk.trans wk⟩
  unfold next
  cases up <;> rcases ht with rfl | rfl | rfl
  all_goals
    refine WP.seq ?_
    crun [typeOff, hinT', hvT]
  all_goals
    refine WP.seq (wp_ite_eq (fun h => ?_) (fun h => ?_))
  all_goals first
    | exact absurd (h.symm.trans (z_sub _ _ _)) (by decide)
    | refine WP.mono (Q := fun u : State => Keep [.r0] s u ∧ u.mem = s.mem ∧
          u.gpr .r0 = BitVec.ofNat 32 (nextT _ _)) ?_ fun u ⟨a, b, c⟩ => tail u a b c
      crun
      exact ⟨⟨by keep_regs, rfl, rfl, rfl⟩, by decide⟩

/-! ## The round -/

/-- `f` of a round of type `t` with the subkeys `km`, `kr`, on `D = d`. -/
def fT (t : Nat) (km kr d : Spec.Cast5.Word) : Spec.Cast5.Word :=
  let i := (Proof.Cast5.mix t km d).rotateLeft (kr.toNat % 32)
  Proof.Cast5.comb t (Spec.Cast5.S1 (Spec.Cast5.byte i 0)) (Spec.Cast5.S2 (Spec.Cast5.byte i 1))
    (Spec.Cast5.S3 (Spec.Cast5.byte i 2)) (Spec.Cast5.S4 (Spec.Cast5.byte i 3))

/-- What a round needs: `(L, R)` in `(r2, r3)`; `Kmᵢ` at `lr` and `Krᵢ` at
`lr + 64`; the type `t` and the count `cnt` of rounds left in their slots;
the scan's slots writable; and the table `VG_CAST5_S1234`, readable and
apart from them. -/
structure RoundPre (s : State) (km kr l r : Spec.Cast5.Word) (t : Nat) (cnt : BitVec 32) : Prop where
  r2 : s.gpr .r2 = l
  r3 : s.gpr .r3 = r
  inM : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 4
  valM : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 0)) 32 = km
  inR : InRegions (s.rd ++ s.wr) (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 4
  valR : s.mem.readW (State.addr (s.gpr .lr + BitVec.ofNat 32 64)) 32 = kr
  ht : t = 1 ∨ t = 2 ∨ t = 3
  inT : InRegions s.wr (slot s 20) 4
  valT : s.mem.readW (slot s 20) 32 = BitVec.ofNat 32 t
  inC : InRegions s.wr (slot s 16) 4
  valC : s.mem.readW (slot s 16) 32 = cnt
  sep : Mem.Sep (slot s 16) 4 (slot s 20) 4
  cfit : (s.gpr .r12).toNat + 64 ≤ 2 ^ 32
  inS : ∀ {off w : Nat}, off + w ≤ 40 → InRegions s.wr (sbase s 24 + BitVec.ofNat 64 off) w
  tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (State.addr (s.syms s1234Sym)) Impl.Cast5.s1234
  dTS : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨sbase s 24, 40⟩

theorem RoundPre.inT' {s : State} {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) : InRegions (s.rd ++ s.wr) (slot s 20) 4 := by
  obtain ⟨g, hg, hc⟩ := h.inT; exact ⟨g, List.mem_append_right _ hg, hc⟩

/-- The registers a round writes before its Feistel step. -/
def preRegs : List Reg := [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

/-- The registers a round writes. -/
def roundRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .lr]

/-- The slots of the working space, as the scan addresses them. -/
theorem slot_addr {s : State} (hc : (s.gpr .r12).toNat + 64 ≤ 2 ^ 32) {off : Nat} (ho : off < 64) :
    slot s off = State.addr (s.gpr .r12) + BitVec.ofNat 64 off := addr_add (by omega_using [hc, ho])

/-- A slot below the scan's, in a memory that differs in the scan's words. -/
theorem frame_slot (s : State) {m m' : Mem} (hf : Frame [⟨sbase s 24, 40⟩] m m')
    (hc : (s.gpr .r12).toNat + 64 ≤ 2 ^ 32) {off : Nat} (ho : off + 4 ≤ 24) :
    m'.readW (slot s off) 32 = m.readW (slot s off) 32 := by
  rw [slot_addr hc (by omega_using [ho])]
  exact hf.readW (r := ⟨State.addr (s.gpr .r12) + BitVec.ofNat 64 off, 4⟩) (Region.contains_self _ _)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (.inl ho) (by omega_using [ho]) (by decide)) (by decide)

theorem round_ok (s : State) (up : Bool) {km kr l r : Spec.Cast5.Word} {t : Nat} {cnt : BitVec 32}
    (h : RoundPre s km kr l r t cnt) :
    WP isa (round up) s fun u =>
      u.gpr .r2 = r ∧ u.gpr .r3 = l ^^^ fT t km kr r ∧
      u.gpr .lr = (if up then s.gpr .lr + 4 else s.gpr .lr - 4) ∧
      (∃ m, Frame [⟨sbase s 24, 40⟩] s.mem m ∧
        u.mem = (m.writeW (slot s 20) (BitVec.ofNat 32 (nextT up t))).writeW (slot s 16) (cnt - 1)) ∧
      u.z = (cnt - 1 == 0) ∧ Keep roundRegs s u := by
  have ht := h.ht
  unfold round
  -- `I` before the rotation.
  refine WP.seq (VG.Arm.WP.mono_syms (byType_ok s Impl.Cast5.Arm.mix (Q := fun v => v.gpr .r1 = Proof.Cast5.mix t km r ∧
      Keep [.r0, .r1] s v ∧ v.mem = s.mem) ht h.inT' h.valT fun u uk um => ?_) fun v hv vsy => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = s.gpr q := uk.gpr q (by simpa using hq)
    exact WP.mono (mix_ok u ht (by rw [g _ (by decide)]; exact h.r3)
      (by rw [uk.rd, uk.wr, g _ (by decide)]; exact h.inM) (by rw [um, g _ (by decide)]; exact h.valM))
      fun v ⟨v1, vk, vm⟩ => ⟨v1, (uk.mono (by decide)).trans (vk.mono (by decide)), vm.trans um⟩
  obtain ⟨v1, vk, vm⟩ := hv
  have gv (q : Reg) (hq : q ∉ [Reg.r0, .r1]) : v.gpr q = s.gpr q := vk.gpr q hq
  -- The rotation, the indices and the scan.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine (VG.Arm.WP.mono_syms (rotate_ok v v1 (kr := kr) (by rw [vk.rd, vk.wr, gv _ (by decide)]; exact h.inR)
    (by rw [vm, gv _ (by decide)]; exact h.valR)) fun w ⟨w1, wk, wm⟩ wsy => ?_)
  obtain ⟨i, hi⟩ : ∃ i, (Proof.Cast5.mix t km r).rotateLeft (kr.toNat % 32) = i := ⟨_, rfl⟩
  rw [hi] at w1
  refine VG.Arm.WP.mono_syms (spread_ok w w1) fun x ⟨xi, xk, xm⟩ xsy => ?_
  have kx := (vk.mono (by decide)).trans ((wk.mono (by decide)).trans
    (xk.mono (show ∀ q ∈ [Reg.r4, .r5, .r6, .r7], q ∈ preRegs by decide)))
  have mx : x.mem = s.mem := xm.trans (wm.trans vm)
  have sx : x.syms = s.syms := xsy.trans (wsy.trans vsy)
  have r12x : x.gpr .r12 = s.gpr .r12 := kx.gpr _ (by decide)
  have sp : ScanPre s1234Sym spillEcb x :=
    { idx := fun k hk => by rw [xi k hk]; exact idx_lt i hk
      cfit := by rw [r12x]; have := h.cfit; unfold spillEcb; omega_using [this]
      ofit := by decide
      inS := fun hw => by rw [r12x, kx.wr]; exact h.inS hw
      tfit := by rw [sx]; exact h.tfit
      trd := by rw [sx, kx.rd, kx.wr]; exact h.trd
      dTS := by rw [sx, r12x]; exact h.dTS }
  refine WP.seq (WP.mono (scan_ok x s1234Sym spillEcb sp) fun y ⟨ya, yk, yf⟩ => ?_)
  have kxy := kx.trans (yk.mono (show ∀ r ∈ [Reg.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11], r ∈ preRegs by decide))
  rw [r12x, mx] at yf
  obtain yf : Frame [⟨sbase s 24, 40⟩] s.mem y.mem := yf
  have r12y : y.gpr .r12 = s.gpr .r12 := kxy.gpr _ (by decide)
  have esl (off : Nat) : slot y off = slot s off := by rw [r12y]
  have valT : y.mem.readW (slot y 20) 32 = BitVec.ofNat 32 t := by
    rw [esl, frame_slot s yf h.cfit (by decide)]; exact h.valT
  -- `f`.
  refine WP.seq (WP.mono (byType_ok y Impl.Cast5.Arm.comb (Q := fun z => z.gpr .r1 = fT t km kr r ∧
      Keep preRegs s z ∧ z.mem = y.mem) ht (by rw [kxy.rd, kxy.wr, r12y]; exact h.inT')
      valT fun u uk um => ?_) fun z hz => ?_)
  · have g (q : Reg) (hq : q ≠ .r0) : u.gpr q = y.gpr q := uk.gpr q (by simpa using hq)
    refine WP.mono (comb_ok u ht) fun z ⟨z1, zk, zm⟩ => ⟨?_, kxy.trans ((uk.mono (by decide)).trans
      (zk.mono (by decide))), zm.trans um⟩
    have hT := h.tfit
    have ent (k : Nat) (hk : k < 4) : y.gpr (accReg k) = tableEnt Spec.Cast5.S4 Spec.Cast5.S3 Spec.Cast5.S2
        Spec.Cast5.S1 (idx i k).toNat k := by
      rw [ya k hk, mx, xi k hk, sx]; exact tw_table hT h.held (idx_lt i hk) hk
    have a0 : y.gpr .r8 = _ := ent 0 (by decide)
    have a1 : y.gpr .r9 = _ := ent 1 (by decide)
    have a2 : y.gpr .r10 = _ := ent 2 (by decide)
    have a3 : y.gpr .r11 = _ := ent 3 (by decide)
    rw [z1, g _ (by decide), g _ (by decide), g _ (by decide), g _ (by decide), a0, a1, a2, a3]
    unfold fT
    rw [hi]
    simp only [tableEnt, idx_byte i (show 0 < 4 by decide), idx_byte i (show 1 < 4 by decide),
      idx_byte i (show 2 < 4 by decide), idx_byte i (show 3 < 4 by decide)]
  obtain ⟨z1, zk, zm⟩ := hz
  have gz (q : Reg) (hq : q ∉ preRegs) : z.gpr q = s.gpr q := zk.gpr q hq
  -- The Feistel step, then the type and the count.
  refine WP.seq (WP.mono (feistel_ok z up) fun a ⟨a2, a3, alr, ak, am⟩ => ?_)
  have ka := (zk.mono (show ∀ q ∈ preRegs, q ∈ roundRegs by decide)).trans
    (ak.mono (show ∀ q ∈ [Reg.r1, .r2, .r3, .lr], q ∈ roundRegs by decide))
  have r12a : a.gpr .r12 = s.gpr .r12 := ka.gpr _ (by decide)
  have es (off : Nat) : slot a off = slot s off := by rw [r12a]
  have ma : a.mem = y.mem := am.trans zm
  have hinT := h.inT
  have hinC := h.inC
  refine WP.mono (next_ok a up ht (cnt := cnt) (by rw [es, ka.wr]; exact h.inT)
    (by rw [es, ma, frame_slot s yf h.cfit (by decide)]; exact h.valT)
    (by rw [es, ka.wr]; exact h.inC) (by rw [es, ma, frame_slot s yf h.cfit (by decide)]; exact h.valC)
    (by rw [es, es]; exact h.sep))
    fun b ⟨bm, bz, bk⟩ => ?_
  have gb (q : Reg) (hq : q ≠ .r0) : b.gpr q = a.gpr q := bk.gpr q (by simpa using hq)
  refine ⟨by rw [gb _ (by decide), a2, gz _ (by decide), h.r3], ?_, ?_, ⟨y.mem, yf, by rw [bm, es, es, ma]⟩, bz,
    ka.trans (bk.mono (by decide))⟩
  · rw [gb _ (by decide), a3, z1, gz _ (by decide), h.r2, BitVec.xor_comm]
  · rw [gb _ (by decide), alr, gz _ (by decide)]

end VG.Proof.Cast5.Arm

end

end

/-! ### `Cast5.Arm.Block`, which this module and modules that import it used -/

section

/-!
# CAST5 on ARMv7: the block function

`crypt up` encrypts (`up`) or decrypts the block whose address is in the
data slot of the working space at `r12`, in place, with the schedule and the
number of rounds in their slots (`crypt_ok`). Besides the block it writes
only the slots of the count and type of rounds (`cntOff`, `typeOff`) and the
scan's ten words after them, and it keeps `r12`: this is the block function
a mode reuses.
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym)
open VG.Proof.Cast5 (encFold decFold encFold_succ decFold_succ encryptBlock_eq decryptBlock_eq f_eq roundI)

/-- `fT` of the type of round `i` is the spec's `f`. -/
theorem fT_eq {t i : Nat} (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (km kr d : Spec.Cast5.Word) :
    fT t km kr d = Spec.Cast5.f i d km kr := by
  rw [f_eq]
  unfold fT roundI
  rcases ht with rfl | rfl | rfl <;> rw [← hti] <;> rfl

theorem rev_eq (x : BitVec 32) : rev x = byteRev32 x := rfl

/-- The block's cipher. -/
def cipher (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) : Spec.Cast5.Block → Spec.Cast5.Block :=
  if up then Spec.Cast5.encryptBlock k n else Spec.Cast5.decryptBlock k n

/-- The slots of the count and type of rounds, and the scan's ten words. -/
abbrev ctRegion (c : BitVec 32) : Region := ⟨State.addr c + BitVec.ofNat 64 16, 48⟩

/-- What the block function needs: the working space at `c` in `r12`, the
block at `p` (in the data slot), the schedule at `kb` (in its slot) and the
number of rounds `n` (in its slot); and the table `VG_CAST5_S1234`, readable
and apart from the working space. -/
structure BPre (s : State) (c p kb : BitVec 32) (n : Nat) : Prop where
  r12 : s.gpr .r12 = c
  cfit : c.toNat + 256 ≤ 2 ^ 32
  pfit : p.toNat + 8 ≤ 2 ^ 32
  kfit : kb.toNat + 128 ≤ 2 ^ 32
  scr : (⟨State.addr c, 256⟩ : Region) ∈ s.wr
  blk : ∀ {off w : Nat}, off + w ≤ 8 → InRegions s.wr (State.addr p + BitVec.ofNat 64 off) w
  sch : (⟨State.addr kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  dPS : Region.Disjoint ⟨State.addr p, 8⟩ ⟨State.addr c, 256⟩
  dKS : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr c, 256⟩
  dKP : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr p, 8⟩
  data : s.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = p
  sched : s.mem.readW (State.addr c + BitVec.ofNat 64 8) 32 = kb
  rounds : s.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 = BitVec.ofNat 32 n
  nv : n = 12 ∨ n = 16
  tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  held : Held s.mem (State.addr (s.syms s1234Sym)) Impl.Cast5.s1234
  dTS : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨State.addr c, 256⟩

section
variable {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
include h

theorem BPre.inS {off w : Nat} (hw : off + w ≤ 256) : InRegions s.wr (State.addr c + BitVec.ofNat 64 off) w :=
  ⟨_, h.scr, Offset.contains_base _ hw (by omega_arith)⟩

theorem BPre.inS' {off w : Nat} (hw : off + w ≤ 256) :
    InRegions (s.rd ++ s.wr) (State.addr c + BitVec.ofNat 64 off) w :=
  ⟨_, List.mem_append_right _ h.scr, Offset.contains_base _ hw (by omega_arith)⟩

theorem BPre.inP {off w : Nat} (hw : off + w ≤ 8) : InRegions s.wr (State.addr p + BitVec.ofNat 64 off) w :=
  h.blk hw

theorem BPre.inP' {off w : Nat} (hw : off + w ≤ 8) :
    InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 off) w := by
  obtain ⟨g, hg, hc⟩ := h.blk hw; exact ⟨g, List.mem_append_right _ hg, hc⟩

theorem BPre.inK {off w : Nat} (hw : off + w ≤ 128) :
    InRegions (s.rd ++ s.wr) (State.addr kb + BitVec.ofNat 64 off) w :=
  ⟨_, h.sch, Offset.contains_base _ hw (by omega_arith)⟩

theorem BPre.aS : ∀ off, off < 256 → State.addr (c + BitVec.ofNat 32 off) = State.addr c + BitVec.ofNat 64 off :=
  addr_off h.cfit

theorem BPre.aP : ∀ off, off < 8 → State.addr (p + BitVec.ofNat 32 off) = State.addr p + BitVec.ofNat 64 off :=
  addr_off h.pfit

end

/-! ## The rounds -/

/-- The state of a block's rounds, from `s`: the halves `lr`, the next
round's subkeys at `kp`, its type `t` and `left` rounds left. -/
structure RInv (s : State) (c : BitVec 32) (lr : Spec.Cast5.Word × Spec.Cast5.Word) (kp : BitVec 32) (t left : Nat)
    (u : State) : Prop where
  r2 : u.gpr .r2 = lr.1
  r3 : u.gpr .r3 = lr.2
  lr : u.gpr .lr = kp
  r12 : u.gpr .r12 = c
  fr : Frame [ctRegion c] s.mem u.mem
  cnt : u.mem.readW (State.addr c + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 left
  typ : u.mem.readW (State.addr c + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 t
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  syms : u.syms = s.syms

theorem RInv_iff {s : State} {c : BitVec 32} {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : BitVec 32}
    {t left : Nat} {u : State} : RInv s c lr kp t left u ↔
      (u.gpr .r2 = lr.1 ∧ u.gpr .r3 = lr.2 ∧ u.gpr .lr = kp ∧ u.gpr .r12 = c ∧ Frame [ctRegion c] s.mem u.mem ∧
        u.mem.readW (State.addr c + BitVec.ofNat 64 16) 32 = BitVec.ofNat 32 left ∧
        u.mem.readW (State.addr c + BitVec.ofNat 64 20) 32 = BitVec.ofNat 32 t ∧
        u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧ u.syms = s.syms) :=
  ⟨fun h => ⟨h.r2, h.r3, h.lr, h.r12, h.fr, h.cnt, h.typ, h.rd, h.wr, h.sp, h.syms⟩,
   fun ⟨a, b, c, d, e, f, g, i, j, k, l⟩ => ⟨a, b, c, d, e, f, g, i, j, k, l⟩⟩

/-- The subkeys of round `i` (`1 … 16`) at `kp`, read through a frame. -/
theorem key_at {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
    (hf : Frame [ctRegion c] s.mem u.mem) {i : Nat} (hi : 1 ≤ i ∧ i ≤ 16) {j : Nat} (hj : j = i - 1 ∨ j = 15 + i) :
    u.mem.readW (State.addr kb + BitVec.ofNat 64 (4 * j)) 32 =
      (Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD j 0 := by
  rw [Proof.Cast5.scheduleAt_getD _ _ (by omega_arith)]
  refine hf.readW (r := ⟨State.addr kb, 128⟩) (Offset.contains_base _ (by omega_arith) (by omega_arith)) ?_ (by decide)
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h.dKS.sub_right (Offset.sub_base _ (by decide))

theorem kp_addr {kb : BitVec 32} (hk : kb.toNat + 128 ≤ 2 ^ 32) {j : Nat} (off : Nat)
    (hjo : 4 * j + off + 4 ≤ 128) :
    State.addr (kb + BitVec.ofNat 32 (4 * j) + BitVec.ofNat 32 off) =
      State.addr kb + BitVec.ofNat 64 (4 * j + off) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact addr_add (by omega_arith)

/-- A round, from the state of the rounds. -/
theorem round_step {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) {lr : Spec.Cast5.Word × Spec.Cast5.Word}
    {t left i : Nat} (hu : RInv s c lr (kb + BitVec.ofNat 32 (4 * (i - 1))) t left u) (up : Bool)
    (ht : t = 1 ∨ t = 2 ∨ t = 3) (hti : t % 3 = i % 3) (hi : 1 ≤ i ∧ i ≤ 16) (hl : 1 ≤ left ∧ left < 2 ^ 32) :
    WP isa (round up) u fun v =>
      RInv s c (Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem (State.addr kb)) i lr)
        (if up then kb + BitVec.ofNat 32 (4 * (i - 1)) + 4 else kb + BitVec.ofNat 32 (4 * (i - 1)) - 4)
        (nextT up t) (left - 1) v ∧ v.z = (BitVec.ofNat 32 left - 1 == 0) := by
  have aS := h.aS
  have e0 : State.addr (u.gpr .lr + BitVec.ofNat 32 0) = State.addr kb + BitVec.ofNat 64 (4 * (i - 1)) := by
    rw [hu.lr, kp_addr h.kfit 0 (by omega_arith), Nat.add_zero]
  have e64 : State.addr (u.gpr .lr + BitVec.ofNat 32 64) = State.addr kb + BitVec.ofNat 64 (4 * (15 + i)) := by
    rw [hu.lr, kp_addr h.kfit 64 (by omega_arith)]; congr 2; omega_arith
  have es (off : Nat) (ho : off < 256) : slot u off = State.addr c + BitVec.ofNat 64 off := by
    rw [hu.r12, aS off ho]
  have pre : RoundPre u ((Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD (i - 1) 0)
      ((Spec.Cast5.scheduleAt s.mem (State.addr kb)).getD (15 + i) 0) lr.1 lr.2 t (BitVec.ofNat 32 left) :=
    { r2 := hu.r2
      r3 := hu.r3
      inM := by rw [e0, hu.rd, hu.wr]; exact h.inK (by omega_arith)
      valM := by rw [e0]; exact key_at h hu.fr hi (.inl rfl)
      inR := by rw [e64, hu.rd, hu.wr]; exact h.inK (by omega_arith)
      valR := by rw [e64]; exact key_at h hu.fr hi (.inr rfl)
      ht := ht
      inT := by rw [es 20 (by decide), hu.wr]; exact h.inS (by decide)
      valT := by rw [es 20 (by decide)]; exact hu.typ
      inC := by rw [es 16 (by decide), hu.wr]; exact h.inS (by decide)
      valC := by rw [es 16 (by decide)]; exact hu.cnt
      sep := by rw [es 16 (by decide), es 20 (by decide)]; exact Offset.sep _ (by decide) (by decide) (by decide)
      cfit := by rw [hu.r12]; have := h.cfit; omega_arith
      inS := fun {off w} hw => by
        rw [hu.r12, hu.wr, Offset.add_add]; exact h.inS (by omega_using [hw])
      tfit := by rw [hu.syms]; exact h.tfit
      trd := by rw [hu.syms, hu.rd, hu.wr]; exact h.trd
      held := by
        rw [hu.syms]
        refine held_frame hu.fr (fun r hr => ?_) (by rw [Impl.Cast5.s1234, table_length]; decide) h.held
        simp only [List.mem_singleton] at hr; subst hr
        rw [Impl.Cast5.s1234, table_length]
        exact h.dTS.sub_right (Offset.sub_base _ (by decide))
      dTS := by rw [hu.syms, hu.r12]; exact h.dTS.sub_right (Offset.sub_base _ (by decide)) }
  refine VG.Arm.WP.mono_syms (round_ok u up pre) fun v ⟨v2, v3, vlr, ⟨m₁, f₁, vm⟩, vz, vk⟩ vsy => ⟨⟨v2, ?_, ?_, ?_, ?_, ?_, ?_,
    vk.rd.trans hu.rd, vk.wr.trans hu.wr, vk.sp.trans hu.sp, vsy.trans hu.syms⟩, vz⟩
  · rw [v3, fT_eq ht hti]; rfl
  · rw [vlr, hu.lr]
  · rw [vk.gpr _ (by decide), hu.r12]
  · rw [vm, es 16 (by decide), es 20 (by decide)]
    rw [hu.r12] at f₁
    exact ((hu.fr.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, Offset.sub _ (by decide) (by decide)⟩)).writeW
      List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))
  · rw [vm, es 16 (by decide), es 20 (by decide), Mem.readW_writeW_self32]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
    omega_arith
  · rw [vm, es 16 (by decide), es 20 (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

/-- The rounds loop, for any order of the rounds: round `idx i` is the
`i`-th, with its subkeys at `kpf i` and its type `tf i`, and the halves
before it `fold i`. -/
theorem rounds_ok {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) (up : Bool)
    (idx : Nat → Nat) (kpf : Nat → BitVec 32) (tf : Nat → Nat) (fold : Nat → Spec.Cast5.Word × Spec.Cast5.Word)
    (hidx : ∀ i < n, 1 ≤ idx i ∧ idx i ≤ 16) (hkp : ∀ i < n, kpf i = kb + BitVec.ofNat 32 (4 * (idx i - 1)))
    (ht : ∀ i < n, tf i = 1 ∨ tf i = 2 ∨ tf i = 3) (hti : ∀ i < n, tf i % 3 = idx i % 3)
    (hfold : ∀ i < n, fold (i + 1) = Spec.Cast5.round (Spec.Cast5.scheduleAt s.mem (State.addr kb)) (idx i) (fold i))
    (hnext : ∀ i, i + 1 < n → kpf (i + 1) = (if up then kpf i + 4 else kpf i - 4) ∧ tf (i + 1) = nextT up (tf i))
    (h0 : RInv s c (fold 0) (kpf 0) (tf 0) n u) :
    WP isa (.loop (round up) .ne) u fun v => ∃ kp t, RInv s c (fold n) kp t 0 v := by
  have hn : n = 12 ∨ n = 16 := h.nv
  refine WP.loop (M := isa) (fun m (v : State) => ∃ i, m = n - i ∧ i < n ∧ RInv s c (fold i) (kpf i) (tf i) (n - i) v)
    ?_ n u ⟨0, rfl, by omega_arith, by rw [Nat.sub_zero]; exact h0⟩
  rintro m v ⟨i, rfl, hi, hv⟩
  rw [hkp i hi] at hv
  refine WP.mono (round_step h hv up (ht i hi) (hti i hi) (hidx i hi) (by omega_arith)) fun w ⟨hw, wz⟩ => ?_
  rw [← hfold i hi, ← hkp i hi] at hw
  by_cases hlast : i + 1 = n
  · refine .inl ⟨?_, _, _, by rw [hlast] at hw; rw [show n - i - 1 = 0 by omega_arith] at hw; exact hw⟩
    show some (!w.z) = _; rw [wz]
    congr 1
    rw [show n - i = 1 by omega_arith]
    rfl
  · obtain ⟨hk, htn⟩ := hnext i (by omega_arith)
    refine .inr ⟨?_, n - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ?_⟩
    · show some (!w.z) = _; rw [wz]
      congr 1
      have : BitVec.ofNat 32 (n - i) - 1 ≠ 0 := by
        intro e
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
          show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      simpa using this
    · rw [hk, htn, show n - (i + 1) = n - i - 1 by omega_arith]
      exact hw

theorem nextT_up (i : Nat) : nextT true (i % 3 + 1) = (i + 1) % 3 + 1 := by
  simp only [nextT, ite_true]
  split <;> omega_arith

/-! ## The block function -/

/-- Storing the word read: nothing changes. -/
theorem writeW_readW (m : Mem) (a : Addr) : m.writeW a (m.readW a 32) = m := by
  funext x
  simp only [Mem.writeW, Mem.write, BitVec.setWidth_eq, show 32 / 8 = 4 from rfl]
  split
  · rename_i h
    rw [← Mem.readW_byte m a h, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rfl


/-- The memory after the start of a block: the count and type of rounds. -/
theorem start_frame {m : Mem} {c : BitVec 32} (x y : BitVec 32) :
    Frame [ctRegion c] m ((m.writeW (State.addr c + BitVec.ofNat 64 16) x).writeW
      (State.addr c + BitVec.ofNat 64 20) y) :=
  ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains _ (by decide) (by decide) (by decide))

theorem start_cnt (m : Mem) (c x y : BitVec 32) :
    ((m.writeW (State.addr c + BitVec.ofNat 64 16) x).writeW (State.addr c + BitVec.ofNat 64 20) y).readW
      (State.addr c + BitVec.ofNat 64 16) 32 = x := by
  rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]

theorem start_typ (m : Mem) (c x y : BitVec 32) :
    ((m.writeW (State.addr c + BitVec.ofNat 64 16) x).writeW (State.addr c + BitVec.ofNat 64 20) y).readW
      (State.addr c + BitVec.ofNat 64 20) 32 = y := Mem.readW_writeW_self32 _ _ _

theorem decode_start (s : State) (p : BitVec 32) :
    (byteRev32 (s.mem.readW (State.addr p + BitVec.ofNat 64 0) 32),
      byteRev32 (s.mem.readW (State.addr p + BitVec.ofNat 64 4) 32)) =
      Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (State.addr p)) := by
  rw [Proof.Cast5.decodeBlock_blockAt, BitVec.add_zero]

theorem startEnc_ok {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) :
    WP isa (.block startEnc) s (RInv s c (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (State.addr p)))
      (kb + BitVec.ofNat 32 (4 * 0)) (0 % 3 + 1) n) := by
  have aS := h.aS
  have aP := h.aP
  have inS := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS (off := off) (w := w) hw
  have inS' := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS' (off := off) (w := w) hw
  have inP' := fun {off w : Nat} (hw : off + w ≤ 8) => h.inP' (off := off) (w := w) hw
  unfold startEnc
  crun [dataOff, schedOff, roundsOff, cntOff, typeOff, h.r12, aS, aP, inS, inS', inP', h.data, h.sched,
    h.rounds, rev_eq, RInv_iff, syms_setReg, syms_mem]
  exact ⟨by rw [← decode_start s p], by rw [← decode_start s p], by bv_omega, start_frame _ _, start_cnt _ _ _ _,
    start_typ _ _ _ _⟩

theorem startDec_ok {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) :
    WP isa (.block startDec) s (RInv s c (Spec.Cast5.decodeBlock (Spec.Cast5.blockAt s.mem (State.addr p)))
      (kb + BitVec.ofNat 32 (4 * (n - 1 - 0))) ((n - 1 - 0) % 3 + 1) n) := by
  have aS := h.aS
  have aP := h.aP
  have inS := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS (off := off) (w := w) hw
  have inS' := fun {off w : Nat} (hw : off + w ≤ 256) => h.inS' (off := off) (w := w) hw
  have inP' := fun {off w : Nat} (hw : off + w ≤ 8) => h.inP' (off := off) (w := w) hw
  unfold startDec
  crun [dataOff, schedOff, roundsOff, cntOff, typeOff, h.r12, aS, aP, inS, inS', inP', h.data, h.sched,
    h.rounds, rev_eq, RInv_iff, syms_setReg, syms_mem]
  refine ⟨by rw [← decode_start s p], by rw [← decode_start s p], ?_, start_frame _ _, start_cnt _ _ _ _, ?_⟩
  · rcases h.nv with rfl | rfl <;> bv_omega
  · rw [start_typ]
    rcases h.nv with rfl | rfl <;> rfl

/-- What the block function does. -/
def BPost (s : State) (c p : BitVec 32) (out : Spec.Cast5.Block) (t : State) : Prop :=
  Spec.Cast5.blockAt t.mem (State.addr p) = out ∧
  Frame [⟨State.addr p, 8⟩, ctRegion c] s.mem t.mem ∧ t.gpr .r12 = c ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp

theorem finish_ok {s u : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n)
    {lr : Spec.Cast5.Word × Spec.Cast5.Word} {kp : BitVec 32} {t : Nat} (hu : RInv s c lr kp t 0 u) :
    WP isa (.block finish) u (BPost s c p (Spec.Cast5.encodeBlock (lr.2, lr.1))) := by
  have aS := h.aS
  have aP := h.aP
  have sl (off : Nat) (ho : off + 4 ≤ 16) :
      u.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 = s.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 :=
    hu.fr.readW (r := ⟨State.addr c + BitVec.ofNat 64 off, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)) (by decide)
  have hd : u.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = p := (sl 0 (by decide)).trans h.data
  have inS' : ∀ {off w : Nat}, off + w ≤ 256 → InRegions (u.rd ++ u.wr) (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by rw [hu.rd, hu.wr]; exact h.inS' hw
  have inS : ∀ {off w : Nat}, off + w ≤ 256 → InRegions u.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by rw [hu.wr]; exact h.inS hw
  have inP0 : InRegions u.wr (State.addr p + BitVec.ofNat 64 0) 4 := by rw [hu.wr]; exact h.inP (by decide)
  have inP4 : InRegions u.wr (State.addr p + BitVec.ofNat 64 4) 4 := by rw [hu.wr]; exact h.inP (by decide)
  -- The block's stores leave the slots alone.
  obtain ⟨m', hm'⟩ : ∃ m', (u.mem.writeW (State.addr p + BitVec.ofNat 64 0) (byteRev32 lr.2)).writeW
      (State.addr p + BitVec.ofNat 64 4) (byteRev32 lr.1) = m' := ⟨_, rfl⟩
  have ms (off : Nat) (ho : off + 4 ≤ 16) :
      m'.readW (State.addr c + BitVec.ofNat 64 off) 32 = u.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 := by
    have dPC : Region.Disjoint ⟨State.addr p, 8⟩ ⟨State.addr c + BitVec.ofNat 64 off, 4⟩ :=
      h.dPS.sub_right (Offset.sub_base _ (by omega_arith))
    rw [← hm', Mem.readW_writeW_sep (dPC.symm.sep (Region.contains_self _ _)
        (Offset.contains_base _ (by decide) (by decide))) (by decide),
      Mem.readW_writeW_sep (dPC.symm.sep (Region.contains_self _ _)
        (Offset.contains_base _ (by decide) (by decide))) (by decide)]
  unfold finish
  crun [dataOff, nOff, schedOff, roundsOff, hu.r12, aS, aP, inS, inS', inP0, inP4, hd, hu.r2, hu.r3, rev_eq, hm']
  have e : (((m'.writeW (State.addr c + BitVec.ofNat 64 0) p).writeW (State.addr c + BitVec.ofNat 64 4)
      (u.mem.readW (State.addr c + BitVec.ofNat 64 4) 32)).writeW (State.addr c + BitVec.ofNat 64 8)
      (u.mem.readW (State.addr c + BitVec.ofNat 64 8) 32)).writeW (State.addr c + BitVec.ofNat 64 12)
      (u.mem.readW (State.addr c + BitVec.ofNat 64 12) 32) = m' := by
    rw [← ms 4 (by decide), ← ms 8 (by decide), ← ms 12 (by decide),
      show p = m'.readW (State.addr c + BitVec.ofNat 64 0) 32 from ((ms 0 (by decide)).trans hd).symm,
      writeW_readW, writeW_readW, writeW_readW, writeW_readW]
  rw [e]
  refine ⟨?_, ?_, by simp only [gpr_setReg, reduceCtorEq, ite_false, hu.r12], hu.rd, hu.wr, hu.sp⟩
  · show Spec.Cast5.blockAt m' _ = _
    rw [← hm', BitVec.add_zero, Proof.Cast5.blockAt_write]
  · show Frame _ s.mem m'
    rw [← hm']
    have f1 := (hu.fr.mono (rs' := [⟨State.addr p, 8⟩, ctRegion c]) (by simp)).writeW List.mem_cons_self
      (byteRev32 lr.2) (Offset.contains_base (State.addr p) (d := 0) (n := 4) (k := 8) (by decide) (by decide))
    exact f1.writeW List.mem_cons_self (byteRev32 lr.1)
      (Offset.contains_base (State.addr p) (d := 4) (n := 4) (k := 8) (by decide) (by decide))

theorem crypt_ok {s : State} {c p kb : BitVec 32} {n : Nat} (h : BPre s c p kb n) (up : Bool) :
    WP isa (crypt up) s (BPost s c p (cipher up (Spec.Cast5.scheduleAt s.mem (State.addr kb)) n
      (Spec.Cast5.blockAt s.mem (State.addr p)))) := by
  have hn := h.nv
  cases up
  · unfold crypt
    simp only [Bool.false_eq_true, ite_false]
    refine WP.seq (WP.mono (startDec_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h false (fun i => n - i) (fun i => kb + BitVec.ofNat 32 (4 * (n - 1 - i)))
      (fun i => (n - 1 - i) % 3 + 1) (fun i => decFold _ n i _) (fun i hi => by omega_arith)
      (fun i hi => by congr 2; omega_arith) (fun i hi => by omega_arith) (fun i hi => by omega_arith)
      (fun i hi => decFold_succ _ _ _ _) (fun i hi => ⟨?_, ?_⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [Bool.false_eq_true, ite_false]
      rw [show n - 1 - i = n - 1 - (i + 1) + 1 by omega_arith, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact (BitVec.add_sub_cancel _ _).symm
    · rw [show n - 1 - i = n - 1 - (i + 1) + 1 by omega_arith]
      simp only [nextT, Bool.false_eq_true, ite_false]
      split <;> omega_arith
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_right Bool.false_ne_true, decryptBlock_eq]
    exact hw
  · unfold crypt
    simp only [ite_true]
    refine WP.seq (WP.mono (startEnc_ok h) fun u hu => ?_)
    refine WP.seq (WP.mono (rounds_ok h true (fun i => i + 1) (fun i => kb + BitVec.ofNat 32 (4 * i))
      (fun i => i % 3 + 1) (fun i => encFold _ i _) (fun i hi => by omega_arith)
      (fun i hi => by rw [Nat.add_sub_cancel]) (fun i hi => by omega_arith) (fun i hi => by omega_arith)
      (fun i hi => encFold_succ _ _ _) (fun i hi => ⟨?_, (nextT_up i).symm⟩) hu) fun v ⟨kp, t, hv⟩ => ?_)
    · simp only [ite_true]
      rw [Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    refine WP.mono (finish_ok h hv) fun w hw => ?_
    rw [cipher, ite_eq_left rfl, encryptBlock_eq]
    exact hw

end VG.Proof.Cast5.Arm

end

end

/-!
# CAST5 on ARMv7: ECB

`ecb up` takes the working space from the stack, saves the callee-saved
registers in it, keeps its arguments in their slots, runs the block function
on each block in turn (`ecbLoop_ok`) and restores the registers
(`ecb_correct`).
-/

@[expose] public section

namespace VG.Proof.Cast5.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Cast5.Arm
open VG.Impl.Cast5 (s1234Sym s1234 ecbConsts)

/-! ## Frames of the layouts -/

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {Q : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨Q, 8⟩ r) : Spec.Cast5.blockAt m' Q = Spec.Cast5.blockAt m Q := by
  apply Vector.ext
  intro j hj
  rw [Proof.Cast5.blockAt_get _ _ hj, Proof.Cast5.blockAt_get _ _ hj]
  exact hf.bytes (R := ⟨Q, 8⟩) hd (by show (8 : Nat) ≤ 2 ^ 64; decide) hj

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨K, 128⟩ r) : Spec.Cast5.scheduleAt m' K = Spec.Cast5.scheduleAt m K := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Cast5.scheduleAt, Vector.getElem_ofFn]
  rw [hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 3 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 2 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i + 1 < 128 by omega_arith),
    hf.bytes (R := ⟨K, 128⟩) hd (by show (128 : Nat) ≤ 2 ^ 64; decide) (show 4 * i < 128 by omega_arith)]

/-! ## The saved registers -/

def savedSlots : List (Reg × Nat) := saved.zipIdx.map fun (r, i) => (r, savedOff + 4 * i)

theorem save_eq : save = savedSlots.map fun p => Instr.str p.1 .r12 p.2 := rfl
theorem restore_eq : restore = savedSlots.map fun p => Instr.ldr p.1 .r12 p.2 := rfl
theorem savedSlots_ok : Spill.Slots 64 100 savedSlots := by decide
theorem savedSlots_restorable : Spill.Restorable .r12 savedSlots := by decide
theorem savedSlots_preserved : ∀ r ∈ preserved, r ∈ savedSlots.map Prod.fst := by decide
/-! ## The loop over the blocks -/

/-- The state of ECB with `j` of the `N` blocks at `d` done, from the memory
`m0` after the setup: the slots, the blocks, and nothing else written but the
data and the first 64 bytes of the working space at `c`; the table
`VG_CAST5_S1234` still held. -/
structure LInv (s : State) (m0 : Mem) (up : Bool) (k : Spec.Cast5.Schedule) (c d kb : BitVec 32) (n N j : Nat)
    (u : State) : Prop where
  r12 : u.gpr .r12 = c
  fr : Frame [⟨State.addr d, 8 * N⟩, ⟨State.addr c, 64⟩] m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (State.addr d + BitVec.ofNat 64 (8 * i)) =
    if i < j then cipher up k n (Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i)))
    else Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i))
  dslot : u.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = d + BitVec.ofNat 32 (8 * j)
  nslot : u.mem.readW (State.addr c + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 (N - j)
  sslot : u.mem.readW (State.addr c + BitVec.ofNat 64 8) 32 = kb
  rslot : u.mem.readW (State.addr c + BitVec.ofNat 64 12) 32 = BitVec.ofNat 32 n
  sk : Spec.Cast5.scheduleAt u.mem (State.addr kb) = k
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  sp : u.sp = s.sp
  syms : u.syms = s.syms
  held : Held u.mem (State.addr (s.syms s1234Sym)) s1234

/-- What the loop needs of the layout: the schedule at `kb`, the `N` blocks at
`d` and the working space at `c`, separate and within the address space;
the table `VG_CAST5_S1234`, readable, within the address space and apart
from the blocks and the working space. -/
structure Lay (s : State) (c d kb : BitVec 32) (n N : Nat) : Prop where
  cfit : c.toNat + 256 ≤ 2 ^ 32
  dfit : d.toNat + 8 * N ≤ 2 ^ 32
  kfit : kb.toNat + 128 ≤ 2 ^ 32
  scr : (⟨State.addr c, 256⟩ : Region) ∈ s.wr
  dat : (⟨State.addr d, 8 * N⟩ : Region) ∈ s.wr
  sch : (⟨State.addr kb, 128⟩ : Region) ∈ s.rd ++ s.wr
  dDS : Region.Disjoint ⟨State.addr d, 8 * N⟩ ⟨State.addr c, 256⟩
  dKS : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr c, 256⟩
  dKD : Region.Disjoint ⟨State.addr kb, 128⟩ ⟨State.addr d, 8 * N⟩
  nv : n = 12 ∨ n = 16
  tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32
  trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd ++ s.wr
  dTD : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨State.addr d, 8 * N⟩
  dTS : Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ ⟨State.addr c, 256⟩

theorem addr_blk {d : BitVec 32} {N j : Nat} (hd : d.toNat + 8 * N ≤ 2 ^ 32) (hj : j < N) :
    State.addr (d + BitVec.ofNat 32 (8 * j)) = State.addr d + BitVec.ofNat 64 (8 * j) := addr_add (by omega_arith)

theorem sub_blk (D : Addr) {N j : Nat} (hj : j < N) :
    Region.Sub ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ ⟨D, 8 * N⟩ := Offset.sub_base _ (by omega_arith)

theorem sub_c64 (C : Addr) : Region.Sub ⟨C, 64⟩ ⟨C, 256⟩ := fun x hx => by
  simp only [Region.Contains] at hx ⊢; omega_arith

theorem sub_ct256 (C : Addr) : Region.Sub ⟨C + BitVec.ofNat 64 16, 48⟩ ⟨C, 256⟩ := Offset.sub_base _ (by decide)

theorem sub_ct (C : Addr) : Region.Sub ⟨C + BitVec.ofNat 64 16, 48⟩ ⟨C, 64⟩ := Offset.sub_base _ (by decide)

theorem s1234_len : 8 * s1234.length = 4096 := by rw [s1234, table_length]

/-- The block function's precondition, at block `j`. -/
theorem LInv.bpre {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N j : Nat}
    (hl : Lay s c d kb n N) (h : LInv s m0 up k c d kb n N j u) (hj : j < N) :
    BPre u c (d + BitVec.ofNat 32 (8 * j)) kb n where
  r12 := h.r12
  cfit := hl.cfit
  pfit := by
    have := hl.dfit
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  kfit := hl.kfit
  scr := by rw [h.wr]; exact hl.scr
  blk := fun {off w} hw => by
    have := hl.dfit
    rw [addr_blk hl.dfit hj, Proof.Cast5.add_ofNat_add, h.wr]
    exact ⟨_, hl.dat, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  sch := by rw [h.rd, h.wr]; exact hl.sch
  dPS := by rw [addr_blk hl.dfit hj]; exact hl.dDS.sub_left (sub_blk _ hj)
  dKS := hl.dKS
  dKP := by rw [addr_blk hl.dfit hj]; exact hl.dKD.sub_right (sub_blk _ hj)
  data := h.dslot
  sched := h.sslot
  rounds := h.rslot
  nv := hl.nv
  tfit := by rw [h.syms]; exact hl.tfit
  trd := by rw [h.syms, h.rd, h.wr]; exact hl.trd
  held := by rw [h.syms]; exact h.held
  dTS := by rw [h.syms]; exact hl.dTS

theorem ofNat_sub_one {a : Nat} (ha : 1 ≤ a) (hb : a < 2 ^ 32) :
    BitVec.ofNat 32 a - 1 = BitVec.ofNat 32 (a - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega_arith

/-- `advance`: on to the next block. -/
theorem advance_ok (v : State) {c : BitVec 32} (hc : v.gpr .r12 = c) (hcf : c.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions v.wr (State.addr c + BitVec.ofNat 64 off) w) {x y : BitVec 32}
    (hx : v.mem.readW (State.addr c + BitVec.ofNat 64 0) 32 = x)
    (hy : (v.mem.writeW (State.addr c + BitVec.ofNat 64 0) (x + 8)).readW (State.addr c + BitVec.ofNat 64 4) 32 = y) :
    WP isa (.block advance) v fun w =>
      w.mem = (v.mem.writeW (State.addr c + BitVec.ofNat 64 0) (x + 8)).writeW (State.addr c + BitVec.ofNat 64 4) (y - 1) ∧
      w.z = (y - 1 == 0) ∧ w.gpr .r12 = c ∧ w.rd = v.rd ∧ w.wr = v.wr ∧ w.sp = v.sp := by
  obtain aS := addr_off hcf
  obtain hin' : ∀ {off w : Nat}, off + w ≤ 256 → InRegions (v.rd ++ v.wr) (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by obtain ⟨g, hg, hcg⟩ := hin hw; exact ⟨g, List.mem_append_right _ hg, hcg⟩
  unfold advance
  crun [dataOff, nOff, hc, aS, hin, hin', hx, hy]

/-- A block and another, or the working space. -/
theorem blk_disj_blk (D : Addr) {N i j : Nat} (hi : i < N) (hj : j < N) (hN : 8 * N ≤ 2 ^ 32) (hij : i ≠ j) :
    Region.Disjoint ⟨D + BitVec.ofNat 64 (8 * i), 8⟩ ⟨D + BitVec.ofNat 64 (8 * j), 8⟩ :=
  Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)

/-- One block, then on to the next. -/
theorem step_ok {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N j : Nat}
    (hl : Lay s c d kb n N) (h : LInv s m0 up k c d kb n N j u) (hj : j < N) :
    WP isa (.seq (crypt up) (.block advance)) u fun w => LInv s m0 up k c d kb n N (j + 1) w ∧
      w.z = decide (j + 1 = N) := by
  have hcf := hl.cfit
  have hdf := hl.dfit
  obtain eP := addr_blk hdf hj
  refine WP.seq (VG.Arm.WP.mono_syms (crypt_ok (h.bpre hl hj) up) fun v ⟨vb, vf, v12, vrd, vwr, vsp⟩ vsy => ?_)
  rw [eP] at vb vf
  -- The regions the block function wrote, against the slots and the other blocks.
  have dCt (off : Nat) (ho : off + 4 ≤ 16) : ∀ r ∈ [(⟨State.addr d + BitVec.ofNat 64 (8 * j), 8⟩ : Region), ctRegion c],
      Region.Disjoint ⟨State.addr c + BitVec.ofNat 64 off, 4⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hl.dDS.sub_left (sub_blk _ hj)).symm.sub_left (Offset.sub_base _ (by omega_arith))
    · exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by decide)
  have vslot (off : Nat) (ho : off + 4 ≤ 16) :
      v.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 = u.mem.readW (State.addr c + BitVec.ofNat 64 off) 32 :=
    vf.readW (Region.contains_self _ _) (dCt off ho) (by decide)
  obtain hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions v.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => by rw [vwr, h.wr]; exact ⟨_, hl.scr, Offset.contains_base _ hw (by omega_arith)⟩
  refine VG.Arm.WP.mono_syms (advance_ok v v12 hcf hin (x := d + BitVec.ofNat 32 (8 * j)) (y := BitVec.ofNat 32 (N - j))
    (by rw [vslot 0 (by decide)]; exact h.dslot)
    (by rw [Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      vslot 4 (by decide)]; exact h.nslot)) fun w ⟨wm, wz, w12, wrd, wwr, wsp⟩ wsy => ?_
  -- The writes of `advance`.
  obtain fw : Frame [⟨State.addr c, 64⟩] v.mem w.mem := by
    rw [wm]
    exact ((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
      List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  have dC24 (R : Region) (hR : Region.Disjoint R ⟨State.addr c, 256⟩) : ∀ r ∈ [(⟨State.addr c, 64⟩ : Region)],
      Region.Disjoint R r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hR.sub_right (sub_c64 _)
  obtain frK : ∀ r ∈ [(⟨State.addr d + BitVec.ofNat 64 (8 * j), 8⟩ : Region), ctRegion c],
      Region.Disjoint ⟨State.addr kb, 128⟩ r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hl.dKD.sub_right (sub_blk _ hj)
    · exact hl.dKS.sub_right (sub_ct256 _)
  refine ⟨⟨w12, ?_, fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, wrd.trans (vrd.trans h.rd), wwr.trans (vwr.trans h.wr),
    wsp.trans (vsp.trans h.sp), wsy.trans (vsy.trans h.syms), ?_⟩, ?_⟩
  · refine h.fr.trans ((vf.sub fun r hr => ?_).trans (fw.mono (by simp)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, sub_blk _ hj⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, sub_ct _⟩
  · have hdi : Region.Disjoint ⟨State.addr d + BitVec.ofNat 64 (8 * i), 8⟩ ⟨State.addr c, 256⟩ :=
      hl.dDS.sub_left (sub_blk _ hi)
    rw [blockAt_frame fw (dC24 _ hdi)]
    by_cases hij : i = j
    · subst hij
      rw [vb, ite_eq_left (by omega_arith), h.blocks i hi, ite_eq_right (by omega_arith), h.sk]
    · rw [blockAt_frame vf ?_, h.blocks i hi]
      · by_cases hlt : i < j
        · rw [ite_eq_left hlt, ite_eq_left (by omega_arith)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega_arith)]
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact blk_disj_blk _ hi hj (by omega_arith) hij
        · exact hdi.sub_right (sub_ct256 _)
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_self32, BitVec.add_assoc, Nat.mul_add, BitVec.ofNat_add (8 * j)]
    rfl
  · rw [wm, Mem.readW_writeW_self32, ofNat_sub_one (by omega_arith) (by omega_arith), Nat.sub_sub]
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), vslot 8 (by decide)]
    exact h.sslot
  · rw [wm, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide), vslot 12 (by decide)]
    exact h.rslot
  · rw [scheduleAt_frame fw (dC24 _ hl.dKS), scheduleAt_frame vf frK]
    exact h.sk
  · refine held_frame fw (by rw [s1234_len]; exact dC24 _ hl.dTS) (by rw [s1234_len]; decide)
      (held_frame vf (fun r hr => ?_) (by rw [s1234_len]; decide) h.held)
    rw [s1234_len]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hl.dTD.sub_right (sub_blk _ hj)
    · exact hl.dTS.sub_right (sub_ct256 _)
  · rw [wz, ofNat_sub_one (by omega_arith) (by omega_arith)]
    by_cases he : j + 1 = N
    · rw [decide_eq_true he, show N - j - 1 = 0 by omega_arith]; rfl
    · rw [decide_eq_false he]
      have : BitVec.ofNat 32 (N - j - 1) ≠ 0 := fun e => by
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl] at this
        omega_arith
      simpa using this

/-- The loop over the blocks, from `j = 0`: afterwards every block is done. -/
theorem ecbLoop_ok {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N : Nat}
    (hl : Lay s c d kb n N) (hN : 0 < N) (h : LInv s m0 up k c d kb n N 0 u) :
    WP isa (.loop (.seq (crypt up) (.block advance)) .ne) u (LInv s m0 up k c d kb n N N) := by
  refine WP.loop (M := isa) (fun m (v : State) => ∃ j, m = N - j ∧ j < N ∧ LInv s m0 up k c d kb n N j v)
    ?_ N u ⟨0, rfl, hN, h⟩
  rintro m v ⟨j, rfl, hj, hv⟩
  refine WP.mono (step_ok hl hv hj) fun w ⟨hw, wz⟩ => ?_
  by_cases he : j + 1 = N
  · exact .inl ⟨by show some (!w.z) = _; rw [wz, decide_eq_true he]; rfl, he ▸ hw⟩
  · exact .inr ⟨by show some (!w.z) = _; rw [wz, decide_eq_false he]; rfl, N - (j + 1), by omega_arith, j + 1, rfl,
      by omega_arith, hw⟩

/-! ## The whole function -/

section
variable {name : String} {ws : List (BitVec 64)} {st : Nat} {s : State}

/-- What the contract says of a function's one table: its words. -/
theorem ConstsOk.held1 (h : ConstsOk [(name, ws)] st s) : Held s.mem (State.addr (s.syms name)) ws :=
  h.2.1 _ List.mem_cons_self

/-- The code may read it. -/
theorem ConstsOk.rd1 (h : ConstsOk [(name, ws)] st s) :
    (⟨State.addr (s.syms name), 8 * ws.length⟩ : Region) ∈ s.rd := by
  obtain hm : (⟨State.addr (s.syms name), 8 * ws.length⟩ : Region) ∈
      s.rd.drop (s.rd.length - [(name, ws)].length) := by
    rw [h.1]; exact List.mem_cons_self
  exact List.mem_of_mem_drop hm

/-- No writable region overlaps it. -/
theorem ConstsOk.wr1 (h : ConstsOk [(name, ws)] st s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr (s.syms name), 8 * ws.length⟩ r :=
  (h.2.2.1 _ List.mem_cons_self).2.1

end

theorem stackArg_strip (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArg (stripConsts K s) i = stackArg s i := rfl
theorem stackArgAddr_strip (K : List (String × List (BitVec 64))) (s : State) (i : Nat) :
    stackArgAddr (stripConsts K s) i = stackArgAddr s i := rfl

/-- The ECB functions' contract on ARMv7, as their proof states it. -/
def ecbArm (up : Bool) : Contract isa where
  pre s :=
    let sch : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let dat : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 256⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sch, args] ∧ s.wr = [dat, scr] ∧ sch.Disjoint dat ∧ sch.Disjoint scr ∧ dat.Disjoint scr ∧
      args.Disjoint dat ∧ args.Disjoint scr ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 256 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 16)
  post s s' :=
    Spec.Cast5.blocksAt s'.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat =
      Spec.Cast5.ecb (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) (s.gpr .r1).toNat
        (if up then .encrypt else .decrypt) (Spec.Cast5.blocksAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

theorem cipher_map (up : Bool) (k : Spec.Cast5.Schedule) (n : Nat) (bs : List Spec.Cast5.Block) :
    bs.map (cipher up k n) = Spec.Cast5.ecb k n (if up then .encrypt else .decrypt) bs := by
  cases up <;> rfl

/-- What the end needs: every block done, and nothing else written since the
setup but the first 64 bytes of the working space. -/
structure Done (s : State) (m0 : Mem) (up : Bool) (k : Spec.Cast5.Schedule) (c d : BitVec 32) (n N : Nat)
    (u : State) : Prop where
  r12 : u.gpr .r12 = c
  fr : Frame [⟨State.addr d, 8 * N⟩, ⟨State.addr c, 64⟩] m0 u.mem
  blocks : ∀ i < N, Spec.Cast5.blockAt u.mem (State.addr d + BitVec.ofNat 64 (8 * i)) =
    cipher up k n (Spec.Cast5.blockAt m0 (State.addr d + BitVec.ofNat 64 (8 * i)))
  rd : u.rd = s.rd
  wr : u.wr = s.wr

theorem LInv.done {s u : State} {m0 : Mem} {up : Bool} {k : Spec.Cast5.Schedule} {c d kb : BitVec 32} {n N : Nat}
    (h : LInv s m0 up k c d kb n N N u) : Done s m0 up k c d n N u :=
  ⟨h.r12, h.fr, fun i hi => by rw [h.blocks i hi, ite_eq_left hi], h.rd, h.wr⟩

/-- The end: the registers restored, and the blocks as the contract says. -/
theorem restore_ok {s u : State} {m0 : Mem} {up : Bool} {c : BitVec 32} (hc : c = stackArg s 0)
    (hs : (ecbArm up).pre (stripConsts ecbConsts s))
    (hsv : Spill.Saved m0 (State.addr c) (s.setReg .r12 c).gpr savedSlots)
    (hm0 : Frame [⟨State.addr c, 256⟩] s.mem m0)
    (h : Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
      (s.gpr .r1).toNat (s.gpr .r3).toNat u) :
    WP isa (.block restore) u fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' := by
  obtain ⟨hrd, hwr, dKD, dKS, dDS, _, _, _, hdf, hcf, _, _⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stackArg_strip] at hwr dKS dDS hdf hcf
  rw [← hc] at hcf dKS dDS hwr
  obtain hsv' : Spill.Saved u.mem (State.addr (u.gpr .r12)) (s.setReg .r12 c).gpr savedSlots := by
    rw [h.r12]
    refine hsv.frame savedSlots_ok h.fr fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (dDS.sub_right (Offset.sub_base _ (by decide))).symm
    · exact Offset.disjoint_base _ (by decide) (by decide)
  rw [restore_eq]
  refine WP.mono (Spill.restore_block_ok savedSlots_ok savedSlots_restorable (by rw [h.r12]; omega_arith)
    (fun d _ hd => by
      rw [h.rd, h.wr, hwr, h.r12]
      exact ⟨⟨State.addr c, 256⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    hsv') fun s' ⟨hg, _, hm, _, _, _⟩ => ⟨fun r hr => ?_, ?_⟩
  · rw [Spill.restored_reg hg (savedSlots_preserved r hr)]
    exact gpr_setReg_of_ne _ _ (by intro e; subst e; exact absurd hr (by decide))
  · show Spec.Cast5.blocksAt s'.mem _ _ = _
    rw [hm, ← cipher_map]
    unfold Spec.Cast5.blocksAt
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    rw [List.mem_range] at hi
    simp only [Function.comp]
    rw [h.blocks i hi, blockAt_frame hm0 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dDS.sub_left (sub_blk _ hi)]

/-- The arguments to their slots, then whether there are blocks. -/
theorem slots_ok (u : State) {c : BitVec 32} (hc : u.gpr .r12 = c) (hcf : c.toNat + 256 ≤ 2 ^ 32)
    (hin : ∀ {off w : Nat}, off + w ≤ 256 → InRegions u.wr (State.addr c + BitVec.ofNat 64 off) w) :
    WP isa (.block [.str .r2 .r12 dataOff, .str .r3 .r12 nOff, .str .r0 .r12 schedOff, .str .r1 .r12 roundsOff,
      .cmp .r3 (.imm 0)]) u fun w =>
      w.mem = (((u.mem.writeW (State.addr c + BitVec.ofNat 64 0) (u.gpr .r2)).writeW (State.addr c + BitVec.ofNat 64 4)
        (u.gpr .r3)).writeW (State.addr c + BitVec.ofNat 64 8) (u.gpr .r0)).writeW (State.addr c + BitVec.ofNat 64 12)
          (u.gpr .r1) ∧
      w.z = (u.gpr .r3 - 0 == 0) ∧ w.gpr = u.gpr ∧ w.rd = u.rd ∧ w.wr = u.wr ∧ w.sp = u.sp := by
  obtain aS := addr_off hcf
  unfold dataOff nOff schedOff roundsOff
  crun [hc, aS, hin]
  rfl

theorem slot_frame (m : Mem) (C : Addr) (a b x y : BitVec 32) :
    Frame [⟨C, 16⟩] m ((((m.writeW (C + BitVec.ofNat 64 0) a).writeW (C + BitVec.ofNat 64 4) b).writeW
      (C + BitVec.ofNat 64 8) x).writeW (C + BitVec.ofNat 64 12) y) :=
  ((((Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))).writeW
    List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))

theorem ecb_correct (up : Bool) (s : State) (hs : (ecbArm up).pre (stripConsts ecbConsts s))
    (hk : ConstsOk ecbConsts 0 s) :
    WP isa (ecb up) s fun s' => (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' := by
  have hs₀ := hs
  obtain ⟨hrd, hwr, dKD, dKS, dDS, _, _, hkf, hdf, hcf, _, hn⟩ := hs
  simp only [stripConsts_gpr, stripConsts_wr, stackArg_strip, stackArgAddr_strip] at hrd hwr dKD dKS dDS hkf
  simp only [stripConsts_gpr, stackArg_strip] at hdf hcf hn
  obtain tfit : (s.syms s1234Sym).toNat + 4096 ≤ 2 ^ 32 := s1234_len ▸ hk.fit List.mem_cons_self
  obtain trd : (⟨State.addr (s.syms s1234Sym), 4096⟩ : Region) ∈ s.rd := s1234_len ▸ ConstsOk.rd1 hk
  obtain twr : ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr (s.syms s1234Sym), 4096⟩ r := s1234_len ▸ ConstsOk.wr1 hk
  obtain held : Held s.mem (State.addr (s.syms s1234Sym)) s1234 := ConstsOk.held1 hk
  obtain ⟨c, hc⟩ : ∃ c, c = stackArg s 0 := ⟨_, rfl⟩
  rw [← hc] at hcf dKS dDS hwr
  obtain hargs : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 0)) 4 :=
    ⟨⟨stackArgAddr s 0, 4⟩, List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp)), Region.contains_self _ _⟩
  obtain inC : ∀ {off w : Nat}, off + w ≤ 256 → InRegions s.wr (State.addr c + BitVec.ofNat 64 off) w :=
    fun hw => ⟨⟨State.addr c, 256⟩, by rw [hwr]; simp, Offset.contains_base _ hw (by omega_arith)⟩
  unfold ecb
  refine WP.seq ?_
  rw [List.append_assoc, WP.block_append_iff]
  -- The working space, and the saved registers.
  obtain h1 : WP isa (.block [.ldrSp .r12 0]) s fun s₁ => s₁ = s.setReg .r12 c := by
    crun [hargs]
    rw [hc]; rfl
  refine WP.mono h1 fun s₁ e₁ => ?_
  subst e₁
  rw [WP.block_append_iff, save_eq]
  refine VG.Arm.WP.mono_syms (WP.keep [] (Spill.save_block_ok savedSlots_ok (s := s.setReg .r12 c)
    (by simp only [gpr_setReg_self]; omega_arith) fun d _ hd => by simp only [gpr_setReg_self, wr_setReg]; exact inC (by omega_arith))
    (by decide)) fun s₂ ⟨⟨g₂, rd₂, wr₂, m₂⟩, k₂⟩ sy₂ => ?_
  simp only [gpr_setReg_self] at m₂
  obtain c₂ : s₂.gpr .r12 = c := by rw [g₂, gpr_setReg_self]
  refine VG.Arm.WP.mono_syms (slots_ok s₂ c₂ hcf fun hw => by rw [wr₂]; exact inC hw)
    fun s₃ ⟨m₃, z₃, g₃, rd₃, wr₃, sp₃⟩ sy₃ => ?_
  -- The memory after the setup.
  obtain ⟨m0, hm0e⟩ : ∃ m0, s₃.mem = m0 := ⟨_, rfl⟩
  obtain hsv : Spill.Saved m0 (State.addr c) (s.setReg .r12 c).gpr savedSlots := by
    rw [← hm0e, m₃, m₂]
    refine (Spill.saveMem_saved _ _ _ _ savedSlots_ok).frame savedSlots_ok (slot_frame _ _ _ _ _ _) fun r hr => ?_
    simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint_base _ (by decide) (by decide)
  obtain hm0 : Frame [⟨State.addr c, 256⟩] s.mem m0 := by
    rw [← hm0e, m₃, m₂]
    exact (Spill.saveMem_frame _ _ _ (by decide) _ (by decide)).trans
      ((slot_frame _ _ _ _ _ _).sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self, fun x hx => by simp only [Region.Contains] at hx ⊢; omega_arith⟩)
  have g₃' (r : Reg) (hr : r ≠ .r12) : s₃.gpr r = s.gpr r := by
    rw [g₃, g₂]; exact gpr_setReg_of_ne _ _ hr
  obtain rd₃' : s₃.rd = s.rd := rd₃.trans rd₂
  obtain wr₃' : s₃.wr = s.wr := wr₃.trans wr₂
  obtain sp₃' : s₃.sp = s.sp := sp₃.trans k₂.sp
  obtain lay : Lay s c (s.gpr .r2) (s.gpr .r0) (s.gpr .r1).toNat (s.gpr .r3).toNat :=
    { cfit := hcf, dfit := hdf, kfit := hkf, scr := by rw [hwr]; simp, dat := by rw [hwr]; simp,
      sch := List.mem_append_left _ (stripConsts_rd_mem (by rw [hrd]; simp)), dDS := dDS, dKS := dKS, dKD := dKD,
      nv := hn, tfit := tfit, trd := List.mem_append_left _ trd, dTD := twr _ (by rw [hwr]; simp),
      dTS := twr _ (by rw [hwr]; simp) }
  obtain done : ∀ u : State, Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
      (s.gpr .r1).toNat (s.gpr .r3).toNat u → WP isa (.block restore) u fun s' =>
        (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (ecbArm up).post s s' :=
    fun u hu => restore_ok hc hs₀ hsv hm0 hu
  refine WP.seq (WP.mono (Q := Done s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2)
    (s.gpr .r1).toNat (s.gpr .r3).toNat) ?_ done)
  refine wp_ite_eq (fun hz => WP.block_nil ⟨by rw [g₃, g₂, gpr_setReg_self], by rw [hm0e]; exact Frame.refl _ _,
      fun i hi => ?_, rd₃', wr₃'⟩) (fun hz => ?_)
  · rw [z₃, g₂, gpr_setReg_of_ne _ _ (by decide)] at hz
    obtain h0 : s.gpr .r3 - 0 = 0 := beq_iff_eq.mp hz
    have : (s.gpr .r3).toNat = 0 := by bv_omega_arith
    omega_arith
  · have hN : 0 < (s.gpr .r3).toNat := by
      rw [z₃, g₂, gpr_setReg_of_ne _ _ (by decide)] at hz
      obtain h0 : s.gpr .r3 - 0 ≠ 0 := fun e => by rw [e] at hz; exact absurd hz (by decide)
      bv_omega_arith
    obtain l0 : LInv s m0 up (Spec.Cast5.scheduleAt s.mem (State.addr (s.gpr .r0))) c (s.gpr .r2) (s.gpr .r0)
        (s.gpr .r1).toNat (s.gpr .r3).toNat 0 s₃ :=
      { r12 := by rw [g₃, g₂, gpr_setReg_self]
        fr := by rw [hm0e]; exact Frame.refl _ _
        blocks := fun i hi => by rw [ite_eq_right (Nat.not_lt_zero _), hm0e]
        dslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide)]
          exact (BitVec.add_zero _).symm
        nslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide), Nat.sub_zero, BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
        sslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_sep (Offset.sep _ (by decide) (by decide) (by decide)) (by decide),
            Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide)]
        rslot := by
          rw [hm0e, ← hm0e, m₃, Mem.readW_writeW_self32, g₂, gpr_setReg_of_ne _ _ (by decide), BitVec.ofNat_toNat,
            BitVec.setWidth_eq]
        sk := by
          rw [hm0e]
          exact scheduleAt_frame hm0 fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dKS
        rd := rd₃'
        wr := wr₃'
        sp := sp₃'
        syms := by rw [sy₃, sy₂]; rfl
        held := by
          rw [hm0e]
          refine held_frame hm0 (fun r hr => ?_) (by rw [s1234_len]; decide) held
          simp only [List.mem_singleton] at hr; subst hr
          rw [s1234_len]; exact twr _ (by rw [hwr]; simp) }
    exact WP.mono (ecbLoop_ok lay hN l0) fun u hu => hu.done

end VG.Proof.Cast5.Arm
