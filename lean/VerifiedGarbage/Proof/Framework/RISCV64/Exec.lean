module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.Block

/-!
# RISC-V: instruction-level rewrite lemmas for symbolic execution

Untrusted: everything here is checked by Lean.

The registers are 64 bits; the `*w` forms read the low words of their
operands and sign-extend their result, so 32-bit values are tracked by the
low word of a register (`(s.gpr r).setWidth 32`); `lo32_sext` and friends
push the low word through the sign extension and the 64-bit operations.
Loads and stores must be naturally aligned; bytes always are.
-/

@[expose] public section

namespace VG.RISCV64

theorem addr_eq {s : State} {bytes : Nat} {n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % bytes = 0) :
    addr s bytes n off = some (s.gpr n + BitVec.ofNat 64 off) := by
  unfold addr; exact ite_eq_left_of_eq_true _ _ (eq_true ⟨ho, ha⟩)

theorem exec_load_b {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.load .b t n off) s =
      some (s.write t ((s.mem.read (s.gpr n + BitVec.ofNat 64 off) 1).setWidth 64)) := by
  simp only [exec, addr_eq (bytes := 1) ho (Nat.mod_one _), Option.bind_some, State.load,
    Width.bytes, h, ite_true, Option.map_some]

theorem exec_load_w {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 4) :
    exec (.load .w t n off) s =
      some (s.write t ((s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 32).setWidth 64)) := by
  simp only [exec, addr_eq (bytes := 4) ho ha, Option.bind_some, State.load, Width.bytes, h,
    ite_true, Option.map_some, Mem.readW]
  rfl

theorem exec_load_d {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 8 = 0)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.load .d t n off) s = some (s.write t (s.mem.readW (s.gpr n + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, addr_eq (bytes := 8) ho ha, Option.bind_some, State.load, Width.bytes, h,
    ite_true, Option.map_some, Mem.readW]

theorem exec_store_b {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 1) :
    exec (.store .b t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 1 ((s.gpr t).setWidth 8) } := by
  simp only [exec, addr_eq (bytes := 1) ho (Nat.mod_one _), Option.bind_some, State.store,
    Width.bytes, h, ite_true]

theorem exec_store_w {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 4 = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 4) :
    exec (.store .w t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) ((s.gpr t).setWidth 32) } := by
  simp only [exec, addr_eq (bytes := 4) ho ha, Option.bind_some, State.store, Width.bytes, h,
    ite_true, Mem.writeW]
  rfl

theorem exec_store_d {s : State} {t n : Reg} {off : Nat} (ho : off < 2048)
    (ha : (s.gpr n + BitVec.ofNat 64 off).toNat % 8 = 0)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 8) :
    exec (.store .d t n off) s =
      some { s with mem := s.mem.writeW (s.gpr n + BitVec.ofNat 64 off) (s.gpr t) } := by
  simp only [exec, addr_eq (bytes := 8) ho ha, Option.bind_some, State.store, Width.bytes, h,
    ite_true, Mem.writeW]

theorem exec_add {s : State} {d n m : Reg} :
    exec (.add d n m) s = some (s.write d (s.gpr n + s.gpr m)) := rfl

theorem exec_sub {s : State} {d n m : Reg} :
    exec (.sub d n m) s = some (s.write d (s.gpr n - s.gpr m)) := rfl

theorem exec_addw {s : State} {d n m : Reg} :
    exec (.addw d n m) s =
      some (s.write d (sext32 ((s.gpr n).setWidth 32 + (s.gpr m).setWidth 32))) := rfl

theorem exec_subw {s : State} {d n m : Reg} :
    exec (.subw d n m) s =
      some (s.write d (sext32 ((s.gpr n).setWidth 32 - (s.gpr m).setWidth 32))) := rfl

theorem exec_sltu {s : State} {d n m : Reg} :
    exec (.sltu d n m) s = some (s.write d (if s.gpr n < s.gpr m then 1 else 0)) := rfl

theorem exec_mul {s : State} {d n m : Reg} :
    exec (.mul d n m) s = some (s.write d (s.gpr n * s.gpr m)) := rfl

theorem exec_mulhu {s : State} {d n m : Reg} :
    exec (.mulhu d n m) s =
      some (s.write d (BitVec.ofNat 64 ((s.gpr n).toNat * (s.gpr m).toNat / 2 ^ 64))) := rfl

theorem exec_logic {op : LogicOp} {s : State} {d n m : Reg} :
    exec (.logic op d n m) s = some (s.write d (match op with
      | .and => s.gpr n &&& s.gpr m | .or => s.gpr n ||| s.gpr m
      | .xor => s.gpr n ^^^ s.gpr m)) := rfl

theorem exec_addi {s : State} {d n : Reg} {imm : Int} (h : imm12 imm) :
    exec (.addi d n imm) s = some (s.write d (s.gpr n + BitVec.ofInt 64 imm)) := by
  simp only [exec]; exact (ite_eq_left_of_eq_true _ _ (eq_true h)).trans rfl

theorem exec_addiw {s : State} {d n : Reg} {imm : Int} (h : imm12 imm) :
    exec (.addiw d n imm) s =
      some (s.write d (sext32 ((s.gpr n).setWidth 32 + BitVec.ofInt 32 imm))) := by
  simp only [exec]; exact (ite_eq_left_of_eq_true _ _ (eq_true h)).trans rfl

theorem exec_logicImm {op : LogicOp} {s : State} {d n : Reg} {imm : Int} (h : imm12 imm) :
    exec (.logicImm op d n imm) s = some (s.write d (match op with
      | .and => s.gpr n &&& BitVec.ofInt 64 imm | .or => s.gpr n ||| BitVec.ofInt 64 imm
      | .xor => s.gpr n ^^^ BitVec.ofInt 64 imm)) := by
  simp only [exec]; exact (ite_eq_left_of_eq_true _ _ (eq_true h)).trans rfl

theorem exec_li {s : State} {d : Reg} {imm : Int} (h : imm12 imm) :
    exec (.li d imm) s = some (s.write d (BitVec.ofInt 64 imm)) := by
  simp only [exec]; exact (ite_eq_left_of_eq_true _ _ (eq_true h)).trans rfl

theorem exec_lui {s : State} {d : Reg} {imm : BitVec 20} :
    exec (.lui d imm) s = some (s.write d (sext32 (imm ++ (0 : BitVec 12)))) := rfl

theorem exec_addSp {s : State} {d : Reg} {imm : Nat} (h : imm < 2048) :
    exec (.addSp d imm) s = some (s.write d (s.sp + BitVec.ofNat 64 imm)) := by
  simp only [exec, h, ite_true]

/-- `lla` puts the static's address in `d`. -/
theorem exec_lla {s : State} {d : Reg} {name : String} :
    exec (.lla d name) s = some (s.write d (s.syms name)) := rfl

theorem exec_shift_d {op : ShiftOp} {s : State} {d n : Reg} {sh : Nat} (h : sh < 64) :
    exec (.shift op .d d n sh) s = some (s.write d (match op with
      | .sll => s.gpr n <<< sh | .srl => s.gpr n >>> sh | .sra => (s.gpr n).sshiftRight sh)) := by
  simp only [exec]; exact (ite_eq_left_of_eq_true _ _ (eq_true h)).trans rfl

theorem exec_shift_w {op : ShiftOp} {s : State} {d n : Reg} {sh : Nat} (h : sh < 32) :
    exec (.shift op .w d n sh) s = some (s.write d (sext32 (match op with
      | .sll => (s.gpr n).setWidth 32 <<< sh | .srl => (s.gpr n).setWidth 32 >>> sh
      | .sra => ((s.gpr n).setWidth 32).sshiftRight sh))) := by
  simp only [exec]; exact (ite_eq_left_of_eq_true _ _ (eq_true h)).trans rfl

/-! ## Low words -/

theorem lo32_sext (x : BitVec 32) : (sext32 x).setWidth 32 = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < 64 by omega]

theorem lo32_add (x y : BitVec 64) : (x + y).setWidth 32 = x.setWidth 32 + y.setWidth 32 :=
  BitVec.setWidth_add x y (by decide)

theorem lo32_sub (x y : BitVec 64) : (x - y).setWidth 32 = x.setWidth 32 - y.setWidth 32 := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, lo32_add, BitVec.setWidth_neg_of_le (by decide)]

theorem lo32_xor (x y : BitVec 64) : (x ^^^ y).setWidth 32 = x.setWidth 32 ^^^ y.setWidth 32 := by
  simp

theorem lo32_or (x y : BitVec 64) : (x ||| y).setWidth 32 = x.setWidth 32 ||| y.setWidth 32 := by
  simp

theorem lo32_and (x y : BitVec 64) : (x &&& y).setWidth 32 = x.setWidth 32 &&& y.setWidth 32 := by
  simp

theorem lo32_ext (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  simp

/-- A word rotated left by `k < 32`, as `slliw`, `srliw` and `or` compute it
in the low word. -/
theorem rotl_shifts (x : BitVec 32) {k : Nat} (h : k < 32) :
    x <<< k ||| x >>> (32 - k) = x.rotateLeft k := by
  rw [BitVec.rotateLeft_eq_rotateLeftAux_of_lt h]; rfl

end VG.RISCV64

namespace VG.RISCV64

theorem exec_sp {i : Instr} {s s' : State} (h : exec i s = some s') : s'.sp = s.sp := by
  cases i with
  | shift op sz =>
    cases sz <;> simp only [exec] at h <;> (split at h <;> [skip; cases h]) <;>
    simp only [Option.some.injEq] at h <;> subst h <;> rfl
  | shiftReg op sz =>
    cases sz <;> simp only [exec, Option.some.injEq] at h <;> subst h <;> rfl
  | _ =>
    simp only [exec, Option.bind_eq_some_iff, Option.map_eq_some_iff, State.write, State.load,
      State.store] at h
    (repeat' split at h) <;>
    (try simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    first
    | (subst h; rfl)
    | (obtain ⟨_, _, _, _, rfl⟩ := h; rfl)
    | (obtain ⟨_, _, h⟩ := h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h;
       subst h; rfl)

theorem execBlock_sp {is : List Instr} {s s' : State} {t : List Leak}
    (h : VG.execBlock isa is s = some (s', t)) : s'.sp = s.sp := by
  induction is generalizing s t with
  | nil => simp only [VG.execBlock, Option.some.injEq, Prod.mk.injEq] at h; rw [h.1]
  | cons i is ih =>
    simp only [VG.execBlock] at h
    split at h
    · cases h
    · rename_i s₁ he
      simp only [Option.map_eq_some_iff, Prod.exists] at h
      obtain ⟨s₂, _, h, he'⟩ := h
      simp only [Prod.mk.injEq] at he'
      obtain ⟨rfl, -⟩ := he'
      rw [ih h]; exact exec_sp he

/-- A frame's push moves `sp` down by the frame (the region it adds). -/
theorem push_sp {i : Instr} {s s₁ : State} (h : push i s = some s₁) :
    ∃ n, s₁.sp = s.sp - BitVec.ofNat 64 n ∧ s₁.wr.head? = some ⟨s₁.sp, n⟩ := by
  cases i <;> simp only [push, reduceCtorEq] at h
  · split at h <;> cases h; exact ⟨16, rfl, rfl⟩
  · split at h <;> cases h; exact ⟨_, rfl, rfl⟩

/-- A frame's pop moves `sp` up by the frame its push made (the head of the
regions). -/
theorem pop_sp {j : Instr} {s₁ s₂ s' : State} (h : pop j s₁ s₂ = some s') :
    s₂.sp = s₁.sp ∧ ∃ n, s₁.wr.head? = some ⟨s₁.sp, n⟩ ∧ s'.sp = s₂.sp + BitVec.ofNat 64 n := by
  cases j <;> simp only [pop, reduceCtorEq] at h
  · split at h <;> cases h
    rename_i hc; exact ⟨hc.1, 16, hc.2.2, rfl⟩
  · split at h <;> cases h
    rename_i hc
    exact ⟨hc.2.2.2.1, _, hc.2.2.2.2.2, rfl⟩

/-- No modelled instruction changes `sp`, and frames restore it. -/
theorem Exec.sp {c : Prog isa} {s s' : State} {t : List Leak} (h : VG.Exec isa c s t s') :
    s'.sp = s.sp := by
  induction h with
  | icall hi => nomatch hi
  | icallNext hi => nomatch hi
  | block h => exact execBlock_sp h
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | iteT _ _ ih => exact ih
  | iteF _ _ ih => exact ih
  | loopExit _ _ ih => exact ih
  | loopNext _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | call hc _ hr ih =>
    simp only [isa, call, ret, Option.some.injEq] at hc hr
    subst hc; split at hr <;> cases hr; exact ih
  | frame hp hb hq ih =>
    obtain ⟨h₁, n', hh', h₂⟩ := pop_sp hq
    obtain ⟨n, hs, hh⟩ := push_sp hp
    rw [hh] at hh'
    obtain rfl : n = n' := by cases hh'; rfl
    rw [h₂, ih, hs, BitVec.sub_add_cancel]

/-! Symbolic execution of a block, one instruction at a time (see `runStep`).
These are deliberately not proved by `rfl`: `simp` would use an `rfl` lemma
as a definitional unfolding, which the kernel then re-checks by unfolding the
structural recursion of `runBlock` over the whole remaining block, at every
instruction. -/

theorem runBlock_nil {s : State} : runBlock isa ([] : List Instr) s = some s := by
  rw [runBlock]

theorem runBlock_cons {i : Instr} {is : List Instr} {s : State} :
    runBlock isa (i :: is : List Instr) s = runStep isa (exec i s) is := by
  rw [runBlock]; rfl

theorem runStep_some {s : State} {is : List Instr} :
    runStep isa (some s : Option State) is = runBlock isa is s := by
  rw [runStep]; rfl

end VG.RISCV64
