module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import all Init.Data.Nat.Bitwise.Basic

/-!
# RISC-V: weakest preconditions one instruction at a time

Untrusted: everything here is checked by Lean. For code whose blocks are
proven an instruction at a time, as the PPC64LE streaming proofs do: each
`wp_*` rule runs the first instruction of a block and hands the rest a state
described by `Upd` (one register written) or `Mupd` (memory written), so the
caller reads registers through the writes without unfolding them. The
immediates, which are `Int`s, are stated as `Nat`s (a negative one as a
subtraction, `wp_subi`).
-/

@[expose] public section

namespace VG.RISCV64.Steps

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨RegUpd.gpr_write_self _ _ _, fun _ h => RegUpd.gpr_write_of_ne _ _ h, rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

theorem ofInt_ofNat (imm : Nat) : BitVec.ofInt 64 (imm : Int) = BitVec.ofNat 64 imm := by
  simp

theorem add_ofInt_neg (x : BitVec 64) (imm : Nat) :
    x + BitVec.ofInt 64 (-(imm : Int)) = x - BitVec.ofNat 64 imm := by
  rw [BitVec.ofInt_neg, ofInt_ofNat, ← BitVec.sub_eq_add_neg]

/-- A one-byte read. -/
theorem read_one (m : Mem) (a : Addr) : (m.read a 1).setWidth 64 = (m a).setWidth 64 := by
  show ((0#0 : BitVec 0) ++ m a).setWidth 64 = _
  rw [BitVec.zero_width_append]; rfl

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_addi (by unfold imm12; omega)) ?_
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

/-- `mv d, n` (`addi d, n, 0`). -/
theorem wp_mv {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n 0 :: is)) s Q :=
  wp_addi (imm := 0) (by decide) fun s' u => k s' (by simpa using u)

theorem wp_subi {d n : Reg} {imm : Nat} (h : imm ≤ 2048)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n (-(imm : Int)) :: is)) s Q := by
  refine WP.cons (exec_addi (by unfold imm12; omega)) ?_
  rw [add_ofInt_neg]; exact k _ (Upd.write _ _ _)

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_li (by unfold imm12; omega)) ?_
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

theorem wp_sltu {d n m : Reg}
    (k : ∀ s', Upd s s' d (if s.gpr n < s.gpr m then 1 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.sltu d n m :: is)) s Q :=
  WP.cons exec_sltu (k _ (Upd.write _ _ _))

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_or {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_andi {d n : Reg} {imm : Int} (h : imm12 imm)
    (k : ∀ s', Upd s s' d (s.gpr n &&& BitVec.ofInt 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n imm :: is)) s Q :=
  WP.cons (exec_logicImm h) (k _ (Upd.write _ _ _))

/-- `x &&& 63`. -/
theorem and63 (x : BitVec 64) : x &&& BitVec.ofInt 64 63 = BitVec.ofNat 64 (x.toNat % 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 63).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

theorem wp_andi63 {d n : Reg}
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 ((s.gpr n).toNat % 64)) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n 63 :: is)) s Q :=
  wp_andi (by decide) fun s' u => k s' (by rw [← and63]; exact u)

theorem wp_srl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .srl .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_sll {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .sll .d d n sh :: is)) s Q :=
  WP.cons (exec_shift_d h) (k _ (Upd.write _ _ _))

theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (exec_addSp h) (k _ (Upd.write _ _ _))

theorem wp_lbu {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .b t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_b ho (by rw [ha]; exact hin), ha, read_one]

theorem wp_sb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .b t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_b ho (by rw [ha]; exact hout), ha]
  rfl

theorem wp_sd {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d ho (by rw [ha]; exact hal) (by rw [ha]; exact hout), ha]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hal : a.toNat % 8 = 0)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d ho (by rw [ha]; exact hal) (by rw [ha]; exact hin), ha]

end

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero r) s = some (s.gpr r == 0) := rfl

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero r) s = some (s.gpr r != 0) := rfl

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem eval_zero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.zero r) s = some (decide (k = 0)) := by
  rw [eval_zero, h, ofNat_beq_zero hk]

theorem eval_nonzero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.nonzero r) s = some (decide (k ≠ 0)) := by
  rw [eval_nonzero, h, bne, ofNat_beq_zero hk]
  simp

end VG.RISCV64.Steps
