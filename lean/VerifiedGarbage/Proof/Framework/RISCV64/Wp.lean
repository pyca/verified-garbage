module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.RISCV64.Isa
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad

/-!
# RISC-V: weakest preconditions of single instructions

Untrusted: everything here is checked by Lean. One rule per instruction
form, each continuing with the state the instruction leads to, described
by what it changes (`Upd`: a register; `Mupd`: memory), as
`Proof/Sha256/RISCV64/Stream/Common.lean` has them for SHA-256.
-/

@[expose] public section

namespace VG.RISCV64.Wp

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

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_addi (by unfold imm12; omega)) ?_
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

theorem wp_mv {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n 0 :: is)) s Q :=
  wp_addi (imm := 0) (by decide) fun s' u => k s' (by simpa using u)

theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (exec_addSp h) (k _ (Upd.write _ _ _))

theorem wp_not {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n ^^^ BitVec.allOnes 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .xor d n (-1) :: is)) s Q :=
  WP.cons (exec_logicImm (by decide)) (k _ (Upd.write _ _ _))

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

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_li (by unfold imm12; omega)) ?_
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

theorem wp_subi {d n : Reg} {imm : Nat} (h : imm ≤ 2048)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n (-(imm : Int)) :: is)) s Q := by
  refine WP.cons (exec_addi (by unfold imm12; omega)) ?_
  rw [BitVec.ofInt_neg, ofInt_ofNat, ← BitVec.sub_eq_add_neg]; exact k _ (Upd.write _ _ _)

theorem wp_add {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.add d n m :: is)) s Q :=
  WP.cons exec_add (k _ (Upd.write _ _ _))

theorem wp_sub {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.sub d n m :: is)) s Q :=
  WP.cons exec_sub (k _ (Upd.write _ _ _))

theorem wp_xor {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .xor d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

theorem wp_xori {d n : Reg} {imm : Nat} (h : imm < 2048)
    (k : ∀ s', Upd s s' d (s.gpr n ^^^ BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .xor d n (imm : Int) :: is)) s Q := by
  refine WP.cons (exec_logicImm (by unfold imm12; omega)) ?_
  simp only
  rw [ofInt_ofNat]; exact k _ (Upd.write _ _ _)

theorem wp_lbu {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Upd s s' t ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .b t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem a).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_b ho (by rw [ha]; exact hin), ha, ByteLoad.read_one]

theorem wp_sb {t n : Reg} {off : Nat} {a : Addr} (ho : off < 2048)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .b t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl⟩)
  rw [exec_store_b ho (by rw [ha]; exact hout), ha]
  rfl

end

/-- `eval` of the branch conditions. -/
theorem eval_zero (s : State) (r : Reg) : eval (.zero r) s = some (s.gpr r == 0) := rfl

theorem eval_nonzero (s : State) (r : Reg) : eval (.nonzero r) s = some (s.gpr r != 0) := rfl

/-- An 8-byte aligned offset of a 16-byte aligned address. -/
theorem al8 {b : Addr} (hb : b.toNat % 16 = 0) {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 32) :
    (b + BitVec.ofNat 64 d).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega)]
  have := b.isLt
  omega

end VG.RISCV64.Wp
