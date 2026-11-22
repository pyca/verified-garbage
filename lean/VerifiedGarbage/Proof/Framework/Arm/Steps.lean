module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd

/-!
# ARMv7: weakest preconditions one instruction at a time

Untrusted: everything here is checked by Lean. As AArch64's `Steps`
(`Proof/Framework/AArch64/Steps.lean`), for code whose blocks are proven an
instruction at a time: each `wp_*` rule runs the first instruction of a
block and hands the rest a state described by `Upd` (one register written,
the flags kept) or `Mupd` (memory written), which also say that the
addresses of the statics (`syms`) are kept, so the caller reads registers
through the writes without unfolding them; `subs` and `cmp` give the flags
they set (`Fl`).
-/

@[expose] public section

namespace VG.Arm.Steps

open VG.Arm.RegUpd

/-- `s'` is `s` with register `d` set to `v`, the flags kept. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  z : s'.z = s.z
  c : s'.c = s.c

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 32) : Upd s (s.setReg d v) d v :=
  ⟨gpr_setReg_self _ _ _, fun _ h => gpr_setReg_of_ne _ _ h, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`, the flags kept. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  sp : s'.sp = s.sp
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  z : s'.z = s.z
  c : s'.c = s.c

/-- `s'` is `s` with the flags of `x - y`, but maybe a register. -/
structure Fl (s s' : State) (x y : BitVec 32) : Prop where
  sp : s'.sp = s.sp
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  syms : s'.syms = s.syms
  z : s'.z = (x - y == 0)
  c : s'.c = decide (y.toNat ≤ x.toNat)

/-- `s'` is `s` with register `d` set to `v` and the flags of `x - y`. -/
structure UpdF (s s' : State) (d : Reg) (v x y : BitVec 32) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  fl : Fl s s' x y

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `mov d, m`. -/
theorem wp_movr {d m : Reg} (k : ∀ s', Upd s s' d (s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg m) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `mov d, #v`. -/
theorem wp_movi {d : Reg} {v : BitVec 32} (h : encodable v = true)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) : WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp only [exec, Op2.eval, h, ↓reduceIte, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-- `add d, n, m`. -/
theorem wp_addr {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n + s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n (.reg m) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `sub d, n, m`. -/
theorem wp_subr {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n - s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n (.reg m) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `and d, n, m`. -/
theorem wp_andr {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .and d n (.reg m) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

/-- `add d, n, #v`. -/
theorem wp_addi {d n : Reg} {v : BitVec 32} (h : encodable v = true)
    (k : ∀ s', Upd s s' d (s.gpr n + v) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .add d n (.imm v) :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + v)) (by simp only [exec, Op2.eval, h, ↓reduceIte, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-- `sub d, n, #v`. -/
theorem wp_subi {d n : Reg} {v : BitVec 32} (h : encodable v = true)
    (k : ∀ s', Upd s s' d (s.gpr n - v) → WP isa (.block is) s' Q) :
    WP isa (.block (.dp .sub d n (.imm v) :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n - v)) (by simp only [exec, Op2.eval, h, ↓reduceIte, Option.map_some])
    (k _ (Upd.setReg _ _ _))

/-- `adc d, n, #v`. -/
theorem wp_adci {d n : Reg} {v : BitVec 32} (h : encodable v = true)
    (k : ∀ s', Upd s s' d (s.gpr n + v + (if s.c then 1 else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (.adc d n (.imm v) :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.gpr n + v + (if s.c then 1 else 0)))
    (by simp only [exec, Op2.eval, h, ↓reduceIte, Option.map_some]) (k _ (Upd.setReg _ _ _))

/-- `add d, sp, #imm`. -/
theorem wp_addSp {d : Reg} {imm : Nat} (h : imm < 256)
    (k : ∀ s', Upd s s' d (s.sp + BitVec.ofNat 32 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addSp d imm :: is)) s Q :=
  WP.cons (s' := s.setReg d (s.sp + BitVec.ofNat 32 imm)) (by simp only [exec, h, ↓reduceIte])
    (k _ (Upd.setReg _ _ _))

/-- `subs d, n, m`. -/
theorem wp_subsr {d n m : Reg}
    (k : ∀ s', UpdF s s' d (s.gpr n - s.gpr m) (s.gpr n) (s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.subs d n (.reg m) :: is)) s Q := by
  refine WP.cons rfl (k _ ⟨?_, fun _ h => ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩)
  · exact gpr_setReg_self _ _ _
  · exact gpr_setReg_of_ne _ _ h

/-- `cmp n, #v`. -/
theorem wp_cmpi {n : Reg} {v : BitVec 32} (h : encodable v = true)
    (k : ∀ s', s'.gpr = s.gpr → Fl s s' (s.gpr n) v → WP isa (.block is) s' Q) :
    WP isa (.block (.cmp n (.imm v) :: is)) s Q :=
  WP.cons (s' := subFlags s (s.gpr n) v) (by simp only [exec, Op2.eval, h, ↓reduceIte, Option.map_some])
    (k _ rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- `ldr t, [n, #off]`. -/
theorem wp_ldr {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldr t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_ldr ho hin) (k _ (Upd.setReg _ _ _))

/-- `ldr t, [sp, #off]`. -/
theorem wp_ldrSp {t : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.sp + BitVec.ofNat 32 off) = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t (s.mem.readW a 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.ldrSp t off :: is)) s Q := by
  subst ha
  exact WP.cons (s' := s.setReg t (s.mem.readW _ 32))
    (by simp only [exec, ho, ↓reduceIte, State.load32, hin, Option.map_some]) (k _ (Upd.setReg _ _ _))

/-- `str t, [n, #off]`. -/
theorem wp_str {t n : Reg} {off : Nat} {a : Addr} (ho : off < 4096)
    (ha : State.addr (s.gpr n + BitVec.ofNat 32 off) = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.str t n off :: is)) s Q := by
  subst ha
  exact WP.cons (exec_str ho hout) (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

end

end VG.Arm.Steps
