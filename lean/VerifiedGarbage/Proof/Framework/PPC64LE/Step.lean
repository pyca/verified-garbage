module

public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec

/-!
# PPC64LE: weakest preconditions one instruction at a time

Untrusted: everything here is checked by Lean. Each `wp_*` lemma runs the
first instruction of a block and hands the continuation the next state,
described by `Upd` (one register written) or `Mupd` (the memory replaced)
rather than by its structure, so that a proof never unfolds `State.write`.
-/

@[expose] public section

namespace VG.PPC64LE

/-- `s'` is `s` with register `d` set to `v`. -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.write (s : State) (d : Reg) (v : BitVec 64) : Upd s (s.write d v) d v :=
  ⟨by simp [State.write], fun r h => by simp [State.write, h], rfl, rfl, rfl⟩

/-- `s'` is `s` with memory `m`. -/
structure Mupd (s s' : State) (m : Mem) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_addi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _))

theorem wp_subi {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm ≤ 2 ^ 15)
    (k : ∀ s', Upd s s' d (s.gpr n - BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.subi d n imm :: is)) s Q :=
  WP.cons (exec_subi hn h) (k _ (Upd.write _ _ _))

theorem wp_li {d : Reg} {imm : Nat} (h : imm < 2 ^ 15)
    (k : ∀ s', Upd s s' d (BitVec.ofNat 64 imm) → WP isa (.block is) s' Q) :
    WP isa (.block (.li d imm :: is)) s Q :=
  WP.cons (exec_li h) (k _ (Upd.write _ _ _))

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

theorem wp_and {d n m : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n &&& s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .and d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

/-- `mr d, n` (`or d, n, n`). -/
theorem wp_mr {d n : Reg}
    (k : ∀ s', Upd s s' d (s.gpr n) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n n :: is)) s Q :=
  WP.cons exec_logic (k _ (by simpa using Upd.write s d (s.gpr n ||| s.gpr n)))

theorem wp_lsr {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n >>> sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsr .d d n sh :: is)) s Q :=
  WP.cons (exec_lsr_d h) (k _ (Upd.write _ _ _))

theorem wp_lsl {d n : Reg} {sh : Nat} (h : sh < 64)
    (k : ∀ s', Upd s s' d (s.gpr n <<< sh) → WP isa (.block is) s' Q) :
    WP isa (.block (.lsl d n sh :: is)) s Q :=
  WP.cons (exec_lsl h) (k _ (Upd.write _ _ _))

theorem wp_rotr_w {d n : Reg} {sh : Nat} (h : sh < 32)
    (k : ∀ s', Upd s s' d ((((s.gpr n).setWidth 32).rotateRight sh).setWidth 64) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.rotr .w d n sh :: is)) s Q :=
  WP.cons (exec_rotr_w h) (k _ (Upd.write _ _ _))

theorem wp_std {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', Mupd s s' (s.mem.writeW a (s.gpr t)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .d t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr t) }) ?_ (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_store_d hn ho (by rw [ha]; exact hout), ha]

theorem wp_stw {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW a ((s.gpr t).setWidth 32)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store .w t n off :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr t).setWidth 32) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_store_w hn ho (by rw [ha]; exact hout), ha]

theorem wp_ld {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15 ∧ off % 4 = 0)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Upd s s' t (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .d t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t (s.mem.readW a 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_d hn ho (by rw [ha]; exact hin), ha]

theorem wp_lwz {t n : Reg} {off : Nat} {a : Addr} (hn : n ≠ .r0) (ho : off < 2 ^ 15)
    (ha : s.gpr n + BitVec.ofNat 64 off = a) (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', Upd s s' t ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.load .w t n off :: is)) s Q := by
  refine WP.cons (s' := s.write t ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.write _ _ _))
  rw [exec_load_w hn ho (by rw [ha]; exact hin), ha]

/-- `lwbrx t, a, b`. -/
theorem wp_lwbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hin : InRegions (s.rd ++ s.wr) ea 4)
    (k : ∀ s', Upd s s' t ((rev32 (s.mem.readW ea 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.loadRev .w t a b :: is)) s Q := by
  refine WP.cons (s' := s.write t ((rev32 (s.mem.readW ea 32)).setWidth 64)) ?_
    (k _ (Upd.write _ _ _))
  rw [exec_loadRev_w hn (by rw [hea]; exact hin), hea]

/-- `stwbrx t, a, b`. -/
theorem wp_stwbrx {t a b : Reg} {ea : Addr} (hn : a ≠ .r0) (hea : s.gpr a + s.gpr b = ea)
    (hout : InRegions s.wr ea 4)
    (k : ∀ s', Mupd s s' (s.mem.writeW ea (rev32 ((s.gpr t).setWidth 32))) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.storeRev .w t a b :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW ea (rev32 ((s.gpr t).setWidth 32)) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl⟩)
  rw [exec_storeRev_w hn (by rw [hea]; exact hout), hea]

theorem wp_nil {s : State} {Q : State → Prop} (h : Q s) : WP isa (.block []) s Q :=
  WP.of_runBlock ⟨s, runBlock_nil, h⟩

end

/-! ## Branch conditions -/

theorem eval_zero (s : State) (r : Reg) : isa.eval (.zero .d r) s = some (s.gpr r == 0) := by
  change VG.PPC64LE.eval (.zero .d r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .d r) s = some (s.gpr r != 0) := by
  change VG.PPC64LE.eval (.nonzero .d r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem eval_zero_ofNat (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.zero .d r) s = some (decide (k = 0)) := by
  rw [eval_zero, h, ofNat_beq_zero hk]

theorem eval_nonzero_ofNat' (s : State) (r : Reg) {k : Nat} (hk : k < 2 ^ 64)
    (h : s.gpr r = BitVec.ofNat 64 k) : isa.eval (.nonzero .d r) s = some (decide (k ≠ 0)) := by
  rw [eval_nonzero, h, bne, ofNat_beq_zero hk]
  simp

end VG.PPC64LE
