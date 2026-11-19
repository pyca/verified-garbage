module

public import VerifiedGarbage.Proof.Mont.X86.CombAccess
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Spec.Rsa
public import VerifiedGarbage.Impl.Mont.X86.ContextSquares
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.PowerInit
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Mont.X86.CombColumnControl`, which this module and modules that import it used -/

section

/-! Public index doubling for the four additional comb columns. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86

private theorem doubled : ∀ i < 4,
    BitVec.ofNat 32 (2^i) + BitVec.ofNat 32 (2^i) = BitVec.ofNat 32 (2^(i+1)) := by decide

theorem column_bound : ∀ i < 5, 2^i < 2^32 := by decide

theorem columnAdvance_ok {s : State} {base : Addr} {size i : Nat}
    (hs : Scr s base size) (hz : 32 ≤ size) (hi : i < 4) (h : w32 s.mem base 28 = 2^i) :
    WP isa VG.Impl.Mont.X86.Comb.columnAdvance s fun t =>
      Outside base 28 4 s.mem t.mem ∧ w32 t.mem base 28 = 2^(i+1) ∧
      t.gpr .esi = BitVec.ofNat 32 (2^(i+1)) ∧ Keeps [.esi] s t := by
  unfold VG.Impl.Mont.X86.Comb.columnAdvance
  refine wp_movS (readSrc_sc hs hz) fun u U _ => wp_addS rfl fun v V _ => ?_
  have reg : v.gpr .esi = BitVec.ofNat 32 (2^(i+1)) := by
    rw [V.gpr, U.gpr]
    have read : s.mem.readW (off base 28) 32 = BitVec.ofNat 32 (2^i) := by
      apply BitVec.eq_of_toNat_eq
      change w32 s.mem base 28 = _
      rw [h, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (column_bound i (by omega_using [hi]))).symm
    rw [read, doubled i hi]
  have K := U.keeps.trans V.keeps
  have hv := hs.of_keeps K (by decide)
  refine wp_storeS (hv.ea (d := 28) (by omega_using [hz])) (hv.write hz) fun t M => WP.block_nil ?_
  refine ⟨?_, ?_, M.gpr ▸ reg, K.trans (M.keeps _)⟩
  · rw [M.mem, V.mem, U.mem]; exact writeW32_outside _ _ _ (by decide)
  · rw [M.mem, w32_write_self, reg, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (column_bound (i+1) (by omega_using [hi]))

theorem column_end : ∀ i < 4,
    (BitVec.ofNat 32 (2^(i+1)) - 16#32 == 0) = decide (i+1 = 4) := by decide

theorem column_index : ∀ i < 4, 0 < 2^(i+1) ∧ 2^(i+1) < 32 := by decide

end VG.Proof.Mont.X86.Comb

end

end

/-! ### `Mont.X86.CombSquares`, which this module and modules that import it used -/

section

/-! Repeated Montgomery squaring with the shared fixed-base comb encoding. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86.PublicRt (countLoop)

theorem combSquares_ok {s : State} {base : Addr} {n size m o g E count : Nat}
    (C : Context n m base size s) (ho : o < 9) (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ho2 : o ≠ 2)
    (hc : 0 < count) (hc32 : count < 2^32)
    (V : wordsVal s.mem base (slot n o) n = Spec.Rsa.powMod g E m * 2^(64*n) % m) :
    WP isa (VG.Impl.Mont.X86.Dynamic.repeatSquares n o count) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base (slot n o) n = Spec.Rsa.powMod g (2^count*E) m * 2^(64*n) % m ∧
      Outs base [(slot n o, 8*n), (slot n 1, 8*n), (slot n 2, 16*n+4)] s.mem t.mem ∧
      Keeps powerClob s t := by
  let ranges := [(slot n o, 8*n), (slot n 1, 8*n), (slot n 2, 16*n+4)]
  let I (i : Nat) (t : State) : Prop :=
    Context n m base size t ∧ t.gpr .esi = BitVec.ofNat 32 (count-i) ∧
    wordsVal t.mem base (slot n o) n = Spec.Rsa.powMod g (2^i*E) m * 2^(64*n) % m ∧
    Outs base ranges s.mem t.mem ∧ Keeps powerClob s t
  unfold VG.Impl.Mont.X86.Dynamic.repeatSquares repeatSquaresWith
  refine WP.seq (wp_movS rfl fun u U _ => WP.block_nil ?_)
  have K : Keeps powerClob s u := U.keeps.mono (by decide)
  have init : I 0 u := by
    refine ⟨⟨C.scr.of_keeps K (by decide), C.size_le, U.mem ▸ C.modulus, C.gt_one, U.mem ▸ C.inverse⟩,
      U.gpr, ?_, U.mem ▸ Outs.refl _ _ _, K⟩
    simpa only [U.mem, Nat.pow_zero, Nat.one_mul] using V
  refine WP.mono (countLoop hc I ?_ init) fun t ⟨Ct, _, Vt, Ot, Kt⟩ => ⟨Ct, Vt, Ot, Kt⟩
  rintro i t hi ⟨Ct, counter, value, O, Kt⟩
  unfold squareStepWith
  refine WP.seq (WP.mono (context_mul_ok Ct ho ho ho ho0 ho1 ho2 ho2 ho2
    (by rw [value]; exact Nat.mod_lt _ (by have := Ct.gt_one; omega_using [this])) ho1 ho1)
    fun v ⟨Cv, Kv, lt, product⟩ => ?_)
  have Vv : wordsVal v.mem base (slot n o) n = Spec.Rsa.powMod g (2^(i+1)*E) m * 2^(64*n) % m := by
    have step := VG.Proof.Rsa.FixedBaseComb.mont_square_encoded Ct.coprime lt value product
    simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using step
  have Ov : Outs base ranges t.mem v.mem := by
    have length : accLen (contextMod n) = 16*n+4 := context_accLen n
    have frame := Kv.mem
    change Outs base [(slot n o, 8*n), (slot n 1, 8*n), (slot n 2, accLen (contextMod n))] t.mem v.mem at frame
    simpa only [length] using frame
  have counterv : v.gpr .esi = BitVec.ofNat 32 (count-i) := (Kv.gpr .esi (by decide)).trans counter
  refine wp_subS rfl fun w UW _ => wp_cmpS rfl fun z F Z => WP.block_nil ?_
  have mem : z.mem = v.mem := F.mem.trans UW.mem
  have keep : Keeps powerClob v z := (UW.keeps.mono (by decide)).trans (F.keeps _)
  have Cz : Context n m base size z :=
    ⟨Cv.scr.of_keeps keep (by decide), Cv.size_le, mem ▸ Cv.modulus, Cv.gt_one, mem ▸ Cv.inverse⟩
  refine ⟨⟨Cz, ?_, mem ▸ Vv, mem ▸ O.trans Ov,
    Kt.trans (((OpKeep.keeps Kv).mono (by decide)).trans keep)⟩, ?_⟩
  · rw [F.gpr, UW.gpr, counterv, counter_sub (by omega_using [hc32]) (by omega_using [hi])]
    congr 1
  · rw [Z, UW.gpr, counterv, counter_sub (by omega_using [hc32]) (by omega_using [hi]), counter_zero (by omega_using [hc32]) (by omega_using [hi])]
    simp only [show (count-i = 1) ↔ i+1 = count by omega_using []]

end VG.Proof.Mont.X86.Dynamic

end

end

/-! Construct the five single-tooth entries by repeatedly squaring one residue. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

def columnValue (n m g d i : Nat) : Nat := Spec.Rsa.powMod g (2^(d*i)) m * 2^(64*n) % m

def columnRanges (n context : Nat) : List (Nat × Nat) :=
  [(slot n 5,8*n), (slot n 1,8*n), (slot n 2,16*n+4), (28,4), (context+24*n,248*n)]

structure Columns (n context size m g d i : Nat) (base : Addr) (s t : State) : Prop where
  ctx : Context n m base size t
  header : w32 t.mem base 28 = 2^i
  value : wordsVal t.mem base (slot n 5) n = columnValue n m g d i
  table : ∀ j ≤ i, wordsVal t.mem base (entry n (context+16*n) (2^j)) n = columnValue n m g d j
  mem : Outs base (columnRanges n context) s.mem t.mem
  keeps : Keeps powerClob s t

theorem columnStep_ok {n context size m g d i : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (I : Columns n context size m g d i base s t)
    (hi : i < 4) (hd : 0 < d) (hd32 : d < 2^32) :
    WP isa (VG.Impl.Mont.X86.Comb.columnStep n d (context+16*n)) t fun z =>
      Columns n context size m g d (i+1) base s z ∧ z.zf = some (decide (i+1=4)) := by
  have bound := L.bound
  have apart := L.apart
  obtain nh := slot_header n 9
  obtain context32 : 32 ≤ context := by change slot n 9 ≤ context at apart; omega_arith
  have nw := I.ctx.scr.nowrap
  obtain b5 := L.slot (i := 5) (by decide)
  unfold VG.Impl.Mont.X86.Comb.columnStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (combSquares_ok I.ctx (o := 5) (by decide) (by decide) (by decide) (by decide)
    hd hd32 I.value) fun u ⟨Cu, Vu, Ou, Ku⟩ => ?_)
  obtain Vnext : wordsVal u.mem base (slot n 5) n = columnValue n m g d (i+1) := by
    rw [Vu]
    unfold columnValue
    rw [← Nat.pow_add]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm d]
  obtain Oenc : Outs base (encodeRanges n) t.mem u.mem := Ou.mono (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [encodeRanges])
  obtain Hu : w32 u.mem base 28 = 2^i := by
    obtain H := Ou.val32 (d := 28) (k := 1) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> left <;> simp [slot, stride] <;> omega_arith) (by decide)
    obtain equal : w32 u.mem base 28 = w32 t.mem base 28 := by simpa only [val32, Nat.mul_zero, Nat.add_zero] using H
    exact equal.trans I.header
  refine WP.seq (WP.mono (columnAdvance_ok Cu.scr (by omega_arith) hi Hu) fun v ⟨Ov, Hv, ESI, Kv⟩ => ?_)
  obtain Cv := Cu.outside_keep Kv (by decide) (by decide) Ov (.inr (by simp [slot])) (by decide)
  obtain Vv : wordsVal v.mem base (slot n 5) n = columnValue n m g d (i+1) :=
    (Ov.wordsVal (.inr (by have := slot_header n 5; omega_arith)) (by omega_arith)).trans Vnext
  obtain idx : (v.gpr .esi).toNat = 2^(i+1) := by rw [ESI, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (column_bound _ (by omega_arith))]
  obtain ⟨ipos, ilt⟩ := column_index i hi
  obtain ent := L.entry ilt
  obtain tablow : context+24*n ≤ entry n (context+16*n) (2^(i+1)) := by
    have := Nat.mul_le_mul_left (8*n) ipos
    simp only [Nat.mul_one] at this
    unfold entry; omega_arith
  refine WP.seq (WP.mono (copyToComb_ok L.positive (hs := Cv.scr) (by omega_arith)
    (by rw [idx]; omega_arith) (.inl (by rw [idx]; omega_arith))) fun w ⟨Ow, Vw, Kw⟩ => ?_)
  rw [idx] at Ow Vw
  obtain Cw := outside_high_context L Cv Kw (by decide) (by decide) Ow (by omega_arith)
  refine WP.seq (wp_cmpS rfl fun z F Z => WP.block_nil (WP.block_nil ?_))
  obtain ESIw : w.gpr .esi = BitVec.ofNat 32 (2^(i+1)) := (Kw.1 .esi (by decide)).trans ESI
  obtain Cz : Context n m base size z :=
    ⟨Cw.scr.of_keeps (F.keeps []) (by decide), Cw.size_le, F.mem ▸ Cw.modulus, Cw.gt_one, F.mem ▸ Cw.inverse⟩
  refine ⟨⟨Cz, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [F.mem, Ow.w32 (by omega_arith) (by decide), Hv]
  · rw [F.mem, high_write_low L Cv.scr (by decide) Ow (by omega_arith), Vv]
  · intro j hj
    rw [F.mem]
    by_cases eq : j=i+1
    · subst j; exact Vw.trans Vv
    · have ji : j ≤ i := by omega_arith
      obtain jlt : 2^j < 32 := by
        have : ∀ j < 5, 2^j < 32 := by decide
        exact this j (by omega_arith)
      obtain ej := L.entry jlt
      obtain unequal : 2^j ≠ 2^(i+1) := by
        exact Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide) (by omega_arith))
      rw [Ow.wordsVal (entry_apart n (context+16*n) unequal) (by omega_arith),
        Ov.wordsVal (.inr (by omega_arith)) (by omega_arith), encode_high L I.ctx.scr Oenc (by omega_arith) (by omega_arith)]
      exact I.table j ji
  · have arithmetic : Outs base (columnRanges n context) t.mem u.mem := Ou.mono (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [columnRanges])
    obtain header := Outs.of_outside Ov (rs := columnRanges n context) (by simp [columnRanges])
    obtain table : Outs base (columnRanges n context) v.mem w.mem :=
      widen (Outs.of_outside Ow (rs := [(entry n (context+16*n) (2^(i+1)),8*n)]) (by simp)) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨(context+24*n,248*n), by simp [columnRanges], tablow, by omega_arith⟩)
    rw [F.mem]; exact ((I.mem.trans arithmetic).trans header).trans table
  · exact (((I.keeps.trans Ku).trans (Kv.mono (by decide))).trans (Kw.mono (by decide))).trans (F.keeps _)
  · rw [Z, ESIw, column_end i hi]

/-- Four loop iterations produce every single-tooth entry, using one shared
multiplication body regardless of the exponent storage width. -/
theorem buildColumns_initial {n e context size m g : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (V : wordsVal s.mem base (slot n 5) n = columnValue n m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0)
    (T : wordsVal s.mem base (context+24*n) n = columnValue n m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0) :
    WP isa (.block [.mov .eax (VG.Impl.Mont.X86.Comb.imm 1), .store (sc 28) .eax]) s
      (Columns n context size m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0 base s) := by
  have bound := L.bound
  have apart := L.apart
  obtain hdr := slot_header n 9
  obtain context32 : 32 ≤ context := by change slot n 9 ≤ context at apart; omega_using [hdr, apart]
  have nw := C.scr.nowrap
  refine wp_movS rfl fun u U _ => ?_
  obtain hu := C.scr.of_keeps U.keeps (by decide)
  refine wp_storeS (hu.ea (d := 28) (by omega_using [bound, context32])) (hu.write (d := 28) (n := 4) (by omega_using [bound, context32]))
    fun t M => WP.block_nil ?_
  obtain O : Outside base 28 4 s.mem t.mem := by
    rw [M.mem, U.mem]; exact writeW32_outside _ _ _ (by decide)
  obtain K : Keeps powerClob s t := (U.keeps.mono (by decide)).trans (M.keeps _)
  obtain Ct := C.outside_keep K (by decide) (by decide) O (.inr (by simp [slot])) (by decide)
  obtain init : Columns n context size m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0 base s t := by
    refine ⟨Ct, ?_, ?_, ?_, Outs.of_outside O (by simp [columnRanges]), K⟩
    · rw [M.mem, w32_write_self, U.gpr]; rfl
    · rw [O.wordsVal (.inr (by have := slot_header n 5; omega_using [this]))
        (by have := L.slot (i := 5) (by decide); omega_using [bound, nw, this]), V]
    · intro j hj
      obtain eq : j=0 := by omega_using [hj]
      subst j
      obtain addr : entry n (context+16*n) (2^0) = context+24*n := by simp [entry]; omega_using []
      rw [addr, O.wordsVal (.inr (by omega_using [context32])) (by omega_using [bound, nw]), T]
  exact init

theorem buildColumns_ok {n e context size m g : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (hd : 0 < Spec.Rsa.FixedBaseComb.rows (32*e)) (hd32 : Spec.Rsa.FixedBaseComb.rows (32*e) < 2^32)
    (V : wordsVal s.mem base (slot n 5) n = columnValue n m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0)
    (T : wordsVal s.mem base (context+24*n) n = columnValue n m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0) :
    WP isa (VG.Impl.Mont.X86.Comb.buildColumns n e context) s
      (Columns n context size m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 4 base s) := by
  unfold VG.Impl.Mont.X86.Comb.buildColumns
  refine WP.seq (WP.mono (buildColumns_initial L C V T) fun t init => ?_)
  exact VG.Proof.Bignum.X86.PublicRt.countLoop (by decide)
    (Columns n context size m g (Spec.Rsa.FixedBaseComb.rows (32*e)) · base s)
    (fun i t hi I => columnStep_ok L I hi hd hd32) init

end VG.Proof.Mont.X86.Comb
