module

public import VerifiedGarbage.Proof.Mont.X86.CombFrame
public import VerifiedGarbage.Proof.Mont.X86.CombSquares
public import VerifiedGarbage.Proof.Mont.X86.CombColumnControl
import VerifiedGarbage.Proof.Mont.X86.CombAccess
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

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
  have nh := slot_header n 9
  have context32 : 32 ≤ context := by change slot n 9 ≤ context at apart; omega
  have nw := I.ctx.scr.nowrap
  have b5 := L.slot (i := 5) (by decide)
  unfold VG.Impl.Mont.X86.Comb.columnStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons, List.foldr_nil]
  refine WP.seq (WP.mono (combSquares_ok I.ctx (o := 5) (by decide) (by decide) (by decide) (by decide)
    hd hd32 I.value) fun u ⟨Cu, Vu, Ou, Ku⟩ => ?_)
  have Vnext : wordsVal u.mem base (slot n 5) n = columnValue n m g d (i+1) := by
    rw [Vu]
    unfold columnValue
    rw [← Nat.pow_add]
    rw [Nat.mul_add, Nat.mul_one, Nat.add_comm d]
  have Oenc : Outs base (encodeRanges n) t.mem u.mem := Ou.mono (by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [encodeRanges])
  have Hu : w32 u.mem base 28 = 2^i := by
    have H := Ou.val32 (d := 28) (k := 1) (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> left <;> simp [slot, stride] <;> omega) (by decide)
    have equal : w32 u.mem base 28 = w32 t.mem base 28 := by simpa only [val32, Nat.mul_zero, Nat.add_zero] using H
    exact equal.trans I.header
  refine WP.seq (WP.mono (columnAdvance_ok Cu.scr (by omega) hi Hu) fun v ⟨Ov, Hv, ESI, Kv⟩ => ?_)
  have Cv := Cu.outside_keep Kv (by decide) (by decide) Ov (.inr (by simp [slot])) (by decide)
  have Vv : wordsVal v.mem base (slot n 5) n = columnValue n m g d (i+1) :=
    (Ov.wordsVal (.inr (by have := slot_header n 5; omega)) (by omega)).trans Vnext
  have idx : (v.gpr .esi).toNat = 2^(i+1) := by rw [ESI, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (column_bound _ (by omega))]
  obtain ⟨ipos, ilt⟩ := column_index i hi
  have ent := L.entry ilt
  have tablow : context+24*n ≤ entry n (context+16*n) (2^(i+1)) := by
    have := Nat.mul_le_mul_left (8*n) ipos
    simp only [Nat.mul_one] at this
    unfold entry; omega
  refine WP.seq (WP.mono (copyToComb_ok L.positive (hs := Cv.scr) (by omega)
    (by rw [idx]; omega) (.inl (by rw [idx]; omega))) fun w ⟨Ow, Vw, Kw⟩ => ?_)
  rw [idx] at Ow Vw
  have Cw := outside_high_context L Cv Kw (by decide) (by decide) Ow (by omega)
  refine WP.seq (wp_cmpS rfl fun z F Z => WP.block_nil (WP.block_nil ?_))
  have ESIw : w.gpr .esi = BitVec.ofNat 32 (2^(i+1)) := (Kw.1 .esi (by decide)).trans ESI
  have Cz : Context n m base size z :=
    ⟨Cw.scr.of_keeps (F.keeps []) (by decide), Cw.size_le, F.mem ▸ Cw.modulus, Cw.gt_one, F.mem ▸ Cw.inverse⟩
  refine ⟨⟨Cz, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [F.mem, Ow.w32 (by omega) (by decide), Hv]
  · rw [F.mem, high_write_low L Cv.scr (by decide) Ow (by omega), Vv]
  · intro j hj
    rw [F.mem]
    by_cases eq : j=i+1
    · subst j; exact Vw.trans Vv
    · have ji : j ≤ i := by omega
      have jlt : 2^j < 32 := by
        have : ∀ j < 5, 2^j < 32 := by decide
        exact this j (by omega)
      have ej := L.entry jlt
      have unequal : 2^j ≠ 2^(i+1) := by
        exact Nat.ne_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
      rw [Ow.wordsVal (entry_apart n (context+16*n) unequal) (by omega),
        Ov.wordsVal (.inr (by omega)) (by omega), encode_high L I.ctx.scr Oenc (by omega) (by omega)]
      exact I.table j ji
  · have arithmetic : Outs base (columnRanges n context) t.mem u.mem := Ou.mono (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [columnRanges])
    have header := Outs.of_outside Ov (rs := columnRanges n context) (by simp [columnRanges])
    have table : Outs base (columnRanges n context) v.mem w.mem :=
      widen (Outs.of_outside Ow (rs := [(entry n (context+16*n) (2^(i+1)),8*n)]) (by simp)) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨(context+24*n,248*n), by simp [columnRanges], tablow, by omega⟩)
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
  have hdr := slot_header n 9
  have context32 : 32 ≤ context := by change slot n 9 ≤ context at apart; omega
  have nw := C.scr.nowrap
  refine wp_movS rfl fun u U _ => ?_
  have hu := C.scr.of_keeps U.keeps (by decide)
  refine wp_storeS (hu.ea (d := 28) (by omega)) (hu.write (d := 28) (n := 4) (by omega))
    fun t M => WP.block_nil ?_
  have O : Outside base 28 4 s.mem t.mem := by
    rw [M.mem, U.mem]; exact writeW32_outside _ _ _ (by decide)
  have K : Keeps powerClob s t := (U.keeps.mono (by decide)).trans (M.keeps _)
  have Ct := C.outside_keep K (by decide) (by decide) O (.inr (by simp [slot])) (by decide)
  have init : Columns n context size m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0 base s t := by
    refine ⟨Ct, ?_, ?_, ?_, Outs.of_outside O (by simp [columnRanges]), K⟩
    · rw [M.mem, w32_write_self, U.gpr]; rfl
    · rw [O.wordsVal (.inr (by have := slot_header n 5; omega))
        (by have := L.slot (i := 5) (by decide); omega), V]
    · intro j hj
      have eq : j=0 := by omega
      subst j
      have addr : entry n (context+16*n) (2^0) = context+24*n := by simp [entry]; omega
      rw [addr, O.wordsVal (.inr (by omega)) (by omega), T]
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
