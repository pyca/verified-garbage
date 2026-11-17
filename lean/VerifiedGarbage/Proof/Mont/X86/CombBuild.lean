module

import VerifiedGarbage.Proof.Mont.X86.CombStart
public import VerifiedGarbage.Proof.Mont.X86.CombColumns
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
public import VerifiedGarbage.Proof.Mont.X86.CombFrame
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
public import VerifiedGarbage.Proof.Mont.X86.CombTableState
import VerifiedGarbage.Proof.Mont.X86.CombAccess
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops
public import VerifiedGarbage.Impl.Mont.X86.CombTable
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Spec.Rsa.FixedBaseComb

/-! ### `Mont.X86.CombSubsets`, which this module and modules that import it used -/

section

/-! ### `Mont.X86.CombSubsetControl`, which this module and modules that import it used -/

section

/-! ### `Rsa.FixedBaseCombSubset`, which this module and modules that import it used -/

section

/-! The low-bit subset recurrence used by a compact comb-table builder.
The finite index arithmetic is independent of modulus, base and word width. -/

@[expose] public section
namespace VG.Proof.Rsa.FixedBaseComb
open VG.Spec.Rsa.FixedBaseComb (exponent)

/-- Isolate the least set bit using the same 32-bit operations as the code. -/
def lowTooth (a : Nat) : Nat :=
  ((0 - BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a).toNat

private theorem lowTooth_coeff : ∀ a < 32, ∀ j < 5,
    a / 2^j % 2 = (a - lowTooth a) / 2^j % 2 + lowTooth a / 2^j % 2 := by
  decide

/-- Both input table entries precede the current entry, except the already
initialized single-tooth entry. The zero entry supplies Montgomery one. -/
theorem lowTooth_bounds : ∀ a < 32, 0 < a →
    0 < lowTooth a ∧ lowTooth a ≤ a ∧ a - lowTooth a < a ∧
    (lowTooth a = 1 ∨ lowTooth a = 2 ∨ lowTooth a = 4 ∨
      lowTooth a = 8 ∨ lowTooth a = 16) := by
  decide

/-- Multiplying the low-tooth entry by the remaining-subset entry gives
exactly the existing RSA comb table exponent. -/
theorem exponent_lowTooth (bits a : Nat) (ha : a < 32) :
    exponent bits a = exponent bits (a - lowTooth a) + exponent bits (lowTooth a) := by
  simp only [exponent, VG.Spec.Rsa.FixedBaseComb.teeth, List.range_succ, List.range_zero,
    List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rw [lowTooth_coeff a ha 0 (by decide), lowTooth_coeff a ha 1 (by decide),
    lowTooth_coeff a ha 2 (by decide), lowTooth_coeff a ha 3 (by decide),
    lowTooth_coeff a ha 4 (by decide)]
  simp only [Nat.add_mul]
  ac_rfl

end VG.Proof.Rsa.FixedBaseComb

end

end

/-! Public low-tooth and remaining-subset indices for the table builder. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.FixedBaseComb (lowTooth)

private theorem indices : ∀ a < 32,
    ((0#32-BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a).toNat = lowTooth a ∧
    (BitVec.ofNat 32 a - ((0#32-BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a)).toNat = a-lowTooth a := by decide

theorem subsetIndices_ok {s : State} {base : Addr} {size a : Nat}
    (hs : Scr s base size) (hz : 32 ≤ size) (ha : a < 32) (count : s.gpr .esi = BitVec.ofNat 32 a) :
    WP isa VG.Impl.Mont.X86.Comb.subsetIndices s fun t =>
      Outs base [(28,4),(4,4)] s.mem t.mem ∧ w32 t.mem base 28 = lowTooth a ∧
      w32 t.mem base 4 = a-lowTooth a ∧ Keeps [.eax,.edx] s t := by
  unfold VG.Impl.Mont.X86.Comb.subsetIndices
  refine wp_movS rfl fun u₁ U₁ _ => wp_subS rfl fun u₂ U₂ _ => wp_logicS (.inl rfl) rfl fun u₃ U₃ => ?_
  have K3 : Keeps [.eax,.edx] s u₃ := ((U₁.keeps.mono (by decide)).widen U₂.keeps).widen U₃.keeps
  have H3 := hs.of_keeps K3 (by decide)
  have low : u₃.gpr .eax = ((0#32-BitVec.ofNat 32 a) &&& BitVec.ofNat 32 a) := by
    rw [U₃.gpr, U₂.gpr, U₁.gpr, U₂.other _ (by decide), U₁.other _ (by decide), count]
    rfl
  refine wp_storeS (H3.ea (d := 28) (by omega_using [hz])) (H3.write (d := 28) (n := 4) hz) fun u₄ M₄ => ?_
  refine wp_movS rfl fun u₅ U₅ _ => wp_subS rfl fun u₆ U₆ _ => ?_
  have K6 : Keeps [.eax,.edx] s u₆ := ((K3.trans (M₄.keeps _)).widen U₅.keeps).widen U₆.keeps
  have H6 := hs.of_keeps K6 (by decide)
  refine wp_storeS (H6.ea (d := 4) (by omega_using [hz])) (H6.write (d := 4) (n := 4) (by omega_using [hz])) fun t M₇ => WP.block_nil ?_
  have mem : u₆.mem = u₃.mem.writeW (off base 28) (u₃.gpr .eax) := by rw [U₆.mem,U₅.mem,M₄.mem]
  have initial : u₃.mem = s.mem := U₃.mem.trans (U₂.mem.trans U₁.mem)
  have O28 : Outside base 28 4 s.mem u₆.mem := by rw [mem,initial]; exact writeW32_outside _ _ _ (by decide)
  have O4 : Outside base 4 4 u₆.mem t.mem := by rw [M₇.mem]; exact writeW32_outside _ _ _ (by decide)
  refine ⟨(Outs.of_outside O28 (by simp)).trans (Outs.of_outside O4 (by simp)), ?_, ?_, K6.trans (M₇.keeps _)⟩
  · rw [O4.w32 (by decide) (by decide), mem, w32_write_self, low]
    exact (indices a ha).1
  · rw [M₇.mem, w32_write_self, U₆.gpr, U₅.gpr, M₄.gpr, K3.1 .esi (by decide),
      U₅.other _ (by decide), M₄.gpr, low, count]
    exact (indices a ha).2

theorem subsetLow_ok {s : State} {base : Addr} {size : Nat}
    (hs : Scr s base size) (hz : 32 ≤ size) :
    WP isa VG.Impl.Mont.X86.Comb.subsetLow s fun t =>
      Outside base 4 4 s.mem t.mem ∧ w32 t.mem base 4 = w32 s.mem base 28 ∧ Keeps [.eax] s t := by
  unfold VG.Impl.Mont.X86.Comb.subsetLow VG.Impl.Mont.X86.Dynamic.windowOffset
  refine wp_movS (readSrc_sc hs hz) fun u U _ => ?_
  have hu := hs.of_keeps U.keeps (by decide)
  refine wp_storeS (hu.ea (d := 4) (by omega_using [hz])) (hu.write (d := 4) (n := 4) (by omega_using [hz])) fun t M => WP.block_nil ?_
  refine ⟨?_, ?_, U.keeps.trans (M.keeps _)⟩
  · rw [M.mem,U.mem]; exact writeW32_outside _ _ _ (by decide)
  · rw [M.mem,w32_write_self,U.gpr]

end VG.Proof.Mont.X86.Comb

end

end

/-! Complete the comb table by adding one low tooth to each preceding subset. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Proof.Rsa.FixedBaseComb (lowTooth)

def tooth (j : Nat) : Prop := j=1 ∨ j=2 ∨ j=4 ∨ j=8 ∨ j=16

def knownSubset (a j : Nat) : Prop := j<a ∨ tooth j

def subsetRanges (n context : Nat) : List (Nat × Nat) :=
  [(4,4),(28,4),(slot n 5,8*n),(slot n 6,8*n),(slot n 7,8*n),
    (slot n 1,8*n),(slot n 2,16*n+4),(context+24*n,248*n)]

structure Subsets (n context size m g bits a : Nat) (base : Addr) (s t : State) : Prop where
  ctx : Context n m base size t
  count : t.gpr .esi = BitVec.ofNat 32 a
  table : TableAt n context m g bits base (knownSubset a) t.mem
  mem : Outs base (subsetRanges n context) s.mem t.mem
  keeps : Keeps powerClob s t

theorem subsetStep_ok {n context size m g bits a : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (I : Subsets n context size m g bits a base s t)
    (ha : 0<a) (ha32 : a<32) :
    WP isa (VG.Impl.Mont.X86.Comb.subsetStep n (context+16*n)) t fun z =>
      Subsets n context size m g bits (a+1) base s z ∧ z.zf = some (decide (a+1=32)) := by
  have bound := L.bound
  have apart := L.apart
  obtain hdr := slot_header n 9
  obtain context32 : 32 ≤ context := by change slot n 9 ≤ context at apart; omega_arith
  have nw := I.ctx.scr.nowrap
  obtain b5 := L.slot (i := 5) (by decide)
  obtain b6 := L.slot (i := 6) (by decide)
  obtain b7 := L.slot (i := 7) (by decide)
  obtain h5 := slot_header n 5
  obtain h6 := slot_header n 6
  obtain h7 := slot_header n 7
  obtain ⟨loPos,loLe,remLt,loTooth⟩ := VG.Proof.Rsa.FixedBaseComb.lowTooth_bounds a ha32 ha
  obtain loLt : lowTooth a < 32 := by omega_arith
  unfold VG.Impl.Mont.X86.Comb.subsetStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (subsetIndices_ok I.ctx.scr (by omega_arith) ha32 I.count) fun u ⟨Ou,Hu,Vu,Ku⟩ => ?_)
  obtain Cu := I.ctx.outs_keep Ku (by decide) (by decide) Ou (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> right <;> simp [slot]) (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> decide)
  obtain Tu := I.table.outs L I.ctx.scr Ou (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> left <;> omega_arith)
  refine WP.seq (WP.mono (select_table_ok L Cu Tu (o := 6) (by decide) (by decide)
    (by rw [Vu]; omega_arith) (by rw [Vu]; exact .inl remLt)) fun v ⟨Cv,Tv,Vv,Ov,Kv⟩ => ?_)
  rw [Vu] at Vv
  obtain Hv : w32 v.mem base 28 = lowTooth a := (Ov.w32 (by omega_arith) (by decide)).trans Hu
  refine WP.seq (WP.mono (subsetLow_ok Cv.scr (by omega_arith)) fun w ⟨Ow,Vw,Kw⟩ => ?_)
  obtain Cw := Cv.outside_keep Kw (by decide) (by decide) Ow (.inr (by simp [slot])) (by decide)
  obtain Tw := Tv.outside L Cv.scr Ow (.inl (by omega_arith))
  obtain Vw' : w32 w.mem base 4 = lowTooth a := Vw.trans Hv
  obtain leftW : wordsVal w.mem base (slot n 6) n = tableValue n m g bits (a-lowTooth a) :=
    (Ow.wordsVal (.inr (by omega_arith)) (by omega_arith)).trans Vv
  refine WP.seq (WP.mono (select_table_ok L Cw Tw (o := 5) (by decide) (by decide)
    (by rw [Vw']; exact loLt) (by rw [Vw']; exact .inr loTooth)) fun x ⟨Cx,Tx,Vx,Ox,Kx⟩ => ?_)
  rw [Vw'] at Vx
  obtain sep56 := slot_sep (n := n) (i := 6) (j := 5) (by decide)
  obtain leftX : wordsVal x.mem base (slot n 6) n = tableValue n m g bits (a-lowTooth a) :=
    (Ox.wordsVal (by unfold stride at sep56; omega_arith) (by omega_arith)).trans leftW
  refine WP.seq (WP.mono (context_mul_ok Cx (o := 7) (a := 6) (b := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Vx]; exact Nat.mod_lt _ (by have := Cx.gt_one; omega_arith))) fun y ⟨Cy,Ky,lty,Vy⟩ => ?_)
  obtain Ty := Tx.op L Cx (by decide) Ky
  obtain value : wordsVal y.mem base (slot n 7) n = tableValue n m g bits a := by
    obtain product := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded Cx.coprime lty leftX Vx Vy
    unfold tableValue
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_lowTooth bits a ha32]
    exact product
  obtain esiy : y.gpr .esi = BitVec.ofNat 32 a := by
    rw [Ky.gpr .esi (by decide),Kx.1 .esi (by decide),Kw.1 .esi (by decide),Kv.1 .esi (by decide),Ku.1 .esi (by decide),I.count]
  obtain idx : (y.gpr .esi).toNat = a := by rw [esiy,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_arith)]
  obtain ent := L.entry ha32
  obtain low : context+24*n ≤ entry n (context+16*n) a := by
    have := Nat.mul_le_mul_left (8*n) ha
    simp only [Nat.mul_one] at this
    unfold entry; omega_arith
  refine WP.seq (WP.mono (copyToComb_ok Cy.scr L.positive (by omega_arith) (by rw [idx]; omega_arith)
    (.inl (by rw [idx]; omega_arith))) fun f ⟨Of,Vf,Kf⟩ => ?_)
  rw [idx] at Of Vf
  obtain Cf := outside_high_context L Cy Kf (by decide) (by decide) Of (by omega_arith)
  obtain Tf : TableAt n context m g bits base (knownSubset (a+1)) f.mem := by
    intro j hj hk
    by_cases same : j=a
    · subst j; exact Vf.trans value
    · have ej := L.entry hj
      rw [Of.wordsVal (entry_apart n (context+16*n) same) (by omega_arith)]
      apply Ty j hj
      rcases hk with before | tooth
      · left; omega_arith
      · right; exact tooth
  refine WP.seq (wp_addS rfl fun q U _ => wp_cmpS rfl fun z F Z => WP.block_nil (WP.block_nil ?_))
  obtain esif : f.gpr .esi = BitVec.ofNat 32 a := (Kf.1 .esi (by decide)).trans esiy
  obtain count : z.gpr .esi = BitVec.ofNat 32 (a+1) := by
    rw [F.gpr,U.gpr,esif]
    exact (BitVec.ofNat_add a 1).symm
  obtain M : z.mem = f.mem := F.mem.trans U.mem
  obtain Klast : Keeps powerClob f z := (U.keeps.mono (by decide)).trans (F.keeps _)
  obtain Cz : Context n m base size z :=
    ⟨Cf.scr.of_keeps Klast (by decide),Cf.size_le,M ▸ Cf.modulus,Cf.gt_one,M ▸ Cf.inverse⟩
  refine ⟨⟨Cz,count,M ▸ Tf,?_,?_⟩,?_⟩
  · have ou : Outs base (subsetRanges n context) t.mem u.mem := Ou.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [subsetRanges])
    obtain ov := Outs.of_outside Ov (rs := subsetRanges n context) (by simp [subsetRanges])
    obtain ow := Outs.of_outside Ow (rs := subsetRanges n context) (by simp [subsetRanges])
    obtain ox := Outs.of_outside Ox (rs := subsetRanges n context) (by simp [subsetRanges])
    obtain oy : Outs base (subsetRanges n context) x.mem y.mem := Ky.mem.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [subsetRanges,contextMod,accLen,words] <;> omega_arith)
    obtain of : Outs base (subsetRanges n context) y.mem f.mem :=
      widen (Outs.of_outside Of (rs := [(entry n (context+16*n) a,8*n)]) (by simp)) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨(context+24*n,248*n),by simp [subsetRanges],low,by omega_arith⟩)
    rw [M]
    exact ((((((I.mem.trans ou).trans ov).trans ow).trans ox).trans oy).trans of)
  · have k1 := I.keeps.trans (Ku.mono (by decide))
    obtain k2 := k1.trans (Kv.mono (by decide))
    obtain k3 := k2.trans (Kw.mono (by decide))
    obtain k4 := k3.trans (Kx.mono (by decide))
    obtain k5 := k4.trans ((OpKeep.keeps Ky).mono (by decide))
    exact (k5.trans (Kf.mono (by decide))).trans Klast
  · rw [Z,U.gpr,esif,← BitVec.ofNat_add]
    obtain finite : ∀ a < 32, (BitVec.ofNat 32 (a+1)-32#32 == 0) = decide (a+1=32) := by decide
    rw [finite a ha32]

/-- Fill all 31 nonzero entries from their lower subsets and single teeth. -/
theorem buildSubsets_initial {n context size m g bits : Nat} {base : Addr} {s : State}
    (C : Context n m base size s)
    (T : TableAt n context m g bits base (knownSubset 1) s.mem) :
    WP isa (.block [.mov .esi (VG.Impl.Mont.X86.Comb.imm 1)]) s
      (Subsets n context size m g bits 1 base s) := by
  refine wp_movS rfl fun t U _ => WP.block_nil ?_
  obtain K : Keeps powerClob s t := U.keeps.mono (by decide)
  obtain Ct : Context n m base size t :=
    ⟨C.scr.of_keeps K (by decide), C.size_le, U.mem ▸ C.modulus, C.gt_one, U.mem ▸ C.inverse⟩
  obtain init : Subsets n context size m g bits 1 base s t :=
    ⟨Ct, U.gpr, U.mem ▸ T, U.mem ▸ Outs.refl _ _ _, K⟩
  exact init

theorem buildSubsets_ok {n context size m g bits : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (T : TableAt n context m g bits base (knownSubset 1) s.mem) :
    WP isa (VG.Impl.Mont.X86.Comb.buildSubsets n context) s
      (Subsets n context size m g bits 32 base s) := by
  unfold VG.Impl.Mont.X86.Comb.buildSubsets
  refine WP.seq (WP.mono (buildSubsets_initial C T) fun t init => ?_)
  exact VG.Proof.Bignum.X86.PublicRt.countLoop (N := 31) (by decide)
    (fun i => Subsets n context size m g bits (i+1) base s)
    (fun i t hi I => WP.mono (subsetStep_ok L I (by omega_using []) (by omega_using [hi]))
      fun z ⟨Iz,Z⟩ => ⟨Iz, by simpa only [show (i+1+1=32) ↔ (i+1=31) by omega_using []] using Z⟩) init

end VG.Proof.Mont.X86.Comb

end

end

/-! Compose initialization, column generation, and subset completion. -/

@[expose] public section
namespace VG.Proof.Mont.X86.Comb
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

/-- The arithmetic workspace and the retained context are the only writes. -/
def buildRanges (n context : Nat) : List (Nat × Nat) :=
  [(4,4),(28,4),(slot n 1,8*n),(slot n 2,16*n+4),
   (slot n 5,8*n),(slot n 6,8*n),(slot n 7,8*n),(context,272*n)]

theorem columns_prefix {n context size d : Nat} {base : Addr} {s t : Mem}
    (L : Layout n context size) (nw : base.toNat+size ≤ 2^32)
    (O : Outs base (columnRanges n context) s t)
    (lo : context ≤ d) (hi : d+8*n ≤ context+24*n) :
    wordsVal t base d n = wordsVal s base d n := by
  have h5 := L.slot (i := 5) (by decide)
  have h1 := L.slot (i := 1) (by decide)
  have h2 := L.slot (i := 3) (by decide)
  have hd := L.apart
  have hb := L.bound
  have hh := slot_header n 9
  change slot n 9 ≤ context at hd
  have sep : slot n 2 + (16*n+4) ≤ context := by
    simp only [slot,stride] at *; omega_using [h5]
  rw [wordsVal_eq_val32,wordsVal_eq_val32]
  exact O.val32 (by
    intro r hr; simp only [columnRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> omega_arith) (by omega_using [nw, hi, hb])

theorem subsets_prefix {n context size d : Nat} {base : Addr} {s t : Mem}
    (L : Layout n context size) (nw : base.toNat+size ≤ 2^32)
    (O : Outs base (subsetRanges n context) s t)
    (lo : context ≤ d) (hi : d+8*n ≤ context+24*n) :
    wordsVal t base d n = wordsVal s base d n := by
  have h5 := L.slot (i := 5) (by decide)
  have h6 := L.slot (i := 6) (by decide)
  have h7 := L.slot (i := 7) (by decide)
  have h1 := L.slot (i := 1) (by decide)
  have hd := L.apart
  have hb := L.bound
  have hh := slot_header n 9
  change slot n 9 ≤ context at hd
  have sep : slot n 2 + (16*n+4) ≤ context := by
    simp only [slot,stride] at *; omega_using [h5]
  rw [wordsVal_eq_val32,wordsVal_eq_val32]
  exact O.val32 (by
    intro r hr; simp only [subsetRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega_arith) (by omega_using [nw, hi, hb])

theorem Columns.tableAt {n e context size m g : Nat} {base : Addr} {s t : State}
    (L : Layout n context size) (nw : base.toNat+size≤2^32)
    (I : Columns n context size m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 4 base s t)
    (zeroEntry : wordsVal s.mem base (context+16*n) n=2^(64*n)%m) :
    TableAt n context m g (32*e) base (knownSubset 1) t.mem := by
  have bound := L.bound

  intro j hj hk
  rcases hk with zero | tooth
  · have eq : j=0 := by omega_using [zero]
    subst j
    have addr : entry n (context+16*n) 0 = context+16*n := by simp [entry]
    rw [addr,columns_prefix L nw I.mem (by omega_using []) (by omega_using []),zeroEntry]
    simp only [tableValue,VG.Proof.Rsa.FixedBaseComb.exponent_zero,VG.Proof.Bignum.powMod_eq,Nat.pow_zero]
    rw [Nat.mod_mul_mod,Nat.one_mul]
  · have jt : ∃ k, k≤4 ∧ j=2^k := by
      rcases tooth with rfl|rfl|rfl|rfl|rfl
      · exact ⟨0,by decide,rfl⟩
      · exact ⟨1,by decide,rfl⟩
      · exact ⟨2,by decide,rfl⟩
      · exact ⟨3,by decide,rfl⟩
      · exact ⟨4,by decide,rfl⟩
    obtain ⟨k,hk,rfl⟩ := jt
    rw [I.table k hk]
    unfold tableValue columnValue
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_tooth _ _ (by omega_using [hk]),Nat.mul_comm k]


theorem build_ok {n e context size m : Nat} {base : Addr} {s : State}
    (L : Layout n context size) (C : Context n m base size s)
    (one : wordsVal s.mem base (slot n 3) n = 1)
    (r2 : wordsVal s.mem base (slot n 4) n = 2^(128*n) % m)
    (hd : 0 < Spec.Rsa.FixedBaseComb.rows (32*e))
    (hd32 : Spec.Rsa.FixedBaseComb.rows (32*e) < 2^32) :
    WP isa (VG.Impl.Mont.X86.Comb.combBuild n e context) s fun t =>
      Context n m base size t ∧
      wordsVal t.mem base context n = m ∧
      wordsVal t.mem base (context+8*n) n = 2^(128*n) % m ∧
      TableAt n context m (wordsVal s.mem base (slot n 5) n) (32*e) base (fun _ => True) t.mem ∧
      Outs base (buildRanges n context) s.mem t.mem ∧ Keeps powerClob s t := by
  have bound := L.bound
  have nw := C.scr.nowrap
  unfold VG.Impl.Mont.X86.Comb.combBuild VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (buildStart_ok L C one r2) fun u ⟨Cu,Pu,Ru,Yu,Gu,Vu,Ou,Ku⟩ => ?_)
  have initial (g : Nat) : columnValue n m g (Spec.Rsa.FixedBaseComb.rows (32*e)) 0 = g*2^(64*n)%m := by
    simp only [columnValue,Nat.mul_zero,Nat.pow_zero,VG.Proof.Bignum.powMod_eq,Nat.pow_one]
    exact Nat.mod_mul_mod _ _ _
  refine WP.seq (WP.mono (buildColumns_ok L Cu hd hd32 (Vu.trans (initial _).symm)
    (Gu.trans (initial _).symm)) fun v I => ?_)
  have Tv := I.tableAt L nw Yu
  refine WP.seq (WP.mono (buildSubsets_ok L I.ctx Tv) fun t J => WP.block_nil ?_)
  refine ⟨J.ctx,?_,?_,?_,?_,(Ku.trans I.keeps).trans J.keeps⟩
  · rw [subsets_prefix L nw J.mem (by omega_using []) (by omega_using []),columns_prefix L nw I.mem (by omega_using []) (by omega_using []),Pu]
  · rw [subsets_prefix L nw J.mem (by omega_using []) (by omega_using []),columns_prefix L nw I.mem (by omega_using []) (by omega_using []),Ru]
  · intro j hj _; exact J.table j hj (.inl hj)
  · have a : Outs base (buildRanges n context) s.mem u.mem := Ou.mono (by
      intro r hr; simp only [startRanges,encodeRanges,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with (rfl|rfl|rfl|rfl)|rfl <;> simp [buildRanges])
    have b : Outs base (buildRanges n context) u.mem v.mem := widen I.mem (by
      intro r hr; simp only [columnRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨(context,272*n),by simp [buildRanges],by omega_using [],by omega_using []⟩)
    have c : Outs base (buildRanges n context) v.mem t.mem := widen J.mem (by
      intro r hr; simp only [subsetRanges,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,by simp [buildRanges],Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨(context,272*n),by simp [buildRanges],by omega_using [],by omega_using []⟩)
    exact (a.trans b).trans c

end VG.Proof.Mont.X86.Comb
