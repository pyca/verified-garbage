module

public import VerifiedGarbage.Proof.Mont.X86.CombTableState
public import VerifiedGarbage.Proof.Mont.X86.CombSubsetControl
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.Mont.X86.CombAccess
import VerifiedGarbage.Proof.Mont.X86.ContextMul
import VerifiedGarbage.Proof.Mont.X86.ContextMath
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.DynamicFrame
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Rsa.FixedBaseCombMont
import VerifiedGarbage.Proof.Rsa.FixedBaseCombSubset
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Loops

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
  have hdr := slot_header n 9
  have context32 : 32 ≤ context := by change slot n 9 ≤ context at apart; omega
  have nw := I.ctx.scr.nowrap
  have b5 := L.slot (i := 5) (by decide)
  have b6 := L.slot (i := 6) (by decide)
  have b7 := L.slot (i := 7) (by decide)
  have h5 := slot_header n 5
  have h6 := slot_header n 6
  have h7 := slot_header n 7
  obtain ⟨loPos,loLe,remLt,loTooth⟩ := VG.Proof.Rsa.FixedBaseComb.lowTooth_bounds a ha32 ha
  have loLt : lowTooth a < 32 := by omega
  unfold VG.Impl.Mont.X86.Comb.subsetStep VG.Impl.Mont.X86.Comb.seq
  simp only [List.foldr_cons,List.foldr_nil]
  refine WP.seq (WP.mono (subsetIndices_ok I.ctx.scr (by omega) ha32 I.count) fun u ⟨Ou,Hu,Vu,Ku⟩ => ?_)
  have Cu := I.ctx.outs_keep Ku (by decide) (by decide) Ou (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> right <;> simp [slot]) (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> decide)
  have Tu := I.table.outs L I.ctx.scr Ou (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl <;> left <;> omega)
  refine WP.seq (WP.mono (select_table_ok L Cu Tu (o := 6) (by decide) (by decide)
    (by rw [Vu]; omega) (by rw [Vu]; exact .inl remLt)) fun v ⟨Cv,Tv,Vv,Ov,Kv⟩ => ?_)
  rw [Vu] at Vv
  have Hv : w32 v.mem base 28 = lowTooth a := (Ov.w32 (by omega) (by decide)).trans Hu
  refine WP.seq (WP.mono (subsetLow_ok Cv.scr (by omega)) fun w ⟨Ow,Vw,Kw⟩ => ?_)
  have Cw := Cv.outside_keep Kw (by decide) (by decide) Ow (.inr (by simp [slot])) (by decide)
  have Tw := Tv.outside L Cv.scr Ow (.inl (by omega))
  have Vw' : w32 w.mem base 4 = lowTooth a := Vw.trans Hv
  have leftW : wordsVal w.mem base (slot n 6) n = tableValue n m g bits (a-lowTooth a) :=
    (Ow.wordsVal (.inr (by omega)) (by omega)).trans Vv
  refine WP.seq (WP.mono (select_table_ok L Cw Tw (o := 5) (by decide) (by decide)
    (by rw [Vw']; exact loLt) (by rw [Vw']; exact .inr loTooth)) fun x ⟨Cx,Tx,Vx,Ox,Kx⟩ => ?_)
  rw [Vw'] at Vx
  have sep56 := slot_sep (n := n) (i := 6) (j := 5) (by decide)
  have leftX : wordsVal x.mem base (slot n 6) n = tableValue n m g bits (a-lowTooth a) :=
    (Ox.wordsVal (by unfold stride at sep56; omega) (by omega)).trans leftW
  refine WP.seq (WP.mono (context_mul_ok Cx (o := 7) (a := 6) (b := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [Vx]; exact Nat.mod_lt _ (by have := Cx.gt_one; omega))) fun y ⟨Cy,Ky,lty,Vy⟩ => ?_)
  have Ty := Tx.op L Cx (by decide) Ky
  have value : wordsVal y.mem base (slot n 7) n = tableValue n m g bits a := by
    have product := VG.Proof.Rsa.FixedBaseComb.mont_product_encoded Cx.coprime lty leftX Vx Vy
    unfold tableValue
    rw [VG.Proof.Rsa.FixedBaseComb.exponent_lowTooth bits a ha32]
    exact product
  have esiy : y.gpr .esi = BitVec.ofNat 32 a := by
    rw [Ky.gpr .esi (by decide),Kx.1 .esi (by decide),Kw.1 .esi (by decide),Kv.1 .esi (by decide),Ku.1 .esi (by decide),I.count]
  have idx : (y.gpr .esi).toNat = a := by rw [esiy,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ent := L.entry ha32
  have low : context+24*n ≤ entry n (context+16*n) a := by
    have := Nat.mul_le_mul_left (8*n) ha
    simp only [Nat.mul_one] at this
    unfold entry; omega
  refine WP.seq (WP.mono (copyToComb_ok Cy.scr L.positive (by omega) (by rw [idx]; omega)
    (.inl (by rw [idx]; omega))) fun f ⟨Of,Vf,Kf⟩ => ?_)
  rw [idx] at Of Vf
  have Cf := outside_high_context L Cy Kf (by decide) (by decide) Of (by omega)
  have Tf : TableAt n context m g bits base (knownSubset (a+1)) f.mem := by
    intro j hj hk
    by_cases same : j=a
    · subst j; exact Vf.trans value
    · have ej := L.entry hj
      rw [Of.wordsVal (entry_apart n (context+16*n) same) (by omega)]
      apply Ty j hj
      rcases hk with before | tooth
      · left; omega
      · right; exact tooth
  refine WP.seq (wp_addS rfl fun q U _ => wp_cmpS rfl fun z F Z => WP.block_nil (WP.block_nil ?_))
  have esif : f.gpr .esi = BitVec.ofNat 32 a := (Kf.1 .esi (by decide)).trans esiy
  have count : z.gpr .esi = BitVec.ofNat 32 (a+1) := by
    rw [F.gpr,U.gpr,esif]
    exact (BitVec.ofNat_add a 1).symm
  have M : z.mem = f.mem := F.mem.trans U.mem
  have Klast : Keeps powerClob f z := (U.keeps.mono (by decide)).trans (F.keeps _)
  have Cz : Context n m base size z :=
    ⟨Cf.scr.of_keeps Klast (by decide),Cf.size_le,M ▸ Cf.modulus,Cf.gt_one,M ▸ Cf.inverse⟩
  refine ⟨⟨Cz,count,M ▸ Tf,?_,?_⟩,?_⟩
  · have ou : Outs base (subsetRanges n context) t.mem u.mem := Ou.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl <;> simp [subsetRanges])
    have ov := Outs.of_outside Ov (rs := subsetRanges n context) (by simp [subsetRanges])
    have ow := Outs.of_outside Ow (rs := subsetRanges n context) (by simp [subsetRanges])
    have ox := Outs.of_outside Ox (rs := subsetRanges n context) (by simp [subsetRanges])
    have oy : Outs base (subsetRanges n context) x.mem y.mem := Ky.mem.mono (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl <;> simp [subsetRanges,contextMod,accLen,words] <;> omega)
    have of : Outs base (subsetRanges n context) y.mem f.mem :=
      widen (Outs.of_outside Of (rs := [(entry n (context+16*n) a,8*n)]) (by simp)) (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨(context+24*n,248*n),by simp [subsetRanges],low,by omega⟩)
    rw [M]
    exact ((((((I.mem.trans ou).trans ov).trans ow).trans ox).trans oy).trans of)
  · have k1 := I.keeps.trans (Ku.mono (by decide))
    have k2 := k1.trans (Kv.mono (by decide))
    have k3 := k2.trans (Kw.mono (by decide))
    have k4 := k3.trans (Kx.mono (by decide))
    have k5 := k4.trans ((OpKeep.keeps Ky).mono (by decide))
    exact (k5.trans (Kf.mono (by decide))).trans Klast
  · rw [Z,U.gpr,esif,← BitVec.ofNat_add]
    have finite : ∀ a < 32, (BitVec.ofNat 32 (a+1)-32#32 == 0) = decide (a+1=32) := by decide
    rw [finite a ha32]

/-- Fill all 31 nonzero entries from their lower subsets and single teeth. -/
theorem buildSubsets_initial {n context size m g bits : Nat} {base : Addr} {s : State}
    (C : Context n m base size s)
    (T : TableAt n context m g bits base (knownSubset 1) s.mem) :
    WP isa (.block [.mov .esi (VG.Impl.Mont.X86.Comb.imm 1)]) s
      (Subsets n context size m g bits 1 base s) := by
  refine wp_movS rfl fun t U _ => WP.block_nil ?_
  have K : Keeps powerClob s t := U.keeps.mono (by decide)
  have Ct : Context n m base size t :=
    ⟨C.scr.of_keeps K (by decide), C.size_le, U.mem ▸ C.modulus, C.gt_one, U.mem ▸ C.inverse⟩
  have init : Subsets n context size m g bits 1 base s t :=
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
    (fun i t hi I => WP.mono (subsetStep_ok L I (by omega) (by omega))
      fun z ⟨Iz,Z⟩ => ⟨Iz, by simpa only [show (i+1+1=32) ↔ (i+1=31) by omega] using Z⟩) init

end VG.Proof.Mont.X86.Comb
