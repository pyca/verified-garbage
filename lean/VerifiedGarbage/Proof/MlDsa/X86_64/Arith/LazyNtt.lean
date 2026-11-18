module

public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Lazy
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyBase
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyInvariant
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Lazy
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyBase
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyInvariant
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlDsa.Arith.LazyButterfly
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
meta import VerifiedGarbage.Proof.MlDsa.Arith.LazyButterfly
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay
public import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery

/-! ### `MlDsa.X86_64.Arith.LazyNttLayers`, which this module and modules that import it used -/

section

/-! ### `MlDsa.X86_64.Arith.LazyButterfly`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q Zq)

theorem prod_lt {y z : BitVec 128} {f : Nat → Word} {ζ : Nat → Zq}
    (hy : DLanes y f) (hz : ZLanes z ζ) :
    ∀ i < 4, (dword y i).toNat * (dword z i).toNat < q * 2 ^ 32 := fun i hi => by
  rw [hy i hi, hz i hi]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (f i).isLt
    (Nat.le_of_lt (Nat.mod_lt _ (show 0 < q by decide))) (by decide)) (by decide)

theorem bfly_ok : VBflyOk lazyBfly op := by
  intro s hc x y ζ hx hy hz ho
  simp only [lazyBfly, vmont, vredc, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, hc.q2]
  have hm (i : Nat) (hi : i < 4) :
      (dword (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12)) i).toNat = product (y i) (ζ i) := by
    rw [dword_montV ho (prod_lt hy hz) hi, hy i hi, hz i hi]; rfl
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (XBinOp.eval .paddd (s.xmm .xmm0)
      (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))) _
    intro i hi
    rw [dword_paddd _ _ hi, BitVec.toNat_add, hx i hi, hm i hi]
    simp only [op, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod]
  · change DLanes (XBinOp.eval .psubd
      (XBinOp.eval .paddd (s.xmm .xmm0) (ofDwords 16760834#32 16760834#32 16760834#32 16760834#32))
      (montV (s.xmm .xmm1) (s.xmm .xmm13) (s.xmm .xmm12))) _
    intro i hi
    have hq : (dword (ofDwords 16760834#32 16760834#32 16760834#32 16760834#32) i).toNat = 16760834 := by
      rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [dword_psubd _ _ hi, BitVec.toNat_sub, dword_paddd _ _ hi, BitVec.toNat_add, hx i hi, hq, hm i hi]
    have ht := product_lt (y i) (ζ i)
    simp only [op, Fin.val_sub, Fin.val_add, Fin.val_ofNat,
      show (16760834 : Word).val = 16760834 from rfl]
    have ht32 : product (y i) (ζ i) < 4294967296 := by exact Nat.lt_trans ht (by decide)
    rw [Nat.mod_eq_of_lt ht32]

/-- `128 q`, the bias of `vibflyLazy`, in each doubleword of xmm11. -/
abbrev bInvC : BitVec 32 := 1072693376#32

theorem bflyInv_ok : VBflyOkW bInvC vibflyLazy opInv := by
  intro s hc x y ζ hx hy hz ho
  simp only [vibflyLazy, vmont, vredc, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, hc.q2]
  have hw : DLanes (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0))
      (ofDwords bInvC bInvC bInvC bInvC)) (fun i => y i + 1072693376 - x i) := by
    intro i hi
    have hb : (dword (ofDwords bInvC bInvC bInvC bInvC) i).toNat = 1072693376 := by
      rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [dword_paddd _ _ hi, BitVec.toNat_add, dword_psubd _ _ hi, BitVec.toNat_sub, hx i hi, hy i hi, hb]
    simp only [Fin.val_sub, Fin.val_add, show (1072693376 : Word).val = 1072693376 from rfl]
    have := (x i).isLt; have := (y i).isLt
    omega_using []
  refine ⟨?_, ?_, by xonly⟩
  · change DLanes (XBinOp.eval .paddd (s.xmm .xmm0) (s.xmm .xmm1)) _
    intro i hi
    rw [dword_paddd _ _ hi, BitVec.toNat_add, hx i hi, hy i hi]
    simp only [opInv, Fin.val_add]
  · change DLanes (montV (XBinOp.eval .paddd (XBinOp.eval .psubd (s.xmm .xmm1) (s.xmm .xmm0))
      (ofDwords bInvC bInvC bInvC bInvC)) (s.xmm .xmm13) (s.xmm .xmm12)) _
    intro i hi
    rw [dword_montV ho (prod_lt hw hz) hi, hw i hi, hz i hi]
    have ht := product_lt (y i + 1072693376 - x i) (ζ i)
    have ht32 : product (y i + 1072693376 - x i) (ζ i) < 4294967296 := Nat.lt_trans ht (by decide)
    simp only [opInv, Fin.val_ofNat, Nat.mod_eq_of_lt ht32]
    rfl

end VG.Proof.MlDsa.X86_64.Arith.Lazy

end

end

/-! ### `MlDsa.X86_64.Arith.LazyLay21`, which this module and modules that import it used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy

variable {c11 : BitVec 32}

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith hiding BlkOk layF layF1_get layF2_get
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt add_ofNat_zero GOnly
  addR_ok wp_rcxLoopY wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem q256lo q256hi
  lo4 hi4)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Zq zetas)
open VG.Proof.MlDsa (coeffAt)

/-! ## An iteration -/

/-- An iteration of a layer with `len` = 2 or 1: the sixteen coefficients of
`G` from `j`, in lane `l` the four from `j + 4l` and the four from
`j + 8 + 4l`, become those of `R`, with the zetas `ζ l` that `zl` leaves in
the lanes of `ymm13`. -/
theorem ystep21 {core zl : List Instr} {r2 : XReg} {zs : List XReg} {dz : BitVec 32}
    (hY : laneSseBlock (toY core) = some core) (h0 : XReg.xmm0 ∉ zs) (h2 : r2 ∉ zs)
    (h14 : XReg.xmm14 ∉ [XReg.xmm0] ++ [r2] ++ zs) (h15 : XReg.xmm15 ∉ [XReg.xmm0] ++ [r2] ++ zs)
    (h11 : XReg.xmm11 ∉ [XReg.xmm0] ++ [r2] ++ zs) (h20 : XReg.xmm0 ∉ [r2]) {fP : Addr} {j : Nat} (hj : j + 16 ≤ 256) {G R : Poly}
    {ζ : Nat → Nat → Zq} {s : State} (hc : YConstsW c11 s) (hdx : s.gpr .rdx = coeffAddr fP j)
    (hS : PolyIs s.mem fP G) (hw : pR fP ∈ s.wr)
    (hz : ∀ s', XKeep s s' →
      WP isa (.block zl) s' fun s'' => (∀ l < 2, ZLanes (s''.lane .xmm13 l) (ζ l) ∧
        ZOdd (s''.lane .xmm13 l) (s''.lane .xmm12 l)) ∧ YOnly zs s' s'')
    (hcore : ∀ l < 2, ∀ t : State, VConstsW c11 t → DLanes (t.xmm .xmm0) (fun e => G[j + 4 * l + e]!) →
      DLanes (t.xmm r2) (fun e => G[j + 8 + 4 * l + e]!) → ZLanes (t.xmm .xmm13) (ζ l) →
      ZOdd (t.xmm .xmm13) (t.xmm .xmm12) →
      WP isa (.block core) t fun t' => (DLanes (t'.xmm .xmm0) (fun e => R[j + 4 * l + e]!) ∧
        DLanes (t'.xmm .xmm1) (fun e => R[j + 8 + 4 * l + e]!)) ∧
        XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t')
    (hR : ∀ i < 256, i < j ∨ j + 16 ≤ i → R[i]! = G[i]!) :
    WP isa (.block (ybody21 r2 zl core dz)) s fun s' =>
      PolyIs s'.mem fP R ∧ s'.gpr .rdx = coeffAddr fP (j + 16) ∧
      s'.gpr .r8 = s.gpr .r8 + BitVec.signExtend 64 dz ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
      s'.zf = some (s.gpr .rcx - 1 == 0) ∧ BInvYW c11 fP s s' := by
  have j0 : j + 8 ≤ 256 := by omega_using [hj]
  have j1 : j + 8 + 8 ≤ 256 := by omega_using [hj]
  have a1 : coeffAddr fP j + BitVec.ofNat 64 32 = coeffAddr fP (j + 8) := coeffAddr_add _ _ 8
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right s.rd hw) j0
  have r1 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 32) 32 := by
    rw [hdx, a1]; exact f_in32 (List.mem_append_right s.rd hw) j1
  rw [ybody21, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L0, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (d := r2) (by rw [o1.rd, o1.wr, o1.gpr]; exact r1)) fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (hz s2 o12.toXKeep) fun s3 ⟨Z3, o3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (addR_ok .r8 dz s3) fun s4 ⟨h84, g4, y4⟩ => ?_
  have l4 := g4.lane y4
  have c4 : YConstsW c11 s4 := ylanes_gpr (s := s3) l4 (o12.trans o3) hc h14 h15 h11
  rw [WP.block_append_iff]
  refine WP.mono (ylanes hY (P := fun l t => DLanes (t.xmm .xmm0) (fun e => R[j + 4 * l + e]!) ∧
      DLanes (t.xmm .xmm1) (fun e => R[j + 8 + 4 * l + e]!))
    fun l hl => hcore l hl _ (c4 l hl)
      (by rw [State.proj_xmm, l4, o3.lane _ h0 l hl, o2.lane _ h20 l hl, L0 l hl, hdx, add_ofNat_zero]
          exact dlanes_loadY hS j0 hl)
      (by rw [State.proj_xmm, l4, o3.lane _ h2 l hl, L2 l hl, o1.gpr, o1.mem, hdx, a1]
          exact dlanes_loadY hS j1 hl)
      (by rw [State.proj_xmm, l4]; exact (Z3 l hl).1)
      (by rw [State.proj_xmm, State.proj_xmm, l4, l4]; exact (Z3 l hl).2)) fun s5 ⟨C5, o5⟩ => ?_
  have m5 : s5.mem = s.mem := by rw [o5.mem, g4.mem, o3.mem, o12.mem]
  have g5 : s5.gpr = s4.gpr := o5.gpr
  have dx5 : s5.gpr .rdx = coeffAddr fP j := by rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr, hdx]
  have k5 : s5.rd = s.rd ∧ s5.wr = s.wr := ⟨by rw [o5.rd, g4.keep.2.1, o3.rd, o12.rd],
    by rw [o5.wr, g4.keep.2.2, o3.wr, o12.wr]⟩
  have w0 : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [k5.2, dx5]; exact f_in32 hw j0
  have w1 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 32) 32 := by rw [k5.2, dx5, a1]; exact f_in32 hw j1
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, State.setMem_setMem, w0, w1, sx_ofNat (show 64 < 2 ^ 31 by decide)]
  rw [dx5, a1, m5]
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩
  · exact polyIs_write2L (s := s5) hS j0 j1 (by omega_using []) (fun l hl => (C5 l hl).1)
      (fun l hl => (C5 l hl).2) fun i hi _ _ => hR i hi (by omega_arith)
  · rw [show BitVec.signExtend 64 (64 : BitVec 32) = BitVec.ofNat 64 (4 * 16) by decide, coeffAddr_add]
  · rw [g5, h84, o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · rw [g5, g4.keep.gpr (by decide), o3.gpr, o12.gpr]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false, State.setMem_gpr]
    rw [g5, g4.keep.gpr (by simp [hr]), o3.gpr, o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; exact k5.1
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; exact k5.2
  · exact frame_write2Y (Frame.refl _ _) j0 j1 _ _
  · exact ylanes_gpr (s := s5) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o5 c4
      (by decide) (by decide)
  · exact o5.mxcsr.trans (g4.mxcsr.trans (o12.trans o3).mxcsr)

/-! ## The gatherings, the butterflies and the interleavings back of a lane -/

section
variable {bf : List Instr} {op : Word → Word → Zq → Word × Word} (hbf : VBflyOkW c11 bf op)
include hbf

/-- `vlay2`'s work on the coefficients `A` of `xmm0` and `B` of `xmm1`: the
blocks `A` and `B` of `len = 2`, with the zetas `ζ` (the first two for `A`,
the last two for `B`). -/
theorem core2_ok {t : State} (hc : VConstsW c11 t) {A B : Nat → Word} {ζ : Nat → Zq} (hA : DLanes (t.xmm .xmm0) A)
    (hB : DLanes (t.xmm .xmm1) B) (hz : ZLanes (t.xmm .xmm13) ζ) (ho : ZOdd (t.xmm .xmm13) (t.xmm .xmm12)) :
    WP isa (.block (gath2 ++ bf ++ scat2)) t fun t' =>
      (DLanes (t'.xmm .xmm0) (fun e => if e < 2 then (op (A e) (A (2 + e)) (ζ e)).1
          else (op (A (e - 2)) (A e) (ζ (e - 2))).2) ∧
        DLanes (t'.xmm .xmm1) (fun e => if e < 2 then (op (B e) (B (2 + e)) (ζ (2 + e))).1
          else (op (B (e - 2)) (B e) (ζ e)).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (gath2_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (xonly_vconsts o1 hc (by decide) (by decide))
    (fun e => if e < 2 then A e else B (e - 2)) (fun e => if e < 2 then A (2 + e) else B e) ζ
    (fun e he => by
      dsimp only; rw [e0, dword_punpcklqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · exact hA e he
      · exact hB (e - 2) (by omega_using [he]))
    (fun e he => by
      dsimp only; rw [e1, dword_punpckhqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · exact hA (2 + e) (by omega_using [h])
      · exact hB e he)
    (by rw [o1.xmm _ (by decide)]; exact hz) (by rw [o1.xmm _ (by decide), o1.xmm _ (by decide)]; exact ho))
    fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (scat2_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, dword_punpcklqdq _ _ he]
    split
    · rw [X e he]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›), ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›)]
    · rw [Y (e - 2) (by omega_using [he])]; dsimp only
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show e - 2 < 2 by omega_using [he])),
        ite_eq_left_of_eq_true _ _ (eq_true (show e - 2 < 2 by omega_using [he])),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›), show 2 + (e - 2) = e by omega_arith]
  · rw [f1, dword_punpckhqdq _ _ he]
    split
    · rw [X (2 + e) (by omega_arith)]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 2 + e < 2 by omega_using [])),
        ite_eq_right_of_eq_false _ _ (eq_false (show ¬ 2 + e < 2 by omega_using [])),
        ite_eq_left_of_eq_true _ _ (eq_true ‹e < 2›), show 2 + e - 2 = e by omega_using []]
    · rw [Y e he]; dsimp only
      rw [ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›), ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›),
        ite_eq_right_of_eq_false _ _ (eq_false ‹¬ e < 2›)]
  · exact ((o1.trans o2).trans o3).mono (by simp)

/-- `vlay1`'s work on the coefficients `A` of `xmm0` and `B` of `xmm2`: the
blocks `A₀₁`, `A₂₃`, `B₀₁` and `B₂₃` of `len = 1`, with the zetas `ζ`. -/
theorem core1_ok {t : State} (hc : VConstsW c11 t) {A B : Nat → Word} {ζ : Nat → Zq} (hA : DLanes (t.xmm .xmm0) A)
    (hB : DLanes (t.xmm .xmm2) B) (hz : ZLanes (t.xmm .xmm13) ζ) (ho : ZOdd (t.xmm .xmm13) (t.xmm .xmm12)) :
    WP isa (.block (gath1 ++ bf ++ scat1)) t fun t' =>
      (DLanes (t'.xmm .xmm0) (fun e => if e % 2 = 0 then (op (A e) (A (e + 1)) (ζ (e / 2))).1
          else (op (A (e - 1)) (A e) (ζ (e / 2))).2) ∧
        DLanes (t'.xmm .xmm1) (fun e => if e % 2 = 0 then (op (B e) (B (e + 1)) (ζ (2 + e / 2))).1
          else (op (B (e - 1)) (B e) (ζ (2 + e / 2))).2)) ∧ XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] t t' := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (gath1_ok t) fun t1 ⟨⟨e0, e1⟩, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hbf _ (xonly_vconsts o1 hc (by decide) (by decide))
    (fun e => if e < 2 then A (2 * e) else B (2 * (e - 2))) (fun e => if e < 2 then A (2 * e + 1) else B (2 * (e - 2) + 1))
    ζ
    (fun e he => by
      dsimp only; rw [e0, dword_punpcklqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · rw [dword_d8 _ he, ite_eq_left h]; exact hA _ (by omega_using [h])
      · rw [dword_d8 _ (by omega_using [he]), ite_eq_left (by omega_using [he])]; exact hB _ (by omega_using [he]))
    (fun e he => by
      dsimp only; rw [e1, dword_punpckhqdq _ _ he]
      by_cases h : e < 2 <;> simp only [h, ite_true, ite_false]
      · rw [dword_d8 _ (by omega_using [h]), ite_eq_right (by omega_using []), show 2 * (2 + e - 2) + 1 = 2 * e + 1 by omega_using []]
        exact hA _ (by omega_using [h])
      · rw [dword_d8 _ he, ite_eq_right h]; exact hB _ (by omega_using [he]))
    (by rw [o1.xmm _ (by decide)]; exact hz) (by rw [o1.xmm _ (by decide), o1.xmm _ (by decide)]; exact ho))
    fun t2 ⟨X, Y, o2⟩ => ?_
  refine WP.mono (scat1_ok t2) fun t3 ⟨⟨f0, f1⟩, o3⟩ => ⟨⟨fun e he => ?_, fun e he => ?_⟩, ?_⟩
  · rw [f0, dword_punpckldq' _ _ he]
    split
    · rw [X (e / 2) (by omega_using [he])]; dsimp only
      rw [ite_eq_left (by omega_using [he]), ite_eq_left (by omega_using [he]), ite_eq_left ‹e % 2 = 0›,
        show 2 * (e / 2) = e by omega_arith]
    · rw [Y (e / 2) (by omega_using [he])]; dsimp only
      rw [ite_eq_left (by omega_using [he]), ite_eq_left (by omega_using [he]), ite_eq_right ‹¬ e % 2 = 0›,
        show 2 * (e / 2) = e - 1 by omega_arith, show e - 1 + 1 = e by omega_arith]
  · rw [f1, dword_punpckhdq' _ _ he]
    split
    · rw [X (2 + e / 2) (by omega_using [he])]; dsimp only
      rw [ite_eq_right (by omega_using []), ite_eq_right (by omega_using []), ite_eq_left ‹e % 2 = 0›,
        show 2 * (2 + e / 2 - 2) = e by omega_arith]
    · rw [Y (2 + e / 2) (by omega_using [he])]; dsimp only
      rw [ite_eq_right (by omega_using []), ite_eq_right (by omega_using []), ite_eq_right ‹¬ e % 2 = 0›,
        show 2 * (2 + e / 2 - 2) = e - 1 by omega_arith, show e - 1 + 1 = e by omega_arith]
  · exact ((o1.trans o2).trans o3).mono (by simp)

end

/-! ## The layers -/

section
variable {op : Word → Word → Zq → Word × Word} {blk : Poly → Nat → Nat → Nat → Nat → Poly} (hblk : BlkOk blk op)
include hblk

/-- The sixteen coefficients from `16i` after the next blocks of the layer
with `len = 2`. -/
theorem layF2_next (F : Poly) (zi : Nat → Nat) {i : Nat} (hi : i < 16) {x : Nat} (hx : x < 256) :
    (layF blk F 2 zi (4 * (i + 1)))[x]! = if 16 * i ≤ x ∧ x < 16 * i + 16 then
      (if x % (2 * 2) < 2 then
        (op (layF blk F 2 zi (4 * i))[x]! (layF blk F 2 zi (4 * i))[x + 2]! (zetas (zi (x / (2 * 2))))).1
      else (op (layF blk F 2 zi (4 * i))[x - 2]! (layF blk F 2 zi (4 * i))[x]! (zetas (zi (x / (2 * 2))))).2)
      else (layF blk F 2 zi (4 * i))[x]! := by
  have hF : ∀ y, 16 * i ≤ y → y < 256 → (layF blk F 2 zi (4 * i))[y]! = F[y]! := fun y h1 h2 => by
    rw [Arith.Lazy.layF_get hblk F (by decide) zi (by omega_using [h1, h2]) h2, ite_eq_right (by omega_using [h1])]
  rw [Arith.Lazy.layF_get hblk F (by decide) zi (by omega_using [hi]) hx]
  by_cases h1 : 16 * i ≤ x ∧ x < 16 * i + 16
  · rw [ite_eq_left (by omega_using [h1]), ite_eq_left h1]
    by_cases h2 : x % (2 * 2) < 2
    · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hx, hF _ (by omega_using [h1]) (by omega_using [hx, h2])]
    · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega_using [h1, h2]) (by omega_using [hx]), hF _ h1.1 hx]
  · rw [ite_eq_right h1, Arith.Lazy.layF_get hblk F (by decide) zi (by omega_using [hi]) hx]
    by_cases h3 : x < 16 * i
    · rw [ite_eq_left (show x < 2 * 2 * (4 * (i + 1)) by omega_using [h3]), ite_eq_left (show x < 2 * 2 * (4 * i) by omega_using [h3])]
    · rw [ite_eq_right (show ¬ x < 2 * 2 * (4 * (i + 1)) by omega_using [h1, h3]),
        ite_eq_right (show ¬ x < 2 * 2 * (4 * i) by omega_using [h3])]

/-- The sixteen coefficients from `16i` after the next blocks of the layer
with `len = 1`. -/
theorem layF1_next (F : Poly) (zi : Nat → Nat) {i : Nat} (hi : i < 16) {x : Nat} (hx : x < 256) :
    (layF blk F 1 zi (8 * (i + 1)))[x]! = if 16 * i ≤ x ∧ x < 16 * i + 16 then
      (if x % (2 * 1) < 1 then
        (op (layF blk F 1 zi (8 * i))[x]! (layF blk F 1 zi (8 * i))[x + 1]! (zetas (zi (x / (2 * 1))))).1
      else (op (layF blk F 1 zi (8 * i))[x - 1]! (layF blk F 1 zi (8 * i))[x]! (zetas (zi (x / (2 * 1))))).2)
      else (layF blk F 1 zi (8 * i))[x]! := by
  have hF : ∀ y, 16 * i ≤ y → y < 256 → (layF blk F 1 zi (8 * i))[y]! = F[y]! := fun y h1 h2 => by
    rw [Arith.Lazy.layF_get hblk F (by decide) zi (by omega_using [h1, h2]) h2, ite_eq_right (by omega_using [h1])]
  rw [Arith.Lazy.layF_get hblk F (by decide) zi (by omega_using [hi]) hx]
  by_cases h1 : 16 * i ≤ x ∧ x < 16 * i + 16
  · rw [ite_eq_left (by omega_using [h1]), ite_eq_left h1]
    by_cases h2 : x % (2 * 1) < 1
    · rw [ite_eq_left h2, ite_eq_left h2, hF _ h1.1 hx, hF _ (by omega_using [h1]) (by omega_using [hx, h2])]
    · rw [ite_eq_right h2, ite_eq_right h2, hF _ (by omega_using [h1, h2]) (by omega_using [hx]), hF _ h1.1 hx]
  · rw [ite_eq_right h1, Arith.Lazy.layF_get hblk F (by decide) zi (by omega_using [hi]) hx]
    by_cases h3 : x < 16 * i
    · rw [ite_eq_left (show x < 2 * 1 * (8 * (i + 1)) by omega_using [h3]), ite_eq_left (show x < 2 * 1 * (8 * i) by omega_using [h3])]
    · rw [ite_eq_right (show ¬ x < 2 * 1 * (8 * (i + 1)) by omega_using [h1, h3]),
        ite_eq_right (show ¬ x < 2 * 1 * (8 * i) by omega_using [h3])]

variable {bf : List Instr} (hbf : VBflyOkW c11 bf op)
include hbf

theorem ylay2_ok (hY : laneSseBlock (toY (gath2 ++ bf ++ scat2)) = some (gath2 ++ bf ++ scat2)) {fP sP : Addr}
    (k : Nat) (o₀ o₁ : BitVec 8) (dz : BitVec 32) (zi kb : Nat → Nat) (hkb0 : kb 0 = k)
    (hk : ∀ i < 16, kb i + 4 ≤ 256)
    (hsel : ∀ i < 16, ∀ e < 4, kb i + sel o₀ e = zi (4 * i + 2 * (e / 2)) ∧
      kb i + sel o₁ e = zi (4 * i + 1 + 2 * (e / 2)))
    (hstep : ∀ i < 16, coeffAddr sP (kb i) + BitVec.signExtend 64 dz = coeffAddr sP (kb (i + 1)))
    {F : Poly} {s : State} (hc : YConstsW c11 s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay2 bf k o₀ o₁ dz) s fun s' => PolyIs s'.mem fP (layF blk F 2 zi 64) ∧ BInvYW c11 fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega_using [hkb0, this]
  refine WP.seq (WP.mono (ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConstsW c11 w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 2 zi (4 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
      u.gpr .r8 = coeffAddr sP (kb i) ∧ BInvYW c11 fP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkb0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ylanes_gpr (s := w) (ou.lane hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  have hk0' : ∀ j < 4, kb i + sel o₀ j < 256 := fun j _ => by have := sel_lt o₀ j; have := hk i hi; omega_arith
  have hk1' : ∀ j < 4, kb i + sel o₁ j < 256 := fun j _ => by have := sel_lt o₁ j; have := hk i hi; omega_arith
  rw [show [Instr.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm1 (at_ .rdx 32)] ++ yzetaS o₀ o₁ ++
      [.alu .add .r8 (.imm dz)] ++ toY (gath2 ++ bf ++ scat2) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] =
      ybody21 .xmm1 (yzetaS o₀ o₁) (gath2 ++ bf ++ scat2) dz by simp [List.append_assoc]]
  have hR := fun x hx => layF2_next hblk F zi hi (x := x) hx
  refine WP.mono (ystep21 hY (zs := [.xmm13, .xmm2, .xmm12]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (j := 16 * i) (by omega_using [hi]) (R := layF blk F 2 zi (4 * (i + 1)))
    (ζ := fun l e => zetas (zi (4 * i + l + 2 * (e / 2)))) hb'.consts hdx' hS' hwf' (fun s' k' => ?_)
    (fun l hl t ht hA hB hz ho => ?_) (fun x hx h => by rw [hR x hx, ite_eq_right (by omega_using [h])]))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hstep i hi], hb'.trans hb''⟩, hcx, hzf⟩
  · -- the zetas
    refine WP.mono (yzetaS_ok o₀ o₁ (zP := sP) (k := kb i) hk0' hk1' (by rw [k'.gpr, h8'])
      (by rw [k'.rd, k'.wr]; exact tab_in (List.mem_append_right _ hw') (hk i hi)) (by rw [k'.mem]; exact hT'))
      fun s'' ⟨Z0, Z1, ZO, o⟩ => ⟨fun l hl => ⟨?_, ZO l hl⟩, o⟩
    rcases lane01 hl with rfl | rfl
    · exact Z0.congr fun e he => congrArg zetas ((hsel i hi e he).1.trans (congrArg zi (by omega_using [])))
    · exact Z1.congr fun e he => congrArg zetas ((hsel i hi e he).2.trans (congrArg zi (by omega_using [])))
  · -- the blocks of a lane
    refine WP.mono (core2_ok hbf ht hA hB hz ho) fun t' ⟨⟨a, b⟩, o⟩ =>
      ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
    · by_cases h : e < 2
      · rw [ite_eq_left h, hR _ (by omega_using [hi, hl, h]), ite_eq_left (by omega_using [hl, h]), ite_eq_left (by omega_using [h])]
        exact congrArg Prod.fst (op_idx op _ zi (by omega_using []) (by omega_using []) (by omega_using [h]))
      · rw [ite_eq_right h, hR _ (by omega_using [hi, hl, he]), ite_eq_left (by omega_using [hl, he]), ite_eq_right (by omega_using [he, h])]
        exact congrArg Prod.snd (op_idx op _ zi (by omega_using [h]) (by omega_using []) (by omega_using [he]))
    · by_cases h : e < 2
      · rw [ite_eq_left h, hR _ (by omega_using [hi, hl, h]), ite_eq_left (by omega_using [hl, h]), ite_eq_left (by omega_using [h])]
        exact congrArg Prod.fst (op_idx op _ zi (by omega_using []) (by omega_using []) (by omega_using [h]))
      · rw [ite_eq_right h, hR _ (by omega_using [hi, hl, he]), ite_eq_left (by omega_using [hl, he]), ite_eq_right (by omega_using [he, h])]
        exact congrArg Prod.snd (op_idx op _ zi (by omega_using [h]) (by omega_using []) (by omega_using [he, h]))

theorem ylay1_ok (hY : laneSseBlock (toY (gath1 ++ bf ++ scat1)) = some (gath1 ++ bf ++ scat1)) {fP sP : Addr}
    (k : Nat) (zl : List Instr) (dz : BitVec 32) (zi kb : Nat → Nat) (hkb0 : kb 0 = k)
    (hk : ∀ i < 16, kb i + 8 ≤ 256)
    (hzl : ∀ i < 16, ∀ s : State, s.gpr .r8 = coeffAddr sP (kb i) →
      InRegions (s.rd ++ s.wr) (coeffAddr sP (kb i)) 32 → Tab zmTab s.mem sP 256 →
      WP isa (.block zl) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l)
          (fun e => zetas (zi (8 * i + 2 * l + e + 2 * (e / 2)))) ∧ ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧
        YOnly [.xmm13, .xmm12] s s')
    (hstep : ∀ i < 16, coeffAddr sP (kb i) + BitVec.signExtend 64 dz = coeffAddr sP (kb (i + 1)))
    {F : Poly} {s : State} (hc : YConstsW c11 s) (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr)
    (hd : (pR sP).Disjoint (pR fP)) :
    WP isa (ylay1 bf k zl dz) s fun s' => PolyIs s'.mem fP (layF blk F 1 zi 128) ∧ BInvYW c11 fP s s' := by
  have hk0 : k + 4 ≤ 256 := by have := hk 0 (by decide); omega_using [hkb0, this]
  refine WP.seq (WP.mono (ypre21 k hk0 hdi hsi) fun w ⟨hdx, h8, og, hy⟩ => ?_)
  have cw : YConstsW c11 w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => PolyIs u.mem fP (layF blk F 1 zi (8 * i)) ∧ u.gpr .rdx = coeffAddr fP (16 * i) ∧
      u.gpr .r8 = coeffAddr sP (kb i) ∧ BInvYW c11 fP w u)
    (fun u ou hu _ => ⟨by rw [ou.mem, og.mem]; exact hS,
      by rw [ou.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [ou.keep.gpr (by decide), h8, hkb0], ⟨ou.keep.mono (by simp), by rw [ou.mem]; exact Frame.refl _ _,
        ylanes_gpr (s := w) (ou.lane hu) (YOnly.refl [] w) cw (by decide) (by decide), ou.mxcsr⟩⟩)
    (fun i hi u ⟨hS', hdx', h8', hb'⟩ => ?_)) fun u ⟨hS', _, _, hb'⟩ =>
      ⟨hS', ⟨(og.keep.trans hb'.keep).mono (by simp), by rw [← og.mem]; exact hb'.frame, hb'.consts,
        by rw [hb'.mxcsr, og.mxcsr]⟩⟩
  have hT' : Tab zmTab u.mem sP 256 := (by rw [og.mem]; exact hT : Tab zmTab w.mem sP 256).frame hb'.frame
    (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) (by decide)
  have hwf' : pR fP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hwf
  have hw' : pR sP ∈ u.wr := by rw [hb'.keep.2.2, og.keep.2.2]; exact hw
  rw [show [Instr.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm2 (at_ .rdx 32)] ++ zl ++
      [.alu .add .r8 (.imm dz)] ++ toY (gath1 ++ bf ++ scat1) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1,
        .alu .add .rdx (.imm 64)] ++ [.alu .sub .rcx (.imm 1)] =
      ybody21 .xmm2 zl (gath1 ++ bf ++ scat1) dz by simp [List.append_assoc]]
  have hR := fun x hx => layF1_next hblk F zi hi (x := x) hx
  refine WP.mono (ystep21 hY (zs := [.xmm13, .xmm12]) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (j := 16 * i) (by omega_using [hi]) (R := layF blk F 1 zi (8 * (i + 1)))
    (ζ := fun l e => zetas (zi (8 * i + 2 * l + e + 2 * (e / 2)))) hb'.consts hdx' hS' hwf'
    (fun s' k' => hzl i hi s' (by rw [k'.gpr, h8'])
      (by rw [k'.rd, k'.wr]; exact f_in32 (List.mem_append_right _ hw') (hk i hi)) (by rw [k'.mem]; exact hT'))
    (fun l hl t ht hA hB hz ho => ?_) (fun x hx h => by rw [hR x hx, ite_eq_right (by omega_using [h])]))
    fun u' ⟨hS'', hdx'', h8'', hcx, hzf, hb''⟩ => ⟨⟨hS'', by rw [hdx'', Nat.mul_succ],
      by rw [h8'', h8', hstep i hi], hb'.trans hb''⟩, hcx, hzf⟩
  -- the blocks of a lane
  refine WP.mono (core1_ok hbf ht hA hB hz ho) fun t' ⟨⟨a, b⟩, o⟩ =>
    ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, hR _ (by omega_using [hi, hl, he]), ite_eq_left (by omega_using [hl, he]), ite_eq_left (by omega_using [h])]
      exact congrArg Prod.fst (op_idx op _ zi (by omega_using []) (by omega_using []) (by omega_using [he]))
    · rw [ite_eq_right h, hR _ (by omega_using [hi, hl, he]), ite_eq_left (by omega_using [hl, he]), ite_eq_right (by omega_using [h])]
      exact congrArg Prod.snd (op_idx op _ zi (by omega_using [h]) (by omega_using []) (by omega_using [he]))
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, hR _ (by omega_using [hi, hl, he]), ite_eq_left (by omega_using [hl, he]), ite_eq_left (by omega_using [h])]
      exact congrArg Prod.fst (op_idx op _ zi (by omega_using []) (by omega_using []) (by omega_using [he]))
    · rw [ite_eq_right h, hR _ (by omega_using [hi, hl, he]), ite_eq_left (by omega_using [hl, he]), ite_eq_right (by omega_using [h])]
      exact congrArg Prod.snd (op_idx op _ zi (by omega_using [h]) (by omega_using []) (by omega_using [he]))

end

end VG.Proof.MlDsa.X86_64.Arith.Lazy

end

end

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith hiding bfly blockN layF
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep sel)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Spec.MlDsa (zetas)

theorem lane_lazyBfly : laneSseBlock (toY lazyBfly) = some lazyBfly := by decide +kernel
theorem lane_core2f : laneSseBlock (toY (gath2 ++ lazyBfly ++ scat2)) = some (gath2 ++ lazyBfly ++ scat2) := by
  decide +kernel
theorem lane_core1f : laneSseBlock (toY (gath1 ++ lazyBfly ++ scat1)) = some (gath1 ++ lazyBfly ++ scat1) := by
  decide +kernel

structure LIY (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : YConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LIY.seq {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l c : Prog isa}
    {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, YConsts s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F → Tab zmTab s.mem sP 256 →
      pR fP ∈ s.wr → pR sP ∈ s.wr → WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInvY fP s s')
    (hc : ∀ s, LIY fP sP s₀ F' s → WP isa c s Q) {s : State} (hI : LIY fP sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

theorem yfwdLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat)
    (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 128 / len = k) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay lazyBfly len k 4) s fun s' => PolyIs s'.mem fP (layer F len) ∧ BInvY fP s s' := by
  rw [layer]
  exact ylay_ok bfly_ok lane_lazyBfly (block_ok op) hlen 4 (fun c => 128 / len + c) (by rw [hk]; rfl)
    (fun c hc => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      rcases hlen with rfl | rfl | rfl | rfl | rfl <;> omega_using [hc])
    (fun c _ => step_fwd _ _ 1 (by decide)) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay4_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 lazyBfly 32 0x00 0x55 8) s fun s' => PolyIs s'.mem fP (layer F 4) ∧ BInvY fP s s' := by
  have h0 : ∀ e < 4, sel 0x00 e = 0 := by decide
  have h5 : ∀ e < 4, sel 0x55 e = 1 := by decide
  rw [layer, show 128 / 4 = 32 from rfl]
  exact ylay4_ok bfly_ok lane_lazyBfly (block_ok op) 32 0x00 0x55 8 (fun c => 32 + c) (fun m => 32 + 2 * m) rfl
    (fun m _ => by omega_arith) (fun m _ e he => ⟨by rw [h0 e he]; omega_using [], by rw [h5 e he]; omega_using []⟩)
    (fun m _ => (step_fwd _ _ 2 (by decide)).trans (congrArg _ (by omega_using []))) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 lazyBfly 64 0xA0 0xF5 16) s fun s' => PolyIs s'.mem fP (layer F 2) ∧ BInvY fP s s' := by
  have hA : ∀ e < 4, sel 0xA0 e = 2 * (e / 2) := by decide
  have hF : ∀ e < 4, sel 0xF5 e = 1 + 2 * (e / 2) := by decide
  rw [layer, show 128 / 2 = 64 from rfl]
  exact ylay2_ok (block_ok op) bfly_ok lane_core2f 64 0xA0 0xF5 16 (fun c => 64 + c) (fun i => 64 + 4 * i) rfl
    (fun i _ => by omega_arith) (fun i _ e he => ⟨by rw [hA e he]; omega_using [], by rw [hF e he]; omega_using []⟩)
    (fun i _ => (step_fwd _ _ 4 (by decide)).trans (congrArg _ (by omega_using []))) hc hdi hsi hS hT hwf hw hd

theorem yfwdLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay1 lazyBfly 128 yzeta8 32) s fun s' => PolyIs s'.mem fP (layer F 1) ∧ BInvY fP s s' := by
  rw [layer, show 128 / 1 = 128 from rfl]
  exact ylay1_ok (block_ok op) bfly_ok lane_core1f 128 yzeta8 32 (fun c => 128 + c) (fun i => 128 + 8 * i) rfl
    (fun i _ => by omega_arith)
    (fun i hi s h8 hin hT => WP.mono (yzeta8_ok (by omega_using [hi]) h8 hin hT) fun _ ⟨z, o⟩ =>
      ⟨fun l hl => ⟨(z l hl).1.congr fun e he => congrArg zetas (by omega_using []), (z l hl).2⟩, o⟩)
    (fun i _ => (step_fwd _ _ 8 (by decide)).trans (congrArg _ (by omega_using []))) hc hdi hsi hS hT hwf hw hd


end VG.Proof.MlDsa.X86_64.Arith.Lazy

end

end

/-! ### `MlDsa.X86_64.Arith.YNtt`, which this module and modules that import it used -/

section

/-!
# ML-DSA on x86-64: the frame of the NTT and its inverse on AVX2 registers

What the NTT and its inverse on AVX2 registers (`LazyNtt.lean`) share: the
code sets no MXCSR of its own (`ymx_correct`); the prologue leaves the table of zetas in `scratch` and the
constants in both lanes (`ypro_ok`), with which the layers start (`LIY`,
`ynttBody_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly YOnly ylanes yld_ok yconst_ok ifp ifn sel GOnly WP.keep writesOnly
  gprPreserved_of mxR add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop yconst)
open VG.Spec.MlDsa (q n Poly Zq zetas ntt nttInv)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs)

/-! ## The prologue and the layers -/

/-- The table of zetas and the constants. -/
theorem ypro_ok {sP : Addr} {s : State} (hsi : s.gpr .rsi = sP) (hw : pR sP ∈ s.wr) :
    WP isa (.block ypro) s fun s' => Tab zmTab s'.mem sP 256 ∧ YConsts s' ∧
      Frame [pR sP] s.mem s'.mem ∧ Keep [.r9, .rax] s s' ∧ s'.mxcsr = s.mxcsr := by
  rw [ypro, WP.block_append_iff]
  refine WP.mono (ytabFill_ok zetaTbl zmTab (fun k => Nat.lt_trans (zmTab_lt k) (by decide)) (by decide) hsi hw)
    fun s1 ⟨hT, hf, k1, x1⟩ => WP.mono (yconsts_ok s1) fun s2 ⟨hc, k2, m2, x2, _⟩ =>
      ⟨by rw [m2]; exact hT, hc, by rw [m2]; exact hf, (k1.trans k2).mono (by simp), by rw [x2, x1]⟩

/-- Between the layers: the polynomial `F` at `fP`, the table at `sP`, and
the constants in both lanes. -/
structure LIY (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : YConsts s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-! ## The functions -/

/-- The code, from its state `s1`: the prologue, then the
layers `l`, which leave `G`. -/
theorem ynttBody_ok {t : Poly → Poly} {s s1 : State} (hs : (inPlaceK t).pre s) {l : Prog isa} {G : Poly}
    (k1 : Keep [.rax, .r11] s s1) (f1 : Frame [mxR (s.gpr .rsi)] s.mem s1.mem)
    (hl : ∀ s2, LIY (s.gpr .rdi) (s.gpr .rsi) s2 (polyAt s.mem (s.gpr .rdi)) s2 → s2.gpr .rdi = s.gpr .rdi →
      s2.gpr .rsi = s.gpr .rsi → pR (s.gpr .rdi) ∈ s2.wr → pR (s.gpr .rsi) ∈ s2.wr →
      WP isa l s2 fun s3 => PolyIs s3.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi)] s2.mem s3.mem) :
    WP isa (.seq (.block ypro) l) s1 fun s' =>
      PolyIs s'.mem (s.gpr .rdi) G ∧ Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem := by
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hdi1 : s1.gpr .rdi = s.gpr .rdi := k1.gpr (by decide)
  have hsi1 : s1.gpr .rsi = s.gpr .rsi := k1.gpr (by decide)
  have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _))
      ⟨hs.2.2.2.2.2, rfl⟩
  refine WP.seq (WP.mono (ypro_ok hsi1 (by rw [k1.2.2]; exact hw)) fun s2 ⟨hT, hc, hf2, k2, _⟩ => ?_)
  have hF2 : PolyIs s2.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF1
  refine WP.mono (hl s2 ⟨hF2, hT, hc, Keep.refl _ _, Frame.refl _ _⟩
    (by rw [k2.gpr (by decide), hdi1]) (by rw [k2.gpr (by decide), hsi1])
    (by rw [k2.2.2, k1.2.2]; exact hwf) (by rw [k2.2.2, k1.2.2]; exact hw)) fun s3 ⟨hP, hf3⟩ => ⟨hP, ?_⟩
  refine (frame_fs f1 ?_).trans ((frame_fs hf2 ?_).trans (frame_fs hf3 ?_)) <;>
    intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
  exacts [.inr (mx_sub' _), .inr fun _ h => h, .inl fun _ h => h]

/-- The body, and the ABI. -/
theorem ymx_correct {t : Poly → Poly} {l : Prog isa} (s : State) (hs : (inPlaceK t).pre s)
    (hctl : ctlOk (.seq (.block ypro) l : Prog isa) = true)
    (hk' : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r11])
      (.seq (.block ypro) l : Prog isa) = true)
    (hl : ∀ s1, Keep [.rax, .r11] s s1 → Frame [mxR (s.gpr .rsi)] s.mem s1.mem →
      WP isa (.seq (.block ypro) l) s1 fun s' => PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi))) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rsi)] s.mem s'.mem) :
    ∃ tr s', Exec isa (.seq (.block ypro) l : Prog isa) s tr s' ∧
      abiPreserved s s' ∧ (inPlaceK t).post s s' := by
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  have hW := noMx_ok (c := .seq (.block ypro) l) hl
  obtain ⟨tr, s', he, ⟨s2, ⟨hP, hf⟩, hf', -⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r11] hW (writesOnly_of hk')
  refine ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk (by decide)
    (hf.trans (hf'.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩))
    (by simpa using ⟨hs.2.2.2.1, hs.2.2.2.2.1⟩)), ?_⟩
  · rw [List.mem_singleton.mp hr]; exact mx_sub' _
  · exact polyIs_frame hf' (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _)) hP

end VG.Proof.MlDsa.X86_64.Arith

end

end

/-! ### `MlDsa.X86_64.Arith.LazyNormalize`, which only this module used -/

section

/-! ### `MlDsa.X86_64.Arith.LazyReduce`, which only this module used -/

section

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (XOnly)
open VG.Impl.MlKem.X86_64 (xb xmov)
open VG.Spec.MlDsa (q Zq)

def foldL (x : BitVec 32) : BitVec 32 := x - ((x >>> 23) <<< 23) + ((x >>> 23) <<< 13) - (x >>> 23)

theorem foldL_toNat (x : BitVec 32) (hx : x.toNat < 17 * q) :
    (foldL x).toNat = x.toNat % 8388608 + x.toNat / 8388608 * 8191 := by
  simp only [foldL, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  change x.toNat < 17 * 8380417 at hx
  omega_using []

theorem reduceL_toNat (x : BitVec 32) (hx : x.toNat < 17 * q) :
    (csubL (foldL x)).toNat = x.toNat % q := by
  have hf := final_reduce hx
  rw [csubL_toNat (by rw [foldL_toNat x hx]; exact hf.1), foldL_toNat x hx, condSub_eq hf.1, hf.2]

theorem dword_psrld (a : BitVec 128) (k : BitVec 8) (hk : k.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .psrld a k) i = dword a i >>> k.toNat := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval, show ¬ 31 < k.toNat by omega_using [hk]]

theorem dword_pslld (a : BitVec 128) (k : BitVec 8) (hk : k.toNat < 32) {i : Nat} (hi : i < 4) :
    dword (XShiftOp.eval .pslld a k) i = dword a i <<< k.toNat := by
  rcases cases4 hi with rfl | rfl | rfl | rfl <;> simp [XShiftOp.eval, show ¬ 31 < k.toNat by omega_using [hk]]

def foldV (x : BitVec 128) : BitVec 128 :=
  let t := XShiftOp.eval .psrld x 23
  XBinOp.eval .psubd (XBinOp.eval .paddd
    (XBinOp.eval .psubd x (XShiftOp.eval .pslld t 23)) (XShiftOp.eval .pslld t 13)) t

theorem dword_foldV (x : BitVec 128) {i : Nat} (hi : i < 4) :
    dword (foldV x) i = foldL (dword x i) := by
  rw [foldV, dword_psubd _ _ hi, dword_paddd _ _ hi, dword_psubd _ _ hi,
    dword_pslld _ _ (by decide) hi, dword_pslld _ _ (by decide) hi, dword_psrld _ _ (by decide) hi]
  rfl

theorem reduce_ok {s : State} (hc : Arith.VConsts s) {a : Nat → Word}
    (ha : DLanes (s.xmm .xmm0) a) (hb : ∀ i < 4, (a i).val < 17 * q) :
    WP isa (.block reduceLazy) s fun s' =>
      Arith.DLanes (s'.xmm .xmm0) (fun i => residue (a i)) ∧ XOnly [.xmm0, .xmm1, .xmm2] s s' := by
  simp only [reduceLazy, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  vrun [eval_movdqa]
  rw [hc.q]
  refine ⟨?_, by xonly⟩
  change Arith.DLanes (csubV (foldV (s.xmm .xmm0))) _
  intro i hi
  rw [dword_csubV _ hi, dword_foldV _ hi, reduceL_toNat _ (by rw [ha i hi]; exact hb i hi), ha i hi]
  rfl

end VG.Proof.MlDsa.X86_64.Arith.Lazy

end

end


@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok ifp ifn GOnly
  add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (toY rcxLoop)
open VG.Spec.MlDsa (q n)
open VG.Proof.MlDsa (coeffAt)

def Normalized (m : Mem) (fP : Addr) (G : Poly) (i : Nat) : Prop :=
  ∀ k < 256, (coeffAt m fP k).toNat = if k < 8 * i then (residue G[k]!).val else G[k]!.val

abbrev reduceBody : List Instr :=
  [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0)] ++ toY reduceLazy ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .alu .add .rdx (.imm 32)] ++ [.alu .sub .rcx (.imm 1)]

theorem normalize_step {fP : Addr} {G : Poly} {i : Nat} (hi : i < 32) {s : State} (hc : YConsts s)
    (hb : ∀ k < 256, G[k]!.val < 17 * q)
    (hdx : s.gpr .rdx = coeffAddr fP (8 * i)) (hS : Normalized s.mem fP G i) (hw : pR fP ∈ s.wr) :
    WP isa (.block reduceBody) s fun s' =>
      Normalized s'.mem fP G (i + 1) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : 8 * i + 8 ≤ 256 := by omega_using [hi]
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right _ hw) j0
  rw [reduceBody, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (by decide +kernel)
    (P := fun l t => Arith.DLanes (t.xmm .xmm0) (fun e => residue G[8 * i + 4 * l + e]!))
    fun l hl => reduce_ok (yonly_yconsts o1 hc (by decide) (by decide) (by decide) l hl).toVConsts
      (fun e he => by
        rw [State.proj_xmm, L1 l hl, hdx, add_ofNat_zero, dword_readW _ _ he, lane_load,
          coeffAddr_add, ← coeffAt_eq, hS _ (by omega_using [hi, hl, he]), ifn (by omega_using [])])
      (fun e he => hb _ (by omega_using [hi, hl, he]))) fun s2 ⟨V2, o2⟩ => ?_
  have o12 := o1.trans o2
  have hv : ∀ l < 2, ∀ e < 4, (dword (s2.lane .xmm0 l) e).toNat = (residue G[8 * i + 4 * l + e]!).val :=
    fun l hl e he => V2 l hl e he
  have w0 : InRegions s2.wr (s2.gpr .rdx) 32 := by rw [o12.wr, o12.gpr, hdx]; exact f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    w0, sx32]
  have g2 : s2.gpr .rdx = coeffAddr fP (8 * i) := by rw [o12.gpr, hdx]
  rw [g2, o12.mem]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega_using [h]), State.ymm, extract_ymm _ _ (by omega_using [h])]
      split
      · have := hv 0 (by decide) (k - 8 * i) (by omega_arith)
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega_using [h]] at this; exact this
      · have := hv 1 (by decide) (k - 8 * i - 4) (by omega_using [h])
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega_arith] at this; exact this
    · rename_i h
      rw [hS k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega_using [h'])]
      · rw [ifn h', ifn (by omega_using [h, h'])]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show 8 * i + 8 = 8 * (i + 1) by omega_using []]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP j0)
  · exact ylanes_gpr (s := s2) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o12 hc
      (by decide) (by decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o12.wr]
  · rw [o12.gpr]
  · rw [o12.gpr]
  · exact o12.mxcsr


theorem normalize_ok {fP : Addr} {G : Poly} {f : VG.Spec.MlDsa.Poly}
    (hr : Rel 17 G f) (s : State) (hc : YConsts s) (hdi : s.gpr .rdi = fP)
    (hS : PolyIs s.mem fP G) (hwf : pR fP ∈ s.wr) :
    WP isa normalizeLazy s fun s' => VG.Proof.MlDsa.PolyIs s'.mem fP f ∧ BInvY fP s s' := by
  refine WP.seq ?_
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by vrund [hdi]; exact ⟨by gonlyd, rfl⟩) fun w ⟨hdx, og, hy⟩ => ?_
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide)
    (fun i u => Normalized u.mem fP G i ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧ YConsts u ∧
      Keep [.rcx, .rdx] w u ∧ Frame [pR fP] w.mem u.mem ∧ u.mxcsr = w.mxcsr)
    (fun u o hu _ => ⟨fun k hk => by
        rw [o.mem, og.mem, ifn (by omega_using [])]; exact polyIs_toNat hS hk,
      by rw [o.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      ylanes_gpr (s := w) (o.lane hu) (YOnly.refl [] w) cw (by decide) (by decide),
      o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun i hi u ⟨hS', hdx', hc', hk', hf', hx'⟩ => WP.mono (normalize_step hi hc'
        (fun k hk => (hr k hk).1) hdx' hS' (by rw [hk'.2.2, og.keep.2.2]; exact hwf))
      fun u' ⟨hS'', hdx'', hf'', hc'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', (hk'.trans hk'').mono (by simp), hf'.trans hf'', hx''.trans hx'⟩, hcx, hzf⟩))
    fun u ⟨hS', _, hc', hk', hf', hx'⟩ => ?_
  refine ⟨VG.Proof.MlDsa.Arith.polyIs_of_toNat fun k hk => ?_,
    ⟨(og.keep.trans hk').mono (by simp), by rw [← og.mem]; exact hf', hc', hx'.trans og.mxcsr⟩⟩
  rw [hS' k hk, ifp (by omega), (hr k hk).2]

end VG.Proof.MlDsa.X86_64.Arith.Lazy

end

end

/-! Lazy forward NTT: range/congruence through eight layers, followed by
canonical reduction, under the existing public NTT contract. -/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep yconst_ok)
open VG.Spec.MlDsa (ntt)
open VG.Proof.MlDsa (polyAt)

def transform (F : Poly) : Poly :=
  layer (layer (layer (layer (layer (layer (layer (layer F 128) 64) 32) 16) 8) 4) 2) 1

theorem transform_rel (f : VG.Spec.MlDsa.Poly) : Rel 17 (transform (lift f)) (ntt f) := by
  have h0 := lift_rel f
  have h1 := layer_rel (by decide : 1 ≤ 15) h0 (by decide : 128 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h2 := layer_rel (by decide : 3 ≤ 15) h1 (by decide : 64 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h3 := layer_rel (by decide : 5 ≤ 15) h2 (by decide : 32 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h4 := layer_rel (by decide : 7 ≤ 15) h3 (by decide : 16 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h5 := layer_rel (by decide : 9 ≤ 15) h4 (by decide : 8 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h6 := layer_rel (by decide : 11 ≤ 15) h5 (by decide : 4 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h7 := layer_rel (by decide : 13 ≤ 15) h6 (by decide : 2 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h8 := layer_rel (by decide : 15 ≤ 15) h7 (by decide : 1 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  simpa only [ntt_eq_layers, nttLens, List.foldl_cons, List.foldl_nil, transform] using h8

theorem lift_mem {m : Mem} {p : Addr} {f : VG.Spec.MlDsa.Poly} (hp : VG.Proof.MlDsa.PolyIs m p f) :
    PolyIs m p (lift f) := by
  intro i hi
  rw [VG.Proof.MlDsa.Arith.polyIs_toNat hp hi, getElem!_pos (lift f) i hi, lift, Vector.getElem_map,
    getElem!_pos f i hi]

theorem correct (s : State) (hs : (inPlaceK ntt).pre s) :
    ∃ t s', Exec isa lazyNtt s t s' ∧ abiPreserved s s' ∧ (inPlaceK ntt).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    ynttBody_ok hs k1 f1 (G := ntt (polyAt s.mem (s.gpr .rdi))) fun s2 hI hdi hsi hwf hw => ?_
  refine WP.seq (WP.mono (yconst_ok .xmm11 16760834 s2) fun w ⟨lc, kc, mc, _, oc⟩ => ?_)
  have hc : YConsts w := fun l hl => ⟨⟨by
      rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hI.c l hl).q,
    by rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hI.c l hl).qinv⟩,
    by rw [State.proj_xmm, lc l hl]; rfl⟩
  have hi : LIY (s.gpr .rdi) (s.gpr .rsi) s2 (lift (polyAt s.mem (s.gpr .rdi))) w :=
    ⟨by rw [mc]; exact lift_mem hI.P, by rw [mc]; exact hI.T, hc,
      kc.mono (by simp), by rw [mc]; exact Frame.refl _ _⟩
  refine LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 128 1 (by decide) (by decide)) ?_ hi
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 64 2 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 32 4 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 16 8 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay_ok hd 8 16 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay4_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay2_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yfwdLay1_ok hd) ?_ hI
  intro u hu
  refine WP.seq (WP.mono (normalize_ok (transform_rel _) u hu.c
    (by rw [hu.keep.gpr (by decide), hdi]) hu.P (by rw [hu.keep.2.2]; exact hwf)) fun v ⟨hv, hb⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = v.mem) (by simp only [yepi]; vrund; rfl) fun u' hm => ?_
  rw [hm]
  exact ⟨hv, hu.frame.trans hb.frame⟩

theorem ct : ConstantTime isa (inPlaceK ntt).pre (inPlaceK ntt).pub lazyNtt :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem verified : Verified X86_64.target lazyNtt (Proof.MlDsa.nttContract X86_64.abi) :=
  Verified.of_correct correct ct (by
    mldsa_implies [Proof.MlDsa.nttContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith.Lazy
