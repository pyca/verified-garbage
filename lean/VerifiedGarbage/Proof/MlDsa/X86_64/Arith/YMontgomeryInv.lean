module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YNtt
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
public import VerifiedGarbage.Spec.MlDsa.Montgomery
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay21
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyButterfly
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyInvariant
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyBase
public import VerifiedGarbage.Proof.MlDsa.Arith.LazyButterfly
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YNtt
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
meta import VerifiedGarbage.Spec.MlDsa.Montgomery
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay21
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyButterfly
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyInvariant
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyBase
meta import VerifiedGarbage.Proof.MlDsa.Arith.LazyButterfly
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21

@[expose] public section

/-! # ML-DSA on x86-64: `vg_mldsa_montgomery_inv_ntt_avx2`

The eight layers of `NTT⁻¹` with the lazy butterfly `vibflyLazy`, on unsigned
doublewords whose bound doubles each layer from `q` to `256 q` (`layerInv_rel`)
while their residues are the specification's (`opInv_residue`), with `128 q`
in `xmm11` (`YConstsW bInvC`); then the multiplication by `R/256`, which
accepts any doubleword and reduces (`montScaleL_ok`). -/

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy
open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith hiding bfly blockN layF
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep sel)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Spec.MlDsa (q Zq n zetas)

/-- A layer of `NTT⁻¹` with the lazy butterfly. -/
def layerInv (F : Poly) (len : Nat) : Poly :=
  layF (fun f len k st t => blockN (bfly opInv) f len (zetas k) st t) F len (fun c => 256 / len - 1 - c) (128 / len)

theorem layerInv_rel {b : Nat} (hb1 : 1 ≤ b) (hb : b ≤ 128) {F : Poly} {f : VG.Spec.MlDsa.Poly} (hF : Rel b F f)
    {len : Nat} (hlen : len ∈ [1, 2, 4, 8, 16, 32, 64, 128]) :
    Rel (2 * b) (layerInv F len) (nttInvLayer f len) := by
  have hl : 0 < len ∧ 2 * len * (128 / len) = 256 ∧
      ∀ i < 256, (i % (2 * len) < len → i + len < 256) ∧ (¬ i % (2 * len) < len → len ≤ i) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩
    all_goals intro i hi; omega
  intro i hi
  rw [layerInv, layF_get (block_ok opInv) F hl.1 _ (by omega) hi,
    VG.Proof.MlDsa.X86_64.Arith.nttInvLayer_eq, Arith.layF_get nttInvBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    have h0 := hF i hi
    have h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    have hx := Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb)
    have hy := Nat.lt_of_lt_of_le h1.1 (Nat.mul_le_mul_right q hb)
    exact ⟨(opInv_bound _ _ _ hb1 hb h0.1 h1.1).1, by rw [(opInv_residue _ _ _ hx hy).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    have h0 := hF (i - len) (by omega)
    have h1 := hF i hi
    have hx := Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb)
    have hy := Nat.lt_of_lt_of_le h1.1 (Nat.mul_le_mul_right q hb)
    exact ⟨(opInv_bound _ _ _ hb1 hb h0.1 h1.1).2, by rw [(opInv_residue _ _ _ hx hy).2, h0.2, h1.2]⟩

def transformInv (F : Poly) : Poly :=
  layerInv (layerInv (layerInv (layerInv (layerInv (layerInv (layerInv (layerInv F 1) 2) 4) 8) 16) 32) 64) 128

theorem transformInv_rel (f : VG.Spec.MlDsa.Poly) :
    Rel 256 (transformInv (lift f)) (nttInvLens.foldl nttInvLayer f) := by
  have h0 := lift_rel f
  have h1 := layerInv_rel (by decide) (by decide : 1 ≤ 128) h0 (by decide : 1 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h2 := layerInv_rel (by decide) (by decide : 2 * 1 ≤ 128) h1 (by decide : 2 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h3 := layerInv_rel (by decide) (by decide : 2 * (2 * 1) ≤ 128) h2 (by decide : 4 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h4 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * 1)) ≤ 128) h3
    (by decide : 8 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h5 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * 1))) ≤ 128) h4
    (by decide : 16 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h6 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * (2 * 1)))) ≤ 128) h5
    (by decide : 32 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h7 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * (2 * (2 * 1))))) ≤ 128) h6
    (by decide : 64 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h8 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * (2 * (2 * (2 * 1)))))) ≤ 128) h7
    (by decide : 128 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  simpa only [nttInvLens, List.foldl_cons, List.foldl_nil, transformInv] using h8

theorem lane_vibflyLazy : laneSseBlock (toY vibflyLazy) = some vibflyLazy := by decide +kernel
theorem lane_core2l : laneSseBlock (toY (gath2 ++ vibflyLazy ++ scat2)) = some (gath2 ++ vibflyLazy ++ scat2) := by
  decide +kernel
theorem lane_core1l : laneSseBlock (toY (gath1 ++ vibflyLazy ++ scat1)) = some (gath1 ++ vibflyLazy ++ scat1) := by
  decide +kernel

theorem yinvLay_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) (len k : Nat)
    (hlen : len ∈ [8, 16, 32, 64, 128]) (hk : 256 / len - 1 = k) {F : Poly} (s : State) (hc : YConstsW bInvC s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay vibflyLazy len k (-4)) s fun s' => PolyIs s'.mem fP (layerInv F len) ∧ BInvYW bInvC fP s s' := by
  have hl : 128 / len ≥ 1 ∧ 256 / len = 2 * (128 / len) ∧ 256 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [layerInv]
  exact ylay_ok bflyInv_ok lane_vibflyLazy (block_ok opInv) hlen (-4) (fun c => 256 / len - 1 - c) (by rw [hk]; rfl)
    (fun c _ => by omega)
    (fun c hc' => (congrArg (· + _) (congrArg (coeffAddr sP) (show 256 / len - 1 - c =
      256 / len - 1 - (c + 1) + 1 by omega))).trans (step_bwd _ _ 1 (by decide)))
    hc hdi hsi hS hT hwf hw hd

theorem yinvLay4_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConstsW bInvC s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vibflyLazy 62 0x55 0x00 (-8)) s fun s' => PolyIs s'.mem fP (layerInv F 4) ∧ BInvYW bInvC fP s s' := by
  have h0 : ∀ e < 4, sel 0x00 e = 0 := by decide
  have h5 : ∀ e < 4, sel 0x55 e = 1 := by decide
  rw [layerInv, show 256 / 4 - 1 = 63 from rfl, show 128 / 4 = 32 from rfl]
  exact ylay4_ok bflyInv_ok lane_vibflyLazy (block_ok opInv) 62 0x55 0x00 (-8) (fun c => 63 - c) (fun m => 62 - 2 * m)
    rfl (fun m _ => by omega) (fun m _ e he => ⟨by rw [h5 e he]; omega, by rw [h0 e he]; omega⟩)
    (fun m _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 62 - 2 * m = 62 - 2 * (m + 1) + 2 by
      omega))).trans (step_bwd _ _ 2 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem yinvLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConstsW bInvC s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vibflyLazy 124 0x5F 0x0A (-16)) s fun s' => PolyIs s'.mem fP (layerInv F 2) ∧
      BInvYW bInvC fP s s' := by
  have hA : ∀ e < 4, sel 0x5F e = 3 - 2 * (e / 2) := by decide
  have hB : ∀ e < 4, sel 0x0A e = 2 - 2 * (e / 2) := by decide
  rw [layerInv, show 256 / 2 - 1 = 127 from rfl, show 128 / 2 = 64 from rfl]
  exact ylay2_ok (block_ok opInv) bflyInv_ok lane_core2l 124 0x5F 0x0A (-16) (fun c => 127 - c)
    (fun i => 124 - 4 * i) rfl (fun i _ => by omega)
    (fun i _ e he => ⟨by rw [hA e he]; omega, by rw [hB e he]; omega⟩)
    (fun i _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 124 - 4 * i = 124 - 4 * (i + 1) + 4 by
      omega))).trans (step_bwd _ _ 4 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem yinvLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConstsW bInvC s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay1 vibflyLazy 248 yzeta8R (-32)) s fun s' => PolyIs s'.mem fP (layerInv F 1) ∧
      BInvYW bInvC fP s s' := by
  rw [layerInv, show 256 / 1 - 1 = 255 from rfl, show 128 / 1 = 128 from rfl]
  exact ylay1_ok (block_ok opInv) bflyInv_ok lane_core1l 248 yzeta8R (-32) (fun c => 255 - c)
    (fun i => 248 - 8 * i) rfl (fun i _ => by omega)
    (fun i hi s h8 hin hT => WP.mono (yzeta8R_ok (by omega) h8 hin hT) fun _ ⟨z, o⟩ =>
      ⟨fun l hl => ⟨(z l hl).1.congr fun e he => congrArg zetas (by omega), (z l hl).2⟩, o⟩)
    (fun i _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 248 - 8 * i = 248 - 8 * (i + 1) + 8 by
      omega))).trans (step_bwd _ _ 8 (by decide))) hc hdi hsi hS hT hwf hw hd

/-- Between the lazy layers of `NTT⁻¹`, from `s₀`. -/
structure LII (fP sP : Addr) (s₀ : State) (F : Poly) (s : State) : Prop where
  P : PolyIs s.mem fP F
  T : Tab zmTab s.mem sP 256
  c : YConstsW bInvC s
  keep : Keep [.rax, .rcx, .rdx, .r8] s₀ s
  frame : Frame [pR fP] s₀.mem s.mem

/-- A layer, then `c`. -/
theorem LII.seq {fP sP : Addr} {s₀ : State} (hdi : s₀.gpr .rdi = fP) (hsi : s₀.gpr .rsi = sP)
    (hwf : pR fP ∈ s₀.wr) (hw : pR sP ∈ s₀.wr) (hd : (pR sP).Disjoint (pR fP)) {l c : Prog isa}
    {F F' : Poly} {Q : State → Prop}
    (hl : ∀ s, YConstsW bInvC s → s.gpr .rdi = fP → s.gpr .rsi = sP → PolyIs s.mem fP F →
      Tab zmTab s.mem sP 256 → pR fP ∈ s.wr → pR sP ∈ s.wr →
      WP isa l s fun s' => PolyIs s'.mem fP F' ∧ BInvYW bInvC fP s s')
    (hc : ∀ s, LII fP sP s₀ F' s → WP isa c s Q) {s : State} (hI : LII fP sP s₀ F s) :
    WP isa (.seq l c) s Q :=
  WP.seq (WP.mono (hl s hI.c (by rw [hI.keep.gpr (by decide), hdi]) (by rw [hI.keep.gpr (by decide), hsi]) hI.P
      hI.T (by rw [hI.keep.2.2]; exact hwf) (by rw [hI.keep.2.2]; exact hw))
    fun s' ⟨hS, hb⟩ => hc s' ⟨hS, hI.T.frame hb.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
      (by decide), hb.consts, (hI.keep.trans hb.keep).mono (by decide), hI.frame.trans hb.frame⟩)

end VG.Proof.MlDsa.X86_64.Arith.Lazy

namespace VG.Proof.MlDsa.X86_64.Arith.MontgomeryInv

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok ifp ifn sel GOnly WP.keep writesOnly
  gprPreserved_of withMxcsr_ok mxR add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop yconst)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs zetas ntt nttInv)
open VG.Proof.MlDsa.Arith.Lazy (residue Word)

/-! ## The multiplication by `R/256` of any doublewords -/

/-- `16382 · 2³² mod q` in each doubleword. -/
theorem scale_lanes : ZLanes (ofDwords 41978#32 41978#32 41978#32 41978#32) (fun _ => 16382) ∧
    ZOdd (ofDwords 41978#32 41978#32 41978#32 41978#32) (ofDwords 41978#32 41978#32 41978#32 41978#32) :=
  ⟨fun i hi => by rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide,
    fun j hj => by rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide⟩

/-- A product of any doubleword by a zeta in Montgomery form, reduced: `ζ · (b mod q)`. -/
theorem mulZL {b z m : BitVec 32} {ζ : Zq} (hz : z.toNat = ζ.val * 2 ^ 32 % q)
    (hm : m.toNat = mont (b.toNat * z.toNat)) : (csubL m).toNat = (ζ * Fin.ofNat q b.toNat).val := by
  have hx : b.toNat * z.toNat < q * 2 ^ 32 := by
    rw [hz]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le b.isLt (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
      (by decide)) (by rw [Nat.mul_comm])
  rw [csubL_toNat (by rw [hm]; exact mont_lt hx), hm, condSub_mont hx, hz, mont_mulR, Fin.val_mul, Fin.val_ofNat,
    Nat.mul_mod_mod, Nat.mul_comm]

/-- The coefficients of `F` before `8i` multiplied by `16382`, reduced. -/
def YScaledL (m : VG.Mem) (fP : Addr) (F : VG.Proof.MlDsa.Arith.Lazy.Poly) (i : Nat) : Prop :=
  ∀ k < 256, (coeffAt m fP k).toNat = if k < 8 * i then (residue F[k]! * 16382).val else F[k]!.val

theorem montScaleL_step {fP : Addr} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} {i : Nat} (hi : i < 32) {s : State}
    (hc : YConsts s) (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => 16382))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l))
    (hdx : s.gpr .rdx = coeffAddr fP (8 * i)) (hS : YScaledL s.mem fP F i) (hw : pR fP ∈ s.wr) :
    WP isa (.block sbodyY) s fun s' =>
      YScaledL s'.mem fP F (i + 1) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ YConsts s' ∧ (∀ l < 2, s'.lane .xmm13 l = s.lane .xmm13 l) ∧
        (∀ l < 2, s'.lane .xmm12 l = s.lane .xmm12 l) ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have r0 : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 0) 32 := by
    rw [hdx, add_ofNat_zero]; exact f_in32 (List.mem_append_right _ hw) j0
  rw [sbodyY, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok r0) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_vmul3 (P := fun l t =>
      t.xmm .xmm3 = csubV (montV (s1.lane .xmm3 l) (s1.lane .xmm13 l) (s1.lane .xmm12 l)))
    fun l hl => vmul3_ok (yonly_yconsts o1 hc (by decide) (by decide) l hl)) fun s2 ⟨V2, o2⟩ => ?_
  have o12 := o1.trans o2
  have hv : ∀ l < 2, ∀ e < 4, (dword (s2.lane .xmm3 l) e).toNat = (residue F[8 * i + 4 * l + e]! * 16382).val := by
    intro l hl e he
    have hx : ∀ e < 4, (dword (s1.lane .xmm3 l) e).toNat = F[8 * i + 4 * l + e]!.val := fun e he => by
      rw [L1 l hl, hdx, add_ofNat_zero, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq,
        hS _ (by omega), ifn (by omega)]
    have hz' : ZLanes (s1.lane .xmm13 l) (fun _ => 16382) := by
      rw [o1.lane _ (by decide) l hl]; exact hz l hl
    have ho' : ZOdd (s1.lane .xmm13 l) (s1.lane .xmm12 l) := by
      rw [o1.lane _ (by decide) l hl, o1.lane _ (by decide) l hl]; exact ho l hl
    have hb : ∀ e < 4, (dword (s1.lane .xmm3 l) e).toNat * (dword (s1.lane .xmm13 l) e).toNat < q * 2 ^ 32 :=
      fun e he => by
        rw [hz' e he]
        exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (dword (s1.lane .xmm3 l) e).isLt
          (Nat.le_of_lt (Nat.mod_lt _ (by decide))) (by decide)) (by rw [Nat.mul_comm])
    have e2 : s2.lane .xmm3 l = _ := V2 l hl
    rw [e2, dword_csubV _ he, mulZL (hz' e he) (dword_montV ho' hb he), hx e he]
    simp only [residue]
    rw [Fin.mul_comm]
  have w0 : InRegions s2.wr (s2.gpr .rdx) 32 := by rw [o12.wr, o12.gpr, hdx]; exact f_in32 hw j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm,
    w0, sx32]
  have g2 : s2.gpr .rdx = coeffAddr fP (8 * i) := by rw [o12.gpr, hdx]
  rw [g2, o12.mem]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      split
      · have := hv 0 (by decide) (k - 8 * i) (by omega)
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this; exact this
      · have := hv 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this; exact this
    · rename_i h
      rw [hS k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show 8 * i + 8 = 8 * (i + 1) by omega]
  · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP j0)
  · exact ylanes_gpr (s := s2) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o12 hc
      (by decide) (by decide)
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o12.lane _ (by decide) l hl
  · intro l hl; simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact o12.lane _ (by decide) l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o12.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o12.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o12.wr]
  · rw [o12.gpr]
  · rw [o12.gpr]
  · exact o12.mxcsr

/-- Multiply every doubleword by `R/256`, reduced, retaining the Montgomery scale. -/
theorem montScaleL_ok {fP : Addr} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (hS : Lazy.PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) :
    WP isa montScale s fun s' => PolyIs s'.mem fP (F.map fun x => residue x * 16382) ∧
      Keep [.rax, .rcx, .rdx, .r8] s s' ∧ Frame [pR fP] s.mem s'.mem := by
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by vrund [hdi]; exact ⟨by gonlyd, rfl⟩) fun w ⟨hdx, og, hy⟩ => ?_
  refine WP.mono (yconst_ok .xmm13 41978 w) fun w1 ⟨l1, k1, m1, x1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm12 = w1.lane .xmm13 l)
    fun l _ => mov12_ok (w1.proj l)) fun w2 ⟨l2, o2⟩ => ?_
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  have cw2 : YConsts w2 := yonly_yconsts o2 (fun l hl =>
    ⟨by rw [State.proj_xmm, o1 _ (by decide) l hl]; exact (cw l hl).q,
      by rw [State.proj_xmm, o1 _ (by decide) l hl]; exact (cw l hl).qinv⟩) (by decide) (by decide)
  have z13 : ∀ l < 2, w2.lane .xmm13 l = ofDwords 41978#32 41978#32 41978#32 41978#32 := fun l hl => by
    rw [o2.lane _ (by decide) l hl, l1 l hl]; rfl
  have z12 : ∀ l < 2, w2.lane .xmm12 l = ofDwords 41978#32 41978#32 41978#32 41978#32 := fun l hl => by
    have e : w2.lane .xmm12 l = _ := l2 l hl
    rw [e, l1 l hl]; rfl
  have dx2 : w2.gpr .rdx = fP := by rw [o2.gpr, k1.gpr (by decide), hdx]
  have mw2 : w2.mem = s.mem := by rw [o2.mem, m1, og.mem]
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide)
    (fun i u => YScaledL u.mem fP F i ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧ YConsts u ∧
      (∀ l < 2, u.lane .xmm13 l = w2.lane .xmm13 l) ∧ (∀ l < 2, u.lane .xmm12 l = w2.lane .xmm12 l) ∧
      Keep [.rcx, .rdx] w2 u ∧ Frame [pR fP] w2.mem u.mem ∧ u.mxcsr = w2.mxcsr)
    (fun u o hu _ => ⟨fun k hk => by
        rw [o.mem, mw2, ifn (by omega)]; exact Lazy.polyIs_toNat hS (by rw [n_eq]; exact hk),
      by rw [o.keep.gpr (by decide), dx2, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      ylanes_gpr (s := w2) (o.lane hu) (YOnly.refl [] w2) cw2 (by decide) (by decide),
      fun l _ => o.lane hu _ l, fun l _ => o.lane hu _ l, o.keep.mono (by simp),
      by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun i hi u ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (montScaleL_step hi hc'
        (fun l hl => by rw [hz' l hl, z13 l hl]; exact scale_lanes.1)
        (fun l hl => by rw [hz' l hl, hzo' l hl, z13 l hl, z12 l hl]; exact scale_lanes.2) hdx' hS'
        (by rw [hk'.2.2, o2.wr, k1.2.2, og.keep.2.2]; exact hwf))
      fun u' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', fun l hl => by rw [hz'' l hl, hz' l hl], fun l hl => by rw [hzo'' l hl, hzo' l hl],
          (hk'.trans hk'').mono (by simp), hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩))
    fun u ⟨hS', _, _, _, _, hk', hf', _⟩ => ?_
  have kw2 : Keep [.rdx, .rax] s w2 :=
    ((og.keep.trans k1).trans (⟨fun r _ => by rw [o2.gpr], o2.rd, o2.wr⟩ : Keep [] w1 w2)).mono (by simp)
  refine ⟨polyIs_of_toNat fun k hk => ?_, (kw2.trans hk').mono (by simp), by rw [← mw2]; exact hf'⟩
  rw [n_eq] at hk
  rw [hS' k hk, ifp (by omega), getElem!_pos (F.map fun x => residue x * 16382) k hk, Vector.getElem_map,
    getElem!_pos F k hk]

/-! ## The transform -/

theorem inv_eq (f : Poly) : Spec.MlDsa.montgomeryNttInv f =
    (nttInvLens.foldl nttInvLayer f).map (· * 16382) := by
  rw [Spec.MlDsa.montgomeryNttInv, nttInv_eq_layers, Vector.map_map]
  apply congrArg (fun g : Spec.MlDsa.Zq → Spec.MlDsa.Zq => (nttInvLens.foldl nttInvLayer f).map g)
  funext x
  change (x * 8347681) * Spec.MlDsa.montgomeryR = x * 16382
  rw [Fin.mul_assoc]
  have hc : (8347681 : Spec.MlDsa.Zq) * Spec.MlDsa.montgomeryR = 16382 := by decide +kernel
  rw [hc]

theorem map_residue {b : Nat} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} {g : Poly} (h : Lazy.Rel b F g) :
    F.map (fun x => residue x * 16382) = g.map (· * 16382) := by
  apply Vector.ext; intro i hi
  rw [Vector.getElem_map, Vector.getElem_map, ← getElem!_pos F i hi, ← getElem!_pos g i hi, (h i hi).2]

theorem correct (s : State) (hs : (inPlaceK Spec.MlDsa.montgomeryNttInv).pre s) :
    ∃ t s', Exec isa montNttInvAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK Spec.MlDsa.montgomeryNttInv).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (ynttBody_ok hs k1 f1
      (G := (nttInvLens.foldl nttInvLayer (polyAt s.mem (s.gpr .rdi))).map (· * 16382))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [inv_eq]; exact hP, hf⟩
  refine WP.seq (WP.mono (yconst_ok .xmm11 1072693376 s2) fun w ⟨lc, kc, mc, _, oc⟩ => ?_)
  have hc : Lazy.YConstsW Lazy.bInvC w := fun l hl => ⟨⟨by
      rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hI.c l hl).q,
    by rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hI.c l hl).qinv⟩,
    by rw [State.proj_xmm, lc l hl]; rfl⟩
  have hi : Lazy.LII (s.gpr .rdi) (s.gpr .rsi) s2 (Lazy.lift (polyAt s.mem (s.gpr .rdi))) w :=
    ⟨by rw [mc]; exact Lazy.lift_mem hI.P, by rw [mc]; exact hI.T, hc,
      kc.mono (by simp), by rw [mc]; exact Frame.refl _ _⟩
  refine Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay1_ok hd) ?_ hi
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay2_ok hd) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay4_ok hd) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay_ok hd 8 31 (by decide) (by decide)) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay_ok hd 16 15 (by decide) (by decide)) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay_ok hd 32 7 (by decide) (by decide)) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay_ok hd 64 3 (by decide) (by decide)) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd (Lazy.yinvLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  intro u hu
  refine WP.seq (WP.mono (montScaleL_ok u (fun l hl => (hu.c l hl).toVConsts)
    (by rw [hu.keep.gpr (by decide), hdi]) hu.P (by rw [hu.keep.2.2]; exact hwf)) fun v ⟨hv, _, hb⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = v.mem) (by simp only [yepi]; vrund; rfl) fun u' hm => ?_
  rw [hm, ← map_residue (Lazy.transformInv_rel (polyAt s.mem (s.gpr .rdi)))]
  exact ⟨hv, hu.frame.trans hb⟩

theorem ct : ConstantTime isa (inPlaceK Spec.MlDsa.montgomeryNttInv).pre
    (inPlaceK Spec.MlDsa.montgomeryNttInv).pub montNttInvAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem verified : Verified X86_64.target montNttInvAvx2 (Spec.MlDsa.montgomeryNttInvContract X86_64.abi) :=
  Verified.of_correct correct ct (by
    mldsa_implies [Spec.MlDsa.montgomeryNttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith.MontgomeryInv
