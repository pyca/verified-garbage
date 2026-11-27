module

import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mxcsr
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
public import VerifiedGarbage.Proof.MlDsa.Arith.Representation
public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.DotCore
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
meta import VerifiedGarbage.Proof.MlDsa.Arith.Representation
meta import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.VMxcsr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Basic
public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNtt
meta import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
meta import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21

/-! ### `MlDsa.X86_64.Arith.YMontgomeryInv`, which this module and modules that import it used -/

section

@[expose] public section

/-! # ML-DSA on x86-64: `vg_mldsa_montgomery_inv_ntt_avx2`

The eight layers of `NTT⁻¹` with the lazy butterfly `vibflyLazy`, on unsigned
doublewords whose bound doubles each layer from `q` to `256 q` (`layerInv_rel`)
while their residues are the specification's (`opInv_residue`), with `128 q`
in `xmm11` (`YConstsW bInvC`). The last two layers run in one pass with the
multiplication by `R/256`, which accepts any doubleword and reduces
(`ylast_ok`): `lastCore` computes, in each doubleword, the coefficients
`j + 64 r` of the result from the four inputs `j + 64 r'` (`lastG_get`). -/

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
  obtain hl : 0 < len ∧ 2 * len * (128 / len) = 256 ∧
      ∀ i < 256, (i % (2 * len) < len → i + len < 256) ∧ (¬ i % (2 * len) < len → len ≤ i) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨by decide, by decide, ?_⟩
    all_goals intro i hi; omega_using [hi]
  intro i hi
  rw [layerInv, Arith.Lazy.layF_get (block_ok opInv) F hl.1 _ (by omega) hi,
    VG.Proof.MlDsa.X86_64.Arith.nttInvLayer_eq, Arith.layF_get nttInvBlk_ok f hl.1 _ (by omega) hi]
  simp only [ite_eq_left (show i < 2 * len * (128 / len) by omega)]
  by_cases h : i % (2 * len) < len
  · simp only [ite_eq_left h]
    obtain h0 := hF i hi
    obtain h1 := hF (i + len) ((hl.2.2 i hi).1 h)
    obtain hx := Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb)
    obtain hy := Nat.lt_of_lt_of_le h1.1 (Nat.mul_le_mul_right q hb)
    exact ⟨(opInv_bound _ _ _ hb1 hb h0.1 h1.1).1, by rw [(opInv_residue _ _ _ hx hy).1, h0.2, h1.2]⟩
  · simp only [ite_eq_right h]
    obtain h0 := hF (i - len) (by omega_using [hi])
    obtain h1 := hF i hi
    obtain hx := Nat.lt_of_lt_of_le h0.1 (Nat.mul_le_mul_right q hb)
    obtain hy := Nat.lt_of_lt_of_le h1.1 (Nat.mul_le_mul_right q hb)
    exact ⟨(opInv_bound _ _ _ hb1 hb h0.1 h1.1).2, by rw [(opInv_residue _ _ _ hx hy).2, h0.2, h1.2]⟩

def transformInv (F : Poly) : Poly :=
  layerInv (layerInv (layerInv (layerInv (layerInv (layerInv (layerInv (layerInv F 1) 2) 4) 8) 16) 32) 64) 128

/-- The first six layers, whose coefficients stay below `64 q`. -/
theorem transformInv6_rel (f : VG.Spec.MlDsa.Poly) :
    Rel 64 (layerInv (layerInv (layerInv (layerInv (layerInv (layerInv (lift f) 1) 2) 4) 8) 16) 32)
      (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer f 1) 2) 4) 8) 16) 32) := by
  obtain h0 := lift_rel f
  obtain h1 := layerInv_rel (by decide) (by decide : 1 ≤ 128) h0 (by decide : 1 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  obtain h2 := layerInv_rel (by decide) (by decide : 2 * 1 ≤ 128) h1 (by decide : 2 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  obtain h3 := layerInv_rel (by decide) (by decide : 2 * (2 * 1) ≤ 128) h2 (by decide : 4 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  obtain h4 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * 1)) ≤ 128) h3
    (by decide : 8 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  obtain h5 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * 1))) ≤ 128) h4
    (by decide : 16 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  exact layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * (2 * 1)))) ≤ 128) h5
    (by decide : 32 ∈ [1, 2, 4, 8, 16, 32, 64, 128])

theorem transformInv_rel (f : VG.Spec.MlDsa.Poly) :
    Rel 256 (transformInv (lift f)) (nttInvLens.foldl nttInvLayer f) := by
  obtain h7 := layerInv_rel (by decide) (by decide : 64 ≤ 128) (transformInv6_rel f)
    (by decide : 64 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  obtain h8 := layerInv_rel (by decide) (by decide : 2 * 64 ≤ 128) h7
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
  obtain hl : 128 / len ≥ 1 ∧ 256 / len = 2 * (128 / len) ∧ 256 / len ≤ 32 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl <;> decide
  rw [layerInv]
  exact ylay_ok bflyInv_ok lane_vibflyLazy (block_ok opInv) hlen (-4) (fun c => 256 / len - 1 - c) (by rw [hk]; rfl)
    (fun c _ => by omega_using [hl])
    (fun c hc' => (congrArg (· + _) (congrArg (coeffAddr sP) (show 256 / len - 1 - c =
      256 / len - 1 - (c + 1) + 1 by omega_using [hl, hc']))).trans (step_bwd _ _ 1 (by decide)))
    hc hdi hsi hS hT hwf hw hd

theorem yinvLay4_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConstsW bInvC s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay4 vibflyLazy 62 0x55 0x00 (-8)) s fun s' => PolyIs s'.mem fP (layerInv F 4) ∧ BInvYW bInvC fP s s' := by
  obtain h0 : ∀ e < 4, sel 0x00 e = 0 := by decide
  obtain h5 : ∀ e < 4, sel 0x55 e = 1 := by decide
  rw [layerInv, show 256 / 4 - 1 = 63 from rfl, show 128 / 4 = 32 from rfl]
  exact ylay4_ok bflyInv_ok lane_vibflyLazy (block_ok opInv) 62 0x55 0x00 (-8) (fun c => 63 - c) (fun m => 62 - 2 * m)
    rfl (fun m _ => by omega_using []) (fun m _ e he => ⟨by rw [h5 e he]; omega_arith, by rw [h0 e he]; omega_using []⟩)
    (fun m _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 62 - 2 * m = 62 - 2 * (m + 1) + 2 by
      omega_arith))).trans (step_bwd _ _ 2 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem yinvLay2_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConstsW bInvC s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay2 vibflyLazy 124 0x5F 0x0A (-16)) s fun s' => PolyIs s'.mem fP (layerInv F 2) ∧
      BInvYW bInvC fP s s' := by
  obtain hA : ∀ e < 4, sel 0x5F e = 3 - 2 * (e / 2) := by decide
  obtain hB : ∀ e < 4, sel 0x0A e = 2 - 2 * (e / 2) := by decide
  rw [layerInv, show 256 / 2 - 1 = 127 from rfl, show 128 / 2 = 64 from rfl]
  exact ylay2_ok (block_ok opInv) bflyInv_ok lane_core2l 124 0x5F 0x0A (-16) (fun c => 127 - c)
    (fun i => 124 - 4 * i) rfl (fun i _ => by omega_using [])
    (fun i _ e he => ⟨by rw [hA e he]; omega_arith, by rw [hB e he]; omega_arith⟩)
    (fun i _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 124 - 4 * i = 124 - 4 * (i + 1) + 4 by
      omega_arith))).trans (step_bwd _ _ 4 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem yinvLay1_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {F : Poly} (s : State) (hc : YConstsW bInvC s)
    (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP F) (hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) :
    WP isa (ylay1 vibflyLazy 248 yzeta8R (-32)) s fun s' => PolyIs s'.mem fP (layerInv F 1) ∧
      BInvYW bInvC fP s s' := by
  rw [layerInv, show 256 / 1 - 1 = 255 from rfl, show 128 / 1 = 128 from rfl]
  exact ylay1_ok (block_ok opInv) bflyInv_ok lane_core1l 248 yzeta8R (-32) (fun c => 255 - c)
    (fun i => 248 - 8 * i) rfl (fun i _ => by omega_using [])
    (fun i hi s h8 hin hT => WP.mono (yzeta8R_ok (by omega_using []) h8 hin hT) fun _ ⟨z, o⟩ =>
      ⟨fun l hl => ⟨(z l hl).1.congr fun e he => congrArg zetas (by omega_using [hi]), (z l hl).2⟩, o⟩)
    (fun i _ => (congrArg (· + _) (congrArg (coeffAddr sP) (show 248 - 8 * i = 248 - 8 * (i + 1) + 8 by
      omega_arith))).trans (step_bwd _ _ 8 (by decide))) hc hdi hsi hS hT hwf hw hd

theorem layerInv_get (F : Poly) {len : Nat} (hlen : len ∈ [1, 2, 4, 8, 16, 32, 64, 128]) {i : Nat} (hi : i < 256) :
    (layerInv F len)[i]! = if i % (2 * len) < len then
      (opInv F[i]! F[i + len]! (zetas (256 / len - 1 - i / (2 * len)))).1
      else (opInv F[i - len]! F[i]! (zetas (256 / len - 1 - i / (2 * len)))).2 := by
  obtain hl : 0 < len ∧ 2 * len * (128 / len) = 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [layerInv, Arith.Lazy.layF_get (block_ok opInv) F hl.1 _ (by omega_using [hl]) hi, VG.Proof.MlKem.X86_64.ifp (by omega_using [hi, hl])]

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
  gprPreserved_of mxR add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop yconst)
open VG.Spec.MlDsa (q n Poly Zq zetas ntt nttInv)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs)
open VG.Proof.MlDsa.Arith.Lazy (residue Word opInv product product_lt)

/-- A product of any doubleword by a zeta in Montgomery form, reduced: `ζ · (b mod q)`. -/
theorem mulZL {b z m : BitVec 32} {ζ : Zq} (hz : z.toNat = ζ.val * 2 ^ 32 % q)
    (hm : m.toNat = mont (b.toNat * z.toNat)) : (csubL m).toNat = (ζ * Fin.ofNat q b.toNat).val := by
  obtain hx : b.toNat * z.toNat < q * 2 ^ 32 := by
    rw [hz]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le b.isLt (Nat.le_of_lt (Nat.mod_lt _ (by decide)))
      (by decide)) (by rw [Nat.mul_comm])
  rw [csubL_toNat (by rw [hm]; exact mont_lt hx), hm, condSub_mont hx, hz, mont_mulR, Fin.val_mul, Fin.val_ofNat,
    Nat.mul_mod_mod, Nat.mul_comm]

/-! ## The last two layers and the multiplication by `R/256` -/

/-- The sum of `vibflyLazy`. -/
abbrev bsum (a b : BitVec 128) : BitVec 128 := XBinOp.eval .paddd a b

/-- The product of `vibflyLazy`, `ζ · (b - a + 128 q)`, with the zeta in every
doubleword of `z`. -/
abbrev bdif (a b z : BitVec 128) : BitVec 128 :=
  montV (XBinOp.eval .paddd (XBinOp.eval .psubd b a) (ofDwords Lazy.bInvC Lazy.bInvC Lazy.bInvC Lazy.bInvC)) z z

/-- `lastCore`'s results, from the registers of `s`. -/
def LastPost (s s' : State) : Prop :=
  s'.xmm .xmm0 = csubV (montV (bsum (bsum (s.xmm .xmm0) (s.xmm .xmm1)) (bsum (s.xmm .xmm5) (s.xmm .xmm6)))
    (s.xmm .xmm10) (s.xmm .xmm10)) ∧
  s'.xmm .xmm3 = csubV (montV (bsum (bdif (s.xmm .xmm0) (s.xmm .xmm1) (s.xmm .xmm7))
    (bdif (s.xmm .xmm5) (s.xmm .xmm6) (s.xmm .xmm8))) (s.xmm .xmm10) (s.xmm .xmm10)) ∧
  s'.xmm .xmm6 = csubV (bdif (bsum (s.xmm .xmm0) (s.xmm .xmm1)) (bsum (s.xmm .xmm5) (s.xmm .xmm6))
    (s.xmm .xmm9)) ∧
  s'.xmm .xmm5 = csubV (bdif (bdif (s.xmm .xmm0) (s.xmm .xmm1) (s.xmm .xmm7))
    (bdif (s.xmm .xmm5) (s.xmm .xmm6) (s.xmm .xmm8)) (s.xmm .xmm9))

theorem lastCore_ok {s : State} (hc : Lazy.VConstsW Lazy.bInvC s) :
    WP isa (.block lastCore) s fun s' => LastPost s s' ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6] s s' := by
  simp only [lastCore, ibfR, vmont, vredc, vcsub, vcadd, xmov, xb, List.cons_append, List.nil_append]
  -- reads through the writes before their branches: as post-rewrites `simp` visits each discarded branch
  vrun [↓VG.Proof.MlKem.X86_64.xmm_setXmm, ↓reduceIte, eval_movdqa, hc.q, hc.qinv, hc.q2]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by
    repeat (refine VG.Proof.MlKem.X86_64.XOnly.setXmm (by decide) ?_ _)
    exact VG.Proof.MlKem.X86_64.XOnly.refl _ _⟩

theorem lane_lastCore : laneSseBlock (toY lastCore) = some lastCore := by decide +kernel

theorem bsum_lanes {a b : BitVec 128} {x y : Nat → Word} (ha : Lazy.DLanes a x) (hb : Lazy.DLanes b y) (ζ : Zq) :
    Lazy.DLanes (bsum a b) (fun i => (opInv (x i) (y i) ζ).1) := fun i hi => by
  rw [dword_paddd _ _ hi, BitVec.toNat_add, ha i hi, hb i hi]
  simp only [opInv, Fin.val_add]

theorem bdif_lanes {a b z : BitVec 128} {x y : Nat → Word} {ζ : Zq} (ha : Lazy.DLanes a x)
    (hb : Lazy.DLanes b y) (hz : ZLanes z fun _ => ζ) (ho : ZOdd z z) :
    Lazy.DLanes (bdif a b z) (fun i => (opInv (x i) (y i) ζ).2) := by
  obtain hw : Lazy.DLanes (XBinOp.eval .paddd (XBinOp.eval .psubd b a)
      (ofDwords Lazy.bInvC Lazy.bInvC Lazy.bInvC Lazy.bInvC)) (fun i => y i + 1072693376 - x i) := by
    intro i hi
    obtain hb' : (dword (ofDwords Lazy.bInvC Lazy.bInvC Lazy.bInvC Lazy.bInvC) i).toNat = 1072693376 := by
      rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [dword_paddd _ _ hi, BitVec.toNat_add, dword_psubd _ _ hi, BitVec.toNat_sub, ha i hi, hb i hi, hb']
    simp only [Fin.val_sub, Fin.val_add, show (1072693376 : Word).val = 1072693376 from rfl]
    have := (x i).isLt; have := (y i).isLt
    omega_using []
  intro i hi
  rw [dword_montV ho (Lazy.prod_lt hw hz) hi, hw i hi, hz i hi]
  obtain ht := product_lt (y i + 1072693376 - x i) ζ
  obtain ht32 : product (y i + 1072693376 - x i) ζ < 4294967296 := Nat.lt_trans ht (by decide)
  simp only [opInv, Fin.val_ofNat, Nat.mod_eq_of_lt ht32]
  rfl

/-- A doubleword times `R/256`, reduced. -/
theorem scale_dw {x k : BitVec 128} {w : Nat → Word} (hx : Lazy.DLanes x w) (hk : ZLanes k fun _ => 16382)
    (ho : ZOdd k k) {e : Nat} (he : e < 4) : (dword (csubV (montV x k k)) e).toNat = (residue (w e) * 16382).val := by
  obtain hb : ∀ e < 4, (dword x e).toNat * (dword k e).toNat < q * 2 ^ 32 := fun e he => by
    rw [hk e he]
    exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (dword x e).isLt
      (Nat.le_of_lt (Nat.mod_lt _ (by decide))) (by decide)) (by rw [Nat.mul_comm])
  rw [dword_csubV _ he, mulZL (hk e he) (dword_montV ho hb he), hx e he]
  simp only [residue]
  rw [Fin.mul_comm]

/-- A doubleword below `2q`, reduced. -/
theorem csub_dw {x : BitVec 128} {w : Nat → Word} (hx : Lazy.DLanes x w) {e : Nat} (he : e < 4)
    (hw : (w e).val < 2 * q) : (dword (csubV x) e).toNat = (residue (w e)).val := by
  rw [dword_csubV _ he, csubL_toNat (by rw [hx e he]; exact hw), hx e he, condSub_eq hw]
  rfl

/-- A zeta `ζ · 2³² mod q` in every doubleword. -/
theorem bcast_lanes {c : BitVec 32} {ζ : Zq} (h : c.toNat = ζ.val * 2 ^ 32 % q) :
    ZLanes (ofDwords c c c c) (fun _ => ζ) ∧ ZOdd (ofDwords c c c c) (ofDwords c c c c) :=
  ⟨fun i hi => by rcases cases4 hi with rfl | rfl | rfl | rfl <;> simpa using h,
    fun j hj => by rcases (by omega_using [hj] : j = 0 ∨ j = 1) with rfl | rfl <;> simp⟩

/-- The constants of `ylast`: the zetas `3`, `2`, zeta `1` times `R/256`, and `R/256`. -/
def LastK (s : State) : Prop :=
  ∀ l < 2, s.lane .xmm7 l = ofDwords 7861508#32 7861508#32 7861508#32 7861508#32 ∧
    s.lane .xmm8 l = ofDwords 5771523#32 5771523#32 5771523#32 5771523#32 ∧
    s.lane .xmm9 l = ofDwords 4404704#32 4404704#32 4404704#32 4404704#32 ∧
    s.lane .xmm10 l = ofDwords 41978#32 41978#32 41978#32 41978#32

theorem k7 : ZLanes (ofDwords 7861508#32 7861508#32 7861508#32 7861508#32) (fun _ => zetas 3) ∧
    ZOdd (ofDwords 7861508#32 7861508#32 7861508#32 7861508#32) (ofDwords 7861508#32 7861508#32 7861508#32 7861508#32) :=
  bcast_lanes (by decide)
theorem k8 : ZLanes (ofDwords 5771523#32 5771523#32 5771523#32 5771523#32) (fun _ => zetas 2) ∧
    ZOdd (ofDwords 5771523#32 5771523#32 5771523#32 5771523#32) (ofDwords 5771523#32 5771523#32 5771523#32 5771523#32) :=
  bcast_lanes (by decide)
theorem k9 : ZLanes (ofDwords 4404704#32 4404704#32 4404704#32 4404704#32) (fun _ => zetas 1 * 16382) ∧
    ZOdd (ofDwords 4404704#32 4404704#32 4404704#32 4404704#32) (ofDwords 4404704#32 4404704#32 4404704#32 4404704#32) :=
  bcast_lanes (by decide)
theorem k10 : ZLanes (ofDwords 41978#32 41978#32 41978#32 41978#32) (fun _ => 16382) ∧
    ZOdd (ofDwords 41978#32 41978#32 41978#32 41978#32) (ofDwords 41978#32 41978#32 41978#32 41978#32) :=
  bcast_lanes (by decide)

/-- The coefficient `j + 64 r` of the result, from the four inputs `j + 64 r'`
(`r < 4`): `lastCore`'s output `r` in each doubleword. -/
def lastOut (a0 a1 a2 a3 : Word) (r : Nat) : Zq :=
  let b0 := opInv a0 a1 (zetas 3); let b1 := opInv a2 a3 (zetas 2)
  if r = 0 then residue (opInv b0.1 b1.1 (zetas 1)).1 * 16382
  else if r = 1 then residue (opInv b0.2 b1.2 (zetas 1)).1 * 16382
  else if r = 2 then residue (opInv b0.1 b1.1 (zetas 1 * 16382)).2
  else residue (opInv b0.2 b1.2 (zetas 1 * 16382)).2

theorem lastOut_2 (a0 a1 a2 a3 : Word) : lastOut a0 a1 a2 a3 2 =
    residue (opInv (opInv a0 a1 (zetas 3)).1 (opInv a2 a3 (zetas 2)).1 (zetas 1 * 16382)).2 := rfl

theorem lastOut_3 (a0 a1 a2 a3 : Word) : lastOut a0 a1 a2 a3 3 =
    residue (opInv (opInv a0 a1 (zetas 3)).2 (opInv a2 a3 (zetas 2)).2 (zetas 1 * 16382)).2 := rfl

/-- The product with `ζ`, times `R/256`, is the product with `ζ · R/256`. -/
theorem scale_comm {x y : Word} (hx : x.val < 128 * q) (hy : y.val < 128 * q) :
    residue (opInv x y (zetas 1)).2 * 16382 = residue (opInv x y (zetas 1 * 16382)).2 := by
  rw [(Lazy.opInv_residue _ _ _ hx hy).2, (Lazy.opInv_residue _ _ _ hx hy).2, Fin.mul_assoc, Fin.mul_assoc,
    Fin.mul_comm (16382 : Zq)]

/-- The result: the last two layers, then `R/256`. -/
def lastG (F : VG.Proof.MlDsa.Arith.Lazy.Poly) : Poly := (Lazy.layerInv (Lazy.layerInv F 64) 128).map fun x => residue x * 16382

theorem lastG_get {F : VG.Proof.MlDsa.Arith.Lazy.Poly} (hF : ∀ k < 256, F[k]!.val < 64 * q) {j : Nat} (hj : j < 64) {r : Nat} (hr : r < 4) :
    (lastG F)[j + 64 * r]! = lastOut F[j]! F[j + 64]! F[j + 128]! F[j + 192]! r := by
  obtain g : (lastG F)[j + 64 * r]! = residue (Lazy.layerInv (Lazy.layerInv F 64) 128)[j + 64 * r]! * 16382 := by
    rw [lastG, getElem!_pos (Vector.map _ _) (j + 64 * r) (show j + 64 * r < 256 by omega_using [hj, hr]), Vector.getElem_map,
      getElem!_pos (Lazy.layerInv (Lazy.layerInv F 64) 128) (j + 64 * r) (show j + 64 * r < 256 by omega_using [hj, hr])]
  obtain h64 : ∀ k < 64, ∀ c < 2, (Lazy.layerInv F 64)[k + 128 * c]! = (opInv F[k + 128 * c]! F[k + 128 * c + 64]!
      (zetas (3 - c))).1 ∧ (Lazy.layerInv F 64)[k + 128 * c + 64]! = (opInv F[k + 128 * c]! F[k + 128 * c + 64]!
      (zetas (3 - c))).2 := fun k hk c hc => by
    rw [Lazy.layerInv_get F (by decide) (show k + 128 * c < 256 by omega_using [hk, hc]), ifp (by omega_using [hk]),
      Lazy.layerInv_get F (by decide) (show k + 128 * c + 64 < 256 by omega_using [hk, hc]), ifn (by omega_using [hk]),
      show k + 128 * c + 64 - 64 = k + 128 * c by omega_using [],
      show 256 / 64 - 1 - (k + 128 * c) / (2 * 64) = 3 - c by omega_using [hk],
      show 256 / 64 - 1 - (k + 128 * c + 64) / (2 * 64) = 3 - c by omega_using [hk]]
    exact ⟨rfl, rfl⟩
  obtain h128 : ∀ k < 128, (Lazy.layerInv (Lazy.layerInv F 64) 128)[k]! =
      (opInv (Lazy.layerInv F 64)[k]! (Lazy.layerInv F 64)[k + 128]! (zetas 1)).1 ∧
      (Lazy.layerInv (Lazy.layerInv F 64) 128)[k + 128]! =
      (opInv (Lazy.layerInv F 64)[k]! (Lazy.layerInv F 64)[k + 128]! (zetas 1)).2 := fun k hk => by
    rw [Lazy.layerInv_get (Lazy.layerInv F 64) (len := 128) (by decide) (show k < 256 by omega_using [hk]), ifp (by omega_using [hk]),
      Lazy.layerInv_get (Lazy.layerInv F 64) (len := 128) (by decide) (show k + 128 < 256 by omega_using [hk]), ifn (by omega_using [hk]),
      show k + 128 - 128 = k by omega_using [], show 256 / 128 - 1 - k / (2 * 128) = 1 by omega_using [hk],
      show 256 / 128 - 1 - (k + 128) / (2 * 128) = 1 by omega_using [hk]]
    exact ⟨rfl, rfl⟩
  obtain e0 := h64 j hj 0 (by decide)
  obtain e1 := h64 j hj 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.sub_zero] at e0 e1
  rw [show j + 128 + 64 = j + 192 by omega_using []] at e1
  obtain hx : ∀ k < 256, F[k]!.val < 128 * q := fun k hk => Nat.lt_of_lt_of_le (hF k hk) (by decide)
  obtain hb := fun k (hk : k < 256) => hF k hk
  obtain b0 := Lazy.opInv_bound F[j]! F[j + 64]! (zetas 3) (b := 64) (by decide) (by decide) (hb j (by omega_using [hj]))
    (hb (j + 64) (by omega_using [hj]))
  obtain b1 := Lazy.opInv_bound F[j + 128]! F[j + 192]! (zetas 2) (b := 64) (by decide) (by decide)
    (hb (j + 128) (by omega_using [hj])) (hb (j + 192) (by omega_using [hj]))
  rw [g]
  rcases (by omega_using [hr] : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · rw [Nat.mul_zero, Nat.add_zero, (h128 j (by omega_using [hj])).1, e0.1, e1.1]; rfl
  · rw [show j + 64 * 1 = j + 64 by omega_using [], (h128 (j + 64) (by omega_using [hj])).1, e0.2, e1.2]; rfl
  · rw [show j + 64 * 2 = j + 128 by omega_using [], (h128 j (by omega_using [hj])).2, e0.1, e1.1, lastOut_2]
    exact scale_comm (Nat.lt_of_lt_of_le b0.1 (by decide)) (Nat.lt_of_lt_of_le b1.1 (by decide))
  · rw [show j + 64 * 3 = j + 64 + 128 by omega_using [], (h128 (j + 64) (by omega_using [hj])).2, e0.2, e1.2, lastOut_3]
    exact scale_comm (Nat.lt_of_lt_of_le b0.2 (by decide)) (Nat.lt_of_lt_of_le b1.2 (by decide))

theorem opInv_snd_lt (x y : Word) (z : Zq) : (opInv x y z).2.val < 2 * q := by
  have := product_lt (y + 1072693376 - x) z
  simp only [opInv, Fin.val_ofNat]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) this

/-- After `i` iterations of `ylast`'s loop: the coefficients `j + 64 r` with
`j < 8 i` are the result's. -/
def LastI (fP : Addr) (F : VG.Proof.MlDsa.Arith.Lazy.Poly) (i : Nat) (m : VG.Mem) : Prop :=
  ∀ k < 256, (coeffAt m fP k).toNat = if k % 64 < 8 * i then ((lastG F)[k]!).val else F[k]!.val

/-- The lanes of the coefficients `8 i + 64 r` not yet computed. -/
theorem lastIn {fP : Addr} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} {i : Nat} (hi : i < 8) {m : VG.Mem}
    (hS : LastI fP F i m) {r : Nat} (hr : r < 4) {l : Nat} (hl : l < 2) :
    Lazy.DLanes (m.readW (coeffAddr fP (8 * i + 64 * r) + BitVec.ofNat 64 (16 * l)) 128)
      (fun e => F[8 * i + 4 * l + e + 64 * r]!) := fun e he => by
  rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, hS _ (by omega_using [hi, hr, hl, he]), ifn (by omega_using [hi, hl, he]),
    show 8 * i + 64 * r + 4 * l + e = 8 * i + 4 * l + e + 64 * r by omega_using []]

/-- Coefficient `k` after the stores of `ylast` at `j + 64 r`. -/
theorem coeffAt_write4 (m : VG.Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 64) (x0 x1 x2 x3 : BitVec 256) {k : Nat}
    (hk : k < 256) :
    coeffAt ((((m.writeW (coeffAddr p j) x0).writeW (coeffAddr p (j + 64)) x1).writeW
      (coeffAddr p (j + 128)) x2).writeW (coeffAddr p (j + 192)) x3) p k =
      if j ≤ k % 64 ∧ k % 64 < j + 8 then ([x0, x1, x2, x3][k / 64]!).extractLsb' (32 * (k % 64 - j)) 32
      else coeffAt m p k := by
  rw [coeffAt_write256 _ _ (by omega_using [hj]) _ hk, coeffAt_write256 _ _ (by omega_using [hj]) _ hk,
    coeffAt_write256 _ _ (by omega_using [hj]) _ hk, coeffAt_write256 _ _ (by omega_using [hj]) _ hk]
  by_cases h3 : j + 192 ≤ k ∧ k < j + 192 + 8
  · rw [ifp h3, ifp (by omega_using [hj, h3]), show k / 64 = 3 by omega_using [hk, h3], show k % 64 - j = k - (j + 192) by omega_using [hj, h3]]; rfl
  rw [ifn h3]
  by_cases h2 : j + 128 ≤ k ∧ k < j + 128 + 8
  · rw [ifp h2, ifp (by omega_using [hj, h2]), show k / 64 = 2 by omega_using [hj, h2], show k % 64 - j = k - (j + 128) by omega_using [hj, h2]]; rfl
  rw [ifn h2]
  by_cases h1 : j + 64 ≤ k ∧ k < j + 64 + 8
  · rw [ifp h1, ifp (by omega_using [hj, h1]), show k / 64 = 1 by omega_using [hj, h1], show k % 64 - j = k - (j + 64) by omega_using [hj, h1]]; rfl
  rw [ifn h1]
  by_cases h0 : j ≤ k ∧ k < j + 8
  · rw [ifp h0, ifp (by omega_using [hj, h0]), show k / 64 = 0 by omega_using [hj, h0], show k % 64 - j = k - j by omega_using [hj, h0]]; rfl
  rw [ifn h0, ifn (by omega_using [hk, h3, h2, h1, h0])]

/-- The constants of `lastCore` in a lane. -/
theorem lastK_lane {s : State} (hk : LastK s) {l : Nat} (hl : l < 2) :
    ZLanes ((s.proj l).xmm .xmm7) (fun _ => zetas 3) ∧ ZOdd ((s.proj l).xmm .xmm7) ((s.proj l).xmm .xmm7) ∧
    ZLanes ((s.proj l).xmm .xmm8) (fun _ => zetas 2) ∧ ZOdd ((s.proj l).xmm .xmm8) ((s.proj l).xmm .xmm8) ∧
    ZLanes ((s.proj l).xmm .xmm9) (fun _ => zetas 1 * 16382) ∧
      ZOdd ((s.proj l).xmm .xmm9) ((s.proj l).xmm .xmm9) ∧
    ZLanes ((s.proj l).xmm .xmm10) (fun _ => 16382) ∧ ZOdd ((s.proj l).xmm .xmm10) ((s.proj l).xmm .xmm10) := by
  simp only [State.proj_xmm, (hk l hl).1, (hk l hl).2.1, (hk l hl).2.2.1, (hk l hl).2.2.2]
  exact ⟨k7.1, k7.2, k8.1, k8.2, k9.1, k9.2, k10.1, k10.2⟩

/-- The results of `lastCore` in a lane, from its inputs. -/
theorem lastOut_lanes {s t : State} (hp : LastPost s t) {a0 a1 a2 a3 : Nat → Word}
    (h0 : Lazy.DLanes (s.xmm .xmm0) a0) (h1 : Lazy.DLanes (s.xmm .xmm1) a1) (h5 : Lazy.DLanes (s.xmm .xmm5) a2)
    (h6 : Lazy.DLanes (s.xmm .xmm6) a3)
    (hk : ZLanes (s.xmm .xmm7) (fun _ => zetas 3) ∧ ZOdd (s.xmm .xmm7) (s.xmm .xmm7) ∧
      ZLanes (s.xmm .xmm8) (fun _ => zetas 2) ∧ ZOdd (s.xmm .xmm8) (s.xmm .xmm8) ∧
      ZLanes (s.xmm .xmm9) (fun _ => zetas 1 * 16382) ∧ ZOdd (s.xmm .xmm9) (s.xmm .xmm9) ∧
      ZLanes (s.xmm .xmm10) (fun _ => 16382) ∧ ZOdd (s.xmm .xmm10) (s.xmm .xmm10)) {e : Nat} (he : e < 4) :
    (dword (t.xmm .xmm0) e).toNat = (lastOut (a0 e) (a1 e) (a2 e) (a3 e) 0).val ∧
    (dword (t.xmm .xmm3) e).toNat = (lastOut (a0 e) (a1 e) (a2 e) (a3 e) 1).val ∧
    (dword (t.xmm .xmm6) e).toNat = (lastOut (a0 e) (a1 e) (a2 e) (a3 e) 2).val ∧
    (dword (t.xmm .xmm5) e).toNat = (lastOut (a0 e) (a1 e) (a2 e) (a3 e) 3).val := by
  obtain ⟨z7, o7, z8, o8, z9, o9, z10, o10⟩ := hk
  obtain s0 := bsum_lanes h0 h1 (zetas 3)
  obtain s2 := bsum_lanes h5 h6 (zetas 2)
  obtain d1 := bdif_lanes h0 h1 z7 o7
  obtain d3 := bdif_lanes h5 h6 z8 o8
  rw [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
  exact ⟨scale_dw (bsum_lanes s0 s2 (zetas 1)) z10 o10 he, scale_dw (bsum_lanes d1 d3 (zetas 1)) z10 o10 he,
    csub_dw (bdif_lanes s0 s2 z9 o9) he (opInv_snd_lt _ _ _), csub_dw (bdif_lanes d1 d3 z9 o9) he (opInv_snd_lt _ _ _)⟩

theorem last_step {fP : Addr} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} (hF : ∀ k < 256, F[k]!.val < 64 * q) {i : Nat}
    (hi : i < 8) {s : State} (hc : Lazy.YConstsW Lazy.bInvC s) (hk : LastK s)
    (hdx : s.gpr .rdx = coeffAddr fP (8 * i)) (hS : LastI fP F i s.mem) (hw : pR fP ∈ s.wr) :
    WP isa (.block (lastLoads ++ toY lastCore ++ lastStores ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s
      fun s' => LastI fP F (i + 1) s'.mem ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
        Frame [pR fP] s.mem s'.mem ∧ Lazy.YConstsW Lazy.bInvC s' ∧ LastK s' ∧ Keep [.rdx, .rcx] s s' ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mxcsr = s.mxcsr := by
  obtain j0 : ∀ r < 4, 8 * i + 64 * r + 8 ≤ 256 := fun r hr => by omega_using [hi, hr]
  obtain ad : ∀ r < 4, s.gpr .rdx + BitVec.ofNat 64 (256 * r) = coeffAddr fP (8 * i + 64 * r) := fun r _ => by
    rw [hdx, show 256 * r = 4 * (64 * r) by omega_using [], coeffAddr_add]
  obtain r0 : ∀ r < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (256 * r)) 32 := fun r hr => by
    rw [ad r hr]; exact f_in32 (List.mem_append_right _ hw) (j0 r hr)
  rw [show lastLoads ++ toY lastCore ++ lastStores ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
    [.vmovdquLoad .l256 .xmm0 (at_ .rdx (256 * 0))] ++ ([.vmovdquLoad .l256 .xmm1 (at_ .rdx (256 * 1))] ++
      ([.vmovdquLoad .l256 .xmm5 (at_ .rdx (256 * 2))] ++ ([.vmovdquLoad .l256 .xmm6 (at_ .rdx (256 * 3))] ++
      (toY lastCore ++ (lastStores ++ ([.alu .sub .rcx (.imm 1)] : List Instr)))))) by
    simp [lastLoads, List.append_assoc], WP.block_append_iff]
  refine WP.mono (yld_ok (r0 0 (by decide))) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r0 1 (by decide))) fun s2 ⟨L2, o2⟩ => ?_
  obtain o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o12.rd, o12.wr, o12.gpr]; exact r0 2 (by decide))) fun s3 ⟨L3, o3⟩ => ?_
  obtain o13 := o12.trans o3
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o13.rd, o13.wr, o13.gpr]; exact r0 3 (by decide))) fun s4 ⟨L4, o4⟩ => ?_
  obtain o14 := o13.trans o4
  rw [WP.block_append_iff]
  obtain hin : ∀ r < 4, ∀ l < 2, Lazy.DLanes (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (256 * r) +
      BitVec.ofNat 64 (16 * l)) 128) (fun e => F[8 * i + 4 * l + e + 64 * r]!) := fun r hr l hl => by
    rw [ad r hr]; exact lastIn hi hS hr hl
  refine WP.mono (ylanes lane_lastCore (P := fun l t => LastPost (s4.proj l) t)
    fun l hl => lastCore_ok (Lazy.yonly_yconsts o14 hc (by decide) (by decide) (by decide) l hl)) fun s5 ⟨B5, o5⟩ => ?_
  obtain o15 := o14.trans o5
  obtain hv : ∀ l < 2, ∀ e < 4,
      (dword (s5.lane .xmm0 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 0).val ∧
      (dword (s5.lane .xmm3 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 1).val ∧
      (dword (s5.lane .xmm6 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 2).val ∧
      (dword (s5.lane .xmm5 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 3).val := by
    intro l hl e he
    obtain hk4 : LastK s4 := fun l hl => by
      rw [o14.lane .xmm7 (by decide) l hl, o14.lane .xmm8 (by decide) l hl, o14.lane .xmm9 (by decide) l hl,
        o14.lane .xmm10 (by decide) l hl]
      exact hk l hl
    obtain h0 := hin 0 (by decide) l hl
    obtain h1 := hin 1 (by decide) l hl
    obtain h2 := hin 2 (by decide) l hl
    obtain h3 := hin 3 (by decide) l hl
    rw [← State.proj_xmm, ← State.proj_xmm, ← State.proj_xmm, ← State.proj_xmm]
    refine lastOut_lanes (a0 := fun e => F[8 * i + 4 * l + e]!) (a1 := fun e => F[8 * i + 4 * l + e + 64]!)
      (a2 := fun e => F[8 * i + 4 * l + e + 128]!) (a3 := fun e => F[8 * i + 4 * l + e + 192]!)
      (B5 l hl) ?_ ?_ ?_ ?_ (lastK_lane hk4 hl) he
    · rw [State.proj_xmm, o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl,
        L1 l hl]
      simp only [Nat.mul_zero, Nat.add_zero] at h0 ⊢; exact h0
    · rw [State.proj_xmm, o4.lane _ (by decide) l hl, o3.lane _ (by decide) l hl, L2 l hl, o1.gpr, o1.mem]
      simp only [Nat.mul_one] at h1 ⊢; exact h1
    · rw [State.proj_xmm, o4.lane _ (by decide) l hl, L3 l hl, o12.gpr, o12.mem]
      simp only [Nat.reduceMul] at h2 ⊢; exact h2
    · rw [State.proj_xmm, L4 l hl, o13.gpr, o13.mem]
      simp only [Nat.reduceMul] at h3 ⊢; exact h3
  obtain hk5 : LastK s5 := fun l hl => by
    rw [o15.lane .xmm7 (by decide) l hl, o15.lane .xmm8 (by decide) l hl, o15.lane .xmm9 (by decide) l hl,
      o15.lane .xmm10 (by decide) l hl]
    exact hk l hl
  obtain hreg : ∀ R : XReg, ∀ r : Nat, (∀ l < 2, ∀ e < 4, (dword (s5.lane R l) e).toNat =
      (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]! F[8 * i + 4 * l + e + 128]!
        F[8 * i + 4 * l + e + 192]! r).val) → ∀ j, 8 * i ≤ j → j < 8 * i + 8 →
      ((s5.ymm R).extractLsb' (32 * (j - 8 * i)) 32).toNat = (lastOut F[j]! F[j + 64]! F[j + 128]! F[j + 192]! r).val := by
    intro R r h j h1 h2
    rw [State.ymm, extract_ymm _ _ (by omega_using [h2])]
    split
    · have := h 0 (by decide) (j - 8 * i) (by omega_arith)
      rw [show 8 * i + 4 * 0 + (j - 8 * i) = j by omega_using [h1]] at this; exact this
    · have := h 1 (by decide) (j - 8 * i - 4) (by omega_using [h2])
      rw [show 8 * i + 4 * 1 + (j - 8 * i - 4) = j by omega_arith] at this; exact this
  obtain g5 : s5.gpr .rdx = coeffAddr fP (8 * i) := by rw [o15.gpr, hdx]
  obtain a1 : coeffAddr fP (8 * i) + BitVec.ofNat 64 256 = coeffAddr fP (8 * i + 64) := by
    rw [show (BitVec.ofNat 64 256) = BitVec.ofNat 64 (4 * 64) from rfl, coeffAddr_add]
  obtain a2 : coeffAddr fP (8 * i) + BitVec.ofNat 64 512 = coeffAddr fP (8 * i + 128) := by
    rw [show (BitVec.ofNat 64 512) = BitVec.ofNat 64 (4 * 128) from rfl, coeffAddr_add]
  obtain a3 : coeffAddr fP (8 * i) + BitVec.ofNat 64 768 = coeffAddr fP (8 * i + 192) := by
    rw [show (BitVec.ofNat 64 768) = BitVec.ofNat 64 (4 * 192) from rfl, coeffAddr_add]
  obtain w0 : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [o15.wr, g5]; exact f_in32 hw (by omega_using [hi])
  obtain w1 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 256) 32 := by
    rw [o15.wr, g5, a1]; exact f_in32 hw (by omega_using [hi])
  obtain w2 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 512) 32 := by
    rw [o15.wr, g5, a2]; exact f_in32 hw (by omega_using [hi])
  obtain w3 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 768) 32 := by
    rw [o15.wr, g5, a3]; exact f_in32 hw (by omega_using [hi])
  simp only [lastStores]
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, VG.Proof.MlKem.X86_64.State.setMem_setMem, w0, w1, w2, w3, sx32]
  rw [g5, a1, a2, a3, o15.mem]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun l hl => ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [coeffAt_write4 _ _ (show 8 * i + 8 ≤ 64 by omega_using [hi]) _ _ _ _ hk]
    split
    · rename_i hin'
      rw [ifp (show k % 64 < 8 * (i + 1) by omega_using [hin'])]
      obtain e := lastG_get hF (show k % 64 < 64 by omega_using []) (show k / 64 < 4 by omega_using [hk])
      rw [show k % 64 + 64 * (k / 64) = k by omega_using []] at e
      rw [e]
      rcases (by omega_using [hk] : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3) with h | h | h | h <;> rw [h]
      · exact hreg .xmm0 0 (fun l hl e he => (hv l hl e he).1) _ hin'.1 hin'.2
      · exact hreg .xmm3 1 (fun l hl e he => (hv l hl e he).2.1) _ hin'.1 hin'.2
      · exact hreg .xmm6 2 (fun l hl e he => (hv l hl e he).2.2.1) _ hin'.1 hin'.2
      · exact hreg .xmm5 3 (fun l hl e he => (hv l hl e he).2.2.2) _ hin'.1 hin'.2
    · rw [hS k hk]
      by_cases h' : k % 64 < 8 * i
      · rw [ifp h', ifp (by omega_using [h'])]
      · rw [ifn h', ifn (by omega_arith)]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show 8 * i + 8 = 8 * (i + 1) by omega_using []]
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP (by omega_using [hi]))).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP (by omega_using [hi]))).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP (by omega_using [hi]))).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP (by omega_using [hi]))
  · exact Lazy.ylanes_gpr (s := s5) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o15 hc
      (by decide) (by decide)
  · simp only [lane_setReg, lane_setFlags, State.setMem_lane]; exact hk5 l hl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [o15.gpr]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o15.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o15.wr]
  · rw [o15.gpr]
  · rw [o15.gpr]
  · exact o15.mxcsr

/-- The last two layers and the multiplication by `R/256`, from coefficients
below `64 q`. -/
theorem ylast_ok {fP : Addr} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} (hF : ∀ k < 256, F[k]!.val < 64 * q) (s : State)
    (hc : Lazy.YConstsW Lazy.bInvC s) (hdi : s.gpr .rdi = fP) (hS : Lazy.PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) :
    WP isa ylast s fun s' => PolyIs s'.mem fP (lastG F) ∧ Keep [.rax, .rcx, .rdx, .r8] s s' ∧
      Frame [pR fP] s.mem s'.mem := by
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (Q := fun (w : State) => w.gpr .rdx = fP ∧ GOnly [.rdx] s w ∧ w.ymmHi = s.ymmHi)
    (by vrund [hdi]; exact ⟨by gonlyd, rfl⟩) fun w ⟨hdx, og, hy⟩ => ?_
  refine WP.mono (yconst_ok .xmm7 _ w) fun w1 ⟨l1, k1, m1, _, o1⟩ => ?_
  refine WP.mono (yconst_ok .xmm8 _ w1) fun w2 ⟨l2, k2, m2, _, o2⟩ => ?_
  refine WP.mono (yconst_ok .xmm9 _ w2) fun w3 ⟨l3, k3, m3, _, o3⟩ => ?_
  refine WP.mono (yconst_ok .xmm10 _ w3) fun w4 ⟨l4, k4, m4, _, o4⟩ => ?_
  obtain cw : Lazy.YConstsW Lazy.bInvC w :=
    Lazy.ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  obtain lw : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → ∀ l < 2, w4.lane r l = w.lane r l :=
    fun r h7 h8 h9 h10 l hl => by rw [o4 r h10 l hl, o3 r h9 l hl, o2 r h8 l hl, o1 r h7 l hl]
  obtain cw4 : Lazy.YConstsW Lazy.bInvC w4 := fun l hl =>
    ⟨⟨by rw [State.proj_xmm, lw _ (by decide) (by decide) (by decide) (by decide) l hl]; exact (cw l hl).q,
      by rw [State.proj_xmm, lw _ (by decide) (by decide) (by decide) (by decide) l hl]; exact (cw l hl).qinv⟩,
      by rw [State.proj_xmm, lw _ (by decide) (by decide) (by decide) (by decide) l hl]; exact (cw l hl).q2⟩
  obtain hk4 : LastK w4 := fun l hl =>
    ⟨by rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl, o2 _ (by decide) l hl, l1 l hl]; rfl,
      by rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl, l2 l hl]; rfl, by rw [o4 _ (by decide) l hl, l3 l hl]; rfl,
      l4 l hl⟩
  obtain dx4 : w4.gpr .rdx = fP := by
    rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), hdx]
  obtain mw4 : w4.mem = s.mem := by rw [m4, m3, m2, m1, og.mem]
  obtain kw4 : Keep [.rdx, .rax] s w4 := ((((og.keep.trans k1).trans k2).trans k3).trans k4).mono (by simp)
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide)
    (fun i u => LastI fP F i u.mem ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧ Lazy.YConstsW Lazy.bInvC u ∧ LastK u ∧
      Keep [.rcx, .rdx] w4 u ∧ Frame [pR fP] w4.mem u.mem)
    (fun u o hu _ => ⟨fun k hk => by
        rw [o.mem, mw4, ifn (by omega_using [])]; exact Lazy.polyIs_toNat hS (by rw [n_eq]; exact hk),
      by rw [o.keep.gpr (by decide), dx4, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      Lazy.ylanes_gpr (s := w4) (o.lane hu) (YOnly.refl [] w4) cw4 (by decide) (by decide),
      fun l hl => by simp only [o.lane hu]; exact hk4 l hl,
      o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _⟩)
    (fun i hi u ⟨hS', hdx', hc', hk', hk'', hf'⟩ => WP.mono (last_step hF hi hc' hk' hdx' hS'
        (by rw [hk''.2.2, kw4.2.2]; exact hwf))
      fun u' ⟨hS'', hdx'', hf'', hc'', hk2, hk3, hcx, hzf, _⟩ =>
        ⟨⟨hS'', hdx'', hc'', hk2, (hk''.trans hk3).mono (by simp), hf'.trans hf''⟩, hcx, hzf⟩))
    fun u ⟨hS', _, _, _, hk', hf'⟩ => ?_
  refine ⟨polyIs_of_toNat fun k hk => ?_, (kw4.trans hk').mono (by simp), by rw [← mw4]; exact hf'⟩
  rw [n_eq] at hk
  rw [hS' k hk, ifp (by omega_using [])]

/-! ## The transform -/

theorem inv_eq (f : Poly) : Proof.MlDsa.montgomeryNttInv f =
    (nttInvLens.foldl nttInvLayer f).map (· * 16382) := by
  rw [Proof.MlDsa.montgomeryNttInv, nttInv_eq_layers, Vector.map_map]
  apply congrArg (fun g : Spec.MlDsa.Zq → Spec.MlDsa.Zq => (nttInvLens.foldl nttInvLayer f).map g)
  funext x
  change (x * 8347681) * Proof.MlDsa.montgomeryR = x * 16382
  rw [Fin.mul_assoc]
  obtain hc : (8347681 : Spec.MlDsa.Zq) * Proof.MlDsa.montgomeryR = 16382 := by decide +kernel
  rw [hc]

theorem map_residue {b : Nat} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} {g : Poly} (h : Lazy.Rel b F g) :
    F.map (fun x => residue x * 16382) = g.map (· * 16382) := by
  apply Vector.ext; intro i hi
  rw [Vector.getElem_map, Vector.getElem_map, ← getElem!_pos F i hi, ← getElem!_pos g i hi, (h i hi).2]

/-- The code, on any reduced `F` at `fP`, with the scratch at `sP`. -/
theorem body_ok {fP sP : Addr} {F : Poly} {s : State} (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hF : PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) (hd : (pR fP).Disjoint (pR sP)) :
    WP isa montInvBody s fun s' => PolyIs s'.mem fP (Proof.MlDsa.montgomeryNttInv F) ∧
      Frame [pR fP, pR sP] s.mem s'.mem := by
  have hd' : (pR sP).Disjoint (pR fP) := hd.symm
  refine WP.seq (WP.mono (ypro_ok hsi hw) fun s2 ⟨hT, hc0, hf2, k2, _⟩ => ?_)
  obtain hF2 : PolyIs s2.mem fP F :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF
  obtain hdi : s2.gpr .rdi = fP := by rw [k2.gpr (by decide), hdi]
  obtain hsi : s2.gpr .rsi = sP := by rw [k2.gpr (by decide), hsi]
  obtain hwf : pR fP ∈ s2.wr := by rw [k2.2.2]; exact hwf
  obtain hw : pR sP ∈ s2.wr := by rw [k2.2.2]; exact hw
  refine WP.seq (WP.mono (yconst_ok .xmm11 1072693376 s2) fun w ⟨lc, kc, mc, _, oc⟩ => ?_)
  obtain hc : Lazy.YConstsW Lazy.bInvC w := fun l hl => ⟨⟨by
      rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hc0 l hl).q,
    by rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hc0 l hl).qinv⟩,
    by rw [State.proj_xmm, lc l hl]; rfl⟩
  obtain hi : Lazy.LII fP sP s2 (Lazy.lift F) w :=
    ⟨by rw [mc]; exact Lazy.lift_mem hF2, by rw [mc]; exact hT, hc, kc.mono (by simp), by rw [mc]; exact Frame.refl _ _⟩
  refine Lazy.LII.seq hdi hsi hwf hw hd' (Lazy.yinvLay1_ok hd') ?_ hi
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd' (Lazy.yinvLay2_ok hd') ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd' (Lazy.yinvLay4_ok hd') ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd' (Lazy.yinvLay_ok hd' 8 31 (by decide) (by decide)) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd' (Lazy.yinvLay_ok hd' 16 15 (by decide) (by decide)) ?_ hI
  refine fun _ hI => Lazy.LII.seq hdi hsi hwf hw hd' (Lazy.yinvLay_ok hd' 32 7 (by decide) (by decide)) ?_ hI
  intro u hu
  refine WP.seq (WP.mono (ylast_ok (fun k hk => (Lazy.transformInv6_rel F k hk).1) u
    hu.c (by rw [hu.keep.gpr (by decide), hdi]) hu.P (by rw [hu.keep.2.2]; exact hwf)) fun v ⟨hv, _, hb⟩ => ?_)
  refine WP.mono (Q := fun (u' : State) => u'.mem = v.mem) (by simp only [yepi]; vrund; rfl) fun u' hm => ?_
  rw [hm, inv_eq, ← map_residue (Lazy.transformInv_rel F)]
  refine ⟨hv, (frame_fs hf2 ?_).trans (frame_fs (hu.frame.trans hb) ?_)⟩ <;>
    intro r hr <;> simp only [List.mem_singleton] at hr <;> subst hr
  exacts [.inr fun _ h => h, .inl fun _ h => h]

theorem correct (s : State) (hs : (inPlaceK Proof.MlDsa.montgomeryNttInv).pre s) :
    ∃ t s', Exec isa montNttInvAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK Proof.MlDsa.montgomeryNttInv).post s s' := by
  obtain hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  obtain hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) fun s1 k1 f1 => ?_
  obtain hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
    polyIs_frame f1 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd.sub_right (mx_sub' _))
      ⟨hs.2.2.2.2.2, rfl⟩
  refine WP.mono (body_ok (k1.gpr (by decide)) (k1.gpr (by decide)) hF1 (by rw [k1.2.2]; exact hwf)
    (by rw [k1.2.2]; exact hw) hd) fun s' ⟨hP, hf⟩ => ⟨hP, ?_⟩
  exact (frame_fs f1 fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact .inr (mx_sub' _)).trans hf

theorem ct : ConstantTime isa (inPlaceK Proof.MlDsa.montgomeryNttInv).pre
    (inPlaceK Proof.MlDsa.montgomeryNttInv).pub montNttInvAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem verified : Verified X86_64.target montNttInvAvx2 (Proof.MlDsa.montgomeryNttInvContract X86_64.abi) :=
  Verified.of_correct correct ct (by
    mldsa_implies [Proof.MlDsa.montgomeryNttInvContract, Proof.MlDsa.inPlaceContract, Proof.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith.MontgomeryInv

end

end

/-!
# ML-DSA on x86-64: `vg_mldsa_dot_inverse{c}_avx2`

Each of the 32 iterations of the loop sums, in each lane, the `c` products
of eight coefficients of `a[j]` and `b[j]` in quadwords (`dotMac`, `macs_ok`)
and reduces them (`dotRed`, `dot_lane`), storing the sums times `2⁻³²`
(`step`); then the inverse NTT with Montgomery scaling (`body_ok`) cancels
the factor (`Representation.inverse_encode`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.YDot

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Arith
open VG.Proof.MlKem.X86_64 (writesIn writesOnly_of Keep XOnly YOnly ylanes yld_ok yconst_ok WP.keep writesOnly
  gprPreserved_of ifp ifn GOnly wp_rcxLoopY add_ofNat_zero lane_setReg lane_setFlags sx32 State.setMem_ymm
  mxR)
open VG.Impl.MlKem.X86_64 (xb xmov toY yconst rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq)
open VG.Proof.MlDsa (coeffAt polyAt Reduced PolyIs montgomeryRInv)

theorem lane_dotZero : laneSseBlock (toY dotZero) = some dotZero := by decide +kernel
theorem lane_dotMac : laneSseBlock (toY dotMac) = some dotMac := by decide +kernel
theorem lane_dotRed : laneSseBlock (toY dotRed) = some dotRed := by decide +kernel

/-- The sums of the first `n` products of the eight coefficients `Av j t`,
`Bv j t` (`t < 8`) in the quadwords of the lanes of `ymm5` (even `t`) and
`ymm6` (odd). -/
def AccOk (s : State) (Av Bv : Nat → Nat → Nat) (n : Nat) : Prop :=
  ∀ l < 2, ∀ k < 2,
    (qword (s.lane .xmm5 l) k).toNat = dsum (fun j => Av j (4 * l + 2 * k)) (fun j => Bv j (4 * l + 2 * k)) n ∧
    (qword (s.lane .xmm6 l) k).toNat = dsum (fun j => Av j (4 * l + 2 * k + 1)) (fun j => Bv j (4 * l + 2 * k + 1)) n

/-- The first `n` products. -/
theorem macs_ok {c : Nat} (hc : c ≤ 7) {Av Bv : Nat → Nat → Nat} (hA : ∀ j < c, ∀ t < 8, Av j t < 3 * q)
    (hB : ∀ j < c, ∀ t < 8, Bv j t < 3 * q) {s : State}
    (hr : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .r10 + BitVec.ofNat 64 (1024 * j)) 32)
    (hr' : ∀ j < c, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (1024 * j)) 32)
    (ha : ∀ j < c, ∀ l < 2, ∀ e < 4, (dword (s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * j) +
      BitVec.ofNat 64 (16 * l)) 128) e).toNat = Av j (4 * l + e))
    (hb : ∀ j < c, ∀ l < 2, ∀ e < 4, (dword (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * j) +
      BitVec.ofNat 64 (16 * l)) 128) e).toNat = Bv j (4 * l + e))
    (h0 : AccOk s Av Bv 0) :
    ∀ n ≤ c, WP isa (.block ((List.range n).flatMap fun j => dotLoads j ++ toY dotMac)) s fun s' =>
      AccOk s' Av Bv n ∧ YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm5, .xmm6] s s'
  | 0, _ => by
    simp only [List.range_zero, List.flatMap_nil]
    vrund
    exact ⟨h0, YOnly.refl _ s⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (macs_ok hc hA hB hr hr' ha hb h0 n (by omega_using [hn])) fun s1 ⟨A1, o1⟩ => ?_
    rw [dotLoads, show ∀ (x y : Instr) (l : List Instr), [x, y] ++ l = [x] ++ ([y] ++ l) from fun _ _ _ => rfl,
      WP.block_append_iff]
    refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact hr n (by omega_using [hn]))) fun s2 ⟨L2, o2⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (yld_ok (by rw [o2.rd, o2.wr, o2.gpr, o1.rd, o1.wr, o1.gpr]; exact hr' n (by omega_using [hn])))
      fun s3 ⟨L3, o3⟩ => ?_
    refine WP.mono (ylanes lane_dotMac (P := fun l t =>
        t.xmm .xmm5 = macE ((s3.proj l).xmm .xmm5) ((s3.proj l).xmm .xmm0) ((s3.proj l).xmm .xmm1) ∧
        t.xmm .xmm6 = macO ((s3.proj l).xmm .xmm6) ((s3.proj l).xmm .xmm0) ((s3.proj l).xmm .xmm1))
      fun l _ => WP.mono (dotMac_ok _) fun t ⟨h5, h6, ht⟩ => ⟨⟨h5, h6⟩, ht⟩) fun s4 ⟨M4, o4⟩ => ⟨?_, ?_⟩
    · intro l hl k hk
      obtain x0 : (s3.proj l).xmm .xmm0 = s.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (1024 * n) +
          BitVec.ofNat 64 (16 * l)) 128 := by
        rw [State.proj_xmm, o3.lane _ (by decide) l hl, L2 l hl, o1.mem, o1.gpr]
      obtain x1 : (s3.proj l).xmm .xmm1 = s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (1024 * n) +
          BitVec.ofNat 64 (16 * l)) 128 := by
        rw [State.proj_xmm, L3 l hl, o2.mem, o2.gpr, o1.mem, o1.gpr]
      obtain x5 : (s3.proj l).xmm .xmm5 = s1.lane .xmm5 l := by
        rw [State.proj_xmm, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl]
      obtain x6 : (s3.proj l).xmm .xmm6 = s1.lane .xmm6 l := by
        rw [State.proj_xmm, o3.lane _ (by decide) l hl, o2.lane _ (by decide) l hl]
      obtain e5 : s4.lane .xmm5 l = _ := (M4 l hl).1
      obtain e6 : s4.lane .xmm6 l = _ := (M4 l hl).2
      obtain a0 := ha n (by omega_using [hn]) l hl (2 * k) (by omega_using [hk])
      obtain a1 := ha n (by omega_using [hn]) l hl (2 * k + 1) (by omega_using [hk])
      obtain b0 := hb n (by omega_using [hn]) l hl (2 * k) (by omega_using [hk])
      obtain b1 := hb n (by omega_using [hn]) l hl (2 * k + 1) (by omega_using [hk])
      rw [← x0] at a0 a1
      rw [← x1] at b0 b1
      rw [show 4 * l + (2 * k + 1) = 4 * l + 2 * k + 1 by omega_using []] at a1 b1
      refine ⟨?_, ?_⟩
      · rw [e5, qword_macE hk (by rw [x5, (A1 l hl k hk).1, a0, b0]; exact prod_bound hc hA hB (by omega_using [hn]) (by omega_using [hl, hk])), x5,
          (A1 l hl k hk).1, a0, b0]
        rfl
      · rw [e6, qword_macO hk (by rw [x6, (A1 l hl k hk).2, a1, b1]; exact prod_bound hc hA hB (by omega_using [hn]) (by omega_using [hl, hk])), x6,
          (A1 l hl k hk).2, a1, b1]
        rfl
    · exact (((o1.trans o2).trans o3).trans o4).mono (by simp)

/-- Coefficient `k` of the result: the sum of the products, times `2⁻³²`. -/
def dotOut (m : VG.Mem) (a b : Addr) (c k : Nat) : Zq :=
  Fin.ofNat q (dsum (fun j => famV m a j k) (fun j => famV m b j k) c) * montgomeryRInv

/-- After `i` iterations of the loop, from `s₀`. -/
structure DI (o a b : Addr) (c : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r8 : s.gpr .r8 = coeffAddr o (8 * i)
  r10 : s.gpr .r10 = coeffAddr a (8 * i)
  rdx : s.gpr .rdx = coeffAddr b (8 * i)
  keep : Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s
  yc : YConsts s
  frame : Frame [pR o] s₀.mem s.mem
  done : ∀ k < 8 * i, (coeffAt s.mem o k).toNat = (dotOut s₀.mem a b c k).val

section
variable {o a b : Addr} {c : Nat} {s₀ : State} (hc7 : c ≤ 7) (hwo : pR o ∈ s₀.wr)
  (hra : ∀ j < c, ∀ k, k + 8 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (a + BitVec.ofNat 64 (1024 * j)) k) 32)
  (hrb : ∀ j < c, ∀ k, k + 8 ≤ 256 → InRegions (s₀.rd ++ s₀.wr) (coeffAddr (b + BitVec.ofNat 64 (1024 * j)) k) 32)
  (hda : ∀ j < c, (pR (a + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hdb : ∀ j < c, (pR (b + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o))
  (hA : ∀ j < c, ∀ k < 256, famV s₀.mem a j k < 3 * q) (hB : ∀ j < c, ∀ k < 256, famV s₀.mem b j k < 3 * q)
include hc7 hwo hra hrb hda hdb hA hB

theorem step {i : Nat} (hi : i < 32) {s : State} (hI : DI o a b c s₀ i s) :
    WP isa (.block (dotBody c ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      DI o a b c s₀ (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  obtain j0 : 8 * i + 8 ≤ 256 := by omega_using [hi]
  -- the values of the coefficients loaded
  obtain hv : ∀ (p : Addr), (∀ j < c, (pR (p + BitVec.ofNat 64 (1024 * j))).Disjoint (pR o)) → ∀ j < c, ∀ l < 2,
      ∀ e < 4, (dword (s.mem.readW (coeffAddr p (8 * i) + BitVec.ofNat 64 (1024 * j) + BitVec.ofNat 64 (16 * l)) 128)
        e).toNat = famV s₀.mem p j (8 * i + (4 * l + e)) := fun p hd j hj l hl e he => by
    rw [addr_fam, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, famV, ← Nat.add_assoc,
      coeffAt_frame hI.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd j hj) (by rw [n_eq]; omega_using [hi, hl, he])]
  simp only [dotBody, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_dotZero (P := fun l t => t.xmm .xmm5 = 0 ∧ t.xmm .xmm6 = 0)
    fun l _ => WP.mono (dotZero_ok _) fun t ⟨h5, h6, ht⟩ => ⟨⟨h5, h6⟩, ht⟩) fun s1 ⟨Z1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (macs_ok hc7 (Av := fun j t => famV s₀.mem a j (8 * i + t)) (Bv := fun j t => famV s₀.mem b j (8 * i + t))
    (fun j hj t ht => hA j hj _ (by omega_using [hi, ht])) (fun j hj t ht => hB j hj _ (by omega_using [hi, ht]))
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.r10, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hra j hj _ j0)
    (fun j hj => by
      rw [o1.rd, o1.wr, o1.gpr, hI.rdx, hI.keep.2.1, hI.keep.2.2, addr_fam]; exact hrb j hj _ j0)
    (fun j hj l hl e he => by rw [o1.mem, o1.gpr, hI.r10]; exact hv a hda j hj l hl e he)
    (fun j hj l hl e he => by rw [o1.mem, o1.gpr, hI.rdx]; exact hv b hdb j hj l hl e he)
    (fun l hl k hk => by
      obtain e5 : s1.lane .xmm5 l = _ := (Z1 l hl).1
      obtain e6 : s1.lane .xmm6 l = _ := (Z1 l hl).2
      rw [e5, e6]; exact ⟨by simp [qword, dsum], by simp [qword, dsum]⟩) c (Nat.le_refl _)) fun s2 ⟨A2, o2⟩ => ?_
  obtain o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (ylanes lane_dotRed (P := fun l t => t.xmm .xmm5 = csubV (redV ((s2.proj l).xmm .xmm5) ((s2.proj l).xmm .xmm6)))
    fun l hl => WP.mono (dotRed_ok (yonly_yconsts o12 hI.yc (by decide) (by decide) l hl)) fun t ⟨h5, ht⟩ => ⟨h5, ht⟩)
    fun s3 ⟨R3, o3⟩ => ?_
  obtain o13 := o12.trans o3
  -- the eight results
  obtain hres : ∀ l < 2, ∀ e < 4, (dword (s3.lane .xmm5 l) e).toNat = (dotOut s₀.mem a b c (8 * i + 4 * l + e)).val := by
    intro l hl e he
    obtain e3 : s3.lane .xmm5 l = _ := R3 l hl
    rw [e3, dot_lane (e := (s2.proj l).xmm .xmm5) (o := (s2.proj l).xmm .xmm6)
      (A := fun j t => famV s₀.mem a j (8 * i + (4 * l + t)))
      (B := fun j t => famV s₀.mem b j (8 * i + (4 * l + t))) hc7
      (fun j hj t ht => hA j hj _ (by omega_using [hi, hl, ht])) (fun j hj t ht => hB j hj _ (by omega_using [hi, hl, ht]))
      (fun k hk => by rw [State.proj_xmm]; exact (A2 l hl k hk).1)
      (fun k hk => by rw [State.proj_xmm, (A2 l hl k hk).2]; simp only [Nat.add_assoc]) he]
    simp only [dotOut, Nat.add_assoc]
  obtain g3 : s3.gpr .r8 = coeffAddr o (8 * i) := by rw [o13.gpr, hI.r8]
  obtain w0 : InRegions s3.wr (s3.gpr .r8) 32 := by
    rw [o13.wr, g3, hI.keep.2.2]; exact f_in32 hwo j0
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, w0, sx32]
  rw [g3, o13.mem]
  obtain p8 : coeffAddr o (8 * i) + 32 = coeffAddr o (8 * (i + 1)) := by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, show 8 * i + 8 = 8 * (i + 1) by omega_using []]
  obtain pa : ∀ p : Addr, coeffAddr p (8 * i) + 32 = coeffAddr p (8 * (i + 1)) := fun p => by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add, show 8 * i + 8 = 8 * (i + 1) by omega_using []]
  refine ⟨⟨?_, ?_, ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, fun k hk => ?_⟩, by rw [o13.gpr], by rw [o13.gpr]⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    exact p8
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.r10]; exact pa a
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq, State.setMem_gpr]
    rw [o13.gpr, hI.rdx]; exact pa b
  · have hr0 := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, ite_false,
      State.setMem_gpr]
    rw [o13.gpr, hI.keep.1 r hr0]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd]; rw [o13.rd, hI.keep.2.1]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr]; rw [o13.wr, hI.keep.2.2]
  · exact ylanes_gpr (s := s3) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o13 hI.yc
      (by decide) (by decide)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [coeffAt_write256 _ _ j0 _ (by omega_using [hi, hk])]
    split
    · rw [State.ymm, extract_ymm _ _ (by omega_using [hk])]
      split
      · have := hres 0 (by decide) (k - 8 * i) (by omega_arith)
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega_arith] at this; exact this
      · have := hres 1 (by decide) (k - 8 * i - 4) (by omega_using [hk])
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega_arith] at this; exact this
    · exact hI.done k (by omega_arith)

/-- The loop, from the constants and the pointers, in `s₀`. -/
theorem pass_ok (h8 : s₀.gpr .r8 = o) (h10 : s₀.gpr .r10 = a) (hdx : s₀.gpr .rdx = b) (hc : YConsts s₀) :
    WP isa (rcxLoop 32 (dotBody c)) s₀ fun s' => PolyIs s'.mem o (Vector.ofFn fun k => dotOut s₀.mem a b c k.val) ∧
      Keep [.r8, .r10, .rdx, .rcx, .rax] s₀ s' ∧ Frame [pR o] s₀.mem s'.mem := by
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) (DI o a b c s₀)
    (fun u og hy _ => ⟨by rw [og.keep.gpr (by decide), h8, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), h10, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      by rw [og.keep.gpr (by decide), hdx, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      og.keep.mono (by simp), ylanes_gpr (s := s₀) (og.lane hy) (YOnly.refl [] s₀) hc (by decide) (by decide),
      by rw [og.mem]; exact Frame.refl _ _, fun k hk => absurd hk (by omega_using [])⟩)
    (fun i hi u hI => step hc7 hwo hra hrb hda hdb hA hB hi hI)) fun u hI => ⟨⟨fun k hk => ?_, ?_⟩, hI.keep, hI.frame⟩
  · rw [n_eq] at hk
    rw [hI.done k (by omega_using [hk])]; exact (dotOut s₀.mem a b c k).isLt
  · apply Vector.ext; intro k hk
    rw [polyAt, Vector.getElem_ofFn, Vector.getElem_ofFn]
    apply Fin.ext
    rw [Fin.val_ofNat, hI.done k (by rw [n_eq] at hk; omega_using [hk]), Nat.mod_eq_of_lt (dotOut s₀.mem a b c k).isLt]

end

/-! ## The function -/

/-- The result: the sums times `2⁻³²`, which the inverse transform's factor cancels. -/
theorem dotOut_eq {m m' : VG.Mem} {a b : Addr} {c : Nat}
    (ha : ∀ j < c, ∀ k < 256, coeffAt m' (a + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (a + BitVec.ofNat 64 (1024 * j)) k)
    (hb : ∀ j < c, ∀ k < 256, coeffAt m' (b + BitVec.ofNat 64 (1024 * j)) k = coeffAt m (b + BitVec.ofNat 64 (1024 * j)) k) :
    (Vector.ofFn fun k => dotOut m' a b c k.val) = Representation.encode true (Proof.MlDsa.dotNTT
      (fun j => polyAt m (a + BitVec.ofNat 64 (1024 * j))) (fun j => polyAt m (b + BitVec.ofNat 64 (1024 * j))) c) := by
  apply Vector.ext; intro k hk
  rw [Vector.getElem_ofFn, ← getElem!_pos (Representation.encode true _) k hk]
  change _ = (Montgomery.scale montgomeryRInv _)[k]!
  rw [Montgomery.scale_get, dotNTT_get (A := fun j => famV m' a j k) (B := fun j => famV m' b j k) hk
    (fun j hj => by rw [polyAt_get _ _ hk, famV, ha j hj k hk]) (fun j hj => by rw [polyAt_get _ _ hk, famV, hb j hj k hk])]
  rfl

theorem correct {c : Nat} (hc7 : c ≤ 7)
    (hk : Code.allInstrs (writesIn [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .rsi]) (dotInvAvx2 c) = true)
    (hctl : ctlOk (dotInvAvx2 c) = true) (s : State) (hs : (dotK c).pre s) :
    ∃ t s', Exec isa (dotInvAvx2 c) s t s' ∧ abiPreserved s s' ∧ (dotK c).post s s' := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, r1, r2, pa, pb⟩ := hs
  obtain hwo : pR (s.gpr .rdi) ∈ s.wr := by rw [hwr]; simp
  obtain hws : pR (s.gpr .rcx) ∈ s.wr := by rw [hwr]; simp
  obtain hW : WP isa (dotInvAvx2 c) s fun s' => PolyIs s'.mem (s.gpr .rdi) (Spec.MlDsa.nttInv (Proof.MlDsa.dotNTT
      (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
      (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) ∧
      Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s'.mem := by
    refine WP.seq (WP.mono (Q := fun (w : State) => w.gpr .r10 = s.gpr .rsi ∧ w.gpr .rsi = s.gpr .rcx ∧
        GOnly [.r10, .rsi] s w ∧ w.ymmHi = s.ymmHi)
      (by vrund; exact ⟨by gonlyd, rfl⟩) fun w ⟨h10, hsi, og, hy⟩ => ?_)
    refine WP.mono (noMx_ok (sP := s.gpr .rcx) (Q := fun u => PolyIs u.mem (s.gpr .rdi) (Spec.MlDsa.nttInv
        (Proof.MlDsa.dotNTT (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
          (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) ∧
        Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem u.mem) (fun s1 k1 f1 => ?_))
      fun s' ⟨s2, ⟨hP, hf⟩, hf', _⟩ => ⟨?_, ?_⟩
    rotate_left
    · exact polyIs_frame hf' (fun r hr => by
        rw [List.mem_singleton.mp hr]; exact d3.sub_right (mx_sub' _)) hP
    · exact hf.trans (frame_fs hf' fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr (mx_sub' _))
    obtain hdi1 : s1.gpr .rdi = s.gpr .rdi := by rw [k1.gpr (by decide), og.keep.gpr (by decide)]
    obtain hsi1 : s1.gpr .rsi = s.gpr .rcx := by rw [k1.gpr (by decide), hsi]
    obtain h101 : s1.gpr .r10 = s.gpr .rsi := by rw [k1.gpr (by decide), h10]
    obtain hdx1 : s1.gpr .rdx = s.gpr .rdx := by rw [k1.gpr (by decide), og.keep.gpr (by decide)]
    obtain wr1 : s1.wr = s.wr := by rw [k1.2.2, og.keep.2.2]
    obtain rd1 : s1.rd = s.rd := by rw [k1.2.1, og.keep.2.1]
    obtain hm : ∀ p : Addr, (pR (s.gpr .rcx)).Disjoint (famR p c) → ∀ j < c, ∀ k < 256,
        coeffAt s1.mem (p + BitVec.ofNat 64 (1024 * j)) k = coeffAt s.mem (p + BitVec.ofNat 64 (1024 * j)) k :=
      fun p hd j hj k hk => by
        rw [coeffAt_frame f1 (fun r hr => by
          rw [List.mem_singleton.mp hr]; exact (hd.sub_right (fam_sub p hj)).symm.sub_right (mx_sub' _))
          (by rw [n_eq]; exact hk), og.mem]
    refine WP.seq ?_
    rw [WP.block_append_iff]
    refine WP.mono (yconsts_ok s1) fun s2 ⟨c2, k2, m2, _, _⟩ => ?_
    obtain hdi2 : s2.gpr .rdi = s.gpr .rdi := by rw [k2.gpr (by decide), hdi1]
    refine WP.mono (Q := fun (s3 : State) => s3.gpr .r8 = s.gpr .rdi ∧ GOnly [.r8] s2 s3 ∧ s3.ymmHi = s2.ymmHi)
      (by vrund [hdi2]; exact ⟨by gonlyd, rfl⟩) fun s3 ⟨h8, og3, hy3⟩ => ?_
    obtain c3 : YConsts s3 := ylanes_gpr (s := s2) (GOnly.lane og3 hy3) (YOnly.refl [] s2) c2 (by decide) (by decide)
    obtain k13 : Keep [.rax, .r8] s1 s3 := (k2.trans og3.keep).mono (by simp)
    obtain m3 : s3.mem = s1.mem := by rw [og3.mem, m2]
    obtain hr : ∀ p : Addr, famR p c ∈ s.rd → ∀ j < c, ∀ k, k + 8 ≤ 256 →
        InRegions (s3.rd ++ s3.wr) (coeffAddr (p + BitVec.ofNat 64 (1024 * j)) k) 32 := fun p hp j hj k hk =>
      ⟨famR p c, by rw [k13.2.1, rd1]; exact List.mem_append_left _ hp, by
        rw [coeffAddr, VG.Offset.add_add]; exact VG.Offset.contains_base _ (by omega_using [hj, hk]) (by omega_using [hc7, hj, hk])⟩
    refine WP.seq (WP.mono (pass_ok (s₀ := s3) hc7 (by rw [k13.2.2, wr1]; exact hwo)
      (hr _ (by rw [hrd]; simp)) (hr _ (by rw [hrd]; simp))
      (fun j hj => (d1.sub_right (fam_sub _ hj)).symm) (fun j hj => (d2.sub_right (fam_sub _ hj)).symm)
      (fun j hj k hk => by rw [famV, m3, hm _ d4 j hj k hk]; exact pa j hj k (by rw [n_eq]; exact hk))
      (fun j hj k hk => by rw [famV, m3, hm _ d5 j hj k hk]; exact pb j hj k (by rw [n_eq]; exact hk))
      h8 (by rw [k13.gpr (by decide), h101]) (by rw [k13.gpr (by decide), hdx1]) c3) fun u ⟨hP, ku, fu⟩ => ?_)
    refine WP.mono (MontgomeryInv.body_ok (by rw [ku.gpr (by decide), k13.gpr (by decide), hdi1])
      (by rw [ku.gpr (by decide), k13.gpr (by decide), hsi1]) hP
      (by rw [ku.2.2, k13.2.2, wr1]; exact hwo) (by rw [ku.2.2, k13.2.2, wr1]; exact hws) d3) fun v ⟨hv, fv⟩ => ⟨?_, ?_⟩
    · have e : Proof.MlDsa.montgomeryNttInv (Representation.encode true (Proof.MlDsa.dotNTT
          (fun j => polyAt s.mem (s.gpr .rsi + BitVec.ofNat 64 (1024 * j)))
          (fun j => polyAt s.mem (s.gpr .rdx + BitVec.ofNat 64 (1024 * j))) c)) = _ :=
        Representation.inverse_encode true _
      rw [dotOut_eq (m := s.mem) (fun j hj k hk => by rw [m3, hm _ d4 j hj k hk])
        (fun j hj k hk => by rw [m3, hm _ d5 j hj k hk]), e] at hv
      exact hv
    · have f1' : Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s.mem s1.mem := by
        rw [← og.mem]; exact frame_fs f1 fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact .inr (mx_sub' _)
      obtain fu' : Frame [pR (s.gpr .rdi), pR (s.gpr .rcx)] s1.mem u.mem := by
        rw [← m3]; exact frame_fs fu fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact .inl fun _ h => h
      exact (f1'.trans fu').trans fv
  obtain ⟨tr, s', he, ⟨hP, hf⟩, hk2⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11, .rsi] hW (writesOnly_of hk)
  exact ⟨tr, s', he, abiPreserved_of_ctl hctl he (gprPreserved_of hk2 (by decide) hf (by simpa using ⟨r1, r2⟩)), hP⟩

theorem ct4 : ConstantTime isa (dotK 4).pre (dotK 4).pub (dotInvAvx2 4) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 4) (by taint_decide)

theorem ct5 : ConstantTime isa (dotK 5).pre (dotK 5).pub (dotInvAvx2 5) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 5) (by taint_decide)

theorem ct7 : ConstantTime isa (dotK 7).pre (dotK 7).pub (dotInvAvx2 7) :=
  VG.Taint.constantTime (A := taint) dotτ (dot_agree 7) (by taint_decide)

theorem verified4 : Verified X86_64.target (dotInvAvx2 4) (Proof.MlDsa.dotInverseContract 4 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel)) ct4
    (by dot_implies dotSat 4)

theorem verified5 : Verified X86_64.target (dotInvAvx2 5) (Proof.MlDsa.dotInverseContract 5 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel)) ct5
    (by dot_implies dotSat 5)

theorem verified7 : Verified X86_64.target (dotInvAvx2 7) (Proof.MlDsa.dotInverseContract 7 X86_64.abi) :=
  Verified.of_correct (correct (by decide) (by decide +kernel) (by decide +kernel)) ct7
    (by dot_implies dotSat 7)

end VG.Proof.MlDsa.X86_64.Arith.YDot
