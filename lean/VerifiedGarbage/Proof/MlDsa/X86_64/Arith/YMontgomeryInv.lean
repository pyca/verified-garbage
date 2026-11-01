module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YNtt
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Montgomery
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
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
meta import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
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

/-- The first six layers, whose coefficients stay below `64 q`. -/
theorem transformInv6_rel (f : VG.Spec.MlDsa.Poly) :
    Rel 64 (layerInv (layerInv (layerInv (layerInv (layerInv (layerInv (lift f) 1) 2) 4) 8) 16) 32)
      (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer (nttInvLayer f 1) 2) 4) 8) 16) 32) := by
  have h0 := lift_rel f
  have h1 := layerInv_rel (by decide) (by decide : 1 ≤ 128) h0 (by decide : 1 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h2 := layerInv_rel (by decide) (by decide : 2 * 1 ≤ 128) h1 (by decide : 2 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h3 := layerInv_rel (by decide) (by decide : 2 * (2 * 1) ≤ 128) h2 (by decide : 4 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h4 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * 1)) ≤ 128) h3
    (by decide : 8 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h5 := layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * 1))) ≤ 128) h4
    (by decide : 16 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  exact layerInv_rel (by decide) (by decide : 2 * (2 * (2 * (2 * (2 * 1)))) ≤ 128) h5
    (by decide : 32 ∈ [1, 2, 4, 8, 16, 32, 64, 128])

theorem transformInv_rel (f : VG.Spec.MlDsa.Poly) :
    Rel 256 (transformInv (lift f)) (nttInvLens.foldl nttInvLayer f) := by
  have h7 := layerInv_rel (by decide) (by decide : 64 ≤ 128) (transformInv6_rel f)
    (by decide : 64 ∈ [1, 2, 4, 8, 16, 32, 64, 128])
  have h8 := layerInv_rel (by decide) (by decide : 2 * 64 ≤ 128) h7
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

theorem layerInv_get (F : Poly) {len : Nat} (hlen : len ∈ [1, 2, 4, 8, 16, 32, 64, 128]) {i : Nat} (hi : i < 256) :
    (layerInv F len)[i]! = if i % (2 * len) < len then
      (opInv F[i]! F[i + len]! (zetas (256 / len - 1 - i / (2 * len)))).1
      else (opInv F[i - len]! F[i]! (zetas (256 / len - 1 - i / (2 * len)))).2 := by
  have hl : 0 < len ∧ 2 * len * (128 / len) = 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [layerInv, layF_get (block_ok opInv) F hl.1 _ (by omega) hi, VG.Proof.MlKem.X86_64.ifp (by omega)]

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
open VG.Spec.MlDsa (q n Poly Zq zetas ntt nttInv)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs)
open VG.Proof.MlDsa.Arith.Lazy (residue Word opInv product product_lt)

/-- A product of any doubleword by a zeta in Montgomery form, reduced: `ζ · (b mod q)`. -/
theorem mulZL {b z m : BitVec 32} {ζ : Zq} (hz : z.toNat = ζ.val * 2 ^ 32 % q)
    (hm : m.toNat = mont (b.toNat * z.toNat)) : (csubL m).toNat = (ζ * Fin.ofNat q b.toNat).val := by
  have hx : b.toNat * z.toNat < q * 2 ^ 32 := by
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
  vrun [eval_movdqa]
  rw [hc.q, hc.qinv, hc.q2]
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, by xonly⟩

theorem lane_lastCore : laneSseBlock (toY lastCore) = some lastCore := by decide +kernel

theorem bsum_lanes {a b : BitVec 128} {x y : Nat → Word} (ha : Lazy.DLanes a x) (hb : Lazy.DLanes b y) (ζ : Zq) :
    Lazy.DLanes (bsum a b) (fun i => (opInv (x i) (y i) ζ).1) := fun i hi => by
  rw [dword_paddd _ _ hi, BitVec.toNat_add, ha i hi, hb i hi]
  simp only [opInv, Fin.val_add]

theorem bdif_lanes {a b z : BitVec 128} {x y : Nat → Word} {ζ : Zq} (ha : Lazy.DLanes a x)
    (hb : Lazy.DLanes b y) (hz : ZLanes z fun _ => ζ) (ho : ZOdd z z) :
    Lazy.DLanes (bdif a b z) (fun i => (opInv (x i) (y i) ζ).2) := by
  have hw : Lazy.DLanes (XBinOp.eval .paddd (XBinOp.eval .psubd b a)
      (ofDwords Lazy.bInvC Lazy.bInvC Lazy.bInvC Lazy.bInvC)) (fun i => y i + 1072693376 - x i) := by
    intro i hi
    have hb' : (dword (ofDwords Lazy.bInvC Lazy.bInvC Lazy.bInvC Lazy.bInvC) i).toNat = 1072693376 := by
      rcases cases4 hi with rfl | rfl | rfl | rfl <;> rfl
    rw [dword_paddd _ _ hi, BitVec.toNat_add, dword_psubd _ _ hi, BitVec.toNat_sub, ha i hi, hb i hi, hb']
    simp only [Fin.val_sub, Fin.val_add, show (1072693376 : Word).val = 1072693376 from rfl]
    have := (x i).isLt; have := (y i).isLt
    omega
  intro i hi
  rw [dword_montV ho (Lazy.prod_lt hw hz) hi, hw i hi, hz i hi]
  have ht := product_lt (y i + 1072693376 - x i) ζ
  have ht32 : product (y i + 1072693376 - x i) ζ < 4294967296 := Nat.lt_trans ht (by decide)
  simp only [opInv, Fin.val_ofNat, Nat.mod_eq_of_lt ht32]
  rfl

/-- A doubleword times `R/256`, reduced. -/
theorem scale_dw {x k : BitVec 128} {w : Nat → Word} (hx : Lazy.DLanes x w) (hk : ZLanes k fun _ => 16382)
    (ho : ZOdd k k) {e : Nat} (he : e < 4) : (dword (csubV (montV x k k)) e).toNat = (residue (w e) * 16382).val := by
  have hb : ∀ e < 4, (dword x e).toNat * (dword k e).toNat < q * 2 ^ 32 := fun e he => by
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
    fun j hj => by rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp⟩

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
  have g : (lastG F)[j + 64 * r]! = residue (Lazy.layerInv (Lazy.layerInv F 64) 128)[j + 64 * r]! * 16382 := by
    rw [lastG, getElem!_pos (Vector.map _ _) (j + 64 * r) (show j + 64 * r < 256 by omega), Vector.getElem_map,
      getElem!_pos (Lazy.layerInv (Lazy.layerInv F 64) 128) (j + 64 * r) (show j + 64 * r < 256 by omega)]
  have h64 : ∀ k < 64, ∀ c < 2, (Lazy.layerInv F 64)[k + 128 * c]! = (opInv F[k + 128 * c]! F[k + 128 * c + 64]!
      (zetas (3 - c))).1 ∧ (Lazy.layerInv F 64)[k + 128 * c + 64]! = (opInv F[k + 128 * c]! F[k + 128 * c + 64]!
      (zetas (3 - c))).2 := fun k hk c hc => by
    rw [Lazy.layerInv_get F (by decide) (show k + 128 * c < 256 by omega), ifp (by omega),
      Lazy.layerInv_get F (by decide) (show k + 128 * c + 64 < 256 by omega), ifn (by omega),
      show k + 128 * c + 64 - 64 = k + 128 * c by omega,
      show 256 / 64 - 1 - (k + 128 * c) / (2 * 64) = 3 - c by omega,
      show 256 / 64 - 1 - (k + 128 * c + 64) / (2 * 64) = 3 - c by omega]
    exact ⟨rfl, rfl⟩
  have h128 : ∀ k < 128, (Lazy.layerInv (Lazy.layerInv F 64) 128)[k]! =
      (opInv (Lazy.layerInv F 64)[k]! (Lazy.layerInv F 64)[k + 128]! (zetas 1)).1 ∧
      (Lazy.layerInv (Lazy.layerInv F 64) 128)[k + 128]! =
      (opInv (Lazy.layerInv F 64)[k]! (Lazy.layerInv F 64)[k + 128]! (zetas 1)).2 := fun k hk => by
    rw [Lazy.layerInv_get (Lazy.layerInv F 64) (len := 128) (by decide) (show k < 256 by omega), ifp (by omega),
      Lazy.layerInv_get (Lazy.layerInv F 64) (len := 128) (by decide) (show k + 128 < 256 by omega), ifn (by omega),
      show k + 128 - 128 = k by omega, show 256 / 128 - 1 - k / (2 * 128) = 1 by omega,
      show 256 / 128 - 1 - (k + 128) / (2 * 128) = 1 by omega]
    exact ⟨rfl, rfl⟩
  have e0 := h64 j hj 0 (by decide)
  have e1 := h64 j hj 1 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.sub_zero] at e0 e1
  rw [show j + 128 + 64 = j + 192 by omega] at e1
  have hx : ∀ k < 256, F[k]!.val < 128 * q := fun k hk => Nat.lt_of_lt_of_le (hF k hk) (by decide)
  have hb := fun k (hk : k < 256) => hF k hk
  have b0 := Lazy.opInv_bound F[j]! F[j + 64]! (zetas 3) (b := 64) (by decide) (by decide) (hb j (by omega))
    (hb (j + 64) (by omega))
  have b1 := Lazy.opInv_bound F[j + 128]! F[j + 192]! (zetas 2) (b := 64) (by decide) (by decide)
    (hb (j + 128) (by omega)) (hb (j + 192) (by omega))
  rw [g]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl
  · rw [Nat.mul_zero, Nat.add_zero, (h128 j (by omega)).1, e0.1, e1.1]; rfl
  · rw [show j + 64 * 1 = j + 64 by omega, (h128 (j + 64) (by omega)).1, e0.2, e1.2]; rfl
  · rw [show j + 64 * 2 = j + 128 by omega, (h128 j (by omega)).2, e0.1, e1.1, lastOut_2]
    exact scale_comm (Nat.lt_of_lt_of_le b0.1 (by decide)) (Nat.lt_of_lt_of_le b1.1 (by decide))
  · rw [show j + 64 * 3 = j + 64 + 128 by omega, (h128 (j + 64) (by omega)).2, e0.2, e1.2, lastOut_3]
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
  rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, hS _ (by omega), ifn (by omega),
    show 8 * i + 64 * r + 4 * l + e = 8 * i + 4 * l + e + 64 * r by omega]

/-- Coefficient `k` after the stores of `ylast` at `j + 64 r`. -/
theorem coeffAt_write4 (m : VG.Mem) (p : Addr) {j : Nat} (hj : j + 8 ≤ 64) (x0 x1 x2 x3 : BitVec 256) {k : Nat}
    (hk : k < 256) :
    coeffAt ((((m.writeW (coeffAddr p j) x0).writeW (coeffAddr p (j + 64)) x1).writeW
      (coeffAddr p (j + 128)) x2).writeW (coeffAddr p (j + 192)) x3) p k =
      if j ≤ k % 64 ∧ k % 64 < j + 8 then ([x0, x1, x2, x3][k / 64]!).extractLsb' (32 * (k % 64 - j)) 32
      else coeffAt m p k := by
  rw [coeffAt_write256 _ _ (by omega) _ hk, coeffAt_write256 _ _ (by omega) _ hk,
    coeffAt_write256 _ _ (by omega) _ hk, coeffAt_write256 _ _ (by omega) _ hk]
  by_cases h3 : j + 192 ≤ k ∧ k < j + 192 + 8
  · rw [ifp h3, ifp (by omega), show k / 64 = 3 by omega, show k % 64 - j = k - (j + 192) by omega]; rfl
  rw [ifn h3]
  by_cases h2 : j + 128 ≤ k ∧ k < j + 128 + 8
  · rw [ifp h2, ifp (by omega), show k / 64 = 2 by omega, show k % 64 - j = k - (j + 128) by omega]; rfl
  rw [ifn h2]
  by_cases h1 : j + 64 ≤ k ∧ k < j + 64 + 8
  · rw [ifp h1, ifp (by omega), show k / 64 = 1 by omega, show k % 64 - j = k - (j + 64) by omega]; rfl
  rw [ifn h1]
  by_cases h0 : j ≤ k ∧ k < j + 8
  · rw [ifp h0, ifp (by omega), show k / 64 = 0 by omega, show k % 64 - j = k - j by omega]; rfl
  rw [ifn h0, ifn (by omega)]

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
  have s0 := bsum_lanes h0 h1 (zetas 3)
  have s2 := bsum_lanes h5 h6 (zetas 2)
  have d1 := bdif_lanes h0 h1 z7 o7
  have d3 := bdif_lanes h5 h6 z8 o8
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
  have j0 : ∀ r < 4, 8 * i + 64 * r + 8 ≤ 256 := fun r hr => by omega
  have ad : ∀ r < 4, s.gpr .rdx + BitVec.ofNat 64 (256 * r) = coeffAddr fP (8 * i + 64 * r) := fun r _ => by
    rw [hdx, show 256 * r = 4 * (64 * r) by omega, coeffAddr_add]
  have r0 : ∀ r < 4, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (256 * r)) 32 := fun r hr => by
    rw [ad r hr]; exact f_in32 (List.mem_append_right _ hw) (j0 r hr)
  rw [show lastLoads ++ toY lastCore ++ lastStores ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
    [.vmovdquLoad .l256 .xmm0 (at_ .rdx (256 * 0))] ++ ([.vmovdquLoad .l256 .xmm1 (at_ .rdx (256 * 1))] ++
      ([.vmovdquLoad .l256 .xmm5 (at_ .rdx (256 * 2))] ++ ([.vmovdquLoad .l256 .xmm6 (at_ .rdx (256 * 3))] ++
      (toY lastCore ++ (lastStores ++ ([.alu .sub .rcx (.imm 1)] : List Instr)))))) by
    simp [lastLoads, List.append_assoc], WP.block_append_iff]
  refine WP.mono (yld_ok (r0 0 (by decide))) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr]; exact r0 1 (by decide))) fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o12.rd, o12.wr, o12.gpr]; exact r0 2 (by decide))) fun s3 ⟨L3, o3⟩ => ?_
  have o13 := o12.trans o3
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o13.rd, o13.wr, o13.gpr]; exact r0 3 (by decide))) fun s4 ⟨L4, o4⟩ => ?_
  have o14 := o13.trans o4
  rw [WP.block_append_iff]
  have hin : ∀ r < 4, ∀ l < 2, Lazy.DLanes (s.mem.readW (s.gpr .rdx + BitVec.ofNat 64 (256 * r) +
      BitVec.ofNat 64 (16 * l)) 128) (fun e => F[8 * i + 4 * l + e + 64 * r]!) := fun r hr l hl => by
    rw [ad r hr]; exact lastIn hi hS hr hl
  refine WP.mono (ylanes lane_lastCore (P := fun l t => LastPost (s4.proj l) t)
    fun l hl => lastCore_ok (Lazy.yonly_yconsts o14 hc (by decide) (by decide) (by decide) l hl)) fun s5 ⟨B5, o5⟩ => ?_
  have o15 := o14.trans o5
  have hv : ∀ l < 2, ∀ e < 4,
      (dword (s5.lane .xmm0 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 0).val ∧
      (dword (s5.lane .xmm3 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 1).val ∧
      (dword (s5.lane .xmm6 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 2).val ∧
      (dword (s5.lane .xmm5 l) e).toNat = (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]!
        F[8 * i + 4 * l + e + 128]! F[8 * i + 4 * l + e + 192]! 3).val := by
    intro l hl e he
    have hk4 : LastK s4 := fun l hl => by
      rw [o14.lane .xmm7 (by decide) l hl, o14.lane .xmm8 (by decide) l hl, o14.lane .xmm9 (by decide) l hl,
        o14.lane .xmm10 (by decide) l hl]
      exact hk l hl
    have h0 := hin 0 (by decide) l hl
    have h1 := hin 1 (by decide) l hl
    have h2 := hin 2 (by decide) l hl
    have h3 := hin 3 (by decide) l hl
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
  have hk5 : LastK s5 := fun l hl => by
    rw [o15.lane .xmm7 (by decide) l hl, o15.lane .xmm8 (by decide) l hl, o15.lane .xmm9 (by decide) l hl,
      o15.lane .xmm10 (by decide) l hl]
    exact hk l hl
  have hreg : ∀ R : XReg, ∀ r : Nat, (∀ l < 2, ∀ e < 4, (dword (s5.lane R l) e).toNat =
      (lastOut F[8 * i + 4 * l + e]! F[8 * i + 4 * l + e + 64]! F[8 * i + 4 * l + e + 128]!
        F[8 * i + 4 * l + e + 192]! r).val) → ∀ j, 8 * i ≤ j → j < 8 * i + 8 →
      ((s5.ymm R).extractLsb' (32 * (j - 8 * i)) 32).toNat = (lastOut F[j]! F[j + 64]! F[j + 128]! F[j + 192]! r).val := by
    intro R r h j h1 h2
    rw [State.ymm, extract_ymm _ _ (by omega)]
    split
    · have := h 0 (by decide) (j - 8 * i) (by omega)
      rw [show 8 * i + 4 * 0 + (j - 8 * i) = j by omega] at this; exact this
    · have := h 1 (by decide) (j - 8 * i - 4) (by omega)
      rw [show 8 * i + 4 * 1 + (j - 8 * i - 4) = j by omega] at this; exact this
  have g5 : s5.gpr .rdx = coeffAddr fP (8 * i) := by rw [o15.gpr, hdx]
  have a1 : coeffAddr fP (8 * i) + BitVec.ofNat 64 256 = coeffAddr fP (8 * i + 64) := by
    rw [show (BitVec.ofNat 64 256) = BitVec.ofNat 64 (4 * 64) from rfl, coeffAddr_add]
  have a2 : coeffAddr fP (8 * i) + BitVec.ofNat 64 512 = coeffAddr fP (8 * i + 128) := by
    rw [show (BitVec.ofNat 64 512) = BitVec.ofNat 64 (4 * 128) from rfl, coeffAddr_add]
  have a3 : coeffAddr fP (8 * i) + BitVec.ofNat 64 768 = coeffAddr fP (8 * i + 192) := by
    rw [show (BitVec.ofNat 64 768) = BitVec.ofNat 64 (4 * 192) from rfl, coeffAddr_add]
  have w0 : InRegions s5.wr (s5.gpr .rdx) 32 := by rw [o15.wr, g5]; exact f_in32 hw (by omega)
  have w1 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 256) 32 := by
    rw [o15.wr, g5, a1]; exact f_in32 hw (by omega)
  have w2 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 512) 32 := by
    rw [o15.wr, g5, a2]; exact f_in32 hw (by omega)
  have w3 : InRegions s5.wr (s5.gpr .rdx + BitVec.ofNat 64 768) 32 := by
    rw [o15.wr, g5, a3]; exact f_in32 hw (by omega)
  simp only [lastStores]
  vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
    State.setMem_ymm, VG.Proof.MlKem.X86_64.State.setMem_setMem, w0, w1, w2, w3, sx32]
  rw [g5, a1, a2, a3, o15.mem]
  refine ⟨fun k hk => ?_, ?_, ?_, ?_, fun l hl => ?_, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [coeffAt_write4 _ _ (show 8 * i + 8 ≤ 64 by omega) _ _ _ _ hk]
    split
    · rename_i hin'
      rw [ifp (show k % 64 < 8 * (i + 1) by omega)]
      have e := lastG_get hF (show k % 64 < 64 by omega) (show k / 64 < 4 by omega)
      rw [show k % 64 + 64 * (k / 64) = k by omega] at e
      rw [e]
      rcases (by omega : k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 ∨ k / 64 = 3) with h | h | h | h <;> rw [h]
      · exact hreg .xmm0 0 (fun l hl e he => (hv l hl e he).1) _ hin'.1 hin'.2
      · exact hreg .xmm3 1 (fun l hl e he => (hv l hl e he).2.1) _ hin'.1 hin'.2
      · exact hreg .xmm6 2 (fun l hl e he => (hv l hl e he).2.2.1) _ hin'.1 hin'.2
      · exact hreg .xmm5 3 (fun l hl e he => (hv l hl e he).2.2.2) _ hin'.1 hin'.2
    · rw [hS k hk]
      by_cases h' : k % 64 < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · rw [show (32 : BitVec 64) = BitVec.ofNat 64 (4 * 8) from rfl, coeffAddr_add,
      show 8 * i + 8 = 8 * (i + 1) by omega]
  · exact ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP (by omega))).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP (by omega))).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP (by omega))).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP (by omega))
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
  have cw : Lazy.YConstsW Lazy.bInvC w :=
    Lazy.ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  have lw : ∀ r, r ≠ .xmm7 → r ≠ .xmm8 → r ≠ .xmm9 → r ≠ .xmm10 → ∀ l < 2, w4.lane r l = w.lane r l :=
    fun r h7 h8 h9 h10 l hl => by rw [o4 r h10 l hl, o3 r h9 l hl, o2 r h8 l hl, o1 r h7 l hl]
  have cw4 : Lazy.YConstsW Lazy.bInvC w4 := fun l hl =>
    ⟨⟨by rw [State.proj_xmm, lw _ (by decide) (by decide) (by decide) (by decide) l hl]; exact (cw l hl).q,
      by rw [State.proj_xmm, lw _ (by decide) (by decide) (by decide) (by decide) l hl]; exact (cw l hl).qinv⟩,
      by rw [State.proj_xmm, lw _ (by decide) (by decide) (by decide) (by decide) l hl]; exact (cw l hl).q2⟩
  have hk4 : LastK w4 := fun l hl =>
    ⟨by rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl, o2 _ (by decide) l hl, l1 l hl]; rfl,
      by rw [o4 _ (by decide) l hl, o3 _ (by decide) l hl, l2 l hl]; rfl, by rw [o4 _ (by decide) l hl, l3 l hl]; rfl,
      l4 l hl⟩
  have dx4 : w4.gpr .rdx = fP := by
    rw [k4.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), hdx]
  have mw4 : w4.mem = s.mem := by rw [m4, m3, m2, m1, og.mem]
  have kw4 : Keep [.rdx, .rax] s w4 := ((((og.keep.trans k1).trans k2).trans k3).trans k4).mono (by simp)
  refine WP.mono (wp_rcxLoopY (N := 8) (by decide) (by decide)
    (fun i u => LastI fP F i u.mem ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧ Lazy.YConstsW Lazy.bInvC u ∧ LastK u ∧
      Keep [.rcx, .rdx] w4 u ∧ Frame [pR fP] w4.mem u.mem)
    (fun u o hu _ => ⟨fun k hk => by
        rw [o.mem, mw4, ifn (by omega)]; exact Lazy.polyIs_toNat hS (by rw [n_eq]; exact hk),
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
  rw [hS' k hk, ifp (by omega)]

/-! ## The transform -/

theorem inv_eq (f : Poly) : Proof.MlDsa.montgomeryNttInv f =
    (nttInvLens.foldl nttInvLayer f).map (· * 16382) := by
  rw [Proof.MlDsa.montgomeryNttInv, nttInv_eq_layers, Vector.map_map]
  apply congrArg (fun g : Spec.MlDsa.Zq → Spec.MlDsa.Zq => (nttInvLens.foldl nttInvLayer f).map g)
  funext x
  change (x * 8347681) * Proof.MlDsa.montgomeryR = x * 16382
  rw [Fin.mul_assoc]
  have hc : (8347681 : Spec.MlDsa.Zq) * Proof.MlDsa.montgomeryR = 16382 := by decide +kernel
  rw [hc]

theorem map_residue {b : Nat} {F : VG.Proof.MlDsa.Arith.Lazy.Poly} {g : Poly} (h : Lazy.Rel b F g) :
    F.map (fun x => residue x * 16382) = g.map (· * 16382) := by
  apply Vector.ext; intro i hi
  rw [Vector.getElem_map, Vector.getElem_map, ← getElem!_pos F i hi, ← getElem!_pos g i hi, (h i hi).2]

/-- Everything but `withMxcsr`, on any reduced `F` at `fP`, with the scratch at `sP`. -/
theorem body_ok {fP sP : Addr} {F : Poly} {s : State} (hdi : s.gpr .rdi = fP) (hsi : s.gpr .rsi = sP)
    (hF : PolyIs s.mem fP F) (hwf : pR fP ∈ s.wr) (hw : pR sP ∈ s.wr) (hd : (pR fP).Disjoint (pR sP)) :
    WP isa montInvBody s fun s' => PolyIs s'.mem fP (Proof.MlDsa.montgomeryNttInv F) ∧
      Frame [pR fP, pR sP] s.mem s'.mem := by
  have hd' : (pR sP).Disjoint (pR fP) := hd.symm
  refine WP.seq (WP.mono (ypro_ok hsi hw) fun s2 ⟨hT, hc0, hf2, k2, _⟩ => ?_)
  have hF2 : PolyIs s2.mem fP F :=
    polyIs_frame hf2 (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd) hF
  have hdi : s2.gpr .rdi = fP := by rw [k2.gpr (by decide), hdi]
  have hsi : s2.gpr .rsi = sP := by rw [k2.gpr (by decide), hsi]
  have hwf : pR fP ∈ s2.wr := by rw [k2.2.2]; exact hwf
  have hw : pR sP ∈ s2.wr := by rw [k2.2.2]; exact hw
  refine WP.seq (WP.mono (yconst_ok .xmm11 1072693376 s2) fun w ⟨lc, kc, mc, _, oc⟩ => ?_)
  have hc : Lazy.YConstsW Lazy.bInvC w := fun l hl => ⟨⟨by
      rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hc0 l hl).q,
    by rw [State.proj_xmm, oc _ (by decide) l hl]; exact (hc0 l hl).qinv⟩,
    by rw [State.proj_xmm, lc l hl]; rfl⟩
  have hi : Lazy.LII fP sP s2 (Lazy.lift F) w :=
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
  have hw : pR (s.gpr .rsi) ∈ s.wr := by rw [hs.2.1]; simp
  have hwf : pR (s.gpr .rdi) ∈ s.wr := by rw [hs.2.1]; simp
  have hd : (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) := hs.2.2.1
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 => ?_
  have hF1 : PolyIs s1.mem (s.gpr .rdi) (polyAt s.mem (s.gpr .rdi)) :=
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
