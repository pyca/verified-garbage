module

public import VerifiedGarbage.Proof.MlKem.X86_64.YMulc
public import VerifiedGarbage.Proof.MlKem.X86_64.LazyBfly
public import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ML-KEM on x86-64: the lazy layers of `NTT` and `NTT⁻¹` with AVX2

`nttLazy` and `nttInvLazy` take `S` from the coefficients of `F` to those of
`NTT(F)` and `NTT⁻¹(F)`. Between them, `S` holds words that only represent
the coefficients (`LIW`: `PolyRep`): each layer is a layer of `fwdW` or
`invW` on the words (`ylay_ok`, …, with `vbflyL_spec`, `vibflyL_spec`),
which represents the specification's layer within a bound one `q` larger
(`NTT`, up to `8q`) or twice as large (`NTT⁻¹`, `8q` after three layers, when
`yred` brings the words back to `(-q, q)`) (`layF_rep`). The last pass
(`yredC`, `yscale`) leaves the coefficients' values.
-/

@[expose] public section

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem

/-! ## The code in each lane -/

theorem lane_vbflyL : laneSseBlock (toY vbflyL) = some vbflyL := by decide +kernel
theorem lane_vibflyL : laneSseBlock (toY vibflyL) = some vibflyL := by decide +kernel
theorem lane_vbflyL4 : laneSseBlock (toY (gath4 ++ vbflyL ++ scat4)) = some (gath4 ++ vbflyL ++ scat4) := by
  decide +kernel
theorem lane_vibflyL4 : laneSseBlock (toY (gath4 ++ vibflyL ++ scat4)) = some (gath4 ++ vibflyL ++ scat4) := by
  decide +kernel
theorem lane_vbflyL2 : laneSseBlock (toY (gath2 ++ vbflyL ++ scat2)) = some (gath2 ++ vbflyL ++ scat2) := by
  decide +kernel
theorem lane_vibflyL2 : laneSseBlock (toY (gath2 ++ vibflyL ++ scat2)) = some (gath2 ++ vibflyL ++ scat2) := by
  decide +kernel
theorem lane_vmont3 : laneSseBlock (toY (vmont .xmm3 .xmm13 .xmm2)) = some (vmont .xmm3 .xmm13 .xmm2) := by
  decide +kernel

theorem word_cR {i : Nat} (hi : i < 8) : word (ofDwords 0x08ED08ED 0x08ED08ED 0x08ED08ED 0x08ED08ED) i = rW := by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem word_512 {i : Nat} (hi : i < 8) :
    word (ofDwords 0x02000200 0x02000200 0x02000200 0x02000200) i = zw 3303 := by
  rcases (by bdd_omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## Words representing a polynomial in `S` -/

/-- The zetas of `NTT⁻¹` in the order its layers read them. -/
abbrev zInv (k : Nat) : Zq := zeta (127 - k)

theorem zmTabInv_eq (k : Nat) : zmTabInv k = (zInv k).val * 65536 % 3329 := zmTab_eq _

/-- `S` holds words representing `F` within `k q`, with the table of `z`. -/
def LIW (sP : Addr) (s₀ : State) (z : Nat → Zq) (k : Nat) (F : Poly) (s : State) : Prop :=
  ∃ W : WPoly, S16R (· = ·) s.mem (spW sP) W ∧ PolyRep k W F ∧ TZ s.mem sP z ∧ BInvY sP s₀ s

/-- What a lazy layer or reduction `l` does to `S`. -/
def LayW (sP : Addr) (z : Nat → Zq) (l : Prog isa) (k k' : Nat) (F F' : Poly) : Prop :=
  ∀ s (W : WPoly), YConsts s → s.gpr .rsi = sP → S16R (· = ·) s.mem (spW sP) W → PolyRep k W F →
    TZ s.mem sP z → pR sP ∈ s.wr →
    WP isa l s fun s' => ∃ W' : WPoly, S16R (· = ·) s'.mem (spW sP) W' ∧ PolyRep k' W' F' ∧ BInvY sP s s'

/-- A lazy layer, then `c`. -/
theorem LIW.seq {sP : Addr} {s₀ : State} {z : Nat → Zq} (hsi : s₀.gpr .rsi = sP) (hw : pR sP ∈ s₀.wr)
    {l c : Prog isa} {k k' : Nat} {F F' : Poly} {Q : State → Prop} (hl : LayW sP z l k k' F F')
    (hc : ∀ s, LIW sP s₀ z k' F' s → WP isa c s Q) {s : State} (hI : LIW sP s₀ z k F s) :
    WP isa (.seq l c) s Q := by
  obtain ⟨W, hS, hR, hT, hb⟩ := hI
  exact WP.seq (WP.mono (hl s W hb.consts (by rw [hb.keep.gpr (by decide), hsi]) hS hR hT
    (by rw [hb.keep.2.2]; exact hw)) fun s' ⟨W', hS', hR', hb'⟩ => hc s' ⟨W', hS', hR', hT.frame hb'.frame, hb.trans hb'⟩)

/-! ## The lazy layers of `NTT` -/

theorem fwd_hop {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) :
    ∀ (a b : BitVec 16) (x y ζ : Zq), Rep k a x → Rep k b y →
      Rep (k + 1) (fwdW a b ζ).1 ((fun x y z => (x + z * y, x - z * y)) x y ζ).1 ∧
        Rep (k + 1) (fwdW a b ζ).2 ((fun x y z => (x + z * y, x - z * y)) x y ζ).2 :=
  fun _ _ _ _ ζ ha hb => fwdW_rep hk ζ ha hb.2.2

theorem inv_hop {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) :
    ∀ (a b : BitVec 16) (x y ζ : Zq), Rep k a x → Rep k b y →
      Rep (2 * k) (invW a b ζ).1 ((fun x y z => (x + y, z * (y - x))) x y ζ).1 ∧
        Rep (2 * k) (invW a b ζ).2 ((fun x y z => (x + y, z * (y - x))) x y ζ).2 :=
  fun _ _ _ _ ζ ha hb => ⟨(invW_rep hk ζ ha hb).1, (invW_rep hk ζ ha hb).2.mono hk1⟩

theorem fwdLayL_ok (len t : Nat) (hlen : len ∈ [16, 32, 64, 128]) (ht : 128 / len = t) {sP : Addr} {k : Nat}
    (hk : (k + 1) * 3329 ≤ 32768) {F : Poly} :
    LayW sP zeta (ylay vbflyL len t) k (k + 1) F (nttLayer F len) := by
  subst ht
  intro s W hc hsi hS hR hT hw
  have h8 : 128 / len ≤ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl | rfl <;> decide
  refine WP.mono (ylay_ok vbflyL_spec lane_vbflyL (wBlk_ok fwdW) hlen (fun c => 128 / len + c)
    (fun c _ => ⟨by omega, rfl⟩) hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttLayer_eq]
  exact layF_rep (wBlk_ok fwdW) nttBlk_ok (fwd_hop hk)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen ⊢; omega) _ hR

theorem fwdLay8L_ok {sP : Addr} {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) {F : Poly} :
    LayW sP zeta (ylay8 vbflyL 16) k (k + 1) F (nttLayer F 8) := by
  intro s W hc hsi hS hR hT hw
  refine WP.mono (ylay8_ok vbflyL_spec lane_vbflyL (wBlk_ok fwdW) (fun c => 16 + c) (fun c hc' => ⟨by omega, rfl⟩)
    hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttLayer_eq]
  exact layF_rep (wBlk_ok fwdW) nttBlk_ok (fwd_hop hk) (by decide) _ hR

theorem fwdLay4L_ok {sP : Addr} {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) {F : Poly} :
    LayW sP zeta (ylay4 vbflyL 32) k (k + 1) F (nttLayer F 4) := by
  intro s W hc hsi hS hR hT hw
  refine WP.mono (ylay4_ok vbflyL_spec (wBlk_ok fwdW) lane_vbflyL4 (fun c => 32 + c) (fun c hc' => ⟨by omega, rfl⟩)
    hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttLayer_eq]
  exact layF_rep (wBlk_ok fwdW) nttBlk_ok (fwd_hop hk) (by decide) _ hR

theorem fwdLay2L_ok {sP : Addr} {k : Nat} (hk : (k + 1) * 3329 ≤ 32768) {F : Poly} :
    LayW sP zeta (ylay2 vbflyL 64) k (k + 1) F (nttLayer F 2) := by
  intro s W hc hsi hS hR hT hw
  refine WP.mono (ylay2_ok vbflyL_spec (wBlk_ok fwdW) lane_vbflyL2 (fun c => 64 + c) (fun c hc' => ⟨by omega, rfl⟩)
    hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttLayer_eq]
  exact layF_rep (wBlk_ok fwdW) nttBlk_ok (fwd_hop hk) (by decide) _ hR

/-! ## The lazy layers of `NTT⁻¹` -/

theorem invLayL_ok (len t : Nat) (hlen : len ∈ [16, 32, 64, 128])
    (ht : ∀ c < 128 / len, t + c < 128 ∧ 127 - (t + c) = 256 / len - 1 - c) {sP : Addr} {k : Nat}
    (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) {F : Poly} :
    LayW sP zInv (ylay vibflyL len t) k (2 * k) F (nttInvLayer F len) := by
  intro s W hc hsi hS hR hT hw
  refine WP.mono (ylay_ok vibflyL_spec lane_vibflyL (wBlk_ok invW) hlen (fun c => 256 / len - 1 - c) (z := zInv)
    (fun c hc' => ⟨(ht c hc').1, congrArg zeta (ht c hc').2⟩) hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttInvLayer_eq]
  exact layF_rep (wBlk_ok invW) nttInvBlk_ok (inv_hop hk hk1)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen ⊢; omega) _ hR

theorem invLay8L_ok {sP : Addr} {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) {F : Poly} :
    LayW sP zInv (ylay8 vibflyL 96) k (2 * k) F (nttInvLayer F 8) := by
  intro s W hc hsi hS hR hT hw
  refine WP.mono (ylay8_ok vibflyL_spec lane_vibflyL (wBlk_ok invW) (fun c => 31 - c) (z := zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttInvLayer_eq]
  exact layF_rep (wBlk_ok invW) nttInvBlk_ok (inv_hop hk hk1) (by decide) _ hR

theorem invLay4L_ok {sP : Addr} {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) {F : Poly} :
    LayW sP zInv (ylay4 vibflyL 64) k (2 * k) F (nttInvLayer F 4) := by
  intro s W hc hsi hS hR hT hw
  refine WP.mono (ylay4_ok vibflyL_spec (wBlk_ok invW) lane_vibflyL4 (fun c => 63 - c) (z := zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttInvLayer_eq]
  exact layF_rep (wBlk_ok invW) nttInvBlk_ok (inv_hop hk hk1) (by decide) _ hR

theorem invLay2L_ok {sP : Addr} {k : Nat} (hk : 2 * k * 3329 ≤ 32768) (hk1 : 1 ≤ 2 * k) {F : Poly} :
    LayW sP zInv (ylay2 vibflyL 0) k (2 * k) F (nttInvLayer F 2) := by
  intro s W hc hsi hS hR hT hw
  refine WP.mono (ylay2_ok vibflyL_spec (wBlk_ok invW) lane_vibflyL2 (fun c => 127 - c) (z := zInv)
    (fun c hc' => ⟨by omega, congrArg zeta (by omega)⟩) hc hsi hS hT hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', ?_, hb⟩
  rw [nttInvLayer_eq]
  exact layF_rep (wBlk_ok invW) nttInvBlk_ok (inv_hop hk hk1) (by decide) _ hR

/-! ## The reductions -/

theorem getElem!_map {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (v : Vector α n) {i : Nat} (hi : i < 256) :
    (v.map f)[i]! = f v[i]! := by
  rw [getElem!_pos _ i (by rw [n_eq]; exact hi), getElem!_pos _ i (by rw [n_eq]; exact hi), Vector.getElem_map]

/-- `yred` brings the words back to `(-q, q)`. -/
theorem yredL_ok {sP : Addr} {z : Nat → Zq} {k : Nat} {F : Poly} : LayW sP z yred k 1 F F := by
  intro s W hc hsi hS hR _ hw
  refine WP.mono (ymulc_ok (fun _ h => word_cR h) lane_vmont3 vmont_map hc hsi hS hw) fun s' ⟨hS', hb⟩ => ⟨_, hS', fun i hi => ?_, hb⟩
  rw [getElem!_map _ _ hi]
  exact red_rep (hR i hi).2.2

/-- `yredC` leaves the coefficients' values. -/
theorem yredC_ok {sP : Addr} {k : Nat} {F : Poly} {W : WPoly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16R (· = ·) s.mem (spW sP) W) (hR : PolyRep k W F) (hw : pR sP ∈ s.wr) :
    WP isa yredC s fun s' => S16 s'.mem (spW sP) F ∧ BInvY sP s s' :=
  WP.mono (ymulc_ok (fun _ h => word_cR h) lane_vmulc vmontc_map hc hsi hS hw) fun _ ⟨hS', hb⟩ => ⟨fun i hi => by
    rw [hS' i hi, getElem!_map _ _ hi]
    exact cadd_rep (red_rep (hR i hi).2.2), hb⟩

/-- `yscale` multiplies the coefficients by `3303` and leaves their values. -/
theorem yscaleL_ok {sP : Addr} {k : Nat} {F : Poly} {W : WPoly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16R (· = ·) s.mem (spW sP) W) (hR : PolyRep k W F) (hw : pR sP ∈ s.wr) :
    WP isa yscale s fun s' => S16 s'.mem (spW sP) (F.map (· * 3303)) ∧ BInvY sP s s' :=
  WP.mono (ymulc_ok (fun _ h => word_512 h) lane_vmulc vmontc_map hc hsi hS hw) fun _ ⟨hS', hb⟩ => ⟨fun i hi => by
    rw [hS' i hi, getElem!_map _ _ hi, getElem!_map _ _ hi, Fin.mul_comm]
    exact cadd_rep (mont_rep 3303 (hR i hi).2.2), hb⟩

/-! ## The layers together -/

/-- The words of `S` represent its coefficients. -/
theorem liw_of {sP : Addr} {z : Nat → Zq} {F : Poly} {s : State} (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP z)
    (hc : YConsts s) : LIW sP s z 1 F s :=
  ⟨Vector.ofFn fun i => wordAt s.mem (spW sP) i, fun i hi => by
    rw [getElem!_pos _ i (by rw [n_eq]; exact hi), Vector.getElem_ofFn],
    fun i hi => by
      rw [getElem!_pos _ i (by rw [n_eq]; exact hi), Vector.getElem_ofFn]
      exact Rep.of_can (hS i hi), hT, ⟨Keep.refl _ _, Frame.refl _ _, hc, rfl⟩⟩

theorem nttLazy_ok {sP : Addr} {F : Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zeta) (hw : pR sP ∈ s.wr) :
    WP isa nttLazy s fun s' => S16 s'.mem (spW sP) (ntt F) ∧ BInvY sP s s' := by
  unfold nttLazy
  refine LIW.seq hsi hw (fwdLayL_ok 128 1 (by decide) (by decide) (k := 1) (by decide)) ?_ (liw_of hS hT hc)
  refine fun _ hI => LIW.seq hsi hw (fwdLayL_ok 64 2 (by decide) (by decide) (k := 2) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (fwdLayL_ok 32 4 (by decide) (by decide) (k := 3) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (fwdLayL_ok 16 8 (by decide) (by decide) (k := 4) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (fwdLay8L_ok (k := 5) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (fwdLay4L_ok (k := 6) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (fwdLay2L_ok (k := 7) (by decide)) ?_ hI
  intro s' ⟨W, hS', hR, _, hb⟩
  refine WP.mono (yredC_ok hb.consts (by rw [hb.keep.gpr (by decide), hsi]) hS' hR (by rw [hb.keep.2.2]; exact hw))
    fun s'' ⟨hS'', hb'⟩ => ⟨?_, hb.trans hb'⟩
  rw [ntt_eq_layers]
  simp only [nttLens, List.foldl_cons, List.foldl_nil]
  exact hS''

theorem nttInvLazy_ok {sP : Addr} {F : Poly} {s : State} (hc : YConsts s) (hsi : s.gpr .rsi = sP)
    (hS : S16 s.mem (spW sP) F) (hT : TZ s.mem sP zInv) (hw : pR sP ∈ s.wr) :
    WP isa nttInvLazy s fun s' => S16 s'.mem (spW sP) (nttInv F) ∧ BInvY sP s s' := by
  unfold nttInvLazy
  refine LIW.seq hsi hw (invLay2L_ok (k := 1) (by decide) (by decide)) ?_ (liw_of hS hT hc)
  refine fun _ hI => LIW.seq hsi hw (invLay4L_ok (k := 2) (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (invLay8L_ok (k := 4) (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (yredL_ok (k := 8)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (invLayL_ok 16 112 (by decide) (by decide) (k := 1) (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (invLayL_ok 32 120 (by decide) (by decide) (k := 2) (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (invLayL_ok 64 124 (by decide) (by decide) (k := 4) (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (yredL_ok (k := 8)) ?_ hI
  refine fun _ hI => LIW.seq hsi hw (invLayL_ok 128 126 (by decide) (by decide) (k := 1) (by decide) (by decide)) ?_ hI
  intro s' ⟨W, hS', hR, _, hb⟩
  refine WP.mono (yscaleL_ok hb.consts (by rw [hb.keep.gpr (by decide), hsi]) hS' hR (by rw [hb.keep.2.2]; exact hw))
    fun s'' ⟨hS'', hb'⟩ => ⟨?_, hb.trans hb'⟩
  rw [nttInv_eq_layers]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
  exact hS''

end VG.Proof.MlKem.X86_64
