module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YBase
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-DSA on x86-64: the zetas of the layers of the NTT and its inverse on AVX2 registers

What the layers on AVX2 registers (`LazyLay.lean`, `YLay21.lean`) take from
here: the prologue of the layers with `len` = 4, 2 and 1 (`ypre21`), and the
zetas in the lanes of `ymm13` (`ZLanes`): those of one block (`yzeta1_ok`)
and those `pshufd` selects (`yzetaS_ok`), from their SSE2 forms (`zsse1_ok`,
`zsseS_ok`), and the odd ones in the even doublewords of `ymm12` (`yF5_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt sel_zero sel_55
  add_ofNat_zero GOnly addR_ok wp_rcxLoopY wp_countdown ybcast_ok yblend_ok yperm_ok perm20 perm31
  wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Poly Zq zetas)
open VG.Proof.MlDsa (coeffAt polyAt PolyIs)


/-! ## Coefficients in both lanes -/

/-- `YConsts` after code that changed the vector registers `rs` only, then
nothing in them. -/
theorem ylanes_gpr {s s' : State} (h : ∀ r l, s'.lane r l = s.lane r l) {rs : List XReg} {s₀ : State}
    (o : YOnly rs s₀ s) (hc : YConsts s₀) (h14 : XReg.xmm14 ∉ rs) (h15 : XReg.xmm15 ∉ rs) : YConsts s' :=
  fun l hl => ⟨by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 l hl).q,
    by rw [State.proj_xmm, h]; exact (yonly_yconsts o hc h14 h15 l hl).qinv⟩

theorem ZLanes.congr {x : BitVec 128} {f g : Nat → Zq} (h : ZLanes x f) (e : ∀ i < 4, f i = g i) : ZLanes x g :=
  fun i hi => by rw [h i hi, e i hi]

/-- The prologue of the layers with `len` = 4, 2 and 1. -/
theorem ypre21 {fP sP : Addr} (k : Nat) (hk : k + 4 ≤ 256) {s : State} (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) :
    WP isa (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ leaR .r8 .rsi (4 * k))) s fun w =>
      w.gpr .rdx = fP ∧ w.gpr .r8 = coeffAddr sP k ∧ GOnly [.rdx, .r8] s w ∧ w.ymmHi = s.ymmHi := by
  simp only [leaR]
  vrund [sx_ofNat (show 4 * k < 2 ^ 31 by omega_arith), hsi, hdi]
  exact ⟨by gonlyd, rfl⟩

/-! ## The zetas -/

theorem zodd_F5 (x : BitVec 128) : ZOdd x (shufDwords x 0xF5) := fun j hj => by
  rw [dword_shufDwords _ _ (by omega_arith)]
  rcases (by omega_arith : j = 0 ∨ j = 1) with rfl | rfl <;> rfl

/-- The zetas `pshufd` with `o` leaves of the four at index `k` of the table. -/
theorem zlanes_tab (o : BitVec 8) {zP : Addr} {k : Nat} (hk : ∀ j < 4, k + sel o j < 256) {m : Mem}
    (ht : Tab zmTab m zP 256) :
    ZLanes (shufDwords (m.readW (coeffAddr zP k) 128) o) (fun i => zetas (k + sel o i)) := fun i hi => by
  have hs := sel_lt o i
  rw [dword_shufDwords_sel _ _ hi, dword_readW _ _ hs, coeffAddr_add]
  exact tab_zeta ht (hk i hi)

theorem zsse1_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm13 .xmm13 0), .xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) 0 ∧
        t'.xmm .xmm12 = shufDwords (shufDwords (t.xmm .xmm13) 0) 0xF5) ∧ XOnly [.xmm13, .xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem yzeta1_ok {zP : Addr} {k : Nat} (hk : k + 4 ≤ 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block yzeta1) s fun s' => (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun _ => zetas k) ∧
      ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta1, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by decide) (P := fun l t => t.xmm .xmm13 = shufDwords (s1.lane .xmm13 l) 0 ∧
      t.xmm .xmm12 = shufDwords (shufDwords (s1.lane .xmm13 l) 0) 0xF5)
    fun l _ => zsse1_ok (s1.proj l)) fun s2 ⟨l2, o2⟩ => ⟨fun l hl => ?_, (o1.trans o2).mono (by simp)⟩
  have e13 : s2.lane .xmm13 l = _ := (l2 l hl).1
  have e12 : s2.lane .xmm12 l = _ := (l2 l hl).2
  rw [e12, e13, b1 l hl, h8, add_ofNat_zero]
  refine ⟨fun i hi => ?_, zodd_F5 _⟩
  rw [zlanes_tab 0 (fun j _ => by rw [sel_zero]; omega_arith) ht i hi]
  dsimp only; rw [sel_zero, Nat.add_zero]

theorem zsseS_ok (o₀ o₁ : BitVec 8) (t : State) :
    WP isa (.block [.xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)]) t fun t' =>
      (t'.xmm .xmm13 = shufDwords (t.xmm .xmm13) o₀ ∧ t'.xmm .xmm2 = shufDwords (t.xmm .xmm13) o₁) ∧
        XOnly [.xmm2, .xmm13] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

theorem zsseF5_ok (t : State) :
    WP isa (.block [.xop (.pshufd .xmm12 .xmm13 0xF5)]) t fun t' =>
      t'.xmm .xmm12 = shufDwords (t.xmm .xmm13) 0xF5 ∧ XOnly [.xmm12] t t' := by
  vrun
  exact ⟨by first | trivial | simp, by xonly⟩

/-- The odd zetas of each lane of `ymm13` in the even doublewords of `ymm12`. -/
theorem yF5_ok (s : State) :
    WP isa (.block (toY [.xop (.pshufd .xmm12 .xmm13 0xF5)])) s fun s' =>
      (∀ l < 2, s'.lane .xmm12 l = shufDwords (s.lane .xmm13 l) 0xF5) ∧ YOnly [.xmm12] s s' :=
  ylanes (by decide) (P := fun l t => t.xmm .xmm12 = shufDwords (s.lane .xmm13 l) 0xF5)
    fun l _ => zsseF5_ok (s.proj l)

theorem yzetaS_ok (o₀ o₁ : BitVec 8) {zP : Addr} {k : Nat} (hk0 : ∀ j < 4, k + sel o₀ j < 256)
    (hk1 : ∀ j < 4, k + sel o₁ j < 256) {s : State} (h8 : s.gpr .r8 = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block (yzetaS o₀ o₁)) s fun s' => ZLanes (s'.lane .xmm13 0) (fun i => zetas (k + sel o₀ i)) ∧
      ZLanes (s'.lane .xmm13 1) (fun i => zetas (k + sel o₁ i)) ∧
      (∀ l < 2, ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm2, .xmm12] s s' := by
  rw [yzetaS, WP.block_append_iff, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (ybcast_ok (by rw [h8, add_ofNat_zero]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by rfl) (P := fun l t =>
      t.xmm .xmm13 = shufDwords (s1.lane .xmm13 l) o₀ ∧ t.xmm .xmm2 = shufDwords (s1.lane .xmm13 l) o₁)
    fun l _ => zsseS_ok o₀ o₁ (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ?_
  refine WP.mono (yF5_ok s3) fun s4 ⟨f4, o4⟩ => ?_
  have x0 : s4.lane .xmm13 0 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₀ := by
    have e : s2.lane .xmm13 0 = _ := (l2 0 (by decide)).1
    rw [o4.lane _ (by decide) 0 (by decide), e0, e, b1 0 (by decide), h8, add_ofNat_zero]
  have x1 : s4.lane .xmm13 1 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₁ := by
    have e : s2.lane .xmm2 1 = _ := (l2 1 (by decide)).2
    rw [o4.lane _ (by decide) 1 (by decide), e1, e, b1 1 (by decide), h8, add_ofNat_zero]
  refine ⟨by rw [x0]; exact zlanes_tab o₀ hk0 ht, by rw [x1]; exact zlanes_tab o₁ hk1 ht,
    fun l hl => ?_, (((o1.trans o2).trans o3).trans o4).mono (by simp)⟩
  rw [f4 l hl, o4.lane _ (by decide) l hl]
  exact zodd_F5 _

end VG.Proof.MlDsa.X86_64.Arith
