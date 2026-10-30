module

public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyBase
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YLay21
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Lazy
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyInvariant
public import VerifiedGarbage.Proof.MlDsa.Arith.LazyButterfly
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyReduce
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
import VerifiedGarbage.Proof.MlKem.X86_64.YNttLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyNttLayers
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.LazyButterfly
public import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Avx2
public import VerifiedGarbage.Proof.MlDsa.Arith.Mem
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Table
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLanes
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay
public import VerifiedGarbage.Proof.MlKem.X86_64.YLanes

/-!
# ML-DSA on x86-64: the last three layers of the lazy NTT and its reduction, at once

`fusedLast` runs the layers with `len = 4, 2, 1` and `reduceLazy` on the
sixteen coefficients from `16m` in registers (`fstep`), in one pass over the
polynomial instead of four (`fusedLast_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Arith.Lazy

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith hiding BlkOk layF layF1_get layF2_get
open VG.Proof.MlDsa.Arith.Lazy
open VG.Proof.MlKem.X86_64 (Keep XOnly XKeep YOnly ylanes yld_ok ifp ifn sel sel_lt add_ofNat_zero GOnly
  addR_ok wp_rcxLoopY wp_cons_iff lane_setReg lane_setFlags State.setMem_ymm State.setMem_setMem)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop)
open VG.Spec.MlDsa (q n Zq coeffAt zetas)

/-! ## Loads from any memory operand -/

theorem ybcastM_ok {s : State} {m : MemOp} {d : XReg} (h : InRegions (s.rd ++ s.wr) (s.ea m) 16) :
    WP isa (.block [.vbroadcasti128 d m]) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW (s.ea m) 128) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128, h, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem yldM_ok {s : State} {m : MemOp} {d : XReg} (h : InRegions (s.rd ++ s.wr) (s.ea m) 32) :
    WP isa (.block [.vmovdquLoad .l256 d m]) s fun s' =>
      (∀ l < 2, s'.lane d l = s.mem.readW (s.ea m + BitVec.ofNat 64 (16 * l)) 128) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load256, h, ite_true,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl, VG.Proof.MlKem.X86_64.lane_readW256 _ _ hl]
  · rw [State.lane_setV256, ifn (by simpa using hr)]

/-! ## The zetas, from any memory operand -/

theorem yzetaSm_ok (o₀ o₁ : BitVec 8) {m : MemOp} {zP : Addr} {k : Nat} (hk0 : ∀ j < 4, k + sel o₀ j < 256)
    (hk1 : ∀ j < 4, k + sel o₁ j < 256) {s : State} (hm : s.ea m = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 16) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block (yzetaSm m o₀ o₁)) s fun s' => ZLanes (s'.lane .xmm13 0) (fun i => zetas (k + sel o₀ i)) ∧
      ZLanes (s'.lane .xmm13 1) (fun i => zetas (k + sel o₁ i)) ∧
      (∀ l < 2, ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm2, .xmm12] s s' := by
  rw [yzetaSm, WP.block_append_iff, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (ybcastM_ok (by rw [hm]; exact hin)) fun s1 ⟨b1, o1⟩ => ?_
  refine WP.mono (ylanes (by rfl) (P := fun l t =>
      t.xmm .xmm13 = shufDwords (s1.lane .xmm13 l) o₀ ∧ t.xmm .xmm2 = shufDwords (s1.lane .xmm13 l) o₁)
    fun l _ => zsseS_ok o₀ o₁ (s1.proj l)) fun s2 ⟨l2, o2⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.yblend_ok s2) fun s3 ⟨e0, e1, o3⟩ => ?_
  refine WP.mono (yF5_ok s3) fun s4 ⟨f4, o4⟩ => ?_
  have x0 : s4.lane .xmm13 0 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₀ := by
    have e : s2.lane .xmm13 0 = _ := (l2 0 (by decide)).1
    rw [o4.lane _ (by decide) 0 (by decide), e0, e, b1 0 (by decide), hm]
  have x1 : s4.lane .xmm13 1 = shufDwords (s.mem.readW (coeffAddr zP k) 128) o₁ := by
    have e : s2.lane .xmm2 1 = _ := (l2 1 (by decide)).2
    rw [o4.lane _ (by decide) 1 (by decide), e1, e, b1 1 (by decide), hm]
  refine ⟨by rw [x0]; exact zlanes_tab o₀ hk0 ht, by rw [x1]; exact zlanes_tab o₁ hk1 ht,
    fun l hl => ?_, (((o1.trans o2).trans o3).trans o4).mono (by simp)⟩
  rw [f4 l hl, o4.lane _ (by decide) l hl]
  exact zodd_F5 _

theorem yzeta8m_ok {m : MemOp} {zP : Addr} {k : Nat} (hk : k + 8 ≤ 256) {s : State} (hm : s.ea m = coeffAddr zP k)
    (hin : InRegions (s.rd ++ s.wr) (coeffAddr zP k) 32) (ht : Tab zmTab s.mem zP 256) :
    WP isa (.block (yzeta8m m)) s fun s' =>
      (∀ l < 2, ZLanes (s'.lane .xmm13 l) (fun e => zetas (k + (2 * l + e + 2 * (e / 2)))) ∧
        ZOdd (s'.lane .xmm13 l) (s'.lane .xmm12 l)) ∧ YOnly [.xmm13, .xmm12] s s' := by
  rw [yzeta8m, WP.block_append_iff, wp_cons_iff]
  refine WP.mono (yldM_ok (by rw [hm]; exact hin)) fun s1 ⟨L1, o1⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.ypermq_ok s1) fun s2 ⟨e0, e1, o2⟩ => ?_
  refine WP.mono (yF5_ok s2) fun s3 ⟨f3, o3⟩ => ⟨fun l hl => ?_, ((o1.trans o2).trans o3).mono (by simp)⟩
  rw [f3 l hl, o3.lane _ (by decide) l hl]
  refine ⟨fun e he => ?_, zodd_F5 _⟩
  have a : ∀ l < 2, s1.lane .xmm13 l = s.mem.readW (coeffAddr zP (k + 4 * l)) 128 := fun l hl => by
    rw [L1 l hl, hm, lane_load]
  rcases lane01 hl with rfl | rfl
  · rw [e0, dword_punpcklqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht he (by omega_arith) (by omega_arith)
    · exact dword_tab ht (by omega_arith) (by omega_arith) (by omega_arith)
  · rw [e1, dword_punpckhqdq _ _ he, a 0 (by decide), a 1 (by decide)]
    split
    · exact dword_tab ht (by omega_arith) (by omega_arith) (by omega_arith)
    · exact dword_tab ht he (by omega_arith) (by omega_arith)

/-! ## A layer, coefficient by coefficient -/

/-- Coefficient `x` after a whole layer with `len`. -/
theorem layer_get (G : Poly) {len : Nat} (hlen : len ∈ [1, 2, 4]) {x : Nat} (hx : x < 256) :
    (layer G len)[x]! = if x % (2 * len) < len then (op G[x]! G[x + len]! (zetas (128 / len + x / (2 * len)))).1
      else (op G[x - len]! G[x]! (zetas (128 / len + x / (2 * len)))).2 := by
  have h : 0 < len ∧ 2 * len * (128 / len) = 256 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    rcases hlen with rfl | rfl | rfl <;> decide
  rw [layer, layF_get (block_ok op) G h.1 _ (by omega) hx, ite_eq_left (by omega)]

theorem op_eq (G : Poly) {a b c a' b' c' : Nat} (ha : a = a') (hb : b = b') (hc : c = c') :
    op G[a]! G[b]! (zetas c) = op G[a']! G[b']! (zetas c') := by subst ha hb hc; rfl

/-! ## Sixteen coefficients in registers -/

/-- The sixteen coefficients of `X` from `j` in `ymm0` and `ymm1`, in order:
in lane `l`, those from `j + 4l` and from `j + 8 + 4l`. -/
def CV (s : State) (X : Poly) (j : Nat) : Prop :=
  ∀ l < 2, DLanes (s.lane .xmm0 l) (fun e => X[j + 4 * l + e]!) ∧ DLanes (s.lane .xmm1 l) (fun e => X[j + 8 + 4 * l + e]!)

/-- The code of the layer with `len = 4` on the coefficients in `ymm4` and `ymm5`. -/
abbrev f4code : List Instr :=
  ([.vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20), .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] : List Instr) ++
    (toY lazyBfly ++ ([.vop (.vperm2i128 .xmm1 .xmm0 .xmm3 0x31), .vop (.vperm2i128 .xmm0 .xmm0 .xmm3 0x20)] : List Instr))

/-- The layer with `len = 4` on the sixteen coefficients of `G` from `16m`, in `ymm4` and `ymm5`. -/
theorem f4_ok {G : Poly} {m : Nat} (hm : m < 16) {s : State} (hc : YConsts s)
    (h4 : ∀ l < 2, DLanes (s.lane .xmm4 l) (fun e => G[16 * m + 4 * l + e]!))
    (h5 : ∀ l < 2, DLanes (s.lane .xmm5 l) (fun e => G[16 * m + 8 + 4 * l + e]!))
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => zetas (32 + 2 * m + l)))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l)) :
    WP isa (.block f4code) s fun s' => CV s' (layer G 4) (16 * m) ∧ YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  rw [f4code, WP.block_append_iff, show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl,
    WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s) fun s1 ⟨P1, o1⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s1) fun s2 ⟨P2, o2⟩ => ?_
  have o12 := o1.trans o2
  rw [WP.block_append_iff]
  refine WP.mono (ybf_ok bfly_ok lane_lazyBfly (yonly_yconsts o12 hc (by decide) (by decide))
    (x := fun l e => G[16 * m + 8 * l + e]!) (y := fun l e => G[16 * m + 8 * l + 4 + e]!)
    (ζ := fun l _ => zetas (32 + 2 * m + l))
    (fun l hl => by
      rw [o2.lane _ (by decide) l hl, P1 l hl, VG.Proof.MlKem.X86_64.perm20 _ _ hl]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl]; exact (h4 0 (by decide)).congr fun e _ => getP_congr G (by omega)
      · rw [ifn (by decide)]; exact (h5 0 (by decide)).congr fun e _ => getP_congr G (by omega))
    (fun l hl => by
      rw [P2 l hl, VG.Proof.MlKem.X86_64.perm31 _ _ hl, o1.lane .xmm4 (by decide) 1 (by decide),
        o1.lane .xmm5 (by decide) 1 (by decide)]
      rcases lane01 hl with rfl | rfl
      · rw [ifp rfl]; exact (h4 1 (by decide)).congr fun e _ => getP_congr G (by omega)
      · rw [ifn (by decide)]; exact (h5 1 (by decide)).congr fun e _ => getP_congr G (by omega))
    (fun l hl => by rw [o12.lane _ (by decide) l hl]; exact hz l hl)
    (fun l hl => by rw [o12.lane _ (by decide) l hl, o12.lane _ (by decide) l hl]; exact ho l hl))
    fun s3 ⟨B3, o3⟩ => ?_
  rw [show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, WP.block_append_iff]
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s3) fun s4 ⟨P4, o4⟩ => ?_
  refine WP.mono (VG.Proof.MlKem.X86_64.yperm_ok s4) fun s5 ⟨P5, o5⟩ => ⟨fun l hl => ⟨?_, ?_⟩, ?_⟩
  · rw [P5 l hl, VG.Proof.MlKem.X86_64.perm20 _ _ hl, o4.lane .xmm3 (by decide) 0 (by decide)]
    rcases lane01 hl with rfl | rfl
    · rw [ifp rfl, o4.lane .xmm0 (by decide) 0 (by decide)]
      exact (B3 0 (by decide)).1.congr fun e he => by
        rw [layer_get G (by decide) (by omega), ite_eq_left (by omega)]
        exact congrArg Prod.fst (op_eq G (by omega) (by omega) (by omega))
    · rw [ifn (by decide)]
      exact (B3 0 (by decide)).2.congr fun e he => by
        rw [layer_get G (by decide) (by omega), ite_eq_right (by omega)]
        exact congrArg Prod.snd (op_eq G (by omega) (by omega) (by omega))
  · rw [o5.lane .xmm1 (by decide) l hl, P4 l hl, VG.Proof.MlKem.X86_64.perm31 _ _ hl]
    rcases lane01 hl with rfl | rfl
    · rw [ifp rfl]
      exact (B3 1 (by decide)).1.congr fun e he => by
        rw [layer_get G (by decide) (by omega), ite_eq_left (by omega)]
        exact congrArg Prod.fst (op_eq G (by omega) (by omega) (by omega))
    · rw [ifn (by decide)]
      exact (B3 1 (by decide)).2.congr fun e he => by
        rw [layer_get G (by decide) (by omega), ite_eq_right (by omega)]
        exact congrArg Prod.snd (op_eq G (by omega) (by omega) (by omega))
  · exact (o12.trans (o3.trans (o4.trans o5))).mono (by simp)

/-- The layer with `len = 2` on the sixteen coefficients of `P` from `16m` in `ymm0` and `ymm1`. -/
theorem f2_ok {P : Poly} {m : Nat} (hm : m < 16) {s : State} (hc : YConsts s) (hv : CV s P (16 * m))
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => zetas (64 + 4 * m + l + 2 * (e / 2))))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l)) :
    WP isa (.block (toY (gath2 ++ lazyBfly ++ scat2))) s fun s' =>
      CV s' (layer P 2) (16 * m) ∧ YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  refine WP.mono (ylanes lane_core2f (P := fun l t => DLanes (t.xmm .xmm0) (fun e => (layer P 2)[16 * m + 4 * l + e]!) ∧
      DLanes (t.xmm .xmm1) (fun e => (layer P 2)[16 * m + 8 + 4 * l + e]!))
    fun l hl => WP.mono (core2_ok bfly_ok (hc l hl) (hv l hl).1 (hv l hl).2 (hz l hl) (ho l hl))
      fun t' ⟨⟨a, b⟩, o⟩ => ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩)
    fun s' ⟨h, o⟩ => ⟨fun l hl => h l hl, o⟩
  · by_cases h : e < 2
    · rw [ite_eq_left h, layer_get P (by decide) (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (op_eq P (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, layer_get P (by decide) (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (op_eq P (by omega) (by omega) (by omega))
  · by_cases h : e < 2
    · rw [ite_eq_left h, layer_get P (by decide) (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (op_eq P (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, layer_get P (by decide) (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (op_eq P (by omega) (by omega) (by omega))

/-- The layer with `len = 1` on the sixteen coefficients of `P` from `16m` in `ymm0` and `ymm2`. -/
theorem f1_ok {P : Poly} {m : Nat} (hm : m < 16) {s : State} (hc : YConsts s)
    (h0 : ∀ l < 2, DLanes (s.lane .xmm0 l) (fun e => P[16 * m + 4 * l + e]!))
    (h2 : ∀ l < 2, DLanes (s.lane .xmm2 l) (fun e => P[16 * m + 8 + 4 * l + e]!))
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun e => zetas (128 + 8 * m + (2 * l + e + 2 * (e / 2)))))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l)) :
    WP isa (.block (toY (gath1 ++ lazyBfly ++ scat1))) s fun s' =>
      CV s' (layer P 1) (16 * m) ∧ YOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  refine WP.mono (ylanes lane_core1f (P := fun l t => DLanes (t.xmm .xmm0) (fun e => (layer P 1)[16 * m + 4 * l + e]!) ∧
      DLanes (t.xmm .xmm1) (fun e => (layer P 1)[16 * m + 8 + 4 * l + e]!))
    fun l hl => WP.mono (core1_ok bfly_ok (hc l hl) (h0 l hl) (h2 l hl) (hz l hl) (ho l hl))
      fun t' ⟨⟨a, b⟩, o⟩ => ⟨⟨a.congr fun e he => ?_, b.congr fun e he => ?_⟩, o⟩)
    fun s' ⟨h, o⟩ => ⟨fun l hl => h l hl, o⟩
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, layer_get P (by decide) (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (op_eq P (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, layer_get P (by decide) (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (op_eq P (by omega) (by omega) (by omega))
  · by_cases h : e % 2 = 0
    · rw [ite_eq_left h, layer_get P (by decide) (by omega), ite_eq_left (by omega)]
      exact congrArg Prod.fst (op_eq P (by omega) (by omega) (by omega))
    · rw [ite_eq_right h, layer_get P (by decide) (by omega), ite_eq_right (by omega)]
      exact congrArg Prod.snd (op_eq P (by omega) (by omega) (by omega))

/-! ## The rest of an iteration -/

theorem ymov_ok {d a : XReg} (s : State) :
    WP isa (.block [.vop (.vmovdqa .l256 d a)]) s fun s' => (∀ l < 2, s'.lane d l = s.lane a l) ∧ YOnly [d] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq, exists_eq_left']
  refine ⟨fun l hl => ?_, ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun r hr l hl => ?_⟩⟩
  · rw [State.lane_setV256, ifp rfl]; rcases lane01 hl with rfl | rfl <;> rfl
  · rw [State.lane_setV256, ifn (by simpa using hr)]

theorem ea_fzeta {s : State} {sP : Addr} {m : Nat} (hsi : s.gpr .rsi = sP) (hax : s.gpr .rax = BitVec.ofNat 64 (8 * m))
    (hm : m < 16) (sc d k : Nat) (hsc : sc ≤ 4) (hk : 4 * k = 8 * m * sc + d) (hd : d ≤ 512) :
    s.ea (fzeta sc d) = coeffAddr sP k := by
  show s.gpr .rsi + s.gpr .rax * BitVec.ofNat 64 sc + BitVec.ofInt 64 (d : Int) = _
  rw [BitVec.ofInt_natCast, hsi, hax, coeffAddr]
  apply BitVec.eq_of_toNat_eq
  have h1 : 8 * m * sc < 2 ^ 64 := by
    have : 8 * m * sc ≤ 8 * 16 * 4 := Nat.mul_le_mul (Nat.mul_le_mul_left 8 (by omega)) hsc
    omega
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 8 * m < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show sc < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega), hk]
  generalize 8 * m * sc = c at h1 ⊢
  omega

theorem ea_fcoef {s : State} {fP : Addr} {m : Nat} (hdi : s.gpr .rdi = fP) (hax : s.gpr .rax = BitVec.ofNat 64 (8 * m))
    (hm : m < 16) (d : Nat) (hd : d ≤ 32) : s.ea (fcoef d) = coeffAddr fP (16 * m) + BitVec.ofNat 64 d := by
  show s.gpr .rdi + s.gpr .rax * BitVec.ofNat 64 8 + BitVec.ofInt 64 (d : Int) = _
  rw [BitVec.ofInt_natCast, hdi, hax, coeffAddr]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 8 * m < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (8 : Nat) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 8 * m * 8 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 4 * (16 * m) < 2 ^ 64 by omega)]
  omega

/-- The three layers of an iteration, after the loads. -/
abbrev fmid : List Instr :=
  yzetaSm (fzeta 1 128) 0x00 0x55 ++ (f4code ++ (yzetaSm (fzeta 2 256) 0xA0 0xF5 ++
    (toY (gath2 ++ lazyBfly ++ scat2) ++ (([.vop (.vmovdqa .l256 .xmm2 .xmm1)] : List Instr) ++
      (yzeta8m (fzeta 4 512) ++ toY (gath1 ++ lazyBfly ++ scat1))))))

/-- The three layers on the sixteen coefficients of `G` from `16m` in `ymm4` and `ymm5`. -/
theorem fmid_ok {G : Poly} {m : Nat} (hm : m < 16) {sP : Addr} {s : State} (hc : YConsts s)
    (hsi : s.gpr .rsi = sP) (hax : s.gpr .rax = BitVec.ofNat 64 (8 * m)) (hT : Tab zmTab s.mem sP 256)
    (hw : pR sP ∈ s.wr)
    (h4 : ∀ l < 2, DLanes (s.lane .xmm4 l) (fun e => G[16 * m + 4 * l + e]!))
    (h5 : ∀ l < 2, DLanes (s.lane .xmm5 l) (fun e => G[16 * m + 8 + 4 * l + e]!)) :
    WP isa (.block fmid) s fun s' => CV s' (layer (layer (layer G 4) 2) 1) (16 * m) ∧ YConsts s' ∧
      YOnly [.xmm13, .xmm2, .xmm12, .xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm13, .xmm2, .xmm12, .xmm0, .xmm1, .xmm2,
        .xmm3, .xmm4, .xmm2, .xmm13, .xmm12, .xmm0, .xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  have hin : InRegions (s.rd ++ s.wr) (coeffAddr sP (32 + 2 * m)) 16 := tab_in (List.mem_append_right _ hw) (by omega)
  rw [fmid, WP.block_append_iff]
  refine WP.mono (yzetaSm_ok 0x00 0x55 (k := 32 + 2 * m) (fun j _ => by rw [VG.Proof.MlKem.X86_64.sel_zero]; omega)
    (fun j hj => by rw [VG.Proof.MlKem.X86_64.sel_55 hj]; omega)
    (ea_fzeta hsi hax hm 1 128 _ (by decide) (by omega) (by decide)) hin hT) fun s1 ⟨Z0, Z1, ZO, o1⟩ => ?_
  have c1 : YConsts s1 := yonly_yconsts o1 hc (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (f4_ok (G := G) hm c1 (fun l hl => by rw [o1.lane _ (by decide) l hl]; exact h4 l hl)
    (fun l hl => by rw [o1.lane _ (by decide) l hl]; exact h5 l hl)
    (fun l hl => by
      rcases lane01 hl with rfl | rfl
      · exact Z0.congr fun i _ => congrArg zetas (by rw [VG.Proof.MlKem.X86_64.sel_zero])
      · exact Z1.congr fun i hi => congrArg zetas (by rw [VG.Proof.MlKem.X86_64.sel_55 hi]))
    ZO) fun s2 ⟨V2, o2⟩ => ?_
  have c2 : YConsts s2 := yonly_yconsts o2 c1 (by decide) (by decide)
  have o12 := o1.trans o2
  have hin2 : InRegions (s2.rd ++ s2.wr) (coeffAddr sP (64 + 4 * m)) 16 := by
    rw [o12.rd, o12.wr]; exact tab_in (List.mem_append_right _ hw) (by omega)
  have hA : ∀ e < 4, sel 0xA0 e = 2 * (e / 2) := by decide
  have hF : ∀ e < 4, sel 0xF5 e = 1 + 2 * (e / 2) := by decide
  rw [WP.block_append_iff]
  refine WP.mono (yzetaSm_ok 0xA0 0xF5 (k := 64 + 4 * m) (fun j hj => by rw [hA j hj]; omega)
    (fun j hj => by rw [hF j hj]; omega)
    (ea_fzeta (by rw [o12.gpr, hsi]) (by rw [o12.gpr, hax]) hm 2 256 _ (by decide) (by omega) (by decide)) hin2
    (by rw [o12.mem]; exact hT)) fun s3 ⟨Y0, Y1, YO, o3⟩ => ?_
  have c3 : YConsts s3 := yonly_yconsts o3 c2 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (f2_ok (P := layer G 4) hm c3
    (fun l hl => ⟨by rw [o3.lane _ (by decide) l hl]; exact (V2 l hl).1, by rw [o3.lane _ (by decide) l hl]; exact (V2 l hl).2⟩)
    (fun l hl => by
      rcases lane01 hl with rfl | rfl
      · exact Y0.congr fun e he => congrArg zetas (by rw [hA e he]; omega)
      · exact Y1.congr fun e he => congrArg zetas (by rw [hF e he]; omega))
    YO) fun s4 ⟨V4, o4⟩ => ?_
  have c4 : YConsts s4 := yonly_yconsts o4 c3 (by decide) (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ymov_ok (d := .xmm2) (a := .xmm1) s4) fun s5 ⟨M5, o5⟩ => ?_
  have c5 : YConsts s5 := yonly_yconsts o5 c4 (by decide) (by decide)
  have o15 := (o12.trans o3).trans (o4.trans o5)
  have hin3 : InRegions (s5.rd ++ s5.wr) (coeffAddr sP (128 + 8 * m)) 32 := by
    rw [o15.rd, o15.wr]; exact f_in32 (List.mem_append_right _ hw) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (yzeta8m_ok (k := 128 + 8 * m) (by omega)
    (ea_fzeta (by rw [o15.gpr, hsi]) (by rw [o15.gpr, hax]) hm 4 512 _ (by decide) (by omega) (by decide)) hin3
    (by rw [o15.mem]; exact hT)) fun s6 ⟨Z6, o6⟩ => ?_
  have c6 : YConsts s6 := yonly_yconsts o6 c5 (by decide) (by decide)
  refine WP.mono (f1_ok (P := layer (layer G 4) 2) hm c6
    (fun l hl => by rw [o6.lane _ (by decide) l hl, o5.lane _ (by decide) l hl]; exact (V4 l hl).1)
    (fun l hl => by rw [o6.lane _ (by decide) l hl, M5 l hl]; exact (V4 l hl).2)
    (fun l hl => (Z6 l hl).1) (fun l hl => (Z6 l hl).2)) fun s7 ⟨V7, o7⟩ =>
      ⟨V7, yonly_yconsts o7 c6 (by decide) (by decide), (o15.trans (o6.trans o7)).mono (by simp)⟩

theorem ystM_ok {s : State} {m : MemOp} {d : XReg} (h : InRegions s.wr (s.ea m) 32) :
    WP isa (.block [.vmovdquStore .l256 m d]) s fun s' => s' = s.setMem (s.mem.writeW (s.ea m) (s.ymm d)) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store256_eq, h, ite_true,
    Option.some.injEq, exists_eq_left']

/-! ## An iteration -/

/-- After `m` iterations: the coefficients before `16m` are those of `T`,
reduced, the others those of `G`. -/
structure FI (fP sP : Addr) (G T : Poly) (m : Nat) (s : State) : Prop where
  mem : ∀ k < 256, (coeffAt s.mem fP k).toNat = if k < 16 * m then (residue T[k]!).val else G[k]!.val
  rax : s.gpr .rax = BitVec.ofNat 64 (8 * m)
  rdi : s.gpr .rdi = fP
  rsi : s.gpr .rsi = sP
  tab : Tab zmTab s.mem sP 256
  c : YConsts s
  wf : pR fP ∈ s.wr
  ws : pR sP ∈ s.wr

theorem fusedBody_eq : fusedBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr) =
    ([.vmovdquLoad .l256 .xmm4 (fcoef 0)] : List Instr) ++ (([.vmovdquLoad .l256 .xmm5 (fcoef 32)] : List Instr) ++
      (fmid ++ (([.vop (.vmovdqa .l256 .xmm5 .xmm1)] : List Instr) ++ (toY reduceLazy ++
        (([.vmovdquStore .l256 (fcoef 0) .xmm0] : List Instr) ++ (([.vop (.vmovdqa .l256 .xmm0 .xmm5)] : List Instr) ++
          (toY reduceLazy ++ ([.vmovdquStore .l256 (fcoef 32) .xmm0, .alu .add .rax (.imm 8),
            .alu .sub .rcx (.imm 1)] : List Instr)))))))) := by
  simp only [fusedBody, fmid, f4code, List.append_assoc, List.cons_append, List.nil_append]

/-- `reduceLazy` on the eight coefficients of `ymm0`. -/
theorem fred_ok {X : Poly} {a : Nat} {s : State} (hc : YConsts s)
    (h0 : ∀ l < 2, DLanes (s.lane .xmm0 l) (fun e => X[a + 4 * l + e]!))
    (hb : ∀ l < 2, ∀ e < 4, X[a + 4 * l + e]!.val < 17 * q) :
    WP isa (.block (toY reduceLazy)) s fun s' =>
      (∀ l < 2, Arith.DLanes (s'.lane .xmm0 l) (fun e => residue X[a + 4 * l + e]!)) ∧ YOnly [.xmm0, .xmm1, .xmm2] s s' :=
  ylanes (by decide +kernel) (P := fun l t => Arith.DLanes (t.xmm .xmm0) (fun e => residue X[a + 4 * l + e]!))
    fun l hl => reduce_ok (hc l hl).toVConsts (h0 l hl) (hb l hl)

theorem fstep {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {G : Poly} {m : Nat} (hm : m < 16)
    (hb : ∀ k < 256, (layer (layer (layer G 4) 2) 1)[k]!.val < 17 * q) {s : State}
    (hI : FI fP sP G (layer (layer (layer G 4) 2) 1) m s) :
    WP isa (.block (fusedBody ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      FI fP sP G (layer (layer (layer G 4) 2) 1) (m + 1) s' ∧ Keep [.rax, .rcx] s s' ∧ Frame [pR fP] s.mem s'.mem ∧
        s'.mxcsr = s.mxcsr ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  generalize hT : layer (layer (layer G 4) 2) 1 = T at hb hI
  have j0 : 16 * m + 8 ≤ 256 := by omega
  have j1 : 16 * m + 8 + 8 ≤ 256 := by omega
  have e0 := ea_fcoef hI.rdi hI.rax hm 0 (by decide)
  have e1 := ea_fcoef hI.rdi hI.rax hm 32 (by decide)
  rw [add_ofNat_zero] at e0
  rw [show (32 : Nat) = 4 * 8 from rfl, coeffAddr_add] at e1
  rw [fusedBody_eq, WP.block_append_iff]
  refine WP.mono (yldM_ok (by rw [e0]; exact f_in32 (List.mem_append_right _ hI.wf) j0)) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  have di1 : s1.gpr .rdi = fP := by rw [o1.gpr]; exact hI.rdi
  have ax1 : s1.gpr .rax = BitVec.ofNat 64 (8 * m) := by rw [o1.gpr]; exact hI.rax
  have e1' := ea_fcoef di1 ax1 hm 32 (by decide)
  rw [show (32 : Nat) = 4 * 8 from rfl, coeffAddr_add] at e1'
  refine WP.mono (yldM_ok (by rw [o1.rd, o1.wr, e1']; exact f_in32 (List.mem_append_right _ hI.wf) j1))
    fun s2 ⟨L2, o2⟩ => ?_
  have o12 := o1.trans o2
  have hG : ∀ k, 16 * m ≤ k → k < 256 → (coeffAt s.mem fP k).toNat = G[k]!.val := fun k h1 h2 => by
    rw [hI.mem k h2, ifn (by omega)]
  have ld : ∀ j, 16 * m ≤ j → j + 8 ≤ 256 → ∀ l < 2,
      DLanes (s.mem.readW (coeffAddr fP j + BitVec.ofNat 64 (16 * l)) 128) (fun e => G[j + 4 * l + e]!) :=
    fun j h1 h2 l hl e he => by
      rw [dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, hG _ (by omega) (by omega)]
  rw [WP.block_append_iff]
  have si2 : s2.gpr .rsi = sP := by rw [o12.gpr]; exact hI.rsi
  have ax2 : s2.gpr .rax = BitVec.ofNat 64 (8 * m) := by rw [o12.gpr]; exact hI.rax
  have tb2 : Tab zmTab s2.mem sP 256 := by rw [o12.mem]; exact hI.tab
  have ws2 : pR sP ∈ s2.wr := by rw [o12.wr]; exact hI.ws
  refine WP.mono (fmid_ok (G := G) (sP := sP) hm (yonly_yconsts o12 hI.c (by decide) (by decide)) si2 ax2 tb2 ws2
    (fun l hl => by rw [o2.lane _ (by decide) l hl, L1 l hl, e0]; exact ld _ (by omega) j0 l hl)
    (fun l hl => by rw [L2 l hl, o1.mem, e1']; exact ld _ (by omega) j1 l hl))
    fun s3 ⟨V3, c3, o3⟩ => ?_
  rw [hT] at V3
  rw [WP.block_append_iff]
  refine WP.mono (ymov_ok (d := .xmm5) (a := .xmm1) s3) fun s4 ⟨M4, o4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (fred_ok (X := T) (a := 16 * m) (yonly_yconsts o4 c3 (by decide) (by decide))
    (fun l hl => by rw [o4.lane _ (by decide) l hl]; exact (V3 l hl).1)
    (fun l hl e he => hb (16 * m + 4 * l + e) (by omega))) fun s5 ⟨R5, o5⟩ => ?_
  have o15 := (((o12.trans o3).trans o4).trans o5)
  have di5 : s5.gpr .rdi = fP := by rw [o15.gpr]; exact hI.rdi
  have ax5 : s5.gpr .rax = BitVec.ofNat 64 (8 * m) := by rw [o15.gpr]; exact hI.rax
  have a5 := ea_fcoef di5 ax5 hm 0 (by decide)
  rw [add_ofNat_zero] at a5
  rw [WP.block_append_iff]
  refine WP.mono (ystM_ok (by rw [a5, o15.wr]; exact f_in32 hI.wf j0)) fun s6 h6 => ?_
  subst h6
  rw [WP.block_append_iff]
  refine WP.mono (ymov_ok (d := .xmm0) (a := .xmm5) _) fun s7 ⟨M7, o7⟩ => ?_
  rw [WP.block_append_iff]
  have c6 : YConsts (s5.setMem (s5.mem.writeW (s5.ea (fcoef 0)) (s5.ymm .xmm0))) :=
    ylanes_gpr (s := s5) (fun r l => State.setMem_lane ..) o15 hI.c (by decide) (by decide)
  refine WP.mono (fred_ok (X := T) (a := 16 * m + 8) (yonly_yconsts o7 c6 (by decide) (by decide))
    (fun l hl => by
      rw [M7 l hl, State.setMem_lane, o5.lane _ (by decide) l hl, M4 l hl]; exact (V3 l hl).2)
    (fun l hl e he => hb (16 * m + 8 + 4 * l + e) (by omega))) fun s8 ⟨R8, o8⟩ => ?_
  have o78 := o7.trans o8
  have g8 : s8.gpr = s5.gpr := by simp only [o78.gpr, State.setMem_gpr]
  have a8 : s8.ea (fcoef 32) = coeffAddr fP (16 * m + 8) := by
    have di8 : s8.gpr .rdi = fP := by rw [g8]; exact di5
    have ax8 : s8.gpr .rax = BitVec.ofNat 64 (8 * m) := by rw [g8]; exact ax5
    rw [ea_fcoef di8 ax8 hm 32 (by decide)]
    exact coeffAddr_add fP (16 * m) 8
  rw [show ([.vmovdquStore .l256 (fcoef 32) .xmm0, .alu .add .rax (.imm 8), .alu .sub .rcx (.imm 1)] : List Instr) =
    [.vmovdquStore .l256 (fcoef 32) .xmm0] ++ [.alu .add .rax (.imm 8), .alu .sub .rcx (.imm 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (ystM_ok (by rw [a8, o78.wr, State.setMem_wr, o15.wr]; exact f_in32 hI.wf j1)) fun s9 h9 => ?_
  subst h9
  rw [a8, o78.mem, State.setMem_mem, o15.mem, a5]
  vrund [State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd, State.setMem_ymm]
  have mx : ∀ (t : State) (M : Mem), (t.setMem M).mxcsr = t.mxcsr := fun t _ => by cases t; rfl
  have g5 := o15.gpr
  refine ⟨⟨fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    rw [coeffAt_write256 _ _ j1 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 16 * (m + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      split
      · have := R8 0 (by decide) (k - (16 * m + 8)) (by omega)
        dsimp only at this
        rw [show 16 * m + 8 + 4 * 0 + (k - (16 * m + 8)) = k by omega] at this; exact this
      · have := R8 1 (by decide) (k - (16 * m + 8) - 4) (by omega)
        dsimp only at this
        rw [show 16 * m + 8 + 4 * 1 + (k - (16 * m + 8) - 4) = k by omega] at this; exact this
    · rename_i h
      rw [coeffAt_write256 _ _ j0 _ hk]
      split
      · rename_i h'
        rw [ifp (show k < 16 * (m + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
        split
        · have := R5 0 (by decide) (k - 16 * m) (by omega)
          dsimp only at this
          rw [show 16 * m + 4 * 0 + (k - 16 * m) = k by omega] at this; exact this
        · have := R5 1 (by decide) (k - 16 * m - 4) (by omega)
          dsimp only at this
          rw [show 16 * m + 4 * 1 + (k - 16 * m - 4) = k by omega] at this; exact this
      · rename_i h'
        rw [hI.mem k hk]
        by_cases h'' : k < 16 * m
        · rw [ifp h'', ifp (by omega)]
        · rw [ifn h'', ifn (by omega)]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, ↓reduceIte]
    rw [g8, ax5, show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 from by decide,
      ← BitVec.ofNat_add, Nat.mul_succ]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, reduceCtorEq, ↓reduceIte]
    rw [g8, di5]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, State.setMem_gpr, reduceCtorEq, ↓reduceIte]
    rw [g8, g5, hI.rsi]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags, State.setMem_mem]
    exact hI.tab.frame (((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP j0)).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP j1))
      (fun r hr => by rw [List.mem_singleton.1 hr]; exact hd) (by decide)
  · exact ylanes_gpr (s := s8) (fun r l => by simp only [lane_setReg, lane_setFlags, State.setMem_lane]) o78 c6
      (by decide) (by decide)
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr, o78.wr, o15.wr]; exact hI.wf
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr, o78.wr, o15.wr]; exact hI.ws
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false, State.setMem_gpr]
    rw [g8, g5]
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags, State.setMem_rd, o78.rd, o15.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags, State.setMem_wr, o78.wr, o15.wr]
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (pR_contains32 fP j0)).writeW
      (List.mem_singleton_self _) _ (pR_contains32 fP j1)
  · rw [mx, o78.mxcsr, mx, o15.mxcsr]
  · rw [g8, g5]
  · rw [g8, g5]

/-- The last three layers and the reduction, sixteen chunks of sixteen
coefficients. -/
theorem fusedLast_ok {fP sP : Addr} (hd : (pR sP).Disjoint (pR fP)) {G : Poly} {f : VG.Spec.MlDsa.Poly}
    (hr : Rel 17 (layer (layer (layer G 4) 2) 1) f) (s : State) (hc : YConsts s) (hdi : s.gpr .rdi = fP)
    (hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP G) (hT : Tab zmTab s.mem sP 256) (hwf : pR fP ∈ s.wr)
    (hws : pR sP ∈ s.wr) :
    WP isa fusedLast s fun s' => VG.Spec.MlDsa.PolyIs s'.mem fP f ∧ BInvY fP s s' := by
  refine WP.seq ?_
  refine WP.mono (Q := fun (w : State) => w.gpr .rax = 0 ∧ GOnly [.rax] s w ∧ w.ymmHi = s.ymmHi)
    (by vrund; exact ⟨by gonlyd, rfl⟩) fun w ⟨hax, og, hy⟩ => ?_
  have cw : YConsts w := ylanes_gpr (s := s) (og.lane hy) (YOnly.refl [] s) hc (by decide) (by decide)
  refine WP.mono (wp_rcxLoopY (N := 16) (by decide) (by decide)
    (fun i u => FI fP sP G (layer (layer (layer G 4) 2) 1) i u ∧ Keep [.rcx, .rax] w u ∧
      Frame [pR fP] w.mem u.mem ∧ u.mxcsr = w.mxcsr)
    (fun u o hu _ => ⟨⟨fun k hk => by
        rw [o.mem, og.mem, ifn (by omega)]; exact polyIs_toNat hS hk,
      by rw [o.keep.gpr (by decide), hax]; rfl,
      by rw [o.keep.gpr (by decide), og.keep.gpr (by decide), hdi],
      by rw [o.keep.gpr (by decide), og.keep.gpr (by decide), hsi],
      by rw [o.mem, og.mem]; exact hT,
      ylanes_gpr (s := w) (o.lane hu) (YOnly.refl [] w) cw (by decide) (by decide),
      by rw [o.keep.2.2, og.keep.2.2]; exact hwf, by rw [o.keep.2.2, og.keep.2.2]; exact hws⟩,
      o.keep.mono (by simp), by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun i hi u ⟨hI, hk, hf, hx⟩ => WP.mono (fstep hd hi (fun k hk => (hr k hk).1) hI)
      fun u' ⟨hI', hk', hf', hx', hcx, hzf⟩ =>
        ⟨⟨hI', (hk.trans hk').mono (by simp), hf.trans hf', hx'.trans hx⟩, hcx, hzf⟩))
    fun u ⟨hI, hk, hf, hx⟩ => ?_
  refine ⟨VG.Proof.MlDsa.Arith.polyIs_of_toNat fun k hk => ?_,
    ⟨(og.keep.trans hk).mono (by simp), by rw [← og.mem]; exact hf, hI.c, hx.trans og.mxcsr⟩⟩
  rw [hI.mem k hk, ifp (by omega), (hr k hk).2]

end VG.Proof.MlDsa.X86_64.Arith.Lazy
