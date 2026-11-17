module

public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Prims
import VerifiedGarbage.Proof.MlKem.Arm.Common
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.Arm.Keccak
public import VerifiedGarbage.Proof.MlDsa.Sign.Setup
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
public import VerifiedGarbage.Impl.MlDsa.Arm.Sign.Sign
public import VerifiedGarbage.Proof.MlDsa.Arm.Sign.Top

/-! ### `MlDsa.Arm.Sign.Inv`, which this module and modules that import it used -/

section

/-!
# ML-DSA signing on ARMv7: what holds of the state between the pieces

The inputs of the function entered in `σ` (`skOf`, `muOf`, `rndOf`); what
holds of every state of it (`St`: `Top`, the layout, and the inputs where they
were), kept by each piece that writes only where `stChk` allows (`St.step`);
and polynomials in slots of the working space (`Pl`), in families of
consecutive slots (`Fam`), kept by pieces that write apart from them
(`Fam.keep`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The inputs -/

section
variable (p : Params)

/-- `sk`, `μ` and `rnd`, in the state `σ` the function is entered in. -/
abbrev skOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r0)) p.skLen
abbrev muOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r1)) 64
abbrev rndOf (σ : State) : List Byte := bytesAt σ.mem (State.addr (σ.gpr .r2)) 32

end

/-- The three parameter sets. -/
def Ok3 (p : Params) : Prop := p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87

/-! ## Every state -/

/-- If the kernel was given prepared polynomials (`cache ≠ 0`): they lie apart
from `sig`, `scratch` and the stack, and are where they were. -/
def CK (p : Params) (D : Nat) (σ s : State) : Prop :=
  stackArg σ 1 ≠ 0 →
    (cacheR p σ).Disjoint ⟨State.addr (σ.gpr .r3), p.sigLen⟩ ∧
    (cacheR p σ).Disjoint ⟨State.addr (stackArg σ 0), scrLen p⟩ ∧ (belowA σ.sp D).Disjoint (cacheR p σ) ∧
    cacheLen p ≤ 2 ^ 64 ∧
    bytesAt s.mem (State.addr (stackArg σ 1)) (cacheLen p) = bytesAt σ.mem (State.addr (stackArg σ 1)) (cacheLen p)

/-- What holds of every state of the function entered in `σ`. -/
structure St (p : Params) (D : Nat) (σ s : State) : Prop where
  top : Top σ s
  lay : Lay D (sgR p) (sgW p) s
  sk : bytesAt s.mem (pa s (.r4, 0)) p.skLen = skOf p σ
  mu : bytesAt s.mem (pa s (.r5, 0)) 64 = muOf σ
  rnd : bytesAt s.mem (pa s (.r6, 0)) 32 = rndOf σ
  ck : CK p D σ s

/-- A piece that writes `ws` keeps `St`. -/
def stChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  topChk (sgB p) ws && keepB (sgB p) ws (.r4, 0) p.skLen && keepB (sgB p) ws (.r5, 0) 64 &&
    keepB (sgB p) ws (.r6, 0) 32 && ws.all fun w => inB (sgW p) w.1 w.2

/-- The prepared polynomials lie apart from what the function writes. -/
theorem cacheR_disj {p : Params} {σ s : State} (d1 : (cacheR p σ).Disjoint ⟨State.addr (σ.gpr .r3), p.sigLen⟩)
    (d2 : (cacheR p σ).Disjoint ⟨State.addr (stackArg σ 0), scrLen p⟩) (ht : Top σ s) {q : Ptr} {l : Nat}
    (hw : inB (sgW p) q l = true) : (cacheR p σ).Disjoint ⟨pa s q, l⟩ := by
  obtain ⟨n, hn, hs⟩ := sub_of_inB (s := s) (rbs := []) (wbs := sgW p) (p := q) (l := l) (by simpa using hw)
  simp only [sgW, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, Prod.ext_iff] at hn
  rcases hn with ⟨e1, rfl⟩ | ⟨e1, rfl⟩
  · rw [e1, ht.regs .r7 (by decide)] at hs; exact d2.sub_right hs
  · rw [e1, ht.regs .r8 (by decide)] at hs; exact d1.sub_right hs

theorem CK.step {p : Params} {D : Nat} {σ s s' : State} (h : CK p D σ s) (ht : Top σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hw : ∀ w ∈ ws, inB (sgW p) w.1 w.2 = true) : CK p D σ s' := by
  intro hne
  obtain ⟨d1, d2, d3, hl, hb⟩ := h hne
  refine ⟨d1, d2, d3, hl, ?_⟩
  rw [← hb]
  refine VG.Proof.MlKem.bytesAt_frame hP.frame (fun R hR => ?_) hl
  rcases List.mem_append.mp hR with hR | hR
  · obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hR
    exact cacheR_disj d1 d2 ht (hw w hw')
  · rw [List.mem_singleton] at hR; subst hR; rw [ht.sp]; exact d3.symm

theorem St.step {p : Params} {D : Nat} {σ s s' : State} (h : St p D σ s) {ws : List (Ptr × Nat)}
    (hP : PPostB D s s' ws) (hc : stChk p ws = true) : St p D σ s' := by
  simp only [stChk, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hc
  exact ⟨h.top.step h.lay hP h1, h.lay.post hP (sgB_bases p), (h.lay.keepBytes hP h2).trans h.sk,
    (h.lay.keepBytes hP h3).trans h.mu, (h.lay.keepBytes hP h4).trans h.rnd, h.ck.step h.top hP h5⟩

/-! ## Polynomials in slots -/

/-- Slot `j` holds `f`. -/
abbrev Pl (s : State) (j : Nat) (f : Poly) : Prop := PolyIs s.mem (pa s (pS j)) f

/-- The `m` slots from `b` hold `f 0, …, f (m - 1)`. -/
def Fam (s : State) (b m : Nat) (f : Nat → Poly) : Prop := ∀ j < m, Pl s (b + j) (f j)

/-- The `m` slots from `b` lie apart from `ws`. -/
def famChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) (b m : Nat) : Bool := m == 0 || keepB bs ws (pS b) (1024 * m)

theorem famChk_one {bs : List (Reg × Nat)} {ws : List (Ptr × Nat)} {b m j : Nat} (h : famChk bs ws b m = true) (hj : j < m) :
    keepB bs ws (pS (b + j)) 1024 = true := by
  simp only [famChk, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · exact absurd hj (Nat.not_lt_zero _)
  · refine keepB_sub h ?_ ?_ <;> simp only [oP] <;> omega_arith

theorem Fam.keep {D : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State} (L : Lay D rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB D s s' ws) {b m : Nat} {f : Nat → Poly}
    (hc : famChk (rbs ++ wbs) ws b m = true) (h : Fam s b m f) : Fam s' b m f :=
  fun j hj => L.keepPoly hP (famChk_one hc hj) (h j hj)

end VG.Proof.MlDsa.Arm.Sign

end

end

/-! ### `MlDsa.Arm.Sign.PrimsS`, which only this module used -/

section

/-!
# ML-DSA signing on ARMv7: calls of the samplers

As `Prims.lean`, for `vg_mldsa_rej_ntt_poly`, `vg_mldsa_expand_mask_poly` and
`vg_mldsa_sample_in_ball` (whose fifth argument is on the stack). The results
of `RejNTTPoly` and `SampleInBall` are public in two runs whose seeds agree
(`rejCall_tr`, `ballCall_tr`), and they succeed only if the algorithm finishes
within `maxBounds` (`rejCall_ok`, `ballCall_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlKem.Arm (setWidth_append32 push2_arg)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable {D : Nat} {rbs wbs : List (Reg × Nat)}

/-! ## `RejNTTPoly` -/

/-- What a call of `vg_mldsa_rej_ntt_poly` to `a` needs of the layout. -/
def rejChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  inB wbs a 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oRS) 34 && inB bs a 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oRS) 34 a 1024 && sepB bs (sc oRS) 34 (sc oPS) 2048 && sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ bases)

theorem rejChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : rejChk bs wbs a = true) :
    inB wbs a 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oRS) 34 = true ∧ inB bs a 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oRS) 34 a 1024 = true ∧ sepB bs (sc oRS) 34 (sc oPS) 2048 = true ∧
      sepB bs a 1024 (sc oPS) 2048 = true ∧ ([Arg.ptr (sc oRS), .ptr a, .ptr (sc oPS)].all Arg.ok) = true := by
  simp only [rejChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, by simp [Arg.ok, h9]⟩

theorem rejPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {a : Ptr}
    (hc : rejChk (rbs ++ wbs) wbs a = true) (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oRS)
    (g1 : E.gpr .r1 = s.gpr a.1 + BitVec.ofNat 32 a.2) (g2 : E.gpr .r2 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (hrd : E.rd = [⟨pa s (sc oRS), 34⟩]) (hwr : E.wr = [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]) :
    (rejNTTContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := rejChk_spec hc
  sig_pre [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, En.L.w (p := sc oRS) i1 (by decide), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide)]
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(sc oRS, 34), (a, 1024), (sc oPS, 2048)]) (by simp [i1, i2, i3]),
    En.L.fit (p := sc oRS) i1 (by decide), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide)⟩

/-- The call of `vg_mldsa_rej_ntt_poly`: its outcome, and that it succeeds
only if `RejNTTPoly` finishes within `maxBounds`. -/
theorem rejCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {a : Ptr}
    (hc : rejChk (rbs ++ wbs) wbs a = true) :
    WP isa (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)]) s fun s' =>
      PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ CS s s' ∧
      (s'.gpr .r0 = 1 → Reduced s'.mem (pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)) (s'.gpr .r0)
        (polyAt s'.mem (pa s a)) ∧
      (s'.gpr .r0 = 1 → (rejNTTPoly maxBounds.rejNTT (bytesAt s.mem (pa s (sc oRS)) 34)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rejChk_spec hc
  refine WP.mono (callR_ok (hv_with hP.rejNTT.ver.1 hP.rejMax) (by have := hP.rejNTT.su; have := hP.rejNTT.hS; omega_arith)
    ok L.sp (rd := [⟨pa s (sc oRS), 34⟩]) (wr := [pR (pa s a), ⟨pa s (sc oPS), 2048⟩])
    (fun s1 hA k => rejPre (ent_R L k (by have := hP.rejNTT.hS; omega_using [this]) _ _) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hA).2.2) rfl rfl)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  sig_post [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, Arg.val, k.mem, setWidth_append32,
    L.w (p := sc oRS) i1 (by decide), L.w i2 (by decide)] at hq
  simp only [State.withRegions_gpr, State.withRegions_mem, vR _ _ _ nl0, State.callEntry_mem, e1, Arg.val, k.mem,
    State.addr, L.w (p := sc oRS) i1 (by decide)] at hx
  exact ⟨hq.1, hq.2, hx⟩

theorem rejCall_tr {P : Prims} (hP : PrimsOk P D) {a : Ptr} (hc : rejChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oRS)) 34 = bytesAt y.mem (pa y (sc oRS)) 34)
      (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr a, .ptr (sc oPS)])
      fun x y => x.gpr .r0 = y.gpr .r0 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, ok⟩ := rejChk_spec hc
  have hS : hP.rejNTT.S ≤ D := by have := hP.rejNTT.hS; omega_using [this]
  refine callRRet_tr hP.rejNTT.ver.1 hP.rejRet ok
    fun x y x1 y1 ⟨R, hb⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, rejPre (ent_R R.lx kx hS [⟨pa x (sc oRS), 34⟩] [pR (pa x a), ⟨pa x (sc oPS), 2048⟩]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAx).2.2) rfl rfl,
      rejPre (ent_R R.ly ky hS [⟨pa y (sc oRS), 34⟩] [pR (pa y a), ⟨pa y (sc oPS), 2048⟩]) hc
      (by rw [vR _ _ _ nl0]; exact (argsIn3 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn3 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn3 hAy).2.2) rfl rfl, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2, hx3⟩ := argsIn3 hAx
  obtain ⟨hy1, hy2, hy3⟩ := argsIn3 hAy
  sig_pub [rejNTTContract, rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, kx.mem, ky.mem, hx1, hx2, hx3, hy1, hy2, hy3, Arg.val,
    R.lx.w (p := sc oRS) i1 (by decide), R.ly.w (p := sc oRS) i1 (by decide), hb]
  simp only [R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `ExpandMask` -/

/-- What a call of `vg_mldsa_expand_mask_poly` to `a` needs of the layout. -/
def maskChk (bs wbs : List (Reg × Nat)) (a : Ptr) : Bool :=
  inB wbs a 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oMS) 66 && inB bs a 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oMS) 66 a 1024 && sepB bs (sc oMS) 66 (sc oPS) 2048 && sepB bs a 1024 (sc oPS) 2048 &&
    decide (a.1 ∈ bases)

theorem maskChk_spec {bs wbs : List (Reg × Nat)} {a : Ptr} (hc : maskChk bs wbs a = true) :
    inB wbs a 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oMS) 66 = true ∧ inB bs a 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oMS) 66 a 1024 = true ∧ sepB bs (sc oMS) 66 (sc oPS) 2048 = true ∧
      sepB bs a 1024 (sc oPS) 2048 = true ∧ a.1 ∈ bases := by
  simp only [maskChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem maskPre {S : Nat} {s E : State} (En : Ent D rbs wbs s S E) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChk (rbs ++ wbs) wbs a = true)
    (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oMS) (g1 : E.gpr .r1 = BitVec.ofNat 32 γ)
    (g2 : E.gpr .r2 = s.gpr a.1 + BitVec.ofNat 32 a.2) (g3 : E.gpr .r3 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (hrd : E.rd = [⟨pa s (sc oMS), 66⟩]) (hwr : E.wr = [pR (pa s a), ⟨pa s (sc oPS), 2048⟩]) :
    (expandMaskContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega_arith
  sig_pre [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, En.L.w (p := sc oMS) i1 (by decide), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide), toNat32 hγ']
  exact ⟨wf0 En.wf, hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    En.conj (bs := [(sc oMS, 66), (a, 1024), (sc oPS, 2048)]) (by simp [i1, i2, i3]),
    En.L.fit (p := sc oMS) i1 (by decide), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide), hγ⟩

theorem maskArgs_ok {a : Ptr} {γ : Nat} (b1 : a.1 ∈ bases) :
    [Arg.ptr (sc oMS), .imm γ, .ptr a, .ptr (sc oPS)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem maskAt_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {γ : Nat} {a : Ptr}
    (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) (hc : maskChk (rbs ++ wbs) wbs a = true) :
    WP isa (maskAt P γ a) s fun s' => PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ CS s s' ∧
      PolyIs s'.mem (pa s a) (toRq (bitUnpack (H (bytesAt s.mem (pa s (sc oMS)) 66) (32 * (1 + bitlen (γ - 1))))
        (γ - 1) γ)) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := maskChk_spec hc
  have hγ' : γ < 2 ^ 32 := by omega_arith
  refine WP.mono (callR_ok hP.expandMask.ver.1 (by have := hP.expandMask.su; have := hP.expandMask.hS; omega_arith)
    (maskArgs_ok b1) L.sp (rd := [⟨pa s (sc oMS), 66⟩]) (wr := [pR (pa s a), ⟨pa s (sc oPS), 2048⟩])
    (fun s1 hA k => maskPre (ent_R L k (by have := hP.expandMask.hS; omega_using [this]) _ _) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hA).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hA).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hA).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hA).2.2.2) rfl rfl)
    (Covers.append_left (L.cR i1) (Covers.right (Covers.cons (L.cW w1) (L.cW w2)))) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, hq⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e1, e2, e3, _⟩ := argsIn4 hA
  sig_post [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [e1, e2, e3, Arg.val, k.mem, toNat32 hγ', L.w (p := sc oMS) i1 (by decide), L.w i2 (by decide)] at hq
  exact hq

theorem maskAt_tr {P : Prims} (hP : PrimsOk P D) {γ : Nat} {a : Ptr} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19)
    (hc : maskChk (rbs ++ wbs) wbs a = true) :
    RelCT isa (LRel D rbs wbs) (maskAt P γ a) fun _ _ => True := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := maskChk_spec hc
  have hS : hP.expandMask.S ≤ D := by have := hP.expandMask.hS; omega_using [this]
  refine callR_tr hP.expandMask.ver.1 hP.expandMask.ver.2.1 (maskArgs_ok b1)
    fun x y x1 y1 R ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, maskPre (ent_R R.lx kx hS [⟨pa x (sc oMS), 66⟩] [pR (pa x a), ⟨pa x (sc oPS), 2048⟩]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAx).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAx).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAx).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAx).2.2.2) rfl rfl,
      maskPre (ent_R R.ly ky hS [⟨pa y (sc oMS), 66⟩] [pR (pa y a), ⟨pa y (sc oPS), 2048⟩]) hγ hc
      (by rw [vR _ _ _ nl0]; exact (argsIn4 hAy).1) (by rw [vR _ _ _ nl1]; exact (argsIn4 hAy).2.1)
      (by rw [vR _ _ _ nl2]; exact (argsIn4 hAy).2.2.1) (by rw [vR _ _ _ nl3]; exact (argsIn4 hAy).2.2.2) rfl rfl, ?_,
      by rw [kx.rd, kx.wr]; exact Covers.append_left (R.lx.cR i1) (Covers.right (Covers.cons (R.lx.cW w1) (R.lx.cW w2))),
      by rw [kx.wr]; exact Covers.cons (R.lx.cW w1) (R.lx.cW w2),
      by rw [ky.rd, ky.wr]; exact Covers.append_left (R.ly.cR i1) (Covers.right (Covers.cons (R.ly.cW w1) (R.ly.cW w2))),
      by rw [ky.wr]; exact Covers.cons (R.ly.cW w1) (R.ly.cW w2)⟩
  obtain ⟨hx1, hx2, hx3, hx4⟩ := argsIn4 hAx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := argsIn4 hAy
  sig_pub [expandMaskContract, expandMaskSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [kx.sp, ky.sp, hx1, hx2, hx3, hx4, hy1, hy2, hy3, hy4, Arg.val, R.eq i1, R.eq i2, R.sp, and_self]

/-! ## `SampleInBall` -/

/-- What a call of `vg_mldsa_sample_in_ball` of the `len` bytes at `CT` to `c` needs of the layout. -/
def ballChk (bs wbs : List (Reg × Nat)) (len : Nat) (c : Ptr) : Bool :=
  inB wbs c 1024 && inB wbs (sc oPS) 2048 && inB bs (sc oCT) len && inB bs c 1024 && inB bs (sc oPS) 2048 &&
    sepB bs (sc oCT) len c 1024 && sepB bs (sc oCT) len (sc oPS) 2048 && sepB bs c 1024 (sc oPS) 2048 &&
    decide (c.1 ∈ bases)

theorem ballChk_spec {bs wbs : List (Reg × Nat)} {len : Nat} {c : Ptr} (hc : ballChk bs wbs len c = true) :
    inB wbs c 1024 = true ∧ inB wbs (sc oPS) 2048 = true ∧ inB bs (sc oCT) len = true ∧ inB bs c 1024 = true ∧
      inB bs (sc oPS) 2048 = true ∧ sepB bs (sc oCT) len c 1024 = true ∧ sepB bs (sc oCT) len (sc oPS) 2048 = true ∧
      sepB bs c 1024 (sc oPS) 2048 = true ∧ c.1 ∈ bases := by
  simp only [ballChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem ballArgs_ok {len tau : Nat} {c : Ptr} (b1 : c.1 ∈ bases) :
    [Arg.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)].all Arg.ok = true := by
  simp [Arg.ok, b1]

theorem ballParams_lt {len tau : Nat} (hp : (len, tau) ∈ ballParams) : 0 < len ∧ len < 2 ^ 32 ∧ tau < 2 ^ 32 := by
  simp only [ballParams, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hp; omega_using [hp]

theorem ballPre {S : Nat} (hS : S + 8 ≤ D) {s E : State} (En : Ent D rbs wbs s S E) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true)
    (hsp : E.sp = s.sp - BitVec.ofNat 32 8) (ha : stackArgAddr E 0 = State.addr s.sp - BitVec.ofNat 64 8)
    (hv : stackArg E 0 = s.gpr .r7 + BitVec.ofNat 32 oPS)
    (g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oCT) (g1 : E.gpr .r1 = BitVec.ofNat 32 len)
    (g2 : E.gpr .r2 = BitVec.ofNat 32 tau) (g3 : E.gpr .r3 = s.gpr c.1 + BitVec.ofNat 32 c.2)
    (hrd : E.rd = [⟨pa s (sc oCT), len⟩, argR s]) (hwr : E.wr = [pR (pa s c), ⟨pa s (sc oPS), 2048⟩]) :
    (sampleInBallContract Arm.abi S).pre E := by
  obtain ⟨_, _, i1, i2, i3, d12, d13, d23, _⟩ := ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := ballParams_lt hp
  have h8 : 8 ≤ s.sp.toNat := by have := En.L.sp; omega_using [hS, this]
  have e8 : E.sp.toNat = s.sp.toNat - 8 := by rw [hsp, sp_sub8 h8]
  sig_pre [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [g0, g1, g2, g3, ha, hv, En.L.w (p := sc oCT) i1 (by omega_using [l0]), En.L.w i2 (by decide),
    En.L.w (p := sc oPS) i3 (by decide), toNat32 l1, toNat32 l2]
  have hD : 8 ≤ D := by omega_using [hS]
  refine ⟨wf4 En.wf (by have := s.sp.isLt; omega_using [e8]), hrd, hwr, En.L.disj d12, En.L.disj d13, En.L.disj d23,
    (argR_disj En.L hD i2).symm, (argR_disj (p := sc oPS) En.L hD i3).symm,
    conj_stk [⟨pa s (sc oCT), len⟩, pR (pa s c), ⟨pa s (sc oPS), 2048⟩, argR s] ?_,
    En.L.fit (p := sc oCT) i1 (by omega_using [l0]), En.L.fit i2 (by decide), En.L.fit (p := sc oPS) i3 (by decide), hp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨En.stk _ _ i1, En.stk _ _ i2, En.stk _ _ i3, hsp ▸ argR_stk En.L hS⟩

/-- The regions `SampleInBall` is given. -/
abbrev ballRd (s : State) (len : Nat) : List Region := [⟨pa s (sc oCT), len⟩]
abbrev ballWr (s : State) (c : Ptr) : List Region := [pR (pa s c), ⟨pa s (sc oPS), 2048⟩]

theorem ballPre' {P : Prims} (hP : PrimsOk P D) {s s1 : State} (L : Lay D rbs wbs s) (k : Keep argRegs s s1)
    {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true)
    (hA : ArgsIn [.ptr (sc oCT), .imm len, .imm tau, .ptr c, .ptr (sc oPS)] s s1) :
    (sampleInBallContract Arm.abi hP.ball.S).pre
      ((pushed [.r12, .lr] s1).callEntry.withRegions (ballRd s len ++ [argR s]) (ballWr s c)) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := argsIn5 hA
  have hS := hP.ball.hS
  obtain ⟨ha, hv⟩ := stk_arg L k (by omega_using [hS]) (ballRd s len ++ [argR s]) (ballWr s c)
  exact ballPre hS (ent_S L k hS _ _) hp hc (by rw [State.withRegions_sp, State.callEntry_sp, pushed_sp8, k.sp]) ha
    (by rw [hv, e4]; rfl) (by rw [vS _ _ _ nl0, e0]; rfl) (by rw [vS _ _ _ nl1, e1]; rfl)
    (by rw [vS _ _ _ nl2, e2]; rfl) (by rw [vS _ _ _ nl3, e3]; rfl) rfl rfl

/-- The call of `vg_mldsa_sample_in_ball`: its outcome, and that it succeeds
only if `SampleInBall` finishes within `maxBounds`. -/
theorem ballCall_ok {P : Prims} (hP : PrimsOk P D) {s : State} (L : Lay D rbs wbs s) {len tau : Nat} {c : Ptr}
    (hp : (len, tau) ∈ ballParams) (hc : ballChk (rbs ++ wbs) wbs len c = true) :
    WP isa (ballAt P len tau c) s fun s' =>
      PPostB D s s' [(c, 1024), (sc oPS, 2048)] ∧ CS s s' ∧
      (s'.gpr .r0 = 1 → Reduced s'.mem (pa s c)) ∧
      Outcome (fun b => (sampleInBall tau b.ball (bytesAt s.mem (pa s (sc oCT)) len)).map toRq)
        (s'.gpr .r0) (polyAt s'.mem (pa s c)) ∧
      (s'.gpr .r0 = 1 → (sampleInBall tau maxBounds.ball (bytesAt s.mem (pa s (sc oCT)) len)).isSome) := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := ballParams_lt hp
  refine WP.mono (callS_ok (hv_with hP.ball.ver.1 hP.ballMax) (by have := hP.ball.su; have := hP.ball.hS; omega_arith)
    (ballArgs_ok b1) L.sp (rd := ballRd s len) (wr := ballWr s c)
    (fun s1 hA k => ballPre' hP L k hp hc hA) (L.cR i1) (Covers.cons (L.cW w1) (L.cW w2)))
    fun s' ⟨hpost, hcs, s1, hA, k, s₂, hm₂, hg₂, hq, hx⟩ => ⟨hpost, hcs, ?_⟩
  obtain ⟨e0, e1, e2, e3, _⟩ := argsIn5 hA
  have En := ent_S (S := hP.ball.S) L k hP.ball.hS (ballRd s len ++ [argR s]) (ballWr s c)
  have er : s₂.gpr .r0 = s'.gpr .r0 := hg₂ .r0 (by decide)
  let E := (pushed [.r12, .lr] s1).callEntry.withRegions (ballRd s len ++ [argR s]) (ballWr s c)
  try rewrite [show (pushed [.r12, .lr] s1).callEntry.withRegions (ballRd s len ++ [argR s]) (ballWr s c) = E from rfl] at *
  have hE : E = (pushed [.r12, .lr] s1).callEntry.withRegions (ballRd s len ++ [argR s]) (ballWr s c) := rfl
  have g0 : E.gpr .r0 = s.gpr .r7 + BitVec.ofNat 32 oCT := by rw [hE, vS _ _ _ nl0, e0]; rfl
  have g1 : E.gpr .r1 = BitVec.ofNat 32 len := by rw [hE, vS _ _ _ nl1, e1]; rfl
  have g2 : E.gpr .r2 = BitVec.ofNat 32 tau := by rw [hE, vS _ _ _ nl2, e2]; rfl
  have g3 : E.gpr .r3 = s.gpr c.1 + BitVec.ofNat 32 c.2 := by rw [hE, vS _ _ _ nl3, e3]; rfl
  have eb := En.bytes (p := sc oCT) i1
  clear_value E
  sig_post [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hq
  simp only [g0, g1, g2, g3, er, setWidth_append32, toNat32 l1, toNat32 l2,
    L.w (p := sc oCT) i1 (by omega_using [l0]), L.w i2 (by decide), eb] at hq
  simp only [State.withRegions_gpr, g0, g1, g2, er, toNat32 l1, toNat32 l2, State.addr,
    L.w (p := sc oCT) i1 (by omega_using [l0]), eb] at hx
  -- The polynomial is apart from the released frame.
  obtain hd : ∀ r ∈ [belowA s.sp D], (pR (pa s c)).Disjoint r := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (L.stkD i2).symm
  refine ⟨fun h => reduced_frame hm₂ hd (hq.1 h), ?_, hx⟩
  rw [polyAt_congr (Proof.MlKem.bytes_frame hm₂ hd (by decide))]
  exact hq.2

theorem ballCall_tr {P : Prims} (hP : PrimsOk P D) {len tau : Nat} {c : Ptr} (hp : (len, tau) ∈ ballParams)
    (hc : ballChk (rbs ++ wbs) wbs len c = true) :
    RelCT isa (fun x y => LRel D rbs wbs x y ∧ bytesAt x.mem (pa x (sc oCT)) len = bytesAt y.mem (pa y (sc oCT)) len)
      (ballAt P len tau c) fun x y => x.gpr .r0 = y.gpr .r0 := by
  obtain ⟨w1, w2, i1, i2, i3, _, _, _, b1⟩ := ballChk_spec hc
  obtain ⟨l0, l1, l2⟩ := ballParams_lt hp
  have hS := hP.ball.hS
  refine callSRet_tr hP.ball.ver.1 hP.ballRet (ballArgs_ok b1) (fun x y h => h.1.sp)
    fun x y x1 y1 ⟨R, hb⟩ ⟨hAx, kx⟩ ⟨hAy, ky⟩ =>
    ⟨_, _, _, _, ballPre' hP R.lx kx hp hc hAx, ballPre' hP R.ly ky hp hc hAy, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := argsIn5 hAx
    obtain ⟨hy0, hy1, hy2, hy3, hy4⟩ := argsIn5 hAy
    have Ex := ent_S (S := hP.ball.S) R.lx kx hS (ballRd x len ++ [argR x]) (ballWr x c)
    have Ey := ent_S (S := hP.ball.S) R.ly ky hS (ballRd y len ++ [argR y]) (ballWr y c)
    obtain ⟨-, vx⟩ := stk_arg R.lx kx (by omega_using [hS]) (ballRd x len ++ [argR x]) (ballWr x c)
    obtain ⟨-, vy⟩ := stk_arg R.ly ky (by omega_using [hS]) (ballRd y len ++ [argR y]) (ballWr y c)
    let X := (pushed [.r12, .lr] x1).callEntry.withRegions (ballRd x len ++ [argR x]) (ballWr x c)
    try rewrite [show (pushed [.r12, .lr] x1).callEntry.withRegions (ballRd x len ++ [argR x]) (ballWr x c) = X from rfl] at *
    have hX : X = (pushed [.r12, .lr] x1).callEntry.withRegions (ballRd x len ++ [argR x]) (ballWr x c) := rfl
    let Y := (pushed [.r12, .lr] y1).callEntry.withRegions (ballRd y len ++ [argR y]) (ballWr y c)
    try rewrite [show (pushed [.r12, .lr] y1).callEntry.withRegions (ballRd y len ++ [argR y]) (ballWr y c) = Y from rfl] at *
    have hY : Y = (pushed [.r12, .lr] y1).callEntry.withRegions (ballRd y len ++ [argR y]) (ballWr y c) := rfl
    have gx : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], X.gpr r = x1.gpr r := by
      intro r hr; rw [hX, vS _ _ _ (by revert hr; decide +revert)]
    have gy : ∀ r ∈ [Reg.r0, .r1, .r2, .r3], Y.gpr r = y1.gpr r := by
      intro r hr; rw [hY, vS _ _ _ (by revert hr; decide +revert)]
    have sx : X.sp = x.sp - BitVec.ofNat 32 8 := by rw [hX, State.withRegions_sp, State.callEntry_sp, pushed_sp8, kx.sp]
    have sy : Y.sp = y.sp - BitVec.ofNat 32 8 := by rw [hY, State.withRegions_sp, State.callEntry_sp, pushed_sp8, ky.sp]
    have bx := Ex.bytes (p := sc oCT) i1
    have bY := Ey.bytes (p := sc oCT) i1
    clear_value X Y
    sig_pub [sampleInBallContract, sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    simp only [gx .r0 (by decide), gx .r1 (by decide), gx .r2 (by decide), gx .r3 (by decide),
      gy .r0 (by decide), gy .r1 (by decide), gy .r2 (by decide), gy .r3 (by decide), sx, sy,
      hx0, hx1, hx2, hx3, hy0, hy1, hy2, hy3, vx, vy, hx4, hy4, Arg.val, toNat32 l1]
    rw [R.lx.w (p := sc oCT) i1 (by omega_using [l0]), R.ly.w (p := sc oCT) i1 (by omega_using [l0]), bx, bY, hb]
    simp only [R.eq i1, R.eq i2, R.sp, and_self]
  · exact (cov_S R.lx kx (by omega_using [hS]) (R.lx.cR i1) (Covers.cons (R.lx.cW w1) (R.lx.cW w2))).1
  · exact (cov_S R.lx kx (by omega_using [hS]) (R.lx.cR i1) (Covers.cons (R.lx.cW w1) (R.lx.cW w2))).2
  · exact (cov_S R.ly ky (by omega_using [hS]) (R.ly.cR i1) (Covers.cons (R.ly.cW w1) (R.ly.cW w2))).1
  · exact (cov_S R.ly ky (by omega_using [hS]) (R.ly.cR i1) (Covers.cons (R.ly.cW w1) (R.ly.cW w2))).2

end

end VG.Proof.MlDsa.Arm.Sign

end

end


/-!
# ML-DSA signing on ARMv7: `ExpandA`

`ρ` to `RS`, then entry `e = ℓi + j` of `Â` by `vg_mldsa_rej_ntt_poly` from
the seed `ρ ‖ j ‖ i`, with `r11` the AND of the results (`IA`): if it is 1,
every entry so far is `RejNTTPoly`'s within `maxBounds`; if it is 0, one
entry's `RejNTTPoly` does not finish within `minBounds` (`expandA_ok`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params)

/-- The slot of `Â[0, 0]`; entry `e = ℓi + j` is in slot `aBase + e`. -/
abbrev aBase : Nat := 5 + 4 * p.k + 3 * p.ℓ

/-- `ρ`. -/
abbrev rhoOf (σ : State) : List Byte := (skOf p σ).take 32

/-- The seed of entry `e`. -/
abbrev seedE (σ : State) (e : Nat) : List Byte := aSeed (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

/-- Entry `e` of `Â`, within `maxBounds`. -/
abbrev aVal (σ : State) (e : Nat) : Poly := aF maxBounds.rejNTT (rhoOf p σ) (e / p.ℓ) (e % p.ℓ)

end

theorem aP_eq (p : Params) (e : Nat) : aP p (e / p.ℓ) (e % p.ℓ) = pS (aBase p + e) := by
  show pS (5 + 4 * p.k + 3 * p.ℓ + p.ℓ * (e / p.ℓ) + e % p.ℓ) = pS (5 + 4 * p.k + 3 * p.ℓ + e)
  rw [Nat.add_assoc _ (p.ℓ * _), Nat.div_add_mod]

theorem Fam.snoc {s : State} {b m : Nat} {f : Nat → Poly} (h : Fam s b m f) (h' : Pl s (b + m) (f m)) :
    Fam s b (m + 1) f := fun j hj => by
  rcases (by omega_using [hj] : j < m ∨ j = m) with hj | rfl
  exacts [h j hj, h']

/-- `ExpandA` after `e` entries. -/
structure IA (p : Params) (D : Nat) (σ : State) (e : Nat) (s : State) : Prop where
  st : St p D σ s
  rs : bytesAt s.mem (pa s (sc oRS)) 32 = rhoOf p σ
  r01 : s.gpr .r11 = 0 ∨ s.gpr .r11 = 1
  ok : s.gpr .r11 = 1 → (∀ e' < e, (rejNTTPoly maxBounds.rejNTT (seedE p σ e')).isSome) ∧
    Fam s (aBase p) e (aVal p σ)
  bad : s.gpr .r11 = 0 → ∃ e' < e, rejNTTPoly minBounds.rejNTT (seedE p σ e') = none

/-! ## The seed -/

theorem integerToBytes_one {x : Nat} : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]

theorem seed34 {m : Mem} {a : Addr} {ρ : List Byte} (hρ : bytesAt m a 32 = ρ) {j i : Nat}
    (hj : bytesAt m (a + BitVec.ofNat 64 32) 1 = [BitVec.ofNat 8 j])
    (hi : bytesAt m (a + BitVec.ofNat 64 33) 1 = [BitVec.ofNat 8 i]) :
    bytesAt m a 34 = aSeed ρ i j := by
  rw [VG.Proof.MlKem.bytesAt_add m a 33 1, VG.Proof.MlKem.bytesAt_add m a 32 1, hρ, hj, hi, aSeed,
    integerToBytes_one, integerToBytes_one]

theorem pa_sc_add (s : State) (a b : Nat) : pa s (sc a) + BitVec.ofNat 64 b = pa s (sc (a + b)) :=
  (pa_add s .r7 a b).symm

theorem bytes1_write (m : Mem) (a : Addr) (v : Byte) : bytesAt (m.writeW a v) a 1 = [v] := by
  simp only [bytesAt, List.range_one, List.map_cons, List.map_nil, BitVec.add_zero,
    VG.Proof.MlKem.writeW8_apply, ite_true]

/-! ## An entry -/

/-- What entry `e` needs of the layout. -/
def eChk (p : Params) (e : Nat) : Bool :=
  let a := pS (aBase p + e)
  let w1 : List (Ptr × Nat) := [(sc (oRS + 32), 1)]
  let w2 : List (Ptr × Nat) := [(sc (oRS + 33), 1)]
  let w3 : List (Ptr × Nat) := [(a, 1024), (sc oPS, 2048)]
  stChk p w1 && stChk p w2 && stChk p w3 && stChk p [] && inB (sgW p) (sc (oRS + 32)) 1 &&
    inB (sgW p) (sc (oRS + 33)) 1 && keepB (sgB p) w1 (sc oRS) 32 && keepB (sgB p) w2 (sc oRS) 32 &&
    keepB (sgB p) w3 (sc oRS) 32 && keepB (sgB p) w2 (sc (oRS + 32)) 1 && famChk (sgB p) w1 (aBase p) e &&
    famChk (sgB p) w2 (aBase p) e && famChk (sgB p) w3 (aBase p) e && rejChk (sgB p) (sgW p) a &&
    decide (e % p.ℓ < 256) && decide (e / p.ℓ < 256)

theorem eChk_spec {p : Params} {e : Nat} (h : eChk p e = true) :
    stChk p [(sc (oRS + 32), 1)] = true ∧ stChk p [(sc (oRS + 33), 1)] = true ∧
      stChk p [(pS (aBase p + e), 1024), (sc oPS, 2048)] = true ∧ stChk p [] = true ∧
      inB (sgW p) (sc (oRS + 32)) 1 = true ∧ inB (sgW p) (sc (oRS + 33)) 1 = true ∧
      keepB (sgB p) [(sc (oRS + 32), 1)] (sc oRS) 32 = true ∧ keepB (sgB p) [(sc (oRS + 33), 1)] (sc oRS) 32 = true ∧
      keepB (sgB p) [(pS (aBase p + e), 1024), (sc oPS, 2048)] (sc oRS) 32 = true ∧
      keepB (sgB p) [(sc (oRS + 33), 1)] (sc (oRS + 32)) 1 = true ∧
      famChk (sgB p) [(sc (oRS + 32), 1)] (aBase p) e = true ∧ famChk (sgB p) [(sc (oRS + 33), 1)] (aBase p) e = true ∧
      famChk (sgB p) [(pS (aBase p + e), 1024), (sc oPS, 2048)] (aBase p) e = true ∧
      rejChk (sgB p) (sgW p) (pS (aBase p + e)) = true ∧ e % p.ℓ < 256 ∧ e / p.ℓ < 256 := by
  simp only [eChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- The result of `vg_mldsa_rej_ntt_poly`, if it succeeded within `maxBounds`. -/
theorem rej_val {x : List Byte} {r : BitVec 32} {out : Poly}
    (h : Outcome (fun b => rejNTTPoly b.rejNTT x) r out) (h1 : r = 1)
    (hm : (rejNTTPoly maxBounds.rejNTT x).isSome) : out = (rejNTTPoly maxBounds.rejNTT x).getD zero := by
  rcases h with ⟨_, b, hb⟩ | ⟨h0, _⟩
  · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hm
    have e1 := rejNTTPoly_mono (Nat.le_max_left b.rejNTT maxBounds.rejNTT) hb
    have e2 := rejNTTPoly_mono (Nat.le_max_right b.rejNTT maxBounds.rejNTT) hy
    rw [e1] at e2
    rw [hy, Option.some.inj e2]; rfl
  · rw [h1] at h0; cases h0

theorem outcome01 {α : Type} {f : Bounds → Option α} {r : BitVec 32} {out : α} (h : Outcome f r out) :
    r = 1 ∨ r = 0 := by
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

theorem Fam.of_eq {s s' : State} (hm : s'.mem = s.mem) (hb : s'.gpr .r7 = s.gpr .r7) {b m : Nat}
    {f : Nat → Poly} (h : Fam s b m f) : Fam s' b m f := fun j hj => by
  simp only [Pl, pa, hm, hb]; exact h j hj

/-- The two bytes of the seed of entry `e`. -/
abbrev blkE (p : Params) (e : Nat) : List Instr := setB (sc (oRS + 32)) (e % p.ℓ) ++ setB (sc (oRS + 33)) (e / p.ℓ)

theorem blkE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : eChk p e = true) {s : State}
    (h : IA p D σ e s) : WP isa (.block (blkE p e)) s fun s' =>
      (IA p D σ e s' ∧ bytesAt s'.mem (pa s' (sc oRS)) 34 = seedE p σ e) ∧ s'.gpr .r11 = s.gpr .r11 := by
  obtain ⟨c1, c2, _, _, w1, w2, k1, k2, _, k12, f1, f2, _, _, hj, hi⟩ := eChk_spec he
  have L := h.st.lay
  rw [WP.block_append_iff]
  refine WP.mono (setB_okB L hj (by decide) (by decide) w1) fun s1 ⟨hP1, hcs1, hm1⟩ => ?_
  have S1 := h.st.step hP1 c1
  refine WP.mono (setB_okB S1.lay hi (by decide) (by decide) w2) fun s2 ⟨hP2, hcs2, hm2⟩ => ?_
  have S2 := S1.step hP2 c2
  have e15 : s2.gpr .r11 = s.gpr .r11 := by rw [hcs2 _ (by decide) (by decide), hcs1 _ (by decide) (by decide)]
  have hrs : bytesAt s2.mem (pa s2 (sc oRS)) 32 = rhoOf p σ :=
    (S1.lay.keepBytes hP2 k2).trans ((L.keepBytes hP1 k1).trans h.rs)
  refine ⟨⟨⟨S2, hrs, e15 ▸ h.r01, fun h1 => ?_, fun h0 => h.bad (e15 ▸ h0)⟩, seed34 hrs ?_ ?_⟩, e15⟩
  · obtain ⟨ok, fam⟩ := h.ok (e15 ▸ h1)
    exact ⟨ok, Fam.keep S1.lay hP2 f2 (Fam.keep L hP1 f1 fam)⟩
  · rw [pa_sc_add, S1.lay.keepBytes hP2 k12, hm1, hP1.pa (by decide)]; exact bytes1_write _ _ _
  · rw [pa_sc_add, hm2, hP2.pa (by decide)]; exact bytes1_write _ _ _

/-- What the call of entry `e` leaves. -/
def CallE (D : Nat) (a : Ptr) (x : List Byte) (s s' : State) : Prop :=
  PPostB D s s' [(a, 1024), (sc oPS, 2048)] ∧ CS s s' ∧
    (s'.gpr .r0 = 1 → Reduced s'.mem (pa s a)) ∧
    Outcome (fun b => rejNTTPoly b.rejNTT x) (s'.gpr .r0) (polyAt s'.mem (pa s a)) ∧
    (s'.gpr .r0 = 1 → (rejNTTPoly maxBounds.rejNTT x).isSome)

/-- Entry `e`'s call is done. -/
def JE (p : Params) (D : Nat) (e : Nat) (σ s : State) : Prop :=
  ∃ s₀, IA p D σ e s₀ ∧ CallE D (pS (aBase p + e)) (seedE p σ e) s₀ s

theorem callE_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) (hs : bytesAt s.mem (pa s (sc oRS)) 34 = seedE p σ e) :
    WP isa (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (aBase p + e)), .ptr (sc oPS)]) s
      (JE p D e σ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _, _⟩ := eChk_spec he
  refine WP.mono (rejCall_ok hP h.st.lay hc) fun s' ⟨hP3, hcs3, hred, hout, hmax⟩ => ⟨s, h, hP3, hcs3, hred, ?_, ?_⟩
  · rw [← hs]; exact hout
  · rw [← hs]; exact hmax

theorem andE_ok {D : Nat} {p : Params} {σ : State} {e : Nat} (he : eChk p e = true) {s : State}
    (h : JE p D e σ s) : WP isa (.block [.dp .and .r11 .r11 (.reg .r0)]) s (IA p D σ (e + 1)) := by
  obtain ⟨_, _, c3, c0, _, _, _, _, k3, _, _, _, f3, _, _, _⟩ := eChk_spec he
  obtain ⟨s₀, h, hP3, hcs3, hred, hout, hmax⟩ := h
  have S3 := h.st.step hP3 c3
  refine WP.mono (and11_ok s) fun s4 ⟨h15, k4⟩ => ?_
  have hP4 : PPostB D s s4 [] := (postB11 k4 _).1
  rw [hcs3 _ (by decide) (by decide)] at h15
  have hr := outcome01 hout
  have hb4 : s4.gpr .r7 = s₀.gpr .r7 := by rw [hP4.bs _ (by decide), hP3.bs _ (by decide)]
  refine ⟨S3.step hP4 c0, ?_, ?_, fun h1 => ?_, fun h0 => ?_⟩
  · rw [k4.mem, hP4.pa (by decide), h.st.lay.keepBytes hP3 k3, h.rs]
  · rw [h15]
    rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] <;> decide
  · have hs : s₀.gpr .r11 = 1 ∧ s.gpr .r0 = 1 := by
      rw [h15] at h1
      rcases h.r01 with e0 | e0 <;> rcases hr with e1 | e1 <;> rw [e0, e1] at h1 <;>
        first | exact ⟨e0, e1⟩ | exact absurd h1 (by decide)
    obtain ⟨ok1, fam⟩ := h.ok hs.1
    have hm := hmax hs.2
    refine ⟨fun e' he' => ?_, Fam.snoc ?_ ?_⟩
    · rcases (by omega_using [he'] : e' < e ∨ e' = e) with he' | rfl
      exacts [ok1 e' he', hm]
    · exact Fam.of_eq k4.mem (hP4.bs _ (by decide)) (Fam.keep h.st.lay hP3 f3 fam)
    · show PolyIs s4.mem (pa s4 (pS (aBase p + e))) (aVal p σ e)
      rw [k4.mem, show pa s4 (pS (aBase p + e)) = pa s₀ (pS (aBase p + e)) by simp only [pa, hb4]]
      exact ⟨hred hs.2, rej_val hout hs.2 hm⟩
  · rw [h15] at h0
    rcases h.r01 with e0 | e0
    · obtain ⟨e', he', hn⟩ := h.bad e0
      exact ⟨e', by omega_using [he'], hn⟩
    · rcases hr with e1 | e1
      · rw [e0, e1] at h0; exact absurd h0 (by decide)
      · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
        · rw [e1] at h1; cases h1
        · exact ⟨e, by omega_using [], hn⟩

theorem sampleE_eq (P : Prims) (p : Params) (e : Nat) : sampleE P p e = .seq (.block (blkE p e))
    (.seq (callR "vg_mldsa_rej_ntt_poly" P.rejNTT [.ptr (sc oRS), .ptr (pS (aBase p + e)), .ptr (sc oPS)])
      (.block [.dp .and .r11 .r11 (.reg .r0)])) := by
  unfold sampleE rejAt; rw [aP_eq]

theorem sampleE_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} {σ : State} {e : Nat}
    (he : eChk p e = true) {s : State} (h : IA p D σ e s) : WP isa (sampleE P p e) s (IA p D σ (e + 1)) := by
  rw [sampleE_eq]
  exact WP.seq (WP.mono (blkE_ok he h) fun s1 ⟨⟨h1, hs1⟩, _⟩ =>
    WP.seq (WP.mono (callE_ok hP he h1 hs1) fun s2 h2 => andE_ok he h2))

/-! ## The matrix -/

/-- What `ExpandA` needs of the layout. -/
def aChk (p : Params) : Bool :=
  (List.range (p.k * p.ℓ)).all (eChk p) && copyChk (sgB p) (sgW p) (sc oRS) (.r4, 0) 32 &&
    stChk p [(sc oRS, 32)] && decide (32 ≤ p.skLen)

theorem aChk_ok {p : Params} (h : Ok3 p) : aChk p = true := by
  rcases h with rfl | rfl | rfl <;> decide +kernel

theorem expandA_ok {P : Prims} {D : Nat} (hP : PrimsOk P D) {p : Params} (hc : aChk p = true) {σ s : State}
    (hs : St p D σ s) (h15 : s.gpr .r11 = 1) : WP isa (Impl.MlDsa.Arm.Sign.expandA P p) s (IA p D σ (p.k * p.ℓ)) := by
  simp only [aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨he, hcp⟩, hst⟩, hsk⟩ := hc
  unfold Impl.MlDsa.Arm.Sign.expandA
  refine WP.seq (WP.mono (copy_okB hs.lay hcp) fun s1 ⟨hP1, hcs1, hb⟩ => ?_)
  have S1 := hs.step hP1 hst
  have e15 : s1.gpr .r11 = 1 := by rw [hcs1 _ (by decide) (by decide), h15]
  have I0 : IA p D σ 0 s1 := ⟨S1, by rw [hP1.pa (by decide), hb, rhoOf, ← hs.sk, VG.Proof.MlKem.bytesAt_take _ _ hsk],
    .inr e15, fun _ => ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩,
    fun h0 => absurd (h0.symm.trans e15) (by decide)⟩
  have := seqR_ok (f := sampleE P p) (I := IA p D σ) (p.k * p.ℓ) 0
    (fun k _ hk s h => sampleE_ok hP (he k (by omega_using [hk])) h) s1 I0
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.Arm.Sign
