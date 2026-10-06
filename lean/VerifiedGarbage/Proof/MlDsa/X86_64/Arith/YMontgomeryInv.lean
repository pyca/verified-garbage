import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YNtt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.YMontgomery

namespace VG.Proof.MlDsa.X86_64.Arith.MontgomeryInv

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Arith
open VG.Proof.MlDsa.Arith
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok ifp ifn sel GOnly WP.keep writesOnly
  gprPreserved_of withMxcsr_ok mxR add_ofNat_zero wp_rcxLoopY lane_setReg lane_setFlags State.setMem_ymm sx32)
open VG.Impl.MlKem.X86_64 (xb xmov toY rcxLoop yconst)
open VG.Spec.MlDsa (q n Poly Zq coeffAt polyAt PolyIs zetas ntt nttInv)

/-- The coefficients of `G` before `8i` multiplied by `16382`. -/
def YScaled (m : Mem) (fP : Addr) (G : Poly) (i : Nat) : Prop :=
  ∀ k < 256, (coeffAt m fP k).toNat = (if k < 8 * i then G[k]! * 16382 else G[k]!).val

/-- `16382 · 2³² mod q` in each doubleword. -/
theorem scale_lanes : ZLanes (ofDwords 41978#32 41978#32 41978#32 41978#32) (fun _ => 16382) ∧
    ZOdd (ofDwords 41978#32 41978#32 41978#32 41978#32) (ofDwords 41978#32 41978#32 41978#32 41978#32) :=
  ⟨fun i hi => by rcases cases4 hi with rfl | rfl | rfl | rfl <;> decide,
    fun j hj => by rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> decide⟩

theorem montScale_step {fP : Addr} {G : Poly} {i : Nat} (hi : i < 32) {s : State} (hc : YConsts s)
    (hz : ∀ l < 2, ZLanes (s.lane .xmm13 l) (fun _ => 16382))
    (ho : ∀ l < 2, ZOdd (s.lane .xmm13 l) (s.lane .xmm12 l))
    (hdx : s.gpr .rdx = coeffAddr fP (8 * i)) (hS : YScaled s.mem fP G i) (hw : pR fP ∈ s.wr) :
    WP isa (.block sbodyY) s fun s' =>
      YScaled s'.mem fP G (i + 1) ∧ s'.gpr .rdx = coeffAddr fP (8 * (i + 1)) ∧
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
  have hv : ∀ l < 2, ∀ e < 4, (dword (s2.lane .xmm3 l) e).toNat = (G[8 * i + 4 * l + e]! * 16382).val := by
    intro l hl e he
    have hx : DLanes (s1.lane .xmm3 l) (fun e => G[8 * i + 4 * l + e]!) := fun e he => by
      rw [L1 l hl, hdx, add_ofNat_zero, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq,
        hS _ (by omega), ifn (by omega)]
    have hz' : ZLanes (s1.lane .xmm13 l) (fun _ => 16382) := by
      rw [o1.lane _ (by decide) l hl]; exact hz l hl
    have ho' : ZOdd (s1.lane .xmm13 l) (s1.lane .xmm12 l) := by
      rw [o1.lane _ (by decide) l hl, o1.lane _ (by decide) l hl]; exact ho l hl
    have e2 : s2.lane .xmm3 l = _ := V2 l hl
    rw [e2, dword_csubV _ he, mulZ (hx e he) (hz' e he) (dword_montV ho' (prod_lt hx hz') he)]
    dsimp only
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

/-- Multiply every coefficient by `R/256`, retaining the Montgomery scale. -/
theorem montScale_ok {fP sP : Addr} (_hd : (pR sP).Disjoint (pR fP)) {G : Poly} (s : State) (hc : YConsts s)
    (hdi : s.gpr .rdi = fP) (_hsi : s.gpr .rsi = sP) (hS : PolyIs s.mem fP G) (_hT : Tab zmTab s.mem sP 256)
    (hwf : pR fP ∈ s.wr) (_hw : pR sP ∈ s.wr) :
    WP isa montScale s fun s' => PolyIs s'.mem fP (G.map (· * 16382)) ∧ BInvY fP s s' := by
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
    (fun i u => YScaled u.mem fP G i ∧ u.gpr .rdx = coeffAddr fP (8 * i) ∧ YConsts u ∧
      (∀ l < 2, u.lane .xmm13 l = w2.lane .xmm13 l) ∧ (∀ l < 2, u.lane .xmm12 l = w2.lane .xmm12 l) ∧
      Keep [.rcx, .rdx] w2 u ∧ Frame [pR fP] w2.mem u.mem ∧ u.mxcsr = w2.mxcsr)
    (fun u o hu _ => ⟨fun k hk => by
        rw [o.mem, mw2, ifn (by omega)]; exact polyIs_toNat hS (by rw [n_eq]; exact hk),
      by rw [o.keep.gpr (by decide), dx2, Nat.mul_zero, coeffAddr, Nat.mul_zero, add_ofNat_zero],
      ylanes_gpr (s := w2) (o.lane hu) (YOnly.refl [] w2) cw2 (by decide) (by decide),
      fun l _ => o.lane hu _ l, fun l _ => o.lane hu _ l, o.keep.mono (by simp),
      by rw [o.mem]; exact Frame.refl _ _, o.mxcsr⟩)
    (fun i hi u ⟨hS', hdx', hc', hz', hzo', hk', hf', hx'⟩ => WP.mono (montScale_step hi hc'
        (fun l hl => by rw [hz' l hl, z13 l hl]; exact scale_lanes.1)
        (fun l hl => by rw [hz' l hl, hzo' l hl, z13 l hl, z12 l hl]; exact scale_lanes.2) hdx' hS'
        (by rw [hk'.2.2, o2.wr, k1.2.2, og.keep.2.2]; exact hwf))
      fun u' ⟨hS'', hdx'', hf'', hc'', hz'', hzo'', hk'', hcx, hzf, hx''⟩ =>
        ⟨⟨hS'', hdx'', hc'', fun l hl => by rw [hz'' l hl, hz' l hl], fun l hl => by rw [hzo'' l hl, hzo' l hl],
          (hk'.trans hk'').mono (by simp), hf'.trans hf'', by rw [hx'', hx']⟩, hcx, hzf⟩))
    fun u ⟨hS', _, hc', _, _, hk', hf', hx'⟩ => ?_
  have kw2 : Keep [.rdx, .rax] s w2 :=
    ((og.keep.trans k1).trans (⟨fun r _ => by rw [o2.gpr], o2.rd, o2.wr⟩ : Keep [] w1 w2)).mono (by simp)
  refine ⟨polyIs_of_toNat fun k hk => ?_, ⟨(kw2.trans hk').mono (by simp), by rw [← mw2]; exact hf', hc',
    by rw [hx', o2.mxcsr, x1, og.mxcsr]⟩⟩
  rw [n_eq] at hk
  rw [hS' k hk, ifp (by omega), map_mul_get _ _ (by rw [n_eq]; exact hk)]

theorem inv_eq (f : Poly) : Spec.MlDsa.montgomeryNttInv f =
    (nttInvLens.foldl nttInvLayer f).map (· * 16382) := by
  rw [Spec.MlDsa.montgomeryNttInv, nttInv_eq_layers, Vector.map_map]
  apply congrArg (fun g : Spec.MlDsa.Zq → Spec.MlDsa.Zq => (nttInvLens.foldl nttInvLayer f).map g)
  funext x
  change (x * 8347681) * Spec.MlDsa.montgomeryR = x * 16382
  rw [Fin.mul_assoc]
  have hc : (8347681 : Spec.MlDsa.Zq) * Spec.MlDsa.montgomeryR = 16382 := by decide +kernel
  rw [hc]

theorem correct (s : State) (hs : (inPlaceK Spec.MlDsa.montgomeryNttInv).pre s) :
    ∃ t s', Exec isa montNttInvAvx2 s t s' ∧ abiPreserved s s' ∧ (inPlaceK Spec.MlDsa.montgomeryNttInv).post s s' := by
  have hd : (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdi)) := hs.2.2.1.symm
  refine ymx_correct s hs (by decide +kernel) (by decide +kernel) (by decide +kernel) fun s1 k1 f1 =>
    WP.mono (ynttBody_ok hs k1 f1
      (G := (nttInvLens.foldl nttInvLayer (polyAt s.mem (s.gpr .rdi))).map (· * 16382))
      fun s2 hI hdi hsi hwf hw => ?_) fun s' ⟨hP, hf⟩ => ⟨by rw [inv_eq]; exact hP, hf⟩
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]
  refine LIY.seq hdi hsi hwf hw hd (yinvLay1_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay2_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay4_ok hd) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 8 31 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 16 15 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 32 7 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 64 3 (by decide) (by decide)) ?_ hI
  refine fun _ hI => LIY.seq hdi hsi hwf hw hd (yinvLay_ok hd 128 1 (by decide) (by decide)) ?_ hI
  exact fun _ hI => LIY.seq hdi hsi hwf hw hd (montScale_ok hd) (fun _ hI => hI.epi) hI

theorem ct : ConstantTime isa (inPlaceK Spec.MlDsa.montgomeryNttInv).pre
    (inPlaceK Spec.MlDsa.montgomeryNttInv).pub montNttInvAvx2 :=
  VG.Taint.constantTime (A := taint) (X86_64.Taint.ofRegs [.rdi, .rsi, .rsp]) inPlace_agree (by taint_decide)

theorem verified : Verified X86_64.target montNttInvAvx2 (Spec.MlDsa.montgomeryNttInvContract X86_64.abi) :=
  Verified.of_correct correct ct (by
    mldsa_implies [Spec.MlDsa.montgomeryNttInvContract, Spec.MlDsa.inPlaceContract, Spec.MlDsa.inPlaceSig, inPlaceK,
      X86_64.abi, X86_64.argRegs] [inPlaceSat] using inPlaceSat)

end VG.Proof.MlDsa.X86_64.Arith.MontgomeryInv
