module

public import VerifiedGarbage.Proof.MlKem.Arm.Ntt
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlKem.Arm.Ntt
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_inv_ntt`

As `vg_mlkem_ntt` (`Ntt.lean`), with the zetas from the last and the inverse
butterflies, which store the words `opI` gives (`ibfly_run`, `ibfly_core`):
the first six layers keep words less than `2q` congruent to those of
`NTT⁻¹` (`layersI_rel`). The last layer's one block is the loop over groups
of four of `ibflyS` (`grpLoop_ok` with `ibflyS_core`), with 3303 and the
layer's zeta times it in registers (`scalePre_ok`): it leaves the last
layer's coefficients times 3303 (`lastInv_val`), which `nttInv_split` says
is `NTT⁻¹`.
-/

@[expose] public section

namespace VG.Proof.MlKem.Arm.NttInv

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Proof.MlKem.Arm.Ntt

/-! ## The inverse butterflies -/

section
variable {s : State} {x z zp : BitVec 32} {len o : Nat} (ho : 4 * (o + len) < 4096) (h0 : s.gpr .r0 = x)
  (h7 : s.gpr .r7 = z) (h8 : s.gpr .r8 = Nq) (h9 : s.gpr .r9 = zp) (h12 : s.gpr .r12 = 3329)
  (iA : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (iB : InRegions (s.rd ++ s.wr) (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
  (oA : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * o))) 4)
  (oB : InRegions s.wr (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 4)
include ho h0 h7 h8 h9 h12 iA iB oA oB

theorem ibfly_run :
    WP isa (.block (ibfly len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (bpr (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32))).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32 + 6658 -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32) z zp) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  run_block [ibfly, mulz, bmz, bpr, h0, h7, h8, h9, h12, iA, iB, oA, oB, ho, ho', q_shl1]
  keep_regs

theorem ibflyS_run {f fp : BitVec 32} (h10 : s.gpr .r10 = f) (h11 : s.gpr .r11 = fp) :
    WP isa (.block (ibflyS len o)) s fun s' =>
      s'.mem = (s.mem.writeW (State.addr (x + BitVec.ofNat 32 (4 * o)))
          (cs (bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32 +
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32) f fp))).writeW
        (State.addr (x + BitVec.ofNat 32 (4 * (o + len))))
          (cs (bmz (s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * (o + len)))) 32 + 6658 -
            s.mem.readW (State.addr (x + BitVec.ofNat 32 (4 * o))) 32) z zp)) ∧
      Keep coreKeep s s' := by
  have ho' : 4 * o < 4096 := by omega_using [ho]
  run_block [ibflyS, mulz, csub, bmz, cs, h0, h7, h8, h9, h10, h11, h12, iA, iB, oA, oB, ho, ho', q_shl1]
  keep_regs

end

theorem ibfly_core (c : BitVec 32) : CoreOk ibfly opI (ZetaIn c) := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨z8, z12, z7, z9, _⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (ibfly_run (len := len) (o := o) (by omega_using [hl', ho]) h0 z7 z8 z9 z12
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj)) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, lp_word hG hjn, lp_word hG hjl]
    exact lp_bflyInv hG opI hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)

/-- The registers of the last layer: `ZetaIn` of the zeta times 3303, with
3303 in `r10`, and its quotient in `r11`. -/
def ScaleIn (z : Zq) (s : State) : Prop :=
  ZetaIn (BitVec.ofNat 32 cInv.val) (z * cInv) s ∧ s.gpr .r11 = BitVec.ofNat 32 (zetaQuot cInv.val)

theorem ScaleIn.keep {z : Zq} {s s' : State} (hk : Keep bflyKeep s s') (h : ScaleIn z s) : ScaleIn z s' :=
  ⟨h.1.keep hk, (hk.gpr .r11 (by decide)).trans h.2⟩

theorem ibflyS_core : CoreOk ibflyS opIS ScaleIn := by
  intro p len j o hl hl' ho hj hp z G s h0 ⟨⟨z8, z12, z7, z9, z10⟩, z11⟩ hG hw
  have eA := addr_at hp (j := j) (k := o) (by omega_using [hj])
  have eB := addr_at hp (j := j) (k := o + len) (by omega_using [hj])
  have hjo : j + o < 256 := by omega_using [hj]
  have hjn : j + o < n := by rw [n_eq]; exact hjo
  have hjl : j + o + len < n := by rw [n_eq]; exact hj
  rw [← Nat.add_assoc] at eB
  refine WP.mono (ibflyS_run (len := len) (o := o) (by omega_using [hl', ho]) h0 z7 z8 z9 z12
    (by rw [eA]; exact rd_at hw hjo) (by rw [eB]; exact rd_at hw hj)
    (by rw [eA]; exact wr_at hw hjo) (by rw [eB]; exact wr_at hw hj) z10 z11) fun s' ⟨hm, hk⟩ => ⟨?_, ?_, hk⟩
  · rw [hm, eA, eB, lp_word hG hjn, lp_word hG hjl]
    exact lp_bflyInv hG opIS hl hjl z (toW_val _).symm (toW_val _).symm
  · rw [hm, eA, eB]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hjn)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ hjl)

/-! ## The layers -/

/-- The chain of zeta indices of the layers `ls` of `NTT⁻¹`, from `k`. -/
def ChainInv : Nat → List Nat → Prop
  | _, [] => True
  | k, len :: ls => k = 256 / len - 1 ∧ ChainInv (128 / len - 1) ls

/-- The zeta index after the layers `ls`, from `k`. -/
def chainEndInv : Nat → List Nat → Nat
  | k, [] => k
  | _, len :: ls => chainEndInv (128 / len - 1) ls

theorem lens_inv : ∀ len ∈ [2, 4, 8, 16, 32, 64, 128], 128 / len ≤ 256 / len - 1 ∧ 256 / len ≤ 128 ∧
    256 / len - 1 - 128 / len = 128 / len - 1 := by decide

/-- A layer of `NTT⁻¹` whose blocks are `blk`. -/
theorem layInv_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {c : BitVec 32} {blk : Prog isa}
    {len : Nat} (hlen : len ∈ [2, 4, 8, 16, 32, 64, 128])
    (hblk : BlockOk blk opI .sub c len (pf s₀) (ps s₀)) {G : WPoly} {s : State}
    (hI : LI s₀ m₁ c G (256 / len - 1) s) :
    WP isa (nttLay blk len) s fun s' => LI s₀ m₁ c (layerI G len) (128 / len - 1) s' := by
  obtain ⟨h1, h2, h3⟩ := lens_inv len hlen
  refine WP.mono (layI_ok hp hm hblk hlen (fun b => 256 / len - 1 - b) (fun b hb => by omega_using [h2])
    (fun b hb => by
      simp only [nextZ, reduceCtorEq, ite_false]
      rw [show 4 * (256 / len - 1 - b) = 4 * (256 / len - 1 - (b + 1)) + 4 by omega_using [h1, hb],
        BitVec.ofNat_add, ← BitVec.add_assoc]
      exact BitVec.add_sub_cancel _ _) hI) fun s' hI' => ?_
  rw [h3] at hI'
  exact hI'

theorem lays_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {c : BitVec 32} (blk : Nat → Prog isa) :
    ∀ (ls : List Nat) (G : WPoly) (k : Nat) (s : State),
      (∀ len ∈ ls, len ∈ [2, 4, 8, 16, 32, 64, 128] ∧ BlockOk (blk len) opI .sub c len (pf s₀) (ps s₀)) →
      ChainInv k ls → LI s₀ m₁ c G k s →
      WP isa (lays blk ls) s fun s' => LI s₀ m₁ c (ls.foldl layerI G) (chainEndInv k ls) s'
  | [], _, _, _, _, _, hI => WP.block_nil hI
  | len :: ls, G, k, s, hls, ⟨hk, hc⟩, hI => by
    obtain ⟨hlen, hblk⟩ := hls len (List.mem_cons_self ..)
    exact WP.seq (WP.mono (layInv_ok hp hm hlen hblk (hk ▸ hI)) fun s' hI' =>
      lays_ok hp hm blk ls _ (128 / len - 1) s' (fun l hl => hls l (List.mem_cons_of_mem _ hl)) hc hI')

/-- `NTT⁻¹`, as the code's runs of layers and its last layer. -/
theorem nttInv_split (f : Poly) : Spec.MlKem.nttInv f =
    (nttInvLayer ([8, 16, 32, 64].foldl nttInvLayer ([2, 4].foldl nttInvLayer f)) 128).map (· * 3303) := by
  rw [nttInv_eq_layers]
  simp only [nttInvLens, List.foldl_cons, List.foldl_nil]

/-! ## The last layer -/

theorem scaleZeta_eq : scaleZeta = (zeta 1 * cInv).val := by
  have h : zetaTable.getD 1 0 = (zeta 1).val := by rw [zetaTable_eq]; exact zetas_getD (by decide)
  rw [Fin.val_mul, ← h]
  rfl

theorem scaleZeta_word : (BitVec.ofNat 16 scaleZeta).setWidth 32 = BitVec.ofNat 32 (zeta 1 * cInv).val := by
  rw [movw_val (by rw [scaleZeta_eq]; exact Nat.lt_trans (val_lt _) (by decide)), scaleZeta_eq]

theorem scaleQuot_word :
    (BitVec.ofNat 16 (zetaQuot scaleZeta)).setWidth 32 = BitVec.ofNat 32 (zetaQuot (zeta 1 * cInv).val) := by
  rw [movw_val (by rw [scaleZeta_eq]; exact zetaQuot_lt (zeta 1 * cInv).isLt), scaleZeta_eq]

/-- The constants of the last layer, and the count of its groups. -/
theorem scalePre_ok {s : State} (h8 : s.gpr .r8 = Nq) (h12 : s.gpr .r12 = 3329) :
    WP isa (.block scalePre) s fun s' =>
      ScaleIn (zeta 1) s' ∧ s'.gpr .r3 = BitVec.ofNat 32 (1 * (32 - 0)) ∧ s'.mem = s.mem ∧
        Keep [.r0, .r1, .lr] s s' := by
  run_block [scalePre, ScaleIn, ZetaIn, h8, h12, scaleZeta_word, scaleQuot_word]
  keep_regs

/-! ## Setup and the end -/

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block (saveRegs .r1 512 ++ tableZ zetaTable .r1 ++ constsN ++
      ([.dp .add .r1 .r1 (.imm 508)] : List Instr)))
      s₀ fun s => Setup s₀ s.mem ∧ LI s₀ s.mem (s₀.gpr .r10) (lift (P s₀)) 127 s := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (setup_base hp) fun s₂ ⟨hm, e, rd, wr, sp⟩ => ?_
  have e0 := e .r0 (by decide)
  have e1 := e .r1 (by decide)
  have e10 := e .r10 (by decide)
  have elr := e .lr (by decide)
  run_block [constsN, e0, e1, e10, elr, rd, wr, sp, constsN_val, hm, true_and]
  exact ⟨by simp [e0], by simp, by simp, by simp, by simp [e10], lp_lift hm.poly, Frame.refl _ _,
    ⟨fun r hr => by rw [List.mem_singleton] at hr; subst hr; simp [elr], rfl, rfl, rfl⟩⟩

/-- The registers restored, from a state that kept the working space. -/
theorem restore_ok {s₀ : State} (hp : Pre s₀) {m₁ : Mem} (hm : Setup s₀ m₁) {s : State}
    (h1 : s.gpr .r1 = ps s₀ + BitVec.ofNat 32 4) (hlr : s.gpr .lr = s₀.gpr .lr)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) (hf : Frame [polyRegion (F s₀)] m₁ s.mem)
    {f : Poly} (hP : PolyIs s.mem (F s₀) f) :
    WP isa (.block (restoreRegs .r1 508)) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧
      s'.sp = s₀.sp ∧ PolyIs s'.mem (F s₀) f := by
  have fS := hp.fitS
  have hS : (S s₀).toNat + 1024 ≤ 2 ^ 64 := addr_fit _ (by decide)
  have e1 : State.addr (s.gpr .r1) + BitVec.ofNat 64 508 = S s₀ + BitVec.ofNat 64 512 := by
    rw [h1, addr_add (by omega_arith), add_ofNat_add]
  refine WP.mono (restoreRegs_ok .r1 (by decide) (off := 508) (by decide) (by rw [h1]; bv_omega)
    (g := s₀.gpr) (by
      rw [e1]
      intro i hi
      rw [hf.readW (r := ⟨S s₀ + BitVec.ofNat 64 512 + BitVec.ofNat 64 (4 * i), 4⟩)
        (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
      · exact hm.sav i hi
      · rw [List.mem_singleton] at hr; subst hr
        refine hp.disj.symm.sub_left ?_
        rw [add_ofNat_add]
        exact region_sub_off (by omega_arith))
    fun i hi => by
      rw [e1, hrd, hwr, hp.wr, add_ofNat_add]
      exact inRegions_of (R := polyRegion (S s₀)) (by simp) (contains_off (by omega_arith) (by omega_arith)))
    fun s' h' => ⟨preserved_of_restore h' hlr, h'.sp.trans hsp, ?_⟩
  rw [h'.mem]
  exact hP

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa nttInv s₀ fun s => (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧
      PolyIs s.mem (F s₀) (Spec.MlKem.nttInv (P s₀)) := by
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨hm, hI⟩ => ?_)
  refine WP.seq (WP.mono (lays_ok hp hm (fun len => nttBlkS (ibfly len) len .sub)
    [2, 4] _ 127 s₁ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI) fun s₂ hI₂ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;>
      exact ⟨by decide, blkS_ok (ibfly_core _) hp.fitF hp.fitS (by decide) .sub (.inr rfl) (by decide)⟩
  refine WP.seq (WP.mono (lays_ok hp hm (fun len => nttBlkL (ibfly len) len .sub)
    [8, 16, 32, 64] _ 31 s₂ (fun len hl => ?_) (by simp only [ChainInv]; decide) hI₂) fun s₃ hI₃ => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, blkL_ok (ibfly_core _) hp.fitF hp.fitS (by decide) .sub (.inr rfl) (by decide)
        (by decide)⟩
  refine WP.seq (WP.mono (scalePre_ok hI₃.r8 hI₃.r12) fun s₄ ⟨hz, e3, m₄, k₄⟩ => ?_)
  have hG := hI₃.poly
  rw [← m₄] at hG
  refine WP.seq (WP.mono (grpLoop_ok ibflyS_core (fun _ _ _ hk h => h.keep hk) hp.fitF (len := 128) (start := 0)
    (N := 32) (by decide) (by decide) (by decide) (by decide) (by decide) 1 _ s₄
    (by rw [k₄.gpr .r0 (by decide), hI₃.r0]; simp) hz hG
    (by rw [k₄.wr, hI₃.keep.wr, hp.wr]; simp) e3) fun s₅ ⟨hP, hf, _, k₅⟩ => ?_)
  refine restore_ok hp hm ((k₅.gpr .r1 (by decide)).trans ((k₄.gpr .r1 (by decide)).trans hI₃.r1))
    ((k₅.gpr .lr (by decide)).trans ((k₄.gpr .lr (by decide)).trans (hI₃.keep.gpr .lr (by decide))))
    (k₅.rd.trans (k₄.rd.trans hI₃.keep.rd)) (k₅.wr.trans (k₄.wr.trans hI₃.keep.wr))
    (k₅.sp.trans (k₄.sp.trans hI₃.keep.sp)) (hI₃.frame.trans (m₄ ▸ hf)) ?_
  have h2 : Rel 2 _ _ := layersI_rel [2, 4] _ _ (by decide) ((lift_rel (P s₀)).mono (by decide))
  have hr : Rel 2 _ _ := layersI_rel [8, 16, 32, 64] _ _ (by decide) h2
  rw [nttInv_split]
  refine polyIs_of_toNat fun j hj => ?_
  rw [hP j hj]
  exact lastInv_val hr (by rw [n_eq] at hj; exact hj)

end VG.Proof.MlKem.Arm.NttInv
