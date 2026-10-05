import VerifiedGarbage.Proof.MlDsa.X86_64.Round.YBits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Round.YNorm`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_norm_lt_avx2`

With the bound clamped to `b ≤ q` (which changes no result, `good_clamp`),
each doubleword of `ymm10` keeps its top bit while every coefficient it has
seen is good (`Good b a`: `a < b` or `q - a < b`, `nlL_msb`); at the end the
top bits of the 32 bytes are all set exactly when every coefficient is good
(`bsum_allOnes`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes ifp ifn)
open VG.Impl.MlKem.X86_64 (xb xmov toY)
open VG.Proof.MlDsa.X86_64.Arith (dword_psubd dword_pand dword_psrad)
open VG.Proof.MlKem.X86_64.S4 (bsum bsum_lt byteMask_eq)
open VG.Proof.MlDsa.X86_64.Arith (bc)

/-! ## A doubleword -/

/-- The top bit of a difference of doublewords below `2³¹`: whether it borrows. -/
theorem msb_sub32 {u v : BitVec 32} (hu : u.toNat < 2 ^ 31) (hv : v.toNat < 2 ^ 31) :
    (u - v).msb = decide (u.toNat < v.toNat) := by
  rw [BitVec.msb_eq_decide, BitVec.toNat_sub]
  by_cases h : u.toNat < v.toNat
  · rw [decide_eq_true h, decide_eq_true_iff]; omega
  · rw [decide_eq_false h, decide_eq_false_iff_not]; omega

/-- What `nlX` ORs into a doubleword: `(a - b) | ((q - b) - a)`. -/
def nlL (a b c : BitVec 32) : BitVec 32 := (a - b) ||| (c - a)

theorem nlL_msb {a b : BitVec 32} (ha : a.toNat < q) (hb : b.toNat ≤ q) :
    (VG.Proof.MlDsa.X86_64.Round.nlL a b (BitVec.ofNat 32 (q - b.toNat))).msb = decide (Good b.toNat a.toNat) := by
  rw [q_eq] at ha hb
  have hc : (BitVec.ofNat 32 (q - b.toNat)).toNat = q - b.toNat := by rw [BitVec.toNat_ofNat, q_eq]; omega
  rw [VG.Proof.MlDsa.X86_64.Round.nlL, BitVec.msb_or, VG.Proof.MlDsa.X86_64.Round.msb_sub32 (by omega) (by omega), VG.Proof.MlDsa.X86_64.Round.msb_sub32 (by rw [hc, q_eq]; omega) (by omega), hc]
  simp only [Good, Bool.decide_or, q_eq]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_iff]
  omega

/-- Clamping the bound to `q` changes no coefficient's goodness. -/
theorem good_clamp {B a : Nat} (ha : a < q) : Good (min B q) a ↔ Good B a := by
  simp only [Good]
  constructor
  · rintro (h | h) <;> [left; right] <;> omega
  · intro h
    by_cases hB : B ≤ q
    · rw [Nat.min_eq_left hB]; exact h
    · rw [Nat.min_eq_right (by omega)]; left; exact ha

/-! ## The mask -/

theorem bsum_allOnes (f : Nat → Bool) : ∀ n, bsum f n = 2 ^ n - 1 ↔ ∀ i < n, f i = true
  | 0 => by simp [bsum]
  | n + 1 => by
    have hl := bsum_lt f n
    have ih := VG.Proof.MlDsa.X86_64.Round.bsum_allOnes f n
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [bsum, Nat.pow_succ]
    generalize 2 ^ n = N at hl ih h1 ⊢
    constructor
    · intro h i hi
      have hfn : f n = true := by
        cases e : f n
        · simp only [e, Bool.toNat_false, Nat.zero_mul, Nat.add_zero] at h; omega
        · rfl
      rw [hfn] at h
      simp only [Bool.toNat_true, Nat.one_mul] at h
      rcases (by omega : i < n ∨ i = n) with hi | rfl
      · exact (ih.mp (by omega)) i hi
      · exact hfn
    · intro h
      rw [ih.mpr fun i hi => h i (by omega), h n (by omega)]
      simp only [Bool.toNat_true, Nat.one_mul]
      omega

/-- A bit of a 256-bit register, in its lanes and doublewords. -/
theorem ymm_bit (s : State) (r : XReg) {i : Nat} (hi : i < 32) :
    (s.ymm r).getLsbD (8 * i + 7) = (dword (s.lane r (i / 16)) (i % 16 / 4)).getLsbD (8 * (i % 4) + 7) := by
  simp only [State.ymm, State.lane, dword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
    show 8 * (i % 4) + 7 < 32 by omega, decide_true, Bool.true_and]
  by_cases h : i < 16
  · rw [ite_eq_left (show 8 * i + 7 < 128 by omega), ite_eq_left (show i / 16 = 0 by omega),
      show 32 * (i % 16 / 4) + (8 * (i % 4) + 7) = 8 * i + 7 by omega]
  · rw [ite_eq_right (show ¬ 8 * i + 7 < 128 by omega), ite_eq_right (show ¬ i / 16 = 0 by omega),
      show 32 * (i % 16 / 4) + (8 * (i % 4) + 7) = 8 * i + 7 - 128 by omega]

/-- A doubleword spread from its top bit. -/
theorem bit_of_spread {d : BitVec 32} (h : d = 0 ∨ d = BitVec.allOnes 32) {j : Nat} (hj : j < 32) :
    d.getLsbD j = d.msb := by
  rcases h with rfl | rfl
  · simp
  · rw [BitVec.msb_allOnes (by decide), BitVec.getLsbD_allOnes]; simp [hj]

/-! ## The code on a register -/

theorem nlX_ok (s : State) :
    WP isa (.block nlX) s fun s' => (∀ e < 4, dword (s'.xmm .xmm10) e =
      dword (s.xmm .xmm10) e &&& VG.Proof.MlDsa.X86_64.Round.nlL (dword (s.xmm .xmm0) e) (dword (s.xmm .xmm8) e) (dword (s.xmm .xmm9) e)) ∧
      XOnly [.xmm1, .xmm2, .xmm10] s s' := by
  simp only [nlX, xmov, xb]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨fun e he => ?_, by xonly⟩
  simp only [dword_pand, dword_por, dword_psubd _ _ he]
  rfl

theorem lane_nlX : laneSseBlock (toY nlX) = some nlX := by decide +kernel

/-- `rax`'s low doubleword in each doubleword of `ymm r`. -/
theorem ybc_ok (r : XReg) (s : State) :
    WP isa (.block (ybcast r)) s fun s' =>
      (∀ l < 2, s'.lane r l = bc ((s.gpr .rax).setWidth 32)) ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr ∧ ∀ r' ≠ r, ∀ l < 2, s'.lane r' l = s.lane r' l := by
  apply WP.of_runBlock
  simp only [ybcast, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, Option.some.injEq,
    exists_eq_left']
  refine ⟨fun l hl => ?_, rfl, rfl, rfl, rfl, rfl, fun r' hr' l hl => ?_⟩
  · rw [State.lane_setV256, ifp rfl]
    have : dword ((s.setV .l128 r ((0 : BitVec 64) ++ s.gpr .rax) 0).xmm r) 0 = (s.gpr .rax).setWidth 32 := by
      rw [RegUpd.xmm_setV, ifp rfl]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp only [dword, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
      rw [BitVec.getLsbD_append, ifp (by omega), BitVec.getLsbD_setWidth]
      simp [show i < 64 by omega, hi]
    rcases lane01 hl with rfl | rfl <;> simp only [ite_true, ite_false, this, Nat.one_ne_zero] <;> rfl
  · rw [State.lane_setV256, ifn hr', State.lane_setV128, ifn hr']

end VG.Proof.MlDsa.X86_64.Round

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Round (Good nlL nlL_msb nlX_ok lane_nlX bc_ofDwords)
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok ifp ifn ptr_step add_ofNat_zero lane_setReg lane_setFlags)
open VG.Spec.MlDsa (q n coeffAt Reduced)

namespace YNormL

/-- After `i` vectors of eight: the top bit of doubleword `e` of lane `l` of
`ymm10` is whether coefficients `8j + 4l + e`, `j < i`, are good. -/
structure Inv (s₀ : State) (b : BitVec 32) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = s₀.mem
  c8 : ∀ l < 2, s.lane .xmm8 l = bc b
  c9 : ∀ l < 2, s.lane .xmm9 l = bc (BitVec.ofNat 32 (q - b.toNat))
  acc : ∀ l < 2, ∀ e < 4, (dword (s.lane .xmm10 l) e).msb = true ↔
    ∀ j < i, Good b.toNat (coeffAt s₀.mem (s₀.gpr .rdi) (8 * j + 4 * l + e)).toNat

theorem step {s₀ : State} (hrd : pR (s₀.gpr .rdi) ∈ s₀.rd) (hr : Reduced s₀.mem (s₀.gpr .rdi)) {b : BitVec 32}
    (hb : b.toNat ≤ q) {i : Nat} (hi : i < 32) {s : State} (hI : VG.Proof.MlDsa.X86_64.Arith.YNormL.Inv s₀ b i s) :
    WP isa (.block (nlBodyY ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      VG.Proof.MlDsa.X86_64.Arith.YNormL.Inv s₀ b (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hr' : pR (s₀.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hI.rd]; exact List.mem_append_left _ hrd
  have e1 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  rw [nlBodyY, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 hr' j0)) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ylanes VG.Proof.MlDsa.X86_64.Round.lane_nlX (P := fun l t => ∀ e < 4, dword (t.xmm .xmm10) e =
      dword ((s1.proj l).xmm .xmm10) e &&& VG.Proof.MlDsa.X86_64.Round.nlL (dword ((s1.proj l).xmm .xmm0) e) (dword ((s1.proj l).xmm .xmm8) e)
        (dword ((s1.proj l).xmm .xmm9) e)) fun l hl => VG.Proof.MlDsa.X86_64.Round.nlX_ok _) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := o1.trans o3
  vrund
  refine ⟨⟨?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_, fun l hl e he => ?_⟩, ?_⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [o13.gpr, hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [o13.wr, hI.wr]
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]; rw [o13.mem, hI.mem]
  · simp only [lane_setReg, lane_setFlags]; rw [o13.lane _ (by decide) l hl, hI.c8 l hl]
  · simp only [lane_setReg, lane_setFlags]; rw [o13.lane _ (by decide) l hl, hI.c9 l hl]
  · simp only [lane_setReg, lane_setFlags]
    have hx : dword ((s1.proj l).xmm .xmm0) e = coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e) := by
      rw [State.proj_xmm, L1 l hl, e1, dword_readW _ _ he, lane_load, coeffAddr_add, ← coeffAt_eq, hI.mem]
    have h8 : dword ((s1.proj l).xmm .xmm8) e = b := by
      rw [State.proj_xmm, o1.lane _ (by decide) l hl, hI.c8 l hl]; exact bc_ofDwords _ e he
    have h9 : dword ((s1.proj l).xmm .xmm9) e = BitVec.ofNat 32 (q - b.toNat) := by
      rw [State.proj_xmm, o1.lane _ (by decide) l hl, hI.c9 l hl]; exact bc_ofDwords _ e he
    have h10 : (s1.proj l).xmm .xmm10 = s.lane .xmm10 l := by rw [State.proj_xmm, o1.lane _ (by decide) l hl]
    rw [← State.proj_xmm, B3 l hl e he, BitVec.msb_and, Bool.and_eq_true, hx, h8, h9, h10,
      VG.Proof.MlDsa.X86_64.Round.nlL_msb (by rw [← VG.Proof.MlDsa.Round.n_eq] at *; exact hr _ (by rw [VG.Proof.MlDsa.Round.n_eq]; omega)) hb,
      decide_eq_true_iff, hI.acc l hl e he]
    refine ⟨fun ⟨h₁, h₂⟩ j hj => ?_, fun h => ⟨fun j hj => h j (by omega), h i (by omega)⟩⟩
    rcases (by omega : j < i ∨ j = i) with hj | rfl
    exacts [h₁ j hj, h₂]
  · exact ⟨by rw [o13.gpr], by rw [o13.gpr]⟩

end YNormL

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of XOnly YOnly ylanes yconst_ok ifp ifn)
open VG.Proof.MlDsa.X86_64.Arith (bc dword_psrad sshiftRight31)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Proof.MlKem.X86_64.S4 (bsum byteMask_eq)

theorem sw3264 (y : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 y) = y := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]; have := y.isLt; omega

/-- The bound, clamped to `q`. -/
theorem nlPro_ok (s₀ : State) :
    WP isa nlPro s₀ fun s₂ => (s₂.mem = s₀.mem ∧ ((s₂.gpr .rsi).setWidth 32).toNat = min (arg32 s₀ .rsi) q) ∧
        Keep [.rsi] s₀ s₂ := by
  unfold nlPro
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => (s₁.cf = some (decide (((s₀.gpr .rsi).setWidth 32).toNat < q)) ∧
      s₁.mem = s₀.mem ∧ s₁.gpr .rsi = BitVec.setWidth 64 ((s₀.gpr .rsi).setWidth 32)) ∧ Keep [.rsi] s₀ s₁)
    (by refine WP.keep _ ?_ (by decide); xrun; rfl)
    fun s₁ ⟨⟨hc, hm, hsi⟩, hk⟩ => ?_)
  refine WP.ite (M := isa) _ (show isa.eval .b s₁ = _ from hc) (fun h => ?_) (fun h => ?_)
  · rw [decide_eq_true_iff] at h
    refine WP.mono (Q := fun s₂ => s₂ = s₁) (by vrund) fun s₂ e => ?_
    subst e
    refine ⟨⟨hm, ?_⟩, hk⟩
    rw [hsi, VG.Proof.MlDsa.X86_64.Round.sw3264, Nat.min_eq_left (by unfold arg32; omega)]
  · rw [decide_eq_false_iff_not] at h
    refine WP.mono (Q := fun (s₂ : State) => (s₂.gpr .rsi = BitVec.setWidth 64 qImm ∧ s₂.mem = s₁.mem) ∧
      Keep [.rsi] s₁ s₂) (by refine WP.keep _ ?_ (by decide); xrun) fun s₂ ⟨⟨h1, h2⟩, k2⟩ => ?_
    refine ⟨⟨h2.trans hm, ?_⟩, (hk.trans k2).mono (by simp)⟩
    rw [h1, Nat.min_eq_right (by unfold arg32; omega)]; rfl

theorem qsub_eq {x : BitVec 32} (hx : x.toNat ≤ q) : qImm - x = BitVec.ofNat 32 (q - x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show qImm.toNat = q from rfl]
  rw [q_eq] at hx ⊢; omega

/-- The constants of the loop: `b`, `q - b` and all ones. -/
theorem nlConsts_ok (s : State) (hb : ((s.gpr .rsi).setWidth 32).toNat ≤ q) :
    WP isa (.block nlConsts) s fun s' =>
      (∀ l < 2, s'.lane .xmm8 l = bc ((s.gpr .rsi).setWidth 32) ∧
        s'.lane .xmm9 l = bc (BitVec.ofNat 32 (q - ((s.gpr .rsi).setWidth 32).toNat)) ∧
        s'.lane .xmm10 l = bc (BitVec.allOnes 32)) ∧ Keep [.rax] s s' ∧ s'.mem = s.mem ∧ s'.mxcsr = s.mxcsr := by
  simp only [nlConsts, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => (s1.gpr .rax = BitVec.setWidth 64 ((s.gpr .rsi).setWidth 32) ∧
      s1.mem = s.mem ∧ s1.mxcsr = s.mxcsr ∧ ∀ r l, s1.lane r l = s.lane r l) ∧ Keep [.rax] s s1)
    (by refine WP.keep _ ?_ (by decide); xrun; exact ⟨rfl, fun _ _ => rfl⟩) fun s1 ⟨⟨a1, m1, x1, l1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Round.ybc_ok .xmm8 s1) fun s2 ⟨c2, g2, m2, r2, w2, x2, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s3 : State) => (s3.gpr .rax = BitVec.setWidth 64 (qImm - (s2.gpr .rsi).setWidth 32) ∧
      s3.mem = s2.mem ∧ s3.mxcsr = s2.mxcsr ∧ ∀ r l, s3.lane r l = s2.lane r l) ∧ Keep [.rax] s2 s3)
    (by refine WP.keep _ ?_ (by decide); xrun; exact ⟨rfl, fun _ _ => rfl⟩) fun s3 ⟨⟨a3, m3, x3, l3⟩, k3⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Round.ybc_ok .xmm9 s3) fun s4 ⟨c4, g4, m4, r4, w4, x4, o4⟩ => ?_
  refine WP.mono (yconst_ok .xmm10 _ s4) fun s5 ⟨c5, k5, m5, x5, o5⟩ => ?_
  have e2 : s2.gpr .rsi = s.gpr .rsi := by rw [g2, k1.gpr (by decide)]
  refine ⟨fun l hl => ⟨?_, ?_, ?_⟩, ?_, by rw [m5, m4, m3, m2, m1], by rw [x5, x4, x3, x2, x1]⟩
  · rw [o5 _ (by decide) l hl, o4 _ (by decide) l hl, l3, c2 l hl, a1, VG.Proof.MlDsa.X86_64.Round.sw3264]
  · rw [o5 _ (by decide) l hl, c4 l hl, a3, e2, VG.Proof.MlDsa.X86_64.Round.sw3264, VG.Proof.MlDsa.X86_64.Round.qsub_eq hb]
  · rw [c5 l hl]; rfl
  · refine ⟨fun r hr => ?_, ?_, ?_⟩
    · rw [k5.gpr hr, g4, k3.gpr hr, g2, k1.gpr hr]
    · rw [k5.2.1, r4, k3.2.1, r2, k1.2.1]
    · rw [k5.2.2, w4, k3.2.2, w2, k1.2.2]

theorem lane_psrad : laneSseBlock (toY [.xop (.shift .psrad .xmm10 31)]) = some [.xop (.shift .psrad .xmm10 31)] := by
  decide +kernel

/-- Whether every doubleword of `ymm10` has its top bit set. -/
def allMsb (s : State) : Bool := (List.range 2).all fun l => (List.range 4).all fun e => (dword (s.lane .xmm10 l) e).msb

/-- The end: 1 if every doubleword of `ymm10` has its top bit set, and 0 otherwise. -/
theorem nlEnd_ok (s : State) :
    WP isa (.block nlEnd) s fun s' =>
      ((s'.gpr .rax).setWidth 32 = if VG.Proof.MlDsa.X86_64.Round.allMsb s = true then 1 else 0) ∧
        s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ ∀ r, r ≠ .rax → s'.gpr r = s.gpr r := by
  rw [nlEnd, List.append_assoc, WP.block_append_iff]
  refine WP.mono (ylanes VG.Proof.MlDsa.X86_64.Round.lane_psrad (rs := [.xmm10]) (P := fun l t => ∀ e < 4,
    dword (t.xmm .xmm10) e = (dword ((s.proj l).xmm .xmm10) e).sshiftRight (min (31 : BitVec 8).toNat 32))
    fun l hl => by vrun; exact ⟨fun e he => dword_psrad _ _ he, by xonly⟩) fun s1 ⟨B1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s2 : State) => s2.gpr = (s1.setReg .rax (byteMask (s1.ymm .xmm10) 32)).gpr ∧
    s2.mem = s1.mem ∧ s2.rd = s1.rd ∧ s2.wr = s1.wr) (by vrund; exact ⟨rfl, rfl, rfl, rfl⟩) fun s2 ⟨g2, m2, r2, w2⟩ => ?_
  xrun
  have hf : ∀ i < 32, (s1.ymm .xmm10).getLsbD (8 * i + 7) = (dword (s.lane .xmm10 (i / 16)) (i % 16 / 4)).msb :=
    fun i hi => by
      have hl : i / 16 < 2 := by omega
      have he : i % 16 / 4 < 4 := by omega
      have hd := B1 (i / 16) hl (i % 16 / 4) he
      rw [State.proj_xmm, State.proj_xmm, sshiftRight31] at hd
      rw [VG.Proof.MlDsa.X86_64.Round.ymm_bit _ _ hi, hd]
      split
      · rename_i h
        rw [BitVec.msb_eq_decide]; simp [h]
      · rename_i h
        rw [show (-1 : BitVec 32) = BitVec.allOnes 32 by decide, BitVec.getLsbD_allOnes, BitVec.msb_eq_decide]
        simp only [decide_eq_true (show 8 * (i % 4) + 7 < 32 by omega)]
        rw [decide_eq_true (by omega)]
  have hall : VG.Proof.MlDsa.X86_64.Round.allMsb s = true ↔ ∀ i < 32, (s1.ymm .xmm10).getLsbD (8 * i + 7) = true := by
    simp only [VG.Proof.MlDsa.X86_64.Round.allMsb, List.all_eq_true, List.mem_range]
    constructor
    · intro h i hi; rw [hf i hi]; exact h _ (by omega) _ (by omega)
    · intro h l hl e he
      have := h (16 * l + 4 * e) (by omega)
      rwa [hf _ (by omega), show (16 * l + 4 * e) / 16 = l by omega, show (16 * l + 4 * e) % 16 / 4 = e by omega]
        at this
  have hb := VG.Proof.MlKem.X86_64.S4.bsum_lt (fun i => (s1.ymm .xmm10).getLsbD (8 * i + 7)) 32
  have hax : s2.gpr .rax = BitVec.ofNat 64 (bsum (fun i => (s1.ymm .xmm10).getLsbD (8 * i + 7)) 32) := by
    rw [g2, RegUpd.gpr_setReg_self, byteMask_eq _ (by decide)]
  refine ⟨?_, by rw [m2, o1.mem], by rw [r2, o1.rd], by rw [w2, o1.wr], fun r hr => ?_⟩
  · rw [hax]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    have e1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [e1]
    by_cases h : VG.Proof.MlDsa.X86_64.Round.allMsb s = true
    · rw [ite_eq_left h, (VG.Proof.MlDsa.X86_64.Round.bsum_allOnes _ 32).mpr (hall.mp h)]; rfl
    · rw [ite_eq_right h]
      have : bsum (fun i => (s1.ymm .xmm10).getLsbD (8 * i + 7)) 32 ≠ 2 ^ 32 - 1 := fun e =>
        h (hall.mpr ((VG.Proof.MlDsa.X86_64.Round.bsum_allOnes _ 32).mp e))
      show _ = 0
      omega
  · rw [ite_eq_right hr, ite_eq_right hr, g2, RegUpd.gpr_setReg_of_ne _ _ hr, o1.gpr]

section
variable {s₀ : State} (hp : normLtK.pre s₀)
include hp

theorem normLtY_wp : WP isa normLtAvx2 s₀ fun s' =>
    ((s'.gpr .rax).setWidth 32 = if normRq [polyAt s₀.mem (s₀.gpr .rdi)] < arg32 s₀ .rsi then 1 else 0) ∧
      Frame [] s₀.mem s'.mem := by
  have hr : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2
  have hrd : pR (s₀.gpr .rdi) ∈ s₀.rd := by rw [hp.1]; simp
  unfold normLtAvx2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Round.nlPro_ok s₀) fun s₂ ⟨⟨hm2, hb2⟩, k2⟩ => ?_)
  have hbq : ((s₂.gpr .rsi).setWidth 32).toNat ≤ q := by rw [hb2]; exact Nat.min_le_right _ _
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Round.nlConsts_ok s₂ hbq) fun s₃ ⟨hc, k3, m3, _⟩ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlKem.X86_64.wp_rcxLoopY (N := 32) (by decide) (by decide)
    (Arith.YNormL.Inv s₀ ((s₂.gpr .rsi).setWidth 32)) (fun u o hy _ => ⟨?_, ?_, ?_, ?_, fun l hl => ?_, fun l hl => ?_,
      fun l hl e he => ?_⟩) fun i hi u hI => Arith.YNormL.step hrd hr hbq hi hI) fun s₄ hI => ?_)
  · rw [o.keep.gpr (by decide), k3.gpr (by decide), k2.gpr (by decide), Nat.mul_zero,
      VG.Proof.MlKem.X86_64.add_ofNat_zero]
  · rw [o.keep.2.1, k3.2.1, k2.2.1]
  · rw [o.keep.2.2, k3.2.2, k2.2.2]
  · rw [o.mem, m3, hm2]
  · simp only [State.lane]; rw [o.xmm, hy]; exact (hc l hl).1
  · simp only [State.lane]; rw [o.xmm, hy]; exact (hc l hl).2.1
  · have : u.lane .xmm10 l = bc (BitVec.allOnes 32) := by simp only [State.lane]; rw [o.xmm, hy]; exact (hc l hl).2.2
    rw [this, show dword (bc (BitVec.allOnes 32)) e = BitVec.allOnes 32 from bc_ofDwords _ e he]
    exact iff_of_true (by decide) fun j hj => absurd hj (Nat.not_lt_zero j)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Round.nlEnd_ok s₄) fun s' ⟨hv, hm', _, _, _⟩ => ⟨?_, ?_⟩
  · have hnorm : normRq [polyAt s₀.mem (s₀.gpr .rdi)] < arg32 s₀ .rsi ↔ VG.Proof.MlDsa.X86_64.Round.allMsb s₄ = true := by
      rw [normRq_lt]
      simp only [VG.Proof.MlDsa.X86_64.Round.allMsb, List.all_eq_true, List.mem_range]
      constructor
      · intro h l hl e he
        rw [(hI.acc l hl e he)]
        intro j hj
        have hk : 8 * j + 4 * l + e < 256 := by omega
        have := h _ hk
        rw [normZq_lt, polyAt_val hr hk] at this
        rw [hb2]
        exact (VG.Proof.MlDsa.X86_64.Round.good_clamp (by rw [← VG.Proof.MlDsa.Round.n_eq] at *; exact hr _ hk)).mpr this
      · intro h k hk
        have hk' : k < 256 := by rw [VG.Proof.MlDsa.Round.n_eq] at hk; exact hk
        have := (hI.acc (k % 8 / 4) (by omega) (k % 4) (by omega)).mp (h _ (by omega) _ (by omega)) (k / 8) (by omega)
        rw [show 8 * (k / 8) + 4 * (k % 8 / 4) + k % 4 = k by omega, hb2] at this
        rw [normZq_lt, polyAt_val hr hk]
        exact (VG.Proof.MlDsa.X86_64.Round.good_clamp (by rw [← VG.Proof.MlDsa.Round.n_eq] at *; exact hr _ hk)).mp this
    rw [hv]
    by_cases h : VG.Proof.MlDsa.X86_64.Round.allMsb s₄ = true
    · rw [ite_eq_left h, ite_eq_left (hnorm.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hnorm.mp h'))]
  · rw [hm', hI.mem]; exact Frame.refl _ _

theorem normLtY_correct : ∃ t s', Exec isa normLtAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ normLtK.post s₀ s' := by
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rsi, .rdi] (VG.Proof.MlDsa.X86_64.Round.normLtY_wp hp) (by decide +kernel)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf (by simp)), hv⟩

end

theorem normLtY_ct : ConstantTime isa normLtK.pre normLtK.pub normLtAvx2 :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsp] [.rsi])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [hp.1, hp.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2)
    (by taint_decide)

theorem normLtY_verified : Verified X86_64.target normLtAvx2 (normLtContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => VG.Proof.MlDsa.X86_64.Round.normLtY_correct hp) VG.Proof.MlDsa.X86_64.Round.normLtY_ct (by
    round_implies [normLtContract, normLtSig, normLtK, X86_64.abi, X86_64.argRegs] [normSat] using normSat)

end VG.Proof.MlDsa.X86_64.Round

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Round.YHint`. -/
section

/-!
# ML-DSA on x86-64: `vg_mldsa_make_hint_avx2`

In each doubleword, `mhX` computes the hint bit (`mhL`, `mhL_toNat`); the loop
stores the eight hints of an iteration and adds their count, the sum of the
nibbles of the byte mask of the hints shifted to bit 7 (`cntH_ok`, `nib_sp`),
to `r9`.
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes ifp ifn WP.keep)
open VG.Impl.MlKem.X86_64 (xb xmov toY)
open VG.Proof.MlDsa.X86_64.Arith (qV csubL csubL_toNat dword_csubV bc)

/-! ## A doubleword -/

/-- The hint bit `mhX` computes from `z` and `r`. -/
def mhL (g : Nat) (z r : BitVec 32) : BitVec 32 :=
  ((hbL g (csubL (r + z)) ^^^ hbL g r) + BitVec.ofNat 32 63) >>> 6

theorem mhL_toNat {g : Nat} (h : g ∈ gamma2s) {z r : BitVec 32} (hz : z.toNat < q) (hr : r.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Round.mhL g z r).toNat = (makeHint g (Fin.ofNat q z.toNat) (Fin.ofNat q r.toNat)).toNat := by
  have e1 : (r + z).toNat = r.toNat + z.toNat := by
    rw [BitVec.toNat_add]; rw [q_eq] at hz hr; omega
  have e2 : (csubL (r + z)).toNat = (r.toNat + z.toNat) % q := by
    rw [csubL_toNat (by rw [e1]; omega), e1, VG.Proof.MlDsa.Arith.condSub]
    split <;> rw [q_eq] at * <;> omega
  have hs : (csubL (r + z)).toNat < q := by rw [e2]; exact Nat.mod_lt _ (by decide)
  have hM : hbM g ≤ 44 ∧ 0 < hbM g := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have hu := Nat.mod_lt (hbF g ((r.toNat + z.toNat) % q)) hM.2
  have hv := Nat.mod_lt (hbF g r.toNat) hM.2
  have hx : hbF g ((r.toNat + z.toNat) % q) % hbM g ^^^ hbF g r.toNat % hbM g < 2 ^ 6 :=
    Nat.xor_lt_two_pow (by omega) (by omega)
  have hvz : (Fin.ofNat q z.toNat).val = z.toNat := Nat.mod_eq_of_lt hz
  have hvr : (Fin.ofNat q r.toNat).val = r.toNat := Nat.mod_eq_of_lt hr
  rw [makeHint_eq h, hvz, hvr, VG.Proof.MlDsa.X86_64.Round.mhL, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_xor,
    hbL_toNat h hs, hbL_toNat h hr, e2, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  by_cases e : hbF g r.toNat % hbM g = hbF g ((r.toNat + z.toNat) % q) % hbM g
  · rw [decide_eq_false (fun h' => h' e), e, Nat.xor_self]; rfl
  · rw [decide_eq_true e]
    have : hbF g ((r.toNat + z.toNat) % q) % hbM g ^^^ hbF g r.toNat % hbM g ≠ 0 :=
      fun h' => e (xor_eq_zero h').symm
    show _ = 1
    omega

theorem mhL_le {g : Nat} (h : g ∈ gamma2s) {z r : BitVec 32} (hz : z.toNat < q) (hr : r.toNat < q) :
    (VG.Proof.MlDsa.X86_64.Round.mhL g z r).toNat ≤ 1 := by
  rw [VG.Proof.MlDsa.X86_64.Round.mhL_toNat h hz hr]; exact Bool.toNat_le _

/-! ## The code on a register -/

theorem mhMid_ok (s : State) (hq : s.xmm .xmm15 = qV) :
    WP isa (.block mhMid) s fun s' => s'.xmm .xmm3 = s.xmm .xmm0 ∧
      (∀ e < 4, dword (s'.xmm .xmm0) e = csubL (dword (s.xmm .xmm4) e + dword (s.xmm .xmm5) e)) ∧
      XOnly [.xmm0, .xmm1, .xmm3] s s' := by
  simp only [mhMid, VG.Impl.MlDsa.X86_64.Arith.vcsub, VG.Impl.MlDsa.X86_64.Arith.vcadd, xmov, xb, List.cons_append,
    List.nil_append]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨trivial, fun e he => ?_, by xonly⟩
  rw [hq, ← dword_paddd _ _ he, ← dword_csubV _ he]
  rfl

theorem mhTail_ok (s : State) (h11 : Bc (s.xmm .xmm11) (BitVec.ofNat 32 63)) :
    WP isa (.block mhTail) s fun s' => (∀ e < 4,
      dword (s'.xmm .xmm0) e = ((dword (s.xmm .xmm0) e ^^^ dword (s.xmm .xmm3) e) + BitVec.ofNat 32 63) >>> 6 ∧
      dword (s'.xmm .xmm1) e = (((dword (s.xmm .xmm0) e ^^^ dword (s.xmm .xmm3) e) + BitVec.ofNat 32 63) >>> 6) <<< 7) ∧
      XOnly [.xmm0, .xmm1] s s' := by
  simp only [mhTail, xmov, xb]
  vrun [VG.X86_64.eval_movdqa]
  refine ⟨fun e he => ?_, by xonly⟩
  simp (disch := first | decide | with_reducible assumption) only [dword_pxor, dword_paddd, dword_psrld, dword_pslld, h11 e he]
  exact ⟨rfl, rfl⟩

theorem mhX_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State) (hc : HbC g s) (hq : s.xmm .xmm15 = qV)
    (h11 : Bc (s.xmm .xmm11) (BitVec.ofNat 32 63)) :
    WP isa (.block (mhX g)) s fun s' => (∀ e < 4,
      dword (s'.xmm .xmm0) e = VG.Proof.MlDsa.X86_64.Round.mhL g (dword (s.xmm .xmm5) e) (dword (s.xmm .xmm0) e) ∧
      dword (s'.xmm .xmm1) e = VG.Proof.MlDsa.X86_64.Round.mhL g (dword (s.xmm .xmm5) e) (dword (s.xmm .xmm0) e) <<< 7) ∧
      XOnly [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4] s s' := by
  rw [mhX, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (Q := fun (s1 : State) => s1.xmm .xmm4 = s.xmm .xmm0 ∧ XOnly [.xmm4] s s1)
    (by simp only [xmov, xb]; vrun [VG.X86_64.eval_movdqa]; exact ⟨trivial, by xonly⟩) fun s1 ⟨a1, o1⟩ => ?_
  have hc1 : HbC g s1 := ⟨by rw [o1.xmm _ (by decide)]; exact hc.c8, by rw [o1.xmm _ (by decide)]; exact hc.c9,
    by rw [o1.xmm _ (by decide)]; exact hc.c10⟩
  rw [WP.block_append_iff]
  refine WP.mono (hbX_ok hg s1 hc1) fun s2 ⟨a2, o2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Round.mhMid_ok s2 (by rw [o2.xmm _ (by decide), o1.xmm _ (by decide), hq])) fun s3 ⟨b3, a3, o3⟩ => ?_
  have hc3 : HbC g s3 := ⟨by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]; exact hc1.c8,
    by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]; exact hc1.c9,
    by rw [o3.xmm _ (by decide), o2.xmm _ (by decide)]; exact hc1.c10⟩
  rw [WP.block_append_iff]
  refine WP.mono (hbX_ok hg s3 hc3) fun s4 ⟨a4, o4⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Round.mhTail_ok s4 (by
    rw [o4.xmm _ (by decide), o3.xmm _ (by decide), o2.xmm _ (by decide), o1.xmm _ (by decide)]; exact h11))
    fun s5 ⟨a5, o5⟩ => ⟨fun e he => ?_, ?_⟩
  · have hz : dword (s4.xmm .xmm0) e = hbL g (csubL (dword (s.xmm .xmm0) e + dword (s.xmm .xmm5) e)) := by
      rw [a4 e he, a3 e he, o2.xmm _ (by decide), a1, o2.xmm _ (by decide), o1.xmm _ (by decide)]
    have hr1 : dword (s4.xmm .xmm3) e = hbL g (dword (s.xmm .xmm0) e) := by
      rw [o4.xmm _ (by decide), b3, a2 e he, o1.xmm _ (by decide)]
    rw [(a5 e he).1, (a5 e he).2, hz, hr1]
    exact ⟨rfl, rfl⟩
  · exact ((((o1.trans o2).trans o3).trans o4).trans o5).mono (by simp)

/-! ## The count -/

/-- What `cntH` leaves in `eax`: the sum of the nibbles of `x`, if it fits in one. -/
def nib (x : BitVec 32) : BitVec 32 :=
  let x1 := x + x >>> 4
  let x2 := x1 + x1 >>> 8
  (x2 + x2 >>> 16) &&& 15

/-- The eight bits `b d` at bits `4d`. -/
def sp (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => VG.Proof.MlDsa.X86_64.Round.sp b k + (b k).toNat * 16 ^ k

/-- The number of the first `k` bits set. -/
def cnt8 (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => VG.Proof.MlDsa.X86_64.Round.cnt8 b k + (b k).toNat

theorem nib_bools : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
    (VG.Proof.MlDsa.X86_64.Round.nib (BitVec.ofNat 32 (b0.toNat + b1.toNat * 16 + b2.toNat * 16 ^ 2 + b3.toNat * 16 ^ 3 + b4.toNat * 16 ^ 4 +
      b5.toNat * 16 ^ 5 + b6.toNat * 16 ^ 6 + b7.toNat * 16 ^ 7))).toNat =
      b0.toNat + b1.toNat + b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b7.toNat := by
  decide +kernel

theorem nib_sp (b : Nat → Bool) : (VG.Proof.MlDsa.X86_64.Round.nib (BitVec.ofNat 32 (VG.Proof.MlDsa.X86_64.Round.sp b 8))).toNat = VG.Proof.MlDsa.X86_64.Round.cnt8 b 8 := by
  have := VG.Proof.MlDsa.X86_64.Round.nib_bools (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7)
  simp only [VG.Proof.MlDsa.X86_64.Round.sp, VG.Proof.MlDsa.X86_64.Round.cnt8, Nat.pow_zero, Nat.mul_one, Nat.zero_add, Nat.pow_one] at this ⊢
  exact this

/-- A byte mask with bit `4d` the bit `b d`, and the others clear. -/
theorem bsum_sp {f : Nat → Bool} {b : Nat → Bool} : ∀ k, (∀ j < 4 * k, f j = (decide (j % 4 = 0) && b (j / 4))) →
    VG.Proof.MlKem.X86_64.S4.bsum f (4 * k) = VG.Proof.MlDsa.X86_64.Round.sp b k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := VG.Proof.MlDsa.X86_64.Round.bsum_sp k fun j hj => h j (by omega)
    rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by omega]
    simp only [VG.Proof.MlKem.X86_64.S4.bsum, VG.Proof.MlDsa.X86_64.Round.sp]
    rw [ih, h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
    simp only [show (4 * k) % 4 = 0 by omega, show (4 * k + 1) % 4 = 1 by omega, show (4 * k + 2) % 4 = 2 by omega,
      show (4 * k + 1 + 1 + 1) % 4 = 3 by omega, show 4 * k / 4 = k by omega,
      decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.toNat_false, Nat.zero_mul, Nat.add_zero,
      show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide]
    rw [show 2 ^ (4 * k) = 16 ^ k by rw [Nat.pow_mul]]

theorem cntH_ok (s : State) :
    WP isa (.block cntH) s fun s' =>
      (s'.gpr .r9 = s.gpr .r9 + BitVec.setWidth 64 (VG.Proof.MlDsa.X86_64.Round.nib ((s.gpr .rax).setWidth 32)) ∧ s'.mem = s.mem ∧
        ∀ r l, s'.lane r l = s.lane r l) ∧ Keep [.rax, .rdx, .r9] s s' := by
  refine WP.keep _ ?_ (by decide)
  simp only [cntH]
  xrun
  exact ⟨rfl, fun _ _ => rfl⟩

end VG.Proof.MlDsa.X86_64.Round

namespace VG.Proof.MlDsa.X86_64.Arith

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round
open VG.Proof.MlDsa.Arith
open VG.Proof.MlDsa.X86_64.Round (HbC Bc bc_ofDwords mhL mhL_le mhX_ok nib sp cnt8 nib_sp bsum_sp ymm_bit cntH_ok
  sw3264)
open VG.Proof.MlKem.X86_64 (Keep XOnly YOnly ylanes yld_ok yconst_ok wp_rcxLoopY ifp ifn ptr_step add_ofNat_zero
  lane_setReg lane_setFlags sx32 State.setMem_ymm)
open VG.Impl.MlKem.X86_64 (toY)
open VG.Spec.MlDsa (q n coeffAt Reduced gamma2s)

/-- `Σ k < m, f k`. -/
def csum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => VG.Proof.MlDsa.X86_64.Arith.csum f m + f m

namespace YHintL

/-- After `i` vectors of eight. -/
structure Inv (s₀ : State) (g : Nat) (i : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = s₀.gpr .rdi + BitVec.ofNat 64 (32 * i)
  rsi : s.gpr .rsi = s₀.gpr .rsi + BitVec.ofNat 64 (32 * i)
  r10 : s.gpr .r10 = s₀.gpr .rcx + BitVec.ofNat 64 (32 * i)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  yc : YC g s
  c11 : ∀ l < 2, s.lane .xmm11 l = bc (BitVec.ofNat 32 63)
  frame : Frame [pR (s₀.gpr .rcx)] s₀.mem s.mem
  coeff : ∀ k < 256, coeffAt s.mem (s₀.gpr .rcx) k = if k < 8 * i then
    VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k) else coeffAt s₀.mem (s₀.gpr .rcx) k
  r9 : (s.gpr .r9).toNat =
    VG.Proof.MlDsa.X86_64.Arith.csum (fun k => (VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat) (8 * i)

theorem lane_mhX (g : Nat) (hg : g = g32 ∨ g = g88) : laneSseBlock (toY (mhX g)) = some (mhX g) := by
  rcases hg with rfl | rfl <;> decide +kernel

/-- The constants are kept by code that writes only `xmm0` to `xmm5`. -/
theorem keep_consts {g : Nat} {s s' : State} (hyc : YC g s) (h11 : ∀ l < 2, s.lane .xmm11 l = bc (BitVec.ofNat 32 63))
    {rs : List XReg} (hr : ∀ r ∈ rs, r ∈ [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5])
    (hl : ∀ r ∉ rs, ∀ l < 2, s'.lane r l = s.lane r l) :
    YC g s' ∧ ∀ l < 2, s'.lane .xmm11 l = bc (BitVec.ofNat 32 63) := by
  have n : ∀ r ∈ [XReg.xmm8, .xmm9, .xmm10, .xmm11, .xmm15], r ∉ rs := fun r hr' hr'' => by
    have := hr r hr''; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr' this
    rcases hr' with rfl | rfl | rfl | rfl | rfl <;> rcases this with h | h | h | h | h | h <;> cases h
  refine ⟨fun l hl' => ?_, fun l hl' => by rw [hl _ (n _ (by simp)) l hl']; exact h11 l hl'⟩
  rw [hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl', hl _ (n _ (by simp)) l hl']
  exact hyc l hl'

/-- A hint shifted to bit 7: bit `8m + 7` is the hint's bit 0 if `m = 0`, and clear otherwise. -/
theorem shl7_bit {v : BitVec 32} (hv : v.toNat ≤ 1) {m : Nat} (hm : m < 4) :
    (v <<< 7).getLsbD (8 * m + 7) = (decide (m = 0) && v.getLsbD 0) := by
  rw [BitVec.getLsbD_shiftLeft]
  rcases (by omega : m = 0 ∨ 0 < m) with rfl | h
  · simp
  · have : v.getLsbD (8 * m) = false := by
      rw [← BitVec.testBit_toNat, Nat.testBit_lt_two_pow (Nat.lt_of_le_of_lt hv
        (Nat.one_lt_two_pow (by omega)))]
    simp [show 8 * m + 7 - 7 = 8 * m by omega, this, show m ≠ 0 by omega]

theorem bit0_toNat {v : BitVec 32} (hv : v.toNat ≤ 1) : (v.getLsbD 0).toNat = v.toNat := by
  rw [← BitVec.testBit_toNat, Nat.testBit_zero]
  rcases (by omega : v.toNat = 0 ∨ v.toNat = 1) with h | h <;> rw [h] <;> rfl

theorem csum_le {f : Nat → Nat} : ∀ {m : Nat}, (∀ k < m, f k ≤ 1) → VG.Proof.MlDsa.X86_64.Arith.csum f m ≤ m
  | 0, _ => Nat.le_refl _
  | m + 1, h => by
    have := VG.Proof.MlDsa.X86_64.Arith.YHintL.csum_le (m := m) fun k hk => h k (by omega)
    have := h m (by omega)
    simp only [VG.Proof.MlDsa.X86_64.Arith.csum]; omega

theorem csum8 (f : Nat → Nat) (b : Nat → Bool) (m : Nat) (h : ∀ d < 8, (b d).toNat = f (m + d)) :
    VG.Proof.MlDsa.X86_64.Arith.csum f (m + 8) = VG.Proof.MlDsa.X86_64.Arith.csum f m + VG.Proof.MlDsa.X86_64.Round.cnt8 b 8 := by
  rw [show VG.Proof.MlDsa.X86_64.Arith.csum f (m + 8) = VG.Proof.MlDsa.X86_64.Arith.csum f m + f m + f (m + 1) + f (m + 2) + f (m + 3) + f (m + 4) + f (m + 5) +
      f (m + 6) + f (m + 7) from rfl,
    show VG.Proof.MlDsa.X86_64.Round.cnt8 b 8 = (b 0).toNat + (b 1).toNat + (b 2).toNat + (b 3).toNat + (b 4).toNat + (b 5).toNat +
      (b 6).toNat + (b 7).toNat by simp [VG.Proof.MlDsa.X86_64.Round.cnt8],
    h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide), h 5 (by decide),
    h 6 (by decide), h 7 (by decide)]
  simp only [Nat.add_zero]
  omega

section
variable {s₀ : State} (hrd : s₀.rd = [pR (s₀.gpr .rdi), pR (s₀.gpr .rsi)]) (hwr : s₀.wr = [pR (s₀.gpr .rcx)])
  (hdz : (pR (s₀.gpr .rdi)).Disjoint (pR (s₀.gpr .rcx))) (hdr : (pR (s₀.gpr .rsi)).Disjoint (pR (s₀.gpr .rcx)))
  (hz : Reduced s₀.mem (s₀.gpr .rdi)) (hr : Reduced s₀.mem (s₀.gpr .rsi)) {g : Nat} (hg : g = g32 ∨ g = g88)
include hrd hwr hdz hdr hz hr hg

theorem step {i : Nat} (hi : i < 32) {s : State} (hI : VG.Proof.MlDsa.X86_64.Arith.YHintL.Inv s₀ g i s) :
    WP isa (.block (mhBodyY g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      VG.Proof.MlDsa.X86_64.Arith.YHintL.Inv s₀ g (i + 1) s' ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0) := by
  have hg' : g ∈ gamma2s := by rcases hg with rfl | rfl <;> decide
  have j0 : 8 * i + 8 ≤ 256 := by omega
  have hw : pR (s₀.gpr .rcx) ∈ s.wr := by rw [hI.wr, hwr]; simp
  have hrz : pR (s₀.gpr .rdi) ∈ s.rd ++ s.wr := by rw [hI.rd, hrd]; simp
  have hrr : pR (s₀.gpr .rsi) ∈ s.rd ++ s.wr := by rw [hI.rd, hrd]; simp
  have e1 : s.gpr .rsi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rsi) (8 * i) := by
    rw [add_ofNat_zero, hI.rsi]; congr 2; omega
  have e2 : s.gpr .rdi + BitVec.ofNat 64 0 = coeffAddr (s₀.gpr .rdi) (8 * i) := by
    rw [add_ofNat_zero, hI.rdi]; congr 2; omega
  have e3 : s.gpr .r10 = coeffAddr (s₀.gpr .rcx) (8 * i) := by rw [hI.r10]; congr 2; omega
  rw [mhBodyY, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    show ∀ a b : Instr, [a, b] = [a] ++ [b] from fun _ _ => rfl, List.append_assoc, WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [e1]; exact f_in32 hrr j0)) fun s1 ⟨L1, o1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (yld_ok (by rw [o1.rd, o1.wr, o1.gpr, e2]; exact f_in32 hrz j0)) fun s2 ⟨L2, o2⟩ => ?_
  have k2 := VG.Proof.MlDsa.X86_64.Arith.YHintL.keep_consts hI.yc hI.c11 (rs := [.xmm0, .xmm5]) (by simp) fun r hr' l hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [o2.lane r (by simp [hr'.2]) l hl, o1.lane r (by simp [hr'.1]) l hl]
  rw [WP.block_append_iff]
  refine WP.mono (ylanes (VG.Proof.MlDsa.X86_64.Arith.YHintL.lane_mhX g hg) (P := fun l t => ∀ e < 4,
      dword (t.xmm .xmm0) e = VG.Proof.MlDsa.X86_64.Round.mhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e) ∧
      dword (t.xmm .xmm1) e = VG.Proof.MlDsa.X86_64.Round.mhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e) <<< 7)
    fun l hl => VG.Proof.MlDsa.X86_64.Round.mhX_ok hg _ (k2.1.hbc hl) (k2.1.q hl)
      (by rw [State.proj_xmm, k2.2 l hl]; exact bc_ofDwords _)) fun s3 ⟨B3, o3⟩ => ?_
  have o13 := (o1.trans o2).trans o3
  have k3 := VG.Proof.MlDsa.X86_64.Arith.YHintL.keep_consts k2.1 k2.2 (rs := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4]) (by simp) o3.lane
  have g3 : s3.gpr .r10 = coeffAddr (s₀.gpr .rcx) (8 * i) := by rw [o13.gpr, e3]
  have w0 : InRegions s3.wr (s3.gpr .r10) 32 := by rw [o13.wr, g3]; exact f_in32 hw j0
  -- The values of the lanes.
  have hv : ∀ l < 2, ∀ e < 4, VG.Proof.MlDsa.X86_64.Round.mhL g (dword ((s2.proj l).xmm .xmm5) e) (dword ((s2.proj l).xmm .xmm0) e) =
      VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
    fun l hl e he => by
      rw [State.proj_xmm, State.proj_xmm, L2 l hl, o2.lane _ (by decide) l hl, L1 l hl, o1.mem, o1.gpr, e1, e2,
        dword_readW _ _ he, dword_readW _ _ he, lane_load, lane_load, coeffAddr_add, coeffAddr_add, ← coeffAt_eq,
        ← coeffAt_eq, coeffAt_frame hI.frame (by simpa using hdz) (by rw [n_eq]; omega),
        coeffAt_frame hI.frame (by simpa using hdr) (by rw [n_eq]; omega)]
  have hle : ∀ k < 256, (VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat ≤ 1 :=
    fun k hk => VG.Proof.MlDsa.X86_64.Round.mhL_le hg' (hz k (by rw [n_eq]; exact hk)) (hr k (by rw [n_eq]; exact hk))
  rw [WP.block_append_iff]
  refine WP.mono (Q := fun (s4 : State) => s4.mem = s3.mem.writeW (s3.gpr .r10) (s3.ymm .xmm0) ∧
      s4.gpr = (s3.setReg .rax (byteMask (s3.ymm .xmm1) 32)).gpr ∧ s4.rd = s3.rd ∧ s4.wr = s3.wr ∧
      ∀ r l, s4.lane r l = s3.lane r l)
    (by
      vrund [State.store256_eq, State.setMem_gpr, State.setMem_wr, State.setMem_mem, State.setMem_rd,
        State.setMem_ymm, w0]
      exact ⟨rfl, fun r l => by simp only [lane_setReg, State.setMem_lane]⟩) fun s4 ⟨m4, g4, r4, w4, l4⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Round.cntH_ok s4) fun s5 ⟨⟨h9, m5, l5⟩, k5⟩ => ?_
  have hax : s4.gpr .rax = byteMask (s3.ymm .xmm1) 32 := by rw [g4, RegUpd.gpr_setReg_self]
  -- The count of the eight hints.
  let b : Nat → Bool := fun d =>
    (VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + d)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + d))).getLsbD 0
  have hbits : ∀ j < 4 * 8, (s3.ymm .xmm1).getLsbD (8 * j + 7) = (decide (j % 4 = 0) && b (j / 4)) := fun j hj => by
    have hl : j / 16 < 2 := by omega
    have he : j % 16 / 4 < 4 := by omega
    rw [VG.Proof.MlDsa.X86_64.Round.ymm_bit _ _ (by omega), ← State.proj_xmm, (B3 _ hl _ he).2, hv _ hl _ he,
      VG.Proof.MlDsa.X86_64.Arith.YHintL.shl7_bit (hle _ (by omega)) (by omega)]
    simp only [b, show 8 * i + 4 * (j / 16) + j % 16 / 4 = 8 * i + j / 4 by omega]
  have hcnt : (BitVec.setWidth 64 (VG.Proof.MlDsa.X86_64.Round.nib ((s4.gpr .rax).setWidth 32))).toNat = VG.Proof.MlDsa.X86_64.Round.cnt8 b 8 := by
    rw [hax, VG.Proof.MlKem.X86_64.S4.byteMask_eq _ (by decide), BitVec.toNat_setWidth,
      show BitVec.setWidth 32 (BitVec.ofNat 64 (VG.Proof.MlKem.X86_64.S4.bsum
        (fun i => (s3.ymm .xmm1).getLsbD (8 * i + 7)) 32)) =
        BitVec.ofNat 32 (VG.Proof.MlKem.X86_64.S4.bsum (fun i => (s3.ymm .xmm1).getLsbD (8 * i + 7)) 32) by
      apply BitVec.eq_of_toNat_eq
      have := VG.Proof.MlKem.X86_64.S4.bsum_lt (fun i => (s3.ymm .xmm1).getLsbD (8 * i + 7)) 32
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega,
      (VG.Proof.MlDsa.X86_64.Round.bsum_sp 8 hbits : VG.Proof.MlKem.X86_64.S4.bsum _ 32 = _), VG.Proof.MlDsa.X86_64.Round.nib_sp]
    have : VG.Proof.MlDsa.X86_64.Round.cnt8 b 8 ≤ 8 := by
      simp only [VG.Proof.MlDsa.X86_64.Round.cnt8]
      have hb := fun d => Bool.toNat_le (b d)
      have := hb 0; have := hb 1; have := hb 2; have := hb 3; have := hb 4; have := hb 5
      have := hb 6; have := hb 7
      omega
    have := (VG.Proof.MlDsa.X86_64.Round.nib_sp b).symm ▸ this
    omega
  simp only [List.cons_append, List.nil_append]
  xrun
  have G5 : ∀ r, r ∉ [Reg.rax, .rdx, .r9] → s5.gpr r = s.gpr r := fun r hr => by
    rw [k5.gpr hr, g4, RegUpd.gpr_setReg_of_ne _ _ (fun h => hr (by simp [h])), o13.gpr]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun k hk => ?_, ?_⟩, by rw [G5 .rcx (by simp)], by rw [G5 .rcx (by simp)]⟩
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [G5 .rdi (by simp), hI.rdi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [G5 .rsi (by simp), hI.rsi]; exact ptr_step _ i 32
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_true, ite_false, reduceCtorEq]
    rw [G5 .r10 (by simp), hI.r10]; exact ptr_step _ i 32
  · simp only [RegUpd.rd_setReg, RegUpd.rd_setFlags]; rw [k5.2.1, r4, o13.rd, hI.rd]
  · simp only [RegUpd.wr_setReg, RegUpd.wr_setFlags]; rw [k5.2.2, w4, o13.wr, hI.wr]
  · exact k3.1.keep (rs := []) (by simp) fun r _ l _ => by simp only [lane_setReg, lane_setFlags]; rw [l5, l4]
  · intro l hl; simp only [lane_setReg, lane_setFlags]; rw [l5, l4]; exact k3.2 l hl
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m5, m4, g3, o13.mem]; exact hI.frame.writeW (List.mem_singleton_self _) _ (pR_contains32 _ j0)
  · simp only [RegUpd.mem_setReg, RegUpd.mem_setFlags]
    rw [m5, m4, g3, o13.mem, VG.Proof.MlDsa.X86_64.Arith.coeffAt_write256 _ _ j0 _ hk]
    split
    · rename_i h
      rw [ifp (show k < 8 * (i + 1) by omega), State.ymm, extract_ymm _ _ (by omega)]
      have hc : ∀ l < 2, ∀ e < 4, dword (s3.lane .xmm0 l) e =
          VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) (8 * i + 4 * l + e)) (coeffAt s₀.mem (s₀.gpr .rsi) (8 * i + 4 * l + e)) :=
        fun l hl e he => by rw [← State.proj_xmm, (B3 l hl e he).1, hv l hl e he]
      split
      · rename_i h4
        have := hc 0 (by decide) (k - 8 * i) h4
        rw [show 8 * i + 4 * 0 + (k - 8 * i) = k by omega] at this
        exact this
      · rename_i h4
        have := hc 1 (by decide) (k - 8 * i - 4) (by omega)
        rw [show 8 * i + 4 * 1 + (k - 8 * i - 4) = k by omega] at this
        exact this
    · rename_i h
      rw [hI.coeff k hk]
      by_cases h' : k < 8 * i
      · rw [ifp h', ifp (by omega)]
      · rw [ifn h', ifn (by omega)]
  · simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, ite_false, reduceCtorEq]
    have h94 : s4.gpr .r9 = s.gpr .r9 := by
      rw [g4, RegUpd.gpr_setReg_of_ne _ _ (by decide), o13.gpr]
    have e8 := VG.Proof.MlDsa.X86_64.Arith.YHintL.csum8 (fun k => (VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat) b
      (8 * i) fun d hd => VG.Proof.MlDsa.X86_64.Arith.YHintL.bit0_toNat (hle _ (by omega))
    have hb := VG.Proof.MlDsa.X86_64.Arith.YHintL.csum_le (f := fun k => (VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat)
      (m := 8 * i + 8) fun k hk => hle k (by omega)
    rw [h9, BitVec.toNat_add, hcnt, h94, hI.r9, show 8 * (i + 1) = 8 * i + 8 by omega, e8]
    rw [e8] at hb
    exact Nat.mod_eq_of_lt (by omega)

/-- The constants and the loop: the hints at `h`, and their count in `r9`. -/
theorem loop_ok {s : State} (hs0 : s.gpr .rdi = s₀.gpr .rdi) (hs1 : s.gpr .rsi = s₀.gpr .rsi)
    (hs10 : s.gpr .r10 = s₀.gpr .rcx) (hs9 : s.gpr .r9 = 0) (hsrd : s.rd = s₀.rd) (hswr : s.wr = s₀.wr)
    (hsm : s.mem = s₀.mem) :
    WP isa (mhY g) s fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
      (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
        VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
      (s'.gpr .r9).toNat =
        VG.Proof.MlDsa.X86_64.Arith.csum (fun k => (VG.Proof.MlDsa.X86_64.Round.mhL g (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat) 256 := by
  unfold mhY
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (yC_ok g s) fun w ⟨yc, k1, m1, _, _⟩ =>
    WP.mono (yconst_ok .xmm11 63 w) fun w2 ⟨l2, k2, m2, _, o2⟩ => ?_
  have yc2 : YC g w2 := fun l hl => by
    rw [o2 .xmm8 (by decide) l hl, o2 .xmm9 (by decide) l hl, o2 .xmm10 (by decide) l hl,
      o2 .xmm15 (by decide) l hl]
    exact yc l hl
  refine WP.mono (wp_rcxLoopY (N := 32) (by decide) (by decide) _ (fun u o hy _ =>
    ⟨by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs0],
      by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs1],
      by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), Nat.mul_zero, add_ofNat_zero, hs10],
      by rw [o.keep.2.1, k2.2.1, k1.2.1, hsrd], by rw [o.keep.2.2, k2.2.2, k1.2.2, hswr],
      fun l hl => by simp only [State.lane]; rw [o.xmm, hy]; exact yc2 l hl,
      fun l hl => by simp only [State.lane]; rw [o.xmm, hy]; exact l2 l hl,
      by rw [o.mem, m2, m1, hsm]; exact Frame.refl _ _, fun k _ => by rw [o.mem, m2, m1, hsm, ifn (by omega)],
      by rw [o.keep.gpr (by decide), k2.gpr (by decide), k1.gpr (by decide), hs9]; rfl⟩)
    fun i hi u hI => VG.Proof.MlDsa.X86_64.Arith.YHintL.step hrd hwr hdz hdr hz hr hg hi hI) fun u hI => ⟨hI.frame, fun k hk => by
      rw [hI.coeff k hk, ifp (by omega)], hI.r9⟩

end

end YHintL

end VG.Proof.MlDsa.X86_64.Arith

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)
open VG.Proof.MlDsa.X86_64.Arith (csum)

/-- The count of the hints is `onesFrom` them. -/
theorem csum_onesFrom (v : Vector Bool n) (f : Nat → Nat) (hf : ∀ k < 256, f k = v[k]!.toNat) :
    ∀ m ≤ 256, VG.Proof.MlDsa.X86_64.Arith.csum f m + onesFrom v m = onesFrom v 0
  | 0, _ => Nat.zero_add _
  | m + 1, hm => by
    have ih := VG.Proof.MlDsa.X86_64.Round.csum_onesFrom v f hf m (by omega)
    rw [onesFrom_step v (by rw [n_eq]; omega), ← hf m (by omega)] at ih
    simp only [VG.Proof.MlDsa.X86_64.Arith.csum]; omega

section
variable {s₀ : State} (hp : makeHintK.pre s₀)
include hp

theorem makeHintY_correct : ∃ t s', Exec isa makeHintAvx2 s₀ t s' ∧ abiPreserved s₀ s' ∧ makeHintK.post s₀ s' := by
  have hg : arg32 s₀ .rdx ∈ gamma2s := hp.2.2.2.2.2.2.2.1
  have hz : Reduced s₀.mem (s₀.gpr .rdi) := hp.2.2.2.2.2.2.2.2.1
  have hr : Reduced s₀.mem (s₀.gpr .rsi) := hp.2.2.2.2.2.2.2.2.2
  let f : Nat → Nat := fun k =>
    (VG.Proof.MlDsa.X86_64.Round.mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)).toNat
  have wp : WP isa makeHintAvx2 s₀ fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
      (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
        VG.Proof.MlDsa.X86_64.Round.mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
      (s'.gpr .rax).toNat = VG.Proof.MlDsa.X86_64.Arith.csum f 256 := by
    unfold makeHintAvx2
    refine WP.seq (WP.mono (mhPrologue_ok s₀) fun s₁ ⟨⟨h10, h9, hzf, hm⟩, hk⟩ => ?_)
    have go : ∀ g, arg32 s₀ .rdx = g → (g = g32 ∨ g = g88) → WP isa (mhY g) s₁ fun s' =>
        Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
          VG.Proof.MlDsa.X86_64.Round.mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
        (s'.gpr .r9).toNat = VG.Proof.MlDsa.X86_64.Arith.csum f 256 := fun g hge hg' => by
      subst hge
      exact Arith.YHintL.loop_ok hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hz hr hg' (hk.gpr (by decide))
        (hk.gpr (by decide)) h10 h9 hk.2.1 hk.2.2 hm
    have hite : WP isa (.ite .e (mhY g32) (mhY g88)) s₁ fun s' => Frame [pR (s₀.gpr .rcx)] s₀.mem s'.mem ∧
        (∀ k < 256, coeffAt s'.mem (s₀.gpr .rcx) k =
          VG.Proof.MlDsa.X86_64.Round.mhL (arg32 s₀ .rdx) (coeffAt s₀.mem (s₀.gpr .rdi) k) (coeffAt s₀.mem (s₀.gpr .rsi) k)) ∧
        (s'.gpr .r9).toNat = VG.Proof.MlDsa.X86_64.Arith.csum f 256 := by
      refine WP.ite (M := isa) _ (show isa.eval .e s₁ = _ from hzf) (fun h => ?_) (fun h => ?_)
      · rw [VG.Proof.MlDsa.X86_64.Round.sub_beq_zero32, decide_eq_true_eq] at h
        exact go _ ((gamma_cases hg).1 h) (.inl rfl)
      · rw [VG.Proof.MlDsa.X86_64.Round.sub_beq_zero32, decide_eq_false_iff_not] at h
        exact go _ ((gamma_cases hg).2 h) (.inr rfl)
    refine WP.seq (WP.mono hite fun u ⟨hf, hc, h9'⟩ => ?_)
    refine WP.mono (Q := fun (u' : State) => u'.mem = u.mem ∧ u'.gpr .rax = u.gpr .r9) (by vrund; exact ⟨rfl, rfl⟩)
      fun u' ⟨hm', hax⟩ => ?_
    rw [hm', hax]
    exact ⟨hf, hc, h9'⟩
  obtain ⟨t, s', he, ⟨hf, hv, hax⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .rsi, .rdi, .r9, .r10] wp (by decide +kernel)
  refine ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he (gprPreserved_of hk (by decide) hf ?_), ?_, ?_⟩
  · simpa using hp.2.2.2.2.2.2.1
  · refine hintIs_of_toNat fun k hk' => ?_
    apply BitVec.eq_of_toNat_eq
    rw [hv k hk', VG.Proof.MlDsa.X86_64.Round.mhL_toNat hg (hz k hk') (hr k hk'), zipWith_get _ _ _ hk', polyAt_get _ _ hk', polyAt_get _ _ hk']
    simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Bool.toNat_le _) (by decide))).symm
  · have e := VG.Proof.MlDsa.X86_64.Round.csum_onesFrom (Vector.zipWith (makeHint (arg32 s₀ .rdx)) (polyAt s₀.mem (s₀.gpr .rdi))
      (polyAt s₀.mem (s₀.gpr .rsi))) f (fun k hk' => by
        rw [zipWith_get _ _ _ (by rw [n_eq]; exact hk'), polyAt_get _ _ (by rw [n_eq]; exact hk'),
          polyAt_get _ _ (by rw [n_eq]; exact hk')]
        exact VG.Proof.MlDsa.X86_64.Round.mhL_toNat hg (hz k (by rw [n_eq]; exact hk')) (hr k (by rw [n_eq]; exact hk'))) 256 (Nat.le_refl _)
    have e0 : onesFrom (Vector.zipWith (makeHint (arg32 s₀ .rdx)) (polyAt s₀.mem (s₀.gpr .rdi))
        (polyAt s₀.mem (s₀.gpr .rsi))) 256 = 0 := onesFrom_n _
    have : (s'.gpr .rax).toNat ≤ 256 := by
      rw [hax]
      exact Arith.YHintL.csum_le fun k hk' => VG.Proof.MlDsa.X86_64.Round.mhL_le hg (hz k (by rw [n_eq]; exact hk')) (hr k (by rw [n_eq]; exact hk'))
    rw [BitVec.toNat_setWidth, hintOnes_single]
    omega

end

theorem makeHintY_ct : ConstantTime isa makeHintK.pre makeHintK.pub makeHintAvx2 :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

theorem makeHintY_verified : Verified X86_64.target makeHintAvx2 (makeHintContract X86_64.abi) :=
  Verified.of_correct (fun _ hp => VG.Proof.MlDsa.X86_64.Round.makeHintY_correct hp) VG.Proof.MlDsa.X86_64.Round.makeHintY_ct (by
    round_implies [makeHintContract, makeHintSig, makeHintK, hintK, X86_64.abi, X86_64.argRegs] [hintSat]
      using hintSat)

end VG.Proof.MlDsa.X86_64.Round

end
