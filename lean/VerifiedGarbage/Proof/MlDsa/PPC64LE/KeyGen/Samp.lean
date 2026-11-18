module

public import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
import VerifiedGarbage.Proof.MlDsa.KeyGen.Masked
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Good
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.StepsCT
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Seeds
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.StepsCT
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import all Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.Lay
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.Common
meta import VerifiedGarbage.Proof.MlKem.PPC64LE.SampleCT
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Arith.Common
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Run
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.Offset

/-! ### `MlDsa.PPC64LE.KeyGen.Mask`, which only this module used -/

section

/-!
# ML-DSA key generation on PPC64LE: masking a sampled polynomial

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Samp.lean`): after each sampler,
its result (0 or 1, the low word of `r3`, which `and24` zero-extends) is
ANDed into `r24`, and each coefficient of the polynomial it wrote with
`-r3`: the polynomial is kept if the sampler succeeded, and zeroed if it
failed (`mask_ok`), without a branch.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Proof.MlDsa (coeffAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)

/-! ## Coefficients in memory -/

theorem coeffAt_writeW32 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 256) (hj : j < 256) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega_arith) (by omega_using [hi]) (by omega_using [hj])) (by decide)

/-- A coefficient masked with `-r`, for `r` 0 or 1. -/
theorem and_mask {r : BitVec 64} (hr : r = 0 ∨ r = 1) (x : BitVec 32) :
    (x.setWidth 64 &&& (0 - r)).setWidth 32 = if r = 1 then x else 0 := by
  rcases hr with rfl | rfl
  · simp
  · rw [ifp rfl, show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_toNat_eq
    have := x.isLt
    simp only [BitVec.toNat_setWidth]; omega_using []

/-! ## One coefficient -/

section
variable {s : State} {x c M : BitVec 64}

theorem maskBody_ok (h4 : s.gpr .r4 = x) (h5 : s.gpr .r5 = c) (h12 : s.gpr .r12 = M)
    (ir : InRegions (s.rd ++ s.wr) x 4) (ow : InRegions s.wr x 4) :
    WP isa (.block maskBody) s fun s' =>
      s'.gpr .r4 = x + 4 ∧ s'.gpr .r5 = c - 1 ∧ s'.gpr .r12 = M ∧
      s'.mem = s.mem.writeW x (((s.mem.readW x 32).setWidth 64 &&& M).setWidth 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ ∀ r ∈ preserved, s'.gpr r = s.gpr r := by
  crun [maskBody, h4, h5, h12, ir, ow, preserved, List.forall_mem_cons, List.not_mem_nil, false_imp_iff]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-- After masking `k` coefficients of the polynomial at `P` with `M`. -/
structure MaskInv (P M : Addr) (s₀ : State) (k : Nat) (s : State) : Prop where
  r4 : s.gpr .r4 = P + BitVec.ofNat 64 (4 * k)
  r5 : s.gpr .r5 = BitVec.ofNat 64 (256 - k)
  r12 : s.gpr .r12 = M
  cs : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [reg P 1024] s₀.mem s.mem
  co : ∀ t < 256, coeffAt s.mem P t =
    if t < k then ((coeffAt s₀.mem P t).setWidth 64 &&& M).setWidth 32 else coeffAt s₀.mem P t

theorem mask_step {P M : Addr} {s₀ : State} (cw : Covers [reg P 1024] s₀.wr)
    {k : Nat} (hk : k < 256) {s : State} (h : MaskInv P M s₀ k s) :
    WP isa (.block maskBody) s fun s' => MaskInv P M s₀ (k + 1) s' ∧ (s'.gpr .r5 != 0) = decide (k + 1 ≠ 256) := by
  have cP : (reg P 1024).Contains (P + BitVec.ofNat 64 (4 * k)) 4 := Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  have ow : InRegions s.wr (P + BitVec.ofNat 64 (4 * k)) 4 := by
    rw [h.wr]; exact cw _ _ ⟨_, List.mem_singleton_self _, cP⟩
  have ir : InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 (4 * k)) 4 :=
    let ⟨r, hr, hc⟩ := ow; ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (maskBody_ok h.r4 h.r5 h.r12 ir ow)
    fun s' ⟨r4, r5, r12, m, rd, wr, sp, cs⟩ => ⟨⟨?_, ?_, r12, fun r hr => (cs r hr).trans (h.cs r hr),
      rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [r4]; exact ptr_succ _ 4 k
  · rw [r5]; exact count_sub hk
  · rw [m]; exact h.frame.writeW (List.mem_singleton_self _) _ cP
  · rw [m, coeffAt_writeW32 _ _ ht hk]
    by_cases e : k = t
    · subst e
      have := h.co k hk
      rw [ifn (Nat.lt_irrefl _)] at this
      rw [ifp rfl, ifp (Nat.lt_succ_self _), ← this]; rfl
    · rw [ifn e, h.co t ht]
      by_cases htk : t < k
      · rw [ifp htk, ifp (by omega_using [htk])]
      · rw [ifn htk, ifn (by omega_using [e, htk])]
  · rw [r5, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hk]; exact count_nz hk (by decide)

theorem mask_loop {P M : Addr} {s₀ : State} (cw : Covers [reg P 1024] s₀.wr)
    (h4 : s₀.gpr .r4 = P) (h5 : s₀.gpr .r5 = BitVec.ofNat 64 256) (h12 : s₀.gpr .r12 = M) :
    WP isa (.loop (.block maskBody) (.nonzero .d .r5)) s₀ fun s =>
      Kept [reg P 1024] s₀ s ∧ ∀ t < 256, coeffAt s.mem P t = ((coeffAt s₀.mem P t).setWidth 64 &&& M).setWidth 32 :=
  wp_loop_nz (MaskInv P M s₀) (N := 256) (by decide) (fun k hk s h => mask_step cw hk h)
    (fun s h => ⟨⟨h.cs, h.sp, h.rd, h.wr, h.frame⟩, fun t ht => by rw [h.co t ht, ifp ht]⟩)
    ⟨by rw [h4]; simp, by rw [h5], h12, fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _,
      fun t _ => by rw [ifn (Nat.not_lt_zero t)]⟩

/-! ## The polynomial -/

abbrev maskPre (a : Ptr) : List Instr :=
  ([.li .r12 0, .sub .r12 .r12 .r3] : List Instr) ++ Arg.instrs .r4 (.ptr a) ++ ([.li .r5 256] : List Instr)

theorem maskPre_ok {a : Ptr} (ha : argOk (.ptr a) = true) (s : State) :
    WP isa (.block (maskPre a)) s fun s' =>
      Only s s' ∧ s'.gpr .r12 = 0 - s.gpr .r3 ∧ s'.gpr .r4 = s.gpr a.1 + BitVec.ofNat 64 a.2 ∧
        s'.gpr .r5 = BitVec.ofNat 64 256 := by
  have hb := baseReg_of ha
  have ha2 : a.2 < 2 ^ 31 := by simp only [argOk, Bool.and_eq_true, decide_eq_true_eq] at ha; exact ha.2
  have hn : a.1 ≠ .r4 ∧ a.1 ≠ .r5 ∧ a.1 ≠ .r12 := by
    simp only [baseReg, Bool.or_eq_true, beq_iff_eq] at hb
    rcases hb with ((h | h) | h) | h <;> rw [h] <;> decide
  rw [maskPre, WP.block_append_iff, WP.block_append_iff]
  refine WP.cons (exec_li (by decide)) (WP.cons exec_sub (wp_nil ?_))
  refine WP.mono (arg_ok .r4 ha (argOk_ne (by decide) ha) _) fun s1 e1 => ?_
  subst e1
  refine WP.cons (exec_li (by decide)) (wp_nil ⟨⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩)
  · have : r ≠ .r12 ∧ r ≠ .r4 ∧ r ≠ .r5 := by revert r; decide
    simp only [RegUpd.gpr_write, this.1, this.2.1, this.2.2, ite_false]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.ofNat_eq_ofNat]
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, argVal, hn.2.2]
  · simp only [RegUpd.gpr_write, ite_true]

theorem mask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a : Ptr}
    (pa : PtrIn L a 1024) (hw : ix a.1 ∈ Wb) (hr : s.gpr .r3 = 0 ∨ s.gpr .r3 = 1) :
    WP isa (mask a) s fun s' => Kept (L.RL [tri a 1024]) s s' ∧
      ∀ t < 256, coeffAt s'.mem (lpa L a) t = if s.gpr .r3 = 1 then coeffAt s.mem (lpa L a) t else 0 := by
  have gb := hs.val pa.1
  simp only [argVal] at gb
  have cw := hs.cwE pa hw
  unfold mask
  refine WP.seq (WP.mono (maskPre_ok pa.1 s) fun s₁ ⟨o₁, g12, g4, g5⟩ => ?_)
  rw [gb] at g4
  refine WP.mono (mask_loop (by rw [o₁.wr]; exact cw) g4 g5 g12) fun s' ⟨k, co⟩ => ⟨?_, fun t ht => ?_⟩
  · exact (o₁.kept _).trans k
  · rw [co t ht, o₁.mem, and_mask hr]

end VG.Proof.MlDsa.PPC64LE.KeyGen

end

end

/-! ### `MlDsa.PPC64LE.KeyGen.SeedsCT`, which this module and modules that import it used -/

section

/-!
# ML-DSA key generation on PPC64LE: the seeds leak nothing

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Samp.lean`): two runs of the
seeds in the same layout leak the same (`seeds_two`): the bytes `k` and `ℓ`
are public, and every access is through the pointers of the layout; which
gives the piece of the seeds (`seeds_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa (Params)

/-- Two runs whose entry states have the same layout. -/
def KTwo (p : Params) (STK : Nat) (x y : State) : Prop := ∃ σ, Two (lay p STK σ) kWb STK x y

theorem kc_twoL {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : kgPub p σ₁ σ₂) (h₁ : KC p STK σ₁ x)
    (h₂ : KC p STK σ₂ y) : Two (lay p STK σ₁) kWb STK x y :=
  ⟨h₁.site, lay_pub pub ▸ h₂.site, by rw [h₁.sp, h₂.sp, pub.1]⟩

theorem kc_two {p : Params} {STK : Nat} {σ₁ σ₂ x y : State} (pub : kgPub p σ₁ σ₂) (h₁ : KC p STK σ₁ x)
    (h₂ : KC p STK σ₂ y) : KTwo p STK x y :=
  ⟨σ₁, kc_twoL pub h₁ h₂⟩

/-- A part that leaks the same in two runs in every layout of key generation. -/
theorem ktwo {p : Params} {STK : Nat} {c : Prog isa}
    (h : ∀ σ, RelCT isa (Two (lay p STK σ) kWb STK) c fun _ _ => True) : RelCT isa (KTwo p STK) c fun _ _ => True :=
  RelCT.exists_ h

theorem setKL_taint : ∀ v < 16, ∀ w < 16, (VG.PPC64LE.taint.check (Taint.ofRegs [.r31])
    (.block (setB (sc oKL) v ++ setB (sc (oKL + 1)) w)) (.block [])).isSome = true := by decide +kernel

theorem seeds_two {p : Params} (hF : PFacts p) {STK : Nat} (σ : State) :
    RelCT isa (Two (lay p STK σ) kWb STK) (seeds p) fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  have hP : ∀ x y, Two (lay p STK σ) kWb STK x y → Two (lay p STK σ) kWb STK x y := fun _ _ h => h
  unfold seeds
  refine RelCT.seq (RelCT.two hP (taint31 hP (setKL_taint p.k (by omega_using [hk]) p.ℓ (by omega_using [hl]))) fun x hs => ?_) ?_
  · refine WP.block_append (WP.mono (setB_ok hs (q := sc oKL) ⟨sc_ok (by decide), by lsep hF⟩ (by decide) (by decide)
      (v := p.k) (by omega_using [hk])) fun s₁ ⟨k₁, _⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oKL + 1))
        ⟨sc_ok (by decide), by lsep hF⟩ (by decide) (by decide) (v := p.ℓ) (by omega_using [hl])) fun s₂ ⟨k₂, _⟩ =>
          ⟨_, (k₁.monoL (W' := [tri (sc oKL) 1, tri (sc (oKL + 1)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩)
  have hin : ∀ s, Site (lay p STK σ) kWb STK s → ∀ pc ∈ ([⟨.r30, 0, 32⟩, ⟨.r31, oKL, 2⟩] : List Impl.MlKem.PPC64LE.Piece),
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s false pc := fun s hs pc hpc => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpc
    rcases hpc with rfl | rfl
    · exact pieceS hs rfl (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inr rfl) fun h => absurd h (by decide)
    · exact pieceS hs rfl (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size])
        (.inl rfl) fun h => absurd h (by decide)
  have hq : ∀ s, Site (lay p STK σ) kWb STK s →
      PieceOk (hashLay (lay p STK σ) s fun _ => true) ix s true (⟨.r31, oHX, 128⟩ : Impl.MlKem.PPC64LE.Piece) :=
    fun s hs => pieceS hs rfl (by decide) (by decide) (by decide) (by lsep hF [hashLay, Lay.size]) (.inl rfl)
      fun _ => by decide
  refine RelCT.seq (RelCT.two hP (hashS_tr ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide)
    (by simp) hin hq hP) fun x hs => WP.mono (hashS hs ktrue (rate := 136) (sfx := 0x1f) (by decide) (by decide)
      (by simp) (hin x hs) (hq x hs)) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (taint31 hP (by taint_decide)) fun x hs =>
    WP.mono (copyS hs (sb := .r31) (so := oHX) (db := .r31) (dO := oSA) (len := 32) ⟨by decide, by lsep hF⟩
      ⟨by decide, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (RelCT.two hP (taint31 hP (by taint_decide)) fun x hs =>
    WP.mono (copyS hs (sb := .r31) (so := oHX + 32) (db := .r31) (dO := oSB) (len := 64) ⟨by decide, by lsep hF⟩
      ⟨by decide, by lsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by lsep hF))
      fun _ h => ⟨_, h.1⟩) ?_
  exact taint31 hP (by taint_decide)

theorem seeds_piece {p : Params} (hF : PFacts p) {STK : Nat} :
    KPiece p STK (fun σ s => KC p STK σ s ∧ s.gpr .r24 = 1) (fun σ s => K1 p STK σ s ∧ s.gpr .r24 = 1) (seeds p) :=
  ⟨fun _ _ _ h => seeds_ok hF h.1 h.2,
    rel_of (ktwo fun σ => seeds_two hF σ) fun _ _ _ _ _ _ pub h₁ h₂ => kc_two pub h₁.1 h₂.1⟩

end VG.Proof.MlDsa.PPC64LE.KeyGen

end

end

/-!
# ML-DSA key generation on PPC64LE: the samplers

As on 32-bit ARM (`Proof/MlDsa/Arm/KeyGen/Samp.lean`): the primitives key
generation calls, verified with at most `S` bytes of stack (`PrimsOk`); and
the entries of `Â` (`expA_piece`) and of `s₁ ‖ s₂` (`expS_piece`): after the
first `e` entries of `Â` and `r` of `s₁ ‖ s₂` (`KSamp`), each polynomial is
reduced (and those of `s₁ ‖ s₂` small), and `r24` is 0 or 1, with its low
word what `Good` says. A sampler's result is the low word of `r3`, which
`and24` zero-extends before it ANDs it into `r24`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.KeyGen

open VG VG.PPC64LE VG.PPC64LE.RegUpd VG.Proof.MlKem.PPC64LE
open VG.Impl.MlDsa.PPC64LE.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly rejBoundedPoly toRq Outcome)
open VG.Proof.MlDsa (polyAt coeffAt Reduced PolyIs)
open VG.Proof.MlDsa.KeyGen (seedA seedS Small Good ifp ifn seedA_eq seedS_eq)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure PrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => Proof.MlDsa.nttContract PPC64LE.abi stk) S
  invNtt : Callee P.invNtt (fun stk => Proof.MlDsa.nttInvContract PPC64LE.abi stk) S
  mul : Callee P.mul (fun stk => Proof.MlDsa.mulContract PPC64LE.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => Proof.MlDsa.mulAddContract PPC64LE.abi stk) S
  add : Callee P.add (fun stk => Proof.MlDsa.addContract PPC64LE.abi stk) S
  rejNtt : Callee P.rejNtt (fun stk => Proof.MlDsa.rejNTTContract PPC64LE.abi stk) S
  rejBounded : Callee P.rejBounded (fun stk => Proof.MlDsa.rejBoundedContract PPC64LE.abi stk) S
  power2Round : Callee P.power2Round (fun stk => Proof.MlDsa.power2RoundContract PPC64LE.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => Proof.MlDsa.simpleBitPackContract PPC64LE.abi stk) S
  bitPack : Callee P.bitPack (fun stk => Proof.MlDsa.bitPackContract PPC64LE.abi stk) S

theorem oP_lt {j : Nat} (h : j < 128) : oP j < 2 ^ 31 := by unfold oP; omega_arith

/-! ## `r24` -/

/-- A result, zero-extended. -/
abbrev zx (x : BitVec 64) : BitVec 64 := (x.setWidth 32).setWidth 64

/-- `s'` differs from `s` only in `r3` and `r24`. -/
structure Regs2 (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .r3 → r ≠ .r24 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem and24_ok (s : State) :
    WP isa (.block and24) s fun s' => s'.gpr .r3 = zx (s.gpr .r3) ∧ s'.gpr .r24 = s.gpr .r24 &&& zx (s.gpr .r3) ∧
      Regs2 s s' := by
  crun [and24]
  refine ⟨?_, ?_, ⟨fun r h3 h24 => ?_, rfl, rfl, rfl, rfl⟩⟩
  · simp
  · simp
  · simp [h3, h24]

theorem Site.regs2 {L : Lay} {Wb : List Nat} {STK : Nat} {s s' : State} (h : Site L Wb STK s) (hr : Regs2 s s') :
    Site L Wb STK s' :=
  ⟨h.ok, h.len, h.w0, h.w1, h.sz0, h.sz1, by rw [hr.sp]; exact h.p1, h.s48, by rw [hr.sp]; exact h.spk,
    by rw [hr.gpr _ (by decide) (by decide)]; exact h.r31, by rw [hr.gpr _ (by decide) (by decide)]; exact h.r30,
    by rw [hr.gpr _ (by decide) (by decide)]; exact h.r29, by rw [hr.gpr _ (by decide) (by decide)]; exact h.r28,
    by rw [hr.wr]; exact h.cw, by rw [hr.wr, hr.rd]; exact h.cr⟩

theorem K1.regs2 {p : Params} {STK : Nat} {σ s s' : State} (h : K1 p STK σ s) (hr : Regs2 s s') : K1 p STK σ s' :=
  ⟨⟨h.kc.site.regs2 hr, hr.rd.trans h.kc.rd, hr.wr.trans h.kc.wr, hr.sp.trans h.kc.sp,
    fun r hp hs => by
      have : r ≠ .r3 ∧ r ≠ .r24 := ⟨fun e => by subst e; simp [preserved] at hp,
        fun e => by subst e; simp [savedTop] at hs⟩
      rw [hr.gpr r this.1 this.2]; exact h.kc.pres r hp hs,
    by rw [hr.mem]; exact h.kc.sav, by rw [hr.mem]; exact h.kc.xi⟩,
    by rw [hr.mem]; exact h.hx, by rw [hr.mem]; exact h.sa, by rw [hr.mem]; exact h.sb, by rw [hr.mem]; exact h.z⟩

theorem zx_01 {x : BitVec 64} (h : x.setWidth 32 = 0 ∨ x.setWidth 32 = 1) : zx x = 0 ∨ zx x = 1 := by
  rcases h with h | h <;> rw [zx, h]
  · exact .inl rfl
  · exact .inr rfl

theorem zx_one {x : BitVec 64} (h : x.setWidth 32 = 0 ∨ x.setWidth 32 = 1) : zx x = 1 ↔ x.setWidth 32 = 1 := by
  rcases h with h | h <;> rw [zx, h] <;> decide

theorem and_zx {a x : BitVec 64} (ha : a = 0 ∨ a = 1) (hx : x.setWidth 32 = 0 ∨ x.setWidth 32 = 1) :
    (a &&& zx x = 0 ∨ a &&& zx x = 1) ∧ (a &&& zx x).setWidth 32 = a.setWidth 32 &&& x.setWidth 32 := by
  rcases ha with rfl | rfl <;> rcases hx with h | h <;> simp only [zx, h] <;> decide

/-! ## What the samplers leave -/

/-- After the first `e` entries of `Â` and `r` of `s₁ ‖ s₂`. -/
structure KSamp (p : Params) (STK : Nat) (σ : State) (e r : Nat) (s : State) : Prop where
  k1 : K1 p STK σ s
  r24 : s.gpr .r24 = 0 ∨ s.gpr .r24 = 1
  ex : ∃ (A : Nat → Poly) (S : Nat → IPoly), (∀ e' < e, PolyIs s.mem ((lay p STK σ).A 0 (oP e')) (A e')) ∧
    (∀ r' < r, PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r'))) (toRq (S r')) ∧ Small p.η (S r')) ∧
    Good p (xiOf σ) e r A S ((s.gpr .r24).setWidth 32)

/-- A part that keeps `K1`, the polynomials sampled so far and `r24` keeps `KSamp`. -/
theorem KSamp.keep {p : Params} {STK : Nat} {σ : State} {e r : Nat} {s s' : State} (h : KSamp p STK σ e r s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((lay p STK σ).RL W) s s') (hc : k1Chk p STK W = true)
    (ha : ∀ e' < e, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP e', 1024) W = true)
    (hs : ∀ r' < r, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (0, oP (p.k * p.ℓ + r'), 1024) W = true) :
    KSamp p STK σ e r s' := by
  have hL := h.k1.kc.site.ok
  obtain h24 : s'.gpr .r24 = s.gpr .r24 := hk.cs .r24 (by decide)
  obtain ⟨A, S, hA, hS, hG⟩ := h.ex
  refine ⟨h.k1.keep hk hc, by rw [h24]; exact h.r24, A, S, fun e' he' => ?_, fun r' hr' => ?_, by rw [h24]; exact hG⟩
  · exact polyIs_keepW hL hk.frame (ha e' he') (by decide) rfl (hA e' he')
  · exact ⟨polyIs_keepW hL hk.frame (hs r' hr') (by decide) rfl (hS r' hr').1, (hS r' hr').2⟩

theorem KSamp.zero {p : Params} {STK : Nat} {σ s : State} (h : K1 p STK σ s) (h24 : s.gpr .r24 = 1) :
    KSamp p STK σ 0 0 s :=
  ⟨h, .inr h24, fun _ => Vector.replicate 256 0, fun _ => Vector.replicate 256 0,
    fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h24]; exact Proof.MlDsa.KeyGen.good_zero _ _ _ _⟩

/-! ## A sampled polynomial, masked -/

/-- `and24` and `mask`, after a sampler whose result, the low word of `r3`, is 0 or 1. -/
theorem andMask_ok {L : Lay} {Wb : List Nat} {STK : Nat} {s : State} (hs : Site L Wb STK s) {a : Ptr}
    (pa : PtrIn L a 1024) (hw : ix a.1 ∈ Wb) (hr : (s.gpr .r3).setWidth 32 = 0 ∨ (s.gpr .r3).setWidth 32 = 1) :
    WP isa (.seq (.block and24) (mask a)) s fun s' => ∃ s₁, Regs2 s s₁ ∧
      Kept (L.RL [tri a 1024]) s₁ s' ∧ s'.gpr .r24 = s.gpr .r24 &&& zx (s.gpr .r3) ∧
      ∀ t < 256, coeffAt s'.mem (lpa L a) t =
        if (s.gpr .r3).setWidth 32 = 1 then coeffAt s.mem (lpa L a) t else 0 := by
  refine WP.seq (WP.mono (and24_ok s) fun s₁ ⟨g3, g24, r₁⟩ => ?_)
  refine WP.mono (mask_ok (hs.regs2 r₁) pa hw (by rw [g3]; exact zx_01 hr)) fun s' ⟨k, co⟩ =>
    ⟨s₁, r₁, k, by rw [k.cs .r24 (by decide), g24], fun t ht => ?_⟩
  rw [co t ht, g3, r₁.mem]
  by_cases h1 : (s.gpr .r3).setWidth 32 = 1
  · rw [ifp ((zx_one hr).mpr h1), ifp h1]
  · rw [ifn (fun e => h1 ((zx_one hr).mp e)), ifn h1]

/-- What a sampler and its mask leave in entry `j` of the polynomials, from
the facts the sampler's contract gives. -/
theorem masked_poly {m m' : Mem} {q : Addr} {r : BitVec 32} (hred : r = 1 → Reduced m q)
    (h : ∀ i < 256, coeffAt m' q i = if r = 1 then coeffAt m q i else 0) :
    PolyIs m' q (polyAt m' q) ∧ (r = 1 → polyAt m' q = polyAt m q) ∧
      (r ≠ 1 → PolyIs m' q (toRq (Vector.replicate 256 0))) := by
  by_cases h1 : r = 1
  · have := Proof.MlDsa.KeyGen.masked_one h1 h
    exact ⟨⟨this.2 (hred h1), rfl⟩, fun _ => this.1, fun h => absurd h1 h⟩
  · have := Proof.MlDsa.KeyGen.masked_zero h1 h
    exact ⟨⟨this.1, rfl⟩, fun h => absurd h h1, fun _ => this⟩

/-! ## An entry of `Â` -/

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- The call of `RejNTTPoly`. -/
theorem rnA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (hs : Site (lay p STK σ) kWb STK s) {Q : State → Prop}
    (hQ : ∀ s', Kept ((lay p STK σ).RL [tri (aP e) 1024, tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem ((lay p STK σ).A 0 (oP e))) →
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem ((lay p STK σ).A 0 oSA) 34)) ((s'.gpr .r3).setWidth 32)
        (polyAt s'.mem ((lay p STK σ).A 0 (oP e))) → Q s') :
    WP isa (rejNttAt P (sc oSA) (aP e)) s Q := by
  have := hF.kl; have := hF.l; have := hF.k
  exact rn_ok hP.rejNtt hs hS (sd := sc oSA) (a := aP e) (w := sc oSS)
    ⟨⟨sc_ok (by decide), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (by decide), by lsep hF⟩,
      show ix Reg.r31 ∈ kWb by decide, show ix Reg.r31 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩ hQ

theorem expA_ok {e : Nat} (he : e < p.k * p.ℓ) {σ s : State} (h : KSamp p STK σ e 0 s) :
    WP isa (expA P p e) s (KSamp p STK σ (e + 1) 0) := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  obtain hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_arith)
  have hs := h.k1.kc.site
  unfold expA sampled
  -- `s` and `r` to the seed
  refine WP.seq (WP.block_append (WP.mono (setB_ok hs (q := sc (oSA + 32)) ⟨sc_ok (by decide), by lsep hF⟩
    (by decide) (by decide) (v := e % p.ℓ) (by omega_arith)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁)
      (q := sc (oSA + 33)) ⟨sc_ok (by decide), by lsep hF⟩ (by decide) (by decide) (v := e / p.ℓ) (by omega_arith))
      fun s₂ ⟨k₂, b₂⟩ => ?_))
  obtain h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _))
  obtain h₂ := h₁.keep k₂ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _))
  have hs₂ := h₂.k1.kc.site
  obtain hseed : bytesAt s₂.mem ((lay p STK σ).A 0 oSA) 34 = seedA (rhoOf p σ) (e / p.ℓ) (e % p.ℓ) := by
    obtain b₁' := bytes_keepW hs.ok k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₂.k1.sa,
      seedA_eq, List.append_assoc]
    refine congrArg _ ?_
    obtain e1 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 33)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
    simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
    rw [e1, e2]; rfl
  -- the call
  refine WP.seq (rnA_ok hP hF hS he hs₂ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  obtain hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  obtain hs₃ := hs₂.kept k₃
  -- the result and the mask
  refine WP.mono (andMask_ok hs₃ (a := aP e) ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩ (show ix Reg.r31 ∈ kWb by decide) hr01)
    fun s₄ ⟨s₅, r₅, k₄, r₄, co⟩ => ?_
  obtain h₃ := h₂.keep k₃ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF)
    (fun _ h => absurd h (Nat.not_lt_zero _))
  obtain ⟨A, S', hA, _, hG⟩ := h₃.ex
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  obtain ⟨a01, aeq⟩ := and_zx h₃.r24 hr01
  have hL := hs.ok
  refine ⟨(h₃.k1.regs2 r₅).keep k₄ (by lsep hF [k1Chk, kcChk]), by rw [r₄]; exact a01,
    fun e' => if e' = e then polyAt s₄.mem ((lay p STK σ).A 0 (oP e)) else A e', S', fun e' he' => ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
  · dsimp only
    rcases (by omega_arith : e' < e ∨ e' = e) with he' | rfl
    · rw [ifn (by omega_arith)]
      have := polyIs_keepW hL k₄.frame (i := 0) (o := oP e') (by lsep hF) (by decide) rfl
        (show PolyIs s₅.mem _ _ by rw [r₅.mem]; exact hA e' he')
      exact this
    · rw [ifp rfl]; exact pi
  · rw [r₄, aeq]; exact Proof.MlDsa.KeyGen.good_A he hG hout p1

/-! ## An entry of `s₁ ‖ s₂` -/

omit hP hS in
theorem eta_of : p.η = 2 ∨ p.η = 4 := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩
  exacts [.inl h, .inr h]

/-- The call of `RejBoundedPoly`. -/
theorem rbS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (hs : Site (lay p STK σ) kWb STK s)
    {Q : State → Prop}
    (hQ : ∀ s', Kept ((lay p STK σ).RL [tri (sP p r) 1024, tri (sc oSS) 2048, (1, 0, STK)]) s s' →
      ((s'.gpr .r3).setWidth 32 = 1 → Reduced s'.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) →
      Outcome (fun b => (rejBoundedPoly p.η b.rejBounded (bytesAt s.mem ((lay p STK σ).A 0 oSB) 66)).map toRq)
        ((s'.gpr .r3).setWidth 32) (polyAt s'.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) → Q s') :
    WP isa (rejBoundedAt P (sc oSB) p.η (sP p r)) s Q := by
  have := hF.kl; have := hF.l; have := hF.k
  exact rb_ok hP.rejBounded hs hS (sd := sc oSB) (a := sP p r) (w := sc oSS)
    ⟨⟨sc_ok (by decide), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (by decide), by lsep hF⟩,
      show ix Reg.r31 ∈ kWb by decide, show ix Reg.r31 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
    (eta_of hF) hQ

theorem expS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ s : State} (h : KSamp p STK σ (p.k * p.ℓ) r s) :
    WP isa (expS P p r) s (KSamp p STK σ (p.k * p.ℓ) (r + 1)) := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.k1.kc.site
  unfold expS sampled
  refine WP.seq (WP.mono (setB_ok hs (q := sc (oSB + 64)) ⟨sc_ok (by decide), by lsep hF⟩ (by decide) (by decide)
    (v := r) (by omega_arith)) fun s₁ ⟨k₁, b₁⟩ => ?_)
  obtain h₁ := h.keep k₁ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
  have hs₁ := h₁.k1.kc.site
  obtain hseed : bytesAt s₁.mem ((lay p STK σ).A 0 oSB) 66 = seedS (rho'Of p σ) r := by
    rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, h₁.k1.sb,
      seedS_eq _ (by omega_arith), List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₁.mem ((lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
    have e2 : bytesAt s₁.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] := h₁.k1.z
    simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
    rw [e1, e2]; rfl
  refine WP.seq (rbS_ok hP hF hS hr hs₁ fun s₃ k₃ hred hout => ?_)
  rw [hseed] at hout
  obtain hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  obtain hs₃ := hs₁.kept k₃
  refine WP.mono (andMask_ok hs₃ (a := sP p r) ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩ (show ix Reg.r31 ∈ kWb by decide)
    hr01) fun s₄ ⟨s₅, r₅, k₄, r₄, co⟩ => ?_
  obtain h₃ := h₁.keep k₃ (by lsep hF [k1Chk, kcChk]) (fun e' he' => by lsep hF) (fun r' hr' => by lsep hF)
  obtain ⟨A, S', hA, hS', hG⟩ := h₃.ex
  obtain ⟨pi, p1, p0⟩ := masked_poly hred co
  obtain ⟨z, hz, hz1, hz0, hG'⟩ := Proof.MlDsa.KeyGen.good_S hr hG hout
  obtain ⟨a01, aeq⟩ := and_zx h₃.r24 hr01
  have hL := hs.ok
  refine ⟨(h₃.k1.regs2 r₅).keep k₄ (by lsep hF [k1Chk, kcChk]), by rw [r₄]; exact a01, A,
    fun r' => if r' = r then z else S' r', fun e' he' => ?_, fun r' hr' => ?_, by rw [r₄, aeq]; exact hG'⟩
  · exact polyIs_keepW hL k₄.frame (i := 0) (o := oP e') (by lsep hF) (by decide) rfl
      (show PolyIs s₅.mem _ _ by rw [r₅.mem]; exact hA e' he')
  dsimp only
  rcases (by omega_arith : r' < r ∨ r' = r) with hr' | rfl
  · rw [ifn (by omega_arith)]
    exact ⟨polyIs_keepW hL k₄.frame (i := 0) (o := oP (p.k * p.ℓ + r')) (by lsep hF) (by decide) rfl
      (show PolyIs s₅.mem _ _ by rw [r₅.mem]; exact (hS' r' hr').1), (hS' r' hr').2⟩
  · rw [ifp rfl]
    refine ⟨?_, hz⟩
    show PolyIs s₄.mem (lpa (lay p STK σ) (sP p r')) (toRq z)
    by_cases h1 : (s₃.gpr .r3).setWidth 32 = 1
    · rw [hz1 h1, ← p1 h1]; exact pi
    · rw [hz0 h1]; exact p0 h1

/-! ## Constant time -/

omit hP hF hS in
theorem rho_pub {σ₁ σ₂ : State} (pub : kgPub p σ₁ σ₂) : rhoOf p σ₁ = rhoOf p σ₂ :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).1

omit hP hF hS in
theorem rej_pub {σ₁ σ₂ : State} (pub : kgPub p σ₁ σ₂) {r : Nat} (hr : r < p.ℓ + p.k) :
    Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₁) r) = Spec.MlDsa.rejBoundedLeak p.η (seedS (rho'Of p σ₂) r) :=
  (Proof.MlDsa.KeyGen.keyGenLeak_split pub.2.2.2.2.2).2 r hr

omit hP hF hS in
theorem setIJ_taint : ∀ v < 8, ∀ w < 8, (VG.PPC64LE.taint.check (Taint.ofRegs [.r31])
    (.block (setB (sc (oSA + 32)) v ++ setB (sc (oSA + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
theorem setS_taint : ∀ v < 16, (VG.PPC64LE.taint.check (Taint.ofRegs [.r31]) (.block (setB (sc (oSB + 64)) v))
    (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
/-- The check is the same for every offset: its hint is computed once. -/
theorem andMask_taint : ∀ j < 128, (VG.PPC64LE.taint.check (Taint.ofRegs [.r31])
    (.seq (.block and24) (mask (sc (oP j))))
    (VG.Taint.hintOf VG.PPC64LE.taint (Taint.ofRegs [.r31]) (.seq (.block and24) (mask (sc 0))))).isSome = true := by
  decide +kernel

theorem expA_two {e : Nat} (he : e < p.k * p.ℓ) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32) (expA P p e)
      fun _ _ => True := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain hq : e / p.ℓ < p.k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he)
  obtain hr : e % p.ℓ < p.ℓ := Nat.mod_lt _ (by omega_arith)
  unfold expA sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    bytesAt x'.mem ((lay p STK σ).A 0 oSA) 34 = bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 ++
      [BitVec.ofNat 8 (e % p.ℓ), BitVec.ofNat 8 (e / p.ℓ)]
  obtain hF1 : ∀ x, Site (lay p STK σ) kWb STK x →
      WP isa (.block (setB (sc (oSA + 32)) (e % p.ℓ) ++ setB (sc (oSA + 33)) (e / p.ℓ))) x (F x) := fun x hs =>
    WP.block_append (WP.mono (setB_ok hs (q := sc (oSA + 32)) ⟨sc_ok (by decide), by lsep hF⟩ (by decide) (by decide)
      (v := e % p.ℓ) (by omega_arith)) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSA + 33))
        ⟨sc_ok (by decide), by lsep hF⟩ (by decide) (by decide) (v := e / p.ℓ) (by omega_arith)) fun s₂ ⟨k₂, b₂⟩ =>
        ⟨⟨_, (k₁.monoL (W' := [tri (sc (oSA + 32)) 1, tri (sc (oSA + 33)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩,
        by
        have hL := hs.ok
        obtain b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSA + 32) (l := 1) (by lsep hF) (by decide) (by decide)
        obtain b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide)).trans
          (bytes_keepW hL k₁.frame (i := 0) (o := oSA) (l := 32) (by lsep hF) (by decide) (by decide))
        rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          List.append_assoc]
        refine congrArg _ ?_
        obtain e1 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 32)) 1 = [BitVec.ofNat 8 (e % p.ℓ)] := b₁'.trans b₁
        have e2 : bytesAt s₂.mem ((lay p STK σ).A 0 (oSA + 33)) 1 = [BitVec.ofNat 8 (e / p.ℓ)] := b₂
        simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
        rw [e1, e2]; rfl⟩)
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32)
    (taint31 (fun _ _ h => h.1) (setIJ_taint _ (by omega_arith) _ (by omega_arith))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (lay p STK σ) kWb STK x y ∧
        bytesAt x.mem ((lay p STK σ).A 0 oSA) 34 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 34)
      fun x' y' ⟨_, x, y, ⟨T, e32⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx, by', e32]⟩) ?_
  obtain ok := fun x (hs : Site (lay p STK σ) kWb STK x) =>
    rnA_ok hP hF hS he hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (rn_tr hP.rejNtt hS (sd := sc oSA) (a := aP e) (w := sc oSS)
      ⟨⟨sc_ok (by decide), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (by decide), by lsep hF⟩,
        show ix Reg.r31 ∈ kWb by decide, show ix Reg.r31 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint31 (fun _ _ h => h) (andMask_taint _ (by omega_arith))

theorem expA_tr {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (Rel2 (Pre p STK) (kgPub p) fun σ s => KSamp p STK σ e 0 s) (expA P p e) fun _ _ => True :=
  rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 oSA) 32 = bytesAt y.mem ((lay p STK σ).A 0 oSA) 32)
    (RelCT.exists_ fun σ => expA_two hP hF hS he σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
      ⟨σ₁, kc_twoL pub h₁.k1.kc h₂.k1.kc, by
        rw [h₁.k1.sa, lay_pub pub, h₂.k1.sa, rho_pub pub]⟩

theorem expS_two {r : Nat} (hr : r < p.ℓ + p.k) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧ bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      bytesAt y.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((lay p STK σ).A 0 oSB) 64) r)) (expS P p r)
      fun _ _ => True := by
  obtain hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold expS sampled
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    (bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] →
      bytesAt x'.mem ((lay p STK σ).A 0 oSB) 66 = seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r)
  obtain hF1 : ∀ x, Site (lay p STK σ) kWb STK x → WP isa (.block (setB (sc (oSB + 64)) r)) x (F x) := fun x hs =>
    WP.mono (setB_ok hs (q := sc (oSB + 64)) ⟨sc_ok (by decide), by lsep hF⟩ (by decide) (by decide) (v := r)
      (by omega_arith)) fun x' ⟨k₁, b₁⟩ =>
      ⟨⟨_, k₁⟩, fun hz => by
        have hL := hs.ok
        obtain b₀ := bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 64) (by lsep hF) (by decide) (by decide)
        obtain b₂ := bytes_keepW hL k₁.frame (i := 0) (o := oSB + 65) (l := 1) (by lsep hF) (by decide) (by decide)
        rw [show (66 : Nat) = 64 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          seedS_eq _ (by omega_arith), List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt x'.mem ((lay p STK σ).A 0 (oSB + 64)) 1 = [BitVec.ofNat 8 r] := b₁
        obtain e2 : bytesAt x'.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] := b₂.trans hz
        simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add] at e1 e2 ⊢
        rw [e1, e2]; rfl⟩
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (lay p STK σ) kWb STK x y ∧
      bytesAt x.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧ bytesAt y.mem ((lay p STK σ).A 0 (oSB + 65)) 1 = [0] ∧
      Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt x.mem ((lay p STK σ).A 0 oSB) 64) r) =
        Spec.MlDsa.rejBoundedLeak p.η (seedS (bytesAt y.mem ((lay p STK σ).A 0 oSB) 64) r))
    (taint31 (fun _ _ h => h.1) (setS_taint _ (by omega_arith))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (lay p STK σ) kWb STK x y ∧
        Spec.MlDsa.rejBoundedLeak p.η (bytesAt x.mem ((lay p STK σ).A 0 oSB) 66) =
          Spec.MlDsa.rejBoundedLeak p.η (bytesAt y.mem ((lay p STK σ).A 0 oSB) 66))
      fun x' y' ⟨_, x, y, ⟨T, zx, zy, hl⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx zx, by' zy, hl]⟩) ?_
  obtain ok := fun x (hs : Site (lay p STK σ) kWb STK x) =>
    rbS_ok hP hF hS hr hs (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (RelCT.two (fun _ _ h => h.1) (rb_tr hP.rejBounded hS (sd := sc oSB) (a := sP p r)
      (w := sc oSS) ⟨⟨sc_ok (by decide), by lsep hF⟩, ⟨sc_ok (oP_lt (by omega_arith)), by lsep hF⟩, ⟨sc_ok (by decide), by lsep hF⟩,
        show ix Reg.r31 ∈ kWb by decide, show ix Reg.r31 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩
      (eta_of hF) fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint31 (fun _ _ h => h) (andMask_taint _ (by omega_arith))

theorem expS_tr {r : Nat} (hr : r < p.ℓ + p.k) :
    RelCT isa (Rel2 (Pre p STK) (kgPub p) fun σ s => KSamp p STK σ (p.k * p.ℓ) r s) (expS P p r)
      fun _ _ => True :=
  rel_of (RelCT.exists_ fun σ => expS_two hP hF hS hr σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
    ⟨σ₁, kc_twoL pub h₁.k1.kc h₂.k1.kc, h₁.k1.z, by rw [lay_pub pub]; exact h₂.k1.z, by
      rw [h₁.k1.sb, lay_pub pub, h₂.k1.sb]; exact rej_pub pub hr⟩

/-! ## The pieces -/

theorem expA_piece {e : Nat} (he : e < p.k * p.ℓ) :
    KPiece p STK (fun σ s => KSamp p STK σ e 0 s) (fun σ s => KSamp p STK σ (e + 1) 0 s) (expA P p e) :=
  ⟨fun _ _ _ h => expA_ok hP hF hS he h, expA_tr hP hF hS he⟩

theorem expS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) r s) (fun σ s => KSamp p STK σ (p.k * p.ℓ) (r + 1) s)
      (expS P p r) :=
  ⟨fun _ _ _ h => expS_ok hP hF hS hr h, expS_tr hP hF hS hr⟩

/-- The entries of `Â`. -/
theorem sampA_piece :
    KPiece p STK (fun σ s => K1 p STK σ s ∧ s.gpr .r24 = 1) (fun σ s => KSamp p STK σ (p.k * p.ℓ) 0 s)
      (seqR (expA P p) 0 (p.k * p.ℓ)) := by
  refine Piece.mono (Piece.seqR (I := fun e σ s => KSamp p STK σ e 0 s) (p.k * p.ℓ) 0
    fun e _ he => expA_piece hP hF hS (by omega_arith)) (fun σ s _ h => KSamp.zero h.1 h.2) fun σ s _ h => ?_
  simpa using h

/-- The entries of `s₁ ‖ s₂`. -/
theorem sampS_piece :
    KPiece p STK (fun σ s => KSamp p STK σ (p.k * p.ℓ) 0 s) (fun σ s => KSamp p STK σ (p.k * p.ℓ) (p.ℓ + p.k) s)
      (seqR (expS P p) 0 (p.ℓ + p.k)) := by
  refine Piece.mono (Piece.seqR (I := fun r σ s => KSamp p STK σ (p.k * p.ℓ) r s) (p.ℓ + p.k) 0
    fun r _ hr => expS_piece hP hF hS (by omega_arith)) (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end

end VG.Proof.MlDsa.PPC64LE.KeyGen
