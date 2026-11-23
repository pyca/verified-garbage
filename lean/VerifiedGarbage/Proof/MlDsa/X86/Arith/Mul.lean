module

public import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
public import VerifiedGarbage.Proof.MlDsa.X86.Arith.VLanes
public import VerifiedGarbage.Proof.MlKem.X86.Mcdt
public import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
meta import VerifiedGarbage.Proof.MlDsa.X86.Arith.VLanes
meta import VerifiedGarbage.Proof.MlKem.X86.Mcdt
meta import VerifiedGarbage.Impl.MlDsa.X86.Arith.Mul
meta import VerifiedGarbage.Proof.Framework.X86.Sse
meta import VerifiedGarbage.Proof.Framework.X86.SseDword
meta import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
meta import VerifiedGarbage.Proof.Framework.X86.Wp
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_multiply_ntt` and `vg_mldsa_multiply_add_ntt`

The vector pieces of `Impl/MlDsa/X86/Arith/Mul.lean` on the registers the
code uses them with (`vjoin_wp`, `vmont_wp`, `vmont2_wp`, `vcsub_wp`): each
is run an instruction at a time from a state given by its XMM registers
(`wp_xs`, and `wp_pm` for `pmuludq`, which needs an open MCDT frame), and
leaves in `xmm0` the value `VLanes.lean` describes. A core leaves
`f[i] · g[i] mod q` in each doubleword (`mul_lane`): two Montgomery
reductions, the second of the first times `2⁶⁴ mod q` (`mont_mont_R2`), and
a conditional subtraction; `multiplyAddNTT`'s adds `h[i]` and reduces
(`mulAdd_lane`).

The loop over the 64 groups of four coefficients is proven once for both
functions (`VInv`, `vstep`), for a core (`CoreOk`) whose doublewords are
the value `V a b c` of a coefficient from those of `f`, `g` and `h`
(`LaneOk`): after `k` groups, `eax`, `ecx` and `edx` point at coefficient
`4k` of `h`, `f` and `g`, the slot of `h` holds `h + 1024`, and the first
`4k` coefficients of `h` are the new ones. The function is the loop inside
its MCDT frame (`Piece.mcdt`, `Proof/MlKem/X86/Mcdt.lean`), constant time by the analysis
of general and XMM registers (`Piece.sse`) from `esp` and the three
pointers.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Arith

open VG VG.X86 VG.X86.Lanes VG.Impl.MlDsa.X86.Arith
open VG.Impl.MlKem.X86 (at_)
open VG.Proof.MlDsa.Arith
open VG.Spec.MlDsa VG.Proof.MlDsa
open VG.Proof.MlKem.X86 (toNat_ofNat32 eq_ofNat_of_toNat E0 retR Piece ea_add ptr_next satState)
open VG.Proof.MlKem.X86 (M0 mcdtR McdtEnd McdtPost M0_esp M0_wr M0_rd M0_frame ret_mcdt)

/-! ## Straight-line XMM code -/

/-- `s'` is `s` but for its XMM registers. -/
def Same (s s' : State) : Prop := ∃ f, s' = { s with xmm := f }

variable {s : State}

/-- An instruction that writes an XMM register, from a state given by its XMM registers. -/
theorem wp_xs {f : XReg → BitVec 128} {i : Instr} {is : List Instr} {Q : State → Prop} {d : XReg} {v : BitVec 128}
    (h : exec i { s with xmm := f } = some (State.setXmm { s with xmm := f } d v))
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then v else f r } Q) :
    WP isa (.block (i :: is)) { s with xmm := f } Q := Wp.cons h k

/-- `pmuludq`, inside an MCDT frame. -/
theorem wp_pm {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d r : XReg} (hm : 0 < s.mcdt)
    (k : WP isa (.block is) { s with xmm := fun x => if x = d then pmuludq (f d) (f r) else f x } Q) :
    WP isa (.block (.pmuludq d r :: is)) { s with xmm := f } Q :=
  Wp.cons (show (if 0 < s.mcdt then some _ else none) = _ by rw [ite_eq_left hm]; rfl) k

/-- A 16-byte load. -/
theorem wp_ld {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} {d : XReg} {m : MemOp} {a : Addr}
    (ha : s.ea m = a) (hin : InRegions (s.rd ++ s.wr) a 16)
    (k : WP isa (.block is) { s with xmm := fun r => if r = d then s.mem.readW a 128 else f r } Q) :
    WP isa (.block (.movdquLoad d m :: is)) { s with xmm := f } Q :=
  Wp.cons (show (State.load128 { s with xmm := f } (s.ea m)).map _ = _ by
    rw [ha, State.load128, ite_eq_left hin]; rfl) k

/-- The registers of the constants. -/
structure VC (f : XReg → BitVec 128) : Prop where
  q : f .xmm7 = qV
  nqi : f .xmm6 = nqiV
  r2 : f .xmm5 = bc r2Imm
  ones : f .xmm4 = onesV
  negq : f .xmm3 = negqV

theorem vjoin_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt)
    (h6 : f .xmm6 = nqiV) (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = joinV (f .xmm0) (f .xmm2) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (vjoin .xmm0 .xmm2 .xmm1 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_pm hm (wp_pm hm (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_pm hm (wp_pm hm (wp_xs rfl
    (wp_xs rfl (k _ ?_ ?_))))))))))
  · simp only [joinV, redcV]
    rw [← h6, ← h7]
    rfl
  · intro r h0 h1 h2
    simp only [h0, h1, h2, ite_false]

theorem vmont_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt)
    (h6 : f .xmm6 = nqiV) (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = montV (f .xmm0) (f .xmm5) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (vmont .xmm0 .xmm5 .xmm2 .xmm1 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_pm hm (wp_pm hm (vjoin_wp hm h6 h7 fun g hg hr => k g (hg.trans rfl)
    fun r h0 h1 h2 => (hr r h0 h1 h2).trans ?_))))
  simp only [h0, h2, ite_false]

theorem vmont2_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt)
    (h6 : f .xmm6 = nqiV) (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = mont2V (f .xmm0) (f .xmm1) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (vmont2 .xmm0 .xmm1 .xmm2 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_pm hm (wp_xs rfl (wp_pm hm (vjoin_wp hm h6 h7 fun g hg hr => k g (hg.trans rfl)
    fun r h0 h1 h2 => (hr r h0 h1 h2).trans ?_)))))
  simp only [h0, h1, h2, ite_false]

theorem vcsub_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop}
    (h3 : f .xmm3 = negqV) (h4 : f .xmm4 = onesV) (h7 : f .xmm7 = qV)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = csubV (f .xmm0) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (vcsub .xmm0 .xmm1 ++ is)) { s with xmm := f } Q := by
  refine wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (wp_xs rfl (k _ ?_ ?_))))))
  · simp only [csubV]
    rw [← h3, ← h4, ← h7]
    rfl
  · intro r h0 h1
    simp only [h0, h1, ite_false]

/-! ## The cores -/

/-- What `mulCore` leaves in `xmm0`. -/
def mulX (x y : BitVec 128) : BitVec 128 := csubV (montV (mont2V x y) (bc r2Imm))

/-- What `mulAddCore` leaves in `xmm0`. -/
def mulAddX (x y h : BitVec 128) : BitVec 128 := csubV (XBinOp.eval .paddd (mulX x y) h)

theorem mulCore_wp {f : XReg → BitVec 128} {is : List Instr} {Q : State → Prop} (hm : 0 < s.mcdt) (hc : VC f)
    (k : ∀ g : XReg → BitVec 128, g .xmm0 = mulX (f .xmm0) (f .xmm1) →
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) → WP isa (.block is) { s with xmm := g } Q) :
    WP isa (.block (mulCore ++ is)) { s with xmm := f } Q := by
  rw [show mulCore ++ is = vmont2 .xmm0 .xmm1 .xmm2 ++ (vmont .xmm0 .xmm5 .xmm2 .xmm1 ++ (vcsub .xmm0 .xmm1 ++ is)) by
    simp only [mulCore, List.append_assoc]]
  refine vmont2_wp hm hc.nqi hc.q fun g₁ v₁ r₁ => ?_
  have e₁ : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g₁ r = f r := r₁
  refine vmont_wp hm ((e₁ _ (by decide) (by decide) (by decide)).trans hc.nqi)
    ((e₁ _ (by decide) (by decide) (by decide)).trans hc.q) fun g₂ v₂ r₂ => ?_
  have e₂ : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g₂ r = f r := fun r h0 h1 h2 =>
    (r₂ r h0 h1 h2).trans (e₁ r h0 h1 h2)
  refine vcsub_wp ((e₂ _ (by decide) (by decide) (by decide)).trans hc.negq)
    ((e₂ _ (by decide) (by decide) (by decide)).trans hc.ones)
    ((e₂ _ (by decide) (by decide) (by decide)).trans hc.q) fun g₃ v₃ r₃ => k g₃ ?_ ?_
  · rw [v₃, v₂, v₁, e₁ .xmm5 (by decide) (by decide) (by decide), hc.r2, mulX]
  · exact fun r h0 h1 h2 => (r₃ r h0 h1).trans (e₂ r h0 h1 h2)

/-- A core: from the four coefficients of `f` and `g` in `xmm0` and `xmm1`
and those of `h` at `[eax]`, it leaves `F` of them in `xmm0`, and keeps the
constants. -/
def CoreOk (core : List Instr) (F : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) : Prop :=
  ∀ (s : State) (f : XReg → BitVec 128) (is : List Instr) (Q : State → Prop) (a : Addr), 0 < s.mcdt → VC f →
    s.ea (at_ .eax 0) = a → InRegions (s.rd ++ s.wr) a 16 →
    (∀ g : XReg → BitVec 128, g .xmm0 = F (f .xmm0) (f .xmm1) (s.mem.readW a 128) → VC g →
      WP isa (.block is) { s with xmm := g } Q) →
    WP isa (.block (core ++ is)) { s with xmm := f } Q

theorem VC.of_eq {f g : XReg → BitVec 128} (hc : VC f) (h : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → g r = f r) :
    VC g :=
  ⟨(h _ (by decide) (by decide) (by decide)).trans hc.q, (h _ (by decide) (by decide) (by decide)).trans hc.nqi,
    (h _ (by decide) (by decide) (by decide)).trans hc.r2, (h _ (by decide) (by decide) (by decide)).trans hc.ones,
    (h _ (by decide) (by decide) (by decide)).trans hc.negq⟩

theorem mul_core : CoreOk mulCore fun x y _ => mulX x y := fun _ _ _ _ _ hm hc _ _ k =>
  mulCore_wp hm hc fun g v r => k g v (hc.of_eq r)

theorem mulAdd_core : CoreOk mulAddCore mulAddX := fun s f is Q a hm hc ha hin k => by
  rw [show mulAddCore ++ is = mulCore ++ (.movdquLoad .xmm1 (at_ .eax 0) :: xb .paddd .xmm0 .xmm1 ::
      (vcsub .xmm0 .xmm1 ++ is)) by
    simp only [mulAddCore, List.append_assoc, List.cons_append, List.nil_append]]
  refine mulCore_wp hm hc fun g₁ v₁ r₁ => ?_
  have c₁ := hc.of_eq r₁
  refine wp_ld ha hin (wp_xs rfl (vcsub_wp c₁.negq c₁.ones c₁.q fun g₂ v₂ r₂ => k g₂ ?_ ?_))
  · rw [v₂, mulAddX, ← v₁]; rfl
  · exact c₁.of_eq fun r h0 h1 _ => (r₂ r h0 h1).trans (by simp only [h0, h1, ite_false])

/-! ## The doublewords of the cores' results -/

theorem r2Imm_toNat : r2Imm.toNat = 2 ^ 64 % q := rfl

theorem mul_lane {x y : BitVec 128} (hx : ∀ i < 4, (dword x i).toNat < q) (hy : ∀ i < 4, (dword y i).toNat < q)
    {j : Nat} (hj : j < 4) :
    (dword (mulX x y) j).toNat = (dword x j).toNat * (dword y j).toNat % q ∧ (dword (mulX x y) j).toNat < q := by
  have h1 : ∀ i < 4, (dword x i).toNat * (dword y i).toNat < q * 2 ^ 32 := fun i hi =>
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt (hx i hi) (hy i hi)) (by decide)
  have h2 : ∀ i < 4, (dword (mont2V x y) i).toNat * (dword (bc r2Imm) (2 * (i / 2))).toNat < q * 2 ^ 32 :=
    fun i hi => by
      rw [dword_mont2V h1 hi, dword_bc _ (by omega_using [hi]), r2Imm_toNat]
      have := mont_lt (h1 i hi)
      rw [q_eq] at this ⊢
      omega_using [this]
  have e : (dword (mulX x y) j).toNat = (dword x j).toNat * (dword y j).toNat % q := by
    rw [mulX, dword_csubV _ hj, csubL_toNat (by rw [dword_montV h2 hj]; exact mont_lt (h2 j hj)),
      dword_montV h2 hj, condSub_mont (h2 j hj), dword_mont2V h1 hj, dword_bc _ (by omega_using [hj]), r2Imm_toNat]
    exact mont_mont_R2 _
  exact ⟨e, by rw [e]; exact Nat.mod_lt _ (by decide)⟩

theorem mulAdd_lane {x y h : BitVec 128} (hx : ∀ i < 4, (dword x i).toNat < q)
    (hy : ∀ i < 4, (dword y i).toNat < q) {j : Nat} (hj : j < 4) (hh : (dword h j).toNat < q) :
    (dword (mulAddX x y h) j).toNat = ((dword x j).toNat * (dword y j).toNat % q + (dword h j).toNat) % q := by
  obtain ⟨e, hl⟩ := mul_lane hx hy hj
  have es : (dword (mulX x y) j + dword h j).toNat = (dword (mulX x y) j).toNat + (dword h j).toNat := by
    rw [BitVec.toNat_add]; rw [q_eq] at hl hh; omega_using [hl, hh]
  rw [mulAddX, dword_csubV _ hj, dword_paddd _ _ hj,
    csubL_toNat (by rw [es]; rw [q_eq] at hl hh ⊢; omega_using [hl, hh]), es,
    condSub_eq (by rw [q_eq] at hl hh ⊢; omega_using [hl, hh]), e]

/-- The doublewords of a core's result: `V` of the coefficients, which are
reduced (those of `h` if `acc`). -/
def LaneOk (F : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128) (acc : Bool) (V : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (x y h : BitVec 128), (∀ i < 4, (dword x i).toNat < q) → (∀ i < 4, (dword y i).toNat < q) →
    (acc = true → ∀ i < 4, (dword h i).toNat < q) → ∀ j < 4,
      (dword (F x y h) j).toNat = V (dword x j).toNat (dword y j).toNat (dword h j).toNat

/-- The value of `multiplyNTT`. -/
def mulV (a b _c : Nat) : Nat := a * b % q

/-- The value of `multiplyAddNTT`. -/
def mulAddV (a b c : Nat) : Nat := (a * b % q + c) % q

theorem mul_lanes : LaneOk (fun x y _ => mulX x y) false mulV :=
  fun _ _ _ hx hy _ _ hj => (mul_lane hx hy hj).1

theorem mulAdd_lanes : LaneOk mulAddX true mulAddV :=
  fun _ _ _ hx hy hh j hj => mulAdd_lane hx hy hj (hh rfl j hj)

/-! ## The precondition -/

section
variable (s₀ : State)
abbrev hP : BitVec 32 := arg s₀ 0
abbrev fP' : BitVec 32 := arg s₀ 1
abbrev gP' : BitVec 32 := arg s₀ 2
abbrev hA : Addr := (hP s₀).setWidth 64
abbrev fA' : Addr := (fP' s₀).setWidth 64
abbrev gA' : Addr := (gP' s₀).setWidth 64
abbrev aR3 : Region := ⟨argAddr s₀ 0, 12⟩
end

/-- The precondition of both functions: `h` is reduced if `acc`. -/
structure MulPre (acc : Bool) (s₀ : State) : Prop where
  sp : 16 ≤ (E0 s₀).toNat
  sp' : (E0 s₀).toNat + 4 + 12 ≤ 2 ^ 32
  rd : s₀.rd = [polyRegion (fA' s₀), polyRegion (gA' s₀)]
  wr : s₀.wr = [polyRegion (hA s₀), aR3 s₀]
  h_f : (polyRegion (hA s₀)).Disjoint (polyRegion (fA' s₀))
  h_g : (polyRegion (hA s₀)).Disjoint (polyRegion (gA' s₀))
  h_a : (polyRegion (hA s₀)).Disjoint (aR3 s₀)
  f_a : (polyRegion (fA' s₀)).Disjoint (aR3 s₀)
  g_a : (polyRegion (gA' s₀)).Disjoint (aR3 s₀)
  ret_h : (retR s₀).Disjoint (polyRegion (hA s₀))
  ret_f : (retR s₀).Disjoint (polyRegion (fA' s₀))
  ret_g : (retR s₀).Disjoint (polyRegion (gA' s₀))
  ret_a : (retR s₀).Disjoint (aR3 s₀)
  stk_h : (stkR s₀).Disjoint (polyRegion (hA s₀))
  stk_f : (stkR s₀).Disjoint (polyRegion (fA' s₀))
  stk_g : (stkR s₀).Disjoint (polyRegion (gA' s₀))
  stk_a : (stkR s₀).Disjoint (aR3 s₀)
  h_fit : (hP s₀).toNat + 1024 ≤ 2 ^ 32
  f_fit : (fP' s₀).toNat + 1024 ≤ 2 ^ 32
  g_fit : (gP' s₀).toNat + 1024 ≤ 2 ^ 32
  h_red : acc = true → Reduced s₀.mem (hA s₀)
  f_red : Reduced s₀.mem (fA' s₀)
  g_red : Reduced s₀.mem (gA' s₀)

theorem MulPre.of_mul {s₀ : State} (h : (mulContract X86.abi 16).pre s₀) : MulPre false s₀ := by
  sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    fun e => absurd e (by decide), h21, h22⟩

theorem MulPre.of_mulAdd {s₀ : State} (h : (mulAddContract X86.abi 16).pre s₀) : MulPre true s₀ := by
  sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    fun _ => h21, h22, h23⟩


/-! ## The loop -/

/-- The new value of coefficient `i`. -/
def newM (V : Nat → Nat → Nat → Nat) (s₀ : State) (i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (V (coeffAt s₀.mem (fA' s₀) i).toNat (coeffAt s₀.mem (gA' s₀) i).toNat
    (coeffAt s₀.mem (hA s₀) i).toNat)

/-- After `k` groups of four coefficients. -/
structure VInv (V : Nat → Nat → Nat → Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  esp : s.gpr .esp = (M0 s₀).gpr .esp
  rd : s.rd = (M0 s₀).rd
  wr : s.wr = (M0 s₀).wr
  eax : s.gpr .eax = hP s₀ + BitVec.ofNat 32 (16 * k)
  ecx : s.gpr .ecx = fP' s₀ + BitVec.ofNat 32 (16 * k)
  edx : s.gpr .edx = gP' s₀ + BitVec.ofNat 32 (16 * k)
  endp : s.mem.readW (argAddr s₀ 0) 32 = hP s₀ + 1024
  frame : Frame [polyRegion (hA s₀), aR3 s₀] (M0 s₀).mem s.mem
  h : ∀ i < 256, coeffAt s.mem (hA s₀) i = if i < 4 * k then newM V s₀ i else coeffAt s₀.mem (hA s₀) i
  mcdt : s.mcdt = s₀.mcdt + 1
  saved : ∀ r ∈ [Reg.ebx, .esi, .edi, .ebp], s.gpr r = s₀.gpr r
  vc : VC s.xmm

theorem coeffAt_write16 (m : Mem) (p : Addr) (v : BitVec 128) {k i : Nat} (hk : k < 64) (hi : i < 256) :
    coeffAt (m.writeW (coeffAddr p (4 * k)) v) p i =
      if 4 * k ≤ i ∧ i < 4 * k + 4 then dword v (i - 4 * k) else coeffAt m p i := by
  split
  · rename_i h
    obtain ⟨j, hj, rfl⟩ : ∃ j < 4, i = 4 * k + j := ⟨i - 4 * k, by omega_using [h], by omega_using [h]⟩
    rw [coeffAt_eq, ← coeffAddr_add, readW_writeW128 _ _ _ hj, Nat.add_sub_cancel_left]
  · rename_i h
    exact Mem.readW_writeW_sep (Offset.sep p (by omega_using [h]) (by omega_using [hi]) (by omega_using [hk]))
      (by decide)

namespace MulPre
variable {acc : Bool} {s₀ : State} (hp : MulPre acc s₀)
include hp

theorem sp12 : 12 ≤ (E0 s₀).toNat := by have := hp.sp; omega_using [this]

/-- A region apart from the contract's stack is apart from the MCDT frame. -/
theorem mcdt_disj {R : Region} (h : (stkR s₀).Disjoint R) : (mcdtR s₀).Disjoint R := by
  intro a h₁ h₂
  refine h a ?_ h₂
  have := hp.sp
  have := (E0 s₀).isLt
  simp only [Region.Contains] at h₁ ⊢
  bv_omega

theorem arg_contains3 {i : Nat} (hi : i < 3) : (aR3 s₀).Contains (argAddr s₀ i) 4 := by
  have := hp.sp'
  simp only [argAddr, Region.Contains, E0] at this ⊢
  bv_omega

/-- The arguments, at `[esp + 16 + 4i]` after the push. -/
theorem arg_M0 {i : Nat} (hi : i < 3) :
    ((M0 s₀).gpr .esp + BitVec.ofNat 32 (16 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      (M0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  refine ⟨?_, ?_⟩
  · rw [M0_esp]; simp only [argAddr, E0]; congr 1; have := hp.sp; bv_omega
  · exact (M0_frame s₀ hp.sp12).readW (hp.arg_contains3 hi) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.mcdt_disj hp.stk_a).symm) (by decide)

theorem in_h16 {s : State} (hw : s.wr = (M0 s₀).wr) {k : Nat} (hk : k < 64) :
    InRegions s.wr (coeffAddr (hA s₀) (4 * k)) 16 := by
  rw [hw, M0_wr, hp.wr]
  exact ⟨polyRegion (hA s₀), by simp, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_h16' {s : State} (hw : s.wr = (M0 s₀).wr) {k : Nat} (hk : k < 64) :
    InRegions (s.rd ++ s.wr) (coeffAddr (hA s₀) (4 * k)) 16 :=
  let ⟨r, h, c⟩ := hp.in_h16 hw hk; ⟨r, List.mem_append_right _ h, c⟩

theorem in_f16 {s : State} (hr : s.rd = (M0 s₀).rd) {k : Nat} (hk : k < 64) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fA' s₀) (4 * k)) 16 := by
  rw [hr, M0_rd, hp.rd]
  exact ⟨polyRegion (fA' s₀), by simp, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_g16 {s : State} (hr : s.rd = (M0 s₀).rd) {k : Nat} (hk : k < 64) :
    InRegions (s.rd ++ s.wr) (coeffAddr (gA' s₀) (4 * k)) 16 := by
  rw [hr, M0_rd, hp.rd]
  exact ⟨polyRegion (gA' s₀), by simp, Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩

theorem in_arg {s : State} (hw : s.wr = (M0 s₀).wr) {i : Nat} (hi : i < 3) : InRegions s.wr (argAddr s₀ i) 4 := by
  rw [hw, M0_wr, hp.wr]
  exact ⟨aR3 s₀, by simp, hp.arg_contains3 hi⟩

/-- A polynomial apart from `h`, the arguments and the stack is never written. -/
theorem keep {s : State} (hf : Frame [polyRegion (hA s₀), aR3 s₀] (M0 s₀).mem s.mem) {p : Addr}
    (h1 : (polyRegion p).Disjoint (polyRegion (hA s₀))) (h2 : (polyRegion p).Disjoint (aR3 s₀))
    (h3 : (stkR s₀).Disjoint (polyRegion p)) {i : Nat} (hi : i < 256) :
    coeffAt s.mem p i = coeffAt s₀.mem p i := by
  rw [coeffAt_congr (m := s₀.mem) (m' := s.mem) (fun j hj => ?_) hi]
  rw [hf.bytes (R := polyRegion p) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact h1
      · exact h2) (polyLen _) hj,
    (M0_frame s₀ hp.sp12).bytes (R := polyRegion p) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (hp.mcdt_disj h3).symm) (polyLen _) hj]

theorem h_M0 {i : Nat} (hi : i < 256) : coeffAt (M0 s₀).mem (hA s₀) i = coeffAt s₀.mem (hA s₀) i :=
  coeffAt_congr (fun j hj => (M0_frame s₀ hp.sp12).bytes (R := polyRegion (hA s₀)) (fun r hr => by
    rw [List.mem_singleton.mp hr]; exact (hp.mcdt_disj hp.stk_h).symm) (polyLen _) hj) hi

end MulPre

theorem vstep {core : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} {acc : Bool}
    {V : Nat → Nat → Nat → Nat} (hc : CoreOk core F) (hl : LaneOk F acc V) {s₀ : State} (hp : MulPre acc s₀)
    {k : Nat} (hk : k < 64) {s : State} (h : VInv V s₀ k s) :
    WP isa (.block (mulStep core)) s fun s' =>
      VInv V s₀ (k + 1) s' ∧ eval .ne s' = some (decide (k + 1 < 64)) := by
  have hk4 : 4 * k < 256 := by omega_using [hk]
  have e16 : 16 * k = 4 * (4 * k) := by omega_using []
  have eh : s.ea (at_ .eax 0) = coeffAddr (hA s₀) (4 * k) := by
    rw [State.ea, at_, h.eax, e16]; exact ea_ptr hp.h_fit hk4
  have ef : s.ea (at_ .ecx 0) = coeffAddr (fA' s₀) (4 * k) := by
    rw [State.ea, at_, h.ecx, e16]; exact ea_ptr hp.f_fit hk4
  have eg : s.ea (at_ .edx 0) = coeffAddr (gA' s₀) (4 * k) := by
    rw [State.ea, at_, h.edx, e16]; exact ea_ptr hp.g_fit hk4
  have hm : 0 < s.mcdt := by rw [h.mcdt]; exact Nat.succ_pos _
  show WP isa (.block (.movdquLoad .xmm0 (at_ .ecx 0) :: .movdquLoad .xmm1 (at_ .edx 0) :: (core ++ _)))
    { s with xmm := s.xmm } _
  refine wp_ld ef (hp.in_f16 h.rd hk) (wp_ld eg (hp.in_g16 h.rd hk) (hc s _ _ _ _ hm
    ⟨h.vc.q, h.vc.nqi, h.vc.r2, h.vc.ones, h.vc.negq⟩ eh (hp.in_h16' h.wr hk) fun g vg cg => ?_))
  have hst : InRegions s.wr ((s.gpr .eax + BitVec.ofNat 32 0).setWidth 64) 16 := by
    have := hp.in_h16 h.wr hk; rwa [← eh] at this
  obtain ⟨a16, -⟩ := hp.arg_M0 (i := 0) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at a16
  have hcmp : InRegions (s.rd ++ s.wr) ((s.gpr .esp + BitVec.ofNat 32 16).setWidth 64) 4 := by
    rw [h.esp, a16]
    exact let ⟨r, hr, c⟩ := hp.in_arg h.wr (i := 0) (by decide); ⟨r, List.mem_append_right _ hr, c⟩
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, State.ea, at_, State.store128, State.load32, State.setReg, arithFlags, State.setFlags, hst, hcmp,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  have eh' : BitVec.setWidth 64 (s.gpr .eax + 0#32) = coeffAddr (hA s₀) (4 * k) := eh
  have ea' : BitVec.setWidth 64 (s.gpr .esp + 16#32) = argAddr s₀ 0 := by rw [h.esp]; exact a16
  have hcon : (polyRegion (hA s₀)).Contains (coeffAddr (hA s₀) (4 * k)) (128 / 8) :=
    Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])
  have hend : (s.mem.writeW (coeffAddr (hA s₀) (4 * k)) (g .xmm0)).readW (argAddr s₀ 0) 32 = hP s₀ + 1024 := by
    rw [((Frame.refl [polyRegion (hA s₀)] s.mem).writeW (List.mem_singleton_self _) (g .xmm0) hcon).readW
      (r := aR3 s₀) (hp.arg_contains3 (i := 0) (by decide))
      (fun r hr => by rw [List.mem_singleton.mp hr]; exact hp.h_a.symm) (by decide), h.endp]
  have vg' : g .xmm0 = F (s.mem.readW (coeffAddr (fA' s₀) (4 * k)) 128) (s.mem.readW (coeffAddr (gA' s₀) (4 * k)) 128)
      (s.mem.readW (coeffAddr (hA s₀) (4 * k)) 128) := vg
  -- the doublewords loaded are the coefficients
  have df : ∀ j < 4, dword (s.mem.readW (coeffAddr (fA' s₀) (4 * k)) 128) j = coeffAt s₀.mem (fA' s₀) (4 * k + j) :=
    fun j hj => by
      rw [dword_readW _ _ hj, coeffAddr_add, ← coeffAt_eq,
        hp.keep h.frame hp.h_f.symm hp.f_a hp.stk_f (by omega_using [hk, hj])]
  have dg : ∀ j < 4, dword (s.mem.readW (coeffAddr (gA' s₀) (4 * k)) 128) j = coeffAt s₀.mem (gA' s₀) (4 * k + j) :=
    fun j hj => by
      rw [dword_readW _ _ hj, coeffAddr_add, ← coeffAt_eq,
        hp.keep h.frame hp.h_g.symm hp.g_a hp.stk_g (by omega_using [hk, hj])]
  have dh : ∀ j < 4, dword (s.mem.readW (coeffAddr (hA s₀) (4 * k)) 128) j = coeffAt s₀.mem (hA s₀) (4 * k + j) :=
    fun j hj => by
      rw [dword_readW _ _ hj, coeffAddr_add, ← coeffAt_eq, h.h _ (by omega_using [hk, hj]),
        ite_eq_right (by omega_using [])]
  have lanes : ∀ j < 4, dword (g .xmm0) j = newM V s₀ (4 * k + j) := fun j hj => by
    refine eq_ofNat_of_toNat ?_
    rw [vg', hl _ _ _ (fun i hi => by rw [df i hi]; exact hp.f_red _ (by rw [n_eq]; omega_using [hk, hi]))
      (fun i hi => by rw [dg i hi]; exact hp.g_red _ (by rw [n_eq]; omega_using [hk, hi]))
      (fun e i hi => by rw [dh i hi]; exact hp.h_red e _ (by rw [n_eq]; omega_using [hk, hi])) j hj, df j hj, dg j hj,
      dh j hj]
  rw [eh', ea', hend]
  refine ⟨⟨h.esp, h.rd, h.wr, ?_, ?_, ?_, hend, h.frame.writeW (List.mem_cons_self ..) _ hcon, fun i hi => ?_,
    h.mcdt, fun r hr => ?_, cg⟩, ?_⟩
  · show s.gpr .eax + 16 = _
    rw [h.eax]; exact ptr_next _ _ 16
  · show s.gpr .ecx + 16 = _
    rw [h.ecx]; exact ptr_next _ _ 16
  · show s.gpr .edx + 16 = _
    rw [h.edx]; exact ptr_next _ _ 16
  · show coeffAt (s.mem.writeW (coeffAddr (hA s₀) (4 * k)) (g .xmm0)) (hA s₀) i = _
    rw [coeffAt_write16 _ _ _ hk hi, h.h i hi]
    by_cases h1 : 4 * k ≤ i ∧ i < 4 * k + 4
    · rw [ite_eq_left h1, ite_eq_left (by omega_using [h1]), lanes _ (by omega_using [h1]),
        show 4 * k + (i - 4 * k) = i by omega_using [h1]]
    · rw [ite_eq_right h1]
      by_cases h2 : i < 4 * k
      · rw [ite_eq_left h2, ite_eq_left (by omega_using [h2])]
      · rw [ite_eq_right h2, ite_eq_right (by omega_using [h1, h2])]
  · have := h.saved r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact this
  · show (some (s.gpr .eax + 16 - (hP s₀ + 1024) == 0) : Option Bool).map (!·) = _
    rw [h.eax, show hP s₀ + BitVec.ofNat 32 (16 * k) + 16 = hP s₀ + BitVec.ofNat 32 (16 * (k + 1)) from
      ptr_next _ _ 16, NttLoop.end_cmp _ (by omega_using [hk])]
    simp only [Option.map_some, Option.some.injEq]
    by_cases h1 : k + 1 < 64
    · rw [decide_eq_true h1, decide_eq_false (by omega_using [h1])]; rfl
    · rw [decide_eq_false h1, decide_eq_true (by omega_using [hk, h1])]; rfl

/-! ## The functions -/

/-- The public data: the stack pointer and the pointers. -/
def MulPub (s₀ s₀' : State) : Prop :=
  E0 s₀ = E0 s₀' ∧ arg s₀ 0 = arg s₀' 0 ∧ arg s₀ 1 = arg s₀' 1 ∧ arg s₀ 2 = arg s₀' 2

theorem vinit {acc : Bool} (V : Nat → Nat → Nat → Nat) {s₀ s : State} (hp : MulPre acc s₀) (e : s = M0 s₀) :
    WP isa (.block mulInit) s (VInv V s₀ 0) := by
  obtain ⟨a₀, v₀⟩ := hp.arg_M0 (i := 0) (by decide)
  obtain ⟨a₁, v₁⟩ := hp.arg_M0 (i := 1) (by decide)
  obtain ⟨a₂, v₂⟩ := hp.arg_M0 (i := 2) (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at a₀ a₁ a₂
  rw [← e] at a₀ a₁ a₂ v₀ v₁ v₂
  have hwr : s.wr = (M0 s₀).wr := by rw [e]
  have i₀ : InRegions (s.rd ++ s.wr) (argAddr s₀ 0) 4 :=
    let ⟨r, hr, c⟩ := hp.in_arg hwr (i := 0) (by decide); ⟨r, List.mem_append_right _ hr, c⟩
  have i₁ : InRegions (s.rd ++ s.wr) (argAddr s₀ 1) 4 :=
    let ⟨r, hr, c⟩ := hp.in_arg hwr (i := 1) (by decide); ⟨r, List.mem_append_right _ hr, c⟩
  have i₂ : InRegions (s.rd ++ s.wr) (argAddr s₀ 2) 4 :=
    let ⟨r, hr, c⟩ := hp.in_arg hwr (i := 2) (by decide); ⟨r, List.mem_append_right _ hr, c⟩
  have w₀ : InRegions s.wr (argAddr s₀ 0) 4 := hp.in_arg hwr (by decide)
  apply WP.of_runBlock
  simp only [reduceCtorEq, ↓reduceIte, mulInit, vconst, at_, List.cons_append, List.nil_append, runBlock_cons,
    runStep_some, runBlock_nil, exec, execAlu, XOp.exec, State.setXmm, readSrc, State.ea, State.load32,
    State.store32, State.setReg, arithFlags, State.setFlags, a₀, a₁, a₂, i₀, i₁, i₂, w₀, v₀,
    Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  have dj : ∀ i, 0 < i → i < 3 → (⟨argAddr s₀ i, 4⟩ : Region).Disjoint ⟨argAddr s₀ 0, 4⟩ := fun i h0 hi a h₁ h₂ => by
    have := hp.sp'
    simp only [Region.Contains, argAddr, E0] at this h₁ h₂
    bv_omega
  have fw : Frame [⟨argAddr s₀ 0, 4⟩] s.mem (s.mem.writeW (argAddr s₀ 0) (arg s₀ 0 + 1024)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have r₁ : (s.mem.writeW (argAddr s₀ 0) (arg s₀ 0 + 1024)).readW (argAddr s₀ 1) 32 = arg s₀ 1 := by
    rw [fw.readW (r := ⟨argAddr s₀ 1, 4⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact dj 1 (by decide) (by decide)) (by decide), v₁]
  have r₂ : (s.mem.writeW (argAddr s₀ 0) (arg s₀ 0 + 1024)).readW (argAddr s₀ 2) 32 = arg s₀ 2 := by
    rw [fw.readW (r := ⟨argAddr s₀ 2, 4⟩) (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact dj 2 (by decide) (by decide)) (by decide), v₂]
  have fr : Frame [polyRegion (hA s₀), aR3 s₀] (M0 s₀).mem (s.mem.writeW (argAddr s₀ 0) (arg s₀ 0 + 1024)) := by
    rw [e]
    exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
      (hp.arg_contains3 (i := 0) (by decide))
  rw [r₁, r₂]
  refine ⟨?_, ?_, hwr, ?_, ?_, ?_, Mem.readW_writeW_self32 _ _ _, fr, fun i hi => ?_, ?_,
    fun r hr => ?_, ⟨bc_eq _, bc_eq _, bc_eq _, bc_eq _, bc_eq _⟩⟩
  · show s.gpr .esp = _
    rw [e]
  · show s.rd = _
    rw [e]
  · show arg s₀ 0 = _
    rw [Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · show arg s₀ 1 = _
    rw [Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · show arg s₀ 2 = _
    rw [Nat.mul_zero]; exact (BitVec.add_zero _).symm
  · show coeffAt (s.mem.writeW (argAddr s₀ 0) (arg s₀ 0 + 1024)) (hA s₀) i = _
    have fa : Frame [aR3 s₀] s.mem (s.mem.writeW (argAddr s₀ 0) (arg s₀ 0 + 1024)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.arg_contains3 (i := 0) (by decide))
    rw [ite_eq_right (Nat.not_lt_zero _), ← hp.h_M0 hi, ← e]
    exact coeffAt_congr (fun j hj => fa.bytes (R := polyRegion (hA s₀)) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hp.h_a) (polyLen _) hj) hi
  · show s.mcdt = _
    rw [e]; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> (show s.gpr _ = _; rw [e]; rfl)

theorem mul_piece {core : List Instr} {F : BitVec 128 → BitVec 128 → BitVec 128 → BitVec 128} {acc : Bool}
    {V : Nat → Nat → Nat → Nat} (hc : CoreOk core F) (hl : LaneOk F acc V)
    (hsp : NoSp (.seq (.block mulInit) (.loop (.block (mulStep core)) .ne)))
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (ht₁ : (VG.X86.sseTaint.check (τr [.esp]) (.block mulInit) h₁).isSome = true)
    (ht₂ : (VG.X86.sseTaint.check (τr [.esp, .eax, .ecx, .edx]) (.block (mulStep core)) h₂).isSome = true) :
    Piece (MulPre acc) MulPub (fun s₀ s => s = s₀) (fun s₀ s' => McdtPost (VInv V s₀ 64) s₀ s') (mulFn core) :=
  Piece.mcdt (fun s₀ => [polyRegion (hA s₀), aR3 s₀]) hsp (fun _ hp => hp.sp12)
    (fun _ hp r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨hp.mcdt_disj hp.stk_h, hp.ret_h⟩
      · exact ⟨hp.mcdt_disj hp.stk_a, hp.ret_a⟩)
    (fun _ _ _ _ hq => hq.1)
    ((Piece.seq (Piece.sse [.esp] (fun _ _ hp e => vinit V hp e) (fun s₀ s₀' s s' _ _ hq e e' r hr => by
          simp only [List.mem_singleton] at hr
          subst hr
          rw [e, e', M0_esp, M0_esp, hq.1]) ht₁)
        (Piece.loop (fun k s₀ s => VInv V s₀ k s) (by decide) fun k hk =>
          Piece.sse [.esp, .eax, .ecx, .edx] (fun _ _ hp h => vstep hc hl hp hk h)
            (fun s₀ s₀' s s' _ _ hq h h' r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl
              · rw [h.esp, h'.esp, M0_esp, M0_esp, hq.1]
              · rw [h.eax, h'.eax, hP, hP, hq.2.1]
              · rw [h.ecx, h'.ecx, fP', fP', hq.2.2.1]
              · rw [h.edx, h'.edx, gP', gP', hq.2.2.2]) ht₂)).mono (fun _ _ _ h => h)
      fun _ _ _ h => ⟨⟨h.frame, h.esp, h.rd, h.wr, h.mcdt, h.saved⟩, h⟩)

/-- Memory with the arguments `0`, `0x400` and `0x800` at `0x5004`. -/
def mulSatMem : Mem := fun a => if a = 0x5009 then 4 else if a = 0x500d then 8 else 0

theorem mulSat_zero (a : Addr) (ha : a.toNat < 0x5000) : mulSatMem a = 0 := by
  simp only [mulSatMem]
  rw [ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha]),
    ite_eq_right_iff.mpr fun h => absurd (congrArg BitVec.toNat h) (by simp; omega_using [ha])]

theorem mul_verified : Verified X86.target mul (mulContract X86.abi 16) := by
  refine Piece.verified (((mul_piece mul_core mul_lanes (NoSp.of_all (by lit_decide)) (by taint_decide) (by taint_decide)).pre_mono
    (fun _ h => MulPre.of_mul h) fun s s' _ _ h => by
      sig_pub [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := MulPre.of_mul h₀
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hp.mcdt_disj hp.stk_h).symm) ?_
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.h i hi, ite_eq_left (show i < 4 * 64 from hi), mul_get _ _ hi, val_mul, polyAt_val hp.f_red hi, polyAt_val hp.g_red hi,
      newM, mulV, toNat_ofNat32 (mod_q_lt32 _)]
  · let st := satState mulSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_below (mulSat_zero) 0x400 (by decide),
      reduced_below mulSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)

theorem mulAdd_verified : Verified X86.target mulAdd (mulAddContract X86.abi 16) := by
  refine Piece.verified ((((mul_piece mulAdd_core mulAdd_lanes (NoSp.of_all (by lit_decide)) (by taint_decide) (by taint_decide)).pre_mono
    (fun _ h => MulPre.of_mulAdd h) fun s s' _ _ h => by
      sig_pub [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
      exact h)).mono (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hinv, hm⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    have hp := MulPre.of_mulAdd h₀
    refine Proof.MlDsa.Arith.polyIs_frame hm (fun r hr => by rw [List.mem_singleton.mp hr]; exact (hp.mcdt_disj hp.stk_h).symm) ?_
    have hr := hp.h_red rfl
    refine polyIs_of_toNat fun i hi => ?_
    rw [hinv.h i hi, ite_eq_left (show i < 4 * 64 from hi), add_get _ _ hi, val_add', mul_get _ _ hi, val_mul, polyAt_val hp.f_red hi,
      polyAt_val hp.g_red hi, polyAt_val hr hi, newM, mulAddV, Nat.add_comm (_ % q),
      toNat_ofNat32 (mod_q_lt32 _)]
  · let st := satState mulSatMem [⟨0x400, 1024⟩, ⟨0x800, 1024⟩] [⟨0, 1024⟩, ⟨0x5004, 12⟩]
    have a0 : arg st 0 = 0 := by decide
    have a1 : arg st 1 = 0x400 := by decide
    have a2 : arg st 2 = 0x800 := by decide
    have e : argAddr st 0 = 0x5004 := by decide
    refine ⟨st, ?_⟩
    sig_pre [mulAddContract, mulSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, e]
    refine ⟨by decide, by decide, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by decide, by decide, by decide, reduced_below mulSat_zero 0 (by decide),
      reduced_below mulSat_zero 0x400 (by decide), reduced_below mulSat_zero 0x800 (by decide)⟩
    all_goals exact Region.disjoint_of_sep (by decide)


end VG.Proof.MlDsa.X86.Arith
