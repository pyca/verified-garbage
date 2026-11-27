module

import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.KernelRfl
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Samp

/-! ### `MlDsa.X86.Verify.Compute`, which this module and modules that import it used -/

section

/-!
# ML-DSA verification on x86 (32-bit): what holds while computing `w′₁`

From the hint `h`, `Â` (`A`) and `c` (`C`) the samplers gave, `CX` says what
`scratch` holds while computing: `ẑ[i]` for `i < j` (and `z[i]` for the
others), `ĉ` once `cd`, and the packed rows `w₁[r]` for `r < nr`; and the
result (`GC`). It is kept by pieces that write only buffers apart from those
(`SafeC`, `CX.keep`). The NTTs of `z` and `c` (`nttZ_piece`, `nttC_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt simpleBitPack)
open VG.Proof.MlDsa (PolyIs Reduced polyAt HintIs)
open VG.Proof.MlDsa.Verify (vZ vHint zHat w1Row)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s₀ : State)

/-- The row `r` of `w₁` packed in `scratch`. -/
abbrev wB (r : Nat) : Buf := sb (oB + w1Len p * r) (w1Len p)

/-- While computing `w′₁`, with the hint `h`, `Â` and `c` of the samplers. -/
structure CX (h : List (Vector Bool Spec.MlDsa.n)) (A : Nat → Nat → Poly) (C : Poly) (j : Nat) (cd : Bool)
    (nr : Nat) (s : State) : Prop where
  ctx : Ctx (YV p) s₀ s
  norms : NormsOk p s₀ p.ℓ
  hh : hOf p s₀ = some h
  hint : HintIs s.mem (Buf.addr s₀ (hB p.k)) p.k h
  a : ∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')
  z : ∀ i < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pZ i))
    (if i < j then zHat p (vSig p s₀) i else toRq (vZ p (vSig p s₀) i))
  c : PolyIs s.mem (Buf.addr s₀ pC) (if cd then ntt C else C)
  gc : GC p s₀ A C (accV s₀ s)
  w : ∀ r < nr, bytesAt s.mem (Buf.addr s₀ (wB p r)) (w1Len p) =
    simpleBitPack (w1Row p (vPk p s₀) (vSig p s₀) A (ntt C) h r) (w1Max p)

/-- While computing `w′₁`. -/
def CI (j : Nat) (cd : Bool) (nr : Nat) (s : State) : Prop :=
  ∃ h A C, CX p s₀ h A C j cd nr s

end

/-- The buffers of `CX` but `z` and `c` are apart from `bs`. -/
structure SafeC (p : Params) (nr : Nat) (bs : List Buf) : Prop where
  h : (YV p).apart (hB p.k) bs = true
  a : ∀ r < p.k, ∀ s < p.ℓ, (YV p).apart (pA r s) bs = true
  acc : (YV p).apart (sb oACC 4) bs = true
  w : ∀ r < nr, (YV p).apart (wB p r) bs = true

/-- `CX` after a piece that writes only `bs`, with `z` and `c` as they are after it. -/
theorem CX.update {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {j : Nat}
    {cd : Bool} {nr : Nat} {s₀ s s' : State} (hc : CX p s₀ h A C j cd nr s) (hp : TPre (YV p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (sf : SafeC p nr bs) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YV p) s₀ s') {j' : Nat} {cd' : Bool}
    (hz : ∀ i < p.ℓ, PolyIs s'.mem (Buf.addr s₀ (pZ i))
      (if i < j' then zHat p (vSig p s₀) i else toRq (vZ p (vSig p s₀) i)))
    (hcc : PolyIs s'.mem (Buf.addr s₀ pC) (if cd' then ntt C else C)) : CX p s₀ h A C j' cd' nr s' :=
  ⟨h', hc.norms, hc.hh, keepHint hp hN sf.h fr hc.hint,
    fun r hr s hs => keepPolyD hp (stkV hN) (sf.a r hr s hs) fr (hc.a r hr s hs), hz, hcc,
    by rw [acc_keepV hp hN sf.acc fr]; exact hc.gc,
    fun r hr => by rw [keepBytes hp (stkV hN) (sf.w r hr) fr]; exact hc.w r hr⟩

/-- `CX` after a piece that writes only `bs`, apart from `z` and `c`. -/
theorem CX.keep {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {j : Nat}
    {cd : Bool} {nr : Nat} {s₀ s s' : State} (hc : CX p s₀ h A C j cd nr s) (hp : TPre (YV p) s₀)
    {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96) (sf : SafeC p nr bs)
    (sz : ∀ i < p.ℓ, (YV p).apart (pZ i) bs = true) (sc : (YV p).apart pC bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YV p) s₀ s') : CX p s₀ h A C j cd nr s' :=
  hc.update hp hN sf fr h' (fun i hi => keepPolyD hp (stkV hN) (sz i hi) fr (hc.z i hi))
    (keepPolyD hp (stkV hN) sc fr hc.c)

theorem w_row {p : Params} {r : Nat} (hr : r < p.k) : w1Len p * r + w1Len p ≤ p.k * w1Len p := by
  rw [Nat.mul_comm p.k]; exact mul_row hr

theorem w_rows {p : Params} {r nr : Nat} (hr : r < nr) (hnr : nr ≤ p.k) :
    w1Len p * r + w1Len p ≤ w1Len p * nr ∧ w1Len p * r + w1Len p ≤ p.k * w1Len p :=
  ⟨mul_row hr, w_row (Nat.lt_of_lt_of_le hr hnr)⟩

/-- Proves `SafeC` for buffers checked by `lv`, with `hnr : nr ≤ p.k`. -/
tactic_template "safeC " hF:term:max hnr:term:max : tactic => `(tactic| exact
  ⟨by lv $hF, fun r hr s hs => by lv $hF, by lv $hF, fun r hr => by
    have := VG.Proof.MlDsa.X86.Verify.w_rows hr $hnr
    lv $hF⟩)

theorem apart_append {Y : Lay} {b : Buf} {bs₁ bs₂ : List Buf} (h₁ : Y.apart b bs₁ = true)
    (h₂ : Y.apart b bs₂ = true) : Y.apart b (bs₁ ++ bs₂) = true := by
  simp only [Lay.apart, List.all_append, Bool.and_eq_true] at *
  exact ⟨h₁.1, h₁.2, h₂.2⟩

/-- `SafeC` of two lists of buffers, for both. -/
theorem SafeC.append {p : Params} {nr : Nat} {bs₁ bs₂ : List Buf} (h₁ : SafeC p nr bs₁) (h₂ : SafeC p nr bs₂) :
    SafeC p nr (bs₁ ++ bs₂) :=
  ⟨apart_append h₁.h h₂.h, fun r hr s hs => apart_append (h₁.a r hr s hs) (h₂.a r hr s hs),
    apart_append h₁.acc h₂.acc, fun r hr => apart_append (h₁.w r hr) (h₂.w r hr)⟩

/-- `SafeC` of a buffer of `scratch` below `Â`, apart from the hint, the result and the rows of `w₁`
so far, proved once for any buffer (`safeC` on a literal list of buffers costs seconds). -/
theorem SafeC.sc {p : Params} (hF : VFacts p) {nr : Nat} (hnr : nr ≤ p.k) {o l : Nat} (h0 : 0 < l)
    (h1 : o + l ≤ oACC ∨ oACC + 4 ≤ o) (h2 : o + l ≤ oB ∨ oB + w1Len p * nr ≤ o) (h3 : o + l ≤ oP 0 ∨ oP 8 ≤ o)
    (h4 : o + l ≤ oP 20) : SafeC p nr [sb o l] := by
  simp only [oACC, oB, oP] at h1 h2 h3 h4
  safeC hF hnr

/-- `SafeC` of no buffers. -/
theorem SafeC.nil {p : Params} (hF : VFacts p) {nr : Nat} (hnr : nr ≤ p.k) : SafeC p nr [] := by
  safeC hF hnr

theorem SafeC.cons_sc {p : Params} (hF : VFacts p) {nr : Nat} (hnr : nr ≤ p.k) {o l : Nat} {bs : List Buf}
    (h0 : 0 < l) (h1 : o + l ≤ oACC ∨ oACC + 4 ≤ o) (h2 : o + l ≤ oB ∨ oB + w1Len p * nr ≤ o ∨ oB + 1024 ≤ o)
    (h3 : o + l ≤ oP 0 ∨ oP 8 ≤ o) (h4 : o + l ≤ oP 20) (h : SafeC p nr bs) : SafeC p nr (sb o l :: bs) := by
  have : w1Len p * nr ≤ 1024 := by
    have := Nat.mul_le_mul_left (w1Len p) hnr; rw [Nat.mul_comm (w1Len p) p.k] at this; have := hF.w1; omega_arith
  exact (SafeC.sc hF hnr h0 h1 (by omega_using [h2, this]) h3 h4).append (bs₁ := [_]) h

/-- Proves `SafeC` of a list of buffers of `scratch` below `Â` by `SafeC.cons_sc`, with `hnr : nr ≤ p.k`. -/
tactic_template "safeCs " hF:term:max hnr:term:max : tactic => `(tactic| (
                   repeat' (first
                     | with_reducible exact VG.Proof.MlDsa.X86.Verify.SafeC.nil $hF $hnr
                     | apply VG.Proof.MlDsa.X86.Verify.SafeC.cons_sc $hF $hnr)
                   all_goals (
                     have := ($hF).w1; have := ($hF).k; have := ($hF).l; have := ($hF).ct
                     try simp only [VG.Impl.MlDsa.X86.Verify.oP, VG.Impl.MlDsa.X86.Verify.oB, VG.Impl.MlDsa.X86.Verify.oACC,
                       VG.Impl.MlDsa.X86.Verify.oSS, VG.Impl.MlDsa.X86.Verify.oCT]
                     omega_arith)))

theorem ci_of_sc {p : Params} {s₀ s : State} (h : SC p s₀ s) : CI p s₀ 0 false 0 s := by
  obtain ⟨hh, ehh, hi⟩ := h.vb.hint
  obtain ⟨A, C, hA, hC, hG⟩ := h.ex
  exact ⟨hh, A, C, h.vb.ctx, h.vb.norms, ehh, hi, hA, fun i hi => by
    rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.not_lt_zero _)]; exact h.vb.z i hi, hC, hG,
    fun r hr => absurd hr (Nat.not_lt_zero _)⟩

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem nttZ_piece {j : Nat} (hj : j < p.ℓ) :
    VP p (CI p · j false 0) (CI p · (j + 1) false 0) (nttAt P (pZ j)) :=
  inPlace_piece (Y := YV p) hP.ntt vS (oP (8 + j)) vS oSS (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => ⟨h.ctx, by have := (h.z j hj).1; exact this⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr post => by
      refine ⟨hh, A, C, h.update hp (N := 80) (by omega_using []) (by safeCs hF (Nat.zero_le p.k)) fr h' (fun i hi => ?_)
        (keepPolyD hp (stkV (by omega_using [])) (by lvd) fr h.c)⟩
      rcases (by omega_using [] : i < j ∨ i = j ∨ j < i) with hij | rfl | hij
      · have e := keepPolyD hp (stkV (by omega_using [])) (by lvd) fr (h.z i hi)
        simp only [hij, show i < j + 1 by omega_using [hij], ite_true] at e ⊢
        exact e
      · rw [ite_eq_left_iff.mpr fun h => absurd (Nat.lt_succ_self i) h]
        have e := (h.z i hi).2
        rw [ite_eq_right_iff.mpr fun h => absurd h (Nat.lt_irrefl _)] at e
        rw [e] at post
        exact post
      · have e := keepPolyD hp (stkV (by omega_using [])) (by lvd) fr (h.z i hi)
        simp only [show ¬ i < j by omega_using [hij], show ¬ i < j + 1 by omega_using [hij], ite_false] at e ⊢
        exact e

theorem nttC_piece : VP p (CI p · p.ℓ false 0) (CI p · p.ℓ true 0) (nttAt P pC) :=
  inPlace_piece (Y := YV p) hP.ntt vS (oP 15) vS oSS (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h⟩ => ⟨h.ctx, h.c.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr post => by
      refine ⟨hh, A, C, h.update hp (N := 80) (by omega_using []) (by safeCs hF (Nat.zero_le p.k)) fr h'
        (fun i hi => keepPolyD hp (stkV (by omega_using [])) (by lvd) fr (h.z i hi)) ?_⟩
      have e := h.c.2
      simp only [Bool.false_eq_true, ite_false] at e
      rw [e] at post
      simpa using post

end

end VG.Proof.MlDsa.X86.Verify

end

end

/-!
# ML-DSA verification on x86 (32-bit): a row of `w′₁`

Row `r`, step by step, with what the temporaries hold (`RI`): `w′ = Σₛ Â[r, s]
ẑ[s]` (`dotAcc`), `ĉ t̂₁[r]` with `t̂₁[r]` from the argument `t1` (`T1Ok`), `w′ = NTT⁻¹(… - ĉ
t̂₁[r])` (`wRow`), its `UseHint`s with `h[r]` (`w1Row`), and their
`SimpleBitPack` to row `r` of `w1Encode(w′₁)` (`row_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Impl.MlDsa.X86.KeyGen (callP)
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv simpleBitPack)
open VG.Proof.MlDsa (PolyIs NatPolyIs Reduced polyAt HintIs)
open VG.Proof.MlDsa.Verify (vZ vHint zHat dotAcc t1Hat wRow w1Row vT1)
open VG.Spec.Sha3 (bytesAt)

/-- In row `r`, with the facts `Q` about the temporaries. -/
def RI (p : Params) (r : Nat)
    (Q : List (Vector Bool Spec.MlDsa.n) → (Nat → Nat → Poly) → Poly → State → Mem → Prop) (s₀ s : State) : Prop :=
  ∃ h A C, CX p s₀ h A C p.ℓ true r s ∧ Q h A C s₀ s.mem

theorem CX.zh {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {cd : Bool}
    {nr : Nat} {s₀ s : State} (hc : CX p s₀ h A C p.ℓ cd nr s) {i : Nat} (hi : i < p.ℓ) :
    PolyIs s.mem (Buf.addr s₀ (pZ i)) (zHat p (vSig p s₀) i) := by
  have e := hc.z i hi
  simp only [hi, ite_true] at e
  exact e

theorem CX.ch {p : Params} {h : List (Vector Bool Spec.MlDsa.n)} {A : Nat → Nat → Poly} {C : Poly} {j nr : Nat}
    {s₀ s : State} (hc : CX p s₀ h A C j true nr s) : PolyIs s.mem (Buf.addr s₀ pC) (ntt C) := by
  have e := hc.c
  simp only [ite_true] at e
  exact e

theorem natPoly_le {m : Mem} {a : Addr} {f : Vector Nat Spec.MlDsa.n} (h : NatPolyIs m a f) {b : Nat}
    (hb : ∀ i (hi : i < Spec.MlDsa.n), f[i] ≤ b) : ∀ i < Spec.MlDsa.n, (Proof.MlDsa.coeffAt m a i).toNat ≤ b :=
  fun i hi => by
    have e := congrArg (·[i]'hi) h
    simp only [Proof.MlDsa.natPolyAt, Vector.getElem_ofFn] at e
    rw [e]; exact hb i hi

/-- `t1` holds `t̂₁` of the public key, on entry. -/
abbrev T1Ok (p : Params) (s₀ : State) : Prop :=
  ∀ r < p.k, PolyIs s₀.mem (Buf.addr s₀ (tB r)) (t1Hat (vPk p s₀) r)

/-- A piece with a precondition `φ` on the initial state, which it keeps. -/
theorem piece_pure {Pre : State → Prop} {Pub : State → State → Prop} {A B : State → State → Prop} {c : Prog isa}
    (φ : State → Prop) (h : Piece Pre Pub A B c) :
    Piece Pre Pub (fun s₀ s => A s₀ s ∧ φ s₀) (fun s₀ s => B s₀ s ∧ φ s₀) c where
  wp s₀ s hp ha := (h.wp s₀ s hp ha.1).mono fun _ hb => ⟨hb, ha.2⟩
  ct s₀ s₀' hp hp' hq := (h.ct s₀ s₀' hp hp' hq).mono (fun _ _ ⟨a, a'⟩ => ⟨a.1, a'.1⟩) fun _ _ h => h

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p) {r : Nat} (hr : r < p.k)
include hP hF hr

theorem mulW_row : VP p (CI p · p.ℓ true r)
    (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r 1))
    (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pW, .buf (pA r 0), .buf (pZ 0)]) := by
  have hl := hF.l
  refine mul_piece (Y := YV p) _ _ _ _ _ _ hP.mul (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨_, _, _, h⟩ => ⟨h.ctx, (h.a r hr 0 (by omega_using [hl])).1, (h.zh (by omega_using [hl])).1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega_using [])
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lvd) (by lvd) fr h', ?_⟩
  rw [(h.a r hr 0 (by omega_using [hl])).2, (h.zh (by omega_using [hl])).2] at out
  show PolyIs _ _ (Spec.MlDsa.add Spec.MlDsa.zero _)
  rw [Proof.MlDsa.Verify.add_zero_left]
  exact out

theorem mulAddW_row {j : Nat} (hj : j < p.ℓ) :
    VP p (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r j))
      (RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r (j + 1)))
      (mulAddS P r j) := by
  have hl := hF.l
  refine mulAdd_piece (Y := YV p) _ _ _ _ _ _ hP.mulAdd (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1, (h.a r hr j hj).1, (h.zh hj).1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega_using [])
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lvd) (by lvd) fr h', ?_⟩
  rw [hw.2, (h.a r hr j hj).2, (h.zh hj).2] at out
  exact out

theorem mulT_row : VP p (fun s₀ s => RI p r (fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ)) s₀ s ∧
      T1Ok p s₀)
    (fun s₀ s => RI p r (fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT2) (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r))) s₀ s ∧ T1Ok p s₀)
    (callP vS "vg_mldsa_multiply_ntt" P.mul [.buf pT2, .buf pC, .buf (tB r)]) := by
  have tp : ∀ {s₀ s : State}, TPre (YV p) s₀ → Ctx (YV p) s₀ s → T1Ok p s₀ →
      PolyIs s.mem (Buf.addr s₀ (tB r)) (t1Hat (vPk p s₀) r) := fun hp hc ht =>
    Proof.MlDsa.Verify.polyIs_congr (fun k hk => hc.ro hp (b := tB r) (by lvd) rfl hk) (ht r hr)
  exact mul_piece (Y := YV p) _ _ _ _ _ _ hP.mul (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ hp ⟨⟨_, _, _, h, _⟩, ht⟩ => ⟨h.ctx, h.ch.1, (tp hp h.ctx ht).1⟩)
    fun s₀ s s' hp ⟨⟨hh, A, C, h, hw⟩, ht⟩ h' fr out => ⟨⟨hh, A, C, h.keep hp (N := 80) (by omega_using [])
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lvd) (by lvd) fr h',
      keepPolyD hp (stkV (by omega_using [])) (by lvd) fr hw, by rw [h.ch.2, (tp hp h.ctx ht).2] at out; exact out⟩, ht⟩

theorem sub_row : VP p (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ) ∧
      PolyIs m (Buf.addr s₀ pT2) (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r)))
    (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (Spec.MlDsa.sub (dotAcc p (vSig p s₀) A r p.ℓ)
      (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r))))
    (callP vS "vg_mldsa_sub" P.sub [.buf pW, .buf pT2]) :=
  acc_piece (Y := YV p) hP.sub _ _ _ _ (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw, ht⟩ => ⟨h.ctx, hw.1, ht.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw, ht⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega_using [])
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lvd) (by lvd) fr h', by rw [hw.2, ht.2] at out; exact out⟩

theorem inv_rowV : VP p (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (Spec.MlDsa.sub
      (dotAcc p (vSig p s₀) A r p.ℓ) (Spec.MlDsa.multiplyNTT (ntt C) (t1Hat (vPk p s₀) r))))
    (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (wRow p (vPk p s₀) (vSig p s₀) A (ntt C) r))
    (callP vS "vg_mldsa_inv_ntt" P.invNtt [.buf pW, .buf (ssB 1024)]) :=
  inPlace_piece (Y := YV p) hP.invNtt vS (oP 18) vS oSS (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega_using [])
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lvd) (by lvd) fr h', by rw [hw.2] at out; exact out⟩

omit hP in
theorem addr_pB {s₀ : State} (hp : TPre (YV p) s₀) :
    Buf.addr s₀ (pB r) = Buf.addr s₀ (hB p.k) + BitVec.ofNat 64 (1024 * r) := by
  rw [Buf.addr_eq hp (b := pB r) (by lvd), Buf.addr_eq hp (b := hB p.k) (by lvd), BitVec.add_assoc,
    ← BitVec.ofNat_add]
  simp only [oP]

theorem hint_row : VP p (RI p r fun _ A C s₀ m => PolyIs m (Buf.addr s₀ pW) (wRow p (vPk p s₀) (vSig p s₀) A (ntt C) r))
    (RI p r fun h A C s₀ m => NatPolyIs m (Buf.addr s₀ pW1) (w1Row p (vPk p s₀) (vSig p s₀) A (ntt C) h r))
    (callP vS "vg_mldsa_use_hint" P.useHint [.buf (pB r), .buf pW, .imm p.γ₂, .buf pW1]) :=
  useHint_piece (Y := YV p) hP.useHint vS (oP r) vS (oP 18) p.γ₂ vS (oP 19) hF.g2 (by lvd)
    (Nat.le_of_eq (YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, hw.1⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, h.keep hp (N := 80) (by omega_using [])
      (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lvd) (by lvd) fr h', by
        have e := addr_pB hF hr hp
        simp only [pB, sb] at e
        rw [hw.2, e, Proof.MlDsa.Verify.hintAt_row h.hint hr] at out
        exact out⟩

theorem pack_row : VP p (RI p r fun h A C s₀ m =>
      NatPolyIs m (Buf.addr s₀ pW1) (w1Row p (vPk p s₀) (vSig p s₀) A (ntt C) h r))
    (CI p · p.ℓ true (r + 1))
    (callP vS "vg_mldsa_simple_bit_pack" P.simpleBitPack
      [.buf pW1, .imm (w1Max p), .buf (sb (oB + w1Len p * r) (w1Len p)), .imm (w1Len p)]) := by
  have hwr := w_row hr
  refine sbp_piece (Y := YV p) hP.simpleBitPack vS (oP 19) (w1Max p) vS (oB + w1Len p * r) (w1Len p) hF.sbp.1
    hF.sbp.2 (by lvd) (Nat.le_of_eq (YV_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ ⟨_, _, _, h, hw⟩ => ⟨h.ctx, natPoly_le hw fun i hi => by
      simp only [w1Row, Vector.getElem_zipWith]
      exact Proof.MlDsa.Verify.useHint_le hF.g2 _ _⟩)
    fun s₀ s s' hp ⟨hh, A, C, h, hw⟩ h' fr out => ⟨hh, A, C, ?_⟩
  have hc := h.keep hp (N := 80) (by omega_using []) (by safeCs hF (Nat.le_of_lt hr)) (fun i hi => by lvd) (by lvd) fr h'
  refine ⟨hc.ctx, hc.norms, hc.hh, hc.hint, hc.a, hc.z, hc.c, hc.gc, fun r' hr' => ?_⟩
  rcases (by omega_using [hr'] : r' < r ∨ r' = r) with hr' | rfl
  · have := w_rows hr' (Nat.le_of_lt hr)
    rw [keepBytes hp (stkV (by omega_using [])) (by lvd) fr]; exact h.w r' hr'
  · rw [hw] at out; exact out

theorem row_piece : VP p (fun s₀ s => CI p s₀ p.ℓ true r s ∧ T1Ok p s₀)
    (fun s₀ s => CI p s₀ p.ℓ true (r + 1) s ∧ T1Ok p s₀) (row P p r) := by
  have hl := hF.l
  unfold row
  refine (piece_pure (T1Ok p) (mulW_row hP hF hr)).seq ?_
  refine Piece.seq (B := fun s₀ s => RI p r (fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r p.ℓ)) s₀ s ∧
      T1Ok p s₀)
    (piece_pure (T1Ok p) ((seqR_piece (I := fun j => RI p r fun _ A _ s₀ m => PolyIs m (Buf.addr s₀ pW) (dotAcc p (vSig p s₀) A r j))
      (p.ℓ - 1) 1 fun j _ hj => mulAddW_row hP hF hr (by omega_using [hl, hj])).mono (fun _ _ _ h => h)
      fun _ _ _ h => by rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_using [hl]] at h)) ?_
  exact (mulT_row hP hF hr).seq ((piece_pure (T1Ok p) (sub_row hP hF hr)).seq
    ((piece_pure (T1Ok p) (inv_rowV hP hF hr)).seq ((piece_pure (T1Ok p) (hint_row hP hF hr)).seq
      (piece_pure (T1Ok p) (pack_row hP hF hr)))))

end

end VG.Proof.MlDsa.X86.Verify
