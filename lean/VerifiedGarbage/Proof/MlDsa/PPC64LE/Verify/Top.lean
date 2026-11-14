module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Cmp
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.SampC
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Compute
import VerifiedGarbage.Proof.MlDsa.Verify.Norm
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallV
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Copy
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Kernel
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Cmp
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final

/-! ### `MlDsa.PPC64LE.Verify.Row`, which only this module used -/

section

/-!
# ML-DSA verification on PPC64LE: a row of `w′₁`

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Row.lean`): row `r` of
`w′ = NTT⁻¹(Â ẑ - ĉ t̂₁)`, then `w′₁ = UseHint(h[r], w′)`, packed to `B`
(`row_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee ip_ok ip_tr
  mul_ok mul_tr mulAdd_ok mulAdd_tr sub_ok sub_tr MulOk AddOk IpOk T1Ok t1_ok t1_tr UhOk uh_ok uh_tr SbpOk sbp_ok
  sbp_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD reg)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlDsa.PPC64LE.KeyGen (seqR)
open VG.Spec.MlDsa (Params toRq ntt nttInv multiplyNTT sub simpleBitPack useHint ofInt simpleBitUnpack t1Max d n q)
open VG.Proof.MlDsa (HintIs PolyIs NatPolyIs polyAt natPolyAt coeffAt Reduced)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row wRow dotAcc t1Hat vT1)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- The polynomial `j` of the working space is `f`. -/
abbrev PIs (p : Params) (STK : Nat) (σ : State) (j : Nat) (f : Spec.MlDsa.Poly) (s : State) : Prop :=
  PolyIs s.mem ((vlay p STK σ).A 0 (oP j)) f

/-- In row `r`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (STK : Nat) (r : Nat)
    (f : State → (Nat → Nat → Spec.MlDsa.Poly) → Spec.MlDsa.Poly → List (Vector Bool n) → State → Prop)
    (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R p.ℓ true r s ∧ f σ A' cc h s

/-- `t₁[r]` unpacked. -/
abbrev t1Raw (pk : List Byte) (r : Nat) : Spec.MlDsa.Poly := (vT1 pk r).map fun c => ofInt (c * 2 ^ d : Nat)

theorem KC5.aR {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc nr} {s : State}
    (hk : KC5 p STK σ A' cc h R nz nc nr s) {r j : Nat} (hr : r < p.k) (hj : j < p.ℓ) :
    PIs p STK σ (20 + 8 * r + j) (A' r j) s := hk.a r hr j hj

theorem KC5.zR {p : Params} {STK : Nat} {σ : State} {A' cc h R nc nr} {s : State}
    (hk : KC5 p STK σ A' cc h R p.ℓ nc nr s) {j : Nat} (hj : j < p.ℓ) :
    PIs p STK σ (8 + j) (zHat p (sgOf p σ) j) s := by
  have := hk.z j hj; rwa [ifp hj] at this

theorem KC5.cR {p : Params} {STK : Nat} {σ : State} {A' cc h R nr} {s : State}
    (hk : KC5 p STK σ A' cc h R p.ℓ true nr s) : PIs p STK σ 15 (ntt cc) s := by
  have := hk.c; rwa [ifp rfl] at this

/-! ## A kernel's cache -/

/-- The precondition of a kernel's verification. -/
abbrev CPre (p : Params) (STK : Nat) (σ : State) : Prop := VPre p STK σ ∧ VCache p STK σ

/-- Its public data: `verifyContract`'s, and the cache's pointer and length. -/
def cPub (p : Params) (σ₁ σ₂ : State) : Prop :=
  vPub p σ₁ σ₂ ∧ σ₁.gpr .r14 = σ₂.gpr .r14 ∧ σ₁.gpr .r15 = σ₂.gpr .r15

/-- The pieces of a kernel's verification. -/
abbrev CPiece (p : Params) (STK : Nat) := Piece (CPre p STK) (cPub p)

theorem VPiece.cache {p : Params} {STK : Nat} {I J : State → State → Prop} {c : Prog isa}
    (h : VPiece p STK I J c) : CPiece p STK I J c :=
  ⟨fun σ s hp hs => h.ok σ s hp.1 hs, RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ =>
    ⟨σ₁, σ₂, p₁.1, p₂.1, pub.1, i₁, i₂⟩) fun _ _ h => h⟩

/-- A branch on the cache's length, which the entry states fix. -/
theorem Piece.ite15 {p : Params} {STK : Nat} {I J : State → State → Prop} {t e : Prog isa}
    (h15 : ∀ σ s, CPre p STK σ → I σ s → s.gpr .r15 = σ.gpr .r15)
    (ht : CPiece p STK (fun σ s => I σ s ∧ σ.gpr .r15 ≠ 0) J t)
    (he : CPiece p STK (fun σ s => I σ s ∧ σ.gpr .r15 = 0) J e) :
    CPiece p STK I J (.ite (.nonzero .d .r15) t e) := by
  refine ⟨fun σ s hp hs => WP.ite _ (eval_nonzero s .r15) (fun hb => ht.ok σ s hp ⟨hs, ?_⟩)
    fun hb => he.ok σ s hp ⟨hs, ?_⟩, ?_⟩
  · rw [← h15 σ s hp hs]; simpa using hb
  · rw [← h15 σ s hp hs]; simpa using hb
  · refine RelCT.ite (fun x y ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => by
      rw [eval_nonzero, eval_nonzero, h15 _ _ p₁ i₁, h15 _ _ p₂ i₂, pub.2.2]) ?_ ?_
    · exact RelCT.mono ht.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩, hb⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨i₁, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; simpa using hb⟩, ⟨i₂, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; rw [← pub.2.2]; simpa using hb⟩⟩) fun _ _ h => h
    · exact RelCT.mono he.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩, hb⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, ⟨i₁, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; simpa using hb⟩, ⟨i₂, by
        rw [eval_nonzero, h15 _ _ p₁ i₁] at hb; rw [← pub.2.2]; simpa using hb⟩⟩) fun _ _ h => h

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
  {r : Nat} (hr : r < p.k)
include hP hF hS hr

/-! ## `W = Σₛ Â[r, s] ẑ[s]` -/

omit hP hS in
theorem mulW_m {σ : State} {j : Nat} (hj : j < p.ℓ) : MulOk (vlay p STK σ) vWb pW (pA r j) (pZ j) := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, by vsep hF,
    by vsep hF⟩

theorem mulW_piece :
    VPiece p STK (KX p STK p.ℓ true r) (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r 1))
      (mulAt P pW (pA r 0) (pZ 0)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5⟩ => ?_, ?_⟩
  · have ha := hk5.aR hr (j := 0) (by omega_using [hl])
    have hz := hk5.zR (j := 0) (by omega_using [hl])
    refine mul_ok hP.mul hk5.vc.site hS (mulW_m hF hr (by omega_using [hl])) ha.1 hz.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    show PolyIs s'.mem (lpa (vlay p STK σ) pW) _
    rw [show dotAcc p (sgOf p σ) A' r 1 = _ from Proof.MlDsa.Verify.add_zero_left _]
    have e1 : polyAt s.mem (lpa (vlay p STK σ) (pA r 0)) = A' r 0 := ha.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) (pZ 0)) = zHat p (sgOf p σ) 0 := hz.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) (pA r 0)) ∧ Reduced x.mem (lpa (vlay p STK σ) (pZ 0))) ∧
      (Reduced y.mem (lpa (vlay p STK σ) (pA r 0)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ 0))))
      (RelCT.exists_ fun σ => mul_tr hP.mul hS (mulW_m hF (σ := σ) hr (by omega_using [hl]))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
    have a₂ : Reduced _ (lpa (vlay p STK _) (pA r 0)) := (h₂.aR hr (j := 0) (by omega_using [hl])).1
    have z₂ : Reduced _ (lpa (vlay p STK _) (pZ 0)) := (h₂.zR (j := 0) (by omega_using [hl])).1
    rw [← vlay_pub pub] at a₂ z₂
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨(h₁.aR hr (j := 0) (by omega_using [hl])).1, (h₁.zR (j := 0) (by omega_using [hl])).1⟩, ⟨a₂, z₂⟩⟩

theorem mulAddW_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r j))
      (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r (j + 1)))
      (mulAddAt P pW (pA r j) (pZ j)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · have ha := hk5.aR hr hj
    have hz := hk5.zR hj
    refine mulAdd_ok hP.mulAdd hk5.vc.site hS (mulW_m hF hr hj) hw.1 ha.1 hz.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    show PolyIs s'.mem (lpa (vlay p STK σ) pW) _
    have e0 : polyAt s.mem (lpa (vlay p STK σ) pW) = dotAcc p (sgOf p σ) A' r j := hw.2
    have e1 : polyAt s.mem (lpa (vlay p STK σ) (pA r j)) = A' r j := ha.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) (pZ j)) = zHat p (sgOf p σ) j := hz.2
    rw [e0, e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced x.mem (lpa (vlay p STK σ) (pA r j)) ∧
        Reduced x.mem (lpa (vlay p STK σ) (pZ j))) ∧
      (Reduced y.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) (pA r j)) ∧
        Reduced y.mem (lpa (vlay p STK σ) (pZ j))))
      (RelCT.exists_ fun σ => mulAdd_tr hP.mulAdd hS (mulW_m hF (σ := σ) hr hj)
        fun x y ⟨T, ⟨a, b, c⟩, ⟨d, e, f⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d, e, f⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    have a₂ : Reduced _ (lpa (vlay p STK _) (pA r j)) := (h₂.aR hr hj).1
    have z₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := (h₂.zR hj).1
    rw [← vlay_pub pub] at w₂' a₂ z₂
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨w₁.1, (h₁.aR hr hj).1, (h₁.zR hj).1⟩, ⟨w₂', a₂, z₂⟩⟩

theorem dot_piece :
    VPiece p STK (KX p STK p.ℓ true r) (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ))
      (dot P p r) := by
  have hl := hF.l
  unfold dot
  refine (mulW_piece hP hF hS hr).seq (Piece.mono (Piece.seqR
    (I := fun j => RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r j)) (p.ℓ - 1) 1
    fun j h1 h2 => mulAddW_piece hP hF hS hr (by omega_using [hl, h2])) (fun _ _ _ h => h) fun _ _ _ h => ?_)
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega_using [hl]] at h

/-! ## `t̂₁[r]` -/

/-- After `t₁[r]`. -/
abbrev F2 (p : Params) (STK r : Nat) (t : State → Spec.MlDsa.Poly) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly)
    (_cc : Spec.MlDsa.Poly) (_h : List (Vector Bool n)) (s : State) : Prop :=
  PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ) s ∧ PIs p STK σ 16 (t σ) s

omit hP hS in
theorem t1_m {σ : State} : T1Ok (vlay p STK σ) vWb (.r30, 32 + 320 * r) pT := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, by vsep hF⟩

theorem t1_piece :
    VPiece p STK (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ))
      (RowI p STK r (F2 p STK r fun σ => t1Raw (pkOf p σ) r)) (unpackT1At P (.r30, 32 + 320 * r) pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold unpackT1At
    refine t1_ok hP.unpackT1 hk5.vc.site hS (t1_m hF hr) fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e : bytesAt s.mem (lpa (vlay p STK σ) (.r30, 32 + 320 * r)) 320 =
        ((pkOf p σ).drop (32 + 320 * r)).take 320 := pk_slice hk5.vc (by rw [hF.pk]; omega_using [hr])
    rw [e] at hb
    exact hb
  · unfold unpackT1At
    exact rel_of (RelCT.exists_ fun σ => t1_tr hP.unpackT1 hS (t1_m hF (σ := σ) hr) fun x y h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩

omit hP hS hr in
theorem nttT_m {σ : State} : PtrIn (vlay p STK σ) pT 1024 ∧ PtrIn (vlay p STK σ) (sc oSS) 1024 ∧
    sepB (vlay p STK σ).sizes (tri pT 1024) (tri (sc oSS) 1024) = true := by
  have hk := hF.k
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, by vsep hF⟩

theorem nttT_piece :
    VPiece p STK (RowI p STK r (F2 p STK r fun σ => t1Raw (pkOf p σ) r))
      (RowI p STK r (F2 p STK r fun σ => t1Hat (pkOf p σ) r)) (nttAt P pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · obtain ⟨m1, m2, m3⟩ := nttT_m hF (STK := STK) (σ := σ)
    unfold nttAt
    refine ip_ok (t := ntt) hP.ntt hk5.vc.site hS ⟨m1, m2, show ix Reg.r31 ∈ vWb by decide,
      show ix Reg.r31 ∈ vWb by decide, m3⟩ ht.1 fun s' k' hb => ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e : polyAt s.mem (lpa (vlay p STK σ) pT) = t1Raw (pkOf p σ) r := ht.2
    rw [e] at hb
    exact hb
  · unfold nttAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) pT) ∧ Reduced y.mem (lpa (vlay p STK σ) pT))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := nttT_m hF (STK := STK) (σ := σ)
        exact ip_tr (t := ntt) hP.ntt hS ⟨m1, m2, show ix Reg.r31 ∈ vWb by decide,
          show ix Reg.r31 ∈ vWb by decide, m3⟩ fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _, t₁⟩ ⟨_, _, _, _, h₂, _, t₂⟩ => ?_
    have t₂' : Reduced _ (lpa (vlay p STK _) pT) := t₂.1
    rw [← vlay_pub pub] at t₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, t₁.1, t₂'⟩

omit hP hS in
/-- `t̂₁[r]` copied from the cache. -/
theorem cachedT_piece :
    CPiece p STK (fun σ s => RowI p STK r (fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ)) σ s ∧
        σ.gpr .r15 ≠ 0)
      (RowI p STK r (F2 p STK r fun σ => t1Hat (pkOf p σ) r)) (Impl.MlDsa.PPC64LE.copyW (.r14, 1024 * r) pT 128) := by
  have hk := hF.k; have hscr := hF.scr
  have hoT : oP 16 + 1024 ≤ scrLen p := by simp only [oP]; omega_using [hscr]
  refine ⟨fun σ s hp ⟨⟨A', cc, h, R, hk5, hw⟩, hne⟩ => ?_, ?_⟩
  · have vc := hk5.vc
    have hs := vc.site
    have g14 : s.gpr .r14 = σ.gpr .r14 := vc.pres .r14 (by decide) (by decide)
    have g31 : s.gpr .r31 = vScr σ := hs.r31
    obtain ⟨hlen, -⟩ := hp.2.polys.resolve_left hne
    have hsub : Region.Sub ⟨σ.gpr .r14 + BitVec.ofNat 64 (1024 * r), 8 * 128⟩
        (reg (σ.gpr .r14) (σ.gpr .r15).toNat) :=
      Offset.sub_base _ (by rw [hlen]; show 1024 * r + 1024 ≤ 4 * 256 * p.k; omega_using [hr])
    have dsub : Region.Sub ⟨vScr σ + BitVec.ofNat 64 (oP 16), 8 * 128⟩ (reg (vScr σ) (scrLen p)) :=
      Offset.sub_base _ hoT
    have cr : PPC64LE.Covers [⟨s.gpr .r14 + BitVec.ofNat 64 (1024 * r), 8 * 128⟩] (s.rd ++ s.wr) := by
      rw [g14, vc.rd]
      exact Covers.of_sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_left _ hp.2.rd, 1024 * r, rfl,
          by rw [hlen]; show 1024 * r + 1024 ≤ 4 * 256 * p.k; omega_using [hr]⟩
    have cw : PPC64LE.Covers [⟨s.gpr .r31 + BitVec.ofNat 64 (oP 16), 8 * 128⟩] s.wr := by
      rw [g31, vc.wr, hp.1.wr]
      exact Covers.of_sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_singleton_self _, oP 16, rfl, hoT⟩
    have hd : (⟨s.gpr .r14 + BitVec.ofNat 64 (1024 * r), 8 * 128⟩ : Region).Disjoint
        ⟨s.gpr .r31 + BitVec.ofNat 64 (oP 16), 8 * 128⟩ := by
      rw [g14, g31]; exact (hp.2.d_c.sub_left hsub).sub_right dsub
    refine WP.mono (copyW_ok (sb := .r14) (db := .r31) (by decide) (by decide)
      (by omega_using [hr, hk]) (by simp only [oP]; omega_using []) (by decide) (by decide) cr cw hd) fun s' ⟨k, hbt⟩ => ?_
    rw [g31] at k hbt
    rw [g14] at hbt
    have k' : Kept ((vlay p STK σ).RL [tri pT 1024]) s s' :=
      k.mono fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact List.mem_cons_self ..
    refine ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)),
      polyIs_keepW hs.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    show PolyIs s'.mem (vScr σ + BitVec.ofNat 64 (oP 16)) (t1Hat (pkOf p σ) r)
    rw [← Proof.MlDsa.PreparedKey.public_poly p _ hr]
    have := vc.cache hp.2 hne r hr
    rw [show 4 * Spec.MlDsa.n * r = 1024 * r by show 4 * 256 * r = 1024 * r; omega_using []] at this
    exact Proof.MlDsa.PreparedKey.polyIs_of_copy hbt this
  · refine rel_of (copyW_tr (by decide) (by decide) (by decide) (by omega_using [hr, hk]) (by simp only [oP]; omega_using [])
      (by decide) (P := fun x y => x.sp = y.sp ∧ x.gpr .r14 = y.gpr .r14 ∧ x.gpr .r31 = y.gpr .r31) fun _ _ h => h)
      fun σ₁ σ₂ x y p₁ p₂ pub ⟨⟨_, _, _, _, h₁, _⟩, _⟩ ⟨⟨_, _, _, _, h₂, _⟩, _⟩ => ⟨?_, ?_, ?_⟩
    · rw [h₁.vc.sp, h₂.vc.sp, pub.1.1]
    · rw [h₁.vc.pres .r14 (by decide) (by decide), h₂.vc.pres .r14 (by decide) (by decide), pub.2.1]
    · rw [h₁.vc.site.r31, h₂.vc.site.r31]; exact pub.1.2.2.2.2.1

/-- `t̂₁[r]`, from the cache if `r15 ≠ 0` and from `pk` otherwise. -/
theorem keyRow_piece :
    CPiece p STK (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ))
      (RowI p STK r (F2 p STK r fun σ => t1Hat (pkOf p σ) r)) (keyRow P r) := by
  unfold keyRow
  exact Piece.ite15 (fun σ s _ ⟨_, _, _, _, hk5, _⟩ => hk5.vc.pres .r15 (by decide) (by decide))
    (cachedT_piece hF hr)
    (Piece.mono (VPiece.cache ((t1_piece hP hF hS hr).seq (nttT_piece hP hF hS hr))) (fun _ _ _ h => h.1) fun _ _ _ h => h)

/-! ## `W = NTT⁻¹(W - ĉ t̂₁[r])` -/

/-- After `ĉ t̂₁[r]`. -/
abbrev F4 (p : Params) (STK r : Nat) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (_h : List (Vector Bool n)) (s : State) : Prop :=
  PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ) s ∧ PIs p STK σ 17 (multiplyNTT (ntt cc) (t1Hat (pkOf p σ) r)) s

omit hP hS hr in
theorem mulT_m {σ : State} : MulOk (vlay p STK σ) vWb pT2 pC pT := by
  have hk := hF.k
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, by vsep hF,
    by vsep hF⟩

theorem mulT_piece :
    VPiece p STK (RowI p STK r (F2 p STK r fun σ => t1Hat (pkOf p σ) r)) (RowI p STK r (F4 p STK r))
      (mulAt P pT2 pC pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · have hc := hk5.cR
    refine mul_ok hP.mul hk5.vc.site hS (mulT_m hF) hc.1 ht.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e1 : polyAt s.mem (lpa (vlay p STK σ) pC) = ntt cc := hc.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) pT) = t1Hat (pkOf p σ) r := ht.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) pC) ∧ Reduced x.mem (lpa (vlay p STK σ) pT)) ∧
      (Reduced y.mem (lpa (vlay p STK σ) pC) ∧ Reduced y.mem (lpa (vlay p STK σ) pT)))
      (RelCT.exists_ fun σ => mul_tr hP.mul hS (mulT_m hF (σ := σ))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _, t₁⟩ ⟨_, _, _, _, h₂, _, t₂⟩ => ?_
    have c₂ : Reduced _ (lpa (vlay p STK _) pC) := h₂.cR.1
    have t₂' : Reduced _ (lpa (vlay p STK _) pT) := t₂.1
    rw [← vlay_pub pub] at c₂ t₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨h₁.cR.1, t₁.1⟩, ⟨c₂, t₂'⟩⟩

omit hP hS hr in
theorem subW_m {σ : State} : AddOk (vlay p STK σ) vWb pW pT2 := by
  have hk := hF.k
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, by vsep hF⟩

theorem subW_piece :
    VPiece p STK (RowI p STK r (F4 p STK r))
      (RowI p STK r fun σ A' cc _ => PIs p STK σ 18
        (sub (dotAcc p (sgOf p σ) A' r p.ℓ) (multiplyNTT (ntt cc) (t1Hat (pkOf p σ) r))))
      (subAt P pW pT2) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · refine sub_ok hP.sub hk5.vc.site hS (subW_m hF) hw.1 ht.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    have e1 : polyAt s.mem (lpa (vlay p STK σ) pW) = dotAcc p (sgOf p σ) A' r p.ℓ := hw.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) pT2) = _ := ht.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced x.mem (lpa (vlay p STK σ) pT2)) ∧
      (Reduced y.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) pT2)))
      (RelCT.exists_ fun σ => sub_tr hP.sub hS (subW_m hF (σ := σ))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁, t₁⟩ ⟨_, _, _, _, h₂, w₂, t₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    have t₂' : Reduced _ (lpa (vlay p STK _) pT2) := t₂.1
    rw [← vlay_pub pub] at w₂' t₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨w₁.1, t₁.1⟩, ⟨w₂', t₂'⟩⟩

omit hP hS hr in
theorem invW_m {σ : State} : PtrIn (vlay p STK σ) pW 1024 ∧ PtrIn (vlay p STK σ) (sc oSS) 1024 ∧
    sepB (vlay p STK σ).sizes (tri pW 1024) (tri (sc oSS) 1024) = true := by
  have hk := hF.k
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, by vsep hF⟩

theorem invW_piece :
    VPiece p STK (RowI p STK r fun σ A' cc _ => PIs p STK σ 18
        (sub (dotAcc p (sgOf p σ) A' r p.ℓ) (multiplyNTT (ntt cc) (t1Hat (pkOf p σ) r))))
      (RowI p STK r fun σ A' cc _ => PIs p STK σ 18 (wRow p (pkOf p σ) (sgOf p σ) A' (ntt cc) r))
      (invNttAt P pW) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · obtain ⟨m1, m2, m3⟩ := invW_m hF (STK := STK) (σ := σ)
    unfold invNttAt
    refine ip_ok (t := nttInv) hP.invNtt hk5.vc.site hS ⟨m1, m2, show ix Reg.r31 ∈ vWb by decide,
      show ix Reg.r31 ∈ vWb by decide, m3⟩ hw.1 fun s' k' hb => ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    have e : polyAt s.mem (lpa (vlay p STK σ) pW) = _ := hw.2
    rw [e] at hb
    exact hb
  · unfold invNttAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) pW))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := invW_m hF (STK := STK) (σ := σ)
        exact ip_tr (t := nttInv) hP.invNtt hS ⟨m1, m2, show ix Reg.r31 ∈ vWb by decide,
          show ix Reg.r31 ∈ vWb by decide, m3⟩ fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    rw [← vlay_pub pub] at w₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, w₁.1, w₂'⟩

/-! ## `w′₁[r]`, packed to `B` -/

omit hP hS in
theorem uh_m {σ : State} : UhOk (vlay p STK σ) vWb (pH r) pW p.γ₂ pW1 := by
  have hk := hF.k
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide, by vsep hF,
    by vsep hF, hF.g2.1, hF.g2.2⟩

omit hP hF hS in
theorem hint_row {σ : State} {m : Mem} {h : List (Vector Bool n)}
    (hh : HintIs m ((vlay p STK σ).A 0 (oP 0)) p.k h) :
    (Proof.MlDsa.hintAt m (lpa (vlay p STK σ) (pH r)) 1).headD (Vector.replicate n false) =
      h.getD r (Vector.replicate n false) := by
  have e : lpa (vlay p STK σ) (pH r) = (vlay p STK σ).A 0 (oP 0) + BitVec.ofNat 64 (1024 * r) := by
    show (vlay p STK σ).A 0 (oP r) = _
    simp only [Lay.A, BitVec.add_assoc, ← BitVec.ofNat_add, show oP 0 + 1024 * r = oP r by simp only [oP]]
  rw [e]
  exact Proof.MlDsa.Verify.hintAt_row hh hr

theorem uh_piece :
    VPiece p STK (RowI p STK r fun σ A' cc _ => PIs p STK σ 18 (wRow p (pkOf p σ) (sgOf p σ) A' (ntt cc) r))
      (RowI p STK r fun σ A' cc h s => NatPolyIs s.mem ((vlay p STK σ).A 0 (oP 19))
        (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r))
      (useHintAt P (pH r) pW p.γ₂ pW1) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold useHintAt
    refine uh_ok hP.useHint hk5.vc.site hS (uh_m hF hr) hw.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chks hF (Nat.le_of_lt hr)), ?_⟩
    have e : polyAt s.mem (lpa (vlay p STK σ) pW) = _ := hw.2
    rw [e, hint_row hr hk5.hint] at hb
    exact hb
  · unfold useHintAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) pW))
      (RelCT.exists_ fun σ => uh_tr hP.useHint hS (uh_m hF (σ := σ) hr)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    rw [← vlay_pub pub] at w₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, w₁.1, w₂'⟩

omit hP hS in
theorem sbpW_m {σ : State} : SbpOk (vlay p STK σ) vWb pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p) := by
  have hk := hF.k
  rcases hF.w1l with e | ⟨e, _⟩ <;>
  exact ⟨⟨vptr_ok rfl (by vlt hF), by vsep hF⟩, ⟨vptr_ok rfl (by simp only [e]; vlt hF), by vsep hF [e]⟩, show ix Reg.r31 ∈ vWb by decide, by vsep hF [e],
    hF.sbp.1, hF.sbp.2.1⟩

omit hP hS hr in
theorem w1_bound {σ : State} {m : Mem} {a : Addr} {A' : Nat → Nat → Spec.MlDsa.Poly} {ch : Spec.MlDsa.Poly}
    {h : List (Vector Bool n)} {r : Nat} (h1 : NatPolyIs m a (w1Row p (pkOf p σ) (sgOf p σ) A' ch h r)) :
    ∀ i < n, (coeffAt m a i).toNat ≤ w1Max p := fun i hi => by
  rw [show (coeffAt m a i).toNat = (w1Row p (pkOf p σ) (sgOf p σ) A' ch h r)[i]'hi from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [w1Row, Vector.getElem_zipWith]
  exact Proof.MlDsa.Verify.useHint_le hF.g2.1 _ _

theorem sbpW_piece :
    VPiece p STK (RowI p STK r fun σ A' cc h s => NatPolyIs s.mem ((vlay p STK σ).A 0 (oP 19))
        (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r))
      (KX p STK p.ℓ true (r + 1)) (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold sbpAt
    refine sbp_ok hP.simpleBitPack hk5.vc.site hS (sbpW_m hF hr) (w1_bound hF hw) fun s' k' hb =>
      ⟨A', cc, h, R, ?_⟩
    have hk' := hk5.keep hF k' (by
      have : w1Len p * r + w1Len p ≤ p.k * w1Len p := by
        rw [← Nat.mul_succ, Nat.mul_comm p.k]; exact Nat.mul_le_mul_left _ hr
      k5chks hF (Nat.le_of_lt hr))
    refine ⟨hk'.vc, hk'.hh, hk'.hint, hk'.a, hk'.z, hk'.c, fun r' hr' => ?_, hk'.r24, hk'.gd⟩
    rcases (by omega_using [hr'] : r' < r ∨ r' = r) with hr' | rfl
    · exact hk'.rows r' hr'
    · show bytesAt s'.mem (lpa (vlay p STK σ) (sc (oB + w1Len p * r'))) (w1Len p) = _
      rw [hb]
      exact congrArg (simpleBitPack · (w1Max p)) hw
  · unfold sbpAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (∀ i < n, (coeffAt x.mem (lpa (vlay p STK σ) pW1) i).toNat ≤ w1Max p) ∧
      (∀ i < n, (coeffAt y.mem (lpa (vlay p STK σ) pW1) i).toNat ≤ w1Max p))
      (RelCT.exists_ fun σ => sbp_tr hP.simpleBitPack hS (sbpW_m hF (σ := σ) hr)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : ∀ i < n, (coeffAt _ (lpa (vlay p STK _) pW1) i).toNat ≤ w1Max p := w1_bound hF w₂
    rw [← vlay_pub pub] at w₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, w1_bound hF w₁, w₂'⟩

theorem row_piece : CPiece p STK (KX p STK p.ℓ true r) (KX p STK p.ℓ true (r + 1)) (row P p r) :=
  (dot_piece hP hF hS hr).cache.seq ((keyRow_piece hP hF hS hr).seq (VPiece.cache ((mulT_piece hP hF hS hr).seq
    ((subW_piece hP hF hS hr).seq ((invW_piece hP hF hS hr).seq
      ((uh_piece hP hF hS hr).seq (sbpW_piece hP hF hS hr)))))))
end

end VG.Proof.MlDsa.PPC64LE.Verify

end

end


/-!
# ML-DSA verification on PPC64LE: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Top.lean`): the function, piece
by piece, for any parameter set of Table 1 and any verified implementations
of the primitives (`verify_piece`, `verify_verified`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv relStart reg)
open VG.Proof.MlDsa.PPC64LE (kSt kSt_gpr kSt_r14 kSt_r15 kSt_sp kSt_rd kSt_wr kSt_mem kernel_wp kernel_tr)
open VG.Impl.MlKem.PPC64LE (topEnd)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlDsa.PPC64LE.KeyGen (seqR)
open VG.Spec.MlDsa (Params Bounds verifyMu minBounds toRq rejNTTPoly sampleInBall)
open VG.Proof.MlDsa (polyAt)
open VG.Proof.MlDsa.Verify (vZ vCt vHint aSeed common_bound verifyMu_rows verifyMu_norm verifyMu_hint_none
  verifyMu_rej_none verifyMu_ball_none verifyMu_mono bmax_left bmax_right normR_vZ_iff)
open VG.Proof.MlDsa.KeyGen (ifn)
open VG.Spec.Sha3 (bytesAt)

/-- A piece keeps a fact about the entry state. -/
theorem pieceFrame {Pre : State → Prop} {Pub : State → State → Prop} {I J : State → State → Prop} {c : Prog isa}
    (h : Piece Pre Pub I J c) (F : State → Prop) :
    Piece Pre Pub (fun σ s => I σ s ∧ F σ) (fun σ s => J σ s ∧ F σ) c :=
  ⟨fun σ s hp ⟨hs, hf⟩ => WP.mono (h.ok σ s hp hs) fun _ h' => ⟨h', hf⟩,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, i₁.1, i₂.1⟩) fun _ _ h => h⟩

/-! ## After the samplers -/

theorem vs4_kx {p : Params} {STK : Nat} {σ s : State} (h : VS4 p STK σ s) : KX p STK 0 false 0 σ s := by
  obtain ⟨hh, e, hi⟩ := h.vb.hint
  exact ⟨fun r c => polyAt s.mem (aA p STK σ r c), polyAt s.mem ((vlay p STK σ).A 0 (oP 15)), hh, s.gpr .r24,
    h.vb.vc, e, hi, fun r hr c hc => ⟨h.red r hr c hc, rfl⟩,
    fun i hi => by rw [ifn (Nat.not_lt_zero i)]; exact h.vb.z i hi, ⟨h.redC, rfl⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), rfl, h.ok⟩

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

theorem compute_piece : CPiece p STK (KX p STK 0 false 0) (KE p STK) (compute P p) := by
  unfold compute
  refine Piece.seq (J := KX p STK p.ℓ false 0) ?_ ((nttC_piece hP hF hS).cache.seq
    (Piece.seq (J := KX p STK p.ℓ true p.k) ?_ ((vhash_piece hF).cache.seq (cmp_piece hF).cache)))
  · refine Piece.mono (Piece.seqR (I := fun j => KX p STK j false 0) p.ℓ 0
      fun j _ hj => (nttZ_piece hP hF hS (by omega_using [hj])).cache) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h
  · refine Piece.mono (Piece.seqR (I := fun r => KX p STK p.ℓ true r) p.k 0
      fun r _ hr => row_piece hP hF hS (by omega_using [hr])) (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

end

/-! ## The result -/

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (pkOf p σ) (muOf σ) (sgOf p σ)

/-- What the result `r` says of `verifyMu`, as `verifyContract` does. -/
abbrev VOut (p : Params) (σ : State) (r : BitVec 64) : Prop :=
  (r = 1 ∧ ∃ b, vv p σ b = some true) ∨ (r = 0 ∧ vv p σ minBounds ≠ some true)

/-- At the end, before the epilogue: the result in `r24`. -/
abbrev VFin (p : Params) (STK : Nat) (σ s : State) : Prop := VC p STK σ s ∧ VOut p σ (s.gpr .r24)

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : vv p σ b = some false) : vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := verifyMu_mono (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := verifyMu_mono (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

theorem ke_out {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : KE p STK σ s)
    (hz : zOk p σ p.ℓ = true) : VFin p STK σ s := by
  obtain ⟨A', cc, hh, R, vc, e, hl, ⟨q, hR, hok, hbad⟩, r24⟩ := h
  refine ⟨vc, ?_⟩
  rw [r24, hR, flag_and]
  cases q with
  | false =>
    refine .inr ⟨rfl, ?_⟩
    rcases hbad rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_rej_none minBounds _ _ e hr hc hn']; nofun
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_ball_none minBounds _ _ e hn']; nofun
  | true =>
    obtain ⟨hA, hB⟩ := hok rfl
    obtain ⟨nA, hnA⟩ := common_bound (P := fun r n => ∀ c < p.ℓ, rejNTTPoly n (aSeed (pkOf p σ) r c) = some (A' r c))
      (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
        common_bound (P := fun c n => rejNTTPoly n (aSeed (pkOf p σ) r c) = some (A' r c))
          (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc => hA r hr c hc
    obtain ⟨bB, hbB⟩ := hB
    obtain ⟨c, hc, hc'⟩ := Option.map_eq_some_iff.mp hbB
    have ev := verifyMu_rows p ⟨0, 0, nA, bB⟩ (pkOf p σ) (muOf σ) (sgOf p σ) e hl hnA hc
    have ew : ((List.range p.k).flatMap fun r => Spec.MlDsa.simpleBitPack
        (Proof.MlDsa.Verify.w1Row p (pkOf p σ) (sgOf p σ) A' (Spec.MlDsa.ntt cc) hh r)
        ((Spec.MlDsa.q - 1) / (2 * p.γ₂) - 1)) = w1Enc p σ A' cc hh := rfl
    rw [decide_eq_true ((normR_vZ_iff hF.nb.2 p hF.g1 _).mpr (of_decide_eq_true hz)), hc', Bool.true_and, ew] at ev
    by_cases hE : Spec.MlDsa.H (muOf σ ++ w1Enc p σ A' cc hh) p.ctildeLen = vCt p (sgOf p σ)
    · exact .inl ⟨by rw [decide_eq_true hE]; rfl, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
    · exact .inr ⟨by rw [decide_eq_false hE]; rfl,
        false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

theorem flag_eq {b : Bool} (h : flag b = 0) : b = false := by
  cases b
  · rfl
  · exact absurd h (by decide)

/-! ## The body -/

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

/-- The samplers and the rest, once `z` is small enough. -/
theorem inner_piece :
    CPiece p STK (V2 p STK p.ℓ) (VFin p STK) (ifOk (.seq (samples P p) (compute P p))) := by
  refine ifOk_piece (v := fun σ => flag (zOk p σ p.ℓ)) (fun _ _ _ h => h.r24) (fun σ₁ σ₂ _ _ pub => ?_)
    ?_ fun σ s _ h hv => ⟨h.vc, .inr ⟨h.r24.trans hv, ?_⟩⟩
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.1.2.2.2.2.2.2.2
    dsimp only [zOk]
    rw [e]
  · refine Piece.mono (pieceFrame ((samples_piece hP hF hS).cache.seq (Piece.mono (compute_piece hP hF hS)
      (fun _ _ _ h => vs4_kx h) fun _ _ _ h => h)) fun σ => zOk p σ p.ℓ = true)
      (fun _ _ _ h => ⟨h, flag_ne.mp h.2⟩) fun _ _ _ ⟨h, hz⟩ => ke_out hF h hz
  · obtain ⟨hh, e, -⟩ := h.hint
    refine verifyMu_norm minBounds _ _ e fun hn => ?_
    have := flag_eq hv
    rw [zOk, decide_eq_false_iff_not] at this
    exact this ((normR_vZ_iff hF.nb.2 p hF.g1 _).mp hn)

omit hP hF hS in
theorem v1_v2 {σ s : State} (h : V1 p STK σ s) (hv : flag (hintOf p σ).isSome ≠ 0) : V2 p STK 0 σ s := by
  cases e : hintOf p σ with
  | none => rw [e] at hv; exact absurd rfl hv
  | some hh =>
    refine ⟨h.vc, ⟨hh, e, h.hint hh e⟩, fun _ h => absurd h (Nat.not_lt_zero _), ?_⟩
    rw [h.r24, e, show zOk p σ 0 = true from decide_eq_true fun _ h => absurd h (Nat.not_lt_zero _)]
    rfl

omit hP hF hS in
theorem v1_out {σ s : State} (h : V1 p STK σ s) (hv : flag (hintOf p σ).isSome = 0) : VFin p STK σ s := by
  refine ⟨h.vc, .inr ⟨h.r24.trans hv, ?_⟩⟩
  have e : hintOf p σ = none := Option.not_isSome_iff_eq_none.mp (by rw [flag_eq hv]; nofun)
  show verifyMu p minBounds _ _ _ ≠ some true
  rw [verifyMu_hint_none minBounds _ _ e]
  nofun

theorem body_piece : CPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r24 = 1) (VFin p STK) (body P p) := by
  have hl := hF.l
  unfold body
  refine (hint_piece hP hF hS).cache.seq (ifOk_piece (v := fun σ => flag (hintOf p σ).isSome) (fun _ _ _ h => h.r24)
    (fun σ₁ σ₂ _ _ pub => ?_) ?_ fun _ _ _ h hv => v1_out h hv)
  · have e : sgOf p σ₁ = sgOf p σ₂ := pub.1.2.2.2.2.2.2.2
    dsimp only [hintOf]
    rw [e]
  · refine Piece.seq (Piece.mono (Piece.seqR (I := fun j => V2 p STK j) p.ℓ 0
      fun j _ hj => (zOne_piece hP hF hS (by omega_using [hj])).cache) (fun _ _ _ h => v1_v2 h.1 h.2) fun _ _ _ h => ?_)
      (inner_piece hP hF hS)
    rwa [Nat.zero_add] at h

end

/-! ## The return -/

theorem vepi_ok {p : Params} (hF : VFacts p) {STK : Nat} {σ s : State} (h : VFin p STK σ s) :
    WP isa (.block topEnd) s fun s' =>
      PPC64LE.target.abiPreserved σ s' ∧ (Spec.MlDsa.verifyContract p PPC64LE.abi STK).post σ s' := by
  obtain ⟨vc, hr⟩ := h
  have hs := vc.site
  have hscr := hF.scr
  have hk := hF.k
  have hin : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions (s.rd ++ s.wr) (vScr σ + BitVec.ofNat 64 o) 8 :=
    fun o h₁ h₂ => mem_rd_wr' (Lay.covers (L := vlay p STK σ) (o := o) (l := 8) (hs.cw 0 (by decide) (by decide))
      (by rw [vlay_size0]; omega_using [hscr, h₂]) _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩)
  refine WP.mono (topEnd_ok hs.r31 vc.sav hin vc.pres)
    fun s' ⟨pr, lr, r3, _, sp', _, _⟩ => ⟨⟨pr, sp'.trans vc.sp, lr⟩, ?_⟩
  sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs]
  rw [r3]
  rcases hr with ⟨e, h⟩ | ⟨e, h⟩ <;> rw [e]
  · exact .inl ⟨rfl, h⟩
  · exact .inr ⟨rfl, h⟩

theorem vepi_piece {p : Params} (hF : VFacts p) {STK : Nat} :
    VPiece p STK (VFin p STK)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p PPC64LE.abi STK).post σ s)
      (.block topEnd) :=
  ⟨fun _ _ _ h => vepi_ok hF h, vrel31 (fun _ _ h => h.1) (by taint_decide)⟩

/-! ## The function -/

theorem verify_piece {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat}
    (hS : S ≤ STK) (h48 : 48 ≤ STK) :
    CPiece p STK (fun σ s => s = σ)
      (fun σ s => PPC64LE.target.abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p PPC64LE.abi STK).post σ s)
      (verify P p) :=
  (vpro_piece hF h48).cache.seq ((body_piece hP hF hS).seq (vepi_piece hF).cache)

/-! ## The kernel -/

/-- The precondition of `verifyWithCacheContract` with `K` bytes of stack. -/
structure KPre (p : Params) (K : Nat) (σ : State) : Prop where
  stk : K ≤ σ.sp.toNat
  rd : σ.rd = [reg (vPk σ) p.pkLen, reg (vMu σ) 64, reg (vSg σ) p.sigLen, reg (σ.gpr .r7) (σ.gpr .r8).toNat]
  wr : σ.wr = [reg (vScr σ) (scrLen p)]
  d_pc : (reg (vPk σ) p.pkLen).Disjoint (reg (vScr σ) (scrLen p))
  d_mc : (reg (vMu σ) 64).Disjoint (reg (vScr σ) (scrLen p))
  d_sc : (reg (vSg σ) p.sigLen).Disjoint (reg (vScr σ) (scrLen p))
  d_cx : (reg (vScr σ) (scrLen p)).Disjoint (reg (σ.gpr .r7) (σ.gpr .r8).toNat)
  b_p : (below σ.sp K).Disjoint (reg (vPk σ) p.pkLen)
  b_m : (below σ.sp K).Disjoint (reg (vMu σ) 64)
  b_s : (below σ.sp K).Disjoint (reg (vSg σ) p.sigLen)
  b_c : (below σ.sp K).Disjoint (reg (vScr σ) (scrLen p))
  b_x : (below σ.sp K).Disjoint (reg (σ.gpr .r7) (σ.gpr .r8).toNat)
  f_p : (vPk σ).toNat + p.pkLen ≤ 2 ^ 64
  f_m : (vMu σ).toNat + 64 ≤ 2 ^ 64
  f_s : (vSg σ).toNat + p.sigLen ≤ 2 ^ 64
  f_c : (vScr σ).toNat + scrLen p ≤ 2 ^ 64
  f_x : (σ.gpr .r7).toNat + (σ.gpr .r8).toNat ≤ 2 ^ 64
  polys : σ.gpr .r8 = 0 ∨ ((σ.gpr .r8).toNat = 4 * Spec.MlDsa.n * p.k ∧
    Proof.MlDsa.CachedPublicPolys p σ.mem (σ.gpr .r7) (pkOf p σ))

theorem kpre_of {p : Params} {k : Nat} {σ : State}
    (h : (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (k + 1)).pre σ) : KPre p (k + 1) σ := by
  sig_pre [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

section
variable {p : Params} {STK : Nat} {σ : State} (h : KPre p (STK + 96) σ)
include h

theorem KPre.fit : STK + 96 < 2 ^ 64 := by have := h.stk; have := σ.sp.isLt; omega_arith

theorem KPre.b96 : Region.Sub (below σ.sp 96) (below σ.sp (STK + 96)) := below_sub (by omega_using []) h.fit

theorem KPre.bSTK : Region.Sub (below (kSt .r7 .r8 σ).sp STK) (below σ.sp (STK + 96)) := by
  rw [kSt_sp]
  intro x hx
  simp only [Region.Contains] at hx ⊢
  have := h.fit; have := h.stk
  bv_omega

/-- Bytes apart from the stack are as on entry, in the state verification starts in. -/
theorem KPre.bytes {a : Addr} {l : Nat} (hd : (below σ.sp (STK + 96)).Disjoint (reg a l)) (hl : l ≤ 2 ^ 64) :
    bytesAt (kSt .r7 .r8 σ).mem a l = bytesAt σ.mem a l :=
  Proof.MlKem.bytesAt_frame (kSt_mem σ) (fun r hr => by
    rw [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left h.b96).symm) hl

theorem kSt_inputs : pkOf p (kSt .r7 .r8 σ) = pkOf p σ ∧ muOf (kSt .r7 .r8 σ) = muOf σ ∧
    sgOf p (kSt .r7 .r8 σ) = sgOf p σ := by
  simp only [pkOf, muOf, sgOf, vPk, vMu, vSg, kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide),
    kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)]
  exact ⟨h.bytes h.b_p (by have := h.f_p; omega_using [this]), h.bytes h.b_m (by decide), h.bytes h.b_s (by have := h.f_s; omega_using [this])⟩

/-- The state verification starts in satisfies `CPre`. -/
theorem kSt_cpre : CPre p STK (kSt .r7 .r8 σ) := by
  have e3 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r3) (by decide) (by decide)
  have e4 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r4) (by decide) (by decide)
  have e5 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r5) (by decide) (by decide)
  have e6 := kSt_gpr (a := .r7) (b := .r8) σ (r := .r6) (by decide) (by decide)
  have e14 : (kSt .r7 .r8 σ).gpr .r14 = σ.gpr .r7 := kSt_r14 σ
  have e15 : (kSt .r7 .r8 σ).gpr .r15 = σ.gpr .r8 := kSt_r15 σ
  have bs := h.bSTK
  have hstk : STK ≤ (kSt .r7 .r8 σ).sp.toNat := by
    rw [kSt_sp]; have := h.stk; have := h.fit; bv_omega
  refine ⟨⟨hstk, ⟨[reg (σ.gpr .r7) (σ.gpr .r8).toNat], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩ <;>
    simp only [vPk, vMu, vSg, vScr, e3, e4, e5, e6, e14, e15, kSt_rd, kSt_wr]
  · rw [h.rd]; rfl
  · exact h.wr
  · exact h.d_pc
  · exact h.d_mc
  · exact h.d_sc
  · exact h.b_p.sub_left bs
  · exact h.b_m.sub_left bs
  · exact h.b_s.sub_left bs
  · exact h.b_c.sub_left bs
  · exact h.f_p
  · exact h.f_m
  · exact h.f_s
  · exact h.f_c
  · rcases h.polys with h0 | ⟨hl, hc⟩
    · exact .inl h0
    · refine .inr ⟨hl, fun i hi => ?_⟩
      rw [kSt_inputs h |>.1]
      have hsub : Region.Sub (Proof.MlDsa.Verify.polyRegion (σ.gpr .r7 + BitVec.ofNat 64 (4 * Spec.MlDsa.n * i)))
          (reg (σ.gpr .r7) (σ.gpr .r8).toNat) :=
        Offset.sub_base _ (by rw [hl]; show 4 * 256 * i + 1024 ≤ 4 * 256 * p.k; omega_using [hi])
      exact Proof.MlDsa.Verify.polyIs_frame (kSt_mem σ) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact (h.b_x.sub_left h.b96).symm.sub_left hsub) (hc i hi)
  · rw [h.rd]; simp
  · exact h.d_cx.symm
  · exact h.b_x.symm.sub_right bs

end

/-- The public data of two kernels' entry states give `cPub` of the states
verification starts in. -/
theorem kSt_cpub {p : Params} {STK : Nat} {σ₁ σ₂ : State} (h₁ : KPre p (STK + 96) σ₁) (h₂ : KPre p (STK + 96) σ₂)
    (hpub : (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (STK + 96)).pub σ₁ σ₂) :
    cPub p (kSt .r7 .r8 σ₁) (kSt .r7 .r8 σ₂) := by
  sig_pub [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig, PPC64LE.abi,
    PPC64LE.argRegs] at hpub
  obtain ⟨hsp, hl, h3, h4, h5, h6, h7, h8⟩ := hpub
  obtain ⟨e12, e3⟩ := List.append_inj (Proof.MlDsa.KeyGen.leakBytes_inj hl)
    (by simp only [List.length_append, Proof.MlKem.bytesAt_length])
  obtain ⟨e1, e2⟩ := List.append_inj e12 (by simp only [Proof.MlKem.bytesAt_length])
  have g : ∀ {r : Reg}, r ≠ .r14 → r ≠ .r15 → σ₁.gpr r = σ₂.gpr r →
      (kSt .r7 .r8 σ₁).gpr r = (kSt .r7 .r8 σ₂).gpr r := fun a b e => by
    rw [kSt_gpr σ₁ a b, kSt_gpr σ₂ a b, e]
  obtain ⟨k₁, m₁, r₁⟩ := kSt_inputs h₁
  obtain ⟨k₂, m₂, r₂⟩ := kSt_inputs h₂
  refine ⟨⟨by rw [kSt_sp, kSt_sp, hsp], g (by decide) (by decide) h3, g (by decide) (by decide) h4,
    g (by decide) (by decide) h5, g (by decide) (by decide) h6, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [k₁, k₂]; exact e1
  · rw [m₁, m₂]; exact e2
  · rw [r₁, r₂]; exact e3
  · rw [kSt_r14, kSt_r14, h7]
  · rw [kSt_r15, kSt_r15, h8]

/-- A state that satisfies `verifyWithCacheContract`'s precondition, for the
contract's satisfiability: an empty cache. -/
def kSat (p : Params) : State where
  gpr r := match r with
    | .r3 => 0x1000 | .r4 => 0x2000 | .r5 => 0x3000 | .r6 => 0x10000 | .r7 => 0x1000 | _ => 0
  lr := 0
  sp := 0x80000
  mem _ := 0
  rd := [⟨0x1000, p.pkLen⟩, ⟨0x2000, 64⟩, ⟨0x3000, p.sigLen⟩, ⟨0x1000, 0⟩]
  wr := [⟨0x10000, scrLen p⟩]

/-- `vg_mldsa*_verify_with_cache` of the parameter set `p` meets its
contract with `S + 96` bytes of stack (the 96 of its frames), for any
verified implementations `P` of the primitives it calls with at most `S`
bytes of stack, `S` at least the 48 bytes the sponge needs, and
verification's frames within `S` bytes. -/
theorem withCache_verified {P : Prims} {S : Nat} (hP : VPrimsOk P S) (h48 : 48 ≤ S)
    (p : Spec.MlDsa.Params) (hp3 : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hd : sdepth (verify P p) ≤ S)
    (hsat : (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (S + 96)).pre (kSat p)) :
    Verified PPC64LE.target (withCache P p) (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (S + 96)) := by
  have hF := vfacts hp3
  have hv := verify_piece hP hF (Nat.le_refl S) h48
  have body (σ : State) (hk : KPre p (S + 96) σ) := hv.ok _ _ (kSt_cpre hk) rfl
  have hd96 (σ : State) (hk : KPre p (S + 96) σ) : ∀ X ∈ σ.wr, (below σ.sp 96).Disjoint X := fun X hX => by
    rw [hk.wr] at hX
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl
    exact hk.b_c.sub_left hk.b96
  have hn (σ : State) (hk : KPre p (S + 96) σ) : sdepth (verify P p) + 96 < 2 ^ 64 := by have := hk.fit; omega_using [hd, this]
  refine ⟨fun σ hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨kSat p, hsat⟩⟩
  · have hk := kpre_of (k := S + 95) hs
    refine WP.mono (kernel_wp (a := .r7) (b := .r8) (by decide) (by decide) (by decide)
      (by have := hk.stk; omega_using [this]) (hd96 σ hk) (hn σ hk)
      (R := fun _ r => (r.setWidth 32 = 1 ∧ ∃ b, vv p σ b = some true) ∨
        (r.setWidth 32 = 0 ∧ vv p σ Spec.MlDsa.minBounds ≠ some true))
      (WP.mono (body σ hk) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩)) fun s' ⟨ha, hq⟩ => ⟨ha, ?_⟩
    · generalize hτ : kSt .r7 .r8 σ = τ at hq
      sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, PPC64LE.abi, PPC64LE.argRegs] at hq
      subst hτ
      obtain ⟨k₁, m₁, r₁⟩ := kSt_inputs hk
      simp only [pkOf, muOf, sgOf, vPk, vMu, vSg, kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide),
        kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)]
        at k₁ m₁ r₁
      rw [kSt_gpr σ (show Reg.r3 ≠ .r14 by decide) (by decide), kSt_gpr σ (show Reg.r4 ≠ .r14 by decide) (by decide),
        kSt_gpr σ (show Reg.r5 ≠ .r14 by decide) (by decide)] at hq
      rw [k₁, m₁, r₁] at hq
      exact hq
    · sig_post [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig,
        PPC64LE.abi, PPC64LE.argRegs]
      exact hq
  · have k₁ := kpre_of (k := S + 95) h₁
    have k₂ := kpre_of (k := S + 95) h₂
    refine (kernel_tr (a := .r7) (b := .r8) (by decide) (by decide) (by decide)
      (P := fun x y => KPre p (S + 96) x ∧ KPre p (S + 96) y ∧
        (Proof.MlDsa.verifyWithCacheContract p PPC64LE.abi (S + 96)).pub x y)
      (fun x y ⟨_, _, hp⟩ => by
        sig_pub [Proof.MlDsa.verifyWithCacheContract, Proof.MlDsa.verifyWithCacheSig, Spec.MlDsa.verifySig,
          PPC64LE.abi, PPC64LE.argRegs] at hp
        exact hp.1)
      (fun x y ⟨a, b, _⟩ => ⟨by have := a.stk; omega_using [this], by have := b.stk; omega_using [this], hd96 x a, hd96 y b⟩) (hn s₁ k₁)
      (fun x y ⟨a, b, _⟩ => ⟨⟨_, body x a⟩, ⟨_, body y b⟩⟩)
      (RelCT.mono hv.tr (fun u v ⟨x, y, ⟨a, b, hp⟩, eu, ev⟩ => by
        subst eu ev; exact ⟨_, _, kSt_cpre a, kSt_cpre b, kSt_cpub a b hp, rfl, rfl⟩) fun _ _ h => h)
      s₁ s₂ t₁ t₂ s₁' s₂' ⟨k₁, k₂, hpub⟩ e₁ e₂).1

end VG.Proof.MlDsa.PPC64LE.Verify
