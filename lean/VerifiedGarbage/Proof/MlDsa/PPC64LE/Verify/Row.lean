module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Compute
import VerifiedGarbage.Proof.MlDsa.Verify.Norm
import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallV
import VerifiedGarbage.Proof.MlDsa.PPC64LE.Copy
import VerifiedGarbage.Proof.MlDsa.PreparedKey.Values
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

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
  · have ha := hk5.aR hr (j := 0) (by omega)
    have hz := hk5.zR (j := 0) (by omega)
    refine mul_ok hP.mul hk5.vc.site hS (mulW_m hF hr (by omega)) ha.1 hz.1 fun s' k' hb =>
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
      (RelCT.exists_ fun σ => mul_tr hP.mul hS (mulW_m hF (σ := σ) hr (by omega))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
    have a₂ : Reduced _ (lpa (vlay p STK _) (pA r 0)) := (h₂.aR hr (j := 0) (by omega)).1
    have z₂ : Reduced _ (lpa (vlay p STK _) (pZ 0)) := (h₂.zR (j := 0) (by omega)).1
    rw [← vlay_pub pub] at a₂ z₂
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨(h₁.aR hr (j := 0) (by omega)).1, (h₁.zR (j := 0) (by omega)).1⟩, ⟨a₂, z₂⟩⟩

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
    fun j h1 h2 => mulAddW_piece hP hF hS hr (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_)
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

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
        ((pkOf p σ).drop (32 + 320 * r)).take 320 := pk_slice hk5.vc (by rw [hF.pk]; omega)
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
  have hoT : oP 16 + 1024 ≤ scrLen p := by simp only [oP]; omega
  refine ⟨fun σ s hp ⟨⟨A', cc, h, R, hk5, hw⟩, hne⟩ => ?_, ?_⟩
  · have vc := hk5.vc
    have hs := vc.site
    have g14 : s.gpr .r14 = σ.gpr .r14 := vc.pres .r14 (by decide) (by decide)
    have g31 : s.gpr .r31 = vScr σ := hs.r31
    obtain ⟨hlen, -⟩ := hp.2.polys.resolve_left hne
    have hsub : Region.Sub ⟨σ.gpr .r14 + BitVec.ofNat 64 (1024 * r), 8 * 128⟩
        (reg (σ.gpr .r14) (σ.gpr .r15).toNat) :=
      Offset.sub_base _ (by rw [hlen]; show 1024 * r + 1024 ≤ 4 * 256 * p.k; omega)
    have dsub : Region.Sub ⟨vScr σ + BitVec.ofNat 64 (oP 16), 8 * 128⟩ (reg (vScr σ) (scrLen p)) :=
      Offset.sub_base _ hoT
    have cr : PPC64LE.Covers [⟨s.gpr .r14 + BitVec.ofNat 64 (1024 * r), 8 * 128⟩] (s.rd ++ s.wr) := by
      rw [g14, vc.rd]
      exact Covers.of_sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_append_left _ hp.2.rd, 1024 * r, rfl,
          by rw [hlen]; show 1024 * r + 1024 ≤ 4 * 256 * p.k; omega⟩
    have cw : PPC64LE.Covers [⟨s.gpr .r31 + BitVec.ofNat 64 (oP 16), 8 * 128⟩] s.wr := by
      rw [g31, vc.wr, hp.1.wr]
      exact Covers.of_sub fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        exact ⟨_, List.mem_singleton_self _, oP 16, rfl, hoT⟩
    have hd : (⟨s.gpr .r14 + BitVec.ofNat 64 (1024 * r), 8 * 128⟩ : Region).Disjoint
        ⟨s.gpr .r31 + BitVec.ofNat 64 (oP 16), 8 * 128⟩ := by
      rw [g14, g31]; exact (hp.2.d_c.sub_left hsub).sub_right dsub
    refine WP.mono (copyW_ok (sb := .r14) (db := .r31) (by decide) (by decide)
      (by omega) (by simp only [oP]; omega) (by decide) (by decide) cr cw hd) fun s' ⟨k, hbt⟩ => ?_
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
    rw [show 4 * Spec.MlDsa.n * r = 1024 * r by show 4 * 256 * r = 1024 * r; omega] at this
    exact Proof.MlDsa.PreparedKey.polyIs_of_copy hbt this
  · refine rel_of (copyW_tr (by decide) (by decide) (by decide) (by omega) (by simp only [oP]; omega)
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
    rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
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
