import VerifiedGarbage.Proof.MlKem.X86.CheckEk
import VerifiedGarbage.Impl.MlKem.X86.Decaps
import VerifiedGarbage.Spec.MlKem.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.EncY`. -/
section

/-!
# ML-KEM on x86 (32-bit): `ŷ` in K-PKE.Encrypt

`SamplePolyCBD₂(PRF₂(r, N))` into a polynomial, keeping what a predicate
states (`cbd_piece`); `ŷ[N]` (`y_piece`), and the start of `encrypt`: `eACC`
set to 1 and the `k` polynomials `ŷ[N]` (`ys_piece`), which reach `P k`.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt shakeSuffix)

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

section
variable [BaseOK L]

/-- `SamplePolyCBD₂(PRF₂(r, N))` into `scratch + o`, keeping `Q`. -/
theorem cbd_piece (hS : SOK L Y) {I : Inp} (N o : Nat) {Q : State → State → Prop}
    (hQ : ∀ s₀ s, Q s₀ s → Base L Y I s₀ s)
    (hk : Keeps Y Q [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, ⟨Y.sc, o, 1024⟩] 72)
    (hc : (Y.ok (bPRF L Y.sc) && Y.okW ⟨Y.sc, o, 1024⟩ && Y.sep (bPRF L Y.sc) ⟨Y.sc, o, 1024⟩) = true) :
    Piece (TPre Y) (TPub Y lk) Q
      (fun s₀ s => Q s₀ s ∧ PolyIs s.mem (Buf.addr s₀ ⟨Y.sc, o, 1024⟩) (cbd (rE I s₀) N)) (encCbd L Y.sc N o) := by
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (B := fun s₀ s => Q s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (bN L Y.sc)) 1 = [BitVec.ofNat 8 N])
    (st8_piece (Y := Y) (L.eKR + 64) N (BaseOK.n hS) (by taint_rfl) (fun _ _ _ h => (hQ _ _ h).ctx)
      fun s₀ s s' hp h h' m' => ⟨hk.widen k88 (bs' := [⟨Y.sc, L.eKR + 64, 1⟩]) (by simp) (Nat.zero_le _)
        s₀ s s' hp h h' (m' ▸ frW8), by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := fun s₀ s => Q s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (bPRF L Y.sc)) 128 = prf 2 (rE I s₀) (BitVec.ofNat 8 N))
    (hash1_piece (Y := Y) L.eST L.eWK 136 0x1f (bRN L Y.sc) (bPRF L Y.sc) rate136 (BaseOK.hash hS) hS.le
      (by show 33 < 2 ^ 32; decide) (by show 128 < 2 ^ 32; decide) (by taint_rfl) (by sc_taint) (by sc_taint) (by sc_taint)
      (fun _ _ _ h => (hQ _ _ h.1).ctx) fun s₀ s s' hp h h' fr out =>
        ⟨hk.widen k88 (by simp) (by decide) s₀ s s' hp h.1 h' fr, ?_⟩) ?_
  · rw [out, rn_split hS hp, (hQ _ _ h.1).kr, h.2,
      show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32, prf_eq]
  exact cbd2C_piece (Y := Y) Y.sc L.ePRF Y.sc o hc hS.le (by sc_taint) (fun _ _ _ h => (hQ _ _ h.1).ctx)
    fun s₀ s s' hp h h' fr post => ⟨hk.widen k88 (by simp) (by decide) s₀ s s' hp h.1 h' fr,
      by rw [h.2] at post; exact post⟩

end

/-- `eACC`. -/
abbrev accE (L : KemLay) (Y : Lay) (s₀ s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (bACC L Y.sc)) 32

/-- While `ŷ` is computed: `ŷ[j]` for `j < N`. -/
structure P (L : KemLay) (Y : Lay) (I : Inp) (N : Nat) (s₀ s : State) : Prop extends Base L Y I s₀ s where
  acc : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1
  y : ∀ j < N, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)

theorem P.keep {I : Inp} {N : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (h₁ : inApart L Y bs = true) (h₂ : Y.apart (bACC L Y.sc) bs = true)
    (h₃ : ∀ j < N, Y.apart (bY Y.sc j) bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.Enc.P L Y I N s₀ s)
    (c : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s') : VG.Proof.MlKem.X86.Enc.P L Y I N s₀ s' :=
  ⟨h.toBase.keep hp hM h₁ fr c, (keepW hp hM h₂ fr).trans h.acc,
    fun j hj => keepPoly hp hM (h₃ j hj) fr (h.y j hj)⟩

/-- The facts of the layout that `ys_piece` uses. -/
class YOK (L : KemLay) : Prop where
  y : ∀ {Y : Lay}, SOK L Y → ∀ N < L.p.k,
    inApart L Y [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bY Y.sc N] = true ∧
    Y.apart (bACC L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bY Y.sc N] = true ∧
    (∀ j < N, Y.apart (bY Y.sc j) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bY Y.sc N] = true) ∧
    (Y.ok (bPRF L Y.sc) && Y.okW (bY Y.sc N) && Y.sep (bPRF L Y.sc) (bY Y.sc N)) = true ∧
    (Y.okW (bY Y.sc N) && Y.okW (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) && Y.sep (bY Y.sc N) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc)) = true ∧
    inApart L Y [bY Y.sc N, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bY Y.sc N, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    (∀ j < N, Y.apart (bY Y.sc j) [bY Y.sc N, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true)
  acc : ∀ {Y : Lay}, SOK L Y → Y.okW (bACC L Y.sc) = true ∧ inApart L Y [bACC L Y.sc] = true

variable [BaseOK L] [VG.Proof.MlKem.X86.Enc.YOK L]

/-- `ŷ[N] = NTT(SamplePolyCBD₂(PRF₂(r, N)))`. -/
theorem y_piece (hS : SOK L Y) {I : Inp} (N : Nat) (hN : N < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.P L Y I N) (VG.Proof.MlKem.X86.Enc.P L Y I (N + 1)) (encYC L Y.sc N) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := YOK.y hS N hN
  refine Piece.seq (VG.Proof.MlKem.X86.Enc.cbd_piece hS N (1024 * N) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => h.keep hp hS.le a₁ a₂ a₃ fr c) a₄) ?_
  refine inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack Y.sc (1024 * N) Y.sc L.eNS a₅ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.1.ctx, h.2.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.1.keep hp hS.le a₆ a₇ a₈ fr h'
  refine ⟨k.toBase, k.acc, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact k.y j hj
  · rw [h.2.2] at post; exact post

/-- `eACC ← 1`, the `k` polynomials `ŷ[N]`, then `c`. -/
theorem ys_piece (hS : SOK L Y) {I : Inp} {Q : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.P L Y I L.p.k) Q c) :
    Piece (TPre Y) (TPub Y lk) (Base L Y I) Q
      (.seq (.block [.mov .eax (.imm 1), .store (at_ .esi L.eACC) .eax]) <|
        seqs ((List.range L.p.k).map (encYC L Y.sc)) c) := by
  obtain ⟨o₁, o₂⟩ := YOK.acc hS
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.P L Y I 0) (st32_piece (Y := Y) L.eACC 1 o₁ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hp (M := 0) hS.le o₂ (m' ▸ frW32) h',
        by show s'.mem.readW _ 32 = _; rw [m']; exact Mem.readW_writeW_self32 _ _ _,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩) ?_
  exact Piece.seqs0 L.p.k (fun N hN => VG.Proof.MlKem.X86.Enc.y_piece hS N hN) h

end VG.Proof.MlKem.X86.Enc

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.EncRow`. -/
section

/-!
# ML-KEM on x86 (32-bit): `u` in K-PKE.Encrypt

Row `i` (`encRow L sc i`): each entry `Â[j, i]` is sampled from `ρ ‖ i ‖ j`,
masked by the value `vg_mlkem_sample_ntt` returned, which is ANDed into `eACC`
(`sample_piece`), and multiplied by `ŷ[j]` into `u[i]` (`entry0_piece`,
`entry_piece`); then `NTT⁻¹`, `e₁[i]` added, and `u[i]` compressed into the
ciphertext (`row_piece`).

`B k e` is what holds after `k` entries and `e` rows: `eACC` is 0 or 1; if 1,
the first `k` samples succeeded, and the first `e` rows of the ciphertext
are those of K-PKE.Encrypt for the matrix `aE` they sampled; if 0, one of the
`k²` samples failed within `minIterations` iterations. The seeds are
public: `ρ` is (`RhoPub`).
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

section
variable (L : KemLay) (I : Inp) (s₀ : State)
/-- The seed of the `k`th entry sampled, `Â[k % k, k / k]`. -/
abbrev mSE (k : Nat) : List Byte := matSeed (ρE L I s₀) (k % L.p.k) (k / L.p.k)

/-- `Â[0, i] ×_T ŷ[0] + … + Â[j - 1, i] ×_T ŷ[j - 1]`. -/
noncomputable abbrev partU (i j : Nat) : VG.Spec.MlKem.Poly := KPke.dotK (fun j => aE L I s₀ j i) (yE I s₀) j
end

/-- Two runs with the same public data have the same `ρ`. -/
def RhoPub (L : KemLay) (Y : Lay) (lk : State → List Byte) (I : Inp) : Prop :=
  ∀ s₀ s₀', TPre Y s₀ → TPre Y s₀' → TPub Y lk s₀ s₀' → ρE L I s₀ = ρE L I s₀'

/-- `u[i]` in the ciphertext. -/
abbrev bCU (L : KemLay) (sc i : Nat) : Buf := ⟨sc, L.eC + 32 * L.p.du * i, 32 * L.p.du⟩

/-- See the module documentation. -/
structure B (L : KemLay) (Y : Lay) (I : Inp) (k e : Nat) (s₀ s : State) : Prop extends Base L Y I s₀ s where
  y : ∀ j < L.p.k, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)
  acc : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 0 ∨ VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1
  ok : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → ∀ k' < k, ∃ a, Samp (VG.Proof.MlKem.X86.Enc.mSE L I s₀ k') a
  fail : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 0 → ∃ k' < L.p.k * L.p.k, sampleNTT minIterations (VG.Proof.MlKem.X86.Enc.mSE L I s₀ k') = none
  c : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → ∀ i < e,
    bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bCU L Y.sc i)) (32 * L.p.du) =
      compressEncode L.p.du (KPke.encU L.p (aE L I s₀) (rE I s₀) i)

/-- Whether `bs` is apart from the inputs and `ŷ`. -/
def safeS (L : KemLay) (Y : Lay) (bs : List Buf) : Bool :=
  inApart L Y bs && (List.range L.p.k).all fun j => Y.apart (bY Y.sc j) bs

/-- Whether `bs` is also apart from `eACC` and the rows of the ciphertext. -/
def safe (L : KemLay) (Y : Lay) (bs : List Buf) : Bool :=
  Y.apart (bACC L Y.sc) bs && VG.Proof.MlKem.X86.Enc.safeS L Y bs && (List.range L.p.k).all fun i => Y.apart (VG.Proof.MlKem.X86.Enc.bCU L Y.sc i) bs

/-- `sc_decide`, for facts that `safe` and `safeS` state. -/
macro "sc_decide'" : tactic => `(tactic| (simp only [safe, safeS]; sc_decide))

theorem keepS {I : Inp} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : VG.Proof.MlKem.X86.Enc.safeS L Y bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (c : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s') (h₁ : Base L Y I s₀ s)
    (h₂ : ∀ j < L.p.k, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)) :
    Base L Y I s₀ s' ∧ ∀ j < L.p.k, PolyIs s'.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j) := by
  simp only [VG.Proof.MlKem.X86.Enc.safeS, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  exact ⟨h₁.keep hp hM hs.1 fr c, fun j hj => keepPoly hp hM (hs.2 j hj) fr (h₂ j hj)⟩

theorem B.keep {I : Inp} {k e : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : VG.Proof.MlKem.X86.Enc.safe L Y bs = true) (he : e ≤ L.p.k) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : VG.Proof.MlKem.X86.Enc.B L Y I k e s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s') : VG.Proof.MlKem.X86.Enc.B L Y I k e s₀ s' := by
  simp only [VG.Proof.MlKem.X86.Enc.safe, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hs
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hs
  have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp hM h₁ fr
  obtain ⟨k₁, k₂⟩ := VG.Proof.MlKem.X86.Enc.keepS hp hM h₂ fr c h.toBase h.y
  refine ⟨k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i hi => ?_⟩
  rw [keepBytes hp hM (h₃ i (by omega)) fr]
  exact h.c (ea ▸ e₁) i hi

/-- Before entry `(i, j)`: and `u[i]` so far, if `0 < j`. -/
structure R (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop
    extends VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * i + j) i s₀ s where
  u : 0 < j → Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = VG.Proof.MlKem.X86.Enc.partU L I s₀ i j)

theorem R.keep {I : Inp} {i j : Nat} (hi : i < L.p.k) {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf}
    {M : Nat} (hM : M + 16 ≤ Y.stk) (hs : VG.Proof.MlKem.X86.Enc.safe L Y bs = true) (hU : Y.apart (bU L Y.sc) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.Enc.R L Y I i j s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s') : VG.Proof.MlKem.X86.Enc.R L Y I i j s₀ s' := by
  have k := h.toB.keep hp hM hs (by omega) fr c
  have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s :=
    keepW hp hM (by simp only [VG.Proof.MlKem.X86.Enc.safe, Bool.and_eq_true] at hs; exact hs.1.1) fr
  refine ⟨k, fun hj => ⟨keepRed hp hM hU fr (h.u hj).1, fun e₁ => ?_⟩⟩
  rw [polyAt_congr (Top.keep hp hM hU fr)]
  exact (h.u hj).2 (ea ▸ e₁)

/-- The facts of the layout that an entry uses. -/
class EntOK (L : KemLay) : Prop where
  seed : ∀ {Y : Lay}, SOK L Y → Y.ok ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩ = true ∧ Y.ok (bEK L Y.sc) = true ∧
    Y.ok ⟨Y.sc, L.eEK + L.p.ekLen, 2⟩ = true ∧ Y.ok ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩ = true ∧
    Y.ok ⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩ = true ∧ Y.okW ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩ = true ∧
    Y.okW ⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩ = true
  ent : ∀ {Y : Lay}, SOK L Y →
    VG.Proof.MlKem.X86.Enc.safe L Y [⟨Y.sc, L.eEK + L.p.ekLen, 1⟩] = true ∧ VG.Proof.MlKem.X86.Enc.safe L Y [⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩] = true ∧
    Y.apart (bU L Y.sc) [⟨Y.sc, L.eEK + L.p.ekLen, 1⟩] = true ∧
    Y.apart (bU L Y.sc) [⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩] = true ∧
    Y.apart ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩ [⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩] = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [VG.Proof.MlKem.X86.Enc.bA L Y.sc, bSS L Y.sc] = true ∧ Y.apart (bU L Y.sc) [VG.Proof.MlKem.X86.Enc.bA L Y.sc, bSS L Y.sc] = true ∧
    VG.Proof.MlKem.X86.Enc.safeS L Y [bACC L Y.sc, VG.Proof.MlKem.X86.Enc.bA L Y.sc] = true ∧
    (∀ i < L.p.k, Y.apart (VG.Proof.MlKem.X86.Enc.bCU L Y.sc i) [bACC L Y.sc, VG.Proof.MlKem.X86.Enc.bA L Y.sc] = true) ∧
    Y.apart (bU L Y.sc) [bACC L Y.sc, VG.Proof.MlKem.X86.Enc.bA L Y.sc] = true ∧
    (Y.ok (bSeed L Y.sc) && Y.okW (VG.Proof.MlKem.X86.Enc.bA L Y.sc) && Y.okW (bSS L Y.sc) && Y.sep (bSeed L Y.sc) (VG.Proof.MlKem.X86.Enc.bA L Y.sc) &&
      Y.sep (bSeed L Y.sc) (bSS L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bA L Y.sc) (bSS L Y.sc)) = true ∧
    (Y.okW (bACC L Y.sc) && Y.okW (VG.Proof.MlKem.X86.Enc.bA L Y.sc) && Y.sep (bACC L Y.sc) (VG.Proof.MlKem.X86.Enc.bA L Y.sc)) = true
  mul : ∀ {Y : Lay}, SOK L Y →
    VG.Proof.MlKem.X86.Enc.safe L Y [bU L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧ VG.Proof.MlKem.X86.Enc.safe L Y [VG.Proof.MlKem.X86.Enc.bP L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [bU L Y.sc] = true ∧ Y.apart (bU L Y.sc) [VG.Proof.MlKem.X86.Enc.bP L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    Y.apart (VG.Proof.MlKem.X86.Enc.bA L Y.sc) [VG.Proof.MlKem.X86.Enc.bP L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    Y.apart (bACC L Y.sc) [VG.Proof.MlKem.X86.Enc.bP L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc] = true ∧
    (Y.okW (bU L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bA L Y.sc) && Y.ok (bY Y.sc 0) && Y.okW (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bA L Y.sc) && Y.sep (bU L Y.sc) (bY Y.sc 0) && Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (VG.Proof.MlKem.X86.Enc.bA L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) && Y.sep (bY Y.sc 0) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc)) = true ∧
    (∀ j < L.p.k, (Y.okW (VG.Proof.MlKem.X86.Enc.bP L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bA L Y.sc) && Y.ok (bY Y.sc j) && Y.okW (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (VG.Proof.MlKem.X86.Enc.bP L Y.sc) (VG.Proof.MlKem.X86.Enc.bA L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bP L Y.sc) (bY Y.sc j) && Y.sep (VG.Proof.MlKem.X86.Enc.bP L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (VG.Proof.MlKem.X86.Enc.bA L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) && Y.sep (bY Y.sc j) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc)) = true) ∧
    (Y.okW (bU L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bP L Y.sc) && Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bP L Y.sc)) = true

theorem mSE_eq (I : Inp) (s₀ : State) {i j : Nat} (hj : j < L.p.k) :
    VG.Proof.MlKem.X86.Enc.mSE L I s₀ (L.p.k * i + j) = matSeed (ρE L I s₀) j i := by
  simp only [VG.Proof.MlKem.X86.Enc.mSE]
  rw [idx_mod hj, idx_div hj]

variable [VG.Proof.MlKem.X86.Enc.EntOK L]

/-! ## The seed -/

/-- `ρ`, in `ek`. -/
theorem rho_eq (hS : SOK L Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Base L Y I s₀ s) :
    bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩) 32 = ρE L I s₀ := by
  obtain ⟨o₁, o₂, -⟩ := EntOK.seed hS
  rw [show ρE L I s₀ = ((I.ek s₀).drop (384 * L.p.k)).take 32 from rfl, ← h.ek,
    bytesAt_slice _ _ (show 384 * L.p.k + 32 ≤ L.p.ekLen from Nat.le_refl _)]
  rw [Buf.addr_eq hp (b := ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩) o₁, Buf.addr_eq hp (b := bEK L Y.sc) o₂,
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem seed_split (hS : SOK L Y) {s₀ : State} (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bSeed L Y.sc)) 34 = bytesAt m (Buf.addr s₀ ⟨Y.sc, L.eEK + 384 * L.p.k, 32⟩) 32 ++
      (bytesAt m (Buf.addr s₀ ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩) 1 ++
        bytesAt m (Buf.addr s₀ ⟨Y.sc, L.eEK + L.p.ekLen + 1, 1⟩) 1) := by
  obtain ⟨o₁, -, o₃, o₄, o₅, -⟩ := EntOK.seed hS
  rw [bytes_split hp m (o' := L.eEK + L.p.ekLen) (l₁ := 32) (l₂ := 2) (by rw [Nat.add_assoc]; rfl) rfl o₁ o₃,
    bytes_split hp m (a := Y.sc) (o := L.eEK + L.p.ekLen) (o' := L.eEK + L.p.ekLen + 1) (l₁ := 1) (l₂ := 1) rfl
      rfl o₄ o₅]

/-! ## An entry -/

/-- After `i` is stored. -/
structure S1 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Enc.R L Y I i j s₀ s where
  bi : bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eEK + L.p.ekLen, 1⟩) 1 = [BitVec.ofNat 8 i]

/-- After `ρ ‖ i ‖ j` is stored. -/
structure S2 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Enc.R L Y I i j s₀ s where
  seed : bytesAt s.mem (Buf.addr s₀ (bSeed L Y.sc)) 34 = matSeed (ρE L I s₀) j i

/-- After `Â[j, i]` is sampled, `r` returned. -/
structure S3 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Enc.R L Y I i j s₀ s where
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bA L Y.sc))
  out : Outcome (fun iters => sampleNTT iters (matSeed (ρE L I s₀) j i)) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bA L Y.sc)))

/-- After it is masked, and `eACC` updated. -/
structure S4 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop
    extends VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * i + j + 1) i s₀ s where
  u : 0 < j → Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = VG.Proof.MlKem.X86.Enc.partU L I s₀ i j)
  red : Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bA L Y.sc))
  a : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bA L Y.sc)) = aE L I s₀ j i

/-- `ρ ‖ i ‖ j`, `Â[j, i]` sampled and masked, then `c`. -/
theorem sample_piece (hS : SOK L Y) {I : Inp} (hρ : VG.Proof.MlKem.X86.Enc.RhoPub L Y lk I) (i j : Nat) (hi : i < L.p.k)
    (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.S4 L Y I i j) Q c) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.R L Y I i j) Q
      (.seq (.block (st8 (L.eEK + L.p.ekLen) i)) <| .seq (.block (st8 (L.eEK + L.p.ekLen + 1) j)) <|
        .seq (sampleC Y.sc (bSeed L Y.sc) (VG.Proof.MlKem.X86.Enc.bA L Y.sc) (bSS L Y.sc)) (.seq (maskA L.eACC L.eA) c)) := by
  obtain ⟨n₁, n₂, n₃, n₄, n₅, p₁, p₂, q₁, q₂, q₃, hs, hm⟩ := EntOK.ent hS
  obtain ⟨-, -, -, -, -, w₁, w₂⟩ := EntOK.seed hS
  have k88 : 0 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.S1 L Y I i j) (st8_piece (Y := Y) (L.eEK + L.p.ekLen) i w₁ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hi hp k88 n₁ n₃ (m' ▸ frW8) h', by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.S2 L Y I i j) (st8_piece (Y := Y) (L.eEK + L.p.ekLen + 1) j w₂ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ?_) ?_
  · have k := h.keep hi hp k88 n₂ n₄ (m' ▸ frW8) h'
    refine ⟨k, ?_⟩
    rw [VG.Proof.MlKem.X86.Enc.seed_split hS hp, VG.Proof.MlKem.X86.Enc.rho_eq hS hp k.toBase, keepBytes hp k88 n₅ (m' ▸ frW8), h.bi, m', st8_byte]
    rfl
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.S3 L Y I i j) (sampleC_piece (Y := Y) Y.sc (L.eEK + 384 * L.p.k) Y.sc L.eA Y.sc L.eSS
    hs hS.le (by sc_taint) (fun _ _ _ h => h.ctx) (fun s₀ s₀' s s' hp hp' hq h h' => ?_)
    fun s₀ s s' hp h h' fr red out => ⟨h.keep hi hp hS.le p₁ p₂ fr h', red, ?_⟩) ?_
  · rw [h.seed, h'.seed, hρ s₀ s₀' hp hp' hq]
  · rw [h.seed] at out; exact out
  refine Piece.seq (maskA_piece (Y := Y) L.eACC L.eA hm (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_) hc
  have fr' := fr2 fr
  have hr := outcome_01 h.out
  have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s &&& s.gpr .eax := ha
  obtain ⟨s₁, s₂, s₃⟩ := acc_step h.acc hr
  rw [← ea] at s₁ s₂ s₃
  obtain ⟨k₁, k₂⟩ := VG.Proof.MlKem.X86.Enc.keepS hp k88 q₁ fr' h' h.toBase h.y
  obtain ⟨mr, ma⟩ := mask_poly hr hc h.red
  refine ⟨⟨k₁, k₂, s₁, fun e₁ k' hk' => ?_, fun e₁ => ?_, fun e₁ i' hi' => ?_⟩,
    fun hj => ⟨keepRed hp k88 q₃ fr' (h.u hj).1, fun e₁ => ?_⟩, mr, fun e₁ => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · exact h.ok (s₂ e₁).1 k' hk'
    · rw [VG.Proof.MlKem.X86.Enc.mSE_eq I s₀ hj]
      rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
      · exact ⟨_, it, e⟩
      · exact absurd ((s₂ e₁).2) (by rw [e]; decide)
  · rcases s₃ e₁ with e₂ | e₂
    · exact h.fail e₂
    · refine ⟨L.p.k * i + j, idx_lt hi hj, ?_⟩
      rw [VG.Proof.MlKem.X86.Enc.mSE_eq I s₀ hj]
      rcases h.out with ⟨e, _⟩ | ⟨_, e⟩
      · exact absurd e (by rw [e₂]; decide)
      · exact e
  · rw [keepBytes hp k88 (q₂ i' (by omega)) fr']
    exact h.c (s₂ e₁).1 i' hi'
  · rw [polyAt_congr (Top.keep hp k88 q₃ fr')]
    exact (h.u hj).2 (s₂ e₁).1
  · refine (ma (s₂ e₁).2).trans ?_
    rcases h.out with ⟨_, it, e⟩ | ⟨e, _⟩
    · exact (sv_eq ⟨it, e⟩).symm
    · exact absurd ((s₂ e₁).2) (by rw [e]; decide)

/-- After `Â[j, i] ×_T ŷ[j]` is computed, for `0 < j`. -/
structure S5 (L : KemLay) (Y : Lay) (I : Inp) (i j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Enc.S4 L Y I i j s₀ s where
  p : Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bP L Y.sc)) ∧
    (VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bP L Y.sc)) = multiplyNTTs (aE L I s₀ j i) (yE I s₀ j))

/-- Entry `(i, 0)`: `u[i] ← Â[0, i] ×_T ŷ[0]`. -/
theorem entry0_piece (hS : SOK L Y) {I : Inp} (hρ : VG.Proof.MlKem.X86.Enc.RhoPub L Y lk I) (i : Nat) (hi : i < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.R L Y I i 0) (VG.Proof.MlKem.X86.Enc.R L Y I i 1) (encEntry L Y.sc i 0) := by
  obtain ⟨m₁, -, -, -, -, a₁, -, -, o₁, -, -⟩ := EntOK.mul hS
  have hk : 0 < L.p.k := by omega
  refine VG.Proof.MlKem.X86.Enc.sample_piece hS hρ i 0 hi hk (mulC_piece (Y := Y) Y.sc L.eU Y.sc L.eA Y.sc 0 Y.sc L.eNS
    o₁ hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.y 0 hk).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  have k := h.toB.keep hp hS.le m₁ (by omega) fr h'
  have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp hS.le a₁ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, h.a (ea ▸ e₁), (h.y 0 hk).2]
  rfl

/-- Entry `(i, j + 1)`: `u[i] ← u[i] + Â[j + 1, i] ×_T ŷ[j + 1]`. -/
theorem entry_piece (hS : SOK L Y) {I : Inp} (hρ : VG.Proof.MlKem.X86.Enc.RhoPub L Y lk I) (i j : Nat) (hi : i < L.p.k)
    (hj : j + 1 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.R L Y I i (j + 1)) (VG.Proof.MlKem.X86.Enc.R L Y I i (j + 2)) (encEntry L Y.sc i (j + 1)) := by
  obtain ⟨-, m₂, m₃, m₄, m₅, -, a₂, a₃, -, o₂, o₃⟩ := EntOK.mul hS
  refine VG.Proof.MlKem.X86.Enc.sample_piece hS hρ i (j + 1) hi hj (.seq (B := VG.Proof.MlKem.X86.Enc.S5 L Y I i (j + 1))
    (mulC_piece (Y := Y) Y.sc L.eP Y.sc L.eA Y.sc (1024 * (j + 1)) Y.sc L.eNS (o₂ (j + 1) hj) hS.le
      (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.red, (h.y (j + 1) (by omega)).1⟩)
      fun s₀ s s' hp h h' fr post => ?_) ?_)
  · have k := h.toB.keep hp hS.le m₂ (by omega) fr h'
    have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp hS.le a₂ fr
    refine ⟨⟨k, fun hj' => ⟨keepRed hp hS.le m₄ fr (h.u hj').1, fun e₁ => ?_⟩,
      keepRed hp hS.le m₅ fr h.red, fun e₁ => ?_⟩, post.1, fun e₁ => ?_⟩
    · rw [polyAt_congr (Top.keep hp hS.le m₄ fr)]; exact (h.u hj').2 (ea ▸ e₁)
    · rw [polyAt_congr (Top.keep hp hS.le m₅ fr)]; exact h.a (ea ▸ e₁)
    · rw [post.2, h.a (ea ▸ e₁), (h.y (j + 1) (by omega)).2]
  refine accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eP o₃ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.u (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.toB.keep hp hS.le m₃ (by omega) fr h'
  have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp hS.le a₃ fr
  refine ⟨k, fun _ => ⟨post.1, fun e₁ => ?_⟩⟩
  rw [post.2, (h.u (Nat.succ_pos _)).2 (ea ▸ e₁), h.p.2 (ea ▸ e₁)]
  rfl

/-- The `k` entries of row `i`, then `c`. -/
theorem entries_piece (hS : SOK L Y) {I : Inp} (hρ : VG.Proof.MlKem.X86.Enc.RhoPub L Y lk I) (i : Nat) (hi : i < L.p.k)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.R L Y I i L.p.k) Q c) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.R L Y I i 0) Q (seqs ((List.range L.p.k).map (encEntry L Y.sc i)) c) :=
  Piece.seqs0 (P := VG.Proof.MlKem.X86.Enc.R L Y I i) L.p.k (fun j hj => match j, hj with
    | 0, _ => VG.Proof.MlKem.X86.Enc.entry0_piece hS hρ i hi
    | j + 1, hj => VG.Proof.MlKem.X86.Enc.entry_piece hS hρ i j hi hj) hc

end VG.Proof.MlKem.X86.Enc

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.EncV`. -/
section

/-!
# ML-KEM on x86 (32-bit): the ciphertext of K-PKE.Encrypt

The end of row `i` (`row_piece`): `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`,
compressed into the ciphertext. Then `v` (`v_piece`): the products `t̂[j] ×_T
ŷ[j]`, with `t̂[j]` decoded from `ek` (`term0_piece`, `term_piece`), summed,
`NTT⁻¹`, `e₂` and `μ` added, and `v` compressed into the ciphertext. `encrypt`
takes the inputs (`Base`) to `Done` (`encrypt_piece`): if `eACC` is 1, the
ciphertext is K-PKE.Encrypt's for the matrix `aE` sampled (`ct_eq`), each of
whose entries was sampled within some bound (`samples`); if 0, one sample
failed within `minIterations`.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

/-! ## The end of a row -/

/-- `NTT⁻¹` of `u[i]` is computed. -/
structure S7 (L : KemLay) (Y : Lay) (I : Inp) (i : Nat) (s₀ s : State) : Prop
    extends VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * i + L.p.k) i s₀ s where
  u : Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = nttInv (VG.Proof.MlKem.X86.Enc.partU L I s₀ i L.p.k))

/-- `u[i]` is computed. -/
structure S8 (L : KemLay) (Y : Lay) (I : Inp) (i : Nat) (s₀ s : State) : Prop
    extends VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * i + L.p.k) i s₀ s where
  u : Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧
    (VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1 → polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = KPke.encU L.p (aE L I s₀) (rE I s₀) i)

/-- The facts of the layout that the end of a row uses. -/
class RowOK (L : KemLay) : Prop where
  row : ∀ {Y : Lay}, SOK L Y →
    VG.Proof.MlKem.X86.Enc.safe L Y [bU L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, VG.Proof.MlKem.X86.Enc.bE L Y.sc] = true ∧
    Y.apart (bU L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, VG.Proof.MlKem.X86.Enc.bE L Y.sc] = true ∧
    Y.apart (bACC L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, VG.Proof.MlKem.X86.Enc.bE L Y.sc] = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [bU L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bU L Y.sc] = true ∧
    (Y.okW (bU L Y.sc) && Y.okW (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) && Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc)) = true ∧
    (Y.ok (bPRF L Y.sc) && Y.okW (VG.Proof.MlKem.X86.Enc.bE L Y.sc) && Y.sep (bPRF L Y.sc) (VG.Proof.MlKem.X86.Enc.bE L Y.sc)) = true ∧
    (Y.okW (bU L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bE L Y.sc) && Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bE L Y.sc)) = true ∧
    (∀ i < L.p.k, (Y.ok (bU L Y.sc) && Y.okW (VG.Proof.MlKem.X86.Enc.bCU L Y.sc i) && Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bCU L Y.sc i)) = true ∧
      VG.Proof.MlKem.X86.Enc.safeS L Y [VG.Proof.MlKem.X86.Enc.bCU L Y.sc i] = true ∧ Y.apart (bACC L Y.sc) [VG.Proof.MlKem.X86.Enc.bCU L Y.sc i] = true ∧
      ∀ i' < i, Y.apart (VG.Proof.MlKem.X86.Enc.bCU L Y.sc i') [VG.Proof.MlKem.X86.Enc.bCU L Y.sc i] = true)

/-- Row `i`: `u[i] = NTT⁻¹(Â^⊺[i] ∘ ŷ) + e₁[i]`, compressed into the ciphertext. -/
theorem row_piece [CeOK L] [BaseOK L] [VG.Proof.MlKem.X86.Enc.EntOK L] [VG.Proof.MlKem.X86.Enc.RowOK L] (hS : SOK L Y) {I : Inp} (hρ : VG.Proof.MlKem.X86.Enc.RhoPub L Y lk I) (i : Nat) (hi : i < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * i) i) (VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * (i + 1)) (i + 1)) (encRow L Y.sc i) := by
  obtain ⟨r₁, r₂, r₃, r₄, r₅, r₆, r₇, o₁, o₂, o₃, o₄⟩ := RowOK.row hS
  obtain ⟨c₁, c₂, c₃, c₄⟩ := o₄ i hi
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine VG.Proof.MlKem.X86.Enc.entries_piece hS hρ i hi ?_ |>.mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.S7 L Y I i) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack Y.sc L.eU Y.sc
    L.eNS o₁ hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, (h.u (by omega)).1⟩)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.toB.keep hp hS.le r₁ (by omega) fr h'
    have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp hS.le r₂ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, (h.u (by omega)).2 (ea ▸ e₁)]
  refine Piece.seq (VG.Proof.MlKem.X86.Enc.cbd_piece hS (L.p.k + i) L.eE (Q := VG.Proof.MlKem.X86.Enc.S7 L Y I i) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => ?_) o₂) ?_
  · have k := h.toB.keep hp k88 r₃ (by omega) fr c
    have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp k88 r₅ fr
    refine ⟨k, keepRed hp k88 r₄ fr h.u.1, fun e₁ => ?_⟩
    rw [polyAt_congr (Top.keep hp k88 r₄ fr)]; exact h.u.2 (ea ▸ e₁)
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.S8 L Y I i) (accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eE o₃ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.u.1, h.2.1⟩) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.1.toB.keep hp hS.le r₆ (by omega) fr h'
    have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp hS.le r₇ fr
    refine ⟨k, post.1, fun e₁ => ?_⟩
    rw [post.2, h.1.u.2 (ea ▸ e₁), h.2.2]
    rfl
  refine ceK_piece (Y := Y) L.p.du (.inl rfl) Y.sc L.eU Y.sc (L.eC + 32 * L.p.du * i) c₁ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, h.u.1⟩) fun s₀ s s' hp h h' fr post => ?_
  obtain ⟨k₁, k₂⟩ := VG.Proof.MlKem.X86.Enc.keepS hp hS.le c₂ fr h' h.toBase h.y
  have ea : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s' = VG.Proof.MlKem.X86.Enc.accE L Y s₀ s := keepW hp hS.le c₃ fr
  refine ⟨k₁, k₂, ea ▸ h.acc, fun e₁ => h.ok (ea ▸ e₁), fun e₁ => h.fail (ea ▸ e₁), fun e₁ i' hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi' with hi' | rfl
  · rw [keepBytes hp hS.le (c₄ i' hi') fr]; exact h.c (ea ▸ e₁) i' hi'
  · rw [post, h.u.2 (ea ▸ e₁)]

/-! ## `v` -/

section
variable (L : KemLay) (I : Inp) (s₀ : State)
/-- `t̂[0] ×_T ŷ[0] + … + t̂[j - 1] ×_T ŷ[j - 1]`. -/
abbrev partV (j : Nat) : VG.Spec.MlKem.Poly := KPke.dotK (ekT (I.ek s₀)) (yE I s₀) j
end

/-- Before term `j` of `v`: and `v` so far, if `0 < j`. -/
structure V (L : KemLay) (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop
    extends VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * L.p.k) L.p.k s₀ s where
  v : 0 < j → Reduced s.mem (Buf.addr s₀ (bU L Y.sc)) ∧ polyAt s.mem (Buf.addr s₀ (bU L Y.sc)) = VG.Proof.MlKem.X86.Enc.partV I s₀ j

/-- After `t̂[j]` is decoded. -/
structure V1 (L : KemLay) (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Enc.V L Y I j s₀ s where
  t : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bT L Y.sc)) (ekT (I.ek s₀) j)

/-- After `t̂[j] ×_T ŷ[j]` is computed, for `0 < j`. -/
structure V2 (L : KemLay) (Y : Lay) (I : Inp) (j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Enc.V L Y I j s₀ s where
  p : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bP L Y.sc)) (multiplyNTTs (ekT (I.ek s₀) j) (yE I s₀ j))

theorem V.keep {I : Inp} {j : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (hs : VG.Proof.MlKem.X86.Enc.safe L Y bs = true) (hU : Y.apart (bU L Y.sc) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : VG.Proof.MlKem.X86.Enc.V L Y I j s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx Y s₀ s') : VG.Proof.MlKem.X86.Enc.V L Y I j s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, fun hj =>
    ⟨keepRed hp hM hU fr (h.v hj).1, by rw [polyAt_congr (Top.keep hp hM hU fr)]; exact (h.v hj).2⟩⟩

/-- The facts of the layout that `v` uses. -/
class VOK (L : KemLay) : Prop where
  v : ∀ {Y : Lay}, SOK L Y →
    VG.Proof.MlKem.X86.Enc.safe L Y [VG.Proof.MlKem.X86.Enc.bT L Y.sc] = true ∧ Y.apart (bU L Y.sc) [VG.Proof.MlKem.X86.Enc.bT L Y.sc] = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [bU L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧ VG.Proof.MlKem.X86.Enc.safe L Y [VG.Proof.MlKem.X86.Enc.bP L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [bU L Y.sc] = true ∧ Y.apart (bU L Y.sc) [VG.Proof.MlKem.X86.Enc.bP L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    Y.apart (VG.Proof.MlKem.X86.Enc.bT L Y.sc) [VG.Proof.MlKem.X86.Enc.bP L Y.sc, VG.Proof.MlKem.X86.Enc.bNS L Y.sc] = true ∧
    (∀ j < L.p.k, (Y.ok ⟨Y.sc, L.eEK + 384 * j, 384⟩ && Y.okW (VG.Proof.MlKem.X86.Enc.bT L Y.sc) &&
      Y.sep ⟨Y.sc, L.eEK + 384 * j, 384⟩ (VG.Proof.MlKem.X86.Enc.bT L Y.sc)) = true) ∧
    (Y.okW (bU L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bT L Y.sc) && Y.ok (bY Y.sc 0) && Y.okW (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bT L Y.sc) && Y.sep (bU L Y.sc) (bY Y.sc 0) && Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (VG.Proof.MlKem.X86.Enc.bT L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) && Y.sep (bY Y.sc 0) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc)) = true ∧
    (∀ j < L.p.k, (Y.okW (VG.Proof.MlKem.X86.Enc.bP L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bT L Y.sc) && Y.ok (bY Y.sc j) && Y.okW (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (VG.Proof.MlKem.X86.Enc.bP L Y.sc) (VG.Proof.MlKem.X86.Enc.bT L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bP L Y.sc) (bY Y.sc j) && Y.sep (VG.Proof.MlKem.X86.Enc.bP L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) &&
      Y.sep (VG.Proof.MlKem.X86.Enc.bT L Y.sc) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc) && Y.sep (bY Y.sc j) (VG.Proof.MlKem.X86.Enc.bNS L Y.sc)) = true) ∧
    (Y.okW (bU L Y.sc) && Y.ok (VG.Proof.MlKem.X86.Enc.bP L Y.sc) && Y.sep (bU L Y.sc) (VG.Proof.MlKem.X86.Enc.bP L Y.sc)) = true
  w : ∀ {Y : Lay}, SOK L Y →
    VG.Proof.MlKem.X86.Enc.safe L Y [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, VG.Proof.MlKem.X86.Enc.bE L Y.sc] = true ∧
    Y.apart (bU L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, VG.Proof.MlKem.X86.Enc.bE L Y.sc] = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [bMU L Y.sc] = true ∧ Y.apart (bU L Y.sc) [bMU L Y.sc] = true ∧
    (Y.ok (VG.Proof.MlKem.X86.Enc.bM L Y.sc) && Y.okW (bMU L Y.sc) && Y.sep (VG.Proof.MlKem.X86.Enc.bM L Y.sc) (bMU L Y.sc)) = true ∧
    (Y.okW (bU L Y.sc) && Y.ok (bMU L Y.sc) && Y.sep (bU L Y.sc) (bMU L Y.sc)) = true ∧
    (Y.ok (bU L Y.sc) && Y.okW ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ &&
      Y.sep (bU L Y.sc) ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩) = true ∧
    VG.Proof.MlKem.X86.Enc.safe L Y [⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩] = true
  ct : ∀ {Y : Lay}, SOK L Y → Y.ok ⟨Y.sc, L.eC, 32 * L.p.du * L.p.k⟩ = true ∧
    Y.ok ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ = true

/-- `ek[384j : 384j + 384]`. -/
theorem ekT_eq [VG.Proof.MlKem.X86.Enc.EntOK L] [VG.Proof.MlKem.X86.Enc.VOK L] (hS : SOK L Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : Base L Y I s₀ s) {j : Nat}
    (hj : j < L.p.k) :
    decode12 (bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eEK + 384 * j, 384⟩) 384) = ekT (I.ek s₀) j := by
  have hok := ((VOK.v hS).2.2.2.2.2.2.2.1 j hj)
  simp only [Bool.and_eq_true] at hok
  rw [ekT, ← h.ek, bytesAt_slice _ _ (show 384 * j + 384 ≤ L.p.ekLen by unfold Params.ekLen; omega),
    Buf.addr_eq hp (b := bEK L Y.sc) (EntOK.seed hS).2.1, Buf.addr_eq hp (b := ⟨Y.sc, L.eEK + 384 * j, 384⟩) hok.1.1,
    BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `t̂[j]`, decoded, then `c`. -/
theorem dec_piece [VG.Proof.MlKem.X86.Enc.EntOK L] [VG.Proof.MlKem.X86.Enc.VOK L] (hS : SOK L Y) {I : Inp} (j : Nat) (hj : j < L.p.k)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.V1 L Y I j) Q c) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.V L Y I j) Q
      (.seq (dec12C Y.sc ⟨Y.sc, L.eEK + 384 * j, 384⟩ (VG.Proof.MlKem.X86.Enc.bT L Y.sc)) c) := by
  obtain ⟨v₁, v₂, -, -, -, -, -, v₈, -, -, -⟩ := VOK.v hS
  exact Piece.seq (dec12C_piece (Y := Y) Y.sc (L.eEK + 384 * j) Y.sc L.eT (v₈ j hj) hS.le (by sc_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp hS.le v₁ v₂ fr h', by rw [VG.Proof.MlKem.X86.Enc.ekT_eq hS hp h.toBase hj] at post; exact post⟩) hc

/-- Term 0 of `v`: `v ← t̂[0] ×_T ŷ[0]`. -/
theorem term0_piece [VG.Proof.MlKem.X86.Enc.EntOK L] [VG.Proof.MlKem.X86.Enc.VOK L] (hS : SOK L Y) {I : Inp} (hk : 0 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.V L Y I 0) (VG.Proof.MlKem.X86.Enc.V L Y I 1) (encTerm L Y.sc 0) := by
  obtain ⟨-, -, v₃, -, -, -, -, -, v₉, -, -⟩ := VOK.v hS
  refine VG.Proof.MlKem.X86.Enc.dec_piece hS 0 hk (mulC_piece (Y := Y) Y.sc L.eU Y.sc L.eT Y.sc 0 Y.sc L.eNS v₉
    hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, (h.y 0 hk).1⟩)
    fun s₀ s s' hp h h' fr post => ?_)
  refine ⟨h.toB.keep hp hS.le v₃ (Nat.le_refl _) fr h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, h.t.2, (h.y 0 hk).2]
  rfl

/-- Term `j + 1` of `v`: `v ← v + t̂[j + 1] ×_T ŷ[j + 1]`. -/
theorem term_piece [VG.Proof.MlKem.X86.Enc.EntOK L] [VG.Proof.MlKem.X86.Enc.VOK L] (hS : SOK L Y) {I : Inp} (j : Nat) (hj : j + 1 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.V L Y I (j + 1)) (VG.Proof.MlKem.X86.Enc.V L Y I (j + 2)) (encTerm L Y.sc (j + 1)) := by
  obtain ⟨-, -, -, v₄, v₅, v₆, -, -, -, v₁₀, v₁₁⟩ := VOK.v hS
  refine VG.Proof.MlKem.X86.Enc.dec_piece hS (j + 1) hj (.seq (B := VG.Proof.MlKem.X86.Enc.V2 L Y I (j + 1))
    (mulC_piece (Y := Y) Y.sc L.eP Y.sc L.eT Y.sc (1024 * (j + 1)) Y.sc L.eNS (v₁₀ (j + 1) hj) hS.le
      (by sc_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, (h.y (j + 1) (by omega)).1⟩)
      fun s₀ s s' hp h h' fr post => ?_) ?_)
  · refine ⟨h.keep hp hS.le v₄ v₆ fr h', ?_⟩
    rw [h.t.2, (h.y (j + 1) (by omega)).2] at post; exact post
  refine accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eP v₁₁ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.v (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  refine ⟨h.toB.keep hp hS.le v₅ (Nat.le_refl _) fr h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, (h.v (Nat.succ_pos _)).2, h.p.2]
  rfl

/-- `NTT⁻¹(t̂ ∘ ŷ)`, then with `e₂`, then with `μ`: `v`. -/
structure W (L : KemLay) (Y : Lay) (I : Inp) (n : Nat) (s₀ s : State) : Prop
    extends VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * L.p.k) L.p.k s₀ s where
  v : PolyIs s.mem (Buf.addr s₀ (bU L Y.sc)) (if n = 0 then nttInv (VG.Proof.MlKem.X86.Enc.partV I s₀ L.p.k)
    else if n = 1 then add (nttInv (VG.Proof.MlKem.X86.Enc.partV I s₀ L.p.k)) (cbd (rE I s₀) (2 * L.p.k))
    else KPke.encV L.p (I.ek s₀) (I.m s₀) (rE I s₀))

/-- After `v` is compressed into the ciphertext. -/
structure Done (L : KemLay) (Y : Lay) (I : Inp) (s₀ s : State) : Prop
    extends VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * L.p.k) L.p.k s₀ s where
  cv : bytesAt s.mem (Buf.addr s₀ ⟨Y.sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩) (32 * L.p.dv) =
    compressEncode L.p.dv (KPke.encV L.p (I.ek s₀) (I.m s₀) (rE I s₀))

/-- `v`, compressed into the ciphertext. -/
theorem v_piece [CeOK L] [BaseOK L] [VG.Proof.MlKem.X86.Enc.EntOK L] [VG.Proof.MlKem.X86.Enc.RowOK L] [VG.Proof.MlKem.X86.Enc.VOK L] (hS : SOK L Y) {I : Inp} (hk : 0 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * L.p.k) L.p.k) (VG.Proof.MlKem.X86.Enc.Done L Y I) (Impl.MlKem.X86.encV L Y.sc) := by
  obtain ⟨r₁, -, -, -, -, r₆, -, o₁, o₂, o₃, -⟩ := RowOK.row hS
  obtain ⟨w₁, w₂, w₃, w₄, w₅, w₆, w₇, w₈⟩ := VOK.w hS
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine (Piece.seqs0 (P := VG.Proof.MlKem.X86.Enc.V L Y I) L.p.k (fun j hj => match j, hj with
    | 0, _ => VG.Proof.MlKem.X86.Enc.term0_piece hS hk
    | j + 1, hj => VG.Proof.MlKem.X86.Enc.term_piece hS j hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.W L Y I 0) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack Y.sc L.eU Y.sc
    L.eNS o₁ hS.le (by sc_taint) (fun _ _ _ h => ⟨h.ctx, (h.v hk).1⟩)
    fun s₀ s s' hp h h' fr post => ⟨h.toB.keep hp hS.le r₁ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [(h.v hk).2] at post; exact post
  refine Piece.seq (VG.Proof.MlKem.X86.Enc.cbd_piece hS (2 * L.p.k) L.eE (Q := VG.Proof.MlKem.X86.Enc.W L Y I 0) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => ⟨h.toB.keep hp k88 w₁ (Nat.le_refl _) fr c, polyIs_congr (Top.keep hp k88 w₂ fr) h.v⟩)
    o₂) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.W L Y I 1) (accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eE o₃ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.v.1, h.2.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.1.toB.keep hp hS.le r₆ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [h.1.v.2, h.2.2] at post; exact post
  refine Piece.seq (B := fun s₀ s => VG.Proof.MlKem.X86.Enc.W L Y I 1 s₀ s ∧
      PolyIs s.mem (Buf.addr s₀ (bMU L Y.sc)) (decodeDecompress 1 (I.m s₀)))
    (ddC_piece (Y := Y) dd768 1 (by decide) Y.sc L.eM Y.sc L.eMU w₅ hS.le (by sc_taint) (fun _ _ _ h => h.ctx)
      fun s₀ s s' hp h h' fr post => ⟨⟨h.toB.keep hp hS.le w₃ (Nat.le_refl _) fr h',
        polyIs_congr (Top.keep hp hS.le w₄ fr) h.v⟩, by rw [h.m] at post; exact post⟩) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.Enc.W L Y I 2) (accC_piece add_verified add_nosp add_stack Y.sc L.eU Y.sc L.eMU w₆ hS.le
    (by sc_taint) (fun _ _ _ h => ⟨h.1.ctx, h.1.v.1, h.2.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.1.toB.keep hp hS.le r₆ (Nat.le_refl _) fr h', ?_⟩) ?_
  · rw [h.1.v.2, h.2.2] at post; exact post
  exact ceK_piece (Y := Y) L.p.dv (.inr rfl) Y.sc L.eU Y.sc (L.eC + 32 * L.p.du * L.p.k) w₇ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.ctx, h.v.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.toB.keep hp hS.le w₈ (Nat.le_refl _) fr h', by rw [post, h.v.2]; rfl⟩

/-! ## K-PKE.Encrypt -/

/-- `encrypt`, from its inputs. -/
theorem encrypt_piece [CeOK L] [BaseOK L] [VG.Proof.MlKem.X86.Enc.YOK L] [VG.Proof.MlKem.X86.Enc.EntOK L] [VG.Proof.MlKem.X86.Enc.RowOK L] [VG.Proof.MlKem.X86.Enc.VOK L] (hS : SOK L Y) {I : Inp} (hρ : VG.Proof.MlKem.X86.Enc.RhoPub L Y lk I) (hk : 0 < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (Base L Y I) (VG.Proof.MlKem.X86.Enc.Done L Y I) (encrypt L Y.sc) :=
  VG.Proof.MlKem.X86.Enc.ys_piece hS <| (Piece.seqs0 (P := fun i => VG.Proof.MlKem.X86.Enc.B L Y I (L.p.k * i) i) L.p.k (fun i hi => VG.Proof.MlKem.X86.Enc.row_piece hS hρ i hi)
    (VG.Proof.MlKem.X86.Enc.v_piece hS hk)).mono (fun _ _ _ h => ⟨h.toBase, h.y, .inr h.acc, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun e => absurd (h.acc.symm.trans e) (by decide), fun _ _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun _ _ _ h => h

/-- The ciphertext, if every sample succeeded. -/
theorem ct_eq [VG.Proof.MlKem.X86.Enc.VOK L] (hS : SOK L Y) {I : Inp} {s₀ s : State} (hp : TPre Y s₀) (h : VG.Proof.MlKem.X86.Enc.Done L Y I s₀ s)
    (e : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Enc.bC L Y.sc)) L.p.ctLen = KPke.ct L.p (aE L I s₀) (I.ek s₀) (I.m s₀) (rE I s₀) := by
  obtain ⟨o₁, o₂⟩ := VOK.ct hS
  rw [bytes_split hp _ (o' := L.eC + 32 * L.p.du * L.p.k) (l₁ := 32 * L.p.du * L.p.k) (l₂ := 32 * L.p.dv) rfl
    (by rw [Params.ctLen, Nat.mul_add, Nat.mul_assoc]) o₁ o₂, bytes_catK hp _ o₁, h.cv, KPke.ct]
  exact congrArg (· ++ _) (catK_congr fun i hi => h.c e i hi)

/-- Every sample, within one bound. -/
theorem samples {I : Inp} {s₀ s : State} (h : VG.Proof.MlKem.X86.Enc.Done L Y I s₀ s) (e : VG.Proof.MlKem.X86.Enc.accE L Y s₀ s = 1) :
    ∃ M, ∀ i < L.p.k, ∀ j < L.p.k, sampleNTT M (matSeed (ρE L I s₀) i j) = some (aE L I s₀ i j) := by
  obtain ⟨M, hM⟩ := samp_bound ((List.range (L.p.k * L.p.k)).map fun k =>
      (VG.Proof.MlKem.X86.Enc.mSE L I s₀ k, aE L I s₀ (k % L.p.k) (k / L.p.k))) (by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha⟩ := h.ok e k (List.mem_range.mp hk)
    show Samp (VG.Proof.MlKem.X86.Enc.mSE L I s₀ k) (sv (VG.Proof.MlKem.X86.Enc.mSE L I s₀ k))
    rw [sv_eq ha]; exact ha)
  refine ⟨M, fun i hi j hj => ?_⟩
  have r := hM (VG.Proof.MlKem.X86.Enc.mSE L I s₀ (L.p.k * j + i), aE L I s₀ ((L.p.k * j + i) % L.p.k) ((L.p.k * j + i) / L.p.k))
    (List.mem_map.mpr ⟨L.p.k * j + i, List.mem_range.mpr (idx_lt hj hi), rfl⟩)
  rw [VG.Proof.MlKem.X86.Enc.mSE_eq I s₀ hi, idx_mod hi, idx_div hi] at r
  exact r

end VG.Proof.MlKem.X86.Enc

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.DecapsPre`. -/
section

/-!
# ML-KEM on x86 (32-bit): the setting of decapsulation

The layout of the arguments (`Y L`: `dk`, `ct`, `key`, `scratch`, and the 88
bytes of stack), which each parameter set's contract implies; the public data,
`ρ`, which is that of the encapsulation key in `dk` (`KPke.ekRho_dkEk`); and
the values the body computes: `m'` (`mD`), and the inputs of the re-encryption
(`I`). `dk`, `ct` and the values computed from them are irreducible, so that
elaboration never evaluates their bytes.
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3_512)

/-- `dk` and `ct` (read), `key` and `scratch` (written); 88 bytes of stack. -/
def Y (L : KemLay) : Lay := ⟨[(L.p.dkLen, false), (L.p.ctLen, false), (32, true), (L.scratch, true)], 3, 88⟩

section
variable (L : KemLay) (s₀ : State)
/-- `dk`. -/
@[irreducible] def dk : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.dkLen⟩) L.p.dkLen
/-- `ct`. -/
@[irreducible] def ct : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, L.p.ctLen⟩) L.p.ctLen
/-- What decaps may leak: `ρ`. -/
abbrev lk : List Byte := dkRho L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀)
/-- `m' = K-PKE.Decrypt(dk_PKE, c)`. -/
@[irreducible] def mD : List Byte := KPke.decM L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) (VG.Proof.MlKem.X86.Decaps.ct L s₀)
/-- The encapsulation key in `dk`. -/
@[irreducible] def ekD : List Byte := KPke.dkEk L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀)
/-- `G(m' ‖ h)`, as 64 bytes. -/
@[irreducible] def krD : List Byte := sha3_512 (VG.Proof.MlKem.X86.Decaps.mD L s₀ ++ KPke.dkH L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀))
end

section
variable (L : KemLay) (s₀ : State)
theorem dk_eq : VG.Proof.MlKem.X86.Decaps.dk L s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.dkLen⟩) L.p.dkLen := by unfold VG.Proof.MlKem.X86.Decaps.dk; rfl
theorem ct_eq : VG.Proof.MlKem.X86.Decaps.ct L s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, L.p.ctLen⟩) L.p.ctLen := by unfold VG.Proof.MlKem.X86.Decaps.ct; rfl
theorem mD_eq : VG.Proof.MlKem.X86.Decaps.mD L s₀ = KPke.decM L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) (VG.Proof.MlKem.X86.Decaps.ct L s₀) := by unfold VG.Proof.MlKem.X86.Decaps.mD; rfl
theorem ekD_eq : VG.Proof.MlKem.X86.Decaps.ekD L s₀ = KPke.dkEk L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) := by unfold VG.Proof.MlKem.X86.Decaps.ekD; rfl
theorem krD_eq : VG.Proof.MlKem.X86.Decaps.krD L s₀ = sha3_512 (VG.Proof.MlKem.X86.Decaps.mD L s₀ ++ KPke.dkH L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀)) := by unfold VG.Proof.MlKem.X86.Decaps.krD; rfl
end

/-- The inputs of the re-encryption. -/
abbrev I (L : KemLay) : Enc.Inp := ⟨VG.Proof.MlKem.X86.Decaps.ekD L, VG.Proof.MlKem.X86.Decaps.mD L, VG.Proof.MlKem.X86.Decaps.krD L⟩

theorem hS (L : KemLay) : Enc.SOK L (VG.Proof.MlKem.X86.Decaps.Y L) := ⟨of_decide_eq_true rfl, rfl, rfl, rfl⟩

/-- `ρ` of the encapsulation key in `dk`, which the contract lets decaps leak. -/
theorem hρ (L : KemLay) : Enc.RhoPub L (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L) (VG.Proof.MlKem.X86.Decaps.I L) := fun s₀ s₀' _ _ hq => by
  show ekRho L.p (VG.Proof.MlKem.X86.Decaps.ekD L s₀) = ekRho L.p (VG.Proof.MlKem.X86.Decaps.ekD L s₀')
  rw [VG.Proof.MlKem.X86.Decaps.ekD_eq, VG.Proof.MlKem.X86.Decaps.ekD_eq, KPke.ekRho_dkEk, KPke.ekRho_dkEk]
  exact hq.2.2

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-- `sc_taint`, for code with `scratch` at `(Y L).sc`. -/
macro "yd_taint" : tactic => `(tactic| ((try simp only [show ∀ L, (Y L).sc = 3 from fun _ => rfl]); sc_taint))

end VG.Proof.MlKem.X86.Decaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.DecapsDec`. -/
section

/-!
# ML-KEM on x86 (32-bit): K-PKE.Decrypt in decapsulation

`w = Σ ŝ[i] ×_T NTT(u'[i])`, with `u'[i]` decoded and decompressed from `ct`
and `ŝ[i]` decoded from `dk` (`term0_piece`, `term_piece`), then `m' =
ByteEncode₁(Compress₁(v' - NTT⁻¹(w)))` (`decrypt_piece`), which is `mD`.
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (L : KemLay) (s₀ : State)
/-- `ŝ[i]`. -/
abbrev dS (i : Nat) : VG.Spec.MlKem.Poly := dcS (KPke.dkPke L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀)) i
/-- `NTT(u'[i])`. -/
abbrev dU (i : Nat) : VG.Spec.MlKem.Poly := ntt (KPke.dcU L.p (VG.Proof.MlKem.X86.Decaps.ct L s₀) i)
/-- `ŝ[0] ×_T NTT(u'[0]) + … + ŝ[j - 1] ×_T NTT(u'[j - 1])`. -/
abbrev partD (j : Nat) : VG.Spec.MlKem.Poly := KPke.dotK (VG.Proof.MlKem.X86.Decaps.dS L s₀) (VG.Proof.MlKem.X86.Decaps.dU L s₀) j
end

section
variable (L : KemLay)
abbrev bA : Buf := ⟨3, L.eA, 1024⟩
abbrev bT : Buf := ⟨3, L.eT, 1024⟩
abbrev bW : Buf := ⟨3, L.eU, 1024⟩
abbrev bP : Buf := ⟨3, L.eP, 1024⟩
abbrev bE : Buf := ⟨3, L.eE, 1024⟩
abbrev bNS : Buf := ⟨3, L.eNS, 1024⟩
abbrev bM : Buf := ⟨3, L.eM, 32⟩
/-- `u'[i]` in `ct`. -/
abbrev bCU (i : Nat) : Buf := ⟨1, 32 * L.p.du * i, 32 * L.p.du⟩
/-- `v'` in `ct`. -/
abbrev bCV : Buf := ⟨1, 32 * L.p.du * L.p.k, 32 * L.p.dv⟩
end

/-- Before term `j`: and `w` so far, if `0 < j`. -/
structure D (L : KemLay) (j : Nat) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s
  w : 0 < j → Reduced s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bW L)) ∧ polyAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bW L)) = VG.Proof.MlKem.X86.Decaps.partD L s₀ j

variable {L : KemLay}

theorem D.keep {j : Nat} {s₀ s s' : State} (hp : TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (VG.Proof.MlKem.X86.Decaps.Y L).stk) (hW : (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bW L) bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : VG.Proof.MlKem.X86.Decaps.D L j s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s') : VG.Proof.MlKem.X86.Decaps.D L j s₀ s' :=
  ⟨c, fun hj => ⟨keepRed hp hM hW fr (h.w hj).1, by rw [polyAt_congr (Top.keep hp hM hW fr)]; exact (h.w hj).2⟩⟩

/-- `u'[i]` is decoded, decompressed and in the NTT domain; `ŝ[i]` decoded. -/
structure D1 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.D L j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bA L)) (KPke.dcU L.p (VG.Proof.MlKem.X86.Decaps.ct L s₀) j)

structure D2 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.D L j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bA L)) (VG.Proof.MlKem.X86.Decaps.dU L s₀ j)

structure D3 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.D2 L j s₀ s where
  t : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bT L)) (VG.Proof.MlKem.X86.Decaps.dS L s₀ j)

structure D4 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.D L j s₀ s where
  p : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bP L)) (multiplyNTTs (VG.Proof.MlKem.X86.Decaps.dS L s₀ j) (VG.Proof.MlKem.X86.Decaps.dU L s₀ j))

/-- The facts of the layout that K-PKE.Decrypt uses. -/
class DecOK (L : KemLay) : Prop where
  ct : (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨1, 0, L.p.ctLen⟩ = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 0, L.p.dkLen⟩ = true ∧
    32 * L.p.du * L.p.k + 32 * L.p.dv ≤ L.p.ctLen
  dec : ∀ i < L.p.k, (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bCU L i) = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 384 * i, 384⟩ = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bCU L i) && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bA L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bCU L i) (VG.Proof.MlKem.X86.Decaps.bA L)) = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 384 * i, 384⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bT L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨0, 384 * i, 384⟩ (VG.Proof.MlKem.X86.Decaps.bT L)) = true
  keep : (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bW L) [VG.Proof.MlKem.X86.Decaps.bA L] = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bW L) [VG.Proof.MlKem.X86.Decaps.bA L, VG.Proof.MlKem.X86.Decaps.bNS L] = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bA L) && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bNS L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bA L) (VG.Proof.MlKem.X86.Decaps.bNS L)) = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bW L) [VG.Proof.MlKem.X86.Decaps.bT L] = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bA L) [VG.Proof.MlKem.X86.Decaps.bT L] = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bW L) [VG.Proof.MlKem.X86.Decaps.bP L, VG.Proof.MlKem.X86.Decaps.bNS L] = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bW L) && (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bP L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bW L) (VG.Proof.MlKem.X86.Decaps.bP L)) = true
  mul : ((VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bW L) && (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bT L) && (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bA L) && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bNS L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bW L) (VG.Proof.MlKem.X86.Decaps.bT L) &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bW L) (VG.Proof.MlKem.X86.Decaps.bA L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bW L) (VG.Proof.MlKem.X86.Decaps.bNS L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bT L) (VG.Proof.MlKem.X86.Decaps.bNS L) &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bA L) (VG.Proof.MlKem.X86.Decaps.bNS L)) = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bP L) && (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bT L) && (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bA L) && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bNS L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bP L) (VG.Proof.MlKem.X86.Decaps.bT L) &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bP L) (VG.Proof.MlKem.X86.Decaps.bA L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bP L) (VG.Proof.MlKem.X86.Decaps.bNS L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bT L) (VG.Proof.MlKem.X86.Decaps.bNS L) &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bA L) (VG.Proof.MlKem.X86.Decaps.bNS L)) = true
  v : ((VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bW L) && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bNS L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bW L) (VG.Proof.MlKem.X86.Decaps.bNS L)) = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bCV L) && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bE L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bCV L) (VG.Proof.MlKem.X86.Decaps.bE L)) = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bCV L) = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bW L) [VG.Proof.MlKem.X86.Decaps.bE L] = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bE L) && (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bW L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bE L) (VG.Proof.MlKem.X86.Decaps.bW L)) = true ∧
    ((VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bE L) && (VG.Proof.MlKem.X86.Decaps.Y L).okW ⟨3, L.eM, 32 * 1⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bE L) ⟨3, L.eM, 32 * 1⟩) = true

variable [VG.Proof.MlKem.X86.Decaps.DecOK L]

/-- The bytes of `ct[o : o + l]`. -/
theorem ct_slice {s₀ s : State} (hp : TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s) {o l : Nat} (hl : o + l ≤ L.p.ctLen)
    (hb : (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨1, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, o, l⟩) l = ((VG.Proof.MlKem.X86.Decaps.ct L s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨1, o, l⟩) hb rfl, VG.Proof.MlKem.X86.Decaps.ct_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨1, o, l⟩) hb, Buf.addr_eq hp (b := ⟨1, 0, L.p.ctLen⟩) DecOK.ct.1, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

/-- The bytes of `dk[o : o + l]`. -/
theorem dk_slice {s₀ s : State} (hp : TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀) (h : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s) {o l : Nat} (hl : o + l ≤ L.p.dkLen)
    (hb : (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((VG.Proof.MlKem.X86.Decaps.dk L s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨0, o, l⟩) hb rfl, VG.Proof.MlKem.X86.Decaps.dk_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨0, o, l⟩) hb, Buf.addr_eq hp (b := ⟨0, 0, L.p.dkLen⟩) DecOK.ct.2.1, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

/-- `u'[i]` and `ŝ[i]`, then `c`. -/
theorem uS_piece [CeOK L] (j : Nat) (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (VG.Proof.MlKem.X86.Decaps.D3 L j) Q c) :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (VG.Proof.MlKem.X86.Decaps.D L j) Q
      (.seq (ddK L 3 L.p.du (VG.Proof.MlKem.X86.Decaps.bCU L j) (VG.Proof.MlKem.X86.Decaps.bA L)) <| .seq (nttC 3 (VG.Proof.MlKem.X86.Decaps.bA L) (VG.Proof.MlKem.X86.Decaps.bNS L)) <|
        .seq (dec12C 3 ⟨0, 384 * j, 384⟩ (VG.Proof.MlKem.X86.Decaps.bT L)) c) := by
  obtain ⟨o₁, o₂, o₃, o₄⟩ := DecOK.dec j hj
  obtain ⟨k₁, k₂, k₃, k₄, k₅, -⟩ := DecOK.keep (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.D1 L j) (ddK_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) L.p.du (.inl rfl) 1 (32 * L.p.du * j) 3 L.eA o₃ (by rdecide)
    (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨h.keep hp (by rdecide) k₁ fr h', ?_⟩) ?_
  · rw [VG.Proof.MlKem.X86.Decaps.ct_slice hp h.ctx ?_ o₁] at post
    · exact post
    · have := DecOK.ct (L := L)
      have : 32 * L.p.du * j + 32 * L.p.du ≤ 32 * L.p.du * L.p.k := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.D2 L j) (inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 L.eA 3 L.eNS k₃
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by rdecide) k₂ fr h', by rw [h.u.2] at post; exact post⟩) ?_
  refine Piece.seq (dec12C_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) 0 (384 * j) 3 L.eT o₄ (by rdecide) (by yd_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨⟨h.keep hp (by rdecide) k₄ fr h',
      polyIs_congr (Top.keep hp (by rdecide) (b := VG.Proof.MlKem.X86.Decaps.bA L) k₅ fr) h.u⟩, ?_⟩) hc
  rw [VG.Proof.MlKem.X86.Decaps.dk_slice hp h.ctx (by unfold Params.dkLen; omega) o₂] at post
  rw [VG.Proof.MlKem.X86.Decaps.dS, dcS, KPke.dkPke, slice_take _ (show 384 * j + 384 ≤ 384 * L.p.k by omega)]
  exact post

/-- Term 0: `w ← ŝ[0] ×_T NTT(u'[0])`. -/
theorem term0_piece [CeOK L] (hk : 0 < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (VG.Proof.MlKem.X86.Decaps.D L 0) (VG.Proof.MlKem.X86.Decaps.D L 1) (decTerm L 0) :=
  VG.Proof.MlKem.X86.Decaps.uS_piece 0 hk (mulC_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) 3 L.eU 3 L.eT 3 L.eA 3 L.eNS DecOK.mul.1
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩)
    fun s₀ s s' hp h h' fr post => ⟨h', fun _ => ⟨post.1, by rw [post.2, h.t.2, h.u.2]; rfl⟩⟩)

/-- Term `j + 1`: `w ← w + ŝ[j + 1] ×_T NTT(u'[j + 1])`. -/
theorem term_piece [CeOK L] (j : Nat) (hj : j + 1 < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (VG.Proof.MlKem.X86.Decaps.D L (j + 1)) (VG.Proof.MlKem.X86.Decaps.D L (j + 2)) (decTerm L (j + 1)) := by
  obtain ⟨-, -, -, -, -, k₆, k₇⟩ := DecOK.keep (L := L)
  refine VG.Proof.MlKem.X86.Decaps.uS_piece (j + 1) hj (.seq (B := VG.Proof.MlKem.X86.Decaps.D4 L (j + 1)) (mulC_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) 3 L.eP 3 L.eT 3 L.eA 3 L.eNS
    DecOK.mul.2 (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by rdecide) k₆ fr h', by rw [h.t.2, h.u.2] at post; exact post⟩) ?_)
  refine accC_piece add_verified add_nosp add_stack 3 L.eU 3 L.eP k₇ (by rdecide) (by yd_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.w (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  refine ⟨h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, (h.w (Nat.succ_pos _)).2, h.p.2]
  rfl

/-- `NTT⁻¹(w)`. -/
structure E1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s
  w : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bW L)) (nttInv (VG.Proof.MlKem.X86.Decaps.partD L s₀ L.p.k))

/-- And `v'`. -/
structure E2 (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.E1 L s₀ s where
  v : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bE L)) (KPke.dcV L.p (VG.Proof.MlKem.X86.Decaps.ct L s₀))

/-- `v' - NTT⁻¹(w)`. -/
structure E3 (L : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s
  v : PolyIs s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bE L)) (sub (KPke.dcV L.p (VG.Proof.MlKem.X86.Decaps.ct L s₀)) (nttInv (VG.Proof.MlKem.X86.Decaps.partD L s₀ L.p.k)))

/-- After `m'` is computed. -/
structure DM (L : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s
  m : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bM L)) 32 = VG.Proof.MlKem.X86.Decaps.mD L s₀

/-- K-PKE.Decrypt(dk_PKE, c). -/
theorem decrypt_piece [CeOK L] (hk : 0 < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L)) (VG.Proof.MlKem.X86.Decaps.DM L) (decrypt L) := by
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆⟩ := DecOK.v (L := L)
  refine (Piece.seqs0 (P := VG.Proof.MlKem.X86.Decaps.D L) L.p.k (fun j hj => match j, hj with
    | 0, _ => VG.Proof.MlKem.X86.Decaps.term0_piece hk
    | j + 1, hj => VG.Proof.MlKem.X86.Decaps.term_piece j hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.E1 L) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack 3 L.eU 3 L.eNS v₁
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, (h.w hk).1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [(h.w hk).2] at post; exact post⟩) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.E2 L) (ddK_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) L.p.dv (.inr rfl) 1 (32 * L.p.du * L.p.k) 3 L.eE v₂
    (by rdecide) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', polyIs_congr (Top.keep hp (by rdecide) (b := VG.Proof.MlKem.X86.Decaps.bW L) v₄ fr) h.w⟩, ?_⟩) ?_
  · rw [VG.Proof.MlKem.X86.Decaps.ct_slice hp h.ctx DecOK.ct.2.2 v₃] at post; exact post
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.E3 L) (accC_piece sub_verified sub_nosp sub_stack 3 L.eE 3 L.eU v₅ (by rdecide)
    (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.v.1, h.w.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [h.v.2, h.w.2] at post; exact post⟩) ?_
  refine ceC_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) ce768 1 (by decide) 3 L.eE 3 L.eM v₆ (by rdecide) (by yd_taint)
    (fun _ _ _ h => ⟨h.ctx, h.v.1⟩) fun s₀ s s' hp h h' fr post => ⟨h', ?_⟩
  rw [show Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bM L) = Buf.addr s₀ ⟨3, L.eM, 32 * 1⟩ from rfl, post, h.v.2, VG.Proof.MlKem.X86.Decaps.mD_eq, KPke.decM,
    KPke.kpkeDecrypt_eq]

end VG.Proof.MlKem.X86.Decaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.DecapsCmp`. -/
section

/-!
# ML-KEM on x86 (32-bit): the implicit rejection in decapsulation

`cmpC` compares `ct` with `c'` (at `eC`) without branching on them: `ebx` is
the OR of the XORs of their bytes (`accB`), then all ones if it is 0 and zero
otherwise (`sub`, `sbb`), which is all ones exactly when `ct = c'`
(`eq_iff_foldl_or_xor`): `cmp_piece`. `selC` writes `K̄ ^ ((K' ^ K̄) & mask)`
byte by byte into `key` (`sel_piece`): `K'` if the mask is all ones, and `K̄`
if it is zero.
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

variable {L : KemLay} {A B : State → State → Prop}

/-! ## Single instructions -/

theorem wp_movzx' {d b : Reg} {disp : Nat} {is : List Instr} {s : State} {Q : State → Prop}
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b disp)) 1)
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.mem (s.ea (at_ b disp))).setWidth 32 → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d (at_ b disp) :: is)) s Q :=
  wp_movzx hin (k _ (Only.setReg s d _) (by simp [State.setReg]))

theorem wp_xorr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d ^^^ s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d ^^^ s.gpr r) false false).setReg d (s.gpr d ^^^ s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_orr {d r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d ||| s.gpr r → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d (.reg r) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d ||| s.gpr r) false false).setReg d (s.gpr d ||| s.gpr r))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

theorem wp_subi {d : Reg} {v : BitVec 32} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - v → s'.cf = some (decide ((s.gpr d).toNat < v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - v) (decide ((s.gpr d).toNat < v.toNat))
      (subOverflow (s.gpr d) v (s.gpr d - v))).setReg d (s.gpr d - v))
    (by simp only [exec, execAlu, readSrc, Option.bind_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]) (by simp [State.setReg, arithFlags, State.setFlags]))

theorem wp_sbbself {d : Reg} {c : Bool} {is : List Instr} {s : State} {Q : State → Prop} (hc : s.cf = some c)
    (k : ∀ s', Only [d] s s' → s'.gpr d = s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32 →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sbb d (.reg d) :: is)) s Q :=
  wp_cons (s' := (arithFlags s (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32)
      (decide ((s.gpr d).toNat < (s.gpr d).toNat + c.toNat))
      (subOverflow (s.gpr d) (s.gpr d) (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32))).setReg d
        (s.gpr d - s.gpr d - (BitVec.ofBool c).setWidth 32))
    (by simp only [exec, execAlu, readSrc, Option.bind_some, hc, Option.map_some])
    (k _ (Only.flags s d _ _ _) (by simp [State.setReg]))

/-! ## The comparison -/

/-- The OR of the XORs of the first `k` bytes of `c` and `c'`. -/
def accB (c c' : List Byte) : Nat → Byte
  | 0 => 0
  | k + 1 => VG.Proof.MlKem.X86.Decaps.accB c c' k ||| (c.getD k 0 ^^^ c'.getD k 0)

theorem accB_eq (c c' : List Byte) : ∀ n, n ≤ c.length → n ≤ c'.length →
    VG.Proof.MlKem.X86.Decaps.accB c c' n = ((c.take n).zipWith (· ^^^ ·) (c'.take n)).foldl (· ||| ·) 0
  | 0, _, _ => by simp [VG.Proof.MlKem.X86.Decaps.accB]
  | n + 1, h₁, h₂ => by
    rw [VG.Proof.MlKem.X86.Decaps.accB, VG.Proof.MlKem.X86.Decaps.accB_eq c c' n (by omega) (by omega), List.take_add_one, List.take_add_one,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), Option.toList_some,
      Option.toList_some, List.zipWith_append (by simp; omega), List.foldl_append]
    simp only [List.zipWith_cons_cons, List.zipWith_nil_left, List.foldl_cons, List.foldl_nil,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show n < c.length by omega),
      List.getElem?_eq_getElem (show n < c'.length by omega), Option.getD_some]

/-- `c` and `c'` of `n` bytes are equal exactly when `accB` of all their bytes is 0. -/
theorem accB_zero {c c' : List Byte} {n : Nat} (h₁ : c.length = n) (h₂ : c'.length = n) :
    c = c' ↔ VG.Proof.MlKem.X86.Decaps.accB c c' n = 0 := by
  rw [VG.Proof.MlKem.X86.Decaps.accB_eq c c' n (by omega) (by omega), List.take_of_length_le (by omega),
    List.take_of_length_le (by omega)]
  exact eq_iff_foldl_or_xor (by omega)

/-- `c'`. -/
abbrev bC (L : KemLay) : Buf := ⟨3, L.eC, L.p.ctLen⟩

/-- The mask: all ones if `p`, and zero otherwise. -/
def mask (p : Prop) [Decidable p] : BitVec 32 := if p then 0xffffffff else 0

/-- The facts of the layout that the comparison and the selection use. -/
class CmpOK (L : KemLay) : Prop where
  ct : (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨1, 0, L.p.ctLen⟩ = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).ok (VG.Proof.MlKem.X86.Decaps.bC L) = true ∧ 0 < L.p.ctLen ∧ L.p.ctLen < 2 ^ 32 ∧
    L.eC + L.p.ctLen ≤ L.scratch
  sel : (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨3, L.eKR, 32⟩ = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨3, L.eH, 32⟩ = true ∧ L.eKR + 32 ≤ L.scratch ∧
    L.eH + 32 ≤ L.scratch

/-- The comparison, from the setup. -/
structure CL (L : KemLay) (s₀ : State) (m : Mem) (k : Nat) (u : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ u
  mem : u.mem = m
  edi : u.gpr .edi = arg s₀ 1 + BitVec.ofNat 32 k
  ebp : u.gpr .ebp = arg s₀ 3 + BitVec.ofNat 32 k
  ecx : u.gpr .ecx = BitVec.ofNat 32 (L.p.ctLen - k)
  ebx : u.gpr .ebx = (VG.Proof.MlKem.X86.Decaps.accB (VG.Proof.MlKem.X86.Decaps.ct L s₀) (bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen) k).setWidth 32

theorem cmp_step [VG.Proof.MlKem.X86.Decaps.CmpOK L] {s₀ : State} (hp : TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀) {m : Mem} {k : Nat} (hk : k < L.p.ctLen) {u : State}
    (h : VG.Proof.MlKem.X86.Decaps.CL L s₀ m k u) :
    WP isa (.block (cmpBody L)) u fun u' => VG.Proof.MlKem.X86.Decaps.CL L s₀ m (k + 1) u' ∧
      isa.eval .ne u' = some (decide (k + 1 < L.p.ctLen)) := by
  obtain ⟨ok₁, ok₂, -, hN, hC⟩ := CmpOK.ct (L := L)
  have f1 : (arg s₀ 1).toNat + L.p.ctLen ≤ 2 ^ 32 := hp.fit 1 (by rdecide)
  have f3 : (arg s₀ 3).toNat + L.scratch ≤ 2 ^ 32 := hp.fit 3 (by rdecide)
  have e₁ : u.ea (at_ .edi 0) = Buf.addr s₀ ⟨1, 0, L.p.ctLen⟩ + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.edi]; rw [ea_add (by omega), VG.Proof.MlKem.X86.Decaps.addr0]; rfl
  have e₂ : u.ea (at_ .ebp L.eC) = Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L) + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, h.ebp]
    rw [ea_add (by omega), Buf.addr_eq hp (b := VG.Proof.MlKem.X86.Decaps.bC L) ok₂, BitVec.add_assoc,
      ← BitVec.ofNat_add, Nat.add_comm]
  have i₁ := Buf.inRegR (o := k) (n := 1) hp (b := ⟨1, 0, L.p.ctLen⟩) ok₁ h.ctx.rd h.ctx.wr
    (show k + 1 ≤ L.p.ctLen by omega)
  refine VG.Proof.MlKem.X86.Decaps.wp_movzx' (by rw [e₁]; exact i₁) fun u₁ o₁ v₁ => ?_
  have c₁ := h.ctx.only o₁ (by decide) (by decide)
  have e₂' : u₁.ea (at_ .ebp L.eC) = Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L) + BitVec.ofNat 64 k := by
    rw [← e₂]; simp only [State.ea, at_, o₁.gpr .ebp (by decide)]
  have i₂ := Buf.inRegR (o := k) (n := 1) hp (b := VG.Proof.MlKem.X86.Decaps.bC L) ok₂ c₁.rd c₁.wr (show k + 1 ≤ L.p.ctLen by omega)
  refine VG.Proof.MlKem.X86.Decaps.wp_movzx' (by rw [e₂']; exact i₂) fun u₂ o₂ v₂ => ?_
  refine VG.Proof.MlKem.X86.Decaps.wp_xorr fun u₃ o₃ v₃ => VG.Proof.MlKem.X86.Decaps.wp_orr fun u₄ o₄ v₄ => wp_addi fun u₅ o₅ v₅ => wp_addi fun u₆ o₆ v₆ =>
    wp_subi_last fun u₇ o₇ v₇ z₇ => ?_
  have c₇ := (((((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide)
    (by decide)).only o₅ (by decide) (by decide)).only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)
  have m₁ : u₁.mem = m := o₁.mem.trans h.mem
  have x₁ : u.mem (Buf.addr s₀ ⟨1, 0, L.p.ctLen⟩ + BitVec.ofNat 64 k) = (VG.Proof.MlKem.X86.Decaps.ct L s₀).getD k 0 := by
    rw [h.ctx.ro hp (b := ⟨1, 0, L.p.ctLen⟩) ok₁ rfl hk, VG.Proof.MlKem.X86.Decaps.ct_eq, bytesAt_getD _ _ hk]
  have x₂ : u₁.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L) + BitVec.ofNat 64 k) =
      (bytesAt m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen).getD k 0 := by
    rw [m₁, bytesAt_getD _ _ hk]
  have ex : u₆.gpr .ecx = BitVec.ofNat 32 (L.p.ctLen - k) := by
    rw [o₆.gpr _ (by decide), o₅.gpr _ (by decide), o₄.gpr _ (by decide), o₃.gpr _ (by decide),
      o₂.gpr _ (by decide), o₁.gpr _ (by decide), h.ecx]
  refine ⟨⟨c₇, by rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, m₁], ?_, ?_, by rw [v₇, ex]; exact cnt_next hk,
    ?_⟩, ?_⟩
  · rw [o₇.gpr .edi (by decide), o₆.gpr .edi (by decide), v₅, o₄.gpr .edi (by decide), o₃.gpr .edi (by decide),
      o₂.gpr .edi (by decide), o₁.gpr .edi (by decide), h.edi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .ebp (by decide), v₆, o₅.gpr .ebp (by decide), o₄.gpr .ebp (by decide), o₃.gpr .ebp (by decide),
      o₂.gpr .ebp (by decide), o₁.gpr .ebp (by decide), h.ebp,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₇.gpr .ebx (by decide), o₆.gpr .ebx (by decide), o₅.gpr .ebx (by decide), v₄, v₃, o₃.gpr .ebx (by decide),
      o₂.gpr .ebx (by decide), o₂.gpr .eax (by decide), v₂, o₁.gpr .ebx (by decide), v₁, h.ebx, e₁, e₂', x₁, x₂,
      VG.Proof.MlKem.X86.Decaps.accB, BitVec.setWidth_or, BitVec.setWidth_xor]
  · show u₇.zf.map (!·) = _
    rw [z₇, ex]; exact cnt_ne hk hN

/-- `ebx ←` all ones if `ct = c'`, and zero otherwise. -/
theorem cmp_piece [VG.Proof.MlKem.X86.Decaps.CmpOK L] (hA : ∀ s₀ s, TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s' → s'.mem = s.mem →
      s'.gpr .ebx = VG.Proof.MlKem.X86.Decaps.mask (VG.Proof.MlKem.X86.Decaps.ct L s₀ = bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen) → B s₀ s') :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) A B (cmpC L) := by
  obtain ⟨-, -, h0, -⟩ := CmpOK.ct (L := L)
  refine Piece.seq (setup_piece (fun s₀ s₁ => s₁.gpr .edi = arg s₀ 1 ∧ s₁.gpr .ebp = arg s₀ 3 ∧
      s₁.gpr .ecx = BitVec.ofNat 32 L.p.ctLen ∧ s₁.gpr .ebx = 0) (fun s₀ s hp h => ?_) hA (by taint_rfl)) ?_
  · have ea : s.ea (at_ .esp 24) = argAddr s₀ 1 := h.argEa (i := 1)
    refine wp_movm' (by rw [ea]; exact h.argIn hp (by rdecide)) fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movr' fun s₂ o₂ v₂ => wp_movi fun s₃ o₃ v₃ => wp_movi fun s₄ o₄ v₄ => WP.block_nil_iff.mpr ?_
    have c₄ := ((c₁.only o₂ (by decide) (by decide)).only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)
    refine ⟨c₄, by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem], ?_, ?_, by rw [o₄.gpr _ (by decide), v₃], v₄⟩
    · rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), o₂.gpr _ (by decide), v₁, ea, h.argw hp (by rdecide)]
    · rw [o₄.gpr _ (by decide), o₃.gpr _ (by decide), v₂, c₁.esi]; rfl
  refine Piece.seq (B := fun s₀ u => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Decaps.CL L s₀ s.mem L.p.ctLen u)
    (Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h₁, m₁, e₁, e₂, e₃, e₄⟩ => ?_)
      (fun s₀ s₀' s s' hp hp' hq ⟨_, _, _, _, e₁, e₂, e₃, _⟩ ⟨_, _, _, _, e₁', e₂', e₃', _⟩ r hr => ?_)
      (by taint_rfl)) ?_
  · refine (wp_count (N := L.p.ctLen) h0 (VG.Proof.MlKem.X86.Decaps.CL L s₀ s.mem) ⟨h₁, m₁, by rw [e₁]; simp, by rw [e₂]; simp,
      by rw [e₃, Nat.sub_zero], by rw [e₄]; rfl⟩ fun k hk u h => VG.Proof.MlKem.X86.Decaps.cmp_step hp hk h).mono fun u h => ⟨s, ha, h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [e₁, e₁', hq.2.1 1 (by rdecide)]
    · rw [e₂, e₂', hq.2.1 3 (by rdecide)]
    · rw [e₃, e₃']
  refine Piece.taint [] (fun s₀ u hp ⟨s, ha, h⟩ => ?_) (fun _ _ _ _ _ _ _ _ _ r hr => absurd hr (by simp))
    (by taint_decide)
  refine VG.Proof.MlKem.X86.Decaps.wp_subi fun u₁ o₁ v₁ f₁ => VG.Proof.MlKem.X86.Decaps.wp_sbbself f₁ fun u₂ o₂ v₂ => WP.block_nil_iff.mpr ?_
  have c₂ := (h.ctx.only o₁ (by decide) (by decide)).only o₂ (by decide) (by decide)
  refine hQ s₀ s u₂ hp ha c₂ (by rw [o₂.mem, o₁.mem, h.mem]) ?_
  rw [v₂, CheckEk.sbb_mask, h.ebx, VG.Proof.MlKem.X86.Decaps.mask]
  have hl : (bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen).length = L.p.ctLen := bytesAt_length _ _ _
  have hc : (VG.Proof.MlKem.X86.Decaps.ct L s₀).length = L.p.ctLen := by rw [VG.Proof.MlKem.X86.Decaps.ct_eq]; exact bytesAt_length _ _ _
  have lt := (VG.Proof.MlKem.X86.Decaps.accB (VG.Proof.MlKem.X86.Decaps.ct L s₀) (bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen) L.p.ctLen).isLt
  by_cases e : VG.Proof.MlKem.X86.Decaps.ct L s₀ = bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen
  · have z := (VG.Proof.MlKem.X86.Decaps.accB_zero hc hl).mp e
    rw [ite_eq_left e, z]; rfl
  · have z : VG.Proof.MlKem.X86.Decaps.accB (VG.Proof.MlKem.X86.Decaps.ct L s₀) (bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen) L.p.ctLen ≠ 0 :=
      fun z => e ((VG.Proof.MlKem.X86.Decaps.accB_zero hc hl).mpr z)
    rw [ite_eq_right e]
    have : ¬ ((VG.Proof.MlKem.X86.Decaps.accB (VG.Proof.MlKem.X86.Decaps.ct L s₀) (bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen) L.p.ctLen).setWidth 32).toNat <
        (1 : BitVec 32).toNat := by
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
      intro h'
      exact z (BitVec.eq_of_toNat_eq (by simp at h'; simp [h']))
    simp only [this, decide_false]
    rfl

/-! ## The selection -/

/-- `b ^ ((a ^ b) & m)`: `a` if `m` is all ones, and `b` if it is zero. -/
def selB (m a b : Byte) : Byte := b ^^^ ((a ^^^ b) &&& m)

/-- `key`, `K'` and `K̄`. -/
abbrev bKey : Buf := ⟨2, 0, 32⟩
abbrev bK (L : KemLay) : Buf := ⟨3, L.eKR, 32⟩
abbrev bKB (L : KemLay) : Buf := ⟨3, L.eH, 32⟩

/-- The selection, from the setup. -/
structure SL (L : KemLay) (s₀ : State) (m : Mem) (M : BitVec 32) (k : Nat) (u : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ u
  fr : Frame [Buf.rgn s₀ VG.Proof.MlKem.X86.Decaps.bKey] m u.mem
  edi : u.gpr .edi = arg s₀ 3 + BitVec.ofNat 32 k
  ebp : u.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 k
  ecx : u.gpr .ecx = BitVec.ofNat 32 (32 - k)
  ebx : u.gpr .ebx = M
  out : ∀ j < k, u.mem (Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey + BitVec.ofNat 64 j) =
    VG.Proof.MlKem.X86.Decaps.selB (M.setWidth 8) (m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bK L) + BitVec.ofNat 64 j)) (m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bKB L) + BitVec.ofNat 64 j))

theorem sel_step [VG.Proof.MlKem.X86.Decaps.CmpOK L] {s₀ : State} (hp : TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀) {m : Mem} {M : BitVec 32} {k : Nat} (hk : k < 32)
    {u : State} (h : VG.Proof.MlKem.X86.Decaps.SL L s₀ m M k u) :
    WP isa (.block (selBody L)) u fun u' => VG.Proof.MlKem.X86.Decaps.SL L s₀ m M (k + 1) u' ∧
      isa.eval .ne u' = some (decide (k + 1 < 32)) := by
  obtain ⟨ok₁, ok₂, n₁, n₂⟩ := CmpOK.sel (L := L)
  have f2 : (arg s₀ 2).toNat + 32 ≤ 2 ^ 32 := hp.fit 2 (by rdecide)
  have f3 : (arg s₀ 3).toNat + L.scratch ≤ 2 ^ 32 := hp.fit 3 (by rdecide)
  have ea : ∀ (u' : State) (o : Nat) (b : Buf), u'.gpr .edi = arg s₀ 3 + BitVec.ofNat 32 k → b.arg = 3 → b.off = o →
      (VG.Proof.MlKem.X86.Decaps.Y L).ok b = true → o + k < L.scratch → u'.ea (at_ .edi o) = Buf.addr s₀ b + BitVec.ofNat 64 k :=
    fun u' o b e h₁ h₂ hok ho => by
      simp only [State.ea, at_, e]
      rw [ea_add (by omega), Buf.addr_eq hp hok, h₁, h₂, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm]
  have e₁ := ea u L.eKR (VG.Proof.MlKem.X86.Decaps.bK L) h.edi rfl rfl ok₁ (by omega)
  have i₁ := Buf.inRegR (o := k) (n := 1) hp (b := VG.Proof.MlKem.X86.Decaps.bK L) ok₁ h.ctx.rd h.ctx.wr (show k + 1 ≤ 32 by omega)
  refine VG.Proof.MlKem.X86.Decaps.wp_movzx' (by rw [e₁]; exact i₁) fun u₁ o₁ v₁ => ?_
  have c₁ := h.ctx.only o₁ (by decide) (by decide)
  have e₂ := ea u₁ L.eH (VG.Proof.MlKem.X86.Decaps.bKB L) (by rw [o₁.gpr .edi (by decide), h.edi]) rfl rfl ok₂ (by omega)
  have i₂ := Buf.inRegR (o := k) (n := 1) hp (b := VG.Proof.MlKem.X86.Decaps.bKB L) ok₂ c₁.rd c₁.wr (show k + 1 ≤ 32 by omega)
  refine VG.Proof.MlKem.X86.Decaps.wp_movzx' (by rw [e₂]; exact i₂) fun u₂ o₂ v₂ => ?_
  have c₂ := c₁.only o₂ (by decide) (by decide)
  refine VG.Proof.MlKem.X86.Decaps.wp_xorr fun u₃ o₃ v₃ => wp_andr fun u₄ o₄ v₄ => VG.Proof.MlKem.X86.Decaps.wp_xorr fun u₅ o₅ v₅ => ?_
  have c₅ := ((c₂.only o₃ (by decide) (by decide)).only o₄ (by decide) (by decide)).only o₅ (by decide) (by decide)
  have eb : u₅.gpr .ebp = arg s₀ 2 + BitVec.ofNat 32 k := by
    rw [o₅.gpr .ebp (by decide), o₄.gpr .ebp (by decide), o₃.gpr .ebp (by decide), o₂.gpr .ebp (by decide),
      o₁.gpr .ebp (by decide), h.ebp]
  have e₃ : u₅.ea (at_ .ebp 0) = Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey + BitVec.ofNat 64 k := by
    simp only [State.ea, at_, eb]; rw [ea_add (by omega), VG.Proof.MlKem.X86.Decaps.addr0]; rfl
  have i₃ := Buf.inRegW (o := k) (n := 1) hp (b := VG.Proof.MlKem.X86.Decaps.bKey) (by rdecide) (by rdecide) c₅.wr (show k + 1 ≤ 32 by omega)
  refine wp_store8 (by rw [e₃]; exact i₃) (wp_addi fun u₆ o₆ v₆ => wp_addi fun u₇ o₇ v₇ =>
    wp_subi_last fun u₈ o₈ v₈ z₈ => ?_)
  obtain ⟨r, hr, hcr⟩ := Buf.contains hp (b := VG.Proof.MlKem.X86.Decaps.bKey) (by rdecide) (by rdecide) (o := k) (n := 1)
    (show k + 1 ≤ 32 by omega)
  set u₅' : State := { u₅ with mem := u₅.mem.writeW (u₅.ea (at_ .ebp 0)) ((u₅.gpr Reg8.al.reg).setWidth 8) }
  have c₅' : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ u₅' := ⟨c₅.esp, c₅.rd, c₅.wr, c₅.esi, by
    show Frame _ _ (u₅.mem.writeW _ _); rw [e₃]; exact c₅.frame.writeW hr _ hcr⟩
  have c₈ := ((c₅'.only o₆ (by decide) (by decide)).only o₇ (by decide) (by decide)).only o₈ (by decide)
    (by decide)
  have m₅ : u₅.mem = u.mem := by rw [o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have m₈ : u₈.mem = u.mem.writeW (Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey + BitVec.ofNat 64 k) ((u₅.gpr .eax).setWidth 8) := by
    rw [o₈.mem, o₇.mem, o₆.mem]; show u₅.mem.writeW _ _ = _; rw [e₃, m₅]; rfl
  have keepK : ∀ b : Buf, b.arg = 3 → (VG.Proof.MlKem.X86.Decaps.Y L).ok b = true → ∀ i < b.len,
      u.mem (Buf.addr s₀ b + BitVec.ofNat 64 i) = m (Buf.addr s₀ b + BitVec.ofNat 64 i) := fun b hb hok i hi =>
    (h.fr.bytes (R := Buf.rgn s₀ b) (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr
      exact Buf.disj hp hok (c := VG.Proof.MlKem.X86.Decaps.bKey) (by rdecide) (by simp [Lay.sep, hb, VG.Proof.MlKem.X86.Decaps.Y, Lay.awr])) (by
        show b.len ≤ 2 ^ 64; have := Buf.fit hp hok; omega) hi)
  have x₁ : u.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bK L) + BitVec.ofNat 64 k) = m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bK L) + BitVec.ofNat 64 k) :=
    keepK (VG.Proof.MlKem.X86.Decaps.bK L) rfl ok₁ k hk
  have x₂ : u₁.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bKB L) + BitVec.ofNat 64 k) = m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bKB L) + BitVec.ofNat 64 k) := by
    rw [o₁.mem]; exact keepK (VG.Proof.MlKem.X86.Decaps.bKB L) rfl ok₂ k hk
  have ex : u₇.gpr .ecx = BitVec.ofNat 32 (32 - k) := by
    rw [o₇.gpr .ecx (by decide), o₆.gpr .ecx (by decide), show u₅'.gpr .ecx = u₅.gpr .ecx from rfl,
      o₅.gpr .ecx (by decide), o₄.gpr .ecx (by decide), o₃.gpr .ecx (by decide), o₂.gpr .ecx (by decide),
      o₁.gpr .ecx (by decide), h.ecx]
  have ebx₅ : u₅.gpr .ebx = M := by
    rw [o₅.gpr .ebx (by decide), o₄.gpr .ebx (by decide), o₃.gpr .ebx (by decide), o₂.gpr .ebx (by decide),
      o₁.gpr .ebx (by decide), h.ebx]
  have val : (u₅.gpr .eax).setWidth 8 =
      VG.Proof.MlKem.X86.Decaps.selB (M.setWidth 8) (m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bK L) + BitVec.ofNat 64 k)) (m (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bKB L) + BitVec.ofNat 64 k)) := by
    rw [v₅, v₄, v₃, o₄.gpr .edx (by decide), o₃.gpr .edx (by decide), o₃.gpr .ebx (by decide),
      o₂.gpr .ebx (by decide), o₂.gpr .eax (by decide), v₂, v₁, o₁.gpr .ebx (by decide), h.ebx, e₁, e₂, x₁, x₂,
      VG.Proof.MlKem.X86.Decaps.selB]
    simp only [BitVec.setWidth_xor, BitVec.setWidth_and, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide),
      BitVec.setWidth_eq]
    rw [BitVec.xor_comm]
  refine ⟨⟨c₈, ?_, ?_, ?_, by rw [v₈, ex]; exact cnt_next hk, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [m₈]
    exact h.fr.writeW (List.mem_singleton_self _) _ (by
      show (⟨Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey, 32⟩ : Region).Contains _ (8 / 8)
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
  · rw [o₈.gpr .edi (by decide), o₇.gpr .edi (by decide), v₆, show u₅'.gpr .edi = u₅.gpr .edi from rfl,
      o₅.gpr .edi (by decide), o₄.gpr .edi (by decide), o₃.gpr .edi (by decide), o₂.gpr .edi (by decide),
      o₁.gpr .edi (by decide), h.edi, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₈.gpr .ebp (by decide), v₇, o₆.gpr .ebp (by decide), show u₅'.gpr .ebp = u₅.gpr .ebp from rfl, eb,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, add_ofNat_add]
  · rw [o₈.gpr .ebx (by decide), o₇.gpr .ebx (by decide), o₆.gpr .ebx (by decide),
      show u₅'.gpr .ebx = u₅.gpr .ebx from rfl, ebx₅]
  · rw [m₈, VG.WriteBytes.writeW8_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have ne : Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey + BitVec.ofNat 64 j ≠ Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey + BitVec.ofNat 64 k := fun e => by
        have := congrArg BitVec.toNat ((BitVec.add_right_inj _).mp e)
        simp only [BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        omega
      rw [ite_eq_right ne]
      exact h.out j hj
    · rw [ite_eq_left rfl, val]
  · show u₈.zf.map (!·) = _
    rw [z₈, ex]; exact cnt_ne hk (by decide)

/-- `key ← K̄ ^ ((K' ^ K̄) & ebx)`, byte by byte. -/
theorem sel_piece [VG.Proof.MlKem.X86.Decaps.CmpOK L] (hA : ∀ s₀ s, TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s)
    (hQ : ∀ s₀ s s', TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀ → A s₀ s → VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s' → Frame [Buf.rgn s₀ VG.Proof.MlKem.X86.Decaps.bKey] s.mem s'.mem →
      (∀ j < 32, s'.mem (Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey + BitVec.ofNat 64 j) = VG.Proof.MlKem.X86.Decaps.selB ((s.gpr .ebx).setWidth 8)
        (s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bK L) + BitVec.ofNat 64 j)) (s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bKB L) + BitVec.ofNat 64 j))) →
      B s₀ s') :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) A B (selC L) := by
  refine Piece.seq (B := fun s₀ s₁ => ∃ s, A s₀ s ∧ VG.Proof.MlKem.X86.Decaps.SL L s₀ s.mem (s.gpr .ebx) 0 s₁)
    (Piece.taint [.esp, .esi] (fun s₀ s hp ha => ?_) (fun s₀ s₀' s s' hp _ hq ha ha' r hr => ?_) (by taint_decide))
    ?_
  · have h := hA s₀ s hp ha
    have ea : s.ea (at_ .esp 28) = argAddr s₀ 2 := h.argEa (i := 2)
    refine wp_movr' fun s₁ o₁ v₁ => ?_
    have c₁ := h.only o₁ (by decide) (by decide)
    refine wp_movm' (by rw [o₁.rd, o₁.wr, show s₁.ea (at_ .esp 28) = s.ea (at_ .esp 28) by
      simp only [State.ea, at_, o₁.gpr .esp (by decide)], ea]; exact h.argIn hp (by rdecide)) fun s₂ o₂ v₂ => ?_
    have c₂ := c₁.only o₂ (by decide) (by decide)
    refine wp_movi fun s₃ o₃ v₃ => WP.block_nil_iff.mpr ⟨s, ha, ?_⟩
    have c₃ := c₂.only o₃ (by decide) (by decide)
    refine ⟨c₃, by rw [o₃.mem, o₂.mem, o₁.mem]; exact Frame.refl _ _, ?_, ?_, by rw [v₃]; rfl, ?_,
      fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · rw [o₃.gpr .edi (by decide), o₂.gpr .edi (by decide), v₁, h.esi]; simp; rfl
    · rw [o₃.gpr .ebp (by decide), v₂, o₁.mem, show s₁.ea (at_ .esp 28) = s.ea (at_ .esp 28) by
        simp only [State.ea, at_, o₁.gpr .esp (by decide)], ea, h.argw hp (by rdecide)]; simp
    · rw [o₃.gpr .ebx (by decide), o₂.gpr .ebx (by decide), o₁.gpr .ebx (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [(hA _ _ hp ha).esp, (hA _ _ ‹_› ha').esp, hq.E1]
    · rw [(hA _ _ hp ha).esi, (hA _ _ ‹_› ha').esi, hq.sc hp]
  refine Piece.taint [.edi, .ebp, .ecx] (fun s₀ s₁ hp ⟨s, ha, h⟩ => ?_)
    (fun s₀ s₀' s s' hp hp' hq ⟨_, _, h⟩ ⟨_, _, h'⟩ r hr => ?_) (by taint_rfl)
  · refine (wp_count (N := 32) (by decide) (VG.Proof.MlKem.X86.Decaps.SL L s₀ s.mem (s.gpr .ebx)) h fun k hk u h => VG.Proof.MlKem.X86.Decaps.sel_step hp hk h).mono
      fun u h => hQ s₀ s u hp ha h.ctx h.fr fun j hj => h.out j hj
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [h.edi, h'.edi, hq.2.1 3 (by rdecide)]
    · rw [h.ebp, h'.ebp, hq.2.1 2 (by rdecide)]
    · rw [h.ecx, h'.ecx]

end VG.Proof.MlKem.X86.Decaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.DecapsBody`. -/
section

/-!
# ML-KEM on x86 (32-bit): the body of decapsulation

`m'` is decrypted (`DecapsDec.lean`), `ek` copied from `dk` and `G(m' ‖ h)`
hashed (`start_piece`), `c'` computed (`Enc.encrypt_piece`), `K̄ = J(z ‖ c)`
hashed, `c` and `c'` compared and `K'` or `K̄` selected into `key`
(`DecapsCmp.lean`) without branching (`fin_piece`). If every `SampleNTT`
succeeded, K-PKE.Encrypt succeeds with the matrix sampled within one bound on
their iterations (`KPke.kpkeEncrypt_some`); if one failed within
`minIterations`, it fails with that bound (`KPke.kpkeEncrypt_none`) (`post`).
Each parameter set's contract implies `TPre (Y L)` and its public data
(`Proof/MlKem/X86/Decaps.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3Suffix shakeSuffix)

/-- The facts of the layout that decapsulation uses beyond K-PKE. -/
class DecapsOK (L : KemLay) : Prop where
  ekc : ((VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 384 * L.p.k, L.p.ekLen⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).okW ⟨3, L.eEK, L.p.ekLen⟩ &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨0, 384 * L.p.k, L.p.ekLen⟩ ⟨3, L.eEK, L.p.ekLen⟩) = true
  ek4 : 4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ctLen < 2 ^ 32
  aEM : (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bM L) [⟨3, L.eEK, L.p.ekLen⟩] = true
  g : ((VG.Proof.MlKem.X86.Decaps.Y L).okW ⟨3, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).okW ⟨3, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).ok (Enc.bM L (VG.Proof.MlKem.X86.Decaps.Y L).sc) &&
    (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 768 * L.p.k + 32, 32⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).okW (Enc.bKR L (VG.Proof.MlKem.X86.Decaps.Y L).sc) &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨3, L.eST, 200⟩ ⟨3, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).sep (Enc.bM L (VG.Proof.MlKem.X86.Decaps.Y L).sc) ⟨3, L.eST, 200⟩ &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep (Enc.bM L (VG.Proof.MlKem.X86.Decaps.Y L).sc) ⟨3, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eST, 200⟩ &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨3, L.eST, 200⟩ (Enc.bKR L (VG.Proof.MlKem.X86.Decaps.Y L).sc) &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep (Enc.bKR L (VG.Proof.MlKem.X86.Decaps.Y L).sc) ⟨3, L.eWK, 640⟩) = true
  aG : (VG.Proof.MlKem.X86.Decaps.Y L).apart (Enc.bEK L (VG.Proof.MlKem.X86.Decaps.Y L).sc) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, Enc.bKR L (VG.Proof.MlKem.X86.Decaps.Y L).sc] = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).apart (Enc.bM L (VG.Proof.MlKem.X86.Decaps.Y L).sc) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, Enc.bKR L (VG.Proof.MlKem.X86.Decaps.Y L).sc] = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 768 * L.p.k + 32, 32⟩ = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 768 * L.p.k + 64, 32⟩ = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 384 * L.p.k, L.p.ekLen⟩ = true
  j : ((VG.Proof.MlKem.X86.Decaps.Y L).okW ⟨3, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).okW ⟨3, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨0, 768 * L.p.k + 64, 32⟩ &&
    (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨1, 0, L.p.ctLen⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).okW (VG.Proof.MlKem.X86.Decaps.bKB L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨3, L.eST, 200⟩ ⟨3, L.eWK, 640⟩ &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨0, 768 * L.p.k + 64, 32⟩ ⟨3, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨0, 768 * L.p.k + 64, 32⟩ ⟨3, L.eWK, 640⟩ &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eWK, 640⟩ &&
    (VG.Proof.MlKem.X86.Decaps.Y L).sep ⟨3, L.eST, 200⟩ (VG.Proof.MlKem.X86.Decaps.bKB L) && (VG.Proof.MlKem.X86.Decaps.Y L).sep (VG.Proof.MlKem.X86.Decaps.bKB L) ⟨3, L.eWK, 640⟩) = true
  dJ : Enc.safe L (VG.Proof.MlKem.X86.Decaps.Y L) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, VG.Proof.MlKem.X86.Decaps.bKB L] = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Decaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, VG.Proof.MlKem.X86.Decaps.bKB L] = true
  dNil : Enc.safe L (VG.Proof.MlKem.X86.Decaps.Y L) [] = true ∧ (VG.Proof.MlKem.X86.Decaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Decaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [] = true
  dKey : Enc.safe L (VG.Proof.MlKem.X86.Decaps.Y L) [VG.Proof.MlKem.X86.Decaps.bKey] = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Decaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [VG.Proof.MlKem.X86.Decaps.bKey] = true ∧
    (VG.Proof.MlKem.X86.Decaps.Y L).apart (VG.Proof.MlKem.X86.Decaps.bC L) [VG.Proof.MlKem.X86.Decaps.bKey] = true
  acc : (VG.Proof.MlKem.X86.Decaps.Y L).ok ⟨3, L.eACC, 4⟩ = true

variable {L : KemLay}

/-- After `ek` is copied from `dk`. -/
structure G1 (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.DM L s₀ s where
  ekc : bytesAt s.mem (Buf.addr s₀ (Enc.bEK L (VG.Proof.MlKem.X86.Decaps.Y L).sc)) L.p.ekLen = VG.Proof.MlKem.X86.Decaps.ekD L s₀

/-- `m'` decrypted, and the inputs of the re-encryption, then `c`. -/
theorem start_piece [CeOK L] [VG.Proof.MlKem.X86.Decaps.DecOK L] [VG.Proof.MlKem.X86.Decaps.DecapsOK L] (hk : 0 < L.p.k) {Q : State → State → Prop}
    {c : Prog isa} (hc : Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (Enc.Base L (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.I L)) Q c) :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <| .seq (decrypt L) <|
        .seq (copyW 3 ⟨0, 384 * L.p.k, L.p.ekLen⟩ ⟨3, L.eEK, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (hash2 3 L.eST L.eWK 72 6 ⟨3, L.eM, 32⟩ ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eKR, 64⟩) c) := by
  obtain ⟨e₁, e₂, e₃, -⟩ := DecapsOK.ek4 (L := L)
  obtain ⟨g₁, g₂, g₃, -, g₅⟩ := DecapsOK.aG (L := L)
  refine Piece.seq (ldsc_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) (by yd_taint)) ?_
  refine Piece.seq (VG.Proof.MlKem.X86.Decaps.decrypt_piece hk) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.G1 L) (copyW_piece' (Y := VG.Proof.MlKem.X86.Decaps.Y L) 0 (384 * L.p.k) 3 L.eEK (L.p.ekLen / 4) L.p.ekLen e₁ e₂ e₃
    DecapsOK.ekc (by yd_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', by rw [keepBytes hp (N := 0) (by rdecide) DecapsOK.aEM (fr1 fr)]; exact h.m⟩, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨3, L.eEK, L.p.ekLen⟩) L.p.ekLen = _
    rw [post, VG.Proof.MlKem.X86.Decaps.ekD_eq]
    exact VG.Proof.MlKem.X86.Decaps.dk_slice hp h.ctx (by unfold Params.ekLen Params.dkLen; omega) g₅
  refine Piece.seq (hash2_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) L.eST L.eWK 72 6 (Enc.bM L (VG.Proof.MlKem.X86.Decaps.Y L).sc) ⟨0, 768 * L.p.k + 32, 32⟩
    (Enc.bKR L (VG.Proof.MlKem.X86.Decaps.Y L).sc) rate72 DecapsOK.g (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yd_taint)
    (by yd_taint) (by yd_taint) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨h', by rw [keepBytes hp (by rdecide) g₁ fr]; exact h.ekc,
        by rw [keepBytes hp (by rdecide) g₂ fr]; exact h.m, ?_⟩) hc
  rw [out, VG.Proof.MlKem.X86.Decaps.dk_slice hp h.ctx (by unfold Params.dkLen; omega) g₃, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from
    sha3Suffix32, ← padded, ← sha3_512_eq]
  show _ = VG.Proof.MlKem.X86.Decaps.krD L s₀
  rw [VG.Proof.MlKem.X86.Decaps.krD_eq, ← h.m]
  rfl

theorem done_keep {s₀ s s' : State} (hp : TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (VG.Proof.MlKem.X86.Decaps.Y L).stk)
    (hs : Enc.safe L (VG.Proof.MlKem.X86.Decaps.Y L) bs = true)
    (hc : (VG.Proof.MlKem.X86.Decaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Decaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : Enc.Done L (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.I L) s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s') :
    Enc.Done L (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.I L) s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, by rw [keepBytes hp hM hc fr]; exact h.cv⟩

/-- `K̄ = J(z ‖ c)`. -/
abbrev kbar (L : KemLay) (s₀ : State) : List Byte := J (KPke.dkZ L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) ++ VG.Proof.MlKem.X86.Decaps.ct L s₀)

/-- After `K̄` is hashed. -/
structure J1 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.I L) s₀ s where
  kb : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bKB L)) 32 = VG.Proof.MlKem.X86.Decaps.kbar L s₀

/-- After `c` and `c'` are compared. -/
structure J2 (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.J1 L s₀ s where
  ebx : s.gpr .ebx = VG.Proof.MlKem.X86.Decaps.mask (VG.Proof.MlKem.X86.Decaps.ct L s₀ = bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen)

/-- After `K'` or `K̄` is selected into `key`. -/
structure J3 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.I L) s₀ s where
  key : bytesAt s.mem (Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey) 32 =
    if VG.Proof.MlKem.X86.Decaps.ct L s₀ = bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen then (VG.Proof.MlKem.X86.Decaps.krD L s₀).take 32 else VG.Proof.MlKem.X86.Decaps.kbar L s₀

/-- After `eACC` is loaded, to be returned. -/
structure Fin (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Decaps.J3 L s₀ s where
  eax : s.gpr .eax = Enc.accE L (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s

theorem selB_mask (p : Prop) [Decidable p] (a b : Byte) :
    VG.Proof.MlKem.X86.Decaps.selB ((VG.Proof.MlKem.X86.Decaps.mask p).setWidth 8) a b = if p then a else b := by
  unfold VG.Proof.MlKem.X86.Decaps.mask
  split
  · rw [show (BitVec.setWidth 8 (0xffffffff : BitVec 32)) = BitVec.allOnes 8 by decide, VG.Proof.MlKem.X86.Decaps.selB, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rw [show (BitVec.setWidth 8 (0 : BitVec 32)) = 0#8 by decide, VG.Proof.MlKem.X86.Decaps.selB, BitVec.and_zero, BitVec.xor_zero]

/-- The key, from the re-encryption. -/
theorem fin_piece [VG.Proof.MlKem.X86.Decaps.DecOK L] [VG.Proof.MlKem.X86.Decaps.CmpOK L] [VG.Proof.MlKem.X86.Decaps.DecapsOK L] :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (Enc.Done L (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.I L)) (VG.Proof.MlKem.X86.Decaps.Fin L)
      (.seq (hash2 3 L.eST L.eWK 136 0x1f ⟨0, 768 * L.p.k + 64, 32⟩ ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eH, 32⟩) <|
        .seq (cmpC L) <| .seq (selC L) (.block [.mov .eax (.mem (at_ .esi L.eACC))])) := by
  obtain ⟨-, -, -, g₄, -⟩ := DecapsOK.aG (L := L)
  obtain ⟨-, -, -, hN⟩ := DecapsOK.ek4 (L := L)
  obtain ⟨d₁, d₂⟩ := DecapsOK.dJ (L := L)
  obtain ⟨n₁, n₂⟩ := DecapsOK.dNil (L := L)
  obtain ⟨k₁, k₂, k₃⟩ := DecapsOK.dKey (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.J1 L) (hash2_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) L.eST L.eWK 136 0x1f ⟨0, 768 * L.p.k + 64, 32⟩
    ⟨1, 0, L.p.ctLen⟩ (VG.Proof.MlKem.X86.Decaps.bKB L) rate136 DecapsOK.j (by rdecide) (by rdecide) hN (by rdecide) (by taint_rfl) (by yd_taint)
    (by yd_taint) (by yd_taint) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨VG.Proof.MlKem.X86.Decaps.done_keep hp (by rdecide) d₁ d₂ fr h h', ?_⟩) ?_
  · rw [out, VG.Proof.MlKem.X86.Decaps.dk_slice hp h.ctx (by unfold Params.dkLen; omega) g₄, VG.Proof.MlKem.X86.Decaps.ct_slice hp h.ctx (by omega) DecOK.ct.1,
      List.drop_zero, List.take_of_length_le (l := VG.Proof.MlKem.X86.Decaps.ct L s₀) (by rw [VG.Proof.MlKem.X86.Decaps.ct_eq, bytesAt_length]),
      show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32, ← padded, ← J_eq]
    show _ = J (KPke.dkZ L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) ++ VG.Proof.MlKem.X86.Decaps.ct L s₀)
    rfl
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.J2 L) (VG.Proof.MlKem.X86.Decaps.cmp_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' e =>
    ⟨⟨VG.Proof.MlKem.X86.Decaps.done_keep hp (bs := []) (M := 0) (by rdecide) n₁ n₂ (m' ▸ Frame.refl _ _) h.toDone h',
      by rw [m']; exact h.kb⟩, by rw [e, m']⟩) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.Decaps.J3 L) (VG.Proof.MlKem.X86.Decaps.sel_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
    ⟨VG.Proof.MlKem.X86.Decaps.done_keep hp (M := 0) (by rdecide) k₁ k₂ (fr1 fr) h.toDone h', ?_⟩) ?_
  · have kc : bytesAt s'.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen = bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen :=
      keepBytes hp (N := 0) (by rdecide) k₃ (fr1 fr)
    have lk : (VG.Proof.MlKem.X86.Decaps.krD L s₀).length = 64 := by rw [show VG.Proof.MlKem.X86.Decaps.krD L s₀ = (VG.Proof.MlKem.X86.Decaps.I L).kr s₀ from rfl, ← h.kr, bytesAt_length]
    have lj : (VG.Proof.MlKem.X86.Decaps.kbar L s₀).length = 32 := J_length _
    rw [kc]
    refine bytesAt_eq (by split <;> simp [lk, lj]) fun j hj => ?_
    rw [out j hj, h.ebx, VG.Proof.MlKem.X86.Decaps.selB_mask]
    have kk : (VG.Proof.MlKem.X86.Decaps.krD L s₀).take 32 = bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bK L)) 32 := by
      rw [show VG.Proof.MlKem.X86.Decaps.krD L s₀ = (VG.Proof.MlKem.X86.Decaps.I L).kr s₀ from rfl, ← h.kr, bytesAt_take _ _ (show 32 ≤ 64 by decide)]; rfl
    split
    · simp only [kk, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
    · simp only [← h.kb, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
  exact ld32_piece (Y := VG.Proof.MlKem.X86.Decaps.Y L) L.eACC DecapsOK.acc (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨⟨VG.Proof.MlKem.X86.Decaps.done_keep hp (bs := []) (M := 0) (by rdecide) n₁ n₂
      (m' ▸ Frame.refl _ _) h.toDone h', by rw [m']; exact h.key⟩,
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']⟩

theorem body_piece [CeOK L] [VG.Proof.MlKem.X86.Decaps.DecOK L] [VG.Proof.MlKem.X86.Decaps.CmpOK L] [VG.Proof.MlKem.X86.Decaps.DecapsOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L]
    [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (fun s₀ s => s = P0 s₀) (VG.Proof.MlKem.X86.Decaps.Fin L) (decapsBody L) :=
  VG.Proof.MlKem.X86.Decaps.start_piece hk <| .seq (Enc.encrypt_piece (VG.Proof.MlKem.X86.Decaps.hS L) (VG.Proof.MlKem.X86.Decaps.hρ L) hk) VG.Proof.MlKem.X86.Decaps.fin_piece

theorem piece [CeOK L] [VG.Proof.MlKem.X86.Decaps.DecOK L] [VG.Proof.MlKem.X86.Decaps.CmpOK L] [VG.Proof.MlKem.X86.Decaps.DecapsOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L]
    [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) (hsp : NoSp (decapsBody L)) :
    Piece (TPre (VG.Proof.MlKem.X86.Decaps.Y L)) (TPub (VG.Proof.MlKem.X86.Decaps.Y L) (VG.Proof.MlKem.X86.Decaps.lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem.X86.Decaps.Fin L s₀) s₀ s')
      (leaf (decapsBody L)) :=
  topLeaf hsp ((VG.Proof.MlKem.X86.Decaps.body_piece hk).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- The postcondition, from the final state of the body. -/
theorem post [Enc.VOK L] (hη : L.p.η₁ = 2 ∧ L.p.η₂ = 2) {s₀ s : State} (hp : TPre (VG.Proof.MlKem.X86.Decaps.Y L) s₀) (h : VG.Proof.MlKem.X86.Decaps.Fin L s₀ s) :
    Outcome (fun iters => decapsInternal L.p iters (VG.Proof.MlKem.X86.Decaps.dk L s₀) (VG.Proof.MlKem.X86.Decaps.ct L s₀)) (Enc.accE L (VG.Proof.MlKem.X86.Decaps.Y L) s₀ s)
      (bytesAt s.mem (Buf.addr s₀ VG.Proof.MlKem.X86.Decaps.bKey) 32) := by
  have er : Enc.rE (VG.Proof.MlKem.X86.Decaps.I L) s₀ = (G (KPke.decM L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) (VG.Proof.MlKem.X86.Decaps.ct L s₀) ++ KPke.dkH L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀))).2 := by
    show (VG.Proof.MlKem.X86.Decaps.krD L s₀).drop 32 = _; rw [VG.Proof.MlKem.X86.Decaps.krD_eq, VG.Proof.MlKem.X86.Decaps.mD_eq]; rfl
  have ek : Enc.ρE L (VG.Proof.MlKem.X86.Decaps.I L) s₀ = ekRho L.p (KPke.dkEk L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀)) := by
    show ekRho L.p (VG.Proof.MlKem.X86.Decaps.ekD L s₀) = _; rw [VG.Proof.MlKem.X86.Decaps.ekD_eq]
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; omega
    refine .inr ⟨e, ?_⟩
    show decapsInternal L.p minIterations (VG.Proof.MlKem.X86.Decaps.dk L s₀) (VG.Proof.MlKem.X86.Decaps.ct L s₀) = none
    rw [Enc.mSE, ek] at hn
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (i := k % L.p.k) (j := k / L.p.k) (Nat.mod_lt _ hk0)
      (Nat.div_lt_of_lt_mul hk) hn]
    rfl
  · obtain ⟨M, hM⟩ := Enc.samples h.toDone e
    rw [ek] at hM
    refine .inl ⟨e, M, ?_⟩
    show decapsInternal L.p M (VG.Proof.MlKem.X86.Decaps.dk L s₀) (VG.Proof.MlKem.X86.Decaps.ct L s₀) = _
    have ec : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Decaps.bC L)) L.p.ctLen =
        KPke.ct L.p (Enc.aE L (VG.Proof.MlKem.X86.Decaps.I L) s₀) ((VG.Proof.MlKem.X86.Decaps.I L).ek s₀) ((VG.Proof.MlKem.X86.Decaps.I L).m s₀) (Enc.rE (VG.Proof.MlKem.X86.Decaps.I L) s₀) :=
      Enc.ct_eq (VG.Proof.MlKem.X86.Decaps.hS L) hp h.toDone e
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some hη hM, h.key, ec, er,
      show Enc.aE L (VG.Proof.MlKem.X86.Decaps.I L) s₀ = fun i j => sv (matSeed (ekRho L.p (KPke.dkEk L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀))) i j) by rw [← ek],
      show (VG.Proof.MlKem.X86.Decaps.I L).ek s₀ = KPke.dkEk L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) from VG.Proof.MlKem.X86.Decaps.ekD_eq L s₀,
      show (VG.Proof.MlKem.X86.Decaps.I L).m s₀ = KPke.decM L.p (VG.Proof.MlKem.X86.Decaps.dk L s₀) (VG.Proof.MlKem.X86.Decaps.ct L s₀) from VG.Proof.MlKem.X86.Decaps.mD_eq L s₀, VG.Proof.MlKem.X86.Decaps.krD_eq, VG.Proof.MlKem.X86.Decaps.mD_eq]
    rfl

end VG.Proof.MlKem.X86.Decaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.EncInst`. -/
section

/-!
# ML-KEM-768 on x86 (32-bit): the layout of K-PKE.Encrypt

The facts of the layout of `scratch` that the proof of `encrypt`
(`Enc*.lean`) uses, for ML-KEM-768 (`L768`), computed from its offsets.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86.Top

instance : BaseOK L768 where
  n hS := by sc_decide
  rn hS := by sc_decide
  hash hS := by sc_decide

instance : VG.Proof.MlKem.X86.Enc.YOK L768 where
  y hS := by sc_decide
  acc hS := by sc_decide

instance : VG.Proof.MlKem.X86.Enc.EntOK L768 where
  seed hS := by sc_decide
  ent hS := by sc_decide'
  mul hS := by sc_decide'

instance : VG.Proof.MlKem.X86.Enc.RowOK L768 where
  row hS := by sc_decide'

instance : VG.Proof.MlKem.X86.Enc.VOK L768 where
  v hS := by sc_decide'
  w hS := by sc_decide'
  ct hS := by sc_decide

end VG.Proof.MlKem.X86.Enc

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Decaps`. -/
section

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_decaps`

Decapsulation (`DecapsBody.lean`) for ML-KEM-768 (`L768`): the facts of its
layout (`DecOK`, `CmpOK`, `DecapsOK`), computed from its offsets; the
contract's precondition implies `TPre (Y L768)` (`pre_of`) and its public data
`TPub` (`pub_of`).
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

instance : VG.Proof.MlKem.X86.Decaps.DecOK L768 where
  ct := by decide
  dec := by decide
  keep := by decide
  mul := by decide
  v := by decide

instance : VG.Proof.MlKem.X86.Decaps.CmpOK L768 where
  ct := by decide
  sel := by decide

instance : VG.Proof.MlKem.X86.Decaps.DecapsOK L768 where
  ekc := by decide
  ek4 := by decide
  aEM := by decide
  g := by decide
  aG := by decide
  j := by decide
  dJ := by simp only [Enc.safe, Enc.safeS]; decide
  dNil := by simp only [Enc.safe, Enc.safeS]; decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by decide

theorem pre_of {s₀ : State} (h : (decapsContract X86.abi 88).pre s₀) : TPre (VG.Proof.MlKem.X86.Decaps.Y L768) s₀ := by
  sig_pre [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -, h19, h20, h21, h22, h23,
    h24, h25, h26, h27⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h19 h20 h21 h22 h23
  have c4 : ∀ i, i < (VG.Proof.MlKem.X86.Decaps.Y L768).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := fun i hi => by
    simp only [VG.Proof.MlKem.X86.Decaps.Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by decide, by simp only [VG.Proof.MlKem.X86.Decaps.Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h23, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c4 i hi with rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlKem.X86.Decaps.Y, L768, Params.dkLen, Params.ctLen, mlKem768]
  · rw [h4]; simp [gR, Lay.n, VG.Proof.MlKem.X86.Decaps.Y]
  · intro i hi j hj hne hw
    rcases c4 i hi with rfl | rfl | rfl | rfl <;> rcases c4 j hj with rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6,
      absurd hw (by decide), absurd rfl hne, h8, h9,
      h5.symm, h8.symm, absurd rfl hne, h11,
      h6.symm, h9.symm, h11.symm, absurd rfl hne]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h7.symm, h10.symm, h12.symm, h13.symm]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h14, h15, h16, h17]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22]
  · intro i hi
    rcases c4 i hi with rfl | rfl | rfl | rfl
    exacts [h24, h25, h26, h27]

theorem pub_of {s₀ s₀' : State} (h : (decapsContract X86.abi 88).pub s₀ s₀') : TPub (VG.Proof.MlKem.X86.Decaps.Y L768) (VG.Proof.MlKem.X86.Decaps.lk L768) s₀ s₀' := by
  sig_pub [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [VG.Proof.MlKem.X86.Decaps.Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    exacts [e₃, e₄, e₅, e₆]
  · have e := map_toNat_inj e₂
    show dkRho L768.p (VG.Proof.MlKem.X86.Decaps.dk L768 s₀) = dkRho L768.p (VG.Proof.MlKem.X86.Decaps.dk L768 s₀')
    rw [VG.Proof.MlKem.X86.Decaps.dk_eq, VG.Proof.MlKem.X86.Decaps.dk_eq, VG.Proof.MlKem.X86.Decaps.addr0, VG.Proof.MlKem.X86.Decaps.addr0]
    exact e

/-- Memory with the arguments `0`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x10 else if a = 0x500d then 0x20 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.decaps (decapsContract X86.abi 88) := by
  refine Piece.verified (((VG.Proof.MlKem.X86.Decaps.piece (L := L768) (by decide) (NoSp.of_all (by decide +kernel))).pre_mono (fun _ h => VG.Proof.MlKem.X86.Decaps.pre_of h) fun _ _ _ _ h => VG.Proof.MlKem.X86.Decaps.pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := VG.Proof.MlKem.X86.Decaps.pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := VG.Proof.MlKem.X86.Decaps.post (by decide) hp hfin
    rw [VG.Proof.MlKem.X86.Decaps.dk_eq, VG.Proof.MlKem.X86.Decaps.ct_eq, VG.Proof.MlKem.X86.Decaps.addr0, VG.Proof.MlKem.X86.Decaps.addr0, VG.Proof.MlKem.X86.Decaps.addr0] at r
    exact r
  · let st := VG.Proof.MlKem.X86.satState VG.Proof.MlKem.X86.Decaps.satMem [⟨0, 2400⟩, ⟨0x1000, 1088⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.Decaps

end
