module

import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Samp
import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.Prim
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.MlDsa.DecideAt
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.MlKem.X86.Pack
import VerifiedGarbage.Proof.MlKem.X86.Table
public import VerifiedGarbage.Proof.MlDsa.X86.Verify.Base
import VerifiedGarbage.Proof.MlDsa.X86.Verify.Local
import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody

/-! ### `MlDsa.X86.Verify.Hint`, which this module and modules that import it used -/

section

/-!
# ML-DSA verification on x86 (32-bit): the hint and `z`

The pieces of the signature and of the public key are the bytes of their
arguments (`sig_slice`, `pk_slice`), which no piece writes. `HintBitUnpack`
gives the result: 1 with the hint stored (`HOk`), or 0 if it is malformed
(`hint_piece`); then each `z[i]` is unpacked and the result ANDed with
`‖z[i]‖∞ < γ₁ - β` (`zOne_piece`, `ZI`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly toRq normRq)
open VG.Proof.MlDsa (PolyIs Reduced polyAt HintIs)
open VG.Proof.MlDsa.Verify (vZ vHint)
open VG.Spec.Sha3 (bytesAt)

theorem accB_YV (p : Params) : accB (YV p) = sb oACC 4 := rfl

/-! ## The inputs -/

section
variable {p : Params} (hF : VFacts p) {s₀ s : State} (hp : TPre (YV p) s₀) (h : Ctx (YV p) s₀ s)
include hF hp h

theorem sig_slice {o l : Nat} (hok : (YV p).ok ⟨2, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, o, l⟩) l = ((vSig p s₀).drop o).take l := by
  obtain ⟨-, -, hl⟩ := Lay.ok_iff.mp hok
  have e := bytes_sub hp s₀.mem (a := 2) (o := 0) (k := o) (c := l) (L := p.sigLen) hl (by lvd)
    (by rw [Nat.zero_add]; exact hok)
  rw [Nat.zero_add] at e
  exact (h.roBytes hp hok rfl).trans e

theorem pk_slice {o l : Nat} (hok : (YV p).ok ⟨0, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((vPk p s₀).drop o).take l := by
  obtain ⟨-, -, hl⟩ := Lay.ok_iff.mp hok
  have e := bytes_sub hp s₀.mem (a := 0) (o := 0) (k := o) (c := l) (L := p.pkLen) hl (by lvd)
    (by rw [Nat.zero_add]; exact hok)
  rw [Nat.zero_add] at e
  exact (h.roBytes hp hok rfl).trans e

end

/-! ## The hint -/

section
variable (p : Params) (s₀ : State)

/-- The hint of the signature, or `⊥`. -/
abbrev hOf : Option (List (Vector Bool Spec.MlDsa.n)) := vHint p (vSig p s₀)

/-- The hint, well formed and stored. -/
def HOk (s : State) : Prop := ∃ h, hOf p s₀ = some h ∧ HintIs s.mem (Buf.addr s₀ (hB p.k)) p.k h

/-- After `HintBitUnpack`: the result 1 and the hint stored, or 0 if it is malformed. -/
def H1 (s : State) : Prop :=
  Ctx (YV p) s₀ s ∧ ((accV s₀ s = 1 ∧ HOk p s₀ s) ∨ (accV s₀ s = 0 ∧ hOf p s₀ = none))

/-- The postcondition, at the end. -/
def VFin (s : State) : Prop :=
  Ctx (YV p) s₀ s ∧ ((accV s₀ s = 1 ∧ ∃ b, Spec.MlDsa.verifyMu p b (vPk p s₀) (vMu s₀) (vSig p s₀) = some true) ∨
    (accV s₀ s = 0 ∧ Spec.MlDsa.verifyMu p Spec.MlDsa.minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true))

end

theorem keepHint {p : Params} {s₀ : State} (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat} (hN : N + 16 ≤ 96)
    (hs : (YV p).apart (hB p.k) bs = true) {m m' : Mem} (fr : Frame (FR s₀ bs N) m m')
    {h : List (Vector Bool Spec.MlDsa.n)} (hh : HintIs m (Buf.addr s₀ (hB p.k)) p.k h) :
    HintIs m' (Buf.addr s₀ (hB p.k)) p.k h :=
  Proof.MlDsa.Verify.hintIs_congr (fun i hi => Top.keep hp (stkV hN) hs fr i (by show i < 256 * p.k * 4; omega_using [hi])) hh

theorem HOk.keep {p : Params} {s₀ s s' : State} (h : HOk p s₀ s) (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : (YV p).apart (hB p.k) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    HOk p s₀ s' := by
  obtain ⟨hh, e, hi⟩ := h
  exact ⟨hh, e, keepHint hp hN hs fr hi⟩

theorem acc_keepV {p : Params} {s₀ s s' : State} (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (hs : (YV p).apart (sb oACC 4) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem) :
    accV s₀ s' = accV s₀ s :=
  keepW hp (stkV hN) hs fr

theorem acc_write {p : Params} {s₀ : State} (m : Mem) (v : BitVec 32) :
    (m.writeW (Buf.addr s₀ (accB (YV p))) v).readW (Buf.addr s₀ (sb oACC 4)) 32 = v :=
  Mem.readW_writeW_self32 _ _ _

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem hint_piece : VP p (Ctx (YV p)) (H1 p) (hint P p) := by
  unfold hint
  refine Piece.seq (B := fun s₀ s => Ctx (YV p) s₀ s ∧ ((s.gpr .eax = 1 ∧ HOk p s₀ s) ∨
      (s.gpr .eax = 0 ∧ hOf p s₀ = none)))
    (hu_piece hP.hintUnpack 2 (oHint p) p.ω p.k vS (oP 0) hF.hint (by lvd) (Nat.le_of_eq (YV_stk p).symm)
      (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h)
      (fun s₀ s₀' s s' hp hp' hq h h' => by
        rw [sig_slice hF hp h (by lvd), sig_slice hF hp' h' (by lvd), (inputs_pub hq).2.2])
      fun s₀ s s' hp h h' fr post => ⟨h', ?_⟩) ?_
  · rw [sig_slice hF hp h (by lvd)] at post
    change (match vHint p (vSig p s₀) with
      | some hint => s'.gpr .eax = 1 ∧ HintIs s'.mem (Buf.addr s₀ (hB p.k)) p.k hint
      | none => s'.gpr .eax = 0) at post
    cases e : vHint p (vSig p s₀) with
    | none => rw [e] at post; exact .inr ⟨post, e⟩
    | some hh => rw [e] at post; exact .inl ⟨post.1, hh, e, post.2⟩
  refine stAcc_piece (Y := YV p) (by lvd) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1)
    fun s₀ s s' hp h h' g m' => ⟨h', ?_⟩
  have ea : accV s₀ s' = s.gpr .eax := by rw [accV, m', acc_write]
  have fr : Frame (FR s₀ [sb oACC 4] 0) s.mem s'.mem := by rw [m']; exact frW32 (Y := YV p)
  rcases h.2 with ⟨e, ho⟩ | ⟨e, hn⟩
  · exact .inl ⟨by rw [ea, e], ho.keep hp (N := 0) (by omega_using []) (by lvd) fr⟩
  · exact .inr ⟨by rw [ea, e], hn⟩

end

/-! ## `z` -/

section
variable (p : Params) (s₀ : State)

/-- The first `i` norms of `z` are within the bound. -/
abbrev NormsOk (i : Nat) : Prop := ∀ j < i, normRq [toRq (vZ p (vSig p s₀) j)] < p.γ₁ - p.β

/-- After the first `i` entries of `z`. -/
structure ZI (i : Nat) (s : State) : Prop where
  ctx : Ctx (YV p) s₀ s
  hint : HOk p s₀ s
  z : ∀ j < i, PolyIs s.mem (Buf.addr s₀ (pZ j)) (toRq (vZ p (vSig p s₀) j))
  acc : accV s₀ s = if NormsOk p s₀ i then 1 else 0

end

theorem ZI.keep {p : Params} {i : Nat} {s₀ s s' : State} (h : ZI p s₀ i s) (hp : TPre (YV p) s₀) {bs : List Buf}
    {N : Nat} (hN : N + 16 ≤ 96) (sh : (YV p).apart (hB p.k) bs = true) (sa : (YV p).apart (sb oACC 4) bs = true)
    (sz : ∀ j < i, (YV p).apart (pZ j) bs = true) (fr : Frame (FR s₀ bs N) s.mem s'.mem)
    (h' : Ctx (YV p) s₀ s') : ZI p s₀ i s' :=
  ⟨h', h.hint.keep hp hN sh fr, fun j hj => keepPolyD hp (stkV hN) (sz j hj) fr (h.z j hj),
    by rw [acc_keepV hp hN sa fr]; exact h.acc⟩

theorem ite_and_ite {P Q : Prop} [Decidable P] [Decidable Q] :
    ((if P then 1 else 0 : BitVec 32) &&& (if Q then 1 else 0)) = if P ∧ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

theorem normsOk_succ {p : Params} {s₀ : State} {i : Nat} :
    (NormsOk p s₀ i ∧ normRq [toRq (vZ p (vSig p s₀) i)] < p.γ₁ - p.β) ↔ NormsOk p s₀ (i + 1) := by
  constructor
  · rintro ⟨h₁, h₂⟩ j hj
    rcases (by omega_using [hj] : j < i ∨ j = i) with hj | rfl
    exacts [h₁ j hj, h₂]
  · intro h
    exact ⟨fun j hj => h j (by omega_using [hj]), h i (by omega_using [])⟩

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem zOne_piece {i : Nat} (hi : i < p.ℓ) : VP p (ZI p · i) (ZI p · (i + 1)) (zOne P p i) := by
  have hzr := mul_row (a := lenZ p) hi
  unfold zOne
  refine Piece.seq (B := fun s₀ s => ZI p s₀ i s ∧ PolyIs s.mem (Buf.addr s₀ (pZ i)) (toRq (vZ p (vSig p s₀) i)))
    (bu_piece hP.bitUnpack 2 (p.ctildeLen + lenZ p * i) (lenZ p) (p.γ₁ - 1) p.γ₁ vS (oP (8 + i)) hF.bp.1 hF.bp.2
      (by lvd) (Nat.le_of_eq (YV_stk p).symm) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.ctx)
      fun s₀ s s' hp h h' fr post => ⟨h.keep hp (N := 80) (by omega_using []) (by lvd) (by lvd)
        (fun j hj => by lvd) fr h', ?_⟩) ?_
  · rw [sig_slice hF hp h.ctx (by lvd)] at post
    exact post
  refine Piece.seq (B := fun s₀ s => (ZI p s₀ i s ∧ PolyIs s.mem (Buf.addr s₀ (pZ i)) (toRq (vZ p (vSig p s₀) i))) ∧
      s.gpr .eax = if normRq [toRq (vZ p (vSig p s₀) i)] < p.γ₁ - p.β then 1 else 0)
    (normLt_piece hP.normLt vS (oP (8 + i)) (p.γ₁ - p.β) hF.beta.2 (by lvd) (Nat.le_of_eq (YV_stk p).symm)
      (ht := .block []) (by kernel_rfl) (fun _ _ _ h => ⟨h.1.ctx, h.2.1⟩)
      fun s₀ s s' hp h h' fr e => ⟨⟨h.1.keep hp (N := 80) (by omega_using []) (by lvd) (by lvd)
        (fun j hj => by lvd) fr h', keepPolyD hp (stkV (by omega_using [])) (by lvd) fr h.2⟩, ?_⟩) ?_
  · rw [e, h.2.2]
  refine accAnd_piece (Y := YV p) (by lvd) (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.1.ctx)
    fun s₀ s s' hp h h' m' => ?_
  have fr : Frame (FR s₀ [sb oACC 4] 0) s.mem s'.mem := by rw [m']; exact frW32 (Y := YV p)
  obtain ⟨⟨hz, hzi⟩, he⟩ := h
  refine ⟨h', hz.hint.keep hp (N := 0) (by omega_using []) (by lvd) fr, fun j hj => ?_, ?_⟩
  · rcases (by omega_using [hj] : j < i ∨ j = i) with hj | rfl
    · have : (YV p).apart (pZ j) [sb oACC 4] = true := by lvd
      exact keepPolyD hp (stkV (by omega_using [])) this fr (hz.z j hj)
    · have : (YV p).apart (pZ j) [sb oACC 4] = true := by lvd
      exact keepPolyD hp (stkV (by omega_using [])) this fr hzi
  · rw [accV, m', acc_write, accB_YV, ← accV, hz.acc, he, ite_and_ite]
    exact ite_congr (propext normsOk_succ) (fun _ => rfl) (fun _ => rfl)

end

end VG.Proof.MlDsa.X86.Verify

end

end

/-!
# ML-DSA verification on x86 (32-bit): the samplers

Once the hint is well formed and the norms of `z` within the bound (`VB`), `ρ`
is copied to the seed, and each entry `e = 8r + s` of `Â` sampled from `ρ ‖ s
‖ r` (`aOne_piece`), the sampler's result ANDed into the result and the
polynomial masked with it, as in key generation; then `c` from `c̃`
(`samples_piece`). The result is 1 if the samplers' outputs are those of the
standard for some bounds, and 0 if verification is not true within the least
bounds (`GA`, `GC`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86.Verify

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top VG.Proof.MlDsa.X86.KeyGen
open VG.Impl.MlDsa.X86.Verify
open VG.Spec.MlDsa (Params Poly IPoly Bounds minBounds rejNTTPoly sampleInBall toRq)
open VG.Proof.MlDsa (PolyIs Reduced polyAt)
open VG.Proof.MlDsa.Verify (vZ vHint vRho vCt aSeed)
open VG.Spec.Sha3 (bytesAt)

section
variable (p : Params) (s₀ : State)

/-- After `z`: the hint and `z` stored, and the norms of `z` within the bound. -/
structure VB (s : State) : Prop where
  ctx : Ctx (YV p) s₀ s
  hint : HOk p s₀ s
  z : ∀ j < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pZ j)) (toRq (vZ p (vSig p s₀) j))
  norms : NormsOk p s₀ p.ℓ

/-- Verification is not true within the least bounds. -/
abbrev VFail : Prop := Spec.MlDsa.verifyMu p minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true

/-- The entries `(r, s)` of `Â` before `e = 8r + s`. -/
abbrev Before (e r s : Nat) : Prop := s < p.ℓ ∧ 8 * r + s < e

/-- The result after the entries of `Â` before `e`, those of `A`. -/
def GA (e : Nat) (A : Nat → Nat → Poly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ b : Bounds, ∀ r s, Before p e r s → rejNTTPoly b.rejNTT (aSeed (vPk p s₀) r s) = some (A r s)) ∨
    (v = 0 ∧ VFail p s₀)

/-- After the entries of `Â` before `e`. -/
structure SA (e : Nat) (s : State) : Prop where
  vb : VB p s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (sb oSB 32)) 32 = vRho (vPk p s₀)
  ex : ∃ A : Nat → Nat → Poly, (∀ r s', Before p e r s' → PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')) ∧
    GA p s₀ e A (accV s₀ s)

/-- The result after `Â` and `c`, those of `A` and `C`. -/
def GC (A : Nat → Nat → Poly) (C : Poly) (v : BitVec 32) : Prop :=
  (v = 1 ∧ ∃ (b : Bounds) (c : IPoly), (∀ r < p.k, ∀ s < p.ℓ,
      rejNTTPoly b.rejNTT (aSeed (vPk p s₀) r s) = some (A r s)) ∧
      sampleInBall p.τ b.ball (vCt p (vSig p s₀)) = some c ∧ toRq c = C) ∨
    (v = 0 ∧ VFail p s₀)

/-- After `Â` and `c`. -/
structure SC (s : State) : Prop where
  vb : VB p s₀ s
  ex : ∃ (A : Nat → Nat → Poly) (C : Poly), (∀ r < p.k, ∀ s' < p.ℓ, PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')) ∧
    PolyIs s.mem (Buf.addr s₀ pC) C ∧ GC p s₀ A C (accV s₀ s)

end

/-! ## Keeping the facts -/

theorem VB.keep {p : Params} {s₀ s s' : State} (h : VB p s₀ s) (hp : TPre (YV p) s₀) {bs : List Buf} {N : Nat}
    (hN : N + 16 ≤ 96) (sh : (YV p).apart (hB p.k) bs = true) (sz : ∀ j < p.ℓ, (YV p).apart (pZ j) bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YV p) s₀ s') : VB p s₀ s' :=
  ⟨h', h.hint.keep hp hN sh fr, fun j hj => keepPolyD hp (stkV hN) (sz j hj) fr (h.z j hj), h.norms⟩

theorem SA.keep {p : Params} {e : Nat} {s₀ s s' : State} (h : SA p s₀ e s) (hp : TPre (YV p) s₀) {bs : List Buf}
    {N : Nat} (hN : N + 16 ≤ 96) (sh : (YV p).apart (hB p.k) bs = true)
    (sz : ∀ j < p.ℓ, (YV p).apart (pZ j) bs = true) (sr : (YV p).apart (sb oSB 32) bs = true)
    (sa : (YV p).apart (sb oACC 4) bs = true) (sA : ∀ r s, Before p e r s → (YV p).apart (pA r s) bs = true)
    (fr : Frame (FR s₀ bs N) s.mem s'.mem) (h' : Ctx (YV p) s₀ s') : SA p s₀ e s' := by
  obtain ⟨A, hA, hG⟩ := h.ex
  refine ⟨h.vb.keep hp hN sh sz fr h', by rw [keepBytes hp (stkV hN) sr fr]; exact h.rho,
    A, fun r s hb => keepPolyD hp (stkV hN) (sA r s hb) fr (hA r s hb), ?_⟩
  rw [acc_keepV hp hN sa fr]; exact hG

theorem SA.congr {p : Params} {e e' : Nat} {s₀ s : State} (h : SA p s₀ e s)
    (he : ∀ r s, s < p.ℓ → (8 * r + s < e ↔ 8 * r + s < e')) : SA p s₀ e' s := by
  obtain ⟨A, hA, hG⟩ := h.ex
  refine ⟨h.vb, h.rho, A, fun r s hb => hA r s ⟨hb.1, (he r s hb.1).mpr hb.2⟩, ?_⟩
  rcases hG with ⟨h1, b, hb⟩ | h0
  · exact .inl ⟨h1, b, fun r s hb' => hb r s ⟨hb'.1, (he r s hb'.1).mpr hb'.2⟩⟩
  · exact .inr h0

/-! ## An entry of `Â` -/

theorem aSeed_eq (pk : List Byte) (r s : Nat) :
    aSeed pk r s = vRho pk ++ ([BitVec.ofNat 8 s] ++ [BitVec.ofNat 8 r]) := by
  simp only [aSeed, Proof.MlDsa.KeyGen.integerToBytes_one, List.append_assoc]

theorem pA_eq (e : Nat) : pA (e / 8) (e % 8) = pB (20 + e) := by
  show pB (20 + 8 * (e / 8) + e % 8) = pB (20 + e)
  rw [show 20 + 8 * (e / 8) + e % 8 = 20 + e by omega_using []]

section
variable (p : Params)

/-- After the first byte of the seed of entry `e`. -/
abbrev SA1 (e : Nat) (s₀ s : State) : Prop :=
  SA p s₀ e s ∧ bytesAt s.mem (Buf.addr s₀ (sb (oSB + 32) 1)) 1 = [BitVec.ofNat 8 (e % 8)]

/-- With the seed of entry `e`. -/
abbrev SA2 (e : Nat) (s₀ s : State) : Prop :=
  SA p s₀ e s ∧ bytesAt s.mem (Buf.addr s₀ (sb oSB 34)) 34 = aSeed (vPk p s₀) (e / 8) (e % 8)

/-- After `RejNTTPoly` for entry `e`. -/
structure SA3 (e : Nat) (s₀ s : State) : Prop where
  vb : VB p s₀ s
  rho : bytesAt s.mem (Buf.addr s₀ (sb oSB 32)) 32 = vRho (vPk p s₀)
  ex : ∃ A : Nat → Nat → Poly, (∀ r s', Before p e r s' → PolyIs s.mem (Buf.addr s₀ (pA r s')) (A r s')) ∧
    GA p s₀ e A (accV s₀ s)
  red : s.gpr .eax = 1 → Reduced s.mem (Buf.addr s₀ (pB (20 + e)))
  out : Spec.MlDsa.Outcome (fun b => rejNTTPoly b.rejNTT (aSeed (vPk p s₀) (e / 8) (e % 8))) (s.gpr .eax)
    (polyAt s.mem (Buf.addr s₀ (pB (20 + e))))

end

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p) {e : Nat} (he : e < 8 * p.k)
  (hel : e % 8 < p.ℓ)
include hF he

theorem sa_st1 : VP p (SA p · e) (SA1 p e) (.block (st8 (oSB + 32) (e % 8))) :=
  st8_piece (Y := YV p) (oSB + 32) (e % 8) (by lvd) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.vb.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hp (N := 0) (by omega_using []) (by lvd) (fun j hj => by lvd) (by lvd) (by lvd)
        (fun r s hb => by have := hb.1; have := hb.2; lv hF) (m' ▸ frW8 (Y := YV p)) h',
        by rw [m']; exact st8_bytes _ _ _ _ _⟩

theorem sa_st2 : VP p (SA1 p e) (SA2 p e) (.block (st8 (oSB + 33) (e / 8))) :=
  st8_piece (Y := YV p) (oSB + 33) (e / 8) (by lvd) (ht := .block []) (by kernel_rfl)
    (fun _ _ _ h => h.1.vb.ctx) fun s₀ s s' hp h h' m' => by
      have fr : Frame (FR s₀ [sb (oSB + 33) 1] 0) s.mem s'.mem := m' ▸ frW8 (Y := YV p)
      refine ⟨h.1.keep hp (N := 0) (by omega_using []) (by lvd) (fun j hj => by lvd) (by lvd) (by lvd)
        (fun r s hb => by have := hb.1; have := hb.2; lv hF) fr h', ?_⟩
      have k32 := keepBytes hp (N := 0) (stkV (by omega_using [])) (b := sb oSB 32) (by lvd) fr
      have k1 := keepBytes hp (N := 0) (stkV (by omega_using [])) (b := sb (oSB + 32) 1) (by lvd) fr
      rw [show (34 : Nat) = 32 + (1 + 1) from rfl, bytes_cat hp _ (l₁ := 32) (by lvd) (by lvd),
        bytes_cat hp _ (l₁ := 1) (l₂ := 1) (by lvd) (by lvd), k32, k1, h.1.rho, h.2, aSeed_eq, m']
      exact congrArg (fun x => vRho (vPk p s₀) ++ ([BitVec.ofNat 8 (e % 8)] ++ x)) (st8_bytes _ _ _ _ _)

include hP in
theorem sa_rej : VP p (SA2 p e) (SA3 p e)
    (Impl.MlDsa.X86.KeyGen.callPR vS "vg_mldsa_rej_ntt_poly" P.rejNtt
      [.buf (sb oSB 34), .buf (pB (20 + e)), .buf (ssB 2048)]) :=
  rejNtt_piece (Y := YV p) hP.rejNtt vS oSB vS (oP (20 + e)) vS oSS (by lvd) (Nat.le_of_eq (YV_stk p).symm)
    (ht := .block []) (by kernel_rfl) (fun _ _ _ h => h.1.vb.ctx)
    (fun s₀ s₀' s s' _ _ hq h h' => by rw [h.2, h'.2, (inputs_pub hq).1])
    fun s₀ s s' hp h h' fr red out => by
      obtain ⟨A, hA, hG⟩ := h.1.ex
      refine ⟨h.1.vb.keep hp (N := 80) (by omega_using []) (by lvd) (fun j hj => by lvd) fr h',
        by rw [keepBytes hp (N := 80) (stkV (by omega_using [])) (by lvd) fr]; exact h.1.rho,
        ⟨A, fun r s hb => keepPolyD hp (stkV (by omega_using [])) (by have := hb.1; have := hb.2; lv hF) fr (hA r s hb), ?_⟩,
        red, by rw [← h.2]; exact out⟩
      rw [acc_keepV hp (N := 80) (by omega_using []) (by lvd) fr]; exact hG

include hel in
theorem sa_mask : VP p (SA3 p e) (SA p · (e + 1)) (maskA oACC (oP (20 + e))) := by
  have hl := hF.l
  refine maskA_piece (Y := YV p) oACC (oP (20 + e)) (by lvd) (maskA_tt _) (fun _ _ _ h => h.vb.ctx)
    fun s₀ s s' hp h h' fr ha hc => ?_
  simp only [YV_sc] at fr ha hc
  obtain ⟨A, hA, hG⟩ := h.ex
  have r01 : s.gpr .eax = 0 ∨ s.gpr .eax = 1 := by
    rcases h.out with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨m1, m0⟩ := Proof.MlDsa.KeyGen.masked r01 hc
  have a01 : accV s₀ s = 0 ∨ accV s₀ s = 1 := by
    rcases hG with ⟨e, _⟩ | ⟨e, _⟩
    exacts [.inr e, .inl e]
  obtain ⟨-, aiff⟩ := Proof.MlDsa.KeyGen.acc_and a01 r01
  have fr' : Frame (FR s₀ [sb oACC 4, pB (20 + e)] 0) s.mem s'.mem := fr2 fr
  have ea : accV s₀ s' = accV s₀ s &&& s.gpr .eax := ha
  have hr : e / 8 < p.k := by omega_using [he]
  have hq : 8 * (e / 8) + e % 8 = e := Nat.div_add_mod e 8
  refine ⟨h.vb.keep hp (N := 0) (by omega_using []) (by lvd) (fun j hj => by lvd) fr' h',
    by rw [keepBytes hp (N := 0) (stkV (by omega_using [])) (by lvd) fr']; exact h.rho,
    fun r s => if r = e / 8 ∧ s = e % 8 then polyAt s'.mem (Buf.addr s₀ (pB (20 + e))) else A r s,
    fun r s hb => ?_, ?_⟩
  · dsimp only
    by_cases hrs : r = e / 8 ∧ s = e % 8
    · obtain ⟨rfl, rfl⟩ := hrs
      rw [ifp ⟨rfl, rfl⟩, pA_eq e]
      refine ⟨?_, rfl⟩
      rcases r01 with e0 | e1
      · exact (m0 e0).1
      · exact (m1 e1).2.2 (h.red e1)
    · rw [ifn hrs]
      have hb' : Before p e r s := ⟨hb.1, by
        have := hb.2
        rcases (by omega_using [this] : 8 * r + s < e ∨ 8 * r + s = e) with h | h
        · exact h
        · exact absurd ⟨by omega, by omega⟩ hrs⟩
      exact keepPolyD hp (stkV (by omega_using [])) (by have := hb'.1; have := hb'.2; lv hF) fr' (hA r s hb')
  · rw [ea]
    rcases hG with ⟨h1, b, hb⟩ | ⟨h0, hn⟩
    · rcases h.out with ⟨ho, b', hb'⟩ | ⟨ho, hn⟩
      · refine .inl ⟨aiff.mpr ⟨h1, ho⟩, Proof.MlDsa.Verify.bmax b b', fun r s hb₁ => ?_⟩
        dsimp only
        by_cases hrs : r = e / 8 ∧ s = e % 8
        · obtain ⟨rfl, rfl⟩ := hrs
          rw [ifp ⟨rfl, rfl⟩, (m1 ho).2.1]
          exact Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_right b b').rejNTT hb'
        · rw [ifn hrs]
          refine Proof.MlDsa.Verify.rejNTTPoly_mono (Proof.MlDsa.Verify.bmax_left b b').rejNTT (hb r s ⟨hb₁.1, ?_⟩)
          have := hb₁.2
          rcases (by omega_using [this] : 8 * r + s < e ∨ 8 * r + s = e) with h | h
          · exact h
          · exact absurd ⟨by omega, by omega⟩ hrs
      · rw [ho, h1]
        obtain ⟨hh, ehh, -⟩ := h.vb.hint
        exact .inr ⟨by decide, by
          show Spec.MlDsa.verifyMu p minBounds (vPk p s₀) (vMu s₀) (vSig p s₀) ≠ some true
          rw [Proof.MlDsa.Verify.verifyMu_rej_none minBounds _ _ ehh hr hel hn]; exact fun h => nomatch h⟩
    · rw [h0]
      exact .inr ⟨BitVec.zero_and, hn⟩

include hP hel in
theorem aOne_piece : VP p (SA p · e) (SA p · (e + 1)) (aOne P e) := by
  unfold aOne
  exact (sa_st1 hF he).seq ((sa_st2 hF he).seq ((sa_rej hP hF he).seq (sa_mask hF he hel)))

end

/-! ## `Â` and `c` -/

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : VFacts p)
include hP hF

theorem aRow_piece {r : Nat} (hr : r < p.k) : VP p (SA p · (8 * r)) (SA p · (8 * (r + 1))) (aRow P p r) := by
  have hl := hF.l
  unfold aRow
  refine (seqR_piece (I := fun e => (SA p · e)) p.ℓ (8 * r) fun e h₁ h₂ =>
    aOne_piece hP hF (by omega_using [hr, hl, h₂]) (by omega_using [h₁, h₂])).mono (fun _ _ _ h => h) fun _ _ _ h => h.congr fun r' s hs => ?_
  omega_using [hl, hs]

end

end VG.Proof.MlDsa.X86.Verify
