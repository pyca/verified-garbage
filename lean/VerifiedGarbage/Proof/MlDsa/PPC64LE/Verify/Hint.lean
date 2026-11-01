module

public import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Control
public import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallV
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.Verify.Control
meta import VerifiedGarbage.Proof.MlDsa.PPC64LE.KeyGen.CallV
meta import VerifiedGarbage.Proof.MlDsa.Verify.Final
meta import VerifiedGarbage.Proof.MlKem.Mem
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Taint
public import VerifiedGarbage.Proof.MlDsa.Verify.Spec

/-!
# ML-DSA verification on PPC64LE: the primitives, and the hint

As on 32-bit ARM (`Proof/MlDsa/Arm/Verify/Hint.lean`): the primitives
verification calls, verified with at most `S` bytes of stack (`VPrimsOk`);
and the hint `h` of the signature, unpacked to polynomials `0, …, k - 1`,
with `r24` 1 if it is well formed and 0 if not (`hint_piece`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.PPC64LE.Verify

open VG VG.PPC64LE VG.Proof.MlKem.PPC64LE
open VG.Proof.MlDsa.PPC64LE.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee HbuOk hbu_ok
  hbu_tr zx and24_ok)
open VG.Impl.MlDsa.PPC64LE.Verify
open VG.Impl.MlDsa.PPC64LE.KeyGen (and24)
open VG.Spec.MlDsa (Params hintBitUnpack)
open VG.Proof.MlDsa (HintIs)
open VG.Spec.Sha3 (bytesAt)

/-! ## The primitives -/

/-- The primitives, each verified against its contract with at most `S`
bytes of stack. -/
structure VPrimsOk (P : Prims) (S : Nat) : Prop where
  ntt : Callee P.ntt (fun stk => Proof.MlDsa.nttContract PPC64LE.abi stk) S
  invNtt : Callee P.invNtt (fun stk => Proof.MlDsa.nttInvContract PPC64LE.abi stk) S
  mul : Callee P.mul (fun stk => Proof.MlDsa.mulContract PPC64LE.abi stk) S
  mulAdd : Callee P.mulAdd (fun stk => Proof.MlDsa.mulAddContract PPC64LE.abi stk) S
  sub : Callee P.sub (fun stk => Proof.MlDsa.subContract PPC64LE.abi stk) S
  rejNtt : Callee P.rejNtt (fun stk => Proof.MlDsa.rejNTTContract PPC64LE.abi stk) S
  ball : Callee P.ball (fun stk => Proof.MlDsa.sampleInBallContract PPC64LE.abi stk) S
  useHint : Callee P.useHint (fun stk => Proof.MlDsa.useHintContract PPC64LE.abi stk) S
  simpleBitPack : Callee P.simpleBitPack (fun stk => Proof.MlDsa.simpleBitPackContract PPC64LE.abi stk) S
  bitUnpack : Callee P.bitUnpack (fun stk => Proof.MlDsa.bitUnpackContract PPC64LE.abi stk) S
  unpackT1 : Callee P.unpackT1 (fun stk => Proof.MlDsa.unpackT1Contract PPC64LE.abi stk) S
  hintUnpack : Callee P.hintUnpack (fun stk => Proof.MlDsa.hintBitUnpackContract PPC64LE.abi stk) S
  normLt : Callee P.normLt (fun stk => Proof.MlDsa.normLtContract PPC64LE.abi stk) S

/-! ## The signature -/

/-- `h`, or `⊥`, of the signature of a run from `σ`. -/
abbrev hintOf (p : Params) (σ : State) : Option (List (Vector Bool Spec.MlDsa.n)) :=
  Proof.MlDsa.Verify.vHint p (sgOf p σ)

/-- Bytes of the signature, from its bytes in memory. -/
theorem sig_slice {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.sigLen) :
    bytesAt s.mem ((vlay p STK σ).A 4 o) l = ((sgOf p σ).drop o).take l := by
  have e := h.sg
  simp only [Lay.A, BitVec.add_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-- Bytes of the public key, from its bytes in memory. -/
theorem pk_slice {p : Params} {STK : Nat} {σ s : State} (h : VC p STK σ s) {o l : Nat} (hl : o + l ≤ p.pkLen) :
    bytesAt s.mem ((vlay p STK σ).A 2 o) l = ((pkOf p σ).drop o).take l := by
  have e := h.pk
  simp only [Lay.A, BitVec.add_zero] at e ⊢
  rw [← e, Proof.MlKem.bytesAt_slice _ _ hl]

/-! ## The hint -/

/-- After the hint. -/
structure V1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  r24 : s.gpr .r24 = flag (hintOf p σ).isSome
  hint : ∀ h, hintOf p σ = some h → HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h

/-- After the call of `HintBitUnpack`: its result in `r3`. -/
structure H1 (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  r24 : s.gpr .r24 = 1
  r3 : zx (s.gpr .r3) = flag (hintOf p σ).isSome
  hint : ∀ h, hintOf p σ = some h → HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S ≤ STK)
include hP hF hS

omit hP hS in
theorem hint_m {σ : State} :
    HbuOk (vlay p STK σ) vWb (.r28, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k) := by
  have hk := hF.k; have hom := hF.om; have hl := hF.l
  have ho : oHint p < 2 ^ 31 := by
    rw [hF.hint]; rcases hF.ct with h | h | h <;> rcases hF.lz with h' | h' <;> rw [h, h'] <;> omega_arith
  exact ⟨⟨vptr_ok rfl ho, by vsep hF⟩, ⟨vptr_ok rfl (by decide), by vsep hF⟩, show ix Reg.r31 ∈ vWb by decide,
    by vsep hF, by rw [Nat.add_sub_cancel_left]; exact hF.hp, by omega_arith, by rw [Nat.add_sub_cancel_left], by omega_arith⟩

omit hP hF hS in
theorem zx_of {x : BitVec 64} {b : Bool} (h : x.setWidth 32 = if b then 1 else 0) : zx x = flag b := by
  cases b <;> simp only [zx, h, flag] <;> decide

theorem hbu_ok' {σ s : State} (h : VC p STK σ s) (h24 : s.gpr .r24 = 1) :
    WP isa (hintUnpackAt P (.r28, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) s (H1 p STK σ) := by
  have hs := h.site
  unfold hintUnpackAt
  refine hbu_ok hP.hintUnpack hs hS (hint_m hF) fun s' k' hm => ?_
  have h' := h.keep k' (by vsep hF [vcChk])
  have eb : bytesAt s.mem (lpa (vlay p STK σ) (.r28, oHint p)) (p.ω + p.k) =
      ((sgOf p σ).drop (oHint p)).take (p.ω + p.k) := sig_slice h (by rw [hF.sig])
  rw [eb, Nat.add_sub_cancel_left] at hm
  refine ⟨h', by rw [k'.cs _ (by decide)]; exact h24, ?_, fun hh e => ?_⟩
  · show zx (s'.gpr .r3) = flag (hintBitUnpack p.ω p.k (((sgOf p σ).drop (oHint p)).take (p.ω + p.k))).isSome
    refine zx_of ?_
    split at hm
    · rename_i hh e; rw [e]; exact hm.1
    · rename_i e; rw [e]; exact hm
  · show HintIs s'.mem _ p.k hh
    have e' : hintBitUnpack p.ω p.k ((sgOf p σ).drop (oHint p) |>.take (p.ω + p.k)) = some hh := e
    rw [e'] at hm
    exact hm.2

theorem hbu_piece :
    VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r24 = 1) (H1 p STK)
      (hintUnpackAt P (.r28, oHint p) (p.ω + p.k) p.ω (pH 0) (256 * p.k)) := by
  refine ⟨fun σ s _ h => hbu_ok' hP hF hS h.1 h.2, ?_⟩
  unfold hintUnpackAt
  refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
    bytesAt x.mem (lpa (vlay p STK σ) (.r28, oHint p)) (p.ω + p.k) =
      bytesAt y.mem (lpa (vlay p STK σ) (.r28, oHint p)) (p.ω + p.k))
    (RelCT.exists_ fun σ => hbu_tr hP.hintUnpack hS (hint_m hF)
      fun x y ⟨T, e⟩ => ⟨T.1, T.2.1, T.2.2, e⟩) ?_
  intro σ₁ _ _ _ _ _ pub h₁ h₂
  refine ⟨σ₁, vc_twoL pub h₁.1 h₂.1, ?_⟩
  show bytesAt _ ((vlay p STK σ₁).A 4 (oHint p)) _ = bytesAt _ ((vlay p STK σ₁).A 4 (oHint p)) _
  rw [sig_slice h₁.1 (by rw [hF.sig]), pub.2.2.2.2.2.2.2, vlay_pub pub, sig_slice h₂.1 (by rw [hF.sig])]

omit hP hF hS in
theorem and24_piece : VPiece p STK (H1 p STK) (V1 p STK) (.block and24) := by
  refine ⟨fun σ s _ h => WP.mono (and24_ok s) fun s' ⟨_, e24, hr⟩ => ⟨h.vc.regs2 hr, ?_, ?_⟩,
    vrel31 (fun _ _ h => h.vc) (by taint_decide)⟩
  · rw [e24, h.r24, h.r3]; cases (hintOf p σ).isSome <;> decide
  · intro hh e; rw [hr.mem]; exact h.hint hh e

theorem hint_piece :
    VPiece p STK (fun σ s => VC p STK σ s ∧ s.gpr .r24 = 1) (V1 p STK) (hint P p) :=
  (hbu_piece hP hF hS).seq and24_piece

end

end VG.Proof.MlDsa.PPC64LE.Verify
