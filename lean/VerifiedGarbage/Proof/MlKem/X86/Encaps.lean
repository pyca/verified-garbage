import VerifiedGarbage.Proof.MlKem.X86.Decaps
import VerifiedGarbage.Impl.MlKem.X86.Encaps
import VerifiedGarbage.Spec.MlKem.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.EncapsBody`. -/
section

/-!
# ML-KEM on x86 (32-bit): the body of encapsulation

The layout of the arguments (`Y L`: `ek`, `m`, `key`, `ct`, `scratch`, and
the 88 bytes of stack). `ek` and `m` are copied into `scratch`, `H(ek)` and
`G(m ‖ H(ek))` hashed (`start_piece`), the ciphertext computed
(`Enc.encrypt_piece`), and `K` and the ciphertext copied out (`fin_piece`).
If every `SampleNTT` succeeded, K-PKE.Encrypt succeeds with the matrix sampled
within one bound on their iterations (`KPke.kpkeEncrypt_some`); if one failed
within `minIterations`, it fails with that bound (`KPke.kpkeEncrypt_none`)
(`post`). Each parameter set's contract implies `TPre (Y L)` and its public
data `TPub (Y L) (lk L)` (`Proof/MlKem/X86/Encaps.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.Encaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3_512 sha3Suffix)

/-- `ek` and `m` (read), `key`, `ct` and `scratch` (written); 88 bytes of stack. -/
def Y (L : KemLay) : Lay :=
  ⟨[(L.p.ekLen, false), (32, false), (32, true), (L.p.ctLen, true), (L.scratch, true)], 4, 88⟩

section
variable (L : KemLay) (s₀ : State)
/-- `ek` (irreducible, so that elaboration never evaluates its bytes). -/
@[irreducible] def ek : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.ekLen⟩) L.p.ekLen
/-- `m`. -/
@[irreducible] def msg : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32
/-- What encaps may leak: `ρ`. -/
abbrev lk : List Byte := ekRho L.p (VG.Proof.MlKem.X86.Encaps.ek L s₀)
/-- `G(m ‖ H(ek))`, as 64 bytes. -/
@[irreducible] def kr : List Byte := sha3_512 (VG.Proof.MlKem.X86.Encaps.msg s₀ ++ H (VG.Proof.MlKem.X86.Encaps.ek L s₀))
end

theorem ek_eq (L : KemLay) (s₀ : State) : VG.Proof.MlKem.X86.Encaps.ek L s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.ekLen⟩) L.p.ekLen := by
  unfold VG.Proof.MlKem.X86.Encaps.ek; rfl
theorem msg_eq (s₀ : State) : VG.Proof.MlKem.X86.Encaps.msg s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 := by unfold VG.Proof.MlKem.X86.Encaps.msg; rfl
theorem kr_eq (L : KemLay) (s₀ : State) : VG.Proof.MlKem.X86.Encaps.kr L s₀ = sha3_512 (VG.Proof.MlKem.X86.Encaps.msg s₀ ++ H (VG.Proof.MlKem.X86.Encaps.ek L s₀)) := by unfold VG.Proof.MlKem.X86.Encaps.kr; rfl

/-- The inputs of K-PKE.Encrypt. -/
abbrev I (L : KemLay) : Enc.Inp := ⟨VG.Proof.MlKem.X86.Encaps.ek L, VG.Proof.MlKem.X86.Encaps.msg, VG.Proof.MlKem.X86.Encaps.kr L⟩

theorem hS (L : KemLay) : Enc.SOK L (VG.Proof.MlKem.X86.Encaps.Y L) := ⟨of_decide_eq_true rfl, rfl, rfl, rfl⟩

theorem hρ (L : KemLay) : Enc.RhoPub L (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.lk L) (VG.Proof.MlKem.X86.Encaps.I L) := fun _ _ _ _ hq => hq.2.2

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-! ## The inputs of K-PKE.Encrypt -/

/-- `H(ek)`. -/
abbrev bH (L : KemLay) : Buf := ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eH, 32⟩

/-- The facts of the layout that encapsulation uses. -/
class EncapsOK (L : KemLay) : Prop where
  ekc : ((VG.Proof.MlKem.X86.Encaps.Y L).ok ⟨0, 0, L.p.ekLen⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eEK, L.p.ekLen⟩ &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨0, 0, L.p.ekLen⟩ ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eEK, L.p.ekLen⟩) = true
  mc : ((VG.Proof.MlKem.X86.Encaps.Y L).ok ⟨1, 0, 32⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eM, 32⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨1, 0, 32⟩ ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eM, 32⟩) = true
  ek4 : 4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ekLen < 2 ^ 32
  ct4 : 4 * (L.p.ctLen / 4) = L.p.ctLen ∧ 0 < L.p.ctLen / 4 ∧ L.p.ctLen / 4 < 2 ^ 30
  aEM : (VG.Proof.MlKem.X86.Encaps.Y L).apart (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc) [⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eM, 32⟩] = true
  hh : ((VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).ok (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc) && (VG.Proof.MlKem.X86.Encaps.Y L).okW (VG.Proof.MlKem.X86.Encaps.bH L) &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).sep (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ (VG.Proof.MlKem.X86.Encaps.bH L) &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep (VG.Proof.MlKem.X86.Encaps.bH L) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩) = true
  aH : (VG.Proof.MlKem.X86.Encaps.Y L).apart (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc) [⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩, ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩, VG.Proof.MlKem.X86.Encaps.bH L] = true ∧
    (VG.Proof.MlKem.X86.Encaps.Y L).apart (Enc.bM L (VG.Proof.MlKem.X86.Encaps.Y L).sc) [⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩, ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩, VG.Proof.MlKem.X86.Encaps.bH L] = true
  g : ((VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).ok (Enc.bM L (VG.Proof.MlKem.X86.Encaps.Y L).sc) && (VG.Proof.MlKem.X86.Encaps.Y L).ok (VG.Proof.MlKem.X86.Encaps.bH L) &&
    (VG.Proof.MlKem.X86.Encaps.Y L).okW (Enc.bKR L (VG.Proof.MlKem.X86.Encaps.Y L).sc) && (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩ &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep (Enc.bM L (VG.Proof.MlKem.X86.Encaps.Y L).sc) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).sep (Enc.bM L (VG.Proof.MlKem.X86.Encaps.Y L).sc) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩ &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep (VG.Proof.MlKem.X86.Encaps.bH L) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).sep (VG.Proof.MlKem.X86.Encaps.bH L) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩ &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩ (Enc.bKR L (VG.Proof.MlKem.X86.Encaps.Y L).sc) && (VG.Proof.MlKem.X86.Encaps.Y L).sep (Enc.bKR L (VG.Proof.MlKem.X86.Encaps.Y L).sc) ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩) = true
  aG : (VG.Proof.MlKem.X86.Encaps.Y L).apart (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc) [⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩, ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩, Enc.bKR L (VG.Proof.MlKem.X86.Encaps.Y L).sc] = true ∧
    (VG.Proof.MlKem.X86.Encaps.Y L).apart (Enc.bM L (VG.Proof.MlKem.X86.Encaps.Y L).sc) [⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eST, 200⟩, ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eWK, 640⟩, Enc.bKR L (VG.Proof.MlKem.X86.Encaps.Y L).sc] = true
  key : ((VG.Proof.MlKem.X86.Encaps.Y L).ok ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eKR, 32⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨2, 0, 32⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eKR, 32⟩ ⟨2, 0, 32⟩) = true
  ct : ((VG.Proof.MlKem.X86.Encaps.Y L).ok ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eC, L.p.ctLen⟩ && (VG.Proof.MlKem.X86.Encaps.Y L).okW ⟨3, 0, L.p.ctLen⟩ &&
    (VG.Proof.MlKem.X86.Encaps.Y L).sep ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eC, L.p.ctLen⟩ ⟨3, 0, L.p.ctLen⟩) = true
  dKey : Enc.safe L (VG.Proof.MlKem.X86.Encaps.Y L) [⟨2, 0, 32⟩] = true ∧
    (VG.Proof.MlKem.X86.Encaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [⟨2, 0, 32⟩] = true
  dCt : Enc.safe L (VG.Proof.MlKem.X86.Encaps.Y L) [⟨3, 0, L.p.ctLen⟩] = true ∧
    (VG.Proof.MlKem.X86.Encaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [⟨3, 0, L.p.ctLen⟩] = true ∧
    (VG.Proof.MlKem.X86.Encaps.Y L).apart ⟨2, 0, 32⟩ [⟨3, 0, L.p.ctLen⟩] = true ∧ (VG.Proof.MlKem.X86.Encaps.Y L).apart (Enc.bACC L (VG.Proof.MlKem.X86.Encaps.Y L).sc) [⟨3, 0, L.p.ctLen⟩] = true
  acc : (VG.Proof.MlKem.X86.Encaps.Y L).ok (Enc.bACC L (VG.Proof.MlKem.X86.Encaps.Y L).sc) = true ∧ Enc.safe L (VG.Proof.MlKem.X86.Encaps.Y L) [] = true ∧
    (VG.Proof.MlKem.X86.Encaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [] = true

/-- `sc_taint`, for code with `scratch` at `(Y L).sc`. -/
macro "ye_taint" : tactic => `(tactic| ((try simp only [show ∀ L, (Y L).sc = 4 from fun _ => rfl]); sc_taint))

variable {L : KemLay}

/-- After `ek` is copied. -/
structure Q1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Encaps.Y L) s₀ s
  ekc : bytesAt s.mem (Buf.addr s₀ (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc)) L.p.ekLen = VG.Proof.MlKem.X86.Encaps.ek L s₀

/-- After `m` is copied. -/
structure Q2 (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Encaps.Q1 L s₀ s where
  mc : bytesAt s.mem (Buf.addr s₀ (Enc.bM L (VG.Proof.MlKem.X86.Encaps.Y L).sc)) 32 = VG.Proof.MlKem.X86.Encaps.msg s₀

/-- After `H(ek)` is hashed. -/
structure Q3 (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Encaps.Q2 L s₀ s where
  hh : bytesAt s.mem (Buf.addr s₀ (VG.Proof.MlKem.X86.Encaps.bH L)) 32 = H (VG.Proof.MlKem.X86.Encaps.ek L s₀)

variable [VG.Proof.MlKem.X86.Encaps.EncapsOK L]

/-- The inputs of K-PKE.Encrypt, then `c`. -/
theorem start_piece {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (VG.Proof.MlKem.X86.Encaps.Y L)) (TPub (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.lk L)) (Enc.Base L (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.I L)) Q c) :
    Piece (TPre (VG.Proof.MlKem.X86.Encaps.Y L)) (TPub (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 36))]) <|
        .seq (copyW 4 ⟨0, 0, L.p.ekLen⟩ ⟨4, L.eEK, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (copyW 4 ⟨1, 0, 32⟩ ⟨4, L.eM, 32⟩ 8) <|
        .seq (hash1 4 L.eST L.eWK 136 6 ⟨4, L.eEK, L.p.ekLen⟩ ⟨4, L.eH, 32⟩) <|
        .seq (hash2 4 L.eST L.eWK 72 6 ⟨4, L.eM, 32⟩ ⟨4, L.eH, 32⟩ ⟨4, L.eKR, 64⟩) c) := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := EncapsOK.ek4 (L := L)
  have ekc := EncapsOK.ekc (L := L)
  have hok : (VG.Proof.MlKem.X86.Encaps.Y L).ok ⟨0, 0, L.p.ekLen⟩ = true := by simp only [Bool.and_eq_true] at ekc; exact ekc.1.1
  have mc := EncapsOK.mc (L := L)
  have hokm : (VG.Proof.MlKem.X86.Encaps.Y L).ok ⟨1, 0, 32⟩ = true := by simp only [Bool.and_eq_true] at mc; exact mc.1.1
  refine Piece.seq (ldsc_piece (Y := VG.Proof.MlKem.X86.Encaps.Y L) (by ye_taint)) ?_
  refine Piece.seq (B := VG.Proof.MlKem.X86.Encaps.Q1 L) (copyW_piece' (Y := VG.Proof.MlKem.X86.Encaps.Y L) 0 0 4 L.eEK (L.p.ekLen / 4) L.p.ekLen e₁ e₂ e₃ ekc
    (by ye_taint) (by taint_decide) (fun _ _ _ h => h) fun s₀ s s' hp h h' _ post => ⟨h', ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨4, L.eEK, L.p.ekLen⟩) L.p.ekLen = _
    rw [post, VG.Proof.MlKem.X86.Encaps.ek_eq]
    exact h.roBytes hp (b := ⟨0, 0, L.p.ekLen⟩) hok rfl
  refine Piece.seq (B := VG.Proof.MlKem.X86.Encaps.Q2 L) (copyW_piece (Y := VG.Proof.MlKem.X86.Encaps.Y L) 1 0 4 L.eM 8 (by rdecide) (by rdecide) mc
    (by ye_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', by rw [keepBytes hp (N := 0) (by rdecide) EncapsOK.aEM (fr1 fr)]; exact h.ekc⟩, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨4, L.eM, 4 * 8⟩) (4 * 8) = _
    rw [post, VG.Proof.MlKem.X86.Encaps.msg_eq]
    exact h.ctx.roBytes hp (b := ⟨1, 0, 32⟩) hokm rfl
  obtain ⟨a₁, a₂⟩ := EncapsOK.aH (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.Encaps.Q3 L) (hash1_piece (Y := VG.Proof.MlKem.X86.Encaps.Y L) L.eST L.eWK 136 6 (Enc.bEK L (VG.Proof.MlKem.X86.Encaps.Y L).sc) (VG.Proof.MlKem.X86.Encaps.bH L) rate136
    EncapsOK.hh (by rdecide) e₄ (by rdecide) (by taint_rfl) (by ye_taint) (by ye_taint) (by ye_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨⟨⟨h', by rw [keepBytes hp (by rdecide) a₁ fr]; exact h.ekc⟩,
        by rw [keepBytes hp (by rdecide) a₂ fr]; exact h.mc⟩, ?_⟩) ?_
  · rw [out, h.ekc, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← H_eq]
  obtain ⟨g₁, g₂⟩ := EncapsOK.aG (L := L)
  refine Piece.seq (hash2_piece (Y := VG.Proof.MlKem.X86.Encaps.Y L) L.eST L.eWK 72 6 (Enc.bM L (VG.Proof.MlKem.X86.Encaps.Y L).sc) (VG.Proof.MlKem.X86.Encaps.bH L) (Enc.bKR L (VG.Proof.MlKem.X86.Encaps.Y L).sc) rate72
    EncapsOK.g (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by ye_taint) (by ye_taint) (by ye_taint)
    (by ye_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨h', by rw [keepBytes hp (by rdecide) g₁ fr]; exact h.ekc,
        by rw [keepBytes hp (by rdecide) g₂ fr]; exact h.mc, ?_⟩) hc
  rw [out, h.mc, h.hh, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← sha3_512_eq]
  exact (VG.Proof.MlKem.X86.Encaps.kr_eq L s₀).symm

/-! ## The outputs -/

omit [VG.Proof.MlKem.X86.Encaps.EncapsOK L] in
theorem done_keep {s₀ s s' : State} (hp : TPre (VG.Proof.MlKem.X86.Encaps.Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (VG.Proof.MlKem.X86.Encaps.Y L).stk)
    (hs : Enc.safe L (VG.Proof.MlKem.X86.Encaps.Y L) bs = true) (hc : (VG.Proof.MlKem.X86.Encaps.Y L).apart ⟨(VG.Proof.MlKem.X86.Encaps.Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : Enc.Done L (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.I L) s₀ s) (c : VG.Proof.MlKem.X86.Top.Ctx (VG.Proof.MlKem.X86.Encaps.Y L) s₀ s') :
    Enc.Done L (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.I L) s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, by rw [keepBytes hp hM hc fr]; exact h.cv⟩

/-- After `K` is copied into `key`. -/
structure F1 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.I L) s₀ s where
  key : bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = (Encaps.kr L s₀).take 32

/-- After the ciphertext is copied into `ct`. -/
structure F2 (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Encaps.F1 L s₀ s where
  ct : Enc.accE L (VG.Proof.MlKem.X86.Encaps.Y L) s₀ s = 1 → bytesAt s.mem (Buf.addr s₀ ⟨3, 0, L.p.ctLen⟩) L.p.ctLen =
    KPke.ct L.p (Enc.aE L (VG.Proof.MlKem.X86.Encaps.I L) s₀) (Encaps.ek L s₀) (VG.Proof.MlKem.X86.Encaps.msg s₀) (Enc.rE (VG.Proof.MlKem.X86.Encaps.I L) s₀)

/-- After `eACC` is loaded, to be returned. -/
structure Fin (L : KemLay) (s₀ s : State) : Prop extends VG.Proof.MlKem.X86.Encaps.F2 L s₀ s where
  eax : s.gpr .eax = Enc.accE L (VG.Proof.MlKem.X86.Encaps.Y L) s₀ s

theorem fin_piece [Enc.VOK L] :
    Piece (TPre (VG.Proof.MlKem.X86.Encaps.Y L)) (TPub (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.lk L)) (Enc.Done L (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.I L)) (VG.Proof.MlKem.X86.Encaps.Fin L)
      (.seq (copyW 4 ⟨4, L.eKR, 32⟩ ⟨2, 0, 32⟩ 8) <|
        .seq (copyW 4 ⟨4, L.eC, L.p.ctLen⟩ ⟨3, 0, L.p.ctLen⟩ (L.p.ctLen / 4))
          (.block [.mov .eax (.mem (at_ .esi L.eACC))])) := by
  obtain ⟨c₁, c₂, c₃⟩ := EncapsOK.ct4 (L := L)
  obtain ⟨d₁, d₂⟩ := EncapsOK.dKey (L := L)
  obtain ⟨d₃, d₄, d₅, d₆⟩ := EncapsOK.dCt (L := L)
  obtain ⟨u₁, u₂, u₃⟩ := EncapsOK.acc (L := L)
  refine Piece.seq (B := VG.Proof.MlKem.X86.Encaps.F1 L) (copyW_piece (Y := VG.Proof.MlKem.X86.Encaps.Y L) 4 L.eKR 2 0 8 (by rdecide) (by rdecide) EncapsOK.key
    (by ye_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨VG.Proof.MlKem.X86.Encaps.done_keep hp (M := 0) (by rdecide) d₁ d₂ (fr1 fr) h h', ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨2, 0, 4 * 8⟩) (4 * 8) = _
    rw [post, show Encaps.kr L s₀ = (VG.Proof.MlKem.X86.Encaps.I L).kr s₀ from rfl, ← h.kr, bytesAt_take _ _ (show 32 ≤ 64 by decide)]
    rfl
  refine Piece.seq (B := VG.Proof.MlKem.X86.Encaps.F2 L) (copyW_piece' (Y := VG.Proof.MlKem.X86.Encaps.Y L) 4 L.eC 3 0 (L.p.ctLen / 4) L.p.ctLen c₁ c₂ c₃
    EncapsOK.ct (by ye_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨VG.Proof.MlKem.X86.Encaps.done_keep hp (M := 0) (by rdecide) d₃ d₄ (fr1 fr) h.toDone h',
        by rw [keepBytes hp (N := 0) (by rdecide) d₅ (fr1 fr)]; exact h.key⟩, fun e => ?_⟩) ?_
  · have ea : Enc.accE L (VG.Proof.MlKem.X86.Encaps.Y L) s₀ s' = Enc.accE L (VG.Proof.MlKem.X86.Encaps.Y L) s₀ s := keepW hp (N := 0) (by rdecide) d₆ (fr1 fr)
    rw [post]
    exact Enc.ct_eq (VG.Proof.MlKem.X86.Encaps.hS L) hp h.toDone (ea ▸ e)
  exact ld32_piece (Y := VG.Proof.MlKem.X86.Encaps.Y L) L.eACC u₁ (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨⟨⟨VG.Proof.MlKem.X86.Encaps.done_keep hp (bs := []) (M := 0) (by rdecide) u₂ u₃
      (m' ▸ Frame.refl _ _) h.toDone h', by rw [m']; exact h.key⟩, fun e₁ => by
        rw [m']; exact h.ct (by show s.mem.readW _ 32 = _; rw [← m']; exact e₁)⟩,
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']⟩

theorem body_piece [CeOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L] [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) :
    Piece (TPre (VG.Proof.MlKem.X86.Encaps.Y L)) (TPub (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.lk L)) (fun s₀ s => s = P0 s₀) (VG.Proof.MlKem.X86.Encaps.Fin L) (encapsBody L) :=
  VG.Proof.MlKem.X86.Encaps.start_piece <| .seq (Enc.encrypt_piece (VG.Proof.MlKem.X86.Encaps.hS L) (VG.Proof.MlKem.X86.Encaps.hρ L) hk) VG.Proof.MlKem.X86.Encaps.fin_piece

theorem piece [CeOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L] [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k)
    (hsp : NoSp (encapsBody L)) :
    Piece (TPre (VG.Proof.MlKem.X86.Encaps.Y L)) (TPub (VG.Proof.MlKem.X86.Encaps.Y L) (VG.Proof.MlKem.X86.Encaps.lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (VG.Proof.MlKem.X86.Encaps.Fin L s₀) s₀ s')
      (leaf (encapsBody L)) :=
  topLeaf hsp ((VG.Proof.MlKem.X86.Encaps.body_piece hk).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

omit [VG.Proof.MlKem.X86.Encaps.EncapsOK L] in
/-- The postcondition, from the final state of the body. -/
theorem post (hη : L.p.η₁ = 2 ∧ L.p.η₂ = 2) {s₀ s : State} (h : VG.Proof.MlKem.X86.Encaps.Fin L s₀ s) :
    Outcome (fun iters => encapsInternal L.p iters (VG.Proof.MlKem.X86.Encaps.ek L s₀) (VG.Proof.MlKem.X86.Encaps.msg s₀)) (Enc.accE L (VG.Proof.MlKem.X86.Encaps.Y L) s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32, bytesAt s.mem (Buf.addr s₀ ⟨3, 0, L.p.ctLen⟩) L.p.ctLen) := by
  have er : Enc.rE (VG.Proof.MlKem.X86.Encaps.I L) s₀ = (G (VG.Proof.MlKem.X86.Encaps.msg s₀ ++ H (VG.Proof.MlKem.X86.Encaps.ek L s₀))).2 := by
    show (VG.Proof.MlKem.X86.Encaps.kr L s₀).drop 32 = _; rw [VG.Proof.MlKem.X86.Encaps.kr_eq]; rfl
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; exact absurd hk (by rdecide)
    refine .inr ⟨e, ?_⟩
    show encapsInternal L.p minIterations (VG.Proof.MlKem.X86.Encaps.ek L s₀) (VG.Proof.MlKem.X86.Encaps.msg s₀) = none
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none (i := k % L.p.k) (j := k / L.p.k) (Nat.mod_lt _ hk0)
      (Nat.div_lt_of_lt_mul hk) hn]
    rfl
  · obtain ⟨M, hM⟩ := Enc.samples h.toDone e
    refine .inl ⟨e, M, ?_⟩
    show encapsInternal L.p M (VG.Proof.MlKem.X86.Encaps.ek L s₀) (VG.Proof.MlKem.X86.Encaps.msg s₀) = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some hη hM, h.key, h.ct e, er, VG.Proof.MlKem.X86.Encaps.kr_eq]
    rfl

end VG.Proof.MlKem.X86.Encaps

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlKem.X86.Encaps`. -/
section

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_encaps`

Encapsulation (`EncapsBody.lean`) for ML-KEM-768 (`L768`): the facts of its
layout (`EncapsOK`), computed from its offsets; the contract's precondition
implies `TPre (Y L768)` (`pre_of`) and its public data `TPub` (`pub_of`).
-/

namespace VG.Proof.MlKem.X86.Encaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

instance : VG.Proof.MlKem.X86.Encaps.EncapsOK L768 where
  ekc := by decide
  mc := by decide
  ek4 := by decide
  ct4 := by decide
  aEM := by decide
  hh := by decide
  aH := by decide
  g := by decide
  aG := by decide
  key := by decide
  ct := by decide
  dKey := by simp only [Enc.safe, Enc.safeS]; decide
  dCt := by simp only [Enc.safe, Enc.safeS]; decide
  acc := by simp only [Enc.safe, Enc.safeS]; decide

theorem pre_of {s₀ : State} (h : (encapsContract X86.abi 88).pre s₀) : TPre (VG.Proof.MlKem.X86.Encaps.Y L768) s₀ := by
  sig_pre [encapsContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, -, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h25 h26 h27 h28 h29 h30
  have c5 : ∀ i, i < (VG.Proof.MlKem.X86.Encaps.Y L768).n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    simp only [VG.Proof.MlKem.X86.Encaps.Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by decide, by simp only [VG.Proof.MlKem.X86.Encaps.Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h30, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [VG.Proof.MlKem.X86.Top.argR, Lay.alen, VG.Proof.MlKem.X86.Encaps.Y, L768, Params.ekLen, Params.ctLen, mlKem768]
  · rw [h4]; simp [gR, Lay.n, VG.Proof.MlKem.X86.Encaps.Y]
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6, h7,
      absurd hw (by decide), absurd rfl hne, h9, h10, h11,
      h5.symm, h9.symm, absurd rfl hne, h13, h14,
      h6.symm, h10.symm, h13.symm, absurd rfl hne, h16,
      h7.symm, h11.symm, h14.symm, h16.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h8.symm, h12.symm, h15.symm, h17.symm, h18.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22, h23]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h25, h26, h27, h28, h29]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h31, h32, h33, h34, h35]

theorem pub_of {s₀ s₀' : State} (h : (encapsContract X86.abi 88).pub s₀ s₀') : TPub (VG.Proof.MlKem.X86.Encaps.Y L768) (VG.Proof.MlKem.X86.Encaps.lk L768) s₀ s₀' := by
  sig_pub [encapsContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [VG.Proof.MlKem.X86.Encaps.Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [e₃, e₄, e₅, e₆, e₇]
  · have e := map_toNat_inj e₂
    show ekRho L768.p (VG.Proof.MlKem.X86.Encaps.ek L768 s₀) = ekRho L768.p (VG.Proof.MlKem.X86.Encaps.ek L768 s₀')
    rw [VG.Proof.MlKem.X86.Encaps.ek_eq, VG.Proof.MlKem.X86.Encaps.ek_eq, VG.Proof.MlKem.X86.Encaps.addr0, VG.Proof.MlKem.X86.Encaps.addr0]
    exact e

/-- Memory with the arguments `0`, `0x800`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x08 else if a = 0x500d then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5016 then 1
  else 0

theorem verified : Verified X86.target Impl.MlKem.X86.encaps (encapsContract X86.abi 88) := by
  refine Piece.verified (((VG.Proof.MlKem.X86.Encaps.piece (L := L768) (by decide) (NoSp.of_all (by decide +kernel))).pre_mono (fun _ h => VG.Proof.MlKem.X86.Encaps.pre_of h) fun _ _ _ _ h => VG.Proof.MlKem.X86.Encaps.pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [encapsContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := VG.Proof.MlKem.X86.Encaps.post (by decide) hfin
    rw [VG.Proof.MlKem.X86.Encaps.ek_eq, VG.Proof.MlKem.X86.Encaps.msg_eq, VG.Proof.MlKem.X86.Encaps.addr0, VG.Proof.MlKem.X86.Encaps.addr0, VG.Proof.MlKem.X86.Encaps.addr0, VG.Proof.MlKem.X86.Encaps.addr0] at r
    exact r
  · let st := VG.Proof.MlKem.X86.satState VG.Proof.MlKem.X86.Encaps.satMem [⟨0, 1184⟩, ⟨0x800, 32⟩]
      [⟨0x1000, 32⟩, ⟨0x2000, 1088⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 20⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [encapsContract, encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.Encaps

end
