module

public import VerifiedGarbage.Proof.MlKem.X86.DecapsCmp
public import VerifiedGarbage.Proof.MlKem.X86.EncV
meta import VerifiedGarbage.Proof.MlKem.X86.DecapsCmp
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.MlKem.X86.TopLocal
meta import VerifiedGarbage.Proof.MlKem.X86.TopLocal
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
import VerifiedGarbage.Proof.MlKem.X86.NttSetup
import VerifiedGarbage.Proof.MlKem.X86.Red
import VerifiedGarbage.Proof.MlKem.X86.Table
import VerifiedGarbage.Proof.MlKem.X86.TopCall
import VerifiedGarbage.Proof.MlKem.X86.TopSeq
import VerifiedGarbage.Proof.Sha512.Spec
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.MlKem.X86.CheckEkBody
meta import VerifiedGarbage.Proof.MlKem.X86.EncV
meta import VerifiedGarbage.Proof.MlKem.X86.NttSetup
meta import VerifiedGarbage.Proof.MlKem.X86.Red
meta import VerifiedGarbage.Proof.MlKem.X86.Table
meta import VerifiedGarbage.Proof.MlKem.X86.TopCall
meta import VerifiedGarbage.Proof.MlKem.X86.TopSeq
meta import VerifiedGarbage.Proof.Sha512.Spec
public import VerifiedGarbage.Impl.MlKem.X86.Decaps
public import VerifiedGarbage.Proof.MlKem.X86.TopKem
meta import VerifiedGarbage.Impl.MlKem.X86.Decaps
meta import VerifiedGarbage.Proof.MlKem.X86.TopKem

/-! ### `MlKem.X86.DecapsDec`, which only this module used -/

section

/-!
# ML-KEM on x86 (32-bit): K-PKE.Decrypt in decapsulation

`w = Σ ŝ[i] ×_T NTT(u'[i])`, with `u'[i]` decoded and decompressed from `ct`
and `ŝ[i]` decoded from `dk` (`term0_piece`, `term_piece`), then `m' =
ByteEncode₁(Compress₁(v' - NTT⁻¹(w)))` (`decrypt_piece`), which is `mD`.
-/

@[expose] public section

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
abbrev dS (i : Nat) : Poly := dcS (KPke.dkPke L.p (dk L s₀)) i
/-- `NTT(u'[i])`. -/
abbrev dU (i : Nat) : Poly := ntt (KPke.dcU L.p (ct L s₀) i)
/-- `ŝ[0] ×_T NTT(u'[0]) + … + ŝ[j - 1] ×_T NTT(u'[j - 1])`. -/
abbrev partD (j : Nat) : Poly := KPke.dotK (dS L s₀) (dU L s₀) j
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
  ctx : Ctx (Y L) s₀ s
  w : 0 < j → Reduced s.mem (Buf.addr s₀ (bW L)) ∧ polyAt s.mem (Buf.addr s₀ (bW L)) = partD L s₀ j

variable {L : KemLay}

theorem D.keep {j : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hW : (Y L).apart (bW L) bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : D L j s₀ s) (c : Ctx (Y L) s₀ s') : D L j s₀ s' :=
  ⟨c, fun hj => ⟨keepRed hp hM hW fr (h.w hj).1, by rw [polyAt_congr (Top.keep hp hM hW fr)]; exact (h.w hj).2⟩⟩

/-- `u'[i]` is decoded, decompressed and in the NTT domain; `ŝ[i]` decoded. -/
structure D1 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D L j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ (bA L)) (KPke.dcU L.p (ct L s₀) j)

structure D2 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D L j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ (bA L)) (dU L s₀ j)

structure D3 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D2 L j s₀ s where
  t : PolyIs s.mem (Buf.addr s₀ (bT L)) (dS L s₀ j)

structure D4 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D L j s₀ s where
  p : PolyIs s.mem (Buf.addr s₀ (bP L)) (multiplyNTTs (dS L s₀ j) (dU L s₀ j))

/-- The facts of the layout that K-PKE.Decrypt uses. -/
class DecOK (L : KemLay) : Prop where
  ct : (Y L).ok ⟨1, 0, L.p.ctLen⟩ = true ∧ (Y L).ok ⟨0, 0, L.p.dkLen⟩ = true ∧
    32 * L.p.du * L.p.k + 32 * L.p.dv ≤ L.p.ctLen
  dec : ∀ i < L.p.k, (Y L).ok (bCU L i) = true ∧ (Y L).ok ⟨0, 384 * i, 384⟩ = true ∧
    ((Y L).ok (bCU L i) && (Y L).okW (bA L) && (Y L).sep (bCU L i) (bA L)) = true ∧
    ((Y L).ok ⟨0, 384 * i, 384⟩ && (Y L).okW (bT L) && (Y L).sep ⟨0, 384 * i, 384⟩ (bT L)) = true
  keep : (Y L).apart (bW L) [bA L] = true ∧ (Y L).apart (bW L) [bA L, bNS L] = true ∧
    ((Y L).okW (bA L) && (Y L).okW (bNS L) && (Y L).sep (bA L) (bNS L)) = true ∧
    (Y L).apart (bW L) [bT L] = true ∧ (Y L).apart (bA L) [bT L] = true ∧
    (Y L).apart (bW L) [bP L, bNS L] = true ∧
    ((Y L).okW (bW L) && (Y L).ok (bP L) && (Y L).sep (bW L) (bP L)) = true
  mul : ((Y L).okW (bW L) && (Y L).ok (bT L) && (Y L).ok (bA L) && (Y L).okW (bNS L) && (Y L).sep (bW L) (bT L) &&
    (Y L).sep (bW L) (bA L) && (Y L).sep (bW L) (bNS L) && (Y L).sep (bT L) (bNS L) &&
    (Y L).sep (bA L) (bNS L)) = true ∧
    ((Y L).okW (bP L) && (Y L).ok (bT L) && (Y L).ok (bA L) && (Y L).okW (bNS L) && (Y L).sep (bP L) (bT L) &&
    (Y L).sep (bP L) (bA L) && (Y L).sep (bP L) (bNS L) && (Y L).sep (bT L) (bNS L) &&
    (Y L).sep (bA L) (bNS L)) = true
  v : ((Y L).okW (bW L) && (Y L).okW (bNS L) && (Y L).sep (bW L) (bNS L)) = true ∧
    ((Y L).ok (bCV L) && (Y L).okW (bE L) && (Y L).sep (bCV L) (bE L)) = true ∧
    (Y L).ok (bCV L) = true ∧ (Y L).apart (bW L) [bE L] = true ∧
    ((Y L).okW (bE L) && (Y L).ok (bW L) && (Y L).sep (bE L) (bW L)) = true ∧
    ((Y L).ok (bE L) && (Y L).okW ⟨3, L.eM, 32 * 1⟩ && (Y L).sep (bE L) ⟨3, L.eM, 32 * 1⟩) = true

variable [DecOK L]

/-- The bytes of `ct[o : o + l]`. -/
theorem ct_slice {s₀ s : State} (hp : TPre (Y L) s₀) (h : Ctx (Y L) s₀ s) {o l : Nat} (hl : o + l ≤ L.p.ctLen)
    (hb : (Y L).ok ⟨1, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, o, l⟩) l = ((ct L s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨1, o, l⟩) hb rfl, ct_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨1, o, l⟩) hb, Buf.addr_eq hp (b := ⟨1, 0, L.p.ctLen⟩) DecOK.ct.1, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

/-- The bytes of `dk[o : o + l]`. -/
theorem dk_slice {s₀ s : State} (hp : TPre (Y L) s₀) (h : Ctx (Y L) s₀ s) {o l : Nat} (hl : o + l ≤ L.p.dkLen)
    (hb : (Y L).ok ⟨0, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((dk L s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨0, o, l⟩) hb rfl, dk_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨0, o, l⟩) hb, Buf.addr_eq hp (b := ⟨0, 0, L.p.dkLen⟩) DecOK.ct.2.1, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

/-- `u'[i]` and `ŝ[i]`, then `c`. -/
theorem uS_piece [CeOK L] (j : Nat) (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D3 L j) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D L j) Q
      (.seq (ddK L 3 L.p.du (bCU L j) (bA L)) <| .seq (nttC 3 (bA L) (bNS L)) <|
        .seq (dec12C 3 ⟨0, 384 * j, 384⟩ (bT L)) c) := by
  obtain ⟨o₁, o₂, o₃, o₄⟩ := DecOK.dec j hj
  obtain ⟨k₁, k₂, k₃, k₄, k₅, -⟩ := DecOK.keep (L := L)
  refine Piece.seq (B := D1 L j) (ddK_piece (Y := Y L) L.p.du (.inl rfl) 1 (32 * L.p.du * j) 3 L.eA o₃ (by rdecide)
    (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨h.keep hp (by rdecide) k₁ fr h', ?_⟩) ?_
  · rw [ct_slice hp h.ctx ?_ o₁] at post
    · exact post
    · have := DecOK.ct (L := L)
      have : 32 * L.p.du * j + 32 * L.p.du ≤ 32 * L.p.du * L.p.k := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega
  refine Piece.seq (B := D2 L j) (inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 L.eA 3 L.eNS k₃
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by rdecide) k₂ fr h', by rw [h.u.2] at post; exact post⟩) ?_
  refine Piece.seq (dec12C_piece (Y := Y L) 0 (384 * j) 3 L.eT o₄ (by rdecide) (by yd_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨⟨h.keep hp (by rdecide) k₄ fr h',
      polyIs_congr (Top.keep hp (by rdecide) (b := bA L) k₅ fr) h.u⟩, ?_⟩) hc
  rw [dk_slice hp h.ctx (by unfold Params.dkLen; omega_using [hj]) o₂] at post
  rw [dS, dcS, KPke.dkPke, slice_take _ (show 384 * j + 384 ≤ 384 * L.p.k by omega_using [hj])]
  exact post

/-- Term 0: `w ← ŝ[0] ×_T NTT(u'[0])`. -/
theorem term0_piece [CeOK L] (hk : 0 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D L 0) (D L 1) (decTerm L 0) :=
  uS_piece 0 hk (mulC_piece (Y := Y L) 3 L.eU 3 L.eT 3 L.eA 3 L.eNS DecOK.mul.1
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩)
    fun s₀ s s' hp h h' fr post => ⟨h', fun _ => ⟨post.1, by rw [post.2, h.t.2, h.u.2]; rfl⟩⟩)

/-- Term `j + 1`: `w ← w + ŝ[j + 1] ×_T NTT(u'[j + 1])`. -/
theorem term_piece [CeOK L] (j : Nat) (hj : j + 1 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D L (j + 1)) (D L (j + 2)) (decTerm L (j + 1)) := by
  obtain ⟨-, -, -, -, -, k₆, k₇⟩ := DecOK.keep (L := L)
  refine uS_piece (j + 1) hj (.seq (B := D4 L (j + 1)) (mulC_piece (Y := Y L) 3 L.eP 3 L.eT 3 L.eA 3 L.eNS
    DecOK.mul.2 (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by rdecide) k₆ fr h', by rw [h.t.2, h.u.2] at post; exact post⟩) ?_)
  refine accC_piece add_verified add_nosp add_stack 3 L.eU 3 L.eP k₇ (by rdecide) (by yd_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.w (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  refine ⟨h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, (h.w (Nat.succ_pos _)).2, h.p.2]
  rfl

/-- `NTT⁻¹(w)`. -/
structure E1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  w : PolyIs s.mem (Buf.addr s₀ (bW L)) (nttInv (partD L s₀ L.p.k))

/-- And `v'`. -/
structure E2 (L : KemLay) (s₀ s : State) : Prop extends E1 L s₀ s where
  v : PolyIs s.mem (Buf.addr s₀ (bE L)) (KPke.dcV L.p (ct L s₀))

/-- `v' - NTT⁻¹(w)`. -/
structure E3 (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  v : PolyIs s.mem (Buf.addr s₀ (bE L)) (sub (KPke.dcV L.p (ct L s₀)) (nttInv (partD L s₀ L.p.k)))

/-- After `m'` is computed. -/
structure DM (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  m : bytesAt s.mem (Buf.addr s₀ (bM L)) 32 = mD L s₀

/-- K-PKE.Decrypt(dk_PKE, c). -/
theorem decrypt_piece [CeOK L] (hk : 0 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Ctx (Y L)) (DM L) (decrypt L) := by
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆⟩ := DecOK.v (L := L)
  refine (Piece.seqs0 (P := D L) L.p.k (fun j hj => match j, hj with
    | 0, _ => term0_piece hk
    | j + 1, hj => term_piece j hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := E1 L) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack 3 L.eU 3 L.eNS v₁
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, (h.w hk).1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [(h.w hk).2] at post; exact post⟩) ?_
  refine Piece.seq (B := E2 L) (ddK_piece (Y := Y L) L.p.dv (.inr rfl) 1 (32 * L.p.du * L.p.k) 3 L.eE v₂
    (by rdecide) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', polyIs_congr (Top.keep hp (by rdecide) (b := bW L) v₄ fr) h.w⟩, ?_⟩) ?_
  · rw [ct_slice hp h.ctx DecOK.ct.2.2 v₃] at post; exact post
  refine Piece.seq (B := E3 L) (accC_piece sub_verified sub_nosp sub_stack 3 L.eE 3 L.eU v₅ (by rdecide)
    (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.v.1, h.w.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [h.v.2, h.w.2] at post; exact post⟩) ?_
  refine ceC_piece (Y := Y L) ce768 1 (by decide) 3 L.eE 3 L.eM v₆ (by rdecide) (by yd_taint)
    (fun _ _ _ h => ⟨h.ctx, h.v.1⟩) fun s₀ s s' hp h h' fr post => ⟨h', ?_⟩
  rw [show Buf.addr s₀ (bM L) = Buf.addr s₀ ⟨3, L.eM, 32 * 1⟩ from rfl, post, h.v.2, mD_eq, KPke.decM,
    KPke.kpkeDecrypt_eq]

end VG.Proof.MlKem.X86.Decaps

end

end

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

@[expose] public section

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3Suffix shakeSuffix)

/-- The facts of the layout that decapsulation uses beyond K-PKE. -/
class DecapsOK (L : KemLay) : Prop where
  ekc : ((Y L).ok ⟨0, 384 * L.p.k, L.p.ekLen⟩ && (Y L).okW ⟨3, L.eEK, L.p.ekLen⟩ &&
    (Y L).sep ⟨0, 384 * L.p.k, L.p.ekLen⟩ ⟨3, L.eEK, L.p.ekLen⟩) = true
  ek4 : 4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ctLen < 2 ^ 32
  aEM : (Y L).apart (bM L) [⟨3, L.eEK, L.p.ekLen⟩] = true
  g : ((Y L).okW ⟨3, L.eST, 200⟩ && (Y L).okW ⟨3, L.eWK, 640⟩ && (Y L).ok (Enc.bM L (Y L).sc) &&
    (Y L).ok ⟨0, 768 * L.p.k + 32, 32⟩ && (Y L).okW (Enc.bKR L (Y L).sc) &&
    (Y L).sep ⟨3, L.eST, 200⟩ ⟨3, L.eWK, 640⟩ && (Y L).sep (Enc.bM L (Y L).sc) ⟨3, L.eST, 200⟩ &&
    (Y L).sep (Enc.bM L (Y L).sc) ⟨3, L.eWK, 640⟩ && (Y L).sep ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eST, 200⟩ &&
    (Y L).sep ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eWK, 640⟩ && (Y L).sep ⟨3, L.eST, 200⟩ (Enc.bKR L (Y L).sc) &&
    (Y L).sep (Enc.bKR L (Y L).sc) ⟨3, L.eWK, 640⟩) = true
  aG : (Y L).apart (Enc.bEK L (Y L).sc) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, Enc.bKR L (Y L).sc] = true ∧
    (Y L).apart (Enc.bM L (Y L).sc) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, Enc.bKR L (Y L).sc] = true ∧
    (Y L).ok ⟨0, 768 * L.p.k + 32, 32⟩ = true ∧ (Y L).ok ⟨0, 768 * L.p.k + 64, 32⟩ = true ∧
    (Y L).ok ⟨0, 384 * L.p.k, L.p.ekLen⟩ = true
  j : ((Y L).okW ⟨3, L.eST, 200⟩ && (Y L).okW ⟨3, L.eWK, 640⟩ && (Y L).ok ⟨0, 768 * L.p.k + 64, 32⟩ &&
    (Y L).ok ⟨1, 0, L.p.ctLen⟩ && (Y L).okW (bKB L) && (Y L).sep ⟨3, L.eST, 200⟩ ⟨3, L.eWK, 640⟩ &&
    (Y L).sep ⟨0, 768 * L.p.k + 64, 32⟩ ⟨3, L.eST, 200⟩ && (Y L).sep ⟨0, 768 * L.p.k + 64, 32⟩ ⟨3, L.eWK, 640⟩ &&
    (Y L).sep ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eST, 200⟩ && (Y L).sep ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eWK, 640⟩ &&
    (Y L).sep ⟨3, L.eST, 200⟩ (bKB L) && (Y L).sep (bKB L) ⟨3, L.eWK, 640⟩) = true
  dJ : Enc.safe L (Y L) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, bKB L] = true ∧
    (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, bKB L] = true
  dNil : Enc.safe L (Y L) [] = true ∧ (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [] = true
  dKey : Enc.safe L (Y L) [bKey] = true ∧
    (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [bKey] = true ∧
    (Y L).apart (bC L) [bKey] = true
  acc : (Y L).ok ⟨3, L.eACC, 4⟩ = true

variable {L : KemLay}

/-- After `ek` is copied from `dk`. -/
structure G1 (L : KemLay) (s₀ s : State) : Prop extends DM L s₀ s where
  ekc : bytesAt s.mem (Buf.addr s₀ (Enc.bEK L (Y L).sc)) L.p.ekLen = ekD L s₀

/-- `m'` decrypted, and the inputs of the re-encryption, then `c`. -/
theorem start_piece [CeOK L] [DecOK L] [DecapsOK L] (hk : 0 < L.p.k) {Q : State → State → Prop}
    {c : Prog isa} (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Enc.Base L (Y L) (I L)) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <| .seq (decrypt L) <|
        .seq (copyW 3 ⟨0, 384 * L.p.k, L.p.ekLen⟩ ⟨3, L.eEK, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (hash2 3 L.eST L.eWK 72 6 ⟨3, L.eM, 32⟩ ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eKR, 64⟩) c) := by
  obtain ⟨e₁, e₂, e₃, -⟩ := DecapsOK.ek4 (L := L)
  obtain ⟨g₁, g₂, g₃, -, g₅⟩ := DecapsOK.aG (L := L)
  refine Piece.seq (ldsc_piece (Y := Y L) (by yd_taint)) ?_
  refine Piece.seq (decrypt_piece hk) ?_
  refine Piece.seq (B := G1 L) (copyW_piece' (Y := Y L) 0 (384 * L.p.k) 3 L.eEK (L.p.ekLen / 4) L.p.ekLen e₁ e₂ e₃
    DecapsOK.ekc (by yd_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', by rw [keepBytes hp (N := 0) (by rdecide) DecapsOK.aEM (fr1 fr)]; exact h.m⟩, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨3, L.eEK, L.p.ekLen⟩) L.p.ekLen = _
    rw [post, ekD_eq]
    exact dk_slice hp h.ctx (by unfold Params.ekLen Params.dkLen; omega_using []) g₅
  refine Piece.seq (hash2_piece (Y := Y L) L.eST L.eWK 72 6 (Enc.bM L (Y L).sc) ⟨0, 768 * L.p.k + 32, 32⟩
    (Enc.bKR L (Y L).sc) rate72 DecapsOK.g (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yd_taint)
    (by yd_taint) (by yd_taint) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨h', by rw [keepBytes hp (by rdecide) g₁ fr]; exact h.ekc,
        by rw [keepBytes hp (by rdecide) g₂ fr]; exact h.m, ?_⟩) hc
  rw [out, dk_slice hp h.ctx (by unfold Params.dkLen; omega_using []) g₃, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from
    sha3Suffix32, ← padded, ← sha3_512_eq]
  show _ = krD L s₀
  rw [krD_eq, ← h.m]
  rfl

theorem done_keep {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (Y L).stk)
    (hs : Enc.safe L (Y L) bs = true)
    (hc : (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : Enc.Done L (Y L) (I L) s₀ s) (c : Ctx (Y L) s₀ s') :
    Enc.Done L (Y L) (I L) s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, by rw [keepBytes hp hM hc fr]; exact h.cv⟩

/-- `K̄ = J(z ‖ c)`. -/
abbrev kbar (L : KemLay) (s₀ : State) : List Byte := J (KPke.dkZ L.p (dk L s₀) ++ ct L s₀)

/-- After `K̄` is hashed. -/
structure J1 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (Y L) (I L) s₀ s where
  kb : bytesAt s.mem (Buf.addr s₀ (bKB L)) 32 = kbar L s₀

/-- After `c` and `c'` are compared. -/
structure J2 (L : KemLay) (s₀ s : State) : Prop extends J1 L s₀ s where
  ebx : s.gpr .ebx = mask (ct L s₀ = bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen)

/-- After `K'` or `K̄` is selected into `key`. -/
structure J3 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (Y L) (I L) s₀ s where
  key : bytesAt s.mem (Buf.addr s₀ bKey) 32 =
    if ct L s₀ = bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen then (krD L s₀).take 32 else kbar L s₀

/-- After `eACC` is loaded, to be returned. -/
structure Fin (L : KemLay) (s₀ s : State) : Prop extends J3 L s₀ s where
  eax : s.gpr .eax = Enc.accE L (Y L) s₀ s

theorem selB_mask (p : Prop) [Decidable p] (a b : Byte) :
    selB ((mask p).setWidth 8) a b = if p then a else b := by
  unfold mask
  split
  · rw [show (BitVec.setWidth 8 (0xffffffff : BitVec 32)) = BitVec.allOnes 8 by decide, selB, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rw [show (BitVec.setWidth 8 (0 : BitVec 32)) = 0#8 by decide, selB, BitVec.and_zero, BitVec.xor_zero]

/-- The key, from the re-encryption. -/
theorem fin_piece [DecOK L] [CmpOK L] [DecapsOK L] :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Enc.Done L (Y L) (I L)) (Fin L)
      (.seq (hash2 3 L.eST L.eWK 136 0x1f ⟨0, 768 * L.p.k + 64, 32⟩ ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eH, 32⟩) <|
        .seq (cmpC L) <| .seq (selC L) (.block [.mov .eax (.mem (at_ .esi L.eACC))])) := by
  obtain ⟨-, -, -, g₄, -⟩ := DecapsOK.aG (L := L)
  obtain ⟨-, -, -, hN⟩ := DecapsOK.ek4 (L := L)
  obtain ⟨d₁, d₂⟩ := DecapsOK.dJ (L := L)
  obtain ⟨n₁, n₂⟩ := DecapsOK.dNil (L := L)
  obtain ⟨k₁, k₂, k₃⟩ := DecapsOK.dKey (L := L)
  refine Piece.seq (B := J1 L) (hash2_piece (Y := Y L) L.eST L.eWK 136 0x1f ⟨0, 768 * L.p.k + 64, 32⟩
    ⟨1, 0, L.p.ctLen⟩ (bKB L) rate136 DecapsOK.j (by rdecide) (by rdecide) hN (by rdecide) (by taint_rfl) (by yd_taint)
    (by yd_taint) (by yd_taint) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨done_keep hp (by rdecide) d₁ d₂ fr h h', ?_⟩) ?_
  · rw [out, dk_slice hp h.ctx (by unfold Params.dkLen; omega_using []) g₄, ct_slice hp h.ctx (by omega_using []) DecOK.ct.1,
      List.drop_zero, List.take_of_length_le (l := ct L s₀) (by rw [ct_eq, bytesAt_length]),
      show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32, ← padded, ← J_eq]
    show _ = J (KPke.dkZ L.p (dk L s₀) ++ ct L s₀)
    rfl
  refine Piece.seq (B := J2 L) (cmp_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' e =>
    ⟨⟨done_keep hp (bs := []) (M := 0) (by rdecide) n₁ n₂ (m' ▸ Frame.refl _ _) h.toDone h',
      by rw [m']; exact h.kb⟩, by rw [e, m']⟩) ?_
  refine Piece.seq (B := J3 L) (sel_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
    ⟨done_keep hp (M := 0) (by rdecide) k₁ k₂ (fr1 fr) h.toDone h', ?_⟩) ?_
  · have kc : bytesAt s'.mem (Buf.addr s₀ (bC L)) L.p.ctLen = bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen :=
      keepBytes hp (N := 0) (by rdecide) k₃ (fr1 fr)
    have lk : (krD L s₀).length = 64 := by rw [show krD L s₀ = (I L).kr s₀ from rfl, ← h.kr, bytesAt_length]
    have lj : (kbar L s₀).length = 32 := J_length _
    rw [kc]
    refine bytesAt_eq (by split <;> simp [lk, lj]) fun j hj => ?_
    rw [out j hj, h.ebx, selB_mask]
    have kk : (krD L s₀).take 32 = bytesAt s.mem (Buf.addr s₀ (bK L)) 32 := by
      rw [show krD L s₀ = (I L).kr s₀ from rfl, ← h.kr, bytesAt_take _ _ (show 32 ≤ 64 by decide)]; rfl
    split
    · simp only [kk, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
    · simp only [← h.kb, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
  exact ld32_piece (Y := Y L) L.eACC DecapsOK.acc (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨⟨done_keep hp (bs := []) (M := 0) (by rdecide) n₁ n₂
      (m' ▸ Frame.refl _ _) h.toDone h', by rw [m']; exact h.key⟩,
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']⟩

theorem body_piece [CeOK L] [DecOK L] [CmpOK L] [DecapsOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L]
    [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) (Fin L) (decapsBody L) :=
  start_piece hk <| .seq (Enc.encrypt_piece (hS L) (hρ L) hk) fin_piece

theorem piece [CeOK L] [DecOK L] [CmpOK L] [DecapsOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L]
    [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) (hsp : NoSp (decapsBody L)) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin L s₀) s₀ s')
      (leaf (decapsBody L)) :=
  topLeaf hsp ((body_piece hk).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- The postcondition, from the final state of the body. -/
theorem post [Enc.VOK L] (hη : L.p.η₁ = 2 ∧ L.p.η₂ = 2) {s₀ s : State} (hp : TPre (Y L) s₀) (h : Fin L s₀ s) :
    Outcome (fun iters => decapsInternal L.p iters (dk L s₀) (ct L s₀)) (Enc.accE L (Y L) s₀ s)
      (bytesAt s.mem (Buf.addr s₀ bKey) 32) := by
  have er : Enc.rE (I L) s₀ = (G (KPke.decM L.p (dk L s₀) (ct L s₀) ++ KPke.dkH L.p (dk L s₀))).2 := by
    show (krD L s₀).drop 32 = _; rw [krD_eq, mD_eq]; rfl
  have ek : Enc.ρE L (I L) s₀ = ekRho L.p (KPke.dkEk L.p (dk L s₀)) := by
    show ekRho L.p (ekD L s₀) = _; rw [ekD_eq]
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; omega_using [hk]
    refine .inr ⟨e, ?_⟩
    show decapsInternal L.p minIterations (dk L s₀) (ct L s₀) = none
    rw [Enc.mSE, ek] at hn
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (i := k % L.p.k) (j := k / L.p.k) (Nat.mod_lt _ hk0)
      (Nat.div_lt_of_lt_mul hk) hn]
    rfl
  · obtain ⟨M, hM⟩ := Enc.samples h.toDone e
    rw [ek] at hM
    refine .inl ⟨e, M, ?_⟩
    show decapsInternal L.p M (dk L s₀) (ct L s₀) = _
    have ec : bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen =
        KPke.ct L.p (Enc.aE L (I L) s₀) ((I L).ek s₀) ((I L).m s₀) (Enc.rE (I L) s₀) :=
      Enc.ct_eq (hS L) hp h.toDone e
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some hη hM, h.key, ec, er,
      show Enc.aE L (I L) s₀ = fun i j => sv (matSeed (ekRho L.p (KPke.dkEk L.p (dk L s₀))) i j) by rw [← ek],
      show (I L).ek s₀ = KPke.dkEk L.p (dk L s₀) from ekD_eq L s₀,
      show (I L).m s₀ = KPke.decM L.p (dk L s₀) (ct L s₀) from mD_eq L s₀, krD_eq, mD_eq]
    rfl

end VG.Proof.MlKem.X86.Decaps
