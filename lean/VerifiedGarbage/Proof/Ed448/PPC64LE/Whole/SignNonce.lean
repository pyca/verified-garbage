module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignSteps
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
public import VerifiedGarbage.Proof.Ed448.Ref

/-!
# `vg_ed448_sign_cached` on PPC64LE: the nonce and `R`

From `S2`: `H(dom4(0, C) ‖ prefix ‖ M)` into `16(F)`, reduced modulo `L`
into `256(F)` (`r`), and `R = [r]B` into the first half of `out`
(`nonce_ok`, `S3`). `dom4_hash` is the hash of the pieces the code absorbs.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea ArgsKeep args3_ok)
open VG.Spec.Ed448 (bytesAt)

section
variable (s : State)

/-- The inputs. -/
abbrev seedB : List Byte := bytesAt s.mem (s.gpr .r4) 57
abbrev ctxB : List Byte := bytesAt s.mem (s.gpr .r6) (s.gpr .r7).toNat
abbrev msgB : List Byte := bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat
abbrev pkB : List Byte := bytesAt s.mem (s.gpr .r5) 57

/-- `SHAKE256(seed, 114)`, `r` and `R`. -/
abbrev hS : List Byte := Spec.Sha3.shake256 (seedB s) 114
abbrev rB : List Byte := Spec.Ed448.scalarReduce (Spec.Ed448.hash (ctxB s) ((hS s).drop 57 ++ msgB s))
abbrev RB : List Byte := Spec.Ed448.scalarBase (rB s)

end

/-- `dom4(0, C) ‖ x`, as the code absorbs it: the header, the context and `x`. -/
theorem dom4_hash (ctx x : List Byte) :
    Spec.Sha3.shake256 (hdrBytes ctx.length ++ ctx ++ x) 114 = Spec.Ed448.hash ctx x := by
  rw [Spec.Ed448.hash, dom4_eq, List.append_assoc]

/-- After `r` and `R`. -/
structure S3 (s t : State) : Prop where
  inv : SInv s t
  hdr : bytesAt t.mem (sF s) 10 = hdrBytes (s.gpr .r7).toNat
  sc : Spec.Ed448.decodeLE (bytesAt t.mem (sF s + BitVec.ofNat 64 136) 57) = Spec.Ed448.prune (hS s)
  r : bytesAt t.mem (sF s + BitVec.ofNat 64 256) 57 = rB s
  R : bytesAt t.mem (s.gpr .r3) 57 = RB s

section
variable {s : State} (hp : SignPre s)
include hp

theorem ctxPiece {t : State} (h : SInv s t) :
    PieceOk (s.gpr .r10) t ⟨.r25, 0, .reg .r28⟩ ∧ Piece.bytes t.mem t.gpr ⟨.r25, 0, .reg .r28⟩ = ctxB s := by
  have g23 : t.gpr .r25 = s.gpr .r6 := h.regs _ (by decide)
  have g24 : t.gpr .r28 = s.gpr .r7 := h.regs _ (by decide)
  have e : Piece.R t.gpr ⟨.r25, 0, .reg .r28⟩ = cxR s := by
    simp only [Piece.R, Piece.addr, Len.val, g23, g24, BitVec.add_zero]
  refine ⟨pieceOk_of e (by decide) (by decide) (show Reg.r28 ∈ preserved by decide)
    (by rw [h.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
    hp.cX.symm (by rw [h.sp]; exact hp.bX), ?_⟩
  have := sign_keep hp h (R := cxR s) (.inr (.inr (.inl rfl)))
  simp only [Piece.bytes, Piece.addr, Len.val, g23, g24, BitVec.add_zero]
  exact this

theorem msgPiece {t : State} (h : SInv s t) :
    PieceOk (s.gpr .r10) t ⟨.r29, 0, .reg .r30⟩ ∧ Piece.bytes t.mem t.gpr ⟨.r29, 0, .reg .r30⟩ = msgB s := by
  have g25 : t.gpr .r29 = s.gpr .r8 := h.regs _ (by decide)
  have g28 : t.gpr .r30 = s.gpr .r9 := h.regs _ (by decide)
  have e : Piece.R t.gpr ⟨.r29, 0, .reg .r30⟩ = msR s := by
    simp only [Piece.R, Piece.addr, Len.val, g25, g28, BitVec.add_zero]
  refine ⟨pieceOk_of e (by decide) (by decide) (show Reg.r30 ∈ preserved by decide)
    (by rw [h.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
    hp.cM.symm (by rw [h.sp]; exact hp.bM), ?_⟩
  have := sign_keep hp h (R := msR s) (.inr (.inr (.inr rfl)))
  simp only [Piece.bytes, Piece.addr, Len.val, g25, g28, BitVec.add_zero]
  exact this

/-- A piece of `F`. -/
theorem fPiece {t : State} (h : SInv s t) {d n : Nat} (hd : d < 2 ^ 15) (hn : n < 2 ^ 15) (hdn : d + n ≤ 464) :
    PieceOk (s.gpr .r10) t ⟨.r21, d, .imm n⟩ ∧
      Piece.bytes t.mem t.gpr ⟨.r21, d, .imm n⟩ = bytesAt t.mem (sF s + BitVec.ofNat 64 d) n := by
  have g30 : t.gpr .r21 = sF s := h.regs _ (by decide)
  have e : Piece.R t.gpr ⟨.r21, d, .imm n⟩ = ⟨sF s + BitVec.ofNat 64 d, n⟩ := by
    simp only [Piece.R, Piece.addr, Len.val, g30]
  refine ⟨pieceOk_of e (show Reg.r21 ∈ preserved by decide) hd hn (cov_right (cov_in (fF hp h) hdn)) (fsc hp hdn)
    (by rw [h.sp]; exact fbelow hp hdn), ?_⟩
  simp only [Piece.bytes, Piece.addr, Len.val, g30]; rfl

theorem fPiece0 {t : State} (h : SInv s t) :
    PieceOk (s.gpr .r10) t ⟨.r21, 0, .imm 10⟩ ∧
      Piece.bytes t.mem t.gpr ⟨.r21, 0, .imm 10⟩ = bytesAt t.mem (sF s) 10 := by
  have := fPiece hp h (d := 0) (n := 10) (by decide) (by decide) (by decide)
  rwa [BitVec.add_zero] at this

/-- `scalar_reduce` of the hash at `16(F)` into `o(F)`. -/
theorem reduceF_ok {t : State} (h : SInv s t) {o : Nat} (ho : o + 57 ≤ 384) (ho' : 130 ≤ o) {rest : Prog isa}
    {Q : State → Prop}
    (k : ∀ t', SInv s t' →
      Frame [⟨sF s + BitVec.ofNat 64 o, 57⟩, scR s] t.mem t'.mem →
      bytesAt t'.mem (sF s + BitVec.ofNat 64 o) 57 =
        Spec.Ed448.scalarReduce (bytesAt t.mem (sF s + BitVec.ofNat 64 16) 114) → WP isa rest t' Q) :
    WP isa (.seq (.block [.addi .r3 .r21 o, .addi .r4 .r21 16, mov .r5 .r22])
      (.seq (.call "vg_ed448_scalar_reduce" Impl.Ed448.PPC64LE.scalarReduce) rest)) t Q := by
  have g29 : t.gpr .r22 = s.gpr .r10 := h.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.regs _ (by decide)
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by omega) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u hu a3 a4 a5 => ?_)
  rw [g30] at a3 a4
  rw [g29, BitVec.add_zero] at a5
  have hW : PPC64LE.Covers [⟨sF s + BitVec.ofNat 64 o, 57⟩, scR s] u.wr := by
    rw [hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_in (fF hp h) (by omega) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, fC hp h, hc⟩
  refine WP.seq (reduce_call a3 a4 a5 (Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)) (fsc hp (by omega))
    (fsc hp (by decide)) (cov_app (cov_right (by rw [hu.wr]; exact cov_in (fF hp h) (by decide))) (cov_right hW)) hW
    fun t' rd' wr' sp' f' cs' r' => ?_)
  rw [hu.mem] at f' r'
  refine k t' (h.step signRegs_pres (rd'.trans hu.rd) (wr'.trans hu.wr) (sp'.trans hu.sp)
    (fun r hr => (cs' r hr).trans (hu.pres r hr)) f' (fun r hr => ?_) fun r hr => ?_) f' r'
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨fR s, by simp, fsub (by omega)⟩
    · exact ⟨scR s, by simp, fun _ h => h⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact fslot ho
    · exact cslot hp

end

theorem nonce_ok (hl : Proof.Ed448.BaseLadder2Ok) {s t : State} (hp : SignPre s) (h : S2 s t) : WP isa signNonce t (S3 s) := by
  obtain ⟨cP, cB⟩ := ctxPiece hp h.inv
  obtain ⟨mP, mB⟩ := msgPiece hp h.inv
  obtain ⟨hP, hB⟩ := fPiece0 hp h.inv
  obtain ⟨pP, pB⟩ := fPiece hp h.inv (d := 193) (n := 57) (by decide) (by decide) (by decide)
  have g29 : t.gpr .r22 = s.gpr .r10 := h.inv.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.inv.regs _ (by decide)
  unfold signNonce
  simp only [dom4Pieces, List.cons_append, List.nil_append]
  refine WP.seq (WP.mono (hash_ok (sc := .r22) (f := .r21) (o := 16) (out := sF s + BitVec.ofNat 64 16)
    (by decide) (by decide) (by decide) g29 (by rw [g30]) (kenv hp h.inv) (by simp) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl
      · exact hP
      · exact cP
      · exact pP
      · exact mP) (cov_in (fF hp h.inv) (by decide))
    (fsc hp (by decide)) (by rw [h.inv.sp]; exact fbelow hp (by decide))) fun t₂ ⟨k₂, d₂⟩ => ?_)
  have h₂ := h.inv.hash hp (by decide) k₂
  have hh : bytesAt t₂.mem (sF s + BitVec.ofNat 64 16) 114 =
      Spec.Ed448.hash (ctxB s) ((hS s).drop 57 ++ msgB s) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, hB, cB, pB, mB,
      h.hdr, h.pre, bytesAt_sha3] at d₂
    rw [d₂, show (s.gpr .r7).toNat = (ctxB s).length by simp [bytesAt], ← List.append_assoc]
    exact dom4_hash _ _
  -- `r`.
  refine reduceF_ok hp h₂ (o := 256) (by decide) (by decide) fun t₃ h₃ f₃ r₃ => ?_
  rw [hh] at r₃
  -- `R`.
  have g20 : t₃.gpr .r20 = s.gpr .r3 := h₃.regs _ (by decide)
  have g29' : t₃.gpr .r22 = s.gpr .r10 := h₃.regs _ (by decide)
  have g30' : t₃.gpr .r21 = sF s := h₃.regs _ (by decide)
  unfold mov
  refine WP.seq (args3_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) fun u hu a3 a4 a5 => ?_)
  rw [g20, BitVec.add_zero] at a3
  rw [g30'] at a4
  rw [g29', BitVec.add_zero] at a5
  have hO57 : Region.Sub ⟨s.gpr .r3, 57⟩ (oR s) := Region.sub_prefix (by decide)
  have hW : PPC64LE.Covers [⟨s.gpr .r3, 57⟩, scR s] u.wr := by
    rw [hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_in0 (fO hp h₃) (by decide) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, fC hp h₃, hc⟩
  refine base_call hl a3 a4 a5 ((hp.oF.sub_left hO57).sub_right (fsub (by decide)))
    (hp.oC.sub_left hO57) (fsc hp (by decide))
    (cov_app (cov_right (by rw [hu.wr]; exact cov_in (fF hp h₃) (by decide))) (cov_right hW)) hW
    fun t₄ rd₄ wr₄ sp₄ f₄ cs₄ b₄ => ?_
  rw [hu.mem] at f₄ b₄
  have h₄ : SInv s t₄ := h₃.step signRegs_pres (rd₄.trans hu.rd) (wr₄.trans hu.wr) (sp₄.trans hu.sp)
    (fun r hr => (cs₄ r hr).trans (hu.pres r hr)) f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨oR s, by simp, hO57⟩
      · exact ⟨scR s, by simp, fun _ h => h⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using oslot hp (d := 0) (n := 57) (by decide)
      · exact cslot hp
  -- What the steps keep.
  have kb : ∀ {d n : Nat}, d + n ≤ 464 → bytesAt t₄.mem (sF s + BitVec.ofNat 64 d) n =
      bytesAt t₃.mem (sF s + BitVec.ofNat 64 d) n := fun hdn =>
    bytes_keep f₄ (by omega) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ((hp.oF.sub_left hO57).sub_right (fsub hdn)).symm
      · exact fsc hp hdn
  have kr : ∀ {d n : Nat}, d + n ≤ 464 → (d + n ≤ 256 ∨ 313 ≤ d) →
      bytesAt t₃.mem (sF s + BitVec.ofNat 64 d) n = bytesAt t₂.mem (sF s + BitVec.ofNat 64 d) n :=
    fun hdn hd => bytes_keep f₃ (by omega) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact fsc hp hdn
  refine ⟨h₄, ?_, ?_, ?_, by rw [b₄, r₃]⟩
  · have a := kb (d := 0) (n := 10) (by decide)
    have b := kr (d := 0) (n := 10) (by decide) (by decide)
    have c := keep_hash hp h.inv (o := 16) (d := 0) (n := 10) (by decide) (by decide) (by decide) k₂
    rw [BitVec.add_zero] at a b c
    rw [a, b, c, h.hdr]
  · rw [kb (by decide), kr (by decide) (by decide),
      keep_hash hp h.inv (o := 16) (d := 136) (n := 57) (by decide) (by decide) (by decide) k₂, h.sc]
  · rw [kb (by decide), r₃]

end VG.Proof.Ed448.PPC64LE.Whole
