module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignNonce
import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Common
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_ed448_sign_cached` on PPC64LE: the challenge and `S`

From `S3`: `H(dom4(0, C) ‖ R ‖ A ‖ M)` into `16(F)`, reduced modulo `L`
into `320(F)` (`k`), and `S = (r + k s) mod L` into the second half of `out`
(`challenge_ok`, `S4`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea ArgsKeep args5_ok)
open VG.Spec.Ed448 (bytesAt)

/-- `k`. -/
abbrev kB (s : State) : List Byte :=
  Spec.Ed448.scalarReduce (Spec.Ed448.hash (ctxB s) (RB s ++ pkB s ++ msgB s))

/-- After `S`. -/
structure S4 (s t : State) : Prop where
  inv : SInv s t
  R : bytesAt t.mem (s.gpr .r3) 57 = RB s
  S : ∃ σ, Spec.Ed448.decodeLE σ = Spec.Ed448.prune (hS s) ∧
    bytesAt t.mem (s.gpr .r3 + BitVec.ofNat 64 57) 57 = Spec.Ed448.scalarMulAdd (rB s) (kB s) σ

theorem challenge_ok {s t : State} (hp : SignPre s) (h : S3 s t) : WP isa signChallenge t (S4 s) := by
  obtain ⟨cP, cB⟩ := ctxPiece hp h.inv
  obtain ⟨mP, mB⟩ := msgPiece hp h.inv
  obtain ⟨hP, hB⟩ := fPiece0 hp h.inv
  have g20 : t.gpr .r20 = s.gpr .r3 := h.inv.regs _ (by decide)
  have g22 : t.gpr .r24 = s.gpr .r5 := h.inv.regs _ (by decide)
  have g29 : t.gpr .r22 = s.gpr .r10 := h.inv.regs _ (by decide)
  have g30 : t.gpr .r21 = sF s := h.inv.regs _ (by decide)
  have hO57 : Region.Sub ⟨s.gpr .r3, 57⟩ (oR s) := Region.sub_prefix (by decide)
  have oP : PieceOk (s.gpr .r10) t ⟨.r20, 0, .imm 57⟩ :=
    pieceOk_of (R := ⟨s.gpr .r3, 57⟩) (by simp only [Piece.R, Piece.addr, Len.val, g20, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide) (cov_right (cov_in0 (fO hp h.inv) (by decide)))
      (hp.oC.sub_left hO57) (by rw [h.inv.sp]; exact hp.bO.sub_right hO57)
  have oB : Piece.bytes t.mem t.gpr ⟨.r20, 0, .imm 57⟩ = RB s := by
    simp only [Piece.bytes, Piece.addr, Len.val, g20, BitVec.add_zero]; exact h.R
  have pP : PieceOk (s.gpr .r10) t ⟨.r24, 0, .imm 57⟩ :=
    pieceOk_of (R := pkR s) (by simp only [Piece.R, Piece.addr, Len.val, g22, BitVec.add_zero])
      (by decide) (by decide) (show 57 < 2 ^ 15 by decide)
      (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
      hp.cP.symm (by rw [h.inv.sp]; exact hp.bP)
  have pB : Piece.bytes t.mem t.gpr ⟨.r24, 0, .imm 57⟩ = pkB s := by
    have := sign_keep hp h.inv (R := pkR s) (.inr (.inl rfl))
    simp only [Piece.bytes, Piece.addr, Len.val, g22, BitVec.add_zero]; exact this
  unfold signChallenge
  simp only [dom4Pieces, List.cons_append, List.nil_append]
  refine WP.seq (WP.mono (hash_ok (sc := .r22) (f := .r21) (o := 16) (out := sF s + BitVec.ofNat 64 16)
    (by decide) (by decide) (by decide) g29 (by rw [g30]) (kenv hp h.inv) (by simp) (fun p hp' => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl
      · exact hP
      · exact cP
      · exact oP
      · exact pP
      · exact mP) (cov_in (fF hp h.inv) (by decide))
    (fsc hp (by decide)) (by rw [h.inv.sp]; exact fbelow hp (by decide))) fun t₂ ⟨k₂, d₂⟩ => ?_)
  have h₂ := h.inv.hash hp (by decide) k₂
  have hh : bytesAt t₂.mem (sF s + BitVec.ofNat 64 16) 114 =
      Spec.Ed448.hash (ctxB s) (RB s ++ pkB s ++ msgB s) := by
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, hB, cB, oB, pB,
      mB, h.hdr, bytesAt_sha3] at d₂
    rw [d₂, show (s.gpr .r7).toNat = (ctxB s).length by simp [bytesAt], ← List.append_assoc, List.append_assoc (RB s)]
    exact dom4_hash _ _
  -- `k`.
  refine reduceF_ok hp h₂ (o := 320) (by decide) (by decide) fun t₃ h₃ f₃ r₃ => ?_
  rw [hh] at r₃
  -- `S`.
  have g20' : t₃.gpr .r20 = s.gpr .r3 := h₃.regs _ (by decide)
  have g29' : t₃.gpr .r22 = s.gpr .r10 := h₃.regs _ (by decide)
  have g30' : t₃.gpr .r21 = sF s := h₃.regs _ (by decide)
  unfold mov
  refine WP.seq (args5_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) fun u hu a3 a4 a5 a6 a7 => ?_)
  rw [g20'] at a3
  rw [g30'] at a4 a5 a6
  rw [g29', BitVec.add_zero] at a7
  have hOs : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 57, 57⟩ (oR s) := osub (by decide)
  have hW : PPC64LE.Covers [⟨s.gpr .r3 + BitVec.ofNat 64 57, 57⟩, scR s] u.wr := by
    rw [hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact cov_in (fO hp h₃) (by decide) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact ⟨_, fC hp h₃, hc⟩
  have hR : PPC64LE.Covers [⟨sF s + BitVec.ofNat 64 256, 57⟩, ⟨sF s + BitVec.ofNat 64 320, 57⟩,
      ⟨sF s + BitVec.ofNat 64 136, 57⟩] (u.rd ++ u.wr) := by
    rw [hu.rd, hu.wr]
    intro a n ⟨r, hr, hc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact cov_right (cov_in (fF hp h₃) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right (cov_in (fF hp h₃) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
    · exact cov_right (cov_in (fF hp h₃) (by decide)) a n ⟨_, List.mem_singleton_self _, hc⟩
  refine mulAdd_call a3 a4 a5 a6 a7 (hp.oC.sub_left hOs) (fsc hp (by decide)) (fsc hp (by decide))
    (fsc hp (by decide)) (cov_app hR (cov_right hW)) hW fun t₄ rd₄ wr₄ sp₄ f₄ cs₄ b₄ => ?_
  rw [hu.mem] at f₄ b₄
  have h₄ : SInv s t₄ := h₃.step signRegs_pres (rd₄.trans hu.rd) (wr₄.trans hu.wr) (sp₄.trans hu.sp)
    (fun r hr => (cs₄ r hr).trans (hu.pres r hr)) f₄ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨oR s, by simp, hOs⟩
      · exact ⟨scR s, by simp, fun _ h => h⟩) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact oslot hp (by decide)
      · exact cslot hp
  -- What the steps keep.
  have kr : ∀ {d n : Nat}, d + n ≤ 464 → (d + n ≤ 320 ∨ 377 ≤ d) →
      bytesAt t₃.mem (sF s + BitVec.ofNat 64 d) n = bytesAt t₂.mem (sF s + BitVec.ofNat 64 d) n :=
    fun hdn hd => bytes_keep f₃ (by omega) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact fsc hp hdn
  have e256 : bytesAt t₃.mem (sF s + BitVec.ofNat 64 256) 57 = rB s := by
    rw [kr (by decide) (by decide), keep_hash hp h.inv (o := 16) (d := 256) (n := 57) (by decide) (by decide)
      (by decide) k₂, h.r]
  have e136 : Spec.Ed448.decodeLE (bytesAt t₃.mem (sF s + BitVec.ofNat 64 136) 57) = Spec.Ed448.prune (hS s) := by
    rw [kr (by decide) (by decide), keep_hash hp h.inv (o := 16) (d := 136) (n := 57) (by decide) (by decide)
      (by decide) k₂, h.sc]
  have hO0 : ∀ {m m' : Mem} {W : List Region}, Frame W m m' →
      (∀ r ∈ W, Region.Disjoint ⟨s.gpr .r3, 57⟩ r) → bytesAt m' (s.gpr .r3) 57 = bytesAt m (s.gpr .r3) 57 :=
    fun hf hd => bytes_keep hf (by decide) hd
  refine ⟨h₄, ?_, ⟨_, e136, by rw [b₄, e256, r₃]⟩⟩
  rw [hO0 f₄ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using Offset.disjoint (s.gpr .r3) (d := 0) (n := 57) (e := 57) (k := 57) (.inl (by decide))
          (by decide) (by decide)
      · exact hp.oC.sub_left hO57,
    hO0 f₃ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (hp.oF.sub_left hO57).sub_right (fsub (by decide))
      · exact hp.oC.sub_left hO57,
    hO0 k₂.frame fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hp.oF.sub_left hO57).sub_right (fsub (by decide))
      · exact hp.oC.sub_left hO57
      · rw [h.inv.sp]; exact (hp.bO.sub_right hO57).symm, h.R]

end VG.Proof.Ed448.PPC64LE.Whole
