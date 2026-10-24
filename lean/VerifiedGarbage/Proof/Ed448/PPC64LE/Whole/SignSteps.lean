module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.SignSetup
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Calls
public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Prune
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# `vg_ed448_sign_cached` on PPC64LE: the steps

From the setup's invariant (`S1`): `SHAKE256(seed, 114)` into `136(F)`, its
first half pruned there (`S2`, `expand_ok`); the nonce `r` reduced into
`256(F)` and `R = [r]B` into the first half of `out` (`S3`, `nonce_ok`); the
challenge `k` into `320(F)` and `S = (r + k s) mod L` into the second half of
`out` (`S4`, `challenge_ok`). The pieces of the hashes (`pieceOk_of`) and the
regions written are those of `SignPre`.
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Impl.Ed448.PPC64LE.Whole VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea)
open VG.Spec.Ed448 (bytesAt)

theorem bytesAt_sha3 (m : Mem) (p : Addr) (n : Nat) : Spec.Sha3.bytesAt m p n = bytesAt m p n := rfl

theorem pieceOk_of {t : State} {sc : Addr} {p : Piece} {R : Region} (hR : p.R t.gpr = R) (hb : p.base ∈ preserved)
    (ho : p.off < 2 ^ 15) (hl : p.len.Ok) (hc : PPC64LE.Covers [R] (t.rd ++ t.wr))
    (hd : R.Disjoint ⟨sc, 8192⟩) (hb' : (below t.sp 48).Disjoint R) : PieceOk sc t p :=
  ⟨hb, ho, hl, hR ▸ hc, hR ▸ hd, hR ▸ hb'⟩

theorem cov_in {ws : List Region} {P : Addr} {k d n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : d + n ≤ k) :
    PPC64LE.Covers [⟨P + BitVec.ofNat 64 d, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, d, rfl, h⟩

theorem cov_in0 {ws : List Region} {P : Addr} {k n : Nat} (hw : (⟨P, k⟩ : Region) ∈ ws) (h : n ≤ k) :
    PPC64LE.Covers [⟨P, n⟩] ws :=
  Covers.of_sub fun r hr => by rw [List.mem_singleton.mp hr]; exact ⟨_, hw, 0, by simp, by simpa using h⟩

theorem cov_rd {rd wr ws : List Region} (h : PPC64LE.Covers ws rd) : PPC64LE.Covers ws (rd ++ wr) :=
  fun a n hi => let ⟨r, hr, hc⟩ := h a n hi; ⟨r, List.mem_append_left _ hr, hc⟩

theorem fsub {s : State} {d n : Nat} (h : d + n ≤ 464) : Region.Sub ⟨sF s + BitVec.ofNat 64 d, n⟩ (fR s) := Offset.sub_base _ h

theorem fslot {s : State} {d n : Nat} (h : d + n ≤ 384) : (slotArea (sF s) 384 signRegs).Disjoint ⟨sF s + BitVec.ofNat 64 d, n⟩ :=
  Offset.disjoint _ (.inr h) (by decide) (by omega)

theorem osub {s : State} {d n : Nat} (h : d + n ≤ 114) : Region.Sub ⟨s.gpr .r3 + BitVec.ofNat 64 d, n⟩ (oR s) :=
  Offset.sub_base _ h

section
variable {s : State} (hp : SignPre s)
include hp

/-! ## Regions of the frame and of `out` -/

theorem fsc {d n : Nat} (h : d + n ≤ 464) : Region.Disjoint ⟨sF s + BitVec.ofNat 64 d, n⟩ (scR s) :=
  hp.cF.symm.sub_left (fsub h)

theorem fbelow {d n : Nat} (h : d + n ≤ 464) : (below s.sp 48).Disjoint ⟨sF s + BitVec.ofNat 64 d, n⟩ :=
  hp.bF.sub_right (fsub h)

theorem oslot {d n : Nat} (h : d + n ≤ 114) :
    (slotArea (sF s) 384 signRegs).Disjoint ⟨s.gpr .r3 + BitVec.ofNat 64 d, n⟩ :=
  (hp.oF.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (osub h)

theorem cslot : (slotArea (sF s) 384 signRegs).Disjoint (scR s) := hp.cF.symm.sub_left (Offset.sub_base _ (by decide))

theorem bslot : (slotArea (sF s) 384 signRegs).Disjoint (below s.sp 48) := hp.bF.symm.sub_left (Offset.sub_base _ (by decide))

theorem fF {t : State} (h : SInv s t) : (fR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp
theorem fO {t : State} (h : SInv s t) : (oR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp
theorem fC {t : State} (h : SInv s t) : (scR s) ∈ t.wr := by rw [h.wr, hp.wr]; simp

theorem kenv {t : State} (h : SInv s t) : KEnv (s.gpr .r10) t :=
  ⟨fC hp h, by rw [h.sp]; exact hp.sp, by rw [h.sp]; exact hp.bC⟩

/-- A hash into `o(F)` keeps the invariant. -/
theorem SInv.hash {t t' : State} (h : SInv s t) {o : Nat} (ho : o + 114 ≤ 384)
    (hk : Kept ([⟨sF s + BitVec.ofNat 64 o, 114⟩] ++ kW (s.gpr .r10) t.sp) t t') : SInv s t' :=
  Inv.kept h signRegs_pres hk (fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨fR s, by simp, fsub (by omega)⟩
    · exact ⟨scR s, by simp, fun _ h => h⟩
    · exact ⟨below s.sp 48, by simp, by rw [h.sp]; exact fun _ h => h⟩) fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact fslot ho
    · exact cslot hp
    · rw [h.sp]; exact bslot hp

/-- Bytes of the frame apart from what a hash into `o(F)` writes. -/
theorem keep_hash {t t' : State} (h : SInv s t) {o d n : Nat} (hd : d + n ≤ o ∨ o + 114 ≤ d)
    (ho : o + 114 ≤ 464) (hdn : d + n ≤ 464)
    (hk : Kept ([⟨sF s + BitVec.ofNat 64 o, 114⟩] ++ kW (s.gpr .r10) t.sp) t t') :
    bytesAt t'.mem (sF s + BitVec.ofNat 64 d) n = bytesAt t.mem (sF s + BitVec.ofNat 64 d) n :=
  bytes_keep hk.frame (by omega) fun r hr => by
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint _ hd (by omega) (by omega)
    · exact fsc hp hdn
    · rw [h.sp]; exact (fbelow hp hdn).symm

end

/-! ## `s` and the prefix -/

/-- After `s` and the nonce's prefix. -/
structure S2 (s t : State) : Prop where
  inv : SInv s t
  hdr : bytesAt t.mem (sF s) 10 = hdrBytes (s.gpr .r7).toNat
  sc : Spec.Ed448.decodeLE (bytesAt t.mem (sF s + BitVec.ofNat 64 136) 57) =
    Spec.Ed448.prune (Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .r4) 57) 114)
  pre : bytesAt t.mem (sF s + BitVec.ofNat 64 193) 57 = (Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .r4) 57) 114).drop 57

theorem expand_ok {s t : State} (hp : SignPre s) (h : S1 s t) : WP isa signExpand t (S2 s) := by
  have g21 : t.gpr .r21 = s.gpr .r4 := h.inv.regs _ (by decide)
  have g29 : t.gpr .r29 = s.gpr .r10 := h.inv.regs _ (by decide)
  have g30 : t.gpr .r30 = sF s := h.inv.regs _ (by decide)
  have pk : PieceOk (s.gpr .r10) t ⟨.r21, 0, .imm 57⟩ :=
    pieceOk_of (R := sdR s) (by simp only [Piece.R, Piece.addr, Len.val, g21, BitVec.add_zero]) (by decide)
      (by decide) (show 57 < 2 ^ 15 by decide)
      (by rw [h.inv.rd, hp.rd]; exact cov_rd fun a n ⟨r, hr, hc⟩ => ⟨r, by rw [List.mem_singleton.mp hr]; simp, hc⟩)
      hp.cS.symm (by rw [h.inv.sp]; exact hp.bS)
  unfold signExpand
  refine WP.seq (WP.mono (hash_ok (sc := .r29) (f := .r30) (o := 136) (out := sF s + BitVec.ofNat 64 136)
    (by decide) (by decide) (by decide) g29 (by rw [g30]) (kenv hp h.inv) (by simp)
    (fun p hp' => by rw [List.mem_singleton.mp hp']; exact pk) (cov_in (fF hp h.inv) (by decide))
    (fsc hp (by decide)) (by rw [h.inv.sp]; exact fbelow hp (by decide))) fun t₂ ⟨k₂, d₂⟩ => ?_)
  have h₂ := h.inv.hash hp (by decide) k₂
  have hh : bytesAt t₂.mem (sF s + BitVec.ofNat 64 136) 114 = Spec.Sha3.shake256 (bytesAt s.mem (s.gpr .r4) 57) 114 := by
    have e := sign_keep hp h.inv (R := sdR s) (.inl rfl)
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, Piece.bytes,
      Piece.addr, Len.val, g21, BitVec.add_zero, bytesAt_sha3] at d₂ e
    rw [d₂]; exact congrArg (Spec.Sha3.shake256 · 114) e
  refine prune_ok (f := .r30) (o := 136) (q := sF s + BitVec.ofNat 64 136) (is := []) (by decide) (by decide)
    (by decide) (by rw [h₂.regs _ (by decide)]; rfl)
    (fun j hj => by
      rw [h₂.wr, hp.wr, Offset.add_add]; exact in_base (P := sF s) (len := 464) (d := 136 + j) (by simp) (by omega) (by omega))
    fun u um usp urd uwr ug => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · refine h₂.step signRegs_pres urd uwr usp (fun r hr => ug r fun e => by revert hr; rw [e]; decide)
      (um ▸ pruned_frame _ _) (fun r hr => ?_) fun r hr => ?_
    · rw [List.mem_singleton.mp hr]; exact ⟨fR s, by simp, fsub (by decide)⟩
    · rw [List.mem_singleton.mp hr]; exact fslot (by decide)
  · have := keep_hash hp h.inv (o := 136) (d := 0) (n := 10) (by decide) (by decide) (by decide) k₂
    rw [BitVec.add_zero] at this
    rw [um, ← h.hdr, ← this]
    exact bytes_keep (pruned_frame _ _) (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact (Offset.disjoint_base (sF s) (d := 136) (n := 57) (k := 10) (by decide) (by decide)).symm
  · rw [um, pruned_prune, hh]
  · rw [um, ← bytesAt_sha3, bytes_keep (pruned_frame _ _) (by decide) fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint (sF s) (d := 193) (n := 57) (e := 136) (k := 57) (.inr (by decide)) (by decide) (by decide),
      show sF s + BitVec.ofNat 64 193 = sF s + BitVec.ofNat 64 136 + BitVec.ofNat 64 57 by rw [Offset.add_add],
      bytesAt_sha3, ← bytesAt_drop57, hh]

end VG.Proof.Ed448.PPC64LE.Whole
