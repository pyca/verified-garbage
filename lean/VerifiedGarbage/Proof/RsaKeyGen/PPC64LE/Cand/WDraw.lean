module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WRound
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WLoad
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.WSel
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Out
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.RangeCover

/-!
# A candidate on PPC64LE: one draw

`draw_ok`: the next `8 w` octets of `rand` (`load_ok`), the witness from
them (`witness_ok`), and its round (`round_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Witness (draw hUni)
open VG.Impl.MillerRabin.PPC64LE.Search (hRand hUsed hK hIdx hChecks hStat)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.MillerRabin.PPC64LE (RoundImpl arr Env)
open VG.Proof.Bignum (slot)

/-- A witness is below the candidate. -/
theorem witness_lt {c x w : Nat} (hc : c % 2 = 1) (hb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w) (hw : 1 ≤ w)
    (hx : x < 2 ^ (64 * w)) : (Spec.RsaKeyGen.witness (c - 1) x).1 < c := by
  rw [VG.Proof.RsaKeyGen.witness_eq hc hb hx]
  have h0 : c - 1 ≠ 0 := fun e => by
    rw [e] at hb; simp [Spec.RsaKeyGen.bitLength] at hb; omega
  have hl : (c - 1).log2 = 64 * w - 1 := by
    unfold Spec.RsaKeyGen.bitLength at hb; simp only [h0, ↓reduceIte] at hb; omega
  have hp : 2 ^ (64 * w - 1) ≤ c - 1 := hl ▸ Nat.log2_self_le h0
  split
  · rename_i h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; omega
  · have := Nat.mod_lt (x ||| 2) (Nat.two_pow_pos (64 * w - 1)); omega

/-- The header words `draw` changes, as numbers of words. -/
def drWords : List Nat := [23, 26, 29, 30, 1, 20, 22, 19, 2]

/-- What a draw leaves: the witness `x` from the octets at `R + u`. -/
structure DrPost (s : State) (B R : Addr) (L w c u I U ch : Nat) (t : State) : Prop where
  prep : Prep t B L w c
  stat : word t.mem B (8 * hStat) = BitVec.ofNat 64
    (if Proof.MillerRabin.Round.round c (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).1 then
      statOf I (U + if (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).2 then 1 else 0) ch else 2)
  idx : word t.mem B (8 * hIdx) = BitVec.ofNat 64
    (if Proof.MillerRabin.Round.round c (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).1 then I + 1 else I)
  uni : word t.mem B (8 * hUni) = BitVec.ofNat 64 (U + if (Spec.RsaKeyGen.witness (c - 1)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off R u) (8 * w)))).2 then 1 else 0)
  used : word t.mem B (8 * hUsed) = BitVec.ofNat 64 (u + 8 * w)
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ drWords, d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) → word t.mem B d = word s.mem B d
  frame : Frame [⟨B, 8 * L⟩, below s.sp 176] s.mem t.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  cs : ∀ r ∈ preserved, r ∉ Pub.montRegs → r ∉ psRegs → r ∉ ldRegs → r ∉ witRegs → t.gpr r = s.gpr r

/-- The ranges `load` and `witness` change. -/
def lwRanges (w : Nat) : List (Nat × Nat) :=
  [(8 * hUsed, 8), (8 * hUni, 8), (slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

/-- What a draw starts from. -/
structure DrIn (s : State) (B Ra : Addr) (L w c u I U ch : Nat) : Prop where
  prep : Prep s B L w c
  h35 : slot w VG.Impl.RsaKeyGen.PPC64LE.Candidate.nArr ≤ 8 * L
  cb : Spec.RsaKeyGen.bitLength (c - 1) = 64 * w
  cR : c < 2 ^ (64 * w)
  rand : word s.mem B (8 * hRand) = Ra
  used : word s.mem B (8 * hUsed) = BitVec.ofNat 64 u
  kk : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * w)
  rN : ∀ i < 8 * w, InRegions (s.rd ++ s.wr) (off Ra (u + i)) 1
  rsep : ∀ i < 8 * w, ∀ x, ofs B x < 8 * L → off Ra (u + i) ≠ x
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  sp : 176 ≤ s.sp.toNat
  stk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩
  idx : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I
  uni : word s.mem B (8 * hUni) = BitVec.ofNat 64 U
  chk : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  bI : I + 1 < 2 ^ 63
  bU : U + 1 < 2 ^ 63
  bch : ch < 2 ^ 63

/-- The witness drawn at `R + u`. -/
abbrev drX (m : Mem) (Ra : Addr) (w c u : Nat) : Nat × Bool :=
  Spec.RsaKeyGen.witness (c - 1) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off Ra u) (8 * w)))

/-- What `load` leaves. -/
abbrev DrL (sD : State) (B Ra : Addr) (L w u : Nat) (s : State) : Prop :=
  (val32 s.mem B (slot w 4) (2 * w) = Spec.Rsa.os2ip (Spec.Rsa.bytesAt sD.mem (off Ra u) (8 * w)) ∧
    word s.mem B (8 * hUsed) = BitVec.ofNat 64 (u + 8 * w) ∧ Env s B (8 * L) w ∧
    Outs B [(8 * hUsed, 8), (slot w 4, 8 * w)] sD.mem s.mem) ∧ Keep ldRegs sD s

theorem loadS {sD : State} {B Ra : Addr} {L w c u I U ch : Nat} (h : DrIn sD B Ra L w c u I U ch) :
    WP isa VG.Impl.RsaKeyGen.PPC64LE.Witness.load sD (DrL sD B Ra L w u) :=
  load_ok h.prep.env h.rand h.used h.kk h.rN h.rsep

/-- The round's start. -/
structure PreRd (sD : State) (B Ra : Addr) (L w c u I U ch : Nat) (s : State) : Prop where
  prep : Prep s B L w c
  a4 : arr s.mem B w 4 = (drX sD.mem Ra w c u).1
  ac : (drX sD.mem Ra w c u).1 < c
  wr : (⟨B, 8 * L⟩ : Region) ∈ s.wr
  sp : 176 ≤ s.sp.toNat
  stk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩
  idx : word s.mem B (8 * hIdx) = BitVec.ofNat 64 I
  uni : word s.mem B (8 * hUni) = BitVec.ofNat 64 (U + if (drX sD.mem Ra w c u).2 then 1 else 0)
  chk : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  used : word s.mem B (8 * hUsed) = BitVec.ofNat 64 (u + 8 * w)
  hdr : ∀ d, d + 8 ≤ 256 → (∀ k ∈ drWords, d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) → word s.mem B d = word sD.mem B d
  outs : Outs B (lwRanges w) sD.mem s.mem
  keep : Keep (ldRegs ++ witRegs) sD s

theorem witS {sD s₁ : State} {B Ra : Addr} {L w c u I U ch : Nat} (h : DrIn sD B Ra L w c u I U ch)
    (hl : DrL sD B Ra L w u s₁) :
    WP isa VG.Impl.RsaKeyGen.PPC64LE.Witness.witness s₁ (PreRd sD B Ra L w c u I U ch) := by
  obtain ⟨⟨v₁, u₁, e₁, o₁⟩, k₁⟩ := hl
  have e := h.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  have hw4 := e.hw
  rw [slot_lin] at hZ
  have hc0 : VG.Proof.Bignum.wv s₁.mem B (slot w 0) w = c := by
    rw [← Pre.val32_eq_wv, ← h.prep.n]
    exact o₁.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hUsed, slot_lin] <;> omega)
      (by rw [slot_lin]; omega)
  have hU₁ : word s₁.mem B (8 * hUni) = BitVec.ofNat 64 U := by
    rw [o₁.word (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [hUsed, hUni, slot_lin] <;> omega)
      (by simp only [hUni]; omega), h.uni]
  refine WP.mono (witness_ok e₁ h.h35 hc0 h.prep.odd h.cb h.cR hU₁) fun s₂ ⟨⟨a₂, u₂, e₂, o₂⟩, k₂⟩ => ?_
  rw [← Pre.val32_eq_wv, v₁] at a₂ u₂
  have hXc : (drX sD.mem Ra w c u).1 < c := by
    refine witness_lt h.prep.odd h.cb (by omega) ?_
    rw [← v₁, Pre.val32_eq_wv]; exact VG.Proof.Bignum.wv_lt _ _ _ _
  have o₁₂ : Outs B (lwRanges w) sD.mem s₂.mem := by
    refine (o₁.cover (fun r hr => ?_)).trans (o₂.cover (fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, by simp [lwRanges], Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨(slot w 4, 8 * (w + 2)), by simp [lwRanges], Nat.le_refl _, by simp only []; omega⟩
    · refine ⟨r, ?_, Nat.le_refl _, Nat.le_refl _⟩
      simp only [witRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [lwRanges]
  have ap : ∀ d, (d + 8 ≤ 256 ∧ (d + 8 ≤ 152 ∨ 160 ≤ d) ∧ (d + 8 ≤ 16 ∨ 24 ≤ d)) ∨ slot w 0 = d ∨
      slot w 27 + 8 * w = d → word s₂.mem B d = word sD.mem B d := by
    intro d hd
    refine o₁₂.word (fun r hr => ?_) (by rcases hd with hd | rfl | rfl <;> rw [slot_lin] at * <;> omega)
    simp only [lwRanges, hUsed, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rcases hd with hd | rfl | rfl <;> simp only [slot_lin] at * <;> omega
  have K₁₂ := k₁.trans k₂
  have p₂ : Prep s₂ B L w c := by
    refine h.prep.keep e₂ (fun d hd => ?_) (fun j hj => ?_)
    · refine ap d ?_
      rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl
      iterate 5 exact .inl (by omega)
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)
    · refine o₁₂.val32 (fun r hr => ?_) (by rcases hj with rfl | rfl | rfl | rfl | rfl <;> rw [slot_lin] <;> omega)
      simp only [lwRanges, hUsed, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega
  refine ⟨p₂, a₂, hXc, by rw [K₁₂.wr]; exact h.wr, by rw [K₁₂.sp]; exact h.sp, by rw [K₁₂.sp]; exact h.stk,
    (ap _ (.inl (by simp only [hIdx]; omega))).trans h.idx, u₂,
    (ap _ (.inl (by simp only [hChecks]; omega))).trans h.chk, ?_,
    fun d hd hk => ap d (.inl ⟨hd, hk 19 (by simp [drWords]), hk 2 (by simp [drWords])⟩), o₁₂, K₁₂⟩
  rw [o₂.word (fun r hr => by
    simp only [witRanges, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp only [hUsed, slot_lin] <;> omega) (by simp only [hUsed]; omega), u₁]

theorem roundS (R : RoundImpl) {sD s : State} {B Ra : Addr} {L w c u I U ch : Nat}
    (hD : DrIn sD B Ra L w c u I U ch) (h : PreRd sD B Ra L w c u I U ch s) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Witness.round R.name R.code) s (DrPost sD B Ra L w c u I U ch) := by
  have e := h.prep.env
  have hnw := e.hs.nowrap
  have hZ := e.hZ
  rw [slot_lin] at hZ
  refine WP.mono (round_ok R h.prep h.a4 h.ac h.sp h.stk h.idx h.uni h.chk hD.bI
    (by have := hD.bU; split <;> omega) hD.bch) fun t ht => ?_
  have hd' : ∀ d, d + 8 ≤ 256 → (∀ k ∈ [23, 26, 29, 30, 1, 20, 22], d + 8 ≤ 8 * k ∨ 8 * k + 8 ≤ d) →
      word t.mem B d = word s.mem B d := ht.hdr
  refine ⟨ht.prep, ht.stat, ht.idx, ?_, ?_, fun d hd hk => ?_, ?_, ht.rd.trans h.keep.rd, ht.wr.trans h.keep.wr,
    ht.sp.trans h.keep.sp, fun r hr h1 h2 h3 h4 => ?_⟩
  · rw [hd' _ (by simp only [hUni]; omega) (by simp only [hUni]; decide), h.uni]
  · rw [hd' _ (by simp only [hUsed]; omega) (by simp only [hUsed]; decide), h.used]
  · rw [hd' d hd (fun k hk' => hk k (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk'
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [drWords])), h.hdr d hd hk]
  · have fr := ht.frame
    rw [h.keep.sp] at fr
    refine (Frame.mono (frame_of_outs h.outs (Z := 8 * L) (fun r hr => ?_)) (by simp)).trans fr
    simp only [lwRanges, hUsed, hUni, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega
  · rw [ht.cs r hr h1 h2, h.keep.gpr r (by simp [h3, h4])]

theorem draw_ok (R : RoundImpl) {s : State} {B Ra : Addr} {L w c u I U ch : Nat}
    (h : DrIn s B Ra L w c u I U ch) :
    WP isa (draw R.name R.code) s (DrPost s B Ra L w c u I U ch) := by
  unfold draw
  exact WP.seq (WP.mono (loadS h) fun s₁ hl => WP.seq (WP.mono (witS h hl) fun s₂ hp => roundS R h hp))

end VG.Proof.RsaKeyGen.PPC64LE.Cand
