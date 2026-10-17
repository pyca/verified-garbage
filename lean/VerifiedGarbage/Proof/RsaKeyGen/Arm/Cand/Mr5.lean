module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr4
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
import VerifiedGarbage.Proof.Framework.Omega
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A candidate on ARMv7: the call of the round (`round_vp`)

The round, any implementation of it (`RoundImpl`), called on the rest of
the working space from Montgomery multiplication's (`lenR` words): its
precondition from the stage (`round_pre`); it writes, of the key arrays,
only those of Montgomery multiplication's header and of its own arrays
(`rJs`, `outJ_of_round`), and keeps `MS` (`MS.of_round`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (arrAt numAt wOf wordAt Layout)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.MillerRabin.Arm (KeepsLite LayoutLite PreparedLite roundPre roundPost roundPub RoundImpl)

/-- The key arrays the round may write: those of Montgomery multiplication's
header, and its arrays `wJs`. -/
abbrev rJs : List Nat := [15, 16, 17, 18, 19, 20, 23, 24, 26, 27, 29, 32, 33, 34, 35]

theorem rJs_wJs : ∀ j ∈ VG.Proof.MillerRabin.Arm.wJs, mBase + j ∈ rJs := by decide

theorem wJs_ne4 : ∀ j ∈ VG.Proof.MillerRabin.Arm.wJs, j ≠ 4 := by decide

section
variable {P : CP} {σ s t : State} {A : Nat → Nat} {live : List Nat} {V : Nat → Nat} {ls : List Nat}

/-- Memory that changed only in the arrays `js` and outside the working space keeps a stage. -/
theorem KS.of_outJ (h : KS P σ A live V ls s) {js : List Nat}
    (o : Outs (State.addr P.B) (ranges P.W js [] ++ [(P.Z, 2 ^ 64)]) s.mem t.mem)
    (hjl : ∀ j ∈ live, j ∉ js) (fr : Frame P.chg σ.mem t.mem)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : KS P σ A live V ls t := by
  have pre := h.pre
  have hz := pre.hdr_Z
  have zl := pre.Z_le
  have sl : ∀ d, d + 4 ≤ hdr → slot t.mem P.B d = slot s.mem P.B d := fun d hd => by
    have := Outs.val32 (k := 1) (d := d) o (fun r hr => ?_) (by omega)
    · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
    simp only [ranges, List.map_nil, List.append_nil, List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨k, -, rfl⟩ | rfl
    · have : hdr ≤ arr P.W k := Nat.le_add_right _ _; dsimp only; omega
    · dsimp only; omega
  refine ⟨pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, fr, (sl 16 (by decide)).trans h.cnt,
    fun j hj => ?_, fun d hd => (sl d (h.ls_ok d hd).1).trans (h.sl d hd), h.live_lt, h.ls_ok⟩
  have := pre.fitZ (h.live_lt j hj)
  have : S P.W = 4 * (P.W + 2) := rfl
  rw [← h.arrs j hj]
  refine Outs.val32 o (fun r hr => ?_) (by omega)
  simp only [ranges, List.map_nil, List.append_nil, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨k, hk, rfl⟩ | rfl
  · have := arr_disj (w := P.W) (fun e : k = j => hjl j hj (e ▸ hk)); dsimp only; omega
  · dsimp only; omega

/-- An offset in Montgomery multiplication's header is in one of the key arrays 15–20. -/
theorem In.inHdr (pre : In P σ) {X : Nat} (h1 : P.oM ≤ X) (h2 : X < P.oM + 256)
    (hx : ∀ r ∈ ranges P.W rJs [], X < r.1 ∨ r.1 + r.2 ≤ X) : False := by
  have l := pre.oM_le
  have e := pre.oM_eq
  have hS : 0 < S P.W := by simp only [S]; omega
  have hd := Nat.div_add_mod (X - hdr) (S P.W)
  have hr := Nat.mod_lt (X - hdr) hS
  generalize (X - hdr) / S P.W = q at hd
  generalize (X - hdr) % S P.W = r at hd hr
  have h15 : hdr + 15 * S P.W ≤ P.oM := l
  have h21 : P.oM + 256 = hdr + 21 * S P.W := e
  have hq : X = hdr + q * S P.W + r := by rw [Nat.mul_comm] at hd; omega
  have q1 : 15 * S P.W < (q + 1) * S P.W := by rw [Nat.add_mul]; omega
  have q2 : q * S P.W < 21 * S P.W := by omega
  have qa := Nat.lt_of_mul_lt_mul_right q1
  have qb := Nat.lt_of_mul_lt_mul_right q2
  have hm : q ∈ rJs := by
    rcases (by omega : q = 15 ∨ q = 16 ∨ q = 17 ∨ q = 18 ∨ q = 19 ∨ q = 20) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have := hx (arr P.W q, S P.W) (by
    simp only [ranges, List.map_nil, List.append_nil]; exact List.mem_map_of_mem hm)
  simp only [arr] at this
  omega

/-- An offset outside the key array `mBase + j` of `rJs`. -/
theorem In.inArr (pre : In P σ) {X j : Nat} (hj : mBase + j ∈ rJs)
    (hx : ∀ r ∈ ranges P.W rJs [], X < r.1 ∨ r.1 + r.2 ≤ X) :
    X < P.oM + arrAt P.w j ∨ P.oM + arrAt P.w j + 8 * (P.w + 2) ≤ X := by
  have := hx (arr P.W (mBase + j), S P.W) (by
    simp only [ranges, List.map_nil, List.append_nil]; exact List.mem_map_of_mem hj)
  rw [← pre.oM_arrAt j, pre.S_eq] at this
  exact this

/-- The round's region is in the working space. -/
theorem In.subR (pre : In P σ) : Region.Sub ⟨State.addr P.M0, 8 * P.lenR⟩ P.rS := by
  show Region.Sub ⟨State.addr P.M0, 8 * P.lenR⟩ ⟨State.addr P.B, P.Z⟩
  rw [pre.M0_addr]
  exact Offset.sub_base _ (by rw [pre.lenR_fit])

/-- The round writes, of the key arrays, only those of `rJs`. -/
theorem outJ_of_round (pre : In P σ) {m m' : Mem}
    (keeps : KeepsLite (State.addr P.M0) P.lenR P.w m m')
    (fr : Frame [⟨State.addr P.M0, 8 * P.lenR⟩, P.rC] m m') :
    Outs (State.addr P.B) (ranges P.W rJs [] ++ [(P.Z, 2 ^ 64)]) m m' := by
  have hM := pre.M0_addr
  have lr := pre.lenR_fit
  have zl := pre.Z_le
  intro x hx
  have hz : ofs (State.addr P.B) x < P.Z := by
    have := hx (P.Z, 2 ^ 64) (by simp)
    have := (x - State.addr P.B).isLt
    simp only [ofs] at *; omega
  have hx' : ∀ r ∈ ranges P.W rJs [], ofs (State.addr P.B) x < r.1 ∨ r.1 + r.2 ≤ ofs (State.addr P.B) x :=
    fun r hr => hx r (List.mem_append_left _ hr)
  by_cases hin : P.oM ≤ ofs (State.addr P.B) x
  · obtain ⟨i, hi⟩ : ∃ i, ofs (State.addr P.B) x = P.oM + i := ⟨_, (Nat.add_sub_cancel' hin).symm⟩
    have ex : x = State.addr P.M0 + BitVec.ofNat 64 i := by
      rw [hM, Offset.add_add, ← hi]
      simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    have h256 : 256 ≤ i := by
      refine Nat.le_of_not_lt fun hl => pre.inHdr (X := ofs (State.addr P.B) x) hin (by omega) hx'
    rw [ex]
    refine keeps i (by omega) (fun k hk => ?_) (fun j hj => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> omega
    · have := pre.inArr (rJs_wJs j hj) hx'
      omega
  · refine fr x fun r hr hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Region.Contains] at hc
      rw [hM] at hc
      have hlt : P.oM + 8 * P.lenR ≤ 2 ^ 64 := by omega
      have hc' : (x - (State.addr P.B + BitVec.ofNat 64 P.oM)).toNat < 8 * P.lenR := by
        simp only [off] at hc; omega
      exact hin ((Offset.lt_iff x (State.addr P.B) (d := P.oM) (n := 8 * P.lenR) hlt).mp hc').1
    · exact pre.sC x (by simp only [Region.Contains]; simp only [ofs] at hz; omega) hc

/-- The round keeps `MS`. -/
theorem MS.of_round (pre : In P σ) (h : MS P σ s) (spw : s.sp = P.sp)
    (keeps : KeepsLite (State.addr P.M0) P.lenR P.w s.mem t.mem)
    (fr : Frame [⟨State.addr P.M0, 8 * P.lenR⟩, P.rC] s.mem t.mem)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : MS P σ t := by
  have hw := pre.w4
  have lg := pre.lenR_ge
  have kb : ∀ i, i < 8 * P.lenR → (i < 128 ∨ (224 ≤ i ∧ i < 232) ∨
      (arrAt P.w 0 ≤ i ∧ i < arrAt P.w 0 + 8 * P.w) ∨ (arrAt P.w 4 ≤ i ∧ i < arrAt P.w 4 + 8 * P.w)) →
      t.mem (State.addr P.M0 + BitVec.ofNat 64 i) = s.mem (State.addr P.M0 + BitVec.ofNat 64 i) := by
    intro i hi hr
    refine keeps i hi (fun k hk => ?_) (fun j hj => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hr
      rcases hk with rfl | rfl | rfl <;> omega
    · obtain ⟨j2, -⟩ := VG.Proof.MillerRabin.Arm.wJs_lt j hj
      have j4 := wJs_ne4 j hj
      simp only [arrAt, Spec.Rsa.Mont.hdrBytes] at hr ⊢
      rcases (by omega : j ≤ 3 ∨ 5 ≤ j) with c | c
      · have a := Nat.mul_le_mul_right (8 * (P.w + 2)) (show 2 ≤ j by omega)
        have b := Nat.mul_le_mul_right (8 * (P.w + 2)) (show j + 1 ≤ 4 by omega)
        rw [Nat.add_mul] at b
        omega
      · have a := Nat.mul_le_mul_right (8 * (P.w + 2)) c
        omega
  have h4 : 8 * 4 * (P.w + 2) = 4 * (8 * (P.w + 2)) := by omega
  refine h.of_read (fun d n hd => ?_) ?_ ?_ sp rd wr
  · refine Mem.read_congr fun i hi => ?_
    simp only [off]; rw [Offset.add_add]
    simp only [MRd, mHd, arrAt, Spec.Rsa.Mont.hdrBytes] at hd
    exact kb _ (by omega) (by simp only [arrAt, Spec.Rsa.Mont.hdrBytes]; omega)
  · unfold numAt
    exact congrArg BitVec.toNat (Mem.read_congr fun i hi => by
      rw [Offset.add_add]
      exact kb _ (by simp only [arrAt, Spec.Rsa.Mont.hdrBytes]; omega) (.inr (.inr (.inr ⟨by omega, by omega⟩))))
  · rw [sp]
    have hc : (⟨State.addr s.sp, 4⟩ : Region).Contains (State.addr s.sp) (32 / 8) := by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide
    refine fr.readW hc (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [spw]
    rcases hr with rfl | rfl
    · exact (pre.sF.sub_right (Offset.sub_base (State.addr P.sp) (d := 0) (n := 4) (k := 84) (by decide) |>
        fun h => by simpa using h)).symm.sub_right pre.subR
    · have spf := pre.spFit
      rw [pre.rC_eq]
      have := Offset.disjoint_below (State.addr P.sp) (n := 56) (d := 0) (k := 4) (by omega)
      simpa using this

/-- After the round: the stage, and `MS`. -/
theorem round_after (h : KS P σ A live V ls s) (m : MS P σ s) (hl : ∀ j ∈ live, j ∉ rJs)
    (keeps : KeepsLite (State.addr P.M0) P.lenR P.w s.mem t.mem)
    (fr : Frame [⟨State.addr P.M0, 8 * P.lenR⟩, P.rC] s.mem t.mem)
    (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : KS P σ A live V ls t ∧ MS P σ t := by
  have pre := h.pre
  have spw : s.sp = P.sp := h.sp.trans pre.sp
  refine ⟨h.of_outJ (outJ_of_round pre keeps fr) hl (h.frame.trans (fr.sub fun r hr => ?_)) sp rd wr,
    m.of_round pre spw keeps fr sp rd wr⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨P.rS, by simp, pre.subR⟩
  · exact ⟨P.rC, by simp, fun _ h => h⟩

/-- The round's precondition. -/
theorem round_pre (h : KS P σ A live V ls s) (m : MS P σ s) (r0 : s.gpr .r0 = P.M0)
    (r1 : s.gpr .r1 = BitVec.ofNat 32 P.lenR) (x5 : numAt s.mem (State.addr P.M0) P.w 5 < cv P σ)
    (one : numAt s.mem (State.addr P.M0) P.w 9 = Rm P σ)
    (m1 : numAt s.mem (State.addr P.M0) P.w 10 = cv P σ - Rm P σ) :
    roundPre (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]) := by
  have pre := h.pre
  have sp : s.sp = P.sp := h.sp.trans pre.sp
  have hw := pre.w4
  have lg := pre.lenR_ge
  have lt : P.lenR < 2 ^ 32 := by have := pre.lenR_fit; have := pre.Z_le; omega
  have e0 : (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r0 = P.M0 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r0]
  have e1 : (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r1 = BitVec.ofNat 32 P.lenR := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r1]
  dsimp only [roundPre]
  rw [e0, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pre.M0_toNat]; have := pre.lenR_fit; have := pre.fS; omega
  · show 56 ≤ s.sp.toNat
    rw [sp]; exact pre.spLo
  · show (FrameStack.belowA s.sp 56).Disjoint ⟨State.addr P.M0, 8 * P.lenR⟩
    rw [sp]; exact pre.sC.symm.sub_right pre.subR
  · show LayoutLite s.mem (State.addr P.M0) P.lenR
    have wd := m.width
    obtain ⟨l1, l2, l3, l4⟩ := m.layout
    rw [wd] at l1 l2 l3 l4
    unfold LayoutLite Layout
    rw [wd]
    refine ⟨⟨l1, l2, ?_, l4⟩, by omega, by omega, ?_⟩ <;>
      simp only [arrAt, Spec.Rsa.Mont.hdrBytes, VG.Proof.MillerRabin.Arm.nArr] at l3 ⊢ <;> omega
  · show PreparedLite s.mem (State.addr P.M0)
    have hodd := (cv_shape (σ := σ) pre).1
    have hg := cv_gt pre
    dsimp only [PreparedLite]
    rw [m.width, m.n0]
    exact ⟨by omega, hodd, m.inverse, x5, one, m1⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand
