module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mr4
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont5
import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Taint6
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.Arm.Body
import VerifiedGarbage.Proof.Rsa.Arm.RdTwos
import VerifiedGarbage.Proof.Rsa.TwosMath
import VerifiedGarbage.Proof.Bignum.Arm.PrecomputeState
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Mont
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Tools
import VerifiedGarbage.Proof.Rsa.Arm.Stage.MM
import VerifiedGarbage.Proof.Rsa.Arm.Stage.KS
import VerifiedGarbage.Proof.Rsa.Arm.Stage.Taint2
import VerifiedGarbage.Proof.Rsa.Arm.Stage.VP
public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Cand.Mont10
public import VerifiedGarbage.Proof.MillerRabin.Arm.Contract
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `RsaKeyGen.Arm.Cand.Mr5`, which only this module used -/

section

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
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.MillerRabin.Arm (KeepsLite LayoutLite PreparedLite roundPre roundPost roundPub RoundImpl)

/-- The key arrays the round may write: those of Montgomery multiplication's
header, and its arrays `wJs`. -/
abbrev rJs : List Nat := [15, 16, 17, 18, 19, 20, 23, 24, 26, 27, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42,
  43, 44, 45, 46, 47]

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
    have := Outs.val32 (k := 1) (d := d) o (fun r hr => ?_) (by omega_arith)
    · simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
    simp only [ranges, List.map_nil, List.append_nil, List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨k, -, rfl⟩ | rfl
    · have : hdr ≤ arr P.W k := Nat.le_add_right _ _; dsimp only; omega_arith
    · dsimp only; omega_arith
  refine ⟨pre, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, fr, (sl 16 (by decide)).trans h.cnt,
    fun j hj => ?_, fun d hd => (sl d (h.ls_ok d hd).1).trans (h.sl d hd), h.live_lt, h.ls_ok⟩
  have := pre.fitZ (h.live_lt j hj)
  have : S P.W = 4 * (P.W + 2) := rfl
  rw [← h.arrs j hj]
  refine Outs.val32 o (fun r hr => ?_) (by omega_arith)
  simp only [ranges, List.map_nil, List.append_nil, List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨k, hk, rfl⟩ | rfl
  · have := arr_disj (w := P.W) (fun e : k = j => hjl j hj (e ▸ hk)); dsimp only; omega_arith
  · dsimp only; omega_arith

/-- An offset in Montgomery multiplication's header is in one of the key arrays 15–20. -/
theorem In.inHdr (pre : In P σ) {X : Nat} (h1 : P.oM ≤ X) (h2 : X < P.oM + 256)
    (hx : ∀ r ∈ ranges P.W rJs [], X < r.1 ∨ r.1 + r.2 ≤ X) : False := by
  have l := pre.oM_le
  have e := pre.oM_eq
  have hS : 0 < S P.W := by simp only [S]; omega_arith
  have hd := Nat.div_add_mod (X - hdr) (S P.W)
  have hr := Nat.mod_lt (X - hdr) hS
  generalize (X - hdr) / S P.W = q at hd
  generalize (X - hdr) % S P.W = r at hd hr
  have h15 : hdr + 15 * S P.W ≤ P.oM := l
  have h21 : P.oM + 256 = hdr + 21 * S P.W := e
  have hq : X = hdr + q * S P.W + r := by rw [Nat.mul_comm] at hd; omega_arith
  have q1 : 15 * S P.W < (q + 1) * S P.W := by rw [Nat.add_mul]; omega_arith
  have q2 : q * S P.W < 21 * S P.W := by omega_arith
  have qa := Nat.lt_of_mul_lt_mul_right q1
  have qb := Nat.lt_of_mul_lt_mul_right q2
  have hm : q ∈ rJs := by
    rcases (by omega_arith : q = 15 ∨ q = 16 ∨ q = 17 ∨ q = 18 ∨ q = 19 ∨ q = 20) with rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  have := hx (arr P.W q, S P.W) (by
    simp only [ranges, List.map_nil, List.append_nil]; exact List.mem_map_of_mem hm)
  simp only [arr] at this
  omega_arith

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
    simp only [ofs] at *; omega_arith
  have hx' : ∀ r ∈ ranges P.W rJs [], ofs (State.addr P.B) x < r.1 ∨ r.1 + r.2 ≤ ofs (State.addr P.B) x :=
    fun r hr => hx r (List.mem_append_left _ hr)
  by_cases hin : P.oM ≤ ofs (State.addr P.B) x
  · obtain ⟨i, hi⟩ : ∃ i, ofs (State.addr P.B) x = P.oM + i := ⟨_, (Nat.add_sub_cancel' hin).symm⟩
    have ex : x = State.addr P.M0 + BitVec.ofNat 64 i := by
      rw [hM, Offset.add_add, ← hi]
      simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    have h256 : 256 ≤ i := by
      refine Nat.le_of_not_lt fun hl => pre.inHdr (X := ofs (State.addr P.B) x) hin (by omega_arith) hx'
    rw [ex]
    refine keeps i (by omega_arith) (fun k hk => ?_) (fun j hj => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> omega_arith
    · have := pre.inArr (rJs_wJs j hj) hx'
      omega_arith
  · refine fr x fun r hr hc => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Region.Contains] at hc
      rw [hM] at hc
      have hlt : P.oM + 8 * P.lenR ≤ 2 ^ 64 := by omega_arith
      have hc' : (x - (State.addr P.B + BitVec.ofNat 64 P.oM)).toNat < 8 * P.lenR := by
        simp only [off] at hc; omega_arith
      exact hin ((Offset.lt_iff x (State.addr P.B) (d := P.oM) (n := 8 * P.lenR) hlt).mp hc').1
    · exact pre.sC x (by simp only [Region.Contains]; simp only [ofs] at hz; omega_arith) hc

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
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at hr
      rcases hk with rfl | rfl | rfl | rfl <;> omega_arith
    · obtain ⟨j2, -⟩ := VG.Proof.MillerRabin.Arm.wJs_lt j hj
      have j4 := wJs_ne4 j hj
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at hr ⊢
      rcases (by omega_arith : j ≤ 3 ∨ 5 ≤ j) with c | c
      · have a := Nat.mul_le_mul_right (8 * (P.w + 2)) (show 2 ≤ j by omega_arith)
        have b := Nat.mul_le_mul_right (8 * (P.w + 2)) (show j + 1 ≤ 4 by omega_arith)
        rw [Nat.add_mul] at b
        omega_arith
      · have a := Nat.mul_le_mul_right (8 * (P.w + 2)) c
        omega_arith
  have h4 : 8 * 4 * (P.w + 2) = 4 * (8 * (P.w + 2)) := by omega_arith
  refine h.of_read (fun d n hd => ?_) ?_ ?_ sp rd wr
  · refine Mem.read_congr fun i hi => ?_
    simp only [off]; rw [Offset.add_add]
    simp only [MRd, mHd, arrAt, Proof.Rsa.Mont.hdrBytes] at hd
    exact kb _ (by omega_arith) (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith)
  · unfold numAt
    exact congrArg BitVec.toNat (Mem.read_congr fun i hi => by
      rw [Offset.add_add]
      exact kb _ (by simp only [arrAt, Proof.Rsa.Mont.hdrBytes]; omega_arith) (.inr (.inr (.inr ⟨by omega_arith, by omega_arith⟩))))
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
      have := Offset.disjoint_below (State.addr P.sp) (n := 56) (d := 0) (k := 4) (by omega_arith)
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

/-- The round's exponent and the word `2^(t mod 64)` after it, from the key array `mBase + 27`. -/
theorem exp_facts (pre : In P σ) {m : Mem} (e27 : num m P.B P.W (mBase + 27) = EX P σ) :
    numAt m (State.addr P.M0) P.w 27 = Proof.MillerRabin.Round.exponent (cv P σ) ∧
      m.readW (State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w 27 + 8 * P.w)) 64 =
        BitVec.twoPow 64 ((Spec.Rsa.splitTwos (cv P σ - 1)).1 % 64) := by
  have hW := pre.W_eq
  have eL : 32 * (P.W - 2) = 64 * P.w := by omega_arith
  have eLt : Proof.MillerRabin.Round.exponent (cv P σ) < 2 ^ (32 * (P.W - 2)) := by
    rw [eL]; exact Nat.lt_of_le_of_lt (exponent_le _) (cv_lt pre)
  have k64 : (Spec.Rsa.splitTwos (cv P σ - 1)).1 % 64 < 64 := Nat.mod_lt _ (by decide)
  have kLt : 2 ^ ((Spec.Rsa.splitTwos (cv P σ - 1)).1 % 64) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) k64
  have g1 : numAt m (State.addr P.M0) P.w 27 = val32 m (State.addr P.B) (arr P.W (mBase + 27)) (P.W - 2) :=
    pre.numAt_val32 m 27
  have g2 : (m.readW (State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w 27 + 8 * P.w)) 64).toNat =
      val32 m (State.addr P.B) (arr P.W (mBase + 27) + 4 * (P.W - 2)) 2 := by
    have e := word_eq_w32 m (State.addr P.M0) (arrAt P.w 27 + 8 * P.w)
    have d : P.oM + (arrAt P.w 27 + 8 * P.w) = arr P.W (mBase + 27) + 4 * (P.W - 2) := by
      rw [← Nat.add_assoc, pre.oM_arrAt]; omega_arith
    simp only [VG.Proof.Mont.word, w32, pre.M0_off, d] at e
    rw [show P.oM + (arrAt P.w 27 + 8 * P.w + 4) = arr P.W (mBase + 27) + 4 * (P.W - 2) + 4 by omega_arith] at e
    have e' : m.readW (State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w 27 + 8 * P.w)) 64 =
        m.readW (off (State.addr P.B) (arr P.W (mBase + 27) + 4 * (P.W - 2))) 64 := by
      rw [← d, ← pre.M0_off]
    rw [e', e]
    simp only [val32, w32]
    omega_arith
  have split := val32_append m (State.addr P.B) (arr P.W (mBase + 27)) (P.W - 2) 2
  rw [show P.W - 2 + 2 = P.W by omega_arith] at split
  have e2 : num m P.B P.W (mBase + 27) = val32 m (State.addr P.B) (arr P.W (mBase + 27)) (P.W - 2) +
      2 ^ (32 * (P.W - 2)) * val32 m (State.addr P.B) (arr P.W (mBase + 27) + 4 * (P.W - 2)) 2 := split
  rw [e27] at e2
  unfold EX at e2
  rw [← g1] at e2
  rw [← g2] at e2
  have lo : numAt m (State.addr P.M0) P.w 27 < 2 ^ (32 * (P.W - 2)) := by
    rw [g1]; exact val32_lt _ _ _ _
  generalize numAt m (State.addr P.M0) P.w 27 = x at e2 lo ⊢
  generalize (m.readW (State.addr P.M0 + BitVec.ofNat 64 (arrAt P.w 27 + 8 * P.w)) 64) = y at e2 ⊢
  generalize 2 ^ (32 * (P.W - 2)) = R at e2 eLt lo
  have hR : 0 < R := by omega_arith
  have ex : x = Proof.MillerRabin.Round.exponent (cv P σ) := by
    have := congrArg (· % R) e2
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lo, Nat.mod_eq_of_lt eLt] at this
    exact this.symm
  refine ⟨ex, ?_⟩
  rw [ex] at e2
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt kLt]
  exact (Nat.eq_of_mul_eq_mul_left hR (Nat.add_left_cancel e2)).symm

/-- The round's precondition. -/
theorem round_pre (h : KS P σ A live V ls s) (m : MS P σ s) (r0 : s.gpr .r0 = P.M0)
    (r1 : s.gpr .r1 = BitVec.ofNat 32 P.lenR) (x5 : numAt s.mem (State.addr P.M0) P.w 5 < cv P σ)
    (one : numAt s.mem (State.addr P.M0) P.w 9 = Rm P σ)
    (m1 : numAt s.mem (State.addr P.M0) P.w 10 = cv P σ - Rm P σ)
    (e27 : num s.mem P.B P.W (mBase + 27) = EX P σ) :
    roundPre (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]) := by
  have pre := h.pre
  have sp : s.sp = P.sp := h.sp.trans pre.sp
  have hw := pre.w4
  have lg := pre.lenR_ge
  have lt : P.lenR < 2 ^ 32 := by have := pre.lenR_fit; have := pre.Z_le; omega_arith
  have e0 : (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r0 = P.M0 := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r0]
  have e1 : (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r1 = BitVec.ofNat 32 P.lenR := by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r1]
  dsimp only [roundPre]
  rw [e0, e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pre.M0_toNat]; have := pre.lenR_fit; have := pre.fS; omega_arith
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
    refine ⟨⟨l1, l2, ?_, l4⟩, by omega_arith, by omega_arith, ?_⟩ <;>
      simp only [arrAt, Proof.Rsa.Mont.hdrBytes, VG.Proof.MillerRabin.Arm.nArr] at l3 ⊢ <;> omega_arith
  · show PreparedLite s.mem (State.addr P.M0)
    have hodd := (cv_shape (σ := σ) pre).1
    have hg := cv_gt pre
    dsimp only [PreparedLite]
    rw [m.width, m.n0]
    obtain ⟨ex, lo⟩ := exp_facts pre e27
    exact ⟨by omega_arith, hodd, m.inverse, x5, one, m1, ex, lo⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand

end

end

/-! # A candidate on ARMv7: the round on the witness (`mrCall_vp`)

The witness in Montgomery form into Montgomery multiplication's array 5,
the round on it (`round_vp`, as a piece: correct and leaking only the
public parameters), the context, and its result into the header word `sF`.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Cand
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Keys VG.Impl.RsaKeyGen.Arm.Candidate VG.Proof.Rsa.Arm.Keys
open VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (arrAt numAt wOf wordAt Layout Operand)
open VG.Proof.Rsa.Arm.Recover (VP)
open VG.Proof.Rsa (b2n)
open VG.Proof.MillerRabin.Arm (KeepsLite roundPost roundPub RoundImpl)

/-- The stage after the witness. -/
abbrev AF (P : CP) (k : Nat) (σ : State) : Nat → Nat := upd (AW P k σ) aH1 (wf P σ k).1
abbrev VF (P : CP) (k : Nat) (σ : State) : Nat → Nat := upd (VW P k σ) sU (b2n (wf P σ k).2)
abbrev LF : List Nat := aH1 :: aX :: LB2
abbrev LSF : List Nat := sU :: LSW

/-- The round's result on the witness of iteration `k`. -/
abbrev rv (P : CP) (σ : State) (k : Nat) : Nat := b2n (Proof.MillerRabin.Round.round (cv P σ) (wf P σ k).1)

/-- The witness in Montgomery form from its product with `R² mod c`. -/
theorem x5_val {c R n a : Nat} (hR : Nat.Coprime R c) (hn : n < c) (hc : 0 < c)
    (h : n * R % c = a * (R * R % c) % c) : n = a % c * R % c := by
  refine VG.Proof.RsaKeyGen.mont_inj hR hn (Nat.mod_lt _ hc) ?_
  rw [h, Nat.mul_mod_mod, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mod_mul_mod]

section
variable {P : CP} {E : State → Prop} {A : State → Nat → Nat} {L : List Nat} {V : State → Nat → Nat}
  {LS : List Nat}

theorem wit_facts {σ : State} (pre : In P σ) (k : Nat) :
    Spec.RsaKeyGen.bitLength (cv P σ - 1) = 64 * P.w ∧ xw P σ k < 2 ^ (64 * P.w) := by
  have lE := pre.L_eq; have w4 := pre.w4
  have sh : VG.Proof.RsaKeyGen.PrimeShape (64 * P.w) (cv P σ) := by
    have := cv_shape (σ := σ) pre; rwa [show 8 * P.L = 64 * P.w by omega_using [lE]] at this
  refine ⟨(VG.Proof.RsaKeyGen.cand_bits (by omega_using [w4]) sh).2.1, ?_⟩
  have := xw_lt P σ k; rwa [show 8 * P.L = 64 * P.w by omega_using [lE]] at this

theorem wf_lt {σ : State} (pre : In P σ) (k : Nat) : (wf P σ k).1 < 2 ^ (64 * P.w) := by
  obtain ⟨hb, hx⟩ := wit_facts pre k
  have w4 := pre.w4
  rw [show wf P σ k = Spec.RsaKeyGen.witness (cv P σ - 1) (xw P σ k) from rfl, witness_arm hb hx]
  dsimp only
  split
  · exact hx
  · exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) (by omega_using []))

/-- The working space's context, keeping `X`. -/
theorem VP.ctx {X : State → State → Prop}
    (hX : ∀ σ s t, X σ s → t.mem = s.mem → Rest [.r7, .r8, .r9] s t → X σ t) :
    VP (fun σ s => (E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ X σ s) (.block ctx)
      (fun σ s => St P E A L V LS σ s ∧ X σ s) := by
  rw [show VG.Impl.RsaKeyGen.Arm.Candidate.ctx = [.ldrSp .r8 aoS] ++ ctxW from rfl]
  refine VP.block_append (G := fun σ s => ((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ X σ s) ∧ s.gpr .r8 = P.B) ?_ ?_
  · show VP _ (.block ([(Reg.r8, aoS)].map fun p => Instr.ldrSp p.1 p.2)) _
    refine VP.ldrSp (fun σ₁ σ₂ s₁ s₂ h₁ h₂ => ?_) fun σ s ⟨⟨e, k⟩, x⟩ => ?_
    · rw [h₁.1.2.sp, h₁.1.2.pre.sp, h₂.1.2.sp, h₂.1.2.pre.sp]
    refine k.ldrSp (o := aoS) (by decide) fun t u => WP.block_nil ⟨⟨⟨e, k.of_rest (u.rest (ws := [.r8])
      (by simp)) u.mem⟩, hX σ s t x u.mem (u.rest (by simp))⟩, by rw [u.gpr, k.pre.aS]⟩
  · refine VP.taint [.r8] ctxW_taint (fun σ₁ σ₂ s₁ s₂ h₁ h₂ r hr => ?_) fun σ s ⟨⟨⟨e, k⟩, x⟩, r8⟩ => ?_
    · simp only [List.mem_singleton] at hr; subst hr; rw [h₁.2, h₂.2]
    have pre := k.pre
    have hz := pre.hdr_Z
    have hf := pre.fS
    have ea : State.addr (s.gpr .r8 + BitVec.ofNat 32 16) = off (State.addr P.B) 16 := by
      rw [r8]; exact addr_add (by simp only [hdr] at hz; omega_using [hz, hf])
    have rd : InRegions (s.rd ++ s.wr) (off (State.addr P.B) 16) 4 :=
      ⟨P.rS, List.mem_append_right _ (by rw [k.wr]; exact pre.rS_mem),
        Offset.contains_base _ (by simp only [hdr] at hz; omega_using [hz]) (by omega_using [])⟩
    simp only [ctxW, stride, List.cons_append, List.nil_append]
    refine wp_ldr (by decide) ea rd fun s2 u2 => ?_
    refine wp_dp (op2_imm (by decide)) fun s3 u3 => wp_mov (op2_lsl (by decide)) fun s4 u4 => WP.block_nil ?_
    have m4 : s4.mem = s.mem := by rw [u4.mem, u3.mem, u2.mem]
    have r4 : Rest [.r7, .r9] s s4 := (u2.rest (by simp)).trans ((u3.rest (by simp)).trans (u4.rest (by simp)))
    have wl := pre.wle
    have e9 : s4.gpr .r9 = BitVec.ofNat 32 P.W := by
      rw [u4.other _ (by decide), u3.other _ (by decide), u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [wl])]
    have e7 : s4.gpr .r7 = BitVec.ofNat 32 (S P.W) := by
      rw [u4.gpr, u3.gpr, dpVal, u2.gpr]
      apply BitVec.eq_of_toNat_eq
      have := k.cnt
      simp only [slot, w32] at this
      rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, this, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      simp only [show (2 : BitVec 32).toNat = 2 from rfl, S]
      omega_using []
    have e8 : s4.gpr .r8 = P.B := by rw [r4.gpr _ (by decide), r8]
    have k4 := k.of_rest r4 m4
    exact ⟨⟨e, k4, k4.ws e7 e8 e9⟩, hX σ s s4 x m4 (r4.mono (by simp))⟩

/-- The round on Montgomery multiplication's array 5, the witness `b σ` in
Montgomery form. -/
theorem round_vp (v : RoundImpl) {b : State → Nat} (h9 : mBase + 9 ∈ L) (h10 : mBase + 10 ∈ L)
    (h27 : mBase + 27 ∈ L) (hL : ∀ j ∈ L, j ∉ rJs) (a9 : ∀ σ, E σ → A σ (mBase + 9) = Rm P σ)
    (a10 : ∀ σ, E σ → A σ (mBase + 10) = cv P σ - Rm P σ) (a27 : ∀ σ, E σ → A σ (mBase + 27) = EX P σ) :
    VP (fun σ s => ((E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
        numAt s.mem (State.addr P.M0) P.w 5 < cv P σ ∧
        numAt s.mem (State.addr P.M0) P.w 5 = b σ % cv P σ * 2 ^ (64 * P.w) % cv P σ) ∧
        s.gpr .r0 = P.M0 ∧ s.gpr .r1 = BitVec.ofNat 32 P.lenR)
      (.call v.name v.code)
      (fun σ s => (E σ ∧ KS P σ (A σ) L (V σ) LS s) ∧ MS P σ s ∧
        (s.gpr .r0).toNat = if Proof.MillerRabin.Round.round (cv P σ) (b σ) then 1 else 0) := by
  have nums : ∀ σ s, E σ → KS P σ (A σ) L (V σ) LS s →
      numAt s.mem (State.addr P.M0) P.w 9 = Rm P σ ∧
        numAt s.mem (State.addr P.M0) P.w 10 = cv P σ - Rm P σ := by
    intro σ s e h
    have pre := h.pre
    have lt := Rm_lt pre
    have cl := cv_lt pre
    refine ⟨?_, ?_⟩
    · rw [pre.numAt_eq (by rw [h.arrs _ h9, a9 σ e]; omega_using [lt, cl]), h.arrs _ h9, a9 σ e]
    · rw [pre.numAt_eq (by rw [h.arrs _ h10, a10 σ e]; omega_using [cl]), h.arrs _ h10, a10 σ e]
  have cov : ∀ σ s, KS P σ (A σ) L (V σ) LS s → Covers [⟨State.addr P.M0, 8 * P.lenR⟩] s.wr := by
    intro σ s h
    have pre := h.pre
    refine Covers.of_sub fun r hr => ⟨P.rS, by rw [h.wr]; exact pre.rS_mem, P.oM, ?_, ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact pre.M0_addr
    · simp only [List.mem_singleton] at hr; subst hr; dsimp only; rw [pre.lenR_fit]
  have e0 : ∀ s : State, s.gpr .r0 = P.M0 →
      (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r0 = P.M0 := fun s r0 => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r0]
  have e1 : ∀ s : State, s.gpr .r1 = BitVec.ofNat 32 P.lenR →
      (s.callEntry.withRegions [] [⟨State.addr P.M0, 8 * P.lenR⟩]).gpr .r1 = BitVec.ofNat 32 P.lenR := fun s r1 => by
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), r1]
  refine VP.of_ct (fun σ₁ σ₂ => RelCT.call v.verified.1 v.verified.2.1 [] [⟨State.addr P.M0, 8 * P.lenR⟩]
    fun s₁ s₂ ⟨⟨⟨⟨e₁, h₁⟩, m₁, x₁, _⟩, r0₁, r1₁⟩, ⟨⟨⟨e₂, h₂⟩, m₂, x₂, _⟩, r0₂, r1₂⟩⟩ =>
      ⟨round_pre h₁ m₁ r0₁ r1₁ x₁ (nums σ₁ s₁ e₁ h₁).1 (nums σ₁ s₁ e₁ h₁).2 ((h₁.arrs _ h27).trans (a27 σ₁ e₁)),
        round_pre h₂ m₂ r0₂ r1₂ x₂ (nums σ₂ s₂ e₂ h₂).1 (nums σ₂ s₂ e₂ h₂).2 ((h₂.arrs _ h27).trans (a27 σ₂ e₂)), ?_,
        (cov σ₁ s₁ h₁).right, cov σ₁ s₁ h₁, (cov σ₂ s₂ h₂).right, cov σ₂ s₂ h₂⟩)
    fun σ s ⟨⟨⟨e, h⟩, m, x5, xv⟩, r0, r1⟩ => ?_
  · refine ⟨?_, by rw [e0 _ r0₁, e0 _ r0₂], by rw [e1 _ r1₁, e1 _ r1₂], ?_⟩
    · simp only [State.withRegions_sp, State.callEntry_sp]
      rw [h₁.sp, h₁.pre.sp, h₂.sp, h₂.pre.sp]
    · rw [e0 _ r0₁, e0 _ r0₂]
      simp only [State.withRegions_mem, State.callEntry_mem]
      rw [m₁.width, m₂.width]
  have pre := h.pre
  have spw : s.sp = P.sp := h.sp.trans pre.sp
  have lt : P.lenR < 2 ^ 32 := by have := pre.lenR_fit; have := pre.Z_le; omega_arith
  refine FrameStack.WP.callF v.verified.1
    (round_pre h m r0 r1 x5 (nums σ s e h).1 (nums σ s e h).2 ((h.arrs _ h27).trans (a27 σ e)))
    (cov σ s h).right (cov σ s h) (by rw [spw]; have := v.stack; have := pre.spLo; omega_arith)
    fun s' hrd hwr hsp hf _ hpost => ?_
  have fr : Frame [⟨State.addr P.M0, 8 * P.lenR⟩, P.rC] s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · refine ⟨P.rC, by simp, ?_⟩
      have := FrameStack.belowA_sub (sp := s.sp) (a := FrameStack.armStack v.code) (b := 56) v.stack
        (by rw [spw]; exact pre.spLo)
      rw [spw] at this ⊢; exact this
  change roundPost _ _ at hpost
  dsimp only [roundPost] at hpost
  rw [e0 _ r0, e1 _ r1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt] at hpost
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at hpost
  simp only [m.width, m.n0] at hpost
  obtain ⟨hr, keeps⟩ := hpost
  obtain ⟨k', m'⟩ := round_after h m hL keeps fr hsp hrd hwr
  exact ⟨⟨e, k'⟩, m', hr (b σ) xv⟩

end

end VG.Proof.RsaKeyGen.Arm.Cand
