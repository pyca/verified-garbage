import VerifiedGarbage.Proof.Ed448.AArch64.Window.Persist
import VerifiedGarbage.Proof.Ed448.AArch64.Window.SBase
import VerifiedGarbage.Proof.Ed448.AArch64.Window.KInit
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Spec
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Cross
import VerifiedGarbage.Proof.Ed448.AArch64.Window.Result
import VerifiedGarbage.Proof.Ed448.AArch64.VerifyLocal
import VerifiedGarbage.Proof.Ed448.Ref
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Ed448 verification's equation on AArch64: the whole function

Untrusted: everything here is checked by Lean. The correctness of
`vg_ed448_verify_equation` against `verifyEquationLocal` (`VerifyLocal.lean`):
`x20` ends as the OR of the checks of `S` and of decoding `A` and `R`, and
slots 12–15 hold the cross products of `[4]Q` and `[4]R`, for `Q` the comb's
`[S]B` plus the windows' `[k](-A)`, which decide the equation when `A` and
`R` decode (`verifyEquation_eq`); every write is in the working space, so the
inputs are read unchanged, and the callee-saved registers are restored from
it.
-/

namespace VG.Proof.Ed448.AArch64

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off limbs Outside Outside2 ofs far)
open VG.Impl.X448.AArch64 (slot ACC)
open VG.Spec.Ed448 (bytesAt decodeLE)
open VG.Proof.Ed448.AArch64.Window

local notation "EV" => VG.Proof.X448.AArch64.Weak.E
local notation "FV" => VG.Proof.X448.AArch64.Weak.F

theorem bytesAt_take57 (m : Mem) (p : Addr) : (bytesAt m p 114).take 57 = bytesAt m p 57 := by
  simp [Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem bytesAt_drop57 (m : Mem) (p : Addr) :
    (bytesAt m p 114).drop 57 = bytesAt m (p + BitVec.ofNat 64 57) 57 := by
  refine List.ext_getElem (by simp [Spec.Ed448.bytesAt]) fun i _ _ => ?_
  simp only [Spec.Ed448.bytesAt, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [Offset.add_add]

theorem bytesAt_len (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [Spec.Ed448.bytesAt]

theorem verifyEquation_correct (hR : RecoverOk) {s : State} (hp : verifyEquationLocal.pre s) :
    WP isa verifyEquation s fun t => (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      (∀ r ∈ preservedV, (t.v r).extractLsb' 0 64 = (s.v r).extractLsb' 0 64) ∧ verifyEquationLocal.post s t := by
  have htb := hp.2.2.2.2.2.2.tblAt (base := s.gpr .x3)
    (by rw [hp.1]; simp) (by simp)
  obtain ⟨hr, hw, hdk, hds, hdc, hn, -⟩ := hp
  obtain ⟨base, hbase⟩ : ∃ b, s.gpr .x3 = b := ⟨_, rfl⟩
  rw [hbase] at hdk hds hdc hn hw htb
  have hws : (⟨base, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  have rpk : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 i) 1 :=
    fun i h => ⟨⟨s.gpr .x0, 57⟩, by rw [hr]; simp, Offset.contains_base _ (d := i) (n := 1) (k := 57) h (by omega)⟩
  have rsg : ∀ i < 114, InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 i) 1 :=
    fun i h => ⟨⟨s.gpr .x1, 114⟩, by rw [hr]; simp, Offset.contains_base _ (d := i) (n := 1) (k := 114) h (by omega)⟩
  have rch : ∀ i < 57, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 1 :=
    fun i h => ⟨⟨s.gpr .x2, 57⟩, by rw [hr]; simp, Offset.contains_base _ (d := i) (n := 1) (k := 57) h (by omega)⟩
  have fpk : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x0 + BitVec.ofNat 64 i) := fun i hi => far hdk hi (by decide)
  have fsg : ∀ i < 114, 8192 ≤ ofs base (s.gpr .x1 + BitVec.ofNat 64 i) := fun i hi => far hds hi (by decide)
  have fch : ∀ i < 57, 8192 ≤ ofs base (s.gpr .x2 + BitVec.ofNat 64 i) := fun i hi => far hdc hi (by decide)
  obtain ⟨S, hS⟩ : ∃ S, decodeLE (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57) = S := ⟨_, rfl⟩
  have hSlt : S < 256 ^ 57 := by
    have h := VG.Proof.Ed448.decodeLE_lt' (bytesAt s.mem (s.gpr .x1 + BitVec.ofNat 64 57) 57)
    rwa [bytesAt_len, hS] at h
  unfold verifyEquation
  -- The entry, the checks and the decodings.
  refine WP.seq (WP.mono_syms (wfront_ok hR hbase hws hn rpk rsg rch fpk fsg fch) fun s1 F sy1 => ?_)
  have B1 : VG.Proof.X448.AArch64.Base.Bits 57 base S s1.mem := by
    rw [← hS]; exact F.bits
  have P1 : Persist base s.gpr s.v (fun i => s.mem (s.gpr .x2 + BitVec.ofNat 64 i)) s1.mem :=
    ⟨F.saved, F.savedX, F.savedV, F.lrs, F.kb⟩
  -- The table.
  refine WP.seq (WP.seq (WP.mono_syms (tabInit_ok F.scr F.bnd) fun s2 I sy2 =>
    WP.mono_syms (tabLoop_ok 14 s2 (by decide) (by decide) I.inv) fun s3 T sy3 => ?_))
  have P3 := (P1.iframe I.mem).tframe T.mem
  have B3 := Window.Bits.tframe (Window.Bits.iframe B1 I.mem) T.mem
  -- The comb's tables, untouched: everything so far wrote in the working space.
  have tb3 : VG.Proof.X448.AArch64.Base.TblAt s3 base (s3.syms Impl.X448.AArch64.Base.combSym) := by
    rw [sy3, sy2, sy1]
    refine htb.of_far (by rw [T.rd, T.wr, I.rd, I.wr, F.rd, F.wr]) fun x hx => ?_
    rw [T.mem x (Or.inr (by omega)) (Or.inr (by simp only [ACC]; omega)) (Or.inr (by simp only [TAB]; omega)),
      I.mem x (Or.inr (by omega)) (Or.inr (by simp only [RX]; omega)) (Or.inr (by simp only [TAB]; omega)),
      F.mem x (Or.inr hx)]
  -- `[S]B`.
  refine WP.seq (WP.mono (sBase_ok T.scr T.env T.zero hSlt B3 tb3)
    fun s4 ⟨hs4, b4, z4, rep4, o4, _, x4, rd4, wr4⟩ => ?_)
  -- `[k](-A)`, added.
  refine WP.seq (WP.seq (WP.mono (kInit_ok hs4 b4 z4 (T.tab.of_outside2 o4 (by decide)) rfl)
    fun s5 ⟨K5, o5, x5, rd5, wr5⟩ => WP.mono (kLoop_ok 57 s5 (by decide) (by decide) K5) fun s6 K6 => ?_))
  have P6 := ((P3.outside2 o4).outside2 o5).outside2 K6.ctx.mem
  have hrl : ∀ o, o = RX ∨ o = RY → ∀ i < 8, limbs s6.mem base o i = limbs s2.mem base o i := fun o ho i hi => by
    rw [rlimbs_outside2 K6.ctx.mem ho hi, rlimbs_outside2 o5 ho hi, rlimbs_outside2 o4 ho hi,
      rlimbs_tframe T.mem ho hi]
  have hrx : ∀ i < 8, limbs s6.mem base RX i = limbs s1.mem base (slot 8) i := fun i hi =>
    (hrl _ (.inl rfl) i hi).trans (I.rx i hi)
  have hry : ∀ i < 8, limbs s6.mem base RY i = limbs s1.mem base (slot 9) i := fun i hi =>
    (hrl _ (.inr rfl) i hi).trans (I.ry i hi)
  -- The comparison and the result.
  rw [WP.seq_iff]
  refine WP.mono (wcross_ok K6.ctx.scr K6.ctx.env K6.ctx.zero K6.ctx.one
    (ib_of_limbs hrx (F.bnd 8)) (ib_of_limbs hry (F.bnd 9)))
    fun s7 ⟨hs7, k7, o7, c7, b7⟩ => ?_
  have P7 := P6.outside2 o7
  refine WP.mono (wfinish_ok hs7 (fun i h1 h2 j hj => Nat.lt_trans (b7 i h1 h2 j hj) (by decide))
    P7.saved P7.savedX P7.lrs P7.savedV) fun t ⟨t0, t19, t20, tx, tv, t30, _, _, _⟩ => ⟨?_, ?_, ?_⟩
  · intro r hr
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact t19
    · exact t20
    · exact tx 0 (by decide)
    · exact tx 1 (by decide)
    · exact tx 2 (by decide)
    · exact tx 3 (by decide)
    · exact tx 4 (by decide)
    · exact tx 5 (by decide)
    · exact tx 6 (by decide)
    · exact tx 7 (by decide)
    · exact t30
  · intro r hr
    simp only [preservedV, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact tv 0 (by decide)
    · exact tv 1 (by decide)
    · exact tv 2 (by decide)
    · exact tv 3 (by decide)
    · exact tv 4 (by decide)
    · exact tv 5 (by decide)
    · exact tv 6 (by decide)
    · exact tv 7 (by decide)
  · show t.gpr .x0 = _
    obtain ⟨c0, cA, cR, hx, hc0, hcA, hcR⟩ := F.chk
    have hx7 : s7.gpr .x20 = 0 ||| c0 ||| cA ||| cR := by
      rw [k7.1 _ (by decide), K6.ctx.chk, x5, x4, T.chk, I.chk, hx]
    rw [t0]
    refine if_congr ?_ rfl rfl
    rw [hx7, or_eq_zero64, or_eq_zero64, or_eq_zero64]
    cases ha : Spec.Ed448.decodePoint (bytesAt s.mem (s.gpr .x0) 57) with
    | none =>
      rw [VG.Proof.Ed448.verifyEquation_none (Or.inl ha)]
      refine ⟨fun h => absurd (hcA.mp h.1.1.2) (by rw [ha]; decide), fun h => absurd h (by decide)⟩
    | some a =>
      cases hRr : Spec.Ed448.decodePoint (bytesAt s.mem (s.gpr .x1) 57) with
      | none =>
        rw [VG.Proof.Ed448.verifyEquation_none (Or.inr (by rw [bytesAt_take57]; exact hRr))]
        refine ⟨fun h => absurd (hcR.mp h.1.2) (by rw [hRr]; decide), fun h => absurd h (by decide)⟩
      | some r =>
        have cA0 : cA = 0 := hcA.mpr (by rw [ha]; rfl)
        have cR0 : cR = 0 := hcR.mpr (by rw [hRr]; rfl)
        obtain ⟨rX, rY, rZ⟩ := F.rr r hRr
        have hRpt : (⟨FV s6.mem base RX, FV s6.mem base RY, 1⟩ : Spec.Ed448.Point) = r := by
          rw [FV_of_limbs hrx, FV_of_limbs hry]
          cases r
          simp only at rX rY rZ
          rw [← rX, ← rY, ← rZ]
          rfl
        have hP : slotPt s1.mem base = VG.Proof.Ed448.negPoint a := F.na a ha
        have hSB := rep4
        rw [natCast_zsmul, ← hS, ← bytesAt_drop57] at hSB
        have P5 := (P3.outside2 o4).outside2 o5
        have hb : ∀ i (h : i < 57), s5.mem (off base (KB + i)) =
            (bytesAt s.mem (s.gpr .x2) 57)[i]'(by rw [bytesAt_len]; exact h) := fun i h => by
          rw [P5.kb i h]; simp [Spec.Ed448.bytesAt]
        rw [verifyEquation_eq (bytesAt_len _ _ _) (bytesAt_len _ _ _) (bytesAt_len _ _ _) ha
          (by rw [bytesAt_take57]; exact hRr) hSB _ hb, c7.c12, c7.c13, c7.c14, c7.c15, K6.sb, K6.q, hRpt, hP,
          bytesAt_drop57, hS, cA0, cR0]
        rw [hS] at hc0
        simp only [Nat.sub_zero, dbl2, Spec.Ed448.pointEqual, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
          true_and, and_true, hc0]

end VG.Proof.Ed448.AArch64
