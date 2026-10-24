module
public import VerifiedGarbage.Proof.Bignum.X86.PublicCall
public import VerifiedGarbage.Proof.Rsa.X86.RvMont

import VerifiedGarbage.Proof.Rsa.X86.RvCandidateSet
import VerifiedGarbage.Proof.Rsa.X86.RvMontTracked
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage
import VerifiedGarbage.Proof.Rsa.RecoverMath
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowExp
public import VerifiedGarbage.Proof.Rsa.X86.RvSquareStep
public import VerifiedGarbage.Proof.Rsa.X86.RvWindowTable

/-! # Exponentiation of a recovery candidate in Montgomery form -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Bignum.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem liveExp_table : TableLive liveExp := ⟨by decide, by decide, by decide⟩

/-- The arrays after the candidate's initialization. -/
abbrev candA (A V : Nat → Nat) : Nat → Nat := upd (upd A mG (V sCand + 2)) mY (A aO)

/-- The arrays with the candidate in Montgomery form. -/
abbrev candMontA (A V : Nat → Nat) (n m : Nat) : Nat → Nat :=
  upd (upd A mG ((V sCand + 2) * 2 ^ (64 * n) % m)) mY (A aO)

/-- The exponent's four-bit shifts that align it, `(32 W - c) / 4`. -/
abbrev alignShifts (g : Geo) (eLen dLen : Nat) : Nat := 8 * g.W - 2 * (dLen + eLen)

/-- The exponent `r`, aligned to the top of its words. -/
abbrev alignedExp (g : Geo) (r eLen dLen : Nat) : Nat := r * 2 ^ (32 * g.W - 8 * (dLen + eLen))

theorem geo_wide (g : Geo) (upper : g.n ≤ 128) : g.W ≤ 4 * 128 + 6 := by
  simp only [Geo.W, VG.Impl.Rsa.X86.Recover.wide, width]; omega

theorem alignStart_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {eLen dLen : Nat}
    (h : KS g s0 A liveM AW [wR] V slotsExp s) (zero : A aZ = 0) (candidate : V sCand < 100)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (hwide : 8 * (dLen + eLen) < 32 * g.W) (rb : AW wR < 2 ^ (8 * (dLen + eLen))) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.alignStart s
      (AI g s0 (candA A V) (upd AW wRc (AW wR)) V (AW wR) (alignShifts g eLen dLen) 0) := by
  have Wle := geo_wide g h.upper
  unfold VG.Impl.Rsa.X86.RecoverRt.alignStart
  refine WP.seq (WP.mono (candSet_ok h zero candidate) fun s1 h1 => ?_)
  refine WP.mono (alignCount_ok h1 ae ad hwide (by omega)) fun s2 h2 => ?_
  refine h2.mono (fun j hj => ⟨hj, rfl⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨by simp [hd], ?_⟩)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [upd_self, upd_self, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le rb (Nat.pow_le_pow_right (by decide) (by omega)))]
    · simp only [upd_ne _ _ (show wR ≠ wRc by decide)]
  · by_cases e : d = sCnt
    · subst e; rw [upd_self, upd_self, Nat.sub_zero]
    · rw [upd_ne _ _ e, upd_ne _ _ e]

theorem candMont_ok {g : Geo} {s0 s3 : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
    (h3 : AI g s0 (candA A V) (upd AW wRc (AW wR)) V (AW wR) (alignShifts g eLen dLen)
      (alignShifts g eLen dLen) s3)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1)
    (r2 : A mR2 = 2 ^ (128 * g.n) % m) (baseBound : V sCand + 2 < m)
    (hwide : 8 * (dLen + eLen) < 32 * g.W) (rb : AW wR < 2 ^ (8 * (dLen + eLen))) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.mmul mG mG mR2) s3 (KS g s0 (candMontA A V g.n m) liveExp
      (upd AW wRc (alignedExp g (AW wR) eLen dLen)) [wRc, wR] (upd V sCnt 0) slotsExp) := by
  have positive : 0 < m := by omega
  have Wle := geo_wide g h3.upper
  unfold AI at h3
  rw [Nat.sub_self] at h3
  have aligned : AW wR * 16 ^ alignShifts g eLen dLen % 2 ^ (32 * g.W) = alignedExp g (AW wR) eLen dLen := by
    have := aligned_value (L := 32 * g.W) rb (by omega) (by omega)
    rwa [show (32 * g.W - 8 * (dLen + eLen)) / 4 = alignShifts g eLen dLen by unfold alignShifts; omega]
      at this
  rw [aligned] at h3
  have mr3 := h3.montReady (m := m) (by simp [liveExp]) (by simp [slotsExp])
    (by simpa only [upd_ne _ _ (by decide : mBase ≠ mY), upd_ne _ _ (by decide : mBase ≠ mG)] using value)
    bound (by simpa only [upd_ne _ _ (by decide : sInv ≠ sCnt)] using inverse)
  refine WP.mono (h3.mmul mr3 (o := mG) (a := mG) (b := mR2)
    (by decide) (by decide) (by decide) (by decide) (by simp [liveExp]) (by simp [liveExp])
    (by simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_self] using baseBound)
    (by simpa only [upd_ne _ _ (by decide : mR2 ≠ mY), upd_ne _ _ (by decide : mR2 ≠ mG), r2] using
      Nat.mod_lt (2 ^ (128 * g.n)) positive)
    (by decide) (by decide)) fun s4 ⟨G, h4, _, _, glt, gv⟩ => ?_
  have gvalue : G = (V sCand + 2) * 2 ^ (64 * g.n) % m := by
    rw [← Nat.mod_eq_of_lt glt]
    apply VG.Proof.Rsa.g_mont (VG.Proof.Bignum.coprime_pow2 odd _)
      (R2 := 2 ^ (128 * g.n) % m)
    · rw [Nat.mod_mod, ← Nat.pow_add]; congr 2; omega
    · simpa only [upd_ne _ _ (by decide : mG ≠ mY), upd_self,
        upd_ne _ _ (by decide : mR2 ≠ mY), upd_ne _ _ (by decide : mR2 ≠ mG), r2] using gv
  rw [gvalue] at h4
  refine h4.mono (fun j hj => ⟨List.mem_cons_of_mem _ hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩)
    (fun d hd => ⟨hd, rfl⟩)
  · simp only [candA, candMontA]
    by_cases e : j = mG
    · subst e
      rw [upd_self, upd_ne _ _ (by decide : mG ≠ mY), upd_self]
    · by_cases y : j = mY
      · subst y; rw [upd_ne _ _ (by decide), upd_self, upd_self]
      · rw [upd_ne _ _ e, upd_ne _ _ y, upd_ne _ _ e, upd_ne _ _ y, upd_ne _ _ e]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [upd_self, upd_self]
    · simp only [upd_ne _ _ (show wR ≠ wRc by decide)]

theorem tableStart_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
    (h : KS g s0 (tableA (candMontA A V g.n m) g.n m (V sCand + 2) 16) (List.range 16 ++ liveExp)
      (upd AW wRc (alignedExp g (AW wR) eLen dLen)) [wRc, wR] (upd V sCnt 0) slotsExp s)
    (one : A aO = 2 ^ (64 * g.n) % m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (hwide : 8 * (dLen + eLen) < 32 * g.W) (rb : AW wR < 2 ^ (8 * (dLen + eLen))) :
    WP isa (.block windowCount) s
      (WI g s0 (tableA (candMontA A V g.n m) g.n m (V sCand + 2) 16) AW V m (V sCand + 2)
        (alignedExp g (AW wR) eLen dLen) (2 * (dLen + eLen)) 0) := by
  have Wle := geo_wide g h.upper
  have small : alignedExp g (AW wR) eLen dLen < 2 ^ (32 * g.W) := by
    have := Nat.mul_lt_mul_of_pos_right rb (Nat.two_pow_pos (32 * g.W - 8 * (dLen + eLen)))
    rwa [← Nat.pow_add, show 8 * (dLen + eLen) + (32 * g.W - 8 * (dLen + eLen)) = 32 * g.W by omega]
      at this
  refine WP.mono (windowCount_ok h ae ad (by omega)) fun t ht => ?_
  unfold WI
  refine ht.mono (fun j hj => ⟨hj, ?_⟩) (fun j hj => ⟨hj, ?_⟩) (fun d hd => ⟨by simp [hd], ?_⟩)
  · by_cases y : j = mY
    · subst y
      rw [upd_self, Nat.pow_zero, Nat.mul_one, Nat.div_eq_of_lt small, Nat.pow_zero, Nat.one_mul]
      simp only [tableA, show ¬ mY < 16 by decide, ↓reduceIte, candMontA]
      rw [upd_self, one]
    · rw [upd_ne _ _ y]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · rw [upd_self, upd_self, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt small]
    · simp only [upd_ne _ _ (show wR ≠ wRc by decide)]
  · by_cases e : d = sCnt
    · subst e; rw [upd_self, upd_self, Nat.sub_zero]
    · rw [upd_ne _ _ e, upd_ne _ _ e, upd_ne _ _ e]

theorem candTable_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
    (h : KS g s0 (candMontA A V g.n m) liveExp
      (upd AW wRc (alignedExp g (AW wR) eLen dLen)) [wRc, wR] (upd V sCnt 0) slotsExp s)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1)
    (one : A aO = 2 ^ (64 * g.n) % m) (positive : 0 < m) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.table s (KS g s0 (tableA (candMontA A V g.n m) g.n m (V sCand + 2) 16)
      (List.range 16 ++ liveExp) (upd AW wRc (alignedExp g (AW wR) eLen dLen)) [wRc, wR]
      (upd V sCnt 0) slotsExp) :=
  table_ok h liveExp_table (by decide) (by decide) (by decide) (by decide)
    (by simp only [candMontA]; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact value) bound
    (by rw [upd_ne _ _ (by decide)]; exact inverse) odd positive
    (by simp only [candMontA]; rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact one)
    (by simp only [candMontA]; rw [upd_ne _ _ (by decide), upd_self])

/-- The windows' result, as the squaring loop's start. -/
theorem windows_done {g : Geo} {s0 t : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
    (ht : WI g s0 (tableA (candMontA A V g.n m) g.n m (V sCand + 2) 16) AW V m (V sCand + 2)
      (alignedExp g (AW wR) eLen dLen) (2 * (dLen + eLen)) (2 * (dLen + eLen)) t)
    (hwide : 8 * (dLen + eLen) < 32 * g.W) :
    KS g s0 (upd A mY (Spec.Rsa.powMod (V sCand + 2) (AW wR) m * 2 ^ (64 * g.n) % m)) liveSq
      AW [wR] (upd V sCnt 0) slotsExp t := by
  unfold WI at ht
  have wv := windows_value (r := AW wR) (c := 8 * (dLen + eLen)) (L := 32 * g.W) (by omega) (by omega)
  have wr := windows_rest (r := AW wR) (c := 8 * (dLen + eLen)) (L := 32 * g.W) (by omega) (by omega)
  rw [show 8 * (dLen + eLen) / 4 = 2 * (dLen + eLen) by omega] at wv wr
  rw [Nat.sub_self, wv, wr] at ht
  refine ht.mono (fun j hj => ⟨?_, ?_⟩) (fun j hj => ⟨?_, ?_⟩) (fun d hd => ⟨hd, ?_⟩)
  · simp only [liveSq, liveM, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · by_cases y : j = mY
    · subst y
      rw [upd_self, upd_self, VG.Proof.Bignum.powMod_eq, Nat.mod_mul_mod]
    · have facts : ¬ j < 16 ∧ j ≠ mG := by
        simp only [liveSq, liveM, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl y | decide
      obtain ⟨big, ng⟩ := facts
      rw [upd_ne _ _ y, upd_ne _ _ y]
      simp only [tableA, big, ↓reduceIte, candMontA]
      rw [upd_ne _ _ y, upd_ne _ _ ng]
  · simp only [List.mem_singleton] at hj; subst hj; simp
  · simp only [List.mem_singleton] at hj; subst hj; rw [upd_ne _ _ (by decide)]
  · rfl

theorem candExp_ok {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m eLen dLen : Nat}
    (h : KS g s0 A liveM AW [wR] V slotsExp s) (zero : A aZ = 0)
    (value : A mBase = m) (bound : m < 2 ^ (64 * g.n))
    (inverse : (m * V sInv + 1) % 2 ^ 32 = 0) (odd : m % 2 = 1)
    (one : A aO = 2 ^ (64 * g.n) % m) (r2 : A mR2 = 2 ^ (128 * g.n) % m)
    (candidate : V sCand < 100) (baseBound : V sCand + 2 < m)
    (ae : CallArgument s0 g.B g.Z 7 (BitVec.ofNat 32 eLen))
    (ad : CallArgument s0 g.B g.Z 9 (BitVec.ofNat 32 dLen))
    (count : 0 < 8 * (dLen + eLen)) (limit : 8 * (dLen + eLen) ≤ 16384)
    (hwide : 8 * (dLen + eLen) < 32 * g.W) (rb : AW wR < 2 ^ (8 * (dLen + eLen))) :
    WP isa VG.Impl.Rsa.X86.RecoverRt.candExp s fun t =>
      KS g s0 (upd A mY (Spec.Rsa.powMod (V sCand + 2) (AW wR) m * 2 ^ (64 * g.n) % m)) liveSq
        AW [wR] (upd V sCnt 0) slotsExp t := by
  have positive : 0 < m := by omega
  have Wle := geo_wide g h.upper
  unfold VG.Impl.Rsa.X86.RecoverRt.candExp
  simp only [seqs]
  refine WP.seq (WP.mono (alignStart_ok h zero candidate ae ad hwide rb) fun s1 h1 => ?_)
  refine WP.seq (WP.mono (alignLoop_ok h1 (by unfold alignShifts; omega) (by unfold alignShifts; omega))
    fun s2 h2 => ?_)
  refine WP.seq (WP.mono (candMont_ok h2 value bound inverse odd r2 baseBound hwide rb) fun s3 h3 => ?_)
  refine WP.seq (WP.mono (candTable_ok h3 value bound inverse odd one positive) fun s4 h4 => ?_)
  refine WP.seq (WP.mono (tableStart_ok h4 one ae ad hwide rb) fun s5 h5 => ?_)
  refine WP.mono (windowLoop_ok h5 (fun j hj => by simp only [tableA, hj, ↓reduceIte])
    (by simp only [tableA, show ¬ mBase < 16 by decide, ↓reduceIte, candMontA]
        rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact value)
    bound inverse odd positive (by omega) (by omega)) fun t ht => ?_
  exact windows_done ht hwide

end VG.Proof.Rsa.X86.Recover
