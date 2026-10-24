module

public import VerifiedGarbage.Proof.Rc2.PPC64LE.KeySteps
public import VerifiedGarbage.Proof.Rc2.Expansion
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep

/-!
# RC2 on PPC64LE: the loops of key expansion

Each loop keeps `KEnv` (the arguments, PITABLE in the working space, the key
and our caller's saved registers) and builds `L` in the schedule
(`Proof.Rc2.BytesPrefix`): `copy_loop`, `fill_loop`, `descend_loop`.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- Our caller's registers kept in the working space. -/
def keySaved : List (Reg × Nat) := [(.r14, 256), (.r15, 264)]

/-- What the loops keep. -/
structure KEnv (K S W : Addr) (len bits : Nat) (key : List Byte) (g : Reg → BitVec 64) (s : State) : Prop where
  r3 : s.gpr .r3 = K
  r4 : s.gpr .r4 = BitVec.ofNat 64 len
  r5 : s.gpr .r5 = BitVec.ofNat 64 bits
  r6 : s.gpr .r6 = S
  pi : PiEnv W s
  rd : s.rd = [⟨K, len⟩]
  wr : s.wr = [⟨S, 128⟩, ⟨W, 512⟩]
  key : ∀ c < len, s.mem (K + BitVec.ofNat 64 c) = key.getD c 0
  saved : Spill.Saved W g keySaved s.mem

/-- The constant facts about the regions. -/
structure KRegions (K S W : Addr) (len : Nat) : Prop where
  hlen : 1 ≤ len ∧ len ≤ 128
  kS : (⟨K, len⟩ : Region).Disjoint ⟨S, 128⟩
  SW : (⟨S, 128⟩ : Region).Disjoint ⟨W, 512⟩

theorem KEnv.keep {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64} {s t : State}
    (E : KEnv K S W len bits key g s) {rs : List Reg} (k : Keep rs s t)
    (h : Reg.r3 ∉ rs ∧ Reg.r4 ∉ rs ∧ Reg.r5 ∉ rs ∧ Reg.r6 ∉ rs ∧ Reg.r7 ∉ rs) (hm : t.mem = s.mem) :
    KEnv K S W len bits key g t :=
  ⟨by rw [k.gpr h.1]; exact E.r3, by rw [k.gpr h.2.1]; exact E.r4, by rw [k.gpr h.2.2.1]; exact E.r5,
    by rw [k.gpr h.2.2.2.1]; exact E.r6, E.pi.keep k h.2.2.2.2 hm, by rw [k.2.1]; exact E.rd,
    by rw [k.2.2]; exact E.wr, by rw [hm]; exact E.key, by rw [hm]; exact E.saved⟩

theorem keyTemps_ok : Reg.r3 ∉ keyTemps ∧ Reg.r4 ∉ keyTemps ∧ Reg.r5 ∉ keyTemps ∧ Reg.r6 ∉ keyTemps ∧
    Reg.r7 ∉ keyTemps := by decide

/-- After a step that writes byte `i` of `L`. -/
theorem KEnv.write {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64} {s t : State}
    (E : KEnv K S W len bits key g s) (R : KRegions K S W len) (k : Keep keyTemps s t) {i : Nat} (hi : i < 128)
    {b : Byte} (hm : t.mem = s.mem.writeW (S + BitVec.ofNat 64 i) b) : KEnv K S W len bits key g t := by
  have F : Frame [⟨S, 128⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))
  refine ⟨by rw [k.gpr (by decide)]; exact E.r3, by rw [k.gpr (by decide)]; exact E.r4,
    by rw [k.gpr (by decide)]; exact E.r5, by rw [k.gpr (by decide)]; exact E.r6,
    ⟨by rw [k.gpr (by decide)]; exact E.pi.r7, fun j hj => by rw [k.2.1, k.2.2]; exact E.pi.rd j hj, fun j hj => ?_⟩,
    by rw [k.2.1]; exact E.rd, by rw [k.2.2]; exact E.wr, fun c hc => ?_, E.saved.frame F fun p hp r hr => ?_⟩
  · rw [F.readW (r := ⟨W, 512⟩) (Offset.contains_base _ (by rw [Proof.Rc2.piQuads_length] at hj; omega)
      (by rw [Proof.Rc2.piQuads_length] at hj; omega)) (by simpa using R.SW.symm) (by decide)]
    exact E.pi.held j hj
  · rw [F.bytes (R := ⟨K, len⟩) (by simpa using R.kS) (by have := R.hlen; simp; omega) hc]
    exact E.key c hc
  · simp only [List.mem_singleton] at hr; subst hr
    simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    refine (R.SW.symm.sub_left ?_)
    rcases hp with rfl | rfl <;> exact Offset.sub_base _ (by omega)

theorem copy_loop {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) (s : State) (E : KEnv K S W len bits key g s) (h8 : s.gpr .r8 = 0#64) :
    WP isa (.loop (.block copyKey) (.nonzero .d .r0)) s fun t =>
      KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 len ∧
        Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) len := by
  have hl := R.hlen
  refine countLoop _ _ (fun i t => KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 i ∧
      Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) i) len (fun i hi t ⟨E, h8, P⟩ => ?_) 0 (by omega) s
    ⟨E, h8, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.mono (copy_run t (by rw [E.rd, E.wr, E.r3, h8]; exact ⟨⟨K, len⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩)
    (by rw [E.wr, E.r6, h8]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩))
    fun t' ⟨a, b, m, k⟩ => ?_
  rw [E.r6, E.r3, h8, E.key i hi] at m
  refine ⟨⟨E.write R (k.mono (by simp)) (by omega) m, by rw [a, h8, succ_ofNat], ?_⟩, ?_⟩
  · rw [m, ← Proof.Rc2.initial_set key i]
    exact P.extend (by omega) _
  · rw [b, h8, E.r4, succ_ofNat, sub_bne (by omega) (by omega)]

theorem fill_loop {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) (hk : key.length = len) (hl : len < 128) (s : State) (E : KEnv K S W len bits key g s)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 len) (P : Proof.Rc2.BytesPrefix s.mem S (Proof.Rc2.fill key 0) len) :
    WP isa (.loop fillKey (.nonzero .d .r0)) s fun t =>
      KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 128 ∧
        Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl1 := R.hlen
  refine countLoop _ _ (fun i t => KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 i ∧
      Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (i - len)) i ∧ len ≤ i) 128
    (fun i hi t ⟨E, h8, P, hli⟩ => ?_) len hl s ⟨E, h8, by rw [Nat.sub_self]; exact P, Nat.le_refl _⟩
    |> fun h => WP.mono h fun t ⟨a, b, c, _⟩ => ⟨a, b, c⟩
  have lo : t.gpr .r6 + t.gpr .r8 - 1#64 = S + BitVec.ofNat 64 (i - 1) := by
    rw [E.r6, h8, Offset.add_ofNat_sub S (by omega)]
  have hi' : t.gpr .r6 + (t.gpr .r8 - t.gpr .r4) = S + BitVec.ofNat 64 (i - len) := by
    rw [E.r6, h8, E.r4, Offset.ofNat_sub_ofNat hli]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (fill_run t E.pi (by rw [lo]; exact inS' _ (by omega)) (by rw [hi']; exact inS' _ (by omega))
    (by rw [E.r6, h8]; exact inS i hi)) fun t' ⟨a, b, m, k⟩ => ?_
  rw [lo, hi', E.r6, h8, P (i - 1) (by omega), P (i - len) (by omega)] at m
  refine ⟨⟨E.write R k hi m, by rw [a, h8, succ_ofNat], ?_, by omega⟩, ?_⟩
  · have e : Proof.Rc2.fill key (i + 1 - len) = (Proof.Rc2.fill key (i - len)).set! i
        (Spec.Rc2.pi ((Proof.Rc2.fill key (i - len)).getD (i - 1) 0 +
          (Proof.Rc2.fill key (i - len)).getD (i - len) 0)) := by
      rw [show i + 1 - len = (i - len) + 1 by omega, Proof.Rc2.fill_succ]
      simp only [Proof.Rc2.fillStep, hk]
      rw [show len + (i - len) = i by omega]
    rw [m, e]
    exact P.extend (by omega) _
  · rw [b, h8, succ_ofNat, sub_bne (by omega) (by omega)]

theorem descend_loop {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) {t8 : Nat} (ht8 : 1 ≤ t8 ∧ t8 < 128) (l : Proof.Rc2.KeyBytes) (s : State)
    (E : KEnv K S W len bits key g s) (h8 : s.gpr .r8 = BitVec.ofNat 64 (128 - t8))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 t8) (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa (.loop descendKey (.nonzero .d .r8)) s fun t =>
      KEnv K S W len bits key g t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 (128 - t8)) 128 := by
  refine countLoop _ _ (fun j t => KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 (128 - t8 - j) ∧
      t.gpr .r14 = BitVec.ofNat 64 t8 ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 j) 128) (128 - t8)
    (fun j hj t ⟨E, h8, h14, P⟩ => ?_) 0 (by omega) s ⟨E, by rw [h8, Nat.sub_zero], h14, P⟩
    |> fun h => WP.mono h fun t ⟨a, _, _, c⟩ => ⟨a, c⟩
  have hd : t.gpr .r8 - 1#64 = BitVec.ofNat 64 (127 - t8 - j) := by
    rw [h8, Offset.ofNat_sub_ofNat (by omega), show 128 - t8 - j - 1 = 127 - t8 - j by omega]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have lo : t.gpr .r6 + (t.gpr .r8 - 1#64) + 1#64 = S + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [E.r6, hd, Offset.add_add]
  have hi' : t.gpr .r6 + (t.gpr .r8 - 1#64 + t.gpr .r14) = S + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [E.r6, hd, h14, BitVec.ofNat_add_ofNat]
  refine WP.mono (descend_run t E.pi (by rw [lo]; exact inS' _ (by omega)) (by rw [hi']; exact inS' _ (by omega))
    (by rw [E.r6, hd]; exact inS _ (by omega))) fun t' ⟨a, m, k⟩ => ?_
  rw [lo, hi', E.r6, hd, P _ (by omega), P _ (by omega)] at m
  refine ⟨⟨E.write R k (by omega) m, by rw [a, hd, show 128 - t8 - (j + 1) = 127 - t8 - j by omega],
    by rw [k.gpr (by decide), h14], ?_⟩, ?_⟩
  · rw [m, Proof.Rc2.descend_succ]
    exact P.write (by decide) (by omega) _
  · rw [a, hd, ofNat_bne_zero (by omega)]
    congr 1
    exact decide_eq_decide.mpr (by omega)

end VG.Proof.Rc2.PPC64LE
