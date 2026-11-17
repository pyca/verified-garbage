module

public import VerifiedGarbage.Proof.Rc2.Expansion
public import VerifiedGarbage.Proof.Framework.PPC64LE.Spill
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.PPC64LE.Keep
public import VerifiedGarbage.Impl.Rc2.PPC64LE.ExpandKey
public import VerifiedGarbage.Proof.Rc2.Table
public import VerifiedGarbage.Proof.Rc2.PPC64LE.Lookup

/-! ### `Rc2.PPC64LE.KeySteps`, which only this module used -/

section

/-!
# RC2 on PPC64LE: the steps of key expansion

`piLookup_run`: the scan of PITABLE in the working space leaves `pi q` in
`r11`. Each step of the loops (`copy_run`, `fill_run`, `reduce_run`,
`descend_run`) stores one byte of `L`.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

/-- The scan of PITABLE at `r7`. -/
theorem piLookup_run (s : State) {W : Addr} (hW : s.gpr .r7 = W) (hq : (s.gpr .r10).toNat < 256)
    (hr : ∀ o n, o + n ≤ 256 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o) n)
    (hP : Proof.Rc2.PiHeld s.mem W) :
    WP isa piLookup s fun t =>
      t.gpr .r11 = (Spec.Rc2.pi ((s.gpr .r10).setWidth 8)).setWidth 64 ∧
      Keep [.r0, .r11, .r12, .r15] s t ∧ t.mem = s.mem := by
  refine WP.mono (WP.keep [.r0, .r11, .r12, .r15] (piScan_run s hW hq (fun i hi => chunks_in hr (by omega_using [hi])))
    (by decide) rfl) fun t ⟨⟨t11, tm⟩, tk⟩ => ⟨?_, tk, tm⟩
  have e : W + s.gpr .r10 = W + BitVec.ofNat 64 (s.gpr .r10).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [t11, e, hP.byte hq]
  refine congrArg (BitVec.setWidth 64) ?_
  simp only [Spec.Rc2.pi, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt hq]

theorem lo8_ext (b : BitVec 8) : (b.setWidth 64).setWidth 8 = b :=
  BitVec.setWidth_setWidth_of_le _ (by decide) |>.trans (BitVec.setWidth_eq b)

theorem copy_run (s : State) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r3 + s.gpr .r8) 1)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa (.block copyKey) s fun t =>
      t.gpr .r8 = s.gpr .r8 + 1 ∧ t.gpr .r0 = s.gpr .r8 + 1 - s.gpr .r4 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8) (s.mem (s.gpr .r3 + s.gpr .r8)) ∧
      Keep [.r0, .r8, .r9, .r12] s t := by
  refine WP.mono (WP.keep [.r0, .r8, .r9, .r12] (c := .block copyKey) (Q := fun t =>
      t.gpr .r8 = s.gpr .r8 + 1 ∧ t.gpr .r0 = s.gpr .r8 + 1 - s.gpr .r4 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8) (s.mem (s.gpr .r3 + s.gpr .r8))) ?_
    (by rfl) rfl) fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  unfold copyKey
  rrun [hr, hw, lo8_ext]

theorem ext_lt (b : BitVec 8) : (b.setWidth 64).toNat < 256 := by
  rw [BitVec.toNat_setWidth]; have := b.isLt; omega_using []

theorem ext_and (a : BitVec 8) (y : BitVec 64) : a.setWidth 64 &&& y = (a &&& y.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, BitVec.getLsbD_of_ge a i (by omega_using [h])]

theorem ext_xor (a b : BitVec 8) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [BitVec.getLsbD_of_ge a i (by omega_using [h]), BitVec.getLsbD_of_ge b i (by omega_using [h])]

theorem ext_add (a b : BitVec 8) : ((a.setWidth 64 + b.setWidth 64) <<< 56) >>> 56 = (a + b).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt; have hb := b.isLt
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega_using []), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega_using []),
    Nat.mod_eq_of_lt (show a.toNat + b.toNat < 2 ^ 64 by omega_using [])]
  omega_using []

/-- The registers the steps of key expansion write. -/
abbrev keyTemps : List Reg := [.r0, .r8, .r9, .r10, .r11, .r12, .r15]

/-- The scan's environment: PITABLE at `W` in the working space at `r7`. -/
structure PiEnv (W : Addr) (s : State) : Prop where
  r7 : s.gpr .r7 = W
  rd : ∀ o n, o + n ≤ 256 → InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o) n
  held : Proof.Rc2.PiHeld s.mem W

theorem PiEnv.keep {W : Addr} {s t : State} (E : PiEnv W s) {rs : List Reg} (k : Keep rs s t)
    (h7 : Reg.r7 ∉ rs) (hm : t.mem = s.mem) : PiEnv W t :=
  ⟨by rw [k.gpr h7]; exact E.r7, fun o n h => by rw [k.2.1, k.2.2]; exact E.rd o n h, by rw [hm]; exact E.held⟩

/-- A byte through the scan and into `L[i]`: the scan and `storeKey`. -/
theorem piStore_run (s : State) {W : Addr} (E : PiEnv W s) (hq : (s.gpr .r10).toNat < 256)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa (.seq piLookup (.block storeKey)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8) (Spec.Rc2.pi ((s.gpr .r10).setWidth 8)) ∧
      Keep [.r0, .r11, .r12, .r15, .r9] s t := by
  apply WP.seq
  refine WP.mono (piLookup_run s E.r7 hq E.rd E.held) fun t₁ ⟨a₁, k₁, m₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  have h8 : t₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  refine WP.mono (WP.keep [.r9] (c := .block storeKey) (Q := fun t =>
      t.mem = t₁.mem.writeW (t₁.gpr .r6 + t₁.gpr .r8) ((t₁.gpr .r11).setWidth 8)) ?_
    (by rfl) rfl) fun t ⟨a, k⟩ =>
      ⟨by rw [a, a₁, m₁, h6, h8, lo8_ext], (k₁.trans k).mono (by simp)⟩
  unfold storeKey
  rrun [show InRegions t₁.wr (t₁.gpr .r6 + t₁.gpr .r8) 1 by rw [k₁.2.2, h6, h8]; exact hw]

theorem fill_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .r6 + s.gpr .r8 - 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .r6 + (s.gpr .r8 - s.gpr .r4)) 1)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa fillKey s fun t =>
      t.gpr .r8 = s.gpr .r8 + 1 ∧ t.gpr .r0 = s.gpr .r8 + 1 - 128#64 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8)
        (Spec.Rc2.pi (s.mem (s.gpr .r6 + s.gpr .r8 - 1#64) + s.mem (s.gpr .r6 + (s.gpr .r8 - s.gpr .r4)))) ∧
      Keep keyTemps s t := by
  unfold fillKey
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r10, .r11] (c := .block fillInput) (Q := fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r6 + s.gpr .r8 - 1#64) + s.mem (s.gpr .r6 + (s.gpr .r8 - s.gpr .r4))).setWidth 64 ∧
      t.mem = s.mem) (by unfold fillInput mask; rrun [hlo, hhi, ext_add])
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  have h8 : t₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  apply WP.seq
  refine WP.mono (piLookup_run t₁ (E.keep k₁ (by decide) m₁).r7 (by rw [a₁]; exact ext_lt _)
    (E.keep k₁ (by decide) m₁).rd (E.keep k₁ (by decide) m₁).held) fun t₂ ⟨a₂, k₂, m₂⟩ => ?_
  have h6' : t₂.gpr .r6 = s.gpr .r6 := by rw [k₂.gpr (by decide), h6]
  have h8' : t₂.gpr .r8 = s.gpr .r8 := by rw [k₂.gpr (by decide), h8]
  refine WP.mono (WP.keep [.r0, .r8, .r9] (c := .block fillFinish) (Q := fun t =>
      t.gpr .r8 = t₂.gpr .r8 + 1 ∧ t.gpr .r0 = t₂.gpr .r8 + 1 - 128#64 ∧
      t.mem = t₂.mem.writeW (t₂.gpr .r6 + t₂.gpr .r8) ((t₂.gpr .r11).setWidth 8)) ?_
    (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, k⟩ => ⟨by rw [a, h8'], by rw [b, h8'], by rw [c, a₂, m₂, m₁, h6', h8', a₁, lo8_ext, lo8_ext],
      ((k₁.trans k₂).trans k).mono (by simp)⟩
  unfold fillFinish storeKey
  rrun [show InRegions t₂.wr (t₂.gpr .r6 + t₂.gpr .r8) 1 by rw [k₂.2.2, k₁.2.2, h6', h8']; exact hw]

theorem reduce_run (s : State) {W : Addr} (E : PiEnv W s) (hr : InRegions (s.rd ++ s.wr) (s.gpr .r6 + s.gpr .r8) 1)
    (hw : InRegions s.wr (s.gpr .r6 + s.gpr .r8) 1) :
    WP isa reduceKey s fun t =>
      t.mem = s.mem.writeW (s.gpr .r6 + s.gpr .r8)
        (Spec.Rc2.pi (s.mem (s.gpr .r6 + s.gpr .r8) &&& (s.gpr .r12).setWidth 8)) ∧
      Keep [.r0, .r9, .r10, .r11, .r12, .r15] s t := by
  unfold reduceKey
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r10] (c := .block reduceInput) (Q := fun t =>
      t.gpr .r10 = (s.mem (s.gpr .r6 + s.gpr .r8) &&& (s.gpr .r12).setWidth 8).setWidth 64 ∧
      t.mem = s.mem) (by unfold reduceInput; rrun [hr, ext_and])
    (by rfl) rfl) fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  have h8 : t₁.gpr .r8 = s.gpr .r8 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, h8]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [a, m₁, h6, h8, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

theorem descend_run (s : State) {W : Addr} (E : PiEnv W s)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .r6 + (s.gpr .r8 - 1#64) + 1#64) 1)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .r6 + (s.gpr .r8 - 1#64 + s.gpr .r14)) 1)
    (hw : InRegions s.wr (s.gpr .r6 + (s.gpr .r8 - 1#64)) 1) :
    WP isa descendKey s fun t =>
      t.gpr .r8 = s.gpr .r8 - 1#64 ∧
      t.mem = s.mem.writeW (s.gpr .r6 + (s.gpr .r8 - 1#64))
        (Spec.Rc2.pi (s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64) + 1#64) ^^^
          s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64 + s.gpr .r14)))) ∧
      Keep keyTemps s t := by
  unfold descendKey
  apply WP.seq
  refine WP.mono (WP.keep [.r8, .r9, .r10, .r11] (c := .block descendInput) (Q := fun t =>
      t.gpr .r8 = s.gpr .r8 - 1#64 ∧
      t.gpr .r10 = (s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64) + 1#64) ^^^
        s.mem (s.gpr .r6 + (s.gpr .r8 - 1#64 + s.gpr .r14))).setWidth 64 ∧
      t.mem = s.mem) (by unfold descendInput; rrun [hlo, hhi, ext_xor])
    (by rfl) rfl) fun t₁ ⟨⟨i₁, a₁, m₁⟩, k₁⟩ => ?_
  have h6 : t₁.gpr .r6 = s.gpr .r6 := k₁.gpr (by decide)
  refine WP.mono (piStore_run t₁ (E.keep k₁ (by decide) m₁) (by rw [a₁]; exact ext_lt _)
    (by rw [k₁.2.2, h6, i₁]; exact hw)) fun t ⟨a, k⟩ =>
      ⟨by rw [k.gpr (by decide), i₁], by rw [a, m₁, h6, i₁, a₁, lo8_ext], (k₁.trans k).mono (by simp)⟩

end VG.Proof.Rc2.PPC64LE

end

end

/-! ### `Rc2.PPC64LE.KeyLoop`, which only this module used -/

section

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

/-- After a step that writes byte `i` of `L`. -/
theorem KEnv.write {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64} {s t : State}
    (E : KEnv K S W len bits key g s) (R : KRegions K S W len) (k : Keep keyTemps s t) {i : Nat} (hi : i < 128)
    {b : Byte} (hm : t.mem = s.mem.writeW (S + BitVec.ofNat 64 i) b) : KEnv K S W len bits key g t := by
  have F : Frame [⟨S, 128⟩] s.mem t.mem := by
    rw [hm]; exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  refine ⟨by rw [k.gpr (by decide)]; exact E.r3, by rw [k.gpr (by decide)]; exact E.r4,
    by rw [k.gpr (by decide)]; exact E.r5, by rw [k.gpr (by decide)]; exact E.r6,
    ⟨by rw [k.gpr (by decide)]; exact E.pi.r7, fun o n h => by rw [k.2.1, k.2.2]; exact E.pi.rd o n h, fun j hj => ?_⟩,
    by rw [k.2.1]; exact E.rd, by rw [k.2.2]; exact E.wr, fun c hc => ?_, E.saved.frame F fun p hp r hr => ?_⟩
  · rw [F.readW (r := ⟨W, 512⟩) (Offset.contains_base _ (by rw [Proof.Rc2.piQuads_length] at hj; omega_arith)
      (by rw [Proof.Rc2.piQuads_length] at hj; omega_arith)) (by simpa using R.SW.symm) (by decide)]
    exact E.pi.held j hj
  · rw [F.bytes (R := ⟨K, len⟩) (by simpa using R.kS) (by have := R.hlen; simp; omega_arith) hc]
    exact E.key c hc
  · simp only [List.mem_singleton] at hr; subst hr
    simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    refine (R.SW.symm.sub_left ?_)
    rcases hp with rfl | rfl <;> exact Offset.sub_base _ (by omega_arith)

theorem copy_loop {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) (s : State) (E : KEnv K S W len bits key g s) (h8 : s.gpr .r8 = 0#64) :
    WP isa (.loop (.block copyKey) (.nonzero .d .r0)) s fun t =>
      KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 len ∧
        Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) len := by
  have hl := R.hlen
  refine countLoop _ _ (fun i t => KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 i ∧
      Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key 0) i) len (fun i hi t ⟨E, h8, P⟩ => ?_) 0 (by omega_arith) s
    ⟨E, h8, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.mono (copy_run t (by rw [E.rd, E.wr, E.r3, h8]; exact ⟨⟨K, len⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩)
    (by rw [E.wr, E.r6, h8]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩))
    fun t' ⟨a, b, m, k⟩ => ?_
  rw [E.r6, E.r3, h8, E.key i hi] at m
  refine ⟨⟨E.write R (k.mono (by simp)) (by omega_arith) m, by rw [a, h8, succ_ofNat], ?_⟩, ?_⟩
  · rw [m, ← Proof.Rc2.initial_set key i]
    exact P.extend (by omega_arith) _
  · rw [b, h8, E.r4, succ_ofNat, sub_bne (by omega_arith) (by omega_arith)]

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
    rw [E.r6, h8, Offset.add_ofNat_sub S (by omega_arith)]
  have hi' : t.gpr .r6 + (t.gpr .r8 - t.gpr .r4) = S + BitVec.ofNat 64 (i - len) := by
    rw [E.r6, h8, E.r4, Offset.ofNat_sub_ofNat hli]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (fill_run t E.pi (by rw [lo]; exact inS' _ (by omega_arith)) (by rw [hi']; exact inS' _ (by omega_arith))
    (by rw [E.r6, h8]; exact inS i hi)) fun t' ⟨a, b, m, k⟩ => ?_
  rw [lo, hi', E.r6, h8, P (i - 1) (by omega_arith), P (i - len) (by omega_arith)] at m
  refine ⟨⟨E.write R k hi m, by rw [a, h8, succ_ofNat], ?_, by omega_arith⟩, ?_⟩
  · have e : Proof.Rc2.fill key (i + 1 - len) = (Proof.Rc2.fill key (i - len)).set! i
        (Spec.Rc2.pi ((Proof.Rc2.fill key (i - len)).getD (i - 1) 0 +
          (Proof.Rc2.fill key (i - len)).getD (i - len) 0)) := by
      rw [show i + 1 - len = (i - len) + 1 by omega_arith, Proof.Rc2.fill_succ]
      simp only [Proof.Rc2.fillStep, hk]
      rw [show len + (i - len) = i by omega_arith]
    rw [m, e]
    exact P.extend (by omega_arith) _
  · rw [b, h8, succ_ofNat, sub_bne (by omega_arith) (by omega_arith)]

theorem descend_loop {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) {t8 : Nat} (ht8 : 1 ≤ t8 ∧ t8 < 128) (l : Proof.Rc2.KeyBytes) (s : State)
    (E : KEnv K S W len bits key g s) (h8 : s.gpr .r8 = BitVec.ofNat 64 (128 - t8))
    (h14 : s.gpr .r14 = BitVec.ofNat 64 t8) (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa (.loop descendKey (.nonzero .d .r8)) s fun t =>
      KEnv K S W len bits key g t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 (128 - t8)) 128 := by
  refine countLoop _ _ (fun j t => KEnv K S W len bits key g t ∧ t.gpr .r8 = BitVec.ofNat 64 (128 - t8 - j) ∧
      t.gpr .r14 = BitVec.ofNat 64 t8 ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.descend l t8 j) 128) (128 - t8)
    (fun j hj t ⟨E, h8, h14, P⟩ => ?_) 0 (by omega_arith) s ⟨E, by rw [h8, Nat.sub_zero], h14, P⟩
    |> fun h => WP.mono h fun t ⟨a, _, _, c⟩ => ⟨a, c⟩
  have hd : t.gpr .r8 - 1#64 = BitVec.ofNat 64 (127 - t8 - j) := by
    rw [h8, Offset.ofNat_sub_ofNat (by omega_arith), show 128 - t8 - j - 1 = 127 - t8 - j by omega_arith]
  have inS : ∀ c < 128, InRegions t.wr (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    rw [E.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  have inS' : ∀ c < 128, InRegions (t.rd ++ t.wr) (S + BitVec.ofNat 64 c) 1 := fun c hc => by
    obtain ⟨r, hr, hc⟩ := inS c hc; exact ⟨r, List.mem_append_right _ hr, hc⟩
  have lo : t.gpr .r6 + (t.gpr .r8 - 1#64) + 1#64 = S + BitVec.ofNat 64 (127 - t8 - j + 1) := by
    rw [E.r6, hd, Offset.add_add]
  have hi' : t.gpr .r6 + (t.gpr .r8 - 1#64 + t.gpr .r14) = S + BitVec.ofNat 64 (127 - t8 - j + t8) := by
    rw [E.r6, hd, h14, BitVec.ofNat_add_ofNat]
  refine WP.mono (descend_run t E.pi (by rw [lo]; exact inS' _ (by omega_arith)) (by rw [hi']; exact inS' _ (by omega_arith))
    (by rw [E.r6, hd]; exact inS _ (by omega_arith))) fun t' ⟨a, m, k⟩ => ?_
  rw [lo, hi', E.r6, hd, P _ (by omega_arith), P _ (by omega_arith)] at m
  refine ⟨⟨E.write R k (by omega_arith) m, by rw [a, hd, show 128 - t8 - (j + 1) = 127 - t8 - j by omega_arith],
    by rw [k.gpr (by decide), h14], ?_⟩, ?_⟩
  · rw [m, Proof.Rc2.descend_succ]
    exact P.write (by decide) (by omega_arith) _
  · rw [a, hd, ofNat_bne_zero (by omega_arith)]
    congr 1
    exact decide_eq_decide.mpr (by omega_arith)

end VG.Proof.Rc2.PPC64LE

end

end

/-! ### `Rc2.PPC64LE.KeyInit`, which only this module used -/

section

/-!
# RC2 on PPC64LE: the setup of key expansion

`piInit_run`: PITABLE's doublewords, from immediates, into the working space.
`maskCode_run`: `TM`, chosen by branches on the public `effective_bits mod 8`.
`reduceSetup_run`: `T8` and the index of the reduction.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem movImm64_val (v : BitVec 64) :
    (((v.extractLsb' 48 16 ++ (0 : BitVec 16)).signExtend 64 ||| (v.extractLsb' 32 16).setWidth 64) <<< 32 |||
      (v.extractLsb' 16 16).setWidth 64 <<< 16 ||| (v.extractLsb' 0 16).setWidth 64) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_signExtend, BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  by_cases h1 : i < 16
  · simp (disch := omega_arith) [h1, show i < 32 by omega_using [h1]]
  · by_cases h2 : i < 32
    · simp (disch := omega) [h1, h2, show i - 16 < 16 by omega_using [h2], show i - 16 < 64 by omega_using [hi],
        show 16 + (i - 16) = i by omega_using [h1]]
    · by_cases h3 : i < 48
      · simp (disch := omega) [h1, h2, show i - 32 < 16 by omega_using [h3], show ¬i - 16 < 16 by omega_using [h2],
          show i - 32 < 64 by omega_using [hi], show i - 32 < 32 by omega_using [hi], show 32 + (i - 32) = i by omega_using [h2]]
      · simp (disch := omega) [h1, h2, show ¬i - 16 < 16 by omega_using [h2], show i - 32 < 32 by omega_using [hi],
          show ¬i - 32 < 16 by omega_using [h3], show i - 32 < 64 by omega_using [hi], show i - 32 - 16 < 16 by omega_using [hi],
          show 48 + (i - 32 - 16) = i by omega_using [h3]]

theorem movImm64_run (u : State) (v : BitVec 64) :
    WP isa (.block (movImm64 .r12 v)) u fun t => t.gpr .r12 = v ∧ t.mem = u.mem ∧ Keep [.r12] u t := by
  refine WP.mono (WP.keep [.r12] (c := .block (movImm64 .r12 v)) (Q := fun t => t.gpr .r12 = v ∧ t.mem = u.mem) ?_
    (by rfl) rfl) fun t ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩
  unfold movImm64
  rrun
  exact movImm64_val v

theorem piInit_steps (u : State) {W : Addr} (hW : u.gpr .r7 = W)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    ∀ n ≤ 32, WP isa (.block ((List.range n).flatMap fun k =>
        movImm64 .r12 (Impl.Rc2.piQuad k) ++ ([.store .d .r12 .r7 (8 * k)] : List Instr))) u fun t =>
      (∀ i < n, t.mem.readW (W + BitVec.ofNat 64 (8 * i)) 64 = Impl.Rc2.piQuad i) ∧
      Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.r12] u t := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ h => absurd h (Nat.not_lt_zero _), Frame.refl _ _, Keep.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega_using [hn])) fun t ⟨held, F, k⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (movImm64_run t _) fun t₁ ⟨a₁, m₁, k₁⟩ => ?_
    have h7 : t₁.gpr .r7 = W := by rw [k₁.gpr (by decide), k.gpr (by decide), hW]
    refine WP.mono (WP.keep [] (c := .block [.store .d .r12 .r7 (8 * n)]) (Q := fun t₂ =>
        t₂.mem = t₁.mem.writeW (W + BitVec.ofNat 64 (8 * n)) (Impl.Rc2.piQuad n)) ?_
      (by rfl) rfl) fun t₂ ⟨m₂, k₂⟩ => ⟨fun i hi => ?_, ?_, ?_⟩
    · rrun [h7, a₁, show 8 * n < 32768 by omega_using [hn], show 8 * n % 4 = 0 by omega_using [],
        show InRegions t₁.wr (W + BitVec.ofNat 64 (8 * n)) 8 by rw [k₁.2.2, k.2.2]; exact hw n (by omega_using [hn])]
    · rw [m₂, m₁]
      by_cases e : i = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (Offset.sep W (by omega_using [e]) (by omega_using [hn, hi]) (by omega_using [hn])) (by decide)]
        exact held i (by omega_using [hi, e])
    · rw [m₂, m₁]; exact F.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega_using [hn]) (by omega_using [hn]))
    · exact ((k.trans k₁).trans k₂).mono (by simp)

theorem piInit_run (u : State) {W : Addr} (hW : u.gpr .r7 = W)
    (hw : ∀ k < 32, InRegions u.wr (W + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block piInit) u fun t =>
      Proof.Rc2.PiHeld t.mem W ∧ Frame [⟨W, 256⟩] u.mem t.mem ∧ Keep [.r12] u t :=
  WP.mono (piInit_steps u hW hw 32 (Nat.le_refl _)) fun _ ⟨held, F, k⟩ =>
    ⟨fun i hi => by rw [Proof.Rc2.piQuads_length] at hi; rw [held i hi, Proof.Rc2.piQuads_getD hi], F, k⟩

/-- `TM` for `c = effective_bits mod 8`. -/
def maskVal (c : Nat) : Nat := if c = 0 then 255 else 2 ^ c - 1

theorem sub_beq_zero {c k : Nat} (hc : c < 8) (hk : k < 8) :
    (BitVec.ofNat 64 c - BitVec.ofNat 64 k == 0#64) = decide (c = k) := by
  by_cases h : c = k
  · subst h; simp
  · have : BitVec.ofNat 64 c - BitVec.ofNat 64 k ≠ 0#64 := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc]), Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega_using [hk])] at this
      omega_using [hc, hk, h, this]
    simp [this, h]

theorem mask_loop {c₀ : Nat} (hc : c₀ < 8) : ∀ n k, k + n = 7 → ∀ u : State, u.gpr .r9 = BitVec.ofNat 64 c₀ →
    u.gpr .r12 = BitVec.ofNat 64 (if 1 ≤ c₀ ∧ c₀ ≤ k then 2 ^ c₀ - 1 else 255) →
    WP isa ((List.range' k n).foldr (fun c rest => .seq (.block [.subi .r10 .r9 (c + 1)])
        (.seq (.ite (.zero .d .r10) (.block [.li .r12 (2 ^ (c + 1) - 1)]) (.block [])) rest)) (.block [])) u
      fun t => t.gpr .r12 = BitVec.ofNat 64 (maskVal c₀) ∧ t.mem = u.mem ∧ Keep [.r10, .r12] u t := by
  intro n
  induction n with
  | zero =>
    intro k hk u _ h12
    refine WP.block_nil ⟨?_, rfl, Keep.refl _ _⟩
    rw [h12]; unfold maskVal
    by_cases h : c₀ = 0
    · rw [ite_eq_right (by omega_using [h]), ite_eq_left h]
    · rw [ite_eq_left (by omega_using [hc, hk, h]), ite_eq_right h]
  | succ n ih =>
    intro k hk u h9 h12
    rw [List.range'_succ, List.foldr_cons]
    apply WP.seq
    refine WP.mono (WP.keep [.r10] (c := .block [.subi .r10 .r9 (k + 1)]) (Q := fun t =>
        t.gpr .r10 = u.gpr .r9 - BitVec.ofNat 64 (k + 1) ∧ t.mem = u.mem)
      (by rrun [show k + 1 ≤ 32768 by omega_using [hk]]) (by rfl) rfl)
      fun t₁ ⟨⟨a₁, m₁⟩, k₁⟩ => ?_
    apply WP.seq
    have hb : isa.eval (.zero .d .r10) t₁ = some (decide (c₀ = k + 1)) := by
      rw [eval_zero, a₁, h9, sub_beq_zero hc (by omega_using [hk])]
    refine WP.ite _ hb (fun ht => ?_) (fun hf => ?_)
    · have e : c₀ = k + 1 := of_decide_eq_true ht
      have hli : 2 ^ (k + 1) - 1 < 2 ^ 15 := by
        have : 2 ^ (k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega_using [hk])
        omega_using [this]
      refine WP.mono (WP.keep [.r12] (c := .block [.li .r12 (2 ^ (k + 1) - 1)]) (Q := fun t =>
          t.gpr .r12 = BitVec.ofNat 64 (2 ^ (k + 1) - 1) ∧ t.mem = t₁.mem)
        (by rrun [hli])
        (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
      refine WP.mono (ih (k + 1) (by omega_using [hk]) t₂ (by rw [k₂.gpr (by decide), k₁.gpr (by decide), h9])
        (by rw [a₂, ite_eq_left (by omega_using [e]), e])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₂, m₁], ((k₁.trans k₂).trans kk).mono (by simp)⟩
    · have e : c₀ ≠ k + 1 := of_decide_eq_false hf
      refine WP.block_nil ?_
      refine WP.mono (ih (k + 1) (by omega_using [hk]) t₁ (by rw [k₁.gpr (by decide), h9])
        (by
          rw [k₁.gpr (by decide), h12]
          by_cases h : 1 ≤ c₀ ∧ c₀ ≤ k
          · rw [ite_eq_left h, ite_eq_left (by omega_using [h])]
          · rw [ite_eq_right h, ite_eq_right (by omega_using [e, h])])) fun t ⟨a, m, kk⟩ =>
          ⟨a, by rw [m, m₁], (k₁.trans kk).mono (by simp)⟩

theorem low3 (bits : Nat) (hb : bits < 2 ^ 64) :
    (BitVec.ofNat 64 bits <<< 61) >>> 61 = BitVec.ofNat 64 (bits % 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (show bits % 8 < 2 ^ 64 by omega_using [])]
  omega_using []

theorem maskCode_run (u : State) {bits : Nat} (hb : bits < 2 ^ 64) (h5 : u.gpr .r5 = BitVec.ofNat 64 bits) :
    WP isa maskCode u fun t => t.gpr .r12 = BitVec.ofNat 64 (maskVal (bits % 8)) ∧ t.mem = u.mem ∧
      Keep [.r9, .r10, .r12] u t := by
  unfold maskCode
  apply WP.seq
  refine WP.mono (WP.keep [.r9, .r12] (c := .block [.lsl .r9 .r5 61, .lsr .d .r9 .r9 61, .li .r12 255])
      (Q := fun t => t.gpr .r9 = BitVec.ofNat 64 (bits % 8) ∧ t.gpr .r12 = BitVec.ofNat 64 255 ∧ t.mem = u.mem)
    (by rrun [h5]; exact low3 bits hb) (by rfl) rfl)
    fun t₁ ⟨⟨a₁, b₁, m₁⟩, k₁⟩ => ?_
  rw [List.range_eq_range']
  refine WP.mono (mask_loop (c₀ := bits % 8) (by omega_using []) 7 0 rfl t₁ a₁ (by rw [b₁, ite_eq_right (by omega_using [])]))
    fun t ⟨a, m, k⟩ => ⟨a, by rw [m, m₁], (k₁.trans k).mono (by simp)⟩

theorem maskVal_eq {bits : Nat} : maskVal (bits % 8) = 255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8)) := by
  unfold maskVal
  by_cases h : bits % 8 = 0
  · rw [ite_eq_left h, show 8 + bits - 8 * ((bits + 7) / 8) = 8 by omega_using [h]]
  · rw [ite_eq_right h, show 8 + bits - 8 * ((bits + 7) / 8) = bits % 8 by omega_using [h]]
    have : ∀ c < 8, c ≠ 0 → 2 ^ c - 1 = 255 % 2 ^ c := by decide
    exact this _ (Nat.mod_lt _ (by decide)) h

theorem reduceSetup_run (u : State) {bits : Nat} (hb : bits ≤ 1024) (h5 : u.gpr .r5 = BitVec.ofNat 64 bits) :
    WP isa (.block reduceSetup) u fun t => t.gpr .r14 = BitVec.ofNat 64 ((bits + 7) / 8) ∧
      t.gpr .r8 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧ t.mem = u.mem ∧ Keep [.r8, .r14] u t := by
  refine WP.mono (WP.keep [.r8, .r14] (c := .block reduceSetup) (Q := fun t =>
      t.gpr .r14 = BitVec.ofNat 64 ((bits + 7) / 8) ∧ t.gpr .r8 = BitVec.ofNat 64 (128 - (bits + 7) / 8) ∧
        t.mem = u.mem) ?_ (by rfl) rfl)
    fun t ⟨⟨a, b, c⟩, d⟩ => ⟨a, b, c, d⟩
  have e14 : (BitVec.ofNat 64 bits + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((bits + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show bits < 2 ^ 64 by omega_using [hb]), Nat.mod_eq_of_lt (show (7 : Nat) < 2 ^ 64 by omega_using []),
      Nat.mod_eq_of_lt (show bits + 7 < 2 ^ 64 by omega_using [hb]), Nat.mod_eq_of_lt (show (bits + 7) / 8 < 2 ^ 64 by omega_using [hb])]
  have e8 : BitVec.ofNat 64 128 - BitVec.ofNat 64 ((bits + 7) / 8) = BitVec.ofNat 64 (128 - (bits + 7) / 8) :=
    Offset.ofNat_sub_ofNat (by omega_using [hb])
  unfold reduceSetup
  rrun [h5, e14, e8]

end VG.Proof.Rc2.PPC64LE

end

end


/-!
# RC2 on PPC64LE: key expansion

`expandKey_wp`: the schedule at `r6` becomes the expansion of the key at
`r3`; our caller's `r14` and `r15` are saved in the working space at `r7`
and restored.
-/

@[expose] public section

namespace VG.Proof.Rc2.PPC64LE

open VG VG.PPC64LE VG.Impl.Rc2.PPC64LE

theorem copyFill_run {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) (hk : key.length = len) (s : State) (E : KEnv K S W len bits key g s)
    (h8 : s.gpr .r8 = 0#64) :
    WP isa expandCopyFill s fun t =>
      KEnv K S W len bits key g t ∧ Proof.Rc2.BytesPrefix t.mem S (Proof.Rc2.fill key (128 - len)) 128 := by
  have hl := R.hlen
  unfold expandCopyFill
  apply WP.seq
  refine WP.mono (copy_loop R s E h8) fun t₁ ⟨E₁, a₁, P₁⟩ => ?_
  apply WP.seq
  refine WP.mono (WP.keep [.r0] (c := .block [.li .r0 128, .sub .r0 .r8 .r0]) (Q := fun t =>
      t.gpr .r0 = BitVec.ofNat 64 len - BitVec.ofNat 64 128 ∧ t.mem = t₁.mem) (by rrun [a₁])
    (by rfl) rfl) fun t₂ ⟨⟨a₂, m₂⟩, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have hb : isa.eval (.zero .d .r0) t₂ = some (decide (len = 128)) := by
    rw [eval_zero, a₂]
    exact congrArg some (Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith))
  refine WP.ite _ hb (fun ht => WP.block_nil ⟨E₂, ?_⟩) (fun hf => ?_)
  · have e : len = 128 := of_decide_eq_true ht
    rw [m₂, e, Nat.sub_self]; rw [e] at P₁; exact P₁
  · have e : len ≠ 128 := of_decide_eq_false hf
    exact WP.mono (fill_loop R hk (by omega_arith) t₂ E₂ (by rw [k₂.gpr (by decide), a₁]) (by rw [m₂]; exact P₁))
      fun _ ⟨a, _, c⟩ => ⟨a, c⟩

theorem setWidth_ofNat8 (x : Nat) : (BitVec.ofNat 64 x).setWidth 8 = BitVec.ofNat 8 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd _ (by decide)

theorem reducePhase_run {K S W : Addr} {len bits : Nat} {key : List Byte} {g : Reg → BitVec 64}
    (R : KRegions K S W len) (hb : 1 ≤ bits ∧ bits ≤ 1024) (s : State) (E : KEnv K S W len bits key g s)
    {l : Proof.Rc2.KeyBytes} (P : Proof.Rc2.BytesPrefix s.mem S l 128) :
    WP isa expandReduce s fun t =>
      KEnv K S W len bits key g t ∧ Proof.Rc2.BytesPrefix t.mem S
        (Proof.Rc2.descend (Proof.Rc2.reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128 := by
  let t8 := (bits + 7) / 8
  have ht8 : 1 ≤ t8 ∧ t8 ≤ 128 := ⟨by omega_arith, by omega_arith⟩
  unfold expandReduce
  apply WP.seq
  refine WP.mono (reduceSetup_run s hb.2 E.r5) fun t₁ ⟨a₁, b₁, m₁, k₁⟩ => ?_
  have E₁ := E.keep k₁ (by decide) m₁
  apply WP.seq
  refine WP.mono (maskCode_run t₁ (by omega_arith) E₁.r5) fun t₂ ⟨a₂, m₂, k₂⟩ => ?_
  have E₂ := E₁.keep k₂ (by decide) m₂
  have h8₂ : t₂.gpr .r8 = BitVec.ofNat 64 (128 - t8) := by rw [k₂.gpr (by decide), b₁]
  have at₂ : t₂.gpr .r6 + t₂.gpr .r8 = S + BitVec.ofNat 64 (128 - t8) := by rw [E₂.r6, h8₂]
  have inS : InRegions t₂.wr (S + BitVec.ofNat 64 (128 - t8)) 1 := by
    rw [E₂.wr]; exact ⟨⟨S, 128⟩, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  apply WP.seq
  refine WP.mono (reduce_run t₂ E₂.pi (by rw [at₂]; obtain ⟨r, hr, hc⟩ := inS; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [at₂]; exact inS)) fun t₃ ⟨m₃, k₃⟩ => ?_
  have P₂ : Proof.Rc2.BytesPrefix t₂.mem S l 128 := by rw [m₂, m₁]; exact P
  rw [at₂, a₂, setWidth_ofNat8, P₂ _ (by omega_arith), maskVal_eq] at m₃
  have E₃ := E₂.write R (k₃.mono (by simp)) (by omega_arith) m₃
  have P₃ : Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.reduce l bits) 128 := by
    rw [m₃]; exact P₂.write (by decide) (by omega_arith) _
  have h8₃ : t₃.gpr .r8 = BitVec.ofNat 64 (128 - t8) := by rw [k₃.gpr (by decide), h8₂]
  have hz : isa.eval (.zero .d .r8) t₃ = some (decide (128 - t8 = 0)) := by
    rw [eval_zero, h8₃, ofNat_beq_zero (by omega_arith)]
  refine WP.ite _ hz (fun ht => WP.block_nil ⟨E₃, ?_⟩) (fun hf => ?_)
  · have e : 128 - t8 = 0 := of_decide_eq_true ht
    show Proof.Rc2.BytesPrefix t₃.mem S (Proof.Rc2.descend (Proof.Rc2.reduce l bits) t8 (128 - t8)) 128
    rw [e]; exact P₃
  · have e : 128 - t8 ≠ 0 := of_decide_eq_false hf
    exact descend_loop R ⟨ht8.1, by omega_arith⟩ _ t₃ E₃ h8₃
      (by rw [k₃.gpr (by decide), k₂.gpr (by decide), a₁]) P₃

/-- What key expansion may assume. -/
structure KeyPre (s : State) : Prop where
  valid : Spec.Rc2.validKey (s.gpr .r4).toNat (s.gpr .r5).toNat
  rd : s.rd = [⟨s.gpr .r3, (s.gpr .r4).toNat⟩]
  wr : s.wr = [⟨s.gpr .r6, 128⟩, ⟨s.gpr .r7, 512⟩]
  kS : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r6, 128⟩
  kW : (⟨s.gpr .r3, (s.gpr .r4).toNat⟩ : Region).Disjoint ⟨s.gpr .r7, 512⟩
  SW : (⟨s.gpr .r6, 128⟩ : Region).Disjoint ⟨s.gpr .r7, 512⟩

/-- What key expansion guarantees. -/
structure KeyPost (s s' : State) : Prop where
  sched : Spec.Rc2.scheduleAt s'.mem (s.gpr .r6) =
    Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (s.gpr .r5).toNat
  saved : ∀ r ∈ keySaved.map Prod.fst, s'.gpr r = s.gpr r

theorem keySave_eq : keySave = Spill.saveCode .r7 keySaved := rfl
theorem keyRestore_eq : keyRestore = Spill.restoreCode .r7 keySaved := rfl

theorem bytesAt_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Rc2.bytesAt m p n).length = n := by
  simp [Spec.Rc2.bytesAt]

theorem expandKey_wp {s : State} (h : KeyPre s) : WP isa expandKey s (KeyPost s) := by
  let K := s.gpr .r3
  let len := (s.gpr .r4).toNat
  let bits := (s.gpr .r5).toNat
  let S := s.gpr .r6
  let W := s.gpr .r7
  let key := Spec.Rc2.bytesAt s.mem K len
  have hv := h.valid
  unfold Spec.Rc2.validKey at hv
  have R : KRegions K S W len := ⟨⟨hv.1, hv.2.1⟩, h.kS, h.SW⟩
  have wW : ∀ d, d + 8 ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.wr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ hd (by omega_arith)⟩
  have wW' : ∀ d n, d + n ≤ 512 → InRegions s.wr (W + BitVec.ofNat 64 d) n := fun d n hd => by
    rw [h.wr]; exact ⟨⟨W, 512⟩, by simp [W], Offset.contains_base _ hd (by omega_arith)⟩
  unfold expandKey
  apply WP.seq
  rw [List.append_assoc, keySave_eq]
  refine Spill.save_ok (by decide) (by decide) (fun p hp => by
    simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact wW _ (by decide)) ?_
  let M₀ := Spill.saveMem s.mem W s.gpr keySaved
  have F₀ : Frame [⟨W, 512⟩] s.mem M₀ := Spill.saveMem_frame_base (by decide) (by decide) _ _ _
  rw [WP.block_append_iff]
  refine WP.mono (piInit_run { s with mem := M₀ } rfl fun k hk => wW _ (by omega_arith)) fun t₁ ⟨held, F₁, k₁⟩ => ?_
  refine WP.mono (WP.keep [.r8] (c := .block [.li .r8 0]) (Q := fun t => t.gpr .r8 = 0#64 ∧ t.mem = t₁.mem)
    (by rrun) (by rfl) rfl) fun t₀ ⟨⟨a₀, m₀⟩, k₀⟩ => ?_
  have k01 := k₁.trans k₀
  have E₀ : KEnv K S W len bits key s.gpr t₀ := by
    refine ⟨k01.gpr (by decide), by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      by rw [k01.gpr (by decide)]; exact (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _) |>.symm,
      k01.gpr (by decide), ⟨k01.gpr (by decide), fun o n ho => ?_, by rw [m₀]; exact held⟩,
      by rw [k01.2.1]; exact h.rd, by rw [k01.2.2]; exact h.wr, fun c hc => ?_, ?_⟩
    · rw [k01.2.1, k01.2.2]
      obtain ⟨r, hr, hc⟩ := wW' o n (by omega_arith)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [m₀, F₁.bytes (R := ⟨K, len⟩) (by simpa using h.kW.sub_right (Region.sub_prefix (show 256 ≤ 512 by decide)))
        (by simp; omega_arith) hc]
      show M₀ (K + BitVec.ofNat 64 c) = _
      rw [F₀.bytes (R := ⟨K, len⟩) (by simpa using h.kW) (by simp; omega_arith) hc]
      exact (Proof.Rc2.bytesAt_getD _ _ _ _ hc).symm
    · rw [m₀]
      refine (Spill.saveMem_saved (by decide) s.mem W s.gpr).frame F₁ fun p hp r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact Offset.disjoint_base _ (by decide) (by decide)
  have hk : key.length = len := bytesAt_length _ _ _
  apply WP.seq
  refine WP.mono (copyFill_run R hk t₀ E₀ a₀) fun t₂ ⟨E₂, P₂⟩ => ?_
  apply WP.seq
  refine WP.mono (reducePhase_run R ⟨hv.2.2.1, hv.2.2.2⟩ t₂ E₂ P₂) fun t₃ ⟨E₃, P₃⟩ => ?_
  rw [keyRestore_eq]
  refine WP.mono (Spill.restore_wp (by decide) E₃.pi.r7 (by decide) (by decide) (fun p hp => ?_) E₃.saved)
    fun s' Rs => ⟨?_, fun r hr => ?_⟩
  · rw [E₃.rd, E₃.wr]
    simp only [keySaved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> exact ⟨⟨W, 512⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩
  · rw [Rs.mem]
    refine Proof.Rc2.scheduleAt_expanded ?_
    rw [Proof.Rc2.expandBytes_eq, hk]
    exact P₃
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact Rs.gpr p hp

end VG.Proof.Rc2.PPC64LE
