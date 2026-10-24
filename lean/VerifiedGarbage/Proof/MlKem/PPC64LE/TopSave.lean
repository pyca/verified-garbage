module

public import VerifiedGarbage.Proof.MlKem.PPC64LE.Lay
public import VerifiedGarbage.Impl.MlKem.PPC64LE.Top
import VerifiedGarbage.Proof.MlKem.PPC64LE.Sample
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# ML-KEM on PPC64LE: saving and restoring our caller's registers

The top-level functions save our caller's `r24`–`r31` and our return address
in `scratch`, at 840 (`topSave_ok`: `TopSaved`), and restore them at the end
(`topEnd_ok`), returning `r24`.
-/

@[expose] public section

namespace VG.Proof.MlKem.PPC64LE

open VG VG.PPC64LE VG.Impl.MlKem.PPC64LE
open VG.Impl.Sha3.PPC64LE.Stream (mov)

theorem mem_rd_wr' {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The registers the top-level functions save. -/
def savedTop : List Reg := [.r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

/-- Our caller's `r24`–`r31` and return address, saved at `P + 840`. -/
structure TopSaved (m : Mem) (P : Addr) (s₀ : State) : Prop where
  s24 : m.readW (P + BitVec.ofNat 64 840) 64 = s₀.gpr .r24
  s25 : m.readW (P + BitVec.ofNat 64 848) 64 = s₀.gpr .r25
  s26 : m.readW (P + BitVec.ofNat 64 856) 64 = s₀.gpr .r26
  s27 : m.readW (P + BitVec.ofNat 64 864) 64 = s₀.gpr .r27
  s28 : m.readW (P + BitVec.ofNat 64 872) 64 = s₀.gpr .r28
  s29 : m.readW (P + BitVec.ofNat 64 880) 64 = s₀.gpr .r29
  s30 : m.readW (P + BitVec.ofNat 64 888) 64 = s₀.gpr .r30
  s31 : m.readW (P + BitVec.ofNat 64 896) 64 = s₀.gpr .r31
  slr : m.readW (P + BitVec.ofNat 64 904) 64 = s₀.lr

/-- Where they are saved. -/
abbrev saveR (P : Addr) : Region := ⟨P + BitVec.ofNat 64 840, 72⟩

theorem saveR_contains (P : Addr) {o : Nat} (h₁ : 840 ≤ o) (h₂ : o + 8 ≤ 912) :
    (saveR P).Contains (P + BitVec.ofNat 64 o) 8 :=
  Offset.contains _ h₁ (by omega) (by decide)

/-- `TopSaved` through a change of memory apart from where they are saved. -/
theorem TopSaved.keep {m m' : Mem} {P : Addr} {s₀ : State} (h : TopSaved m P s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR P).Disjoint r) : TopSaved m' P s₀ := by
  have k : ∀ o, 840 ≤ o → o + 8 ≤ 912 → m'.readW (P + BitVec.ofNat 64 o) 64 = m.readW (P + BitVec.ofNat 64 o) 64 :=
    fun o h₁ h₂ => hf.readW (saveR_contains P h₁ h₂) hd (by decide)
  exact ⟨(k 840 (by decide) (by decide)).trans h.s24, (k 848 (by decide) (by decide)).trans h.s25,
    (k 856 (by decide) (by decide)).trans h.s26, (k 864 (by decide) (by decide)).trans h.s27,
    (k 872 (by decide) (by decide)).trans h.s28, (k 880 (by decide) (by decide)).trans h.s29,
    (k 888 (by decide) (by decide)).trans h.s30, (k 896 (by decide) (by decide)).trans h.s31,
    (k 904 (by decide) (by decide)).trans h.slr⟩

theorem topSave_eq (b : Reg) : topSave b = [.mflr .r0, .store .d .r24 b 840, .store .d .r25 b 848,
    .store .d .r26 b 856, .store .d .r27 b 864, .store .d .r28 b 872, .store .d .r29 b 880, .store .d .r30 b 888,
    .store .d .r31 b 896, .store .d .r0 b 904] := rfl

theorem topEnd_eq : topEnd = [mov .r3 .r24, .load .d .r0 .r31 904, .mtlr .r0, .load .d .r24 .r31 840,
    .load .d .r25 .r31 848, .load .d .r26 .r31 856, .load .d .r27 .r31 864, .load .d .r28 .r31 872,
    .load .d .r29 .r31 880, .load .d .r30 .r31 888, .load .d .r31 .r31 896] := rfl

/-- Our caller's registers and return address saved, with `scratch` in `b`. -/
theorem topSave_ok {s : State} {b : Reg} {P : Addr} (hb : b = .r6 ∨ b = .r7) (hP : s.gpr b = P)
    (hw : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions s.wr (P + BitVec.ofNat 64 o) 8) :
    WP isa (.block (topSave b)) s fun s' => TopSaved s'.mem P s ∧ Frame [saveR P] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.lr = s.lr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have w840 := hw 840 (by decide) (by decide)
  have w848 := hw 848 (by decide) (by decide)
  have w856 := hw 856 (by decide) (by decide)
  have w864 := hw 864 (by decide) (by decide)
  have w872 := hw 872 (by decide) (by decide)
  have w880 := hw 880 (by decide) (by decide)
  have w888 := hw 888 (by decide) (by decide)
  have w896 := hw 896 (by decide) (by decide)
  have w904 := hw 904 (by decide) (by decide)
  rw [topSave_eq]
  rcases hb with rfl | rfl <;>
  · prun [hP, w840, w848, w856, w864, w872, w880, w888, w896, w904]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, fun r hr => ?_, trivial⟩
    all_goals first
      | (simp (disch := decide) only [Sample.readW_writeW_off, Mem.readW_writeW_self64]; done)
      | exact RegUpd.gpr_write_of_ne _ _ hr
      | ((repeat (first | exact Frame.refl _ _ |
          refine Frame.writeW ?_ (List.mem_singleton_self _) _ (saveR_contains _ (by decide) (by decide)))); done)

/-- The return value, and our caller's registers and return address restored. -/
theorem topEnd_ok {s₀ s : State} {P : Addr} (h31 : s.gpr .r31 = P) (hsav : TopSaved s.mem P s₀)
    (hin : ∀ o, 840 ≤ o → o + 8 ≤ 912 → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 o) 8)
    (hcs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.lr = s₀.lr ∧
      s'.gpr .r3 = s.gpr .r24 ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i840 := hin 840 (by decide) (by decide)
  have i848 := hin 848 (by decide) (by decide)
  have i856 := hin 856 (by decide) (by decide)
  have i864 := hin 864 (by decide) (by decide)
  have i872 := hin 872 (by decide) (by decide)
  have i880 := hin 880 (by decide) (by decide)
  have i888 := hin 888 (by decide) (by decide)
  have i896 := hin 896 (by decide) (by decide)
  have i904 := hin 904 (by decide) (by decide)
  have hk : WP isa (.block topEnd) s fun s' =>
      s'.gpr .r3 = s.gpr .r24 ∧ s'.lr = s₀.lr ∧ s'.gpr .r24 = s₀.gpr .r24 ∧ s'.gpr .r25 = s₀.gpr .r25 ∧
      s'.gpr .r26 = s₀.gpr .r26 ∧ s'.gpr .r27 = s₀.gpr .r27 ∧ s'.gpr .r28 = s₀.gpr .r28 ∧
      s'.gpr .r29 = s₀.gpr .r29 ∧ s'.gpr .r30 = s₀.gpr .r30 ∧ s'.gpr .r31 = s₀.gpr .r31 ∧
      (∀ r ∈ preserved, r ∉ savedTop → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [topEnd_eq]
    prun [h31, i840, i848, i856, i864, i872, i880, i888, i896, i904, hsav.s24, hsav.s25, hsav.s26, hsav.s27,
      hsav.s28, hsav.s29, hsav.s30, hsav.s31, hsav.slr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr hs => ?_, ?_⟩ <;> try first | exact trivial | rfl
    have h0 : r ≠ .r0 := by rintro rfl; simp [preserved] at hr
    have h3 : r ≠ .r3 := by rintro rfl; simp [preserved] at hr
    simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    obtain ⟨a24, a25, a26, a27, a28, a29, a30, a31⟩ := hs
    simp only [RegUpd.gpr_write, a24, a25, a26, a27, a28, a29, a30, a31, h0, h3, ite_false]
  refine WP.mono hk fun s' ⟨r3, lr, g24, g25, g26, g27, g28, g29, g30, g31, cs, m, sp, rd, wr⟩ =>
    ⟨fun r hr => ?_, lr, r3, m, sp, rd, wr⟩
  by_cases hs : r ∈ savedTop
  · simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g24, g25, g26, g27, g28, g29, g30, g31]
  · exact (cs r hr hs).trans (hcs r hr hs)

end VG.Proof.MlKem.PPC64LE
