module

public import VerifiedGarbage.Proof.MlKem.RISCV64.Lay
public import VerifiedGarbage.Impl.MlKem.RISCV64.Top
import VerifiedGarbage.Proof.MlKem.RISCV64.Sample
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run

/-!
# ML-KEM on RISC-V: saving and restoring our caller's registers

As on PPC64LE (`Proof/MlKem/PPC64LE/TopSave.lean`): the top-level functions
save our caller's `s3`–`s11` and our return address in `scratch`, at 1288
(`topSave_ok`: `TopSaved`), and restore them at the end (`topEnd_ok`),
returning `s4`.
-/

@[expose] public section

namespace VG.Proof.MlKem.RISCV64

open VG VG.RISCV64 VG.Impl.MlKem.RISCV64
open VG.Impl.Sha3.RISCV64.Stream (mov)

theorem mem_rd_wr' {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- The registers the top-level functions save. -/
def savedTop : List Reg := [.s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- Our caller's `s3`–`s11` and return address, saved at `P + 1288`. -/
structure TopSaved (m : Mem) (P : Addr) (s₀ : State) : Prop where
  v3 : m.readW (P + BitVec.ofNat 64 1288) 64 = s₀.gpr .s3
  v4 : m.readW (P + BitVec.ofNat 64 1296) 64 = s₀.gpr .s4
  v5 : m.readW (P + BitVec.ofNat 64 1304) 64 = s₀.gpr .s5
  v6 : m.readW (P + BitVec.ofNat 64 1312) 64 = s₀.gpr .s6
  v7 : m.readW (P + BitVec.ofNat 64 1320) 64 = s₀.gpr .s7
  v8 : m.readW (P + BitVec.ofNat 64 1328) 64 = s₀.gpr .s8
  v9 : m.readW (P + BitVec.ofNat 64 1336) 64 = s₀.gpr .s9
  v10 : m.readW (P + BitVec.ofNat 64 1344) 64 = s₀.gpr .s10
  v11 : m.readW (P + BitVec.ofNat 64 1352) 64 = s₀.gpr .s11
  vra : m.readW (P + BitVec.ofNat 64 1360) 64 = s₀.gpr .ra

/-- Where they are saved. -/
abbrev saveR (P : Addr) : Region := ⟨P + BitVec.ofNat 64 1288, 80⟩

theorem saveR_contains (P : Addr) {o : Nat} (h₁ : 1288 ≤ o) (h₂ : o + 8 ≤ 1368) :
    (saveR P).Contains (P + BitVec.ofNat 64 o) 8 :=
  Offset.contains _ h₁ (by omega) (by decide)

/-- `TopSaved` through a change of memory apart from where they are saved. -/
theorem TopSaved.keep {m m' : Mem} {P : Addr} {s₀ : State} (h : TopSaved m P s₀) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (saveR P).Disjoint r) : TopSaved m' P s₀ := by
  have k : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 →
      m'.readW (P + BitVec.ofNat 64 o) 64 = m.readW (P + BitVec.ofNat 64 o) 64 :=
    fun o h₁ h₂ => hf.readW (saveR_contains P h₁ h₂) hd (by decide)
  exact ⟨(k 1288 (by decide) (by decide)).trans h.v3, (k 1296 (by decide) (by decide)).trans h.v4,
    (k 1304 (by decide) (by decide)).trans h.v5, (k 1312 (by decide) (by decide)).trans h.v6,
    (k 1320 (by decide) (by decide)).trans h.v7, (k 1328 (by decide) (by decide)).trans h.v8,
    (k 1336 (by decide) (by decide)).trans h.v9, (k 1344 (by decide) (by decide)).trans h.v10,
    (k 1352 (by decide) (by decide)).trans h.v11, (k 1360 (by decide) (by decide)).trans h.vra⟩

theorem topSave_eq (b : Reg) : topSave b = [.store .d .s3 b 1288, .store .d .s4 b 1296,
    .store .d .s5 b 1304, .store .d .s6 b 1312, .store .d .s7 b 1320, .store .d .s8 b 1328,
    .store .d .s9 b 1336, .store .d .s10 b 1344, .store .d .s11 b 1352, .store .d .ra b 1360] := rfl

theorem topEnd_eq : topEnd = [mov .a0 .s4, .load .d .ra .s11 1360, .load .d .s3 .s11 1288,
    .load .d .s4 .s11 1296, .load .d .s5 .s11 1304, .load .d .s6 .s11 1312, .load .d .s7 .s11 1320,
    .load .d .s8 .s11 1328, .load .d .s9 .s11 1336, .load .d .s10 .s11 1344, .load .d .s11 .s11 1352] := rfl

/-- A doubleword at an offset of an aligned pointer is aligned. -/
theorem al8 {P : Addr} (hP : P.toNat % 8 = 0) {o : Nat} (ho : o % 8 = 0) :
    (P + BitVec.ofNat 64 o).toNat % 8 = 0 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A doubleword store, as `sd` makes it. -/
theorem write8_eq (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := rfl

/-- Our caller's registers and return address saved, with `scratch` in `b`. -/
theorem topSave_ok {s : State} {b : Reg} {P : Addr} (hP : s.gpr b = P) (hal : P.toNat % 8 = 0)
    (hw : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions s.wr (P + BitVec.ofNat 64 o) 8) :
    WP isa (.block (topSave b)) s fun s' => TopSaved s'.mem P s ∧ Frame [saveR P] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have w0 := hw 1288 (by decide) (by decide)
  have w1 := hw 1296 (by decide) (by decide)
  have w2 := hw 1304 (by decide) (by decide)
  have w3 := hw 1312 (by decide) (by decide)
  have w4 := hw 1320 (by decide) (by decide)
  have w5 := hw 1328 (by decide) (by decide)
  have w6 := hw 1336 (by decide) (by decide)
  have w7 := hw 1344 (by decide) (by decide)
  have w8 := hw 1352 (by decide) (by decide)
  have w9 := hw 1360 (by decide) (by decide)
  have a0 := al8 hal (o := 1288) (by decide)
  have a1 := al8 hal (o := 1296) (by decide)
  have a2 := al8 hal (o := 1304) (by decide)
  have a3 := al8 hal (o := 1312) (by decide)
  have a4 := al8 hal (o := 1320) (by decide)
  have a5 := al8 hal (o := 1328) (by decide)
  have a6 := al8 hal (o := 1336) (by decide)
  have a7 := al8 hal (o := 1344) (by decide)
  have a8 := al8 hal (o := 1352) (by decide)
  have a9 := al8 hal (o := 1360) (by decide)
  rw [topSave_eq]
  crun [hP, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  simp only [write8_eq]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals first
    | (simp (disch := decide) only [Sample.readW_writeW_off, Mem.readW_writeW_self64]; done)
    | ((repeat (first | exact Frame.refl _ _ |
        refine Frame.writeW ?_ (List.mem_singleton_self _) _ (saveR_contains _ (by decide) (by decide)))); done)
    | skip

/-- The return value, and our caller's registers and return address restored. -/
theorem topEnd_ok {s₀ s : State} {P : Addr} (h11 : s.gpr .s11 = P) (hal : P.toNat % 8 = 0)
    (hsav : TopSaved s.mem P s₀)
    (hin : ∀ o, 1288 ≤ o → o + 8 ≤ 1368 → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 o) 8)
    (hcs : ∀ r ∈ preserved, r ∉ savedTop → s.gpr r = s₀.gpr r) :
    WP isa (.block topEnd) s fun s' => (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ s'.gpr .ra = s₀.gpr .ra ∧
      s'.gpr .a0 = s.gpr .s4 ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i0 := hin 1288 (by decide) (by decide)
  have i1 := hin 1296 (by decide) (by decide)
  have i2 := hin 1304 (by decide) (by decide)
  have i3 := hin 1312 (by decide) (by decide)
  have i4 := hin 1320 (by decide) (by decide)
  have i5 := hin 1328 (by decide) (by decide)
  have i6 := hin 1336 (by decide) (by decide)
  have i7 := hin 1344 (by decide) (by decide)
  have i8 := hin 1352 (by decide) (by decide)
  have i9 := hin 1360 (by decide) (by decide)
  have a0 := al8 hal (o := 1288) (by decide)
  have a1 := al8 hal (o := 1296) (by decide)
  have a2 := al8 hal (o := 1304) (by decide)
  have a3 := al8 hal (o := 1312) (by decide)
  have a4 := al8 hal (o := 1320) (by decide)
  have a5 := al8 hal (o := 1328) (by decide)
  have a6 := al8 hal (o := 1336) (by decide)
  have a7 := al8 hal (o := 1344) (by decide)
  have a8 := al8 hal (o := 1352) (by decide)
  have a9 := al8 hal (o := 1360) (by decide)
  have hk : WP isa (.block topEnd) s fun s' =>
      s'.gpr .a0 = s.gpr .s4 ∧ s'.gpr .ra = s.mem.readW (P + BitVec.ofNat 64 1360) 64 ∧
      s'.gpr .s3 = s.mem.readW (P + BitVec.ofNat 64 1288) 64 ∧
      s'.gpr .s4 = s.mem.readW (P + BitVec.ofNat 64 1296) 64 ∧
      s'.gpr .s5 = s.mem.readW (P + BitVec.ofNat 64 1304) 64 ∧
      s'.gpr .s6 = s.mem.readW (P + BitVec.ofNat 64 1312) 64 ∧
      s'.gpr .s7 = s.mem.readW (P + BitVec.ofNat 64 1320) 64 ∧
      s'.gpr .s8 = s.mem.readW (P + BitVec.ofNat 64 1328) 64 ∧
      s'.gpr .s9 = s.mem.readW (P + BitVec.ofNat 64 1336) 64 ∧
      s'.gpr .s10 = s.mem.readW (P + BitVec.ofNat 64 1344) 64 ∧
      s'.gpr .s11 = s.mem.readW (P + BitVec.ofNat 64 1352) 64 ∧
      (∀ r ∈ preserved, r ∉ savedTop → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
    rw [topEnd_eq]
    crun [mov, h11, i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr hs => ?_⟩
    all_goals first | rfl | skip
    have h0 : r ≠ .a0 := by rintro rfl; simp [preserved] at hr
    have h3 : r ≠ .ra := by rintro rfl; simp [preserved] at hr
    simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false, not_or] at hs
    obtain ⟨a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hs
    simp [a3, a4, a5, a6, a7, a8, a9, a10, a11, h0, h3]
  refine WP.mono hk fun s' ⟨r3, ra, g3, g4, g5, g6, g7, g8, g9, g10, g11, cs, m, sp, rd, wr⟩ =>
    ⟨fun r hr => ?_, ra.trans hsav.vra, r3, m, sp, rd, wr⟩
  by_cases hs : r ∈ savedTop
  · simp only [savedTop, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [g3.trans hsav.v3, g4.trans hsav.v4, g5.trans hsav.v5, g6.trans hsav.v6, g7.trans hsav.v7,
      g8.trans hsav.v8, g9.trans hsav.v9, g10.trans hsav.v10, g11.trans hsav.v11]
  · exact (cs r hr hs).trans (hcs r hr hs)

end VG.Proof.MlKem.RISCV64
