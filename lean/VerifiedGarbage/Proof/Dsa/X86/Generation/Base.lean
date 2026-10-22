module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # What every stage keeps

A stage changes only ranges of `scratch` and the stack below the saved
registers (`Env.Chg`); the tapes, the table, `out` and every state word
outside those ranges keep their bytes, so the stage keeps `Base`. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

namespace Env
variable {E : Env}

theorem Chg.refl (os : List (Nat × Nat)) (m : Mem) : E.Chg os m m := Frame.refl _ _

theorem Chg.trans {os : List (Nat × Nat)} {m₁ m₂ m₃ : Mem} (h₁ : E.Chg os m₁ m₂) (h₂ : E.Chg os m₂ m₃) :
    E.Chg os m₁ m₃ := Frame.trans h₁ h₂

theorem Chg.mono {os os' : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m') (hs : ∀ o ∈ os, o ∈ os') :
    E.Chg os' m m' :=
  Frame.mono h fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr ⊢
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · exact .inl ⟨o, hs o ho, rfl⟩
    · exact .inr rfl

/-- A range of `scratch` is a part of it. -/
theorem range_sub {o : Nat × Nat} (h : o.1 + o.2 ≤ E.size) :
    Region.Sub ⟨off E.base o.1, o.2⟩ E.scratchRegion :=
  Offset.sub_base E.base h

/-- A region apart from `scratch` and the stack is apart from every region
of a change. -/
theorem far_all {R : Region} (hR : R.Disjoint E.scratchRegion) (hS : R.Disjoint E.stackRegion)
    {os : List (Nat × Nat)} (hos : ∀ o ∈ os, o.1 + o.2 ≤ E.size) :
    ∀ r ∈ (os.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion], R.Disjoint r := by
  intro r hr
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨o, ho, rfl⟩ | rfl
  · exact hR.sub_right (range_sub (hos o ho))
  · exact hS

/-- A word of `scratch` apart from every range of a change keeps its value. -/
theorem Chg.word (v : E.Valid) {os : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m') {d : Nat}
    (hd : d + 4 ≤ E.size) (hos : ∀ o ∈ os, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + 4 ≤ o.1)) :
    m'.readW (off E.base d) 32 = m.readW (off E.base d) 32 := by
  have nw := v.scratchFit
  refine Frame.readW h (r := ⟨off E.base d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨o, ho, rfl⟩ | rfl
  · have := hos o ho
    exact Offset.disjoint E.base this.2.symm (by omega) (by omega)
  · exact v.scratchStack.sub_left (range_sub (o := (d, 4)) hd)

/-- The bytes of a region apart from `scratch` and the stack. -/
theorem Chg.bytesAt {os : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m') {R : Region}
    (hR : R.Disjoint E.scratchRegion) (hS : R.Disjoint E.stackRegion) (hos : ∀ o ∈ os, o.1 + o.2 ≤ E.size)
    (hl : R.len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt m' R.base R.len = Spec.Rsa.bytesAt m R.base R.len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  exact Frame.bytes h (far_all hR hS hos) hl hi

end Env

theorem Base.keep {E : Env} (v : E.Valid) {s t : State} (B : Base E s) {os : List (Nat × Nat)}
    (F : E.Chg os s.mem t.mem) (A : E.Apart os) (edi : t.gpr .edi = s.gpr .edi) (sp : t.gpr .esp = s.gpr .esp)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sy : t.syms = s.syms) : Base E t := by
  have hos : ∀ o ∈ os, o.1 + o.2 ≤ E.size := fun o ho => (A o ho).1
  have word : ∀ d, fOut ≤ d → d + 4 ≤ fWitLen + 4 → t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    fun d h₁ h₂ => Env.Chg.word v F (by have := v.room; simp only [fWitLen, hdr] at h₂; omega)
      fun o ho => ⟨(A o ho).1, by rcases (A o ho).2 with h | h <;> omega⟩
  have tapeEq : ∀ R ∈ [E.seedsRegion, E.hsRegion, E.witRegion],
      Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := fun R hR =>
    Env.Chg.bytesAt F (v.tapesFar R hR).1 (v.tapesFar R hR).2.2 hos (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have := v.seedsFit; have := v.hsFit; have := v.witFit
      rcases hR with rfl | rfl | rfl <;> simp only [Env.seedsRegion, Env.hsRegion, Env.witRegion] <;> omega)
  refine ⟨Scr.of_eq B.scr edi sp wr, sp.trans B.sp, rd ▸ B.tapes, rd ▸ B.table, wr ▸ B.out, sy ▸ B.syms, ?_,
    (tapeEq E.seedsRegion (by simp)).trans B.seeds, (tapeEq E.hsRegion (by simp)).trans B.hs,
    (tapeEq E.witRegion (by simp)).trans B.wit, (word fOut (by decide) (by decide)).trans B.outW,
    (word fHs (by decide) (by decide)).trans B.hsW, (word fHsLen (by decide) (by decide)).trans B.hsLenW,
    (word fWit (by decide) (by decide)).trans B.witW, (word fWitLen (by decide) (by decide)).trans B.witLenW⟩
  intro c hc i hi
  have h := B.held c hc i hi
  simp only [VG.Impl.RsaKeyGen.TrialTable32.consts, List.mem_singleton] at hc
  subst hc
  rw [sy]
  rw [← h]
  simp only [B.syms]
  have := v.tableFit
  have len : i < 1024 := by simpa [VG.Impl.RsaKeyGen.TrialTable32.packed] using hi
  refine Frame.readW F (r := E.tableRegion) (Offset.contains_base E.table (by omega) (by omega)) ?_ (by decide)
  exact Env.far_all v.tableFar.1 v.tableFar.2.2 hos

end VG.Proof.Dsa.X86.Generation
