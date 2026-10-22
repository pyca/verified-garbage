module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.Env
public import VerifiedGarbage.Proof.Mont.Words32
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

/-- A frame within the ranges and the stack. -/
theorem Chg.of_frame {os : List (Nat × Nat)} {rs : List Region} {m m' : Mem} (F : Frame rs m m')
    (h : ∀ r ∈ rs, ∃ r' ∈ (os.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion], Region.Sub r r') :
    E.Chg os m m' :=
  Frame.sub F h

/-- A part of one of the ranges. -/
theorem in_range {os : List (Nat × Nat)} {o : Nat × Nat} (ho : o ∈ os) {d n : Nat} (h₁ : o.1 ≤ d)
    (h₂ : d + n ≤ o.1 + o.2) :
    ∃ r' ∈ (os.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion],
      Region.Sub ⟨off E.base d, n⟩ r' :=
  ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨o, ho, rfl⟩), Offset.sub E.base h₁ h₂⟩

/-- A part of the stack. -/
theorem in_stack {os : List (Nat × Nat)} {r : Region} (h : Region.Sub r E.stackRegion) :
    ∃ r' ∈ (os.map fun o => (⟨off E.base o.1, o.2⟩ : Region)) ++ [E.stackRegion], Region.Sub r r' :=
  ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩

/-- A store of a word into one of the ranges. -/
theorem Chg.store {os : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m') {d n : Nat} (ho : (d, n) ∈ os)
    (hn : 4 ≤ n) (v : BitVec 32) : E.Chg os m (m'.writeW (off E.base d) v) :=
  Frame.writeW h (r := ⟨off E.base d, n⟩) (List.mem_append_left _ (List.mem_map.mpr ⟨_, ho, rfl⟩)) v
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)

/-- A store of a byte into one of the ranges. -/
theorem Chg.byte {os : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m') {d n : Nat} (ho : (d, n) ∈ os)
    {i : Nat} (hi : i < n) (hn : n < 2 ^ 64) (b : Byte) :
    E.Chg os m (m'.writeW (off E.base d + BitVec.ofNat 64 i) b) :=
  Frame.writeW h (r := ⟨off E.base d, n⟩) (List.mem_append_left _ (List.mem_map.mpr ⟨_, ho, rfl⟩)) b
    (Offset.contains_base _ (by omega) (by omega))

/-- The bytes of a range of `scratch` apart from every range of a change. -/
theorem Chg.scratch (v : E.Valid) {os : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m') {d n : Nat}
    (hd : d + n ≤ E.size) (hos : ∀ o ∈ os, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + n ≤ o.1)) :
    Spec.Rsa.bytesAt m' (off E.base d) n = Spec.Rsa.bytesAt m (off E.base d) n := by
  have nw := v.scratchFit
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine Frame.bytes h (R := ⟨off E.base d, n⟩) ?_ (by show n ≤ 2 ^ 64; omega) hi
  intro r hr
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
  rcases hr with ⟨o, ho, rfl⟩ | rfl
  · have := hos o ho
    exact Offset.disjoint E.base (by omega) (by omega) (by omega)
  · exact v.scratchStack.sub_left (range_sub (o := (d, n)) hd)

end Env

/-- The bytes of a range of `scratch` apart from a write to another. -/
theorem frame_bytes {base : Addr} {m m' : Mem} {d n d' n' : Nat}
    (F : Frame [⟨off base d, n⟩] m m') (h : d + n ≤ d' ∨ d' + n' ≤ d) (hd : d + n ≤ 2 ^ 32)
    (hd' : d' + n' ≤ 2 ^ 32) :
    Spec.Rsa.bytesAt m' (off base d') n' = Spec.Rsa.bytesAt m (off base d') n' := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [List.mem_range] at hi
  refine Frame.bytes F (R := ⟨off base d', n'⟩) ?_ (by show n' ≤ 2 ^ 64; omega) hi
  intro r hr; simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint base h.symm (by omega) (by omega)

/-- A store into a word of `scratch` leaves the words apart from it. -/
theorem word_store_other {E : Env} (v : E.Valid) (m : Mem) {d e : Nat} (hd : d + 4 ≤ E.size) (he : e + 4 ≤ E.size)
    (h : d + 4 ≤ e ∨ e + 4 ≤ d) (x : BitVec 32) :
    (m.writeW (off E.base e) x).readW (off E.base d) 32 = m.readW (off E.base d) 32 := by
  have := v.scratchFit
  exact Mem.readW_writeW_sep (Offset.sep E.base h (by omega) (by omega)) (by decide)

theorem Base.keep {E : Env} (v : E.Valid) {s t : State} (B : Base E s) {os : List (Nat × Nat)}
    (F : E.Chg os s.mem t.mem) (A : E.Apart os) (edi : t.gpr .edi = s.gpr .edi) (sp : t.gpr .esp = s.gpr .esp)
    (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sy : t.syms = s.syms) : Base E t := by
  have hos : ∀ o ∈ os, o.1 + o.2 ≤ E.size := fun o ho => (A o ho).1
  have word : ∀ d, d = fOut ∨ (fHs ≤ d ∧ d + 4 ≤ fWitLen + 4) →
      t.mem.readW (off E.base d) 32 = s.mem.readW (off E.base d) 32 :=
    fun d h => Env.Chg.word v F (by have := v.room; simp only [fOut, fHs, fWitLen, hdr] at h; omega)
      fun o ho => ⟨(A o ho).1, by
        have := (A o ho).2
        simp only [fOut, fHs, fWitLen, hdr] at h this ⊢
        omega⟩
  have tapeEq : ∀ R ∈ [E.seedsRegion, E.hsRegion, E.witRegion],
      Spec.Rsa.bytesAt t.mem R.base R.len = Spec.Rsa.bytesAt s.mem R.base R.len := fun R hR =>
    Env.Chg.bytesAt F (v.tapesFar R hR).1 (v.tapesFar R hR).2.2 hos (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have := v.seedsFit; have := v.hsFit; have := v.witFit
      rcases hR with rfl | rfl | rfl <;> simp only [Env.seedsRegion, Env.hsRegion, Env.witRegion] <;> omega)
  refine ⟨Scr.of_eq B.scr edi sp wr, sp.trans B.sp, rd ▸ B.tapes, rd ▸ B.table, wr ▸ B.out, sy ▸ B.syms, ?_,
    (tapeEq E.seedsRegion (by simp)).trans B.seeds, (tapeEq E.hsRegion (by simp)).trans B.hs,
    (tapeEq E.witRegion (by simp)).trans B.wit, (word fOut (.inl rfl)).trans B.outW,
    (word fHs (.inr (by decide))).trans B.hsW, (word fHsLen (.inr (by decide))).trans B.hsLenW,
    (word fWit (.inr (by decide))).trans B.witW, (word fWitLen (.inr (by decide))).trans B.witLenW⟩
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

/-- A state with the same memory, permissions and registers that `Base`
reads. -/
theorem Base.regs {E : Env} {s t : State} (B : Base E s) (hm : t.mem = s.mem) (edi : t.gpr .edi = s.gpr .edi)
    (sp : t.gpr .esp = s.gpr .esp) (rd : t.rd = s.rd) (wr : t.wr = s.wr) (sy : t.syms = s.syms) : Base E t := by
  have := B.scr.nowrap
  refine ⟨Scr.of_eq B.scr edi sp wr, by rw [sp, B.sp], by rw [rd]; exact B.tapes, by rw [rd]; exact B.table,
    by rw [wr]; exact B.out, by rw [sy]; exact B.syms, by rw [hm, sy]; exact B.held, by rw [hm]; exact B.seeds,
    by rw [hm]; exact B.hs, by rw [hm]; exact B.wit, by rw [hm]; exact B.outW, by rw [hm]; exact B.hsW,
    by rw [hm]; exact B.hsLenW, by rw [hm]; exact B.witW, by rw [hm]; exact B.witLenW⟩

/-- The words of `scratch` apart from every range of a change. -/
theorem Env.Chg.val32 {E : Env} (v : E.Valid) {os : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m')
    {d k : Nat} (hd : d + 4 * k ≤ E.size)
    (hos : ∀ o ∈ os, o.1 + o.2 ≤ E.size ∧ (o.1 + o.2 ≤ d ∨ d + 4 * k ≤ o.1)) :
    VG.Proof.Mont.val32 m' E.base d k = VG.Proof.Mont.val32 m E.base d k :=
  VG.Proof.Mont.val32_congr fun j hj => congrArg BitVec.toNat (Env.Chg.word v h (by omega) fun o ho =>
    ⟨(hos o ho).1, by rcases (hos o ho).2 with h | h <;> omega⟩)

/-- A change within ranges is one within ranges around them. -/
theorem Env.Chg.widen {E : Env} {os os' : List (Nat × Nat)} {m m' : Mem} (h : E.Chg os m m')
    (hw : ∀ o ∈ os, ∃ o' ∈ os', o'.1 ≤ o.1 ∧ o.1 + o.2 ≤ o'.1 + o'.2) : E.Chg os' m m' :=
  Env.Chg.of_frame h fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hr
    rcases hr with ⟨o, ho, rfl⟩ | rfl
    · obtain ⟨o', ho', h1, h2⟩ := hw o ho; exact Env.in_range ho' h1 h2
    · exact Env.in_stack (fun _ h => h)

end VG.Proof.Dsa.X86.Generation
