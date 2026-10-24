module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.ScalarRange
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.PublicRange
public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.Initial
import VerifiedGarbage.Proof.Framework.Omega

/-! Range checks preserve the canonical field, scalar bytes and comb controls. -/
@[expose] public section
namespace VG.Proof.Ffdh.AArch64.Cached
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Ffdh.AArch64.Cached
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

theorem scalarRanges_le (w : Nat) : ∀ r∈scalarRanges w,r.1+r.2≤slot w 8 := by
 simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp];omega

theorem publicRangeRanges_le (w : Nat) : ∀ r∈publicRangeRanges w,r.1+r.2≤slot w 8 := by
 simp only [publicRangeRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp];omega

theorem scalarFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (scalarRanges w) m m') (inside : i<32) (different : i≠sTmp) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega)
 simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp] at *;omega

theorem publicRangeFrame_header {B : Addr} {w i : Nat} {m m' : Mem}
 (frame : Frm B (publicRangeRanges w) m m') (inside : i<32) (different : i≠sTmp) :
 word m' B (8*i)=word m B (8*i) := by
 apply frame.word_eq _ (by omega)
 simp only [publicRangeRanges,List.mem_cons,List.not_mem_nil,or_false]
 rintro _ (rfl|rfl)
 all_goals dsimp only [slot,hdrBytes,sTmp] at *;omega

theorem FieldInitial.after_scalarRange {p : Parameters} {s t : State}
 (field : FieldInitial p s) (good : Good t p.B p.Z p.w p.mi) (frame : Frm p.B (scalarRanges p.w) s.mem t.mem) : FieldInitial p t := by
 have nowrap : slot p.w 8≤2^64 := by have := field.good.scr.nowrap;have := p.room;omega
 have same (j : Nat) (allowed : j=0 ∨ j=4) : wv t.mem p.B (slot p.w j) p.w=wv s.mem p.B (slot p.w j) p.w := by
  apply frame.wv_eq
  · simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
    rintro _ (rfl|rfl|rfl)
    all_goals rcases allowed with rfl|rfl <;> dsimp only [slot,hdrBytes,sTmp] <;>omega
  · rcases allowed with rfl|rfl <;> dsimp only [slot,hdrBytes] at * <;>omega
 have wordSame : word t.mem p.B (slot p.w 0)=word s.mem p.B (slot p.w 0) := by
  apply frame.word_eq
  · simp only [scalarRanges,List.mem_cons,List.not_mem_nil,or_false]
    rintro _ (rfl|rfl|rfl)
    all_goals have := p.positive;dsimp only [slot,hdrBytes,sTmp];omega
  · have := p.positive;dsimp only [slot,hdrBytes] at *;omega
 refine ⟨good,(same 0 (by simp)).trans field.modulus,?_,(same 4 (by simp)).trans field.r2⟩
 rw [wordSame]
 exact field.inverse

theorem Controls.after_scalarRange {B src ctx : Addr} {k N w : Nat} {m : State} {t : State}
 (h : Controls B src ctx k N m) (frame : Frm B (scalarRanges w) m.mem t.mem) : Controls B src ctx k N t :=
 ⟨(scalarFrame_header frame (by decide) (by decide)).trans h.context,
  (scalarFrame_header frame (by decide) (by decide)).trans h.source,
  (scalarFrame_header frame (by decide) (by decide)).trans h.length,
  (scalarFrame_header frame (by decide) (by decide)).trans h.bits,
  (scalarFrame_header frame (by decide) (by decide)).trans h.rows⟩

theorem Initial.after_scalarRange {p : Parameters} {s t : State} {bs : List Byte} {rs : List Reg}
 (h : Initial p bs s) (good : Good t p.B p.Z p.w p.mi) (frame : Frm p.B (scalarRanges p.w) s.mem t.mem)
 (rest : Keep rs s t) : Initial p bs t :=
 ⟨h.toFieldInitial.after_scalarRange good frame,h.controls.after_scalarRange frame,
  h.reads.after_inscr (InScr.of_frm frame (fun r hr =>Nat.le_trans (scalarRanges_le _ r hr) p.room)) rest⟩

end VG.Proof.Ffdh.AArch64.Cached
