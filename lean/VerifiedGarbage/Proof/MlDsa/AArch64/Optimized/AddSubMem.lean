import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.AddSubVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.AddSub
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg Lanes wp_ldrq wp_strq)
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Spec.MlDsa (q)

def result (sub : Bool) (a b : Nat) : Nat :=
  (if sub then a + q - b else a + b) % q

theorem arithmetic_ok (sub : Bool) {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.v .v0) A) (hb : Lanes (s.v .v1) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, VChg [.v0,.v4] s t →
      Lanes (t.v .v0) (fun e => result sub (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic sub ++ rest)) s Q := by
  cases sub
  · exact add_ok hc ha hb halt hblt k
  · exact sub_ok hc ha hb halt hblt k

/-- Two vector loads, the canonical arithmetic, and one vector store. -/
theorem group_ok (sub : Bool) {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x0) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x1) 16) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ t v, StepKeep [.v0,.v1,.v4] s t →
      t.mem = s.mem.write (s.gpr .x0) 16 v →
      Lanes v (fun e => result sub (A e) (B e)) → WP isa (.block rest) t Q) :
    WP isa (.block (([.ldrq .v0 .x0 0,.ldrq .v1 .x1 0] : List Instr) ++
      VG.Impl.MlDsa.AArch64.Optimized.AddSub.arithmetic sub ++ ([.strq .v0 .x0 0] : List Instr) ++ rest)) s Q := by
  simp only [List.append_assoc,List.cons_append,List.nil_append]
  refine wp_ldrq (by decide) rfl (by simpa using hra) fun a h1 => ?_
  refine wp_ldrq (by decide) rfl (by simpa only [h1.chg.rd,h1.chg.wr,h1.chg.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hrb) fun b h2 => ?_
  have hk : VChg [.v0,.v1] s b := (h1.chg.trans h2.chg).mono (by decide)
  have hA : Lanes (b.v .v0) A := by
    rw [h2.get .v0,h1.v]; simpa using ha
  have hB : Lanes (b.v .v1) B := by
    rw [h2.v,h1.chg.mem,h1.chg.gpr]; simpa using hb
  refine arithmetic_ok sub (hc.chg hk) hA hB halt hblt fun c h3 hval => ?_
  have hk' : VChg [.v0,.v1,.v4] s c := (hk.trans h3).mono (by decide)
  refine wp_strq (by decide) rfl (by simpa only [hk'.wr,hk'.gpr,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hw) fun d h4 => ?_
  refine k d (c.v .v0) ?_ ?_ hval
  · exact ((StepKeep.ofChg hk' (by decide)).trans (StepKeep.ofMem h4)).mono (by decide)
  · simp only [h4.mem,hk'.mem,hk'.gpr,BitVec.add_zero]

theorem body_ok (sub : Bool) {s : State} (hc : VConsts s) {A B : Nat → Nat}
    (ha : Lanes (s.mem.read (s.gpr .x0) 16) A)
    (hb : Lanes (s.mem.read (s.gpr .x1) 16) B)
    (halt : ∀ e < 4, A e < q) (hblt : ∀ e < 4, B e < q)
    (hra : InRegions (s.rd++s.wr) (s.gpr .x0) 16)
    (hrb : InRegions (s.rd++s.wr) (s.gpr .x1) 16)
    (hw : InRegions s.wr (s.gpr .x0) 16) :
    WP isa (.block (VG.Impl.MlDsa.AArch64.Optimized.AddSub.body sub)) s fun t =>
      ∃ v, t.mem = s.mem.write (s.gpr .x0) 16 v ∧
        Lanes v (fun e => result sub (A e) (B e)) ∧ VConsts t ∧
        t.gpr .x0 = s.gpr .x0 + 16 ∧ t.gpr .x1 = s.gpr .x1 + 16 ∧
        t.gpr .x12 = s.gpr .x12 - 1 ∧ VG.Proof.MlKem.AArch64.Keep [.x0,.x1,.x12] s t := by
  unfold VG.Impl.MlDsa.AArch64.Optimized.AddSub.body
  have he : ([Instr.strq .v0 .x0 0, .addImm .x .x0 .x0 16,
      .addImm .x .x1 .x1 16,.subImm .x .x12 .x12 1] : List Instr) =
      [.strq .v0 .x0 0] ++ [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,.subImm .x .x12 .x12 1] := rfl
  rw [he, ← List.append_assoc]
  refine group_ok sub hc ha hb halt hblt hra hrb hw fun t v hk hm hl => ?_
  have ct : VConsts t := ⟨by rw [hk.vec .v16 (by decide)]; exact hc.q,
    by rw [hk.vec .v17 (by decide)]; exact hc.qi⟩
  have scalar : WP isa (.block [.addImm .x .x0 .x0 16,.addImm .x .x1 .x1 16,
      .subImm .x .x12 .x12 1]) t fun u =>
      u.mem=t.mem ∧ u.v=t.v ∧ u.gpr .x0=t.gpr .x0+16 ∧
      u.gpr .x1=t.gpr .x1+16 ∧ u.gpr .x12=t.gpr .x12-1 := by
    arun [State.write, BitVec.ofNat_eq_ofNat]
  refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x0,.x1,.x12] scalar (by decide))
    fun u ⟨⟨hum,huv,h0,h1,h12⟩,ku⟩ => ?_
  refine ⟨v, hum.trans hm, hl, ?_, ?_, ?_, ?_, (hk.keep.trans ku).mono⟩
  · exact ⟨by rw [huv]; exact ct.q, by rw [huv]; exact ct.qi⟩
  · simpa only [hk.keep.get .x0] using h0
  · simpa only [hk.keep.get .x1] using h1
  · simpa only [hk.keep.get .x12] using h12
end VG.Proof.MlDsa.AArch64.Optimized.AddSub
