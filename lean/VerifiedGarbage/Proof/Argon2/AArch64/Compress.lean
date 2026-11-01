module

import VerifiedGarbage.Proof.Argon2.AArch64.Finish
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Argon2.Permutation
public import VerifiedGarbage.Proof.Argon2.AArch64.Words
import VerifiedGarbage.Proof.Argon2.AArch64.Schedule
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Argon2.Contract
public import VerifiedGarbage.Proof.Argon2.Contract
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Argon2.AArch64.Mix
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Argon2.AArch64.Mix
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorTaint
meta import VerifiedGarbage.Proof.Argon2.AArch64.Finish
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Argon2.Permutation
meta import VerifiedGarbage.Proof.Argon2.AArch64.Words
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Spec.Argon2.Contract
meta import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Inline
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section

section

/-! Merged from `Proof.Argon2.AArch64.Lit`. -/
section
/-! # Argon2 compression as a checked instruction literal -/

namespace VG.Proof.Argon2.AArch64

materialize_code compress := Impl.Argon2.AArch64.compress

end VG.Proof.Argon2.AArch64
end

/-! Merged from `Proof.Argon2.AArch64.Contract`. -/
section
/-! # A local contract for Argon2 block compression -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2

def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .x0, 1024⟩
    let y : Region := ⟨s.gpr .x1, 1024⟩
    let out : Region := ⟨s.gpr .x2, 1024⟩
    let scratch : Region := ⟨s.gpr .x3, 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch
  post s t := blockAt t.mem (s.gpr .x2) =
    compress (blockAt s.mem (s.gpr .x0)) (blockAt s.mem (s.gpr .x1))
  pub s t := s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x1 = t.gpr .x1 ∧
    s.gpr .x2 = t.gpr .x2 ∧ s.gpr .x3 = t.gpr .x3 ∧ s.sp = t.sp

def satState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x6000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩, ⟨0x4000, 4096⟩]

theorem compress_implies : compressLocal.Implies (compressContract AArch64.abi) := by
  sig_implies [compressContract, compressSig, compressLocal, AArch64.abi, AArch64.argRegs]
    [satState] using satState

end VG.Proof.Argon2.AArch64
end

/-! Constant-time compression: memory contents never determine an address or branch. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64

def initialTaint : AArch64.Taint.T := Taint.ofRegs [.x0, .x1, .x2, .x3]

theorem initial_agree {s t : State} (hp : compressLocal.pub s t) :
    AArch64.Taint.Agree initialTaint s t := by
  obtain ⟨h0, h1, h2, h3, hsp⟩ := hp
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [initialTaint, Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> assumption

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.AArch64.compress :=
  VG.Taint.constantTime (A := VectorTaint.taint) (initialTaint, RegSet.ofList [])
    (fun _ _ _ _ hp => ⟨initial_agree hp, fun _ hv => absurd hv (by simp [RegSet.mem_ofList])⟩)
    (by taint_decide)
end VG.Proof.Argon2.AArch64

end

/-! Merged from `Proof.Argon2.AArch64.Round`. -/
section
/-! # The row and column permutations, in registers -/

namespace VG.Proof.Argon2.AArch64

open VG VG.AArch64 VG.Spec.Argon2
open VG.Impl.Argon2.AArch64 (lane)
open VG.Proof.Argon2

/-- The sixteen words of a row or column, in their registers. -/
def InRegs (s : State) (v : Vector Word 16) : Prop := ∀ j : Fin 16, s.gpr (lane j) = v[j]

/-- Registers and permissions preserved throughout a scratch permutation. -/
def Keeps (s t : State) : Prop :=
  (∀ r, (∀ j, lane j ≠ r) → r ≠ .x17 → t.gpr r = s.gpr r) ∧
  t.rd = s.rd ∧ t.wr = s.wr ∧ t.v = s.v

theorem Keeps.refl (s : State) : Keeps s s := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h : Keeps s t) (h' : Keeps t u) : Keeps s u :=
  ⟨fun r hl ht => (h'.1 r hl ht).trans (h.1 r hl ht),
    h'.2.1.trans h.2.1, h'.2.2.1.trans h.2.2.1, h'.2.2.2.trans h.2.2.2⟩

theorem Scratch.of_keeps {s t : State} {p : Addr} (hs : Scratch s p)
    (hk : Keeps s t) : Scratch t p :=
  ⟨(hk.1 .x3 lane_ne_x3 (by decide)).trans hs.reg, hk.2.2.1 ▸ hs.wr⟩

/-- One GB on registers advances the row or column. -/
theorem gbOn_ok (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val)
    (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa (Impl.Argon2.AArch64.gbOn a b c d) s fun t =>
      InRegs t (GB v a b c d) ∧ Keeps s t ∧ t.mem = s.mem := by
  have ne {i j : Fin 16} (h : i.val ≠ j.val) : lane i ≠ lane j :=
    fun e => h (congrArg Fin.val (lane_injective e))
  have dist : Distinct (lane a) (lane b) (lane c) (lane d) .x17 :=
    ⟨ne hab, ne hac, ne had, lane_ne_x17 a, ne hbc, ne hbd, lane_ne_x17 b, ne hcd,
      lane_ne_x17 c, lane_ne_x17 d⟩
  refine (gb_ok dist s).mono ?_
  rintro t ⟨ha, hb, hc, hd, hk, hm, hr, hw, hvv⟩
  refine ⟨?_, ⟨fun r hl ht => hk r (hl a).symm (hl b).symm (hl c).symm (hl d).symm ht,
    hr, hw, hvv⟩, hm⟩
  intro j
  rw [GB_eq_mixWords v hab hac had hbc hbd hcd]
  simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ← hv a, ← hv b, ← hv c, ← hv d]
  by_cases hdj : d.val = j.val
  · obtain rfl := Fin.ext hdj
    simpa only [↓reduceIte] using hd
  simp only [hdj, ite_false]
  by_cases hcj : c.val = j.val
  · obtain rfl := Fin.ext hcj
    simpa only [↓reduceIte] using hc
  simp only [hcj, ite_false]
  by_cases hbj : b.val = j.val
  · obtain rfl := Fin.ext hbj
    simpa only [↓reduceIte] using hb
  simp only [hbj, ite_false]
  by_cases haj : a.val = j.val
  · obtain rfl := Fin.ext haj
    simpa only [↓reduceIte] using ha
  simp only [haj, ite_false]
  rw [hk _ (ne (Ne.symm haj)) (ne (Ne.symm hbj)) (ne (Ne.symm hcj))
    (ne (Ne.symm hdj)) (lane_ne_x17 j), hv j, Fin.getElem_fin]

/-- Serial reference schedule, used only to reuse the arithmetic proof. -/
def serialPermute : Prog isa :=
  .seq (Impl.Argon2.AArch64.gbOn 0 4 8 12) <| .seq (Impl.Argon2.AArch64.gbOn 1 5 9 13) <|
  .seq (Impl.Argon2.AArch64.gbOn 2 6 10 14) <| .seq (Impl.Argon2.AArch64.gbOn 3 7 11 15) <|
  .seq (Impl.Argon2.AArch64.gbOn 0 5 10 15) <| .seq (Impl.Argon2.AArch64.gbOn 1 6 11 12) <|
  .seq (Impl.Argon2.AArch64.gbOn 2 7 8 13) (Impl.Argon2.AArch64.gbOn 3 4 9 14)

/-- P on the sixteen registers. -/
theorem serialPermute_ok (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa serialPermute s fun t =>
      InRegs t (permute v) ∧ Keeps s t ∧ t.mem = s.mem := by
  have advance (t : State) (v' : Vector Word 16)
      (h : InRegs t v' ∧ Keeps s t ∧ t.mem = s.mem) (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.AArch64.gbOn a b c d) t fun u =>
        InRegs u (GB v' a b c d) ∧ Keeps s u ∧ u.mem = s.mem := by
    refine (gbOn_ok a b c d hab hac had hbc hbd hcd t v' h.1).mono ?_
    rintro u ⟨hu, hk, hm⟩
    exact ⟨hu, h.2.1.trans hk, hm.trans h.2.2⟩
  unfold serialPermute
  apply WP.seq
  refine (advance s _ ⟨hv, Keeps.refl s, rfl⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The interleaved schedule has the same lane expressions as the serial
schedule; its only extra state is the same caller-saved temporary. -/
theorem permute_ok (s : State) (v : Vector Word 16) (hv : InRegs s v) :
    WP isa Impl.Argon2.AArch64.permute s fun t =>
      InRegs t (permute v) ∧ Keeps s t ∧ t.mem = s.mem := by
  have hs : WP isa (.block (Schedule.serialOps.flatMap Schedule.lower)) s fun t =>
      InRegs t (permute v) ∧ Keeps s t ∧ t.mem = s.mem := by
    simpa only [Schedule.serialOps, List.flatMap_append, Schedule.columns, Schedule.diagonals,
      List.flatMap_cons, List.flatMap_nil, Schedule.lower_gbOps, List.append_nil,
      serialPermute, Impl.Argon2.AArch64.gbOn, WP.seq_iff (M := isa), WP.block_append_iff (M := isa)]
      using serialPermute_ok s v hv
  have hr := Schedule.list_ok Schedule.serialOps Schedule.good_serial s.gpr s (fun _ _ => rfl)
  obtain ⟨_, old, _, ho, hro, _⟩ := hs.and hr
  have hn := Schedule.list_ok Schedule.scheduledOps Schedule.good_scheduled s.gpr s
    (fun _ _ => rfl)
  have hnew : WP isa (.block (Schedule.scheduledOps.flatMap Schedule.lower)) s fun t =>
      InRegs t (permute v) ∧ Keeps s t ∧ t.mem = s.mem := by
    refine hn.mono ?_
    rintro t ⟨ht, hm, hrd, hwr, hvec⟩
    have same (r : Reg) (hrt : r ≠ .x17) : t.gpr r = old.gpr r :=
      (ht r hrt).trans ((Schedule.same_values s.gpr r).trans (hro r hrt).symm)
    exact ⟨fun j => (same (lane j) (lane_ne_x17 j)).trans (ho.1 j),
      ⟨fun r hl ht => (same r ht).trans (ho.2.1.1 r hl ht), hrd, hwr, hvec⟩, hm⟩
  simpa only [Schedule.scheduledOps, List.flatMap_append, Schedule.groupOps,
    Schedule.lower_halfGroup, Schedule.columns, Schedule.diagonals,
    Impl.Argon2.AArch64.permute, Impl.Argon2.AArch64.gbGroup,
    WP.seq_iff (M := isa), WP.block_append_iff (M := isa)] using hnew

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (Impl.Argon2.AArch64.permuteAt index) s fun t =>
      working t.mem p = Spec.Argon2.permuteAt index (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  unfold Impl.Argon2.AArch64.permuteAt
  apply WP.seq
  refine (loads_ok index (List.finRange 16) (List.nodup_finRange 16) s hs).mono ?_
  rintro s1 ⟨hl, hk1, hm1, hr1, hw1, hv1⟩
  have k1 : Keeps s s1 := ⟨fun r hl' _ => hk1 r (fun j _ => hl' j), hr1, hw1, hv1⟩
  have in1 : InRegs s1 (gather index (working s.mem p)) := by
    intro j
    rw [hl j (List.mem_finRange j)]
    simp only [gather, working, Fin.getElem_fin, Vector.getElem_ofFn]
  apply WP.seq
  refine (permute_ok s1 _ in1).mono ?_
  rintro s2 ⟨in2, k2, hm2⟩
  refine (stores_ok index (List.finRange 16) s2 ((hs.of_keeps k1).of_keeps k2)).mono ?_
  rintro t ⟨hw, hf, hg, hr, hwr, hv⟩
  refine ⟨?_, ?_, (k1.trans k2).trans ⟨fun r _ _ => congrFun hg r, hr, hwr, hv⟩⟩
  · rw [hw, hm2, hm1]
    simp only [in2 _]
    rfl
  · rw [hm2, hm1] at hf
    exact hf

/-- Compose a list of row or column permutations without re-executing any GB proof. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128) (is : List (Fin 8))
    (s : State) {p : Addr} (hs : Scratch s p) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.AArch64.permuteAt (index i)) rest)
      (.block [])) s fun t =>
      working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (working s.mem p) ∧
      Frame [⟨off p 1024, 1024⟩] s.mem t.mem ∧ Keeps s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, Keeps.refl s⟩
  | cons i is ih =>
    apply WP.seq
    refine (permuteAt_ok (index i) s hs).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (ih t (hs.of_keeps hk)).mono ?_
    rintro u ⟨hu, hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    simpa only [List.foldl_cons, ht] using hu

end VG.Proof.Argon2.AArch64
end

/-! Correctness, memory safety, ABI preservation, and constant time of ARM64 Argon2 G. -/
namespace VG.Proof.Argon2.AArch64
open VG VG.AArch64 VG.Spec.Argon2

theorem original_preserved {m m' : Mem} {p : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have he : m'.readW (off p (8 * i)) 64 = m.readW (off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega))
      (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.base_disjoint p (by decide) (by decide)) (by decide)
  rw [← blockAt_get m' p ⟨i, hi⟩, ← blockAt_get m p ⟨i, hi⟩] at he
  exact he

theorem round_frame {m m' : Mem} {p out : Addr}
    (hf : Frame [⟨off p 1024, 1024⟩] m m') : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 4096⟩, by simp, Offset.sub_base p (by decide)⟩

/-- Keep the output pointer in v16 while x2 holds a word. -/
theorem stash_ok (s : State) :
    WP isa (.block [.vop (.dup .d2 .v16 .x2)]) s fun t =>
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      vdword (t.v .v16) 0 = s.gpr .x2 := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, RegUpd.v_setV_self, vdword_ofVDwords_0]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- Restore the output pointer. -/
theorem unstash_ok (s : State) :
    WP isa (.block [.umov .x .x2 .v16 0]) s fun t =>
      t.gpr .x2 = vdword (s.v .v16) 0 ∧ (∀ r, r ≠ .x2 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr :=
  WP.of_runBlock ⟨s.write .x .x2 (vdword (s.v .v16) 0), rfl,
    by simp only [RegUpd.gpr_write_self, BitVec.setWidth_eq],
    fun _ hr => RegUpd.gpr_write_of_ne _ _ _ hr, rfl, rfl, rfl⟩

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.AArch64.compress s fun t => compressLocal.post s t := by
  obtain ⟨hrd, hwr, hout, hx, hy⟩ := hs
  have scr : Scratch s (s.gpr .x3) := ⟨rfl, by simp [hwr]⟩
  have inputs : Inputs s (s.gpr .x0) (s.gpr .x1) (s.gpr .x3) :=
    ⟨rfl, rfl, by simp [hrd], by simp [hrd], hx, hy⟩
  unfold Impl.Argon2.AArch64.compress
  apply WP.seq
  refine (init_prefix 64 (by decide) s scr inputs).mono ?_
  rintro s1 ⟨hinit, _hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := initialized_blocks hinit
  have scr1 := scr.of_copy hk1
  apply WP.seq
  refine (stash_ok s1).mono ?_
  rintro s2 ⟨hg2, hm2, -, hw2, hst⟩
  have scr2 : Scratch s2 (s.gpr .x3) := ⟨by rw [hg2]; exact scr1.reg, by rw [hw2]; exact scr1.wr⟩
  apply WP.seq
  refine (rounds_ok rowIndex (List.finRange 8) s2 scr2).mono ?_
  rintro s3 ⟨hrow, hf3, hk3⟩
  apply WP.seq
  refine (rounds_ok colIndex (List.finRange 8) s3 (scr2.of_keeps hk3)).mono ?_
  rintro s4 ⟨hcol, hf4, hk4⟩
  have scr4 := (scr2.of_keeps hk3).of_keeps hk4
  apply WP.seq
  refine (unstash_ok s4).mono ?_
  rintro s5 ⟨h2, hk5, hm5, -, hw5⟩
  have hout5 : s5.gpr .x2 = s.gpr .x2 := by
    rw [h2, hk4.2.2.2, hk3.2.2.2, hst, hk1.1 .x2 (by decide) (by decide)]
  have scr5 : Scratch s5 (s.gpr .x3) :=
    ⟨by rw [hk5 .x3 (by decide)]; exact scr4.reg, by rw [hw5]; exact scr4.wr⟩
  have hw5' : s5.wr = s.wr := hw5.trans (hk4.2.2.1.trans (hk3.2.2.1.trans (hw2.trans hk1.2.2)))
  refine (finish_prefix 64 (by decide) s5 scr5 hout5
    (by rw [hw5', hwr]; simp) hout.symm).mono ?_
  rintro t ⟨hfinish, _hf, _hk⟩
  have ho := original_preserved (hf3.trans hf4)
  rw [hm2, horig] at ho
  have he := written_block hfinish
  rw [hm5, hcol, hrow, hm2, hwork, ho] at he
  exact he

theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.AArch64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp⟩ := compress_wp s hs
  refine ⟨tr, t, he, ⟨?_, Exec.sp he, Exec.preservedV he (by lit_decide)⟩, hp⟩
  intro r hr
  apply Exec.gpr (c := Impl.Argon2.AArch64.compress) (hn := .inl (by decide +kernel)) _ he
  have hk : Impl.Argon2.AArch64.compress.allInstrs (keeps (RegSet.ofList preserved)) = true := by
    lit_decide
  intro i hi
  have h := List.all_eq_true.mp (List.all_eq_true.mp (instrs_keeps hk) i hi) r hr
  simpa using h

theorem compress_verified : Verified AArch64.target Impl.Argon2.AArch64.compress
    (Proof.Argon2.compressContract AArch64.abi) :=
  Verified.of_correct compress_correct compress_ct compress_implies
end VG.Proof.Argon2.AArch64
