import VerifiedGarbage.Proof.X25519.AArch64.Base.Engine
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarBaseMain
import VerifiedGarbage.Spec.X25519.Contract

/-!
# X25519 of the base point on AArch64: memory and ABI obligations

As Ed25519's `scalarBase` (`Proof/Ed25519/AArch64/ScalarBaseMain.lean`), with
the engine of `Engine.lean` and its result read as a u-coordinate.
-/

namespace VG.Proof.X25519.AArch64.Base

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Impl.X25519.AArch64.Base
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64 (val4)
open VG.Spec.Ed25519 (bytesAt)

/-- `vg_x25519_base(out = x0, scalar = x1, scratch = x2)`, with the comb's tables at the
static's address. -/
def baseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .x1, 32⟩, tblRegion s] ∧ s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x2, 8192⟩ ∧
    (s.gpr .x2).toNat + 8192 ≤ 2 ^ 64 ∧ CombHeld s [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x2, 8192⟩]
  post s t := Spec.X25519.bytesAt t.mem (s.gpr .x0) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem (s.gpr .x1) 32) Spec.X25519.basePoint
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧ s.syms combSym = t.syms combSym

theorem x25519Base_correct {s : State} (hs : baseLocal.pre s) :
    WP isa x25519Base s fun t => abiPreserved s t ∧ baseLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  obtain ⟨hr, hw, hd, hn, hct⟩ := hs
  have hws : (⟨s.gpr .x2, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [x25519Base]
  apply WP.seq
  rw [WP.block_append_iff]
  have htb : TblAt s (s.gpr .x2) (s.syms combSym) := hct.tblAt (by rw [hr]; simp) (by simp)
  refine WP.mono_syms (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, spa, ma, sva⟩ sya => ?_
  have hwa : (⟨a.gpr .x2, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, spb, ob, mb⟩ syb => ?_
  rw [ga] at pb ob mb
  have hb : Scr b (s.gpr .x2) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .x2, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .x2) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .x1) 32 = bytesAt s.mem (s.gpr .x1) 32 := bytesAt32_frame fm hd
  apply WP.seq
  refine WP.mono (engine_ok hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .x1, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun q hq => farScr hd hq (by decide))
    (htb.of_far (by rw [rb, ra, wb, wa]) fun x hx => by
      rw [mb x (Or.inr (by omega)), ma x (Or.inr (by omega))])
    (by rw [syb, sya])) fun c ⟨kc, w, vc, xc⟩ => ?_
  have mc := powersKeep_outside kc
  have svc : Saved (s.gpr .x2) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .x2) 48) 64 = s.gpr .x0 :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have x2d : d.gpr .x2 = s.gpr .x2 := pd
  have x0d : d.gpr .x0 = s.gpr .x0 := od.trans oc
  have wd : d.wr = s.wr := kd.wr.trans wc
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) x2d (wd ▸ hws) (by rw [kd.mem]; exact svc))
    fun e ⟨re, ke⟩ => ?_
  have x0e : e.gpr .x0 = s.gpr .x0 := (ke.gpr _ (by decide)).trans x0d
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ e.wr := by rw [ke.wr, wd, hw]; simp
  refine WP.mono (scalarOut_ok x0e hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.x19, 0) (by decide)
    · exact re (.x20, 8) (by decide)
    · exact re (.x21, 16) (by decide)
    · exact re (.x22, 24) (by decide)
    · exact re (.x23, 32) (by decide)
    · exact re (.x24, 40) (by decide)
    all_goals
      rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
  · exact ke.sp.trans (kd.sp.trans (kc.sp.trans (spb.trans spa)))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    change _ = Spec.X25519.x25519 (bytesAt s.mem (s.gpr .x1) 32) Spec.X25519.basePoint
    rw [bytesAt_st4, ← input, xc, Proof.X25519.encodeUCoordinate_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [ke.gpr .x4 (by decide), ke.gpr .x5 (by decide), ke.gpr .x6 (by decide), ke.gpr .x7 (by decide),
      kd.gpr .x4 (by decide), kd.gpr .x5 (by decide), kd.gpr .x6 (by decide), kd.gpr .x7 (by decide)]
    exact vc

end VG.Proof.X25519.AArch64.Base
