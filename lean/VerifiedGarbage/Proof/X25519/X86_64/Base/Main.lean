import VerifiedGarbage.Proof.X25519.X86_64.Base.Engine
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
import VerifiedGarbage.Spec.X25519.Contract

/-! Memory, output encoding and ABI obligations for fixed-base X25519. -/
namespace VG.Proof.X25519.X86_64.Base
open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64.Base
open VG.Proof.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Saved val4 st4 bytesAt_st4)
open VG.Spec.Ed25519 (bytesAt)
variable {fld : Arith} [EdArith fld]

/-- The contract the proof is written against: the comb's tables at the static `combSym`,
readable after the scalar (`CombHeld`). -/
def baseLocal : Contract isa where
  pre s := s.rd = [⟨s.gpr .rsi, 32⟩, combRegion (s.syms combSym)] ∧
    s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩] ∧
    (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩ ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdx, 8192⟩ ∧
    (s.gpr .rdx).toNat + 8192 ≤ 2 ^ 64 ∧
    CombHeld s [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rsp, 8⟩]
  post s t := Spec.X25519.bytesAt t.mem (s.gpr .rdi) 32 =
    Spec.X25519.x25519 (bytesAt s.mem (s.gpr .rsi) 32) Spec.X25519.basePoint
  pub s t := s.gpr .rsp = t.gpr .rsp ∧ s.gpr .rdi = t.gpr .rdi ∧
    s.gpr .rsi = t.gpr .rsi ∧ s.gpr .rdx = t.gpr .rdx ∧ s.syms combSym = t.syms combSym

/-- `baseLocal` is `scalarBaseLocal`'s precondition. -/
theorem baseLocal_pre {s : State} (hs : baseLocal.pre s) : scalarBaseLocal.pre s := hs

theorem x25519BaseWith_correct (eng : Prog isa) (heng : UEngineOk eng)
    {s : State} (hs : baseLocal.pre s) :
    WP isa (scalarBaseWith eng) s fun t => gprPreserved s t ∧ baseLocal.post s t := by
  have ⟨tbl, far⟩ := scalarBaseLocal_tbl (baseLocal_pre hs)
  obtain ⟨hr, hw, hd, hro, hrs, hn, hh⟩ := hs
  have hws : (⟨s.gpr .rdx, 8192⟩ : Region) ∈ s.wr := by rw [hw]; simp
  rw [scalarBaseWith]
  apply WP.seq
  rw [WP.block_append_iff]
  refine WP.mono_syms (scalarSave_ok rfl hws) fun a ⟨ga, ra, wa, ma, sva⟩ asy => ?_
  have hwa : (⟨a.gpr .rdx, 8192⟩ : Region) ∈ a.wr := by rw [ga, wa]; exact hws
  refine WP.mono_syms (scalarBaseSetup_ok a hwa) fun b ⟨pb, gb, rb, wb, ob, mb⟩ bsy => ?_
  rw [ga] at pb ob mb
  have hb : Scratch b (s.gpr .rdx) := ⟨pb, by rw [wb, wa]; exact hws, hn⟩
  have fm : Frame [⟨s.gpr .rdx, 8192⟩] s.mem b.mem :=
    (scratchFrame ma (by decide)).trans (scratchFrame mb (by decide))
  have svb : Saved (s.gpr .rdx) s.gpr b.mem := sva.outside mb (by decide)
  have input : bytesAt b.mem (s.gpr .rsi) 32 = bytesAt s.mem (s.gpr .rsi) 32 := bytesAt32_frame fm hd
  have tblb : CombTbl b (s.syms combSym) := tbl.frame fm (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hh.2.2 _ (by simp))
    (by rw [rb, wb, ra, wa]) (by rw [bsy, asy])
  apply WP.seq
  refine WP.mono (heng hb ((gb _ (by decide)).trans (congrFun ga _))
    (fun q hq => ⟨⟨s.gpr .rsi, 32⟩, by rw [rb, ra, hr]; simp,
      Offset.contains_base _ (by omega) (by omega)⟩)
    (fun q hq => farScratch hd hq (by decide)) tblb far) fun c ⟨kc, w, vc, xc⟩ => ?_
  have mc := powersKeep_outside kc
  have svc : Saved (s.gpr .rdx) s.gpr c.mem := svb.outside mc (by decide)
  have oc : c.mem.readW (off (s.gpr .rdx) 48) 64 = s.gpr .rdi :=
    (mc.word (d := 48) (Or.inl (by decide)) (by decide)).trans ob
  have wc : c.wr = s.wr := kc.wr.trans (wb.trans wa)
  rw [scalarBaseFinish]
  apply WP.seq
  refine WP.mono (scalarBaseFinishArgs_ok (kc.scratch hb)) fun d ⟨pd, od, kd⟩ => ?_
  have rdxd : d.gpr .rdx = s.gpr .rdx := pd
  have rdid : d.gpr .rdi = s.gpr .rdi := od.trans oc
  have wd : d.wr = s.wr := kd.2.2.2.trans wc
  rw [WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) rdxd (wd ▸ hws) (by rw [kd.2.1]; exact svc))
    fun e ⟨re, ge, me, _, we⟩ => ?_
  have rdie : e.gpr .rdi = s.gpr .rdi := (ge _ (by decide)).trans rdid
  have hwo : (⟨s.gpr .rdi, 32⟩ : Region) ∈ e.wr := by rw [we, wd, hw]; simp
  refine WP.mono (scalarOut_ok rdie hwo) fun t ⟨mt, gt, _, _⟩ => ?_
  have fme : Frame [⟨s.gpr .rdx, 8192⟩] s.mem e.mem := by
    rw [me, kd.2.1]; exact fm.trans (scratchFrame mc (by decide))
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [gt]
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact re (.rbx, 0) (by decide)
    · exact re (.rbp, 8) (by decide)
    · rw [ge _ (by decide), kd.1 _ (by decide), kc.gpr _ (by decide) (by decide) (by decide),
        gb _ (by decide), ga]
    · exact re (.r12, 16) (by decide)
    · exact re (.r13, 24) (by decide)
    · exact re (.r14, 32) (by decide)
    · exact re (.r15, 40) (by decide)
  · have ft : Frame [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] s.mem t.mem := by
      rw [mt]
      have hc : ∀ d, d + 8 ≤ 32 → (⟨s.gpr .rdi, 32⟩ : Region).Contains (off (s.gpr .rdi) d) (64 / 8) :=
        fun d hd => Offset.contains_base _ hd (by omega)
      have hm : (⟨s.gpr .rdi, 32⟩ : Region) ∈ [⟨s.gpr .rdx, 8192⟩, ⟨s.gpr .rdi, 32⟩] := by simp
      exact ((((fme.mono (by simp)).writeW hm _ (hc 0 (by decide))).writeW hm _
        (hc 8 (by decide))).writeW hm _ (hc 16 (by decide))).writeW hm _ (hc 24 (by decide))
    exact ft.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hrs
      · exact hro) (by decide)
  · change Spec.X25519.bytesAt t.mem (s.gpr .rdi) 32 = _
    rw [mt]
    change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, ← input, xc, Proof.X25519.encodeUCoordinate_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    rw [val4, ge .r8 (by decide), ge .r9 (by decide), ge .r10 (by decide), ge .r11 (by decide),
      kd.1 .r8 (by decide), kd.1 .r9 (by decide), kd.1 .r10 (by decide), kd.1 .r11 (by decide)]
    exact vc

theorem x25519Base_correct [DivstepInv] {s : State} (hs : baseLocal.pre s) :
    WP isa (x25519Base fld) s fun t => gprPreserved s t ∧ baseLocal.post s t :=
  x25519BaseWith_correct _ engine_ok hs

end VG.Proof.X25519.X86_64.Base
