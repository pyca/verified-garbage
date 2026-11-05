module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillFinish
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.TCB.Registration
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillCTLoop
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillFinish
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextFrame
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ParameterInvariant
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OnSuccess
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.OutputArgs
meta import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Out
meta import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.TCB.Registration

/-! # Timing of the refillable-tape search's end

`finish`: the words written to `used` and `state` (`results`), at addresses
the controller's words hold, which are public; the output; the status.
Every branch is on the controller's public status and the octets consumed. -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Mgf1.X86_64 (sp)
open VG.Impl.Bignum.X86_64 (at0)

/-! ## The end's state -/

theorem doneAt_rsp {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) :
    t.gpr .rsp = D.ctx.geo.F := h.2.2.2.1.rsp

theorem doneAt_pins (n pLen qLen : Nat) : Pins (DoneAt n pLen qLen) [.rsp] := by
  intro D s t hs ht r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (doneAt_rsp hs).trans (doneAt_rsp ht).symm

/-- `DoneAt` across a step that keeps the memory and the stack pointer. -/
theorem doneAt_keep' {n pLen qLen : Nat} {D : DonePublic} {s t : State} (h : DoneAt n pLen qLen D s)
    (hm : t.mem = s.mem) {rs : List Reg} (hk : Keep rs s t) (hsp : Reg.rsp ∉ rs) : DoneAt n pLen qLen D t := by
  obtain ⟨⟨W, hW, rest⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, more⟩ := h
  refine ⟨⟨W, Refill.genMem_keep hW hm hk hsp, rest⟩, ⟨?_, ?_, ?_, hk.2.2 ▸ cw⟩, ?_,
    hf.congr (hk.gpr hsp) hk.2.2, hk.2.2.trans hw, more⟩
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c0
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c1
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c2
  · rw [Refill.ctlWord_eq_of_mem hm]; exact c3

/-- `DoneAt` across writes to `state` and `used`. -/
theorem doneAt_frame {n pLen qLen : Nat} {D : DonePublic} {s t : State} (h : DoneAt n pLen qLen D s)
    (hf : Frame [⟨D.c1, 32⟩, ⟨D.c0, 8⟩] s.mem t.mem) (hsp : t.gpr .rsp = s.gpr .rsp) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) : DoneAt n pLen qLen D t := by
  obtain ⟨⟨W, hm, rest⟩, ⟨c0, c1, c2, cw⟩, c3, fv, hwr, more⟩ := h
  have e := D.ends
  obtain ⟨V, R⟩ := hm.rep
  have frameIn : (⟨D.ctx.geo.F, frameBytes⟩ : Region) ∈ D.ctx.changed := by simp [GenerationContext.changed]
  have Rt : Rep t.mem D.ctx.geo.F D.ctx.geo.hash V W := rep_of_disjoint_frame R hf
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact (e.stChanged _ frameIn).symm
      · exact (e.usChanged _ frameIn).symm)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact e.stHash.symm
      · exact e.usHash.symm)
  have hmt : GenerationMemory (D.ctx.withHs D.hs) W t :=
    ⟨lay_of_rep hm.layout R Rt rfl hsp hw, ⟨V, Rt⟩, hm.slots, hm.scratch.congr hw,
      Refill.tapeMemory_frame hm.seeds hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.stSeeds.symm
        · exact e.usSeeds.symm) hr hw,
      Refill.tapeMemory_frame hm.hs hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.stRand.symm.sub_left D.hsIn
        · exact e.usRand.symm.sub_left D.hsIn) hr hw,
      Refill.tapeMemory_frame hm.rand hf (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact e.stRand.symm
        · exact e.usRand.symm) hr hw⟩
  have cwd : ∀ k < 4, Refill.ctlWord t.mem D.ctx.geo.F k = Refill.ctlWord s.mem D.ctx.geo.F k :=
    fun k hk => Refill.ctlWord_frame hf (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact e.stCtl.symm
      · exact e.usCtl.symm) hk
  exact ⟨⟨W, hmt, rest⟩, ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1,
    (cwd 2 (by decide)).trans c2, hw ▸ cw⟩, (cwd 3 (by decide)).trans c3, fv.congr hsp hw, hw.trans hwr, more⟩

theorem doneAt_ctlIn {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) {k : Nat}
    (hk : k < 4) : InRegions (t.rd ++ t.wr) (off D.ctx.geo.F (296 + 8 * k)) 8 := by
  have cs : Scr t (off D.ctx.geo.F 296) 32 := Scr.of_mem h.2.1.2.2.2 (by
    have := D.ok.bound; simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have := cs.ld (d := 8 * k) (by omega)
  simpa [off_off] using this

theorem doneAt_stIn {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) {d : Nat}
    (hd : d + 8 ≤ 32) : InRegions t.wr (off D.c1 d) 8 :=
  (Scr.of_mem (h.2.2.2.2.1 ▸ D.ends.stIn) D.ends.stBound).st hd

theorem doneAt_usIn {n pLen qLen : Nat} {D : DonePublic} {t : State} (h : DoneAt n pLen qLen D t) :
    InRegions t.wr (off D.c0 0) 8 :=
  (Scr.of_mem (h.2.2.2.2.1 ▸ D.ends.usIn) D.ends.usBound).st (d := 0) (by decide)

/-! ## The pieces -/

theorem ctlLoad_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s) {k : Nat}
    (hk : k < 4) :
    WP isa (.block [.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl k))]) s fun t =>
      DoneAt n pLen qLen D t ∧ t.gpr .rcx = Refill.ctlWord s.mem D.ctx.geo.F k := by
  have hr := doneAt_ctlIn h hk
  refine WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = Refill.ctlWord s.mem D.ctx.geo.F k ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨rc, mt⟩, kt⟩ => ⟨doneAt_keep' h mt kt (by decide), rc⟩
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
    doneAt_rsp h, hr]
  rfl

theorem stateWords_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (hrcx : s.gpr .rcx = D.c1) (first : List Instr)
    (hfirst : first = [.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .store (at0 .rcx) .rax,
        .store { base := .rcx, disp := 24 } .rdx] ∨
      first = [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) :
    WP isa (.block first) s (DoneAt n pLen qLen D) := by
  have s0 := doneAt_stIn h (d := 0) (by decide)
  have s3 := doneAt_stIn h (d := 24) (by decide)
  have c2 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 312) 8 := doneAt_ctlIn h (k := 2) (by decide)
  replace s0 : InRegions s.wr D.c1 8 := by simpa [off] using s0
  have post : ∀ t : State, (∃ a b : BitVec 64, t.mem = (s.mem.writeW D.c1 a).writeW (off D.c1 24) b) →
      Keep [.rax] s t → DoneAt n pLen qLen D t := by
    intro t ⟨a, b, hm⟩ kt
    refine doneAt_frame h ?_ (kt.gpr (by decide)) kt.2.1 kt.2.2
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Refill.contains_head _ (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains_base _ (d := 24) (by decide) (by decide))
  rcases hfirst with rfl | rfl
  · refine WP.mono (WP.keep [.rax] (Q := fun t => ∃ a b : BitVec 64,
      t.mem = (s.mem.writeW D.c1 a).writeW (off D.c1 24) b) ?_ rfl) fun t ⟨ht, kt⟩ => post t ht kt
    xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
      Refill.ea_at0', Refill.ea_24, doneAt_rsp h, hrcx, c2, s0, s3]
    exact ⟨_, _, rfl⟩
  · refine WP.mono (WP.keep [.rax] (Q := fun t => ∃ a b : BitVec 64,
      t.mem = (s.mem.writeW D.c1 a).writeW (off D.c1 24) b) ?_ rfl) fun t ⟨ht, kt⟩ => post t ht kt
    xrun [Refill.ea_at0', Refill.ea_24, hrcx, s0, s3]
    exact ⟨_, _, rfl⟩

theorem usedLoad_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (src : MemOp) (hsrc : src = Impl.Dsa.X86_64.Generation.Refill.ctl 3 ∨ src = sp 128) :
    WP isa (.block [.mov .rax (.mem src), .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))]) s fun t =>
      DoneAt n pLen qLen D t ∧ t.gpr .rcx = D.c0 := by
  have c0 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 296) 8 := doneAt_ctlIn h (k := 0) (by decide)
  have c3 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 320) 8 := doneAt_ctlIn h (k := 3) (by decide)
  obtain ⟨⟨W, hm, _⟩, ⟨w0, _⟩, _⟩ := id h
  have w0' : s.mem.readW (off D.ctx.geo.F 296) 64 = D.c0 := w0
  have hsp : s.gpr .rsp = D.ctx.geo.F := hm.layout.rsp
  have f128 : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 128) 8 := hm.layout.ld (by decide)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t => t.gpr .rcx = D.c0 ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨⟨rc, mt⟩, kt⟩ => ⟨doneAt_keep' h mt kt (by decide), rc⟩
  rcases hsrc with rfl | rfl
  · xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
      hsp, c0, c3, w0']
  · xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes, ea_sp,
      hsp, c0, f128, w0']

theorem usedStore_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (hrcx : s.gpr .rcx = D.c0) : WP isa (.block [.store (at0 .rcx) .rax]) s (DoneAt n pLen qLen D) := by
  have u0 : InRegions s.wr D.c0 8 := by simpa [off] using doneAt_usIn h
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW D.c0 (s.gpr .rax)) ?_ rfl) fun t ⟨hm, kt⟩ => ?_
  · xrun [Refill.ea_at0', hrcx, u0]
  refine doneAt_frame h ?_ (kt.gpr (by decide)) kt.2.1 kt.2.2
  rw [hm]
  exact (Frame.refl _ _).writeW (List.mem_cons_of_mem _ (List.mem_singleton_self _)) _
    (Refill.contains_head _ (by decide))

end VG.Proof.Dsa.X86_64.Generation
