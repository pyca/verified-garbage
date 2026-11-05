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

/-! ## The blocks writing `state` and `used` -/

theorem doneAt_rcx_pins (n pLen qLen : Nat) (f : DonePublic → BitVec 64) :
    Pins (fun D s => DoneAt n pLen qLen D s ∧ s.gpr .rcx = f D) [.rsp, .rcx] := by
  intro D s t hs ht r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (doneAt_rsp hs.1).trans (doneAt_rsp ht.1).symm
  · exact hs.2.trans ht.2.symm

theorem stateBlock_ct (n pLen qLen : Nat) (first : List Instr)
    (hfirst : first = [.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .store (at0 .rcx) .rax,
        .store { base := .rcx, disp := 24 } .rdx] ∨
      first = [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) :
    RelCT isa (Two (DoneAt n pLen qLen))
      (.block ([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++ first)) (Two (DoneAt n pLen qLen)) := by
  have tf : ∃ hc, (taint.check (Taint.ofRegs [.rsp, .rcx]) (.block first) hc).isSome = true := by
    rcases hfirst with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun D t => DoneAt n pLen qLen D t ∧ t.gpr .rcx = D.c1)
    [.rsp] (doneAt_pins n pLen qLen) (by taint_decide) fun D s h => ?_)
    (two_piece [.rsp, .rcx] (doneAt_rcx_pins n pLen qLen _) tf.choose_spec
      fun D s h => stateWords_ready h.1 h.2 first hfirst))
  exact WP.mono (ctlLoad_ready h (k := 1) (by decide)) fun t ⟨ht, hr⟩ => ⟨ht, hr.trans h.2.1.2.1⟩

theorem usedBlock_ct (n pLen qLen : Nat) (src : MemOp)
    (hsrc : src = Impl.Dsa.X86_64.Generation.Refill.ctl 3 ∨ src = sp 128) :
    RelCT isa (Two (DoneAt n pLen qLen))
      (.block ([.mov .rax (.mem src), .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++
        [.store (at0 .rcx) .rax])) (Two (DoneAt n pLen qLen)) := by
  have ts : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rax (.mem src),
      .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))]) hc).isSome = true := by
    rcases hsrc with rfl | rfl <;> exact ⟨_, by taint_decide⟩
  exact RelCT.block_append (RelCT.seq (two_piece (Ψ := fun D t => DoneAt n pLen qLen D t ∧ t.gpr .rcx = D.c0)
    [.rsp] (doneAt_pins n pLen qLen) ts.choose_spec fun D s h => usedLoad_ready h src hsrc)
    (two_piece [.rsp, .rcx] (doneAt_rcx_pins n pLen qLen _) (by taint_decide)
      fun D s h => usedStore_ready h.1 h.2))

/-! ## A seed that ran out -/

def DonePublic.withStatus (D : DonePublic) (st : BitVec 64) : DonePublic := { D with status := st }

def DonePublic.ranOutStatus (D : DonePublic) : BitVec 64 :=
  if D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen then 0 else 2

/-- A status stored. -/
theorem doneStatus_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s)
    (k : Nat) (hk : k = 0 ∨ k = 2) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.stackStatus k)) s
      (DoneAt n pLen qLen (D.withStatus (BitVec.ofNat 64 k))) := by
  obtain ⟨⟨W, hm, _⟩, ⟨c0, c1, c2, cw⟩, c3, hf, hw, _, hp, hq⟩ := h
  refine WP.mono (Refill.statusMem_ok hm k (by omega)) fun u ⟨mu, fu, ku⟩ => ?_
  have cwd : ∀ j < 4, Refill.ctlWord u.mem D.ctx.geo.F j = Refill.ctlWord s.mem D.ctx.geo.F j :=
    fun j hj => D.ok.word fu hj
  refine ⟨⟨_, mu, by simp [upd, DonePublic.withStatus], fun h1 => ?_⟩,
    ⟨(cwd 0 (by decide)).trans c0, (cwd 1 (by decide)).trans c1, (cwd 2 (by decide)).trans c2, ku.2.2 ▸ cw⟩,
    (cwd 3 (by decide)).trans c3, hf.congr (ku.gpr (by decide)) ku.2.2, ku.2.2.trans hw, ?_, hp, hq⟩
  · rcases hk with rfl | rfl <;> simp [DonePublic.withStatus] at h1
  · rcases hk with rfl | rfl <;> simp [DonePublic.withStatus]

def RanOutCompared (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  (DoneAt n pLen qLen D t ∧ D.status = 0) ∧
  t.gpr .rcx = BitVec.ofNat 64 (D.ctx.rand.bytes.length - D.cursor) ∧
  t.gpr .rdx = BitVec.ofNat 64 (32769 * D.ctx.geo.pLen) ∧
  isa.eval .b t = some (decide (D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen))

theorem ranOut_ct (n pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two fun (D : DonePublic) s => DoneAt n pLen qLen D s ∧ D.status = 0)
      (Impl.Dsa.X86_64.Generation.Refill.ranOut pLen)
      (Two fun (D : DonePublic) s => DoneAt n pLen qLen (D.withStatus D.ranOutStatus) s) := by
  have tc : ∃ hc, (taint.check (Taint.ofRegs [.rsp]) (.block [.mov .rcx (.mem (sp 120)),
      .alu .sub .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
      .mov32 .rdx (.imm (BitVec.ofNat 32 (Impl.Dsa.X86_64.Generation.Refill.budget pLen))),
      .alu .cmp .rcx (.reg .rdx)]) hc).isSome = true := by
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have tr : ∃ hc, (taint.check (Taint.ofRegs [.rsp, .rcx, .rdx])
      (.seq (.block [.mov32 .rax (.imm (BitVec.ofNat 32 (256 * pLen))), .alu .cmp .rcx (.reg .rax)])
        (.seq (.ite .b (.block []) (.block [.mov .rax (.reg .rcx)]))
          (.seq (.block [.alu .add .rax (.reg .rax), .alu .cmp .rax (.reg .rdx)])
            (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block []))))) hc).isSome = true := by
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  have pn : pLen ≤ 384 := by omega
  unfold Impl.Dsa.X86_64.Generation.Refill.ranOut
  refine RelCT.seq (two_piece (Ψ := RanOutCompared n pLen qLen) [.rsp]
    (fun D s t hs ht => doneAt_pins n pLen qLen D s t hs.1 ht.1) tc.choose_spec fun D s h => ?_) ?_
  · obtain ⟨hd, h0⟩ := h
    obtain ⟨⟨W, hm, _⟩, _, c3, _, _, _, hpl, _⟩ := id hd
    obtain ⟨V, R⟩ := hm.rep
    have h15 : W 15 = BitVec.ofNat 64 D.ctx.rand.bytes.length :=
      (hm.slots 15 (by simp [generationSlots])).trans (D.ctx.withHs D.hs).randLengthSlot
    have h3r : InRegions (s.rd ++ s.wr) (off D.ctx.geo.F 320) 8 := doneAt_ctlIn hd (k := 3) (by decide)
    have h3 : s.mem.readW (off D.ctx.geo.F 320) 64 = BitVec.ofNat 64 D.cursor := c3
    refine WP.mono (Refill.ranOutCmp_ok hm.layout R h3r h3 h15 D.cursorBound D.ends.lenBound pn)
      fun t ⟨⟨rc, rd, cf, mt⟩, kt⟩ => ?_
    subst pLen
    exact ⟨⟨doneAt_keep' hd mt kt (by decide), h0⟩, rc, rd, by simp only [eval, cf]⟩
  refine two_ite (fun D s t hs ht => hs.2.2.2.trans ht.2.2.2.symm) ?_ ?_
  · refine two_post (Ψ := fun (D : DonePublic) s => DoneAt n pLen qLen (D.withStatus D.ranOutStatus) s)
      (two_taint [.rsp, .rcx, .rdx] ?_ tr.choose_spec) fun D s h => ?_
    · intro D s t hs ht r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (doneAt_rsp hs.1.1.1).trans (doneAt_rsp ht.1.1.1).symm
      · exact hs.1.2.1.trans ht.1.2.1.symm
      · exact hs.1.2.2.1.trans ht.1.2.2.1.symm
    · obtain ⟨⟨⟨hd, h0⟩, rc, rd, cb⟩, hb⟩ := h
      have lt : D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen := by
        have := cb.symm.trans hb; simpa using this
      have e : D.withStatus D.ranOutStatus = D := by
        simp only [DonePublic.ranOutStatus, lt, ↓reduceIte, ← h0]; rfl
      have pl : D.ctx.geo.pLen = pLen := hd.2.2.2.2.2.2.1
      subst pLen
      have hl := D.ends.lenBound
      refine WP.mono (Refill.request_ok (L := D.ctx.rand.bytes.length - D.cursor) (by omega) (by omega)
        (by omega) rc rd) fun t ⟨_, mt, kt⟩ => ?_
      rw [e]; exact doneAt_keep' hd mt kt (by decide)
  · refine two_piece [.rsp] (fun D s t hs ht => doneAt_pins n pLen qLen D s t hs.1.1.1 ht.1.1.1)
      (by taint_decide) fun D s h => ?_
    obtain ⟨⟨⟨hd, _⟩, _, _, cb⟩, hb⟩ := h
    have ge : ¬ D.ctx.rand.bytes.length - D.cursor < 32769 * D.ctx.geo.pLen := by
      have := cb.symm.trans hb; simpa using this
    have e : D.ranOutStatus = BitVec.ofNat 64 2 := by simp only [DonePublic.ranOutStatus, ge, ↓reduceIte]; rfl
    rw [e]; exact doneStatus_ready hd 2 (Or.inr rfl)

/-! ## `results` -/

def ZeroTested (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  DoneAt n pLen qLen D t ∧ isa.eval .e t = some (D.status == 0)

theorem zeroTest_ready {n pLen qLen : Nat} {D : DonePublic} {s : State} (h : DoneAt n pLen qLen D s) :
    WP isa (.block [.mov .rax (.mem (sp 152)), .alu .test .rax (.reg .rax)]) s (ZeroTested n pLen qLen D) := by
  obtain ⟨⟨W, hm, h19, _⟩, _⟩ := id h
  refine WP.mono (Refill.zeroTest_ok hm) fun t ⟨z, _, mt, kt⟩ => ?_
  exact ⟨doneAt_keep' h mt kt (by decide), by simp only [eval, z, h19]⟩

theorem zeroTest_ct (n pLen qLen : Nat) :
    RelCT isa (Two (DoneAt n pLen qLen)) (.block [.mov .rax (.mem (sp 152)), .alu .test .rax (.reg .rax)])
      (Two (ZeroTested n pLen qLen)) :=
  two_piece [.rsp] (doneAt_pins n pLen qLen) (by taint_decide) fun _ _ h => zeroTest_ready h

def OneTested (n pLen qLen : Nat) (D : DonePublic) (t : State) : Prop :=
  DoneAt n pLen qLen D t ∧ isa.eval .e t = some (D.status == 1)

theorem results_ct (n pLen qLen : Nat) (hp : pLen = 128 ∨ pLen = 256 ∨ pLen = 384) :
    RelCT isa (Two (DoneAt n pLen qLen)) (Impl.Dsa.X86_64.Generation.Refill.results pLen)
      (Two (DoneAt n pLen qLen)) := by
  have zpins : Pins (ZeroTested n pLen qLen) [.rsp] := fun D s t hs ht => doneAt_pins n pLen qLen D s t hs.1 ht.1
  unfold Impl.Dsa.X86_64.Generation.Refill.results
  refine RelCT.seq (zeroTest_ct n pLen qLen) (two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_)
  · refine RelCT.seq (((ranOut_ct n pLen qLen hp).mono (fun s t h => ?_) fun _ _ h => two_image _ h)) ?_
    · obtain ⟨D, ⟨⟨hs, es⟩, bs⟩, ⟨⟨ht, _⟩, _⟩⟩ := h
      have z : D.status = 0 := by have := es.symm.trans bs; simpa using this
      exact ⟨D, ⟨hs, z⟩, ⟨ht, z⟩⟩
    refine RelCT.seq (zeroTest_ct n pLen qLen) (two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_)
    · refine (show RelCT isa _ (.block (([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++
          [.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .store (at0 .rcx) .rax,
            .store { base := .rcx, disp := 24 } .rdx]) ++
          ([.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
            .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax]))) _ from ?_)
      refine RelCT.block_append (RelCT.seq ((stateBlock_ct n pLen qLen _ (Or.inl rfl)).mono
        (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h) (usedBlock_ct n pLen qLen _ (Or.inl rfl)))
    · refine (show RelCT isa _ (.block (([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++
          [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) ++
          ([.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
            .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax]))) _ from ?_)
      refine RelCT.block_append (RelCT.seq ((stateBlock_ct n pLen qLen _ (Or.inr rfl)).mono
        (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h) (usedBlock_ct n pLen qLen _ (Or.inl rfl)))
  · refine RelCT.seq (R := Two (OneTested n pLen qLen)) ?_
      (two_ite (fun D s t hs ht => hs.2.trans ht.2.symm) ?_ ?_)
    · refine (show RelCT isa _ (.block (([.mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 1))] ++
          [.mov32 .rax (.imm 0), .store (at0 .rcx) .rax, .store { base := .rcx, disp := 24 } .rax]) ++
          Impl.Dsa.X86_64.Generation.successStatus)) _ from ?_)
      refine RelCT.block_append (RelCT.seq ((stateBlock_ct n pLen qLen _ (Or.inr rfl)).mono
        (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) fun _ _ h => h)
        (two_piece [.rsp] (doneAt_pins n pLen qLen) (by taint_decide) fun D s h => ?_))
      obtain ⟨⟨W, hm, h19, _⟩, _⟩ := id h
      obtain ⟨V, R⟩ := hm.rep
      refine WP.mono (successStatus_ok hm.layout R) fun t ⟨z, mt, kt⟩ => ?_
      exact ⟨doneAt_keep' h mt kt (by decide), by simp only [eval, z, h19]⟩
    · exact (show RelCT isa _ (.block ([.mov .rax (.mem (sp 128)),
          .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax])) _ from
        (usedBlock_ct n pLen qLen _ (Or.inr rfl)).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h)
          fun _ _ h => h)
    · exact (show RelCT isa _ (.block ([.mov .rax (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 3)),
          .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 0))] ++ [.store (at0 .rcx) .rax])) _ from
        (usedBlock_ct n pLen qLen _ (Or.inl rfl)).mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h)
          fun _ _ h => h)

end VG.Proof.Dsa.X86_64.Generation
