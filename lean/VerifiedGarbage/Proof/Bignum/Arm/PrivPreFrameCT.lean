module

public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreValidCT
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreFrame
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryReady
import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Bignum.Arm.PcPush
import VerifiedGarbage.Proof.Rsa.BytesFrame
import VerifiedGarbage.Proof.Framework.Arm.Frame
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Proof.Bignum.Arm.PrivPreValidCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PrivPreFrame
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
meta import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheckCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtEntryCT
meta import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
meta import VerifiedGarbage.Proof.Bignum.Arm.StackCT
meta import VerifiedGarbage.Proof.Bignum.Arm.PcPush
meta import VerifiedGarbage.Proof.Rsa.BytesFrame
meta import VerifiedGarbage.Proof.Framework.Arm.Frame
meta import VerifiedGarbage.Proof.Framework.Arm.Exec
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Proof.Framework.Semantics

/-! # The precomputation's body and the CRT's frame around it leak only the modulus -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Bignum.Arm.PrivPreFn VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem pp_body_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) :
    RelCT isa (fun s t => (CrtBodyInput g bs1 s ∧ PpPre g s) ∧ (CrtBodyInput g bs2 t ∧ PpPre g t) ∧ s.sp = t.sp)
      body (fun _ _ => True) := by
  let Checked := fun (bs : Fin 7 → List Byte) (s : State) => (CrtBodyInput g bs s ∧ PpPre g s) ∧
    s.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs 0)) g.length
  have checkWP (s : State) {bs : Fin 7 → List Byte} (h : CrtBodyInput g bs s ∧ PpPre g s) :
      WP isa (.block modulusCheck) s (Checked bs) := by
    refine WP.mono (modulusCheck_ok s h.1.buffers.lengthValid.1 h.1.buffers.lengthValid.2
      (h.1.buffers.source 0).fits (h.1.buffers.source 0).read h.1.source h.1.count) ?_
    rintro t ⟨flag, mem, rest⟩
    have nb : Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length = bs 0 := (h.1.buffers.source 0).bytes
    change t.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr g.modulus) g.length)) g.length at flag
    rw [nb] at flag
    exact ⟨⟨h.1.of_mem mem rest ((rest.gpr .r0 (by decide)).trans h.1.ptr)
      ((rest.gpr .r4 (by decide)).trans h.1.source) ((rest.gpr .r6 (by decide)).trans h.1.count), h.2.after rest⟩, flag⟩
  have check : RelCT isa (fun s t => (CrtBodyInput g bs1 s ∧ PpPre g s) ∧ (CrtBodyInput g bs2 t ∧ PpPre g t) ∧
      s.sp = t.sp) (.block modulusCheck) (fun _ _ => True) := by
    intro s t tr1 tr2 u v h e1 e2
    exact ⟨modulusCheck_ct s t tr1 tr2 u v trivial trivial
      ⟨h.1.1.source.trans h.2.1.1.source.symm, h.1.1.count.trans h.2.1.1.count.symm⟩ e1 e2, trivial⟩
  have ready := (relCT_keep_sp check (fun _ _ h => h.2.2)).wp
    (fun s t h => ⟨checkWP s h.1, checkWP t h.2.1⟩)
  refine ready.seq (RelCT.ite ?_ ?_ ?_)
  · intro s t h
    change some s.z = some t.z
    rw [h.2.1.2, h.2.2.2, modulus]
  · apply (pp_valid_ct (g := g) (bs1 := bs1) (bs2 := bs2)).mono ?_ (fun _ _ _ => trivial)
    intro s t h
    have flag : s.z = true := Option.some.inj h.2
    have good := h.1.2.1.2.symm.trans flag
    have good2 : Spec.Rsa.modulusValid (Spec.Rsa.os2ip (bs2 0)) g.length = true := by rw [← modulus]; exact good
    let a := h.1.2.1.1.1
    let b := h.1.2.2.1.1
    exact ⟨⟨⟨a.buffers, a.stack, a.ptr, a.count, a.saved, a.modulusPtr, good⟩, h.1.2.1.1.2⟩,
      ⟨⟨b.buffers, b.stack, b.ptr, b.count, b.saved, b.modulusPtr, good2⟩, h.1.2.2.1.2⟩, h.1.1⟩
  · apply RelCT.taint (A := taint) (Taint.ofRegs []) _ (by taint_decide)
    intro s t _
    exact Taint.agree_ofRegs (by simp)

theorem PpPre.expanded {g : CrtGeometry} {s : State} (h : PpPre g s) : PpPre g (crtExpanded s g.base g.words) :=
  ⟨h.fit, (by obtain ⟨r, hr, hc⟩ := h.write; exact ⟨r, List.mem_append_right _ hr, hc⟩), h.workspace, h.stack,
    h.sources, h.input, h.qi⟩

theorem pp_body_scoped_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) :
    RelCT isa (fun s t =>
      (CrtScopedInput g bs1 s ∧ PpPre g s ∧
        Spec.Rsa.wordsAt s.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0) ∧
      (CrtScopedInput g bs2 t ∧ PpPre g t ∧
        Spec.Rsa.wordsAt t.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0) ∧
      s.sp = t.sp) body (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  obtain ⟨trS, uS, runS, _⟩ := pp_body_ok _ h.1.1.body h.1.2.1.expanded h.1.2.2
  obtain ⟨trT, uT, runT, _⟩ := pp_body_ok _ h.2.1.1.body h.2.1.2.1.expanded h.2.1.2.2
  obtain ⟨writeS, readS⟩ := crt_expanded_covers h.1.1.workspace h.1.1.body.buffers.storageFits
  obtain ⟨writeT, readT⟩ := crt_expanded_covers h.2.1.1.workspace h.2.1.1.body.buffers.storageFits
  have wideS : Exec isa body s trS (uS.withRegions s.rd s.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runS readS writeS
  have wideT : Exec isa body t trT (uT.withRegions t.rd t.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runT readT writeT
  have trace := pp_body_ct modulus _ _ _ _ _ _
    ⟨⟨h.1.1.body, h.1.2.1.expanded⟩, ⟨h.2.1.1.body, h.2.1.2.1.expanded⟩, h.2.2⟩ runS runT
  exact ⟨(Exec.det e1 wideS).1.trans (trace.1.trans (Exec.det e2 wideT).1.symm), trivial⟩

theorem pp_crtFrame_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) :
    RelCT isa (fun s t => (CrtFnInput g bs1 s ∧ PpCall g s) ∧ (CrtFnInput g bs2 t ∧ PpCall g t) ∧ s.sp = t.sp)
      crtFrame (fun _ _ => True) := by
  unfold crtFrame
  apply RelCT.frame (fun _ _ h => h.2.2)
  intro s t tr1 tr2 u v hp e1 e2
  obtain ⟨s0, t0, ⟨hs, ht, sp⟩, ps, pt⟩ := hp
  have ps' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) hs.1.stackFit
  have pt' := push_pushed
    (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr]) (by decide) ht.1.stackFit
  have es : pcPushed s0 = s := Option.some.inj (ps'.symm.trans ps)
  have et : pcPushed t0 = t := Option.some.inj (pt'.symm.trans pt)
  subst s; subst t
  have prep (x : State) {bs : Fin 7 → List Byte} (hx : CrtFnInput g bs x ∧ PpCall g x) :
      WP isa (.block CrtFn.entry) (pcPushed x) fun y => CrtScopedInput g bs y ∧ PpPre g y ∧
        Spec.Rsa.wordsAt y.mem (State.addr g.output) (ppPreWords g) = List.replicate (ppPreWords g) 0 := by
    refine WP.mono (crt_entry_ready x hx.1) ?_
    rintro y ⟨ready, frameY, _, restY⟩
    refine ⟨ready, ⟨hx.2.fit, ?_, hx.2.workspace, ?_, hx.2.sources, hx.2.input, hx.2.qi⟩, ?_⟩
    · rw [restY.wr]; obtain ⟨r, hr, hc⟩ := hx.2.write; exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩
    · rw [restY.sp]; exact pp_push_separate hx.1.stackFit hx.2.below hx.2.args
    · rw [Proof.Rsa.wordsAt_frame frameY (by have := hx.2.fit; omega)
        (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hx.2.below.symm)]
      exact hx.2.cleared
  cases e1 with
  | seq entry1 tail1 =>
    cases e2 with
    | seq entry2 tail2 =>
      obtain ⟨trace, sp'⟩ := crt_entry_ct _ _ _ _ _ _ (by simp only [pcPushed, pushed_sp, sp]) entry1 entry2
      obtain ⟨_, s1, run1, ready1⟩ := prep s0 hs
      obtain ⟨_, t1, run2, ready2⟩ := prep t0 ht
      obtain ⟨-, rfl⟩ := Exec.det entry1 run1
      obtain ⟨-, rfl⟩ := Exec.det entry2 run2
      have bodyCT := relCT_keep_sp (pp_body_scoped_ct (g := g) modulus) (fun _ _ h => h.2.2)
      have restore : RelCT isa (fun s t => s.sp = t.sp) (.block PcFn.restore) (fun s t => s.sp = t.sp) :=
        stackLoads_ct pcCalleeSaved
      obtain ⟨tailTrace, _⟩ := bodyCT.seq restore _ _ _ _ _ _ ⟨ready1, ready2, sp'⟩ tail1 tail2
      exact ⟨by rw [trace, tailTrace], trivial⟩

end VG.Proof.Bignum.Arm
