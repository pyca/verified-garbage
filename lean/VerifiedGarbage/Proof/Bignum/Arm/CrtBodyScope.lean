module

public import VerifiedGarbage.Proof.Bignum.Arm.WindowKernel
public import VerifiedGarbage.Impl.Bignum.Arm.CrtFn
public import VerifiedGarbage.Proof.Bignum.Arm.CrtBodyInput
public import VerifiedGarbage.Proof.Bignum.Arm.CrtStorage
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
public import VerifiedGarbage.Proof.Framework.RelCT

import VerifiedGarbage.Proof.Bignum.Arm.CrtBodyCT
import VerifiedGarbage.Proof.Bignum.Arm.CrtBody

/-! # Run the CRT proof using only the caller's original scratch permissions -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Impl.Bignum.Arm
open VG.Proof.X25519.Arm (Rest)

structure CrtScopedInput (g : CrtGeometry) (bs : Fin 7 → List Byte) (s : State) : Prop where
  workspace : Workspace s g.base g.size
  body : CrtBodyInput g bs (crtExpanded s g.base g.words)

theorem crt_body_scoped_ok (s : State) {g : CrtGeometry} {bs : Fin 7 → List Byte} (h : CrtScopedInput g bs s) (kernel : WindowKernel := baselineWindowKernel) :
    WP isa (CrtFn.bodyWith kernel.code) s fun t =>
      Spec.Rsa.written t.mem (State.addr g.output) g.length (t.gpr .r0)
        (Spec.Rsa.privateCrt (bs 0) (bs 1) (bs 2) (bs 3) (bs 4) (bs 5) (bs 6)) ∧
      Frame (crtMutable g s.sp ++ [⟨State.addr g.output, g.length⟩]) s.mem t.mem ∧ Rest roundClobbers s t := by
  obtain ⟨tr, t, run, written, frame, rest⟩ := (crt_body_ok (kernel := kernel)) _ h.body
  obtain ⟨write, read⟩ := crt_expanded_covers h.workspace h.body.buffers.storageFits
  refine ⟨tr, t.withRegions s.rd s.wr, ?_, written, frame, ?_⟩
  · simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen run read write
  · exact ⟨rest.gpr, rfl, rfl, rest.sp⟩

theorem crt_body_scoped_ct {g : CrtGeometry} {bs1 bs2 : Fin 7 → List Byte} (modulus : bs1 0 = bs2 0) (kernel : WindowKernel := baselineWindowKernel) :
    RelCT isa (fun s t => CrtScopedInput g bs1 s ∧ CrtScopedInput g bs2 t ∧ s.sp = t.sp)
      (CrtFn.bodyWith kernel.code) (fun _ _ => True) := by
  intro s t tr1 tr2 u v h e1 e2
  obtain ⟨trS, uS, runS, _⟩ := (crt_body_ok (kernel := kernel)) _ h.1.body
  obtain ⟨trT, uT, runT, _⟩ := (crt_body_ok (kernel := kernel)) _ h.2.1.body
  obtain ⟨writeS, readS⟩ := crt_expanded_covers h.1.workspace h.1.body.buffers.storageFits
  obtain ⟨writeT, readT⟩ := crt_expanded_covers h.2.1.workspace h.2.1.body.buffers.storageFits
  have wideS : Exec isa (CrtFn.bodyWith kernel.code) s trS (uS.withRegions s.rd s.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runS readS writeS
  have wideT : Exec isa (CrtFn.bodyWith kernel.code) t trT (uT.withRegions t.rd t.wr) := by
    simpa only [crtExpanded, State.withRegions_withRegions, State.withRegions_self] using VG.Arm.Exec.widen runT readT writeT
  have trace := (crt_body_ct (kernel := kernel)) modulus _ _ _ _ _ _ ⟨h.1.body, h.2.1.body, h.2.2⟩ runS runT
  exact ⟨(Exec.det e1 wideS).1.trans (trace.1.trans (Exec.det e2 wideT).1.symm), trivial⟩

end VG.Proof.Bignum.Arm
