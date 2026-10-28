module
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Rsa.X86.InvTimeBase
meta import VerifiedGarbage.Impl.Rsa.X86.InvBatchRt
public import VerifiedGarbage.Proof.Rsa.X86.InvTimeCompare
public import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Base
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Impl.Rsa.X86.CrtValuesRt
import VerifiedGarbage.Proof.Rsa.X86.InvTimeCheck
public import VerifiedGarbage.Proof.Rsa.X86.InvGuard
public import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.Comp
import VerifiedGarbage.Proof.Rsa.X86.InvBatchRt.Time.TimeBody
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! # The inverse's trace: a public guard, then the batches or the general inverse

The guard reads only public lengths, so both runs take the same branch; the batches' trace depends
only on the call's public data (`Time.relBody`), and so does the general inverse's.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.InvTiming
open VG VG.X86 VG.Proof.Mont VG.Proof.Rsa.X86.CrtValuesRt VG.Proof.Rsa.X86.KeyRt

theorem guard_check :
    (VG.Taint.check taint τ VG.Impl.Rsa.X86.InvBatchRt.guard
      (VG.Taint.hintOf taint τ VG.Impl.Rsa.X86.InvBatchRt.guard)).isSome = true := by taint_decide

/-- What the batches need of the lengths, where the guard allows them. -/
theorem fits {args : Nat → BitVec 32} {base : Addr} {size len P Q : Nat} {s : State}
    (h : InvInput args base size len P Q s) (good : Eligible args) :
    VG.Proof.Rsa.X86.InvBatchRt.Time.Fits size len := by
  obtain ⟨m16, big, _, _⟩ := good
  obtain ⟨a, al, aw, arg⟩ := h.ws.lenArg
  change kw a = kw len at aw
  have eq : BitVec.ofNat 32 a = args 7 := Option.some.inj (arg.readSrc.symm.trans h.gate.nArg.readSrc)
  have ae := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ae
  have nwl : VG.Proof.Rsa.X86.InvBatchRt.nw len = a / 8 := by
    have aw' := aw
    simp only [kw, Spec.Rsa.modulusWords] at aw'
    simp only [VG.Proof.Rsa.X86.InvBatchRt.nw, kw, Spec.Rsa.modulusWords]; omega
  have hf : VG.Impl.Rsa.X86.Keys.hdr + VG.Impl.Rsa.X86.CrtValues.nArr * VG.Proof.Rsa.X86.Keys.S (kw len) ≤ size :=
    h.ws.ws.fits
  have ke := VG.Proof.Rsa.X86.InvBatchRt.kw_eq len
  simp only [VG.Impl.Rsa.X86.Keys.hdr, VG.Impl.Rsa.X86.CrtValues.nArr, VG.Proof.Rsa.X86.Keys.S] at hf
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem dispatch_relCT {args : Nat → BitVec 32} {base : Addr} {size len P Q P' Q' : Nat} {sp : BitVec 32} :
    RelCT isa (Pair args base size len P Q P' Q' sp) VG.Impl.Rsa.X86.CrtValuesRt.inverseChoice (fun _ _ => True) := by
  let F (p q : Nat) (u : State) := InvInput args base size len p q u ∧ Public args base size sp u ∧
    u.cf = some (decide (Eligible args))
  have ready {p q : Nat} {s : State} (h : InvInput args base size len p q s) (pub : Public args base size sp s) :
      WP isa VG.Impl.Rsa.X86.InvBatchRt.guard s (F p q) :=
    WP.mono (guard_ok h) fun u g => ⟨g.input, pub.keep g.keeps (by decide) (by rw [g.mem]; exact Outside.refl _ _ _ _),
      g.cf⟩
  have trace : RelCT isa (Pair args base size len P Q P' Q' sp) VG.Impl.Rsa.X86.InvBatchRt.guard (fun _ _ => True) :=
    (RelCT.taint (A := taint) τ (fun _ _ h => agree h.1.1.ws.ws.workspace h.2.1.ws.ws.workspace h.1.2 h.2.2)
      guard_check).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  unfold VG.Impl.Rsa.X86.CrtValuesRt.inverseChoice VG.Impl.Rsa.X86.InvBatchRt.dispatch
  refine RelCT.seq ((trace.wp (F₁ := F P Q) (F₂ := F P' Q')
    (fun _ _ h => ⟨ready h.1.1 h.1.2, ready h.2.1 h.2.2⟩)).mono (fun _ _ h => h) (fun _ _ h => h.2)) ?_
  refine RelCT.ite (fun s t h => by change s.cf = t.cf; rw [h.1.2.2, h.2.2.2]) ?_ ?_
  · intro s t tr ur sf tf ⟨⟨hs, ht⟩, yes⟩ es et
    have good : Eligible args := by
      change s.cf = some true at yes
      rw [hs.2.2] at yes
      exact of_decide_eq_true (Option.some.inj yes)
    refine ⟨(VG.Proof.Rsa.X86.InvBatchRt.Time.relBody (fits hs.1 good) _ _ _ _ _ _
      ⟨⟨hs.1.ws, by decide, hs.2.1⟩, ⟨ht.1.ws, by decide, ht.2.1⟩⟩ es et).1, trivial⟩
  · exact (RelCT.taint (A := sseTaint) τ (fun _ _ h => agree h.1.1.1.ws.ws.workspace h.1.2.1.ws.ws.workspace
      h.1.1.2.1 h.1.2.2.1) fallback_check.choose_spec).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Rsa.X86.InvTiming
