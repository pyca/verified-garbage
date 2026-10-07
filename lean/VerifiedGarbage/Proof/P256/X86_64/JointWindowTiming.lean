import VerifiedGarbage.Proof.P256.X86_64.JointWindow
import VerifiedGarbage.Proof.P256.X86_64.JointTiming
import VerifiedGarbage.Proof.P256.X86_64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointInitTiming

/-! Relate the complete window routine from its two already-recoded public scalars. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

structure JointWindowInput (c : Joint.Cfg) (base T : Addr) (size u v : Nat)
    {G : Point Spec.P256.curve} (Q : Point Spec.P256.curve)
    (row : JointGeneratorRow Spec.P256.curve G) (s : State) : Prop where
  point : InvJ Spec.P256.curve (tmv Spec.P256.curve c.K.M.n base s c.K.P.x)
    (tmv Spec.P256.curve c.K.M.n base s c.K.P.y) (tmv Spec.P256.curve c.K.M.n base s c.K.P.z) Q
  zero : tmv Spec.P256.curve c.K.M.n base s c.K.zero=0
  peer : ∀ i<257,s.mem (off base (c.K.bits+i))=FastNaf.byte 5 v i
  generator : ∀ i<257,s.mem (off base (c.gBits+i))=FastNaf.byte 7 u i
  external : JointGenerator c Spec.P256.curve base T size row s

theorem joint_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJoint.K publicJoint.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_infinity_ct : ScratchCT (.block (Jacobian.infinity publicJointAdx.K publicJointAdx.K.R)) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi]) (fun _ _ _ _ h => h) (by taint_decide)

theorem p256_jointWindow_relCT {c : Joint.Cfg} {base T : Addr} {size u v : Nat}
    {G Q : Point Spec.P256.curve} {row : JointGeneratorRow Spec.P256.curve G} {E : Nat → Fin Spec.P256.p}
    (hL : JointAddLayout c size) (hInit : JointInitLayout c size)
    (hm : UnitMod Spec.P256.p (2^(64*c.K.M.n))) (hC : Law Spec.P256.curve) (ha : AM3 Spec.P256.curve)
    (hn : (doubleSlots c.K.S c.K.R).Nodup)
    (hOne : c.K.one<Spec.P256.p) (hOneVal : toM Spec.P256.p (2^256) c.K.one=1)
    (hG : onCurve Spec.P256.curve G=true) (hQ : onCurve Spec.P256.curve Q=true)
    (hc : JointCachedChecks c) (hf : JointFixedChecks c)
    (hd : ScratchCT (doubleHalfPublic c.K.M c.K.S c.K.R))
    (ht : NafTableChecks c.K) (hcache : ScratchCT (Naf.cacheTable c.K.M c.K.tbl c.cache 8))
    (hseed : ScratchCT (.block (Jacobian.infinity c.K c.K.R))) (hu : u<2^256) (hv : v<2^256) :
    RelCT isa (fun s t => FieldPair c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointWindowInput c base T size u v Q row s ∧ JointWindowInput c base T size u v Q row t)
      (jointWindow c)
      (JointPair c Spec.P256.curve base size
        (JointCore c Spec.P256.curve base size Q u v (JointGenerator c Spec.P256.curve base T size row))
        (add (mul u G) (mul v Q)) 0) := by
  let Init := fun s => Inv c.K.M base size Spec.P256.p (·∈jointSlots c) (jointLive c)
      (tmv Spec.P256.curve c.K.M.n base s) s ∧ JointStable c Spec.P256.curve base Q u v s ∧
      JointGenerator c Spec.P256.curve base T size row s
  have table := (jointTables_relCT (C:=Spec.P256.curve) (base:=base) (E:=E) hInit hm hOne ht hcache).mono
    (P':=fun (s t : State) => FieldPair c.K.M base size Spec.P256.p (·∈nafSlots c.K) (winRo c.K) E s t ∧
      JointWindowInput c base T size u v Q row s ∧ JointWindowInput c base T size u v Q row t)
    (fun s t h => h.1) (fun s t h => h)
  have table' := table.wp (F₁:=Init) (F₂:=Init) (fun s t ⟨hp,ps,pt⟩ =>
    ⟨WP.mono (jointTables_ok hInit hm hC ha hOne hQ hp.1.to_tmv ps.point ps.zero ps.peer ps.generator ps.external)
      (fun _ h => h.2),
     WP.mono (jointTables_ok hInit hm hC ha hOne hQ hp.2.to_tmv pt.point pt.zero pt.peer pt.generator pt.external)
      (fun _ h => h.2)⟩)
  rw [jointWindow,Joint.window]
  apply RelCT.assoc
  apply RelCT.seq (table'.mono
    (Q':=fun (s t : State) => ∃ E',FieldPair c.K.M base size Spec.P256.p (·∈jointSlots c) (jointLive c) E' s t ∧ Init s ∧ Init t)
    (fun _ _ h => h)
    (fun _ _ ⟨⟨E',hp⟩,ps,pt⟩ => ⟨E',hp,ps,pt⟩))
  apply RelCT.seq (R:=JointPair c Spec.P256.curve base size
    (JointCore c Spec.P256.curve base size Q u v (JointGenerator c Spec.P256.curve base T size row)) .infinity 256)
  · apply RelCT.exists_
    intro E'
    have seed := (jointSeed_relCT (C:=Spec.P256.curve) (base:=base) (E:=E') hL.lookup.layout hOne hseed).mono
      (P':=fun (s t : State) => FieldPair c.K.M base size Spec.P256.p (·∈jointSlots c) (jointLive c) E' s t ∧ Init s ∧ Init t)
      (fun s t h => h.1) (fun s t h => h)
    have seed' := seed.wp (fun s t ⟨_,ps,pt⟩ =>
      ⟨WP.mono (jointSeed_ok hL.lookup.layout hOne ps.1 ps.2.1 ps.2.2) (fun _ h => h.2),
       WP.mono (jointSeed_ok hL.lookup.layout hOne pt.1 pt.2.1 pt.2.2) (fun _ h => h.2)⟩)
    exact seed'.mono (fun _ _ h => h) (fun _ _ ⟨hp,ps,pt⟩ => ⟨⟨_,hp⟩,ps.1,pt.1,ps.2,pt.2⟩)
  · exact p256_jointRun_relCT hL hm hC ha hn hOne hOneVal hG hQ hc hf hd hu hv

end VG.Proof.P256.X86_64
