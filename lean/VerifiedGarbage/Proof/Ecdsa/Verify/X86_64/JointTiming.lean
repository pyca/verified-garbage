import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain

/-! Split the public joint verifier at the scalar and point-operation boundaries. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Weierstrass.X86_64

def jointPrefix (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.args c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.prefix' c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.X86_64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.X86_64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.X86_64.Cfg.validate c) <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.scalars c) <| .seq c.nPow <|
  .seq (Impl.Ecdsa.Verify.X86_64.Cfg.uv c) (.block [])

theorem jointPrefix_ok {c : Cfg} (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (jointPrefix c) s₀ fun s => ∃ g,Mid c s₀ (s₀.gpr .rcx) g s := by
  refine front_ok hc hp fun g _ _ hF => mid_ok hc hF fun _ hM => WP.block_nil ⟨g,hM⟩

theorem jointVerify_cut {c : Cfg} {j : Joint.Cfg} {double : Prog isa} {s s' : State} {t : List Leak}
    (he : Exec isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double) s t s') :
    ∃ a b tp tc ts, Exec isa (jointPrefix c) s tp a ∧
      Exec isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double) a tc b ∧
      Exec isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c) b ts s' ∧ t=tp++tc++ts := by
  cases he with
  | seq e0 h => cases h with
    | seq e1 h => cases h with
      | seq e2 h => cases h with
        | seq e3 h => cases h with
          | seq e4 h => cases h with
            | seq e5 h => cases h with
              | seq e6 h => cases h with
                | seq e7 h => cases h with
                  | seq ec es =>
                    have nil : ∀ a : State,Exec isa (.block []) a [] a := fun _ => .block rfl
                    have ep := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5
                      (.seq e6 (.seq e7 (nil _))))))))
                    exact ⟨_,_,_,_,_,ep,ec,es,by simp only [List.append_nil,List.append_assoc]⟩

theorem jointVerify_ct_of_points {c : Cfg} {j : Joint.Cfg} {double : Prog isa} {d : CombData}
    (hc : CfgOk c)
    (before : ConstantTime isa (fun _ => True)
      (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix c))
    (points : ∀ {s₀ t₀ : State},VPre c s₀ → VPre c t₀ → JointPublic c d s₀ t₀ →
      RelCT isa (fun s t => (∃ g,Mid c s₀ (s₀.gpr .rcx) g s) ∧ (∃ h,Mid c t₀ (t₀.gpr .rcx) h t))
        (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double)
        (fun s t => X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t))
    (after : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail c)) :
    ConstantTime isa (VPre c) (JointPublic c d) (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double) := by
  intro s₀ t₀ ls lt s' t' ps pt pub es et
  obtain ⟨a,b,lp,lc,lf,ep,ec,ef,he⟩ := jointVerify_cut es
  obtain ⟨a',b',lp',lc',lf',ep',ec',ef',he'⟩ := jointVerify_cut et
  have hp := before _ _ _ _ _ _ trivial trivial pub.regs ep ep'
  obtain ⟨_,_,wp,pm⟩ := jointPrefix_ok hc ps
  obtain ⟨_,_,wp',pm'⟩ := jointPrefix_ok hc pt
  obtain ⟨_,rfl⟩ := Exec.det ep wp
  obtain ⟨_,rfl⟩ := Exec.det ep' wp'
  obtain ⟨hct,hpub⟩ := points ps pt pub _ _ _ _ _ _ ⟨pm,pm'⟩ ec ec'
  have hf := after _ _ _ _ _ _ trivial trivial hpub ef ef'
  rw [he,he',hp,hct,hf]

end VG.Proof.Ecdsa.Verify.X86_64
