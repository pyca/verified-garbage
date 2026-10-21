module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
import VerifiedGarbage.Proof.Framework.AArch64.Inline
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass.AArch64
theorem verify_cut_generic {c : Cfg} {points : Prog isa} {s s' : State} {t : List Leak}
    (he : Exec isa (.seq (.block (Cfg.args c)) <| .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
      .seq (.block (Cfg.loadS c)) <| .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
      .seq (Impl.Ecdh.AArch64.Cfg.validate c) <| .seq (Cfg.scalars c) <|
      .seq c.nPow <| .seq (Cfg.uv c) <| .seq points (Cfg.tail c)) s t s') :
    ∃ a b tp tq tt,Exec isa (jointPrefix c) s tp a ∧
      Exec isa points a tq b ∧
      Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.tail c) b tt s' ∧ t=tp++tq++tt := by
  cases he with
  | seq e0 e => cases e with
    | seq e1 e => cases e with
      | seq e2 e => cases e with
        | seq e3 e => cases e with
          | seq e4 e => cases e with
            | seq e5 e => cases e with
              | seq e6 e => cases e with
                | seq e7 e => cases e with
                  | seq ep et =>
                    have nil : ∀ a : State,Exec isa (.block []) a [] a := fun _ => .block rfl
                    have pre := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4
                      (.seq e5 (.seq e6 (.seq e7 (nil _))))))))
                    exact ⟨_,_,_,_,_,pre,ep,et,by simp only [List.append_nil,List.append_assoc]⟩

theorem jointVerify_cut {s s' : State} {t : List Leak}
    (he : Exec isa Impl.Ecdsa.Verify.AArch64.P384Joint.verify s t s') :
    ∃ a b tp tq tt,Exec isa (jointPrefix p384) s tp a ∧
      Exec isa Impl.Ecdsa.Verify.AArch64.P384Joint.points a tq b ∧
      Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.tail p384) b tt s' ∧ t=tp++tq++tt := by
  exact verify_cut_generic he

/-- The new points stage has the same public leakage boundary as the original verifier. -/
theorem jointVerify_ct_of_points
    (hc : CfgOk p384)
    (hbefore : ConstantTime isa (fun _ => True)
      (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p384))
    (hpoints : ∀ s₀ t₀,VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s₀ →
      VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords t₀ →
      RelCT isa (JointBoundaryT p384 "VG_P384_GTAB" s₀ t₀) Impl.Ecdsa.Verify.AArch64.P384Joint.points
        (AArch64.Taint.Agree (Taint.ofRegs [.x0])))
    (htail : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p384)) :
    ConstantTime isa (VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords) (JacPublicT p384 "VG_P384_GTAB")
      Impl.Ecdsa.Verify.AArch64.P384Joint.verify := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁,b₁,tp₁,tq₁,tt₁,ep₁,eq₁,et₁,h₁⟩ := jointVerify_cut e₁
  obtain ⟨a₂,b₂,tp₂,tq₂,tt₂,ep₂,eq₂,et₂,h₂⟩ := jointVerify_cut e₂
  have ht := hbefore _ _ _ _ _ _ trivial trivial pub.ptrs ep₁ ep₂
  obtain ⟨_,_,wp₁,m₁⟩ := jointPrefix_ok hc pre₁
  obtain ⟨_,_,wp₂,m₂⟩ := jointPrefix_ok hc pre₂
  obtain ⟨_,rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_,rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3=s₂.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have sp : a₁.sp=a₂.sp := (Exec.rdwr ep₁).2.2.trans
    (pub.ptrs.1.trans (Exec.rdwr ep₂).2.2.symm)
  have boundary : JointBoundaryT p384 "VG_P384_GTAB" s₁ s₂ a₁ a₂ := by
    refine ⟨pub,m₁,?_,sp⟩
    rw [base]; exact m₂
  obtain ⟨hq,tailpub⟩ := hpoints s₁ s₂ pre₁ pre₂ _ _ _ _ _ _ boundary eq₁ eq₂
  have hf := htail _ _ _ _ _ _ trivial trivial tailpub et₁ et₂
  rw [h₁,h₂,ht,hq,hf]

end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
