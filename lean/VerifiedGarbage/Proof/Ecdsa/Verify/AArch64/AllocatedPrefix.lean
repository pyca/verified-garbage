import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedInput
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrefix
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass.AArch64

/-- Public scalar values and stack address at the variable-time inverse boundary. -/
def InversePair (s₀ t₀ : State) (s t : State) : Prop :=
  InverseInput p256 s₀ (s₀.gpr .x3) s ∧
  InverseInput p256 t₀ (s₀.gpr .x3) t ∧ s.sp=t.sp

def allocatedPrefix : Prog isa :=
  .seq (.block (Cfg.args p256)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.prefixWith p256 (some D)) <|
  .seq (.block (Cfg.loadS p256)) <|
  .seq (.block (VG.Impl.Ecdh.AArch64.Cfg.peer p256)) <|
  .seq (VG.Impl.Ecdh.AArch64.Cfg.validate p256) <|
  .seq (Cfg.scalars p256) <| .seq P256Allocated.inverse <|
  .seq (Cfg.uv p256) (.block [])

theorem allocatedPrefix_cut {s s' : State} {trace : List Leak}
    (he : Exec isa allocatedPrefix s trace s') :
    ∃ a b tp ti tu,Exec isa (beforeInverse p256) s tp a ∧
      Exec isa P256Allocated.inverse a ti b ∧
      Exec isa (Cfg.uv p256) b tu s' ∧ trace=tp++ti++tu := by
  cases he with
  | seq e0 e => cases e with
    | seq e1 e => cases e with
      | seq e2 e => cases e with
        | seq e3 e => cases e with
          | seq e4 e => cases e with
            | seq e5 e => cases e with
              | seq ei e => cases e with
                | seq eu en =>
                  cases en
                  rename_i hn
                  cases hn
                  have nil : ∀ a : State,Exec isa (.block []) a [] a := fun _ => .block rfl
                  have pre := Exec.seq e0 (.seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (nil _))))))
                  exact ⟨_,_,_,_,_,pre,ei,eu,by simp only [List.append_nil,List.append_assoc]⟩

theorem allocatedPrefix_ct (hc : CfgOk p256)
    (hinv : ∀ s₀ t₀,JacPublic p256 s₀ t₀ →
      RelCT isa (InversePair s₀ t₀) P256Allocated.inverse
        (AArch64.Taint.Agree (Taint.ofRegs [.x0])))
    (huv : FieldCT (Cfg.uv p256)) :
    ConstantTime isa (VPre p256) (JacPublic p256) allocatedPrefix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁,b₁,tp₁,ti₁,tu₁,ep₁,ei₁,eu₁,h₁⟩ := allocatedPrefix_cut e₁
  obtain ⟨a₂,b₂,tp₂,ti₂,tu₂,ep₂,ei₂,eu₂,h₂⟩ := allocatedPrefix_cut e₂
  have hp := beforeInverse_ct _ _ _ _ _ _ trivial trivial pub.ptrs ep₁ ep₂
  obtain ⟨_,_,wp₁,m₁⟩ := beforeInverse_ok hc pre₁
  obtain ⟨_,_,wp₂,m₂⟩ := beforeInverse_ok hc pre₂
  obtain ⟨_,rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_,rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3=s₂.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have sp : a₁.sp=a₂.sp := (Exec.rdwr ep₁).2.2.trans
    (pub.ptrs.1.trans (Exec.rdwr ep₂).2.2.symm)
  have pair : InversePair s₁ s₂ a₁ a₂ := by
    refine ⟨m₁,?_,sp⟩
    rw [base]; exact m₂
  obtain ⟨hi,uvpub⟩ := hinv s₁ s₂ pub _ _ _ _ _ _ pair ei₁ ei₂
  have hu := huv _ _ _ _ _ _ trivial trivial uvpub eu₁ eu₂
  rw [h₁,h₂,hp,hi,hu]

theorem allocatedVerify_cut {s s' : State} {t : List Leak}
    (he : Exec isa Impl.Ecdsa.Verify.AArch64.P256Allocated.verify s t s') :
    ∃ a b tp tq tt,Exec isa allocatedPrefix s tp a ∧
      Exec isa Impl.Ecdsa.Verify.AArch64.P256Allocated.points a tq b ∧
      Exec isa (Impl.Ecdsa.Verify.AArch64.Cfg.tail p256) b tt s' ∧ t=tp++tq++tt := by
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

/-- The new points stage has the same public leakage boundary as the original verifier. -/
theorem allocatedVerify_ct_of_points
    (hprefix : ∀ s,VPre p256 s → WP isa allocatedPrefix s fun t => ∃ g,Mid p256 s (s.gpr .x3) g t)
    (hbefore : ConstantTime isa (VPre p256)
      (JacPublic p256) allocatedPrefix)
    (hpoints : ∀ s₀ t₀,VPre p256 s₀ → VPre p256 t₀ →
      RelCT isa (JointBoundary p256 s₀ t₀) Impl.Ecdsa.Verify.AArch64.P256Allocated.points
        (AArch64.Taint.Agree (Taint.ofRegs [.x0])))
    (htail : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p256)) :
    ConstantTime isa (VPre p256) (JacPublic p256) Impl.Ecdsa.Verify.AArch64.P256Allocated.verify := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  obtain ⟨a₁,b₁,tp₁,tq₁,tt₁,ep₁,eq₁,et₁,h₁⟩ := allocatedVerify_cut e₁
  obtain ⟨a₂,b₂,tp₂,tq₂,tt₂,ep₂,eq₂,et₂,h₂⟩ := allocatedVerify_cut e₂
  have ht := hbefore _ _ _ _ _ _ pre₁ pre₂ pub ep₁ ep₂
  obtain ⟨_,_,wp₁,m₁⟩ := hprefix _ pre₁
  obtain ⟨_,_,wp₂,m₂⟩ := hprefix _ pre₂
  obtain ⟨_,rfl⟩ := Exec.det ep₁ wp₁
  obtain ⟨_,rfl⟩ := Exec.det ep₂ wp₂
  have base : s₁.gpr .x3=s₂.gpr .x3 := pub.ptrs.2 .x3 (by decide)
  have sp : a₁.sp=a₂.sp := (Exec.rdwr ep₁).2.2.trans
    (pub.ptrs.1.trans (Exec.rdwr ep₂).2.2.symm)
  have boundary : JointBoundary p256 s₁ s₂ a₁ a₂ := by
    refine ⟨pub,m₁,?_,sp⟩
    rw [base]; exact m₂
  obtain ⟨hq,tailpub⟩ := hpoints s₁ s₂ pre₁ pre₂ _ _ _ _ _ _ boundary eq₁ eq₂
  have hf := htail _ _ _ _ _ _ trivial trivial tailpub et₁ et₂
  rw [h₁,h₂,ht,hq,hf]


end VG.Proof.Ecdsa.Verify.AArch64
