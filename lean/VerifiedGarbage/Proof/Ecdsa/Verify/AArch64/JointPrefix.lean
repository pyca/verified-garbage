import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPublic
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64 VG.Proof.Mont.AArch64 VG.Proof.Mont
open VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64

/-- The unchanged verifier prefix, ending immediately after the two public scalars. -/
def jointPrefix (c : Cfg) : Prog isa :=
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.prefixWith c (some D)) <|
  .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) <|
  .seq (.block (Impl.Ecdh.AArch64.Cfg.peer c)) <|
  .seq (Impl.Ecdh.AArch64.Cfg.validate c) <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) <| .seq c.nPow <|
  .seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c) (.block [])

theorem jointPrefix_ok {c : Cfg} (hc : CfgOk c) {s₀ : State} (hp : VPre c s₀) :
    WP isa (jointPrefix c) s₀ fun t => ∃ g,Mid c s₀ (s₀.gpr .x3) g t := by
  refine front_ok hc hp fun g s₁ _ hF => mid_ok hc hF fun s₂ hM => ?_
  exact WP.block_nil ⟨g,hM⟩

theorem jointVerify_cut {s s' : State} {t : List Leak}
    (he : Exec isa Impl.Ecdsa.Verify.AArch64.P256Joint.verify s t s') :
    ∃ a b tp tq tt,Exec isa (jointPrefix p256) s tp a ∧
      Exec isa Impl.Ecdsa.Verify.AArch64.P256Joint.points a tq b ∧
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

/-- At the joint multiplication boundary, public inputs determine both initialized states. -/
def JointBoundary (c : Cfg) (s₀ t₀ : State) (s t : State) : Prop :=
  JacPublic c s₀ t₀ ∧ (∃ g,Mid c s₀ (s₀.gpr .x3) g s) ∧
    (∃ g,Mid c t₀ (s₀.gpr .x3) g t) ∧ s.sp=t.sp

/-- The new points stage has the same public leakage boundary as the original verifier. -/
theorem jointVerify_ct_of_points
    (hc : CfgOk p256)
    (hbefore : ConstantTime isa (fun _ => True)
      (AArch64.Taint.Agree (Taint.ofRegs [.x0,.x1,.x2,.x3])) (jointPrefix p256))
    (hpoints : ∀ s₀ t₀,VPre p256 s₀ → VPre p256 t₀ →
      RelCT isa (JointBoundary p256 s₀ t₀) Impl.Ecdsa.Verify.AArch64.P256Joint.points
        (AArch64.Taint.Agree (Taint.ofRegs [.x0])))
    (htail : FieldCT (Impl.Ecdsa.Verify.AArch64.Cfg.tail p256)) :
    ConstantTime isa (VPre p256) (JacPublic p256) Impl.Ecdsa.Verify.AArch64.P256Joint.verify := by
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
  have boundary : JointBoundary p256 s₁ s₂ a₁ a₂ := by
    refine ⟨pub,m₁,?_,sp⟩
    rw [base]; exact m₂
  obtain ⟨hq,tailpub⟩ := hpoints s₁ s₂ pre₁ pre₂ _ _ _ _ _ _ boundary eq₁ eq₂
  have hf := htail _ _ _ _ _ _ trivial trivial tailpub et₁ et₂
  rw [h₁,h₂,ht,hq,hf]

end VG.Proof.Ecdsa.Verify.AArch64
