import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Joint
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacAddTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedInput
import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.Allocated

/-! ## `JointMain` -/

section

/-! The Jacobian verifier satisfies the existing complete verification postcondition. -/
namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V)

variable {c : Cfg}

/-- Any proven joint multiplication can feed the unchanged verifier prefix and final check. -/
theorem verify_of_joint (hc : CfgOk c) (hC : Law c.C) (points program : Prog isa)
    (heq : program =
      .seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.args c)) (.seq (.seq (.block (c.setupWith (some D)))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8*c.n)) (.block [])))
      (.seq (.block (Impl.Ecdsa.Verify.AArch64.Cfg.loadS c)) (.seq (.block (Impl.Ecdh.AArch64.Cfg.peer c))
      (.seq (Impl.Ecdh.AArch64.Cfg.validate c) (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c)
      (.seq c.nPow (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c)
      (.seq points (Impl.Ecdsa.Verify.AArch64.Cfg.tail c))))))))))
    (hpoints : ∀ {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State},
      Mid c s₀ base g s → TblPre c s₀ (s₀.syms c.tsym) base →
      ∀ {P : Point c.C},onCurve c.C P=true →
      Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
        (tmv c.C c.n base s (c.sl ONEP)) P →
      WP isa points s fun t => FinalState c s₀ base g t ∧
        Rep c.C (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY))
          (tmv c.C c.n base t (c.sl RZ))
          (add (mul (sv c base s U) (G c.C)) (mul (sv c base s V) P)))
    {s₀ : State} (hp : VPre c s₀) :
    WP isa program s₀ fun s' =>
      (∀ r∈Cfg.saved.map Prod.fst,s'.gpr r=s₀.gpr r) ∧ VPost c s₀ s' := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  rw [heq]
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have F₂ := hM.fixed
  have h1 := onep_tmv hc F₂
  -- The point the window method multiplies.
  let P := peerPt c (s₀.mem (s₀.gpr .x0) = 4) (keyX c s₀) (keyY c s₀)
  have hPc : onCurve c.C P = true := peerPt_onCurve hc _ _ _
  have hQ : Rep c.C (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PX)) (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl PY))
      (tmv c.C c.n (s₀.gpr .x3) s₂ (c.sl ONEP)) P := by
    rw [h1]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  refine WP.seq (WP.mono (hpoints hM hp.tbl hPc hQ) fun s₃ ⟨hP,hR⟩ => ?_)
  refine WP.mono (tail_dispatch_ok hc hC hP) fun s' ⟨saved,xo,hxo,hx,ret⟩ =>
    ⟨fun r hr => (saved r hr).trans (hg r hr),?_⟩
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .x0)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x0) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .x2) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz := not_congr (toM_eq_zero_iff hpR hP.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .x0)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      tmv c.C c.n (s₀.gpr .x3) s₃ (c.sl RZ) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, ret]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .x3) s₃ RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointPrefix` -/

section

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

end

/-! ## `AllocatedPrefix` -/

section

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

end
