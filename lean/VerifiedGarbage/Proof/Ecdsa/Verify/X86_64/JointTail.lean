import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointSquare
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.VerifyJacobian

/-! The measured Jacobian denominator square and projective check satisfy verification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 Spec.Weierstrass
open VG.Impl.Ecdsa.Verify.X86_64 (U V)

theorem jointTail_ok {c : Cfg} (hc : CfgOk c) (hC : Law c.C) (hn : c.n=4)
    (hpub : c.pubVerify=true) (hnp : c.C.n<c.C.p) (hpn : c.C.p≤2*c.C.n)
    {s₀ sM s : State} {g : Reg → BitVec 64} (hM : Mid c s₀ (s₀.gpr .rcx) g sM)
    (hInput : ProjectiveInput c s₀ (s₀.gpr .rcx) g s)
    (hR : InvJ c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RX))
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ))
      (add (mul (sv c (s₀.gpr .rcx) sM U) (G c.C))
        (mul (sv c (s₀.gpr .rcx) sM V) (peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀))))) :
    WP isa (.seq (ForwardField.programB c.MP' [.mul (c.sl RZ) (c.sl RZ) (c.sl RZ)])
      (Impl.Ecdsa.Verify.X86_64.Cfg.tail c)) s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=g r) ∧ VPost c s₀ t := by
  have hpR := unitMod_pow_two hc.p_odd (64*c.n)
  apply WP.seq
  refine WP.mono (jointSquare_ok hc hn hInput) fun a ⟨ha,ax,az⟩ => ?_
  rw [Impl.Ecdsa.Verify.X86_64.Cfg.tail,ite_eq_left (show c.pubVerify=true ∧ c.C.n<c.C.p ∧ c.C.p≤2*c.C.n from ⟨hpub,hnp,hpn⟩)]
  refine WP.mono (projectiveFinal_fields_ok hc hC hnp hpn ha) fun t ⟨saved,xo,hxo,hx,rax⟩ => ⟨saved,?_⟩
  rw [ax,az] at hx
  let P := peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀)
  -- The arguments as the specification reads them.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).head? = some (s₀.mem (s₀.gpr .rdi)) := by
    rw [peer_bytes]; rfl
  have hxv : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      keyX c s₀ := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _)]
  have hyv : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdi) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      keyY c s₀ := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdi)) (keyX c s₀) (keyY c s₀),
      P = .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    show peerPt c _ _ _ = _
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have h16 : 2 * c.C.len = c.C.len + c.C.len := by omega
  have hr : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (2 * c.C.len)).take c.C.len) = sigR c s₀ := by
    rw [h16, bytesAt_add, List.take_left' (length_bytesAt _ _ _)]
  have hs : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (s₀.gpr .rdx) (2 * c.C.len)).drop c.C.len) = sigS c s₀ := by
    rw [h16, bytesAt_add, List.drop_left' (length_bytesAt _ _ _)]
  have hspec := Proof.Ecdsa.verify_eq_jacobian hC hlen hb0 hxv hyv hP' hr hs hM.u_lt hM.v_lt hM.u hM.v hR hxo hx
  -- The conditions.
  have hz : (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)*tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)≠0) ↔
      sv c (s₀.gpr .rcx) a RZ≠0 := by
    rw [←az]
    exact not_congr (toM_eq_zero_iff hpR ha.rz_lt)
  have hiff : (Ecdh.Valid c.C (s₀.mem (s₀.gpr .rdi)) (keyX c s₀) (keyY c s₀) ∧
      (1 ≤ sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (1 ≤ sigS c s₀ ∧ sigS c s₀ < c.C.n) ∧
      (tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)*tmv c.C c.n (s₀.gpr .rcx) s (c.sl RZ)) ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) ↔
      ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
        sv c (s₀.gpr .rcx) a RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)) := by
    constructor
    · rintro ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hZ, he⟩
      exact ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hz.mp hZ, he⟩
    · rintro ⟨⟨⟨⟨⟨h4, hx⟩, hy⟩, hcv⟩, hr, hs⟩, hZ, he⟩
      exact ⟨⟨h4, hx, hy, hcv⟩, hr, hs, hz.mpr hZ, he⟩
  unfold VPost
  rw [hashToInt_eq c, hspec, rax]
  by_cases h : (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧
      sv c (s₀.gpr .rcx) a RZ ≠ 0 ∧ Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀)
  · rw [ite_eq_left (decide_eq_true (hiff.mpr h)), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp (of_decide_eq_true h'))), ite_eq_right h]

end VG.Proof.Ecdsa.Verify.X86_64
