module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointFrame
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointGenerator
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPublic
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.JointIfma
public import VerifiedGarbage.Proof.P256.X86_64.Ifma.JointChecks
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Proof.Weierstrass.CombW
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointInput
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdh.X86_64.Main
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMul
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointMulTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrep
import VerifiedGarbage.Proof.Weierstrass.TCombWords
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# ECDSA verification over P-256 on x86-64 with AVX512_IFMA: the points

`ifmaPoints`, the scalars' digits and then the joint multiplication with its
loop in vectors (`vwindow`), is `R = [u]G + [v]Q` from the verifier's scalars
(`ifmaPoints_ok`), and constant time between runs from the same public inputs
(`ifmaPoints_relCT`): the joint verifier with it meets what `jointVerifyWith`
needs of its points' code.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY BP)
open VG.Impl.Ecdsa.Verify.X86_64 (U V ifmaPoints)
open VG.Impl.P256.X86_64 (p256vx p256GTab jointDouble)
open VG.Impl.P256.X86_64.Ifma (publicJointIfma vwindow)
open VG.Proof.P256.X86_64.Ifma

/-- What `ifmaPoints` writes of the working space. -/
def ifmaRanges : List (Nat × Nat) := jointPrepRanges publicJointIfma ++ vRanges publicJointIfma

theorem ifma_frame_layout : FrameLayout p256vx ifmaRanges := by
  constructor
  · unfold VG.Proof.Ecdsa.X86_64.FixedOk
    decide +kernel
  · decide +kernel
  · decide +kernel

/-- `frame_input`, of what the joint multiplication with the loop in vectors leaves: it has `R`'s
coordinates reduced, and no table of `Q`'s multiples as words. -/
theorem frame_res (hc : BaseCfgOk p256vx) {W : List (Nat × Nat)} (hF : FrameLayout p256vx W)
    {s₀ s t : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid p256vx s₀ base g s) {A : Point p256vx.C}
    (ht : VRes publicJointIfma base size A t) (hu : Unch base W s.mem t.mem) :
    ProjectiveInput p256vx s₀ base g t := by
  refine ⟨ht.scr, h.fixed.unch hc.n10 h.scr.nowrap hF.fixed hu,
    (sv_unch hu hc.n10 h.scr.nowrap (by decide) hF.k).trans h.k, ?_, ht.x, ht.z⟩
  refine (hu.word hF.flag ?_).trans h.flag
  have := sl_le p256vx hc.n10 (i := FLAG) (by decide)
  have := hc.n0
  have := h.scr.nowrap
  omega_arith

section
variable (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (hI : InvSounds) (hO : PrimeOrder Spec.P256.curve)

/-- The generator's table, from what the calling convention gives of it. -/
theorem ifma_gtab {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre p256vx s₀)
    (h : Mid p256vx s₀ (s₀.gpr .rcx) g s) :
    GTab (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size s := by
  have hm : (p256GTab.tsym, p256vx.combWords p256GTab) ∈ p256vx.combConsts := gtab_mem_consts rfl
  have table := tbl_of_held_mem hm hp.tbls (by rw [hp.wr]; simp) (s := s)
    (fun r hr => by rw [h.rd, hp.rd]; simp [hr]) h.unch
  have len : (p256vx.combWords p256GTab).length = 2048 := by decide +kernel
  rw [len] at table
  obtain ⟨⟨hrd, -⟩, hout⟩ := table
  rw [len] at hrd
  obtain ⟨r, hr, hc⟩ := hrd
  refine ⟨⟨r, hr, ?_⟩, fun d hd => ?_⟩
  · have := Region.contains_off hc (d := 0) (n := 16320) (by omega_using [])
    rw [show s₀.syms p256GTab.tsym + BitVec.ofNat 64 0 = s₀.syms p256GTab.tsym from BitVec.add_zero _] at this
    exact this
  · have := hout (d / 8) (by omega_using [hd]) (d % 8) (by omega_using [])
    rw [Offset.add_add, show 8 * (d / 8) + d % 8 = d by omega_using []] at this
    exact this

include hL hT hI hO

/-- `R = [u]G + [v]Q` from the verifier's scalars, by the loop in vectors. -/
theorem ifmaPoints_ok {s₀ s : State} {g : Reg → BitVec 64} (hp : VPre p256vx s₀)
    (h : Mid p256vx s₀ (s₀.gpr .rcx) g s) {Q : Point p256vx.C} (hQ : onCurve p256vx.C Q = true)
    (hq : Rep p256vx.C (tmv p256vx.C p256vx.n (s₀.gpr .rcx) s (p256vx.sl PX))
      (tmv p256vx.C p256vx.n (s₀.gpr .rcx) s (p256vx.sl PY)) (tmv p256vx.C p256vx.n (s₀.gpr .rcx) s (p256vx.sl ONEP)) Q) :
    WP isa ifmaPoints.inline s (JointPointsPost p256vx s₀ s g Q) := by
  have hcc := p256vx_ok hI
  have hc := hcc.toBaseCfgOk
  have hG : JointGTable p256vx publicJointIfma p256GTab 1 := .ofGTab rfl hT (by decide) (by decide) rfl
  have hK : publicJointIfma.K = p256vx.winCfg PX PY BP := rfl
  have field := jointMid_field hc hK (by decide +kernel) h
  have point := jointMid_point hc hL hK h hq
  have zero := jointMid_zero hK h
  have generator := jointMid_generator hc hL hG hK hp h
  have hm : UnitMod p256vx.C.p (2 ^ (64 * publicJointIfma.K.M.n)) := unitMod_pow_two hc.p_odd _
  have hone : publicJointIfma.K.one < p256vx.C.p := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p256vx.C.p))
  have honeval : toM p256vx.C.p (2 ^ (64 * publicJointIfma.K.M.n)) publicJointIfma.K.one = 1 := by
    change toM p256vx.C.p (2 ^ (64 * p256vx.n)) (p256vx.mont 1) = 1
    simp only [Cfg.mont, Cfg.R, Nat.one_mul]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  have nlt : p256vx.C.n < 2 ^ (64 * publicJointIfma.K.M.n) := hc.n_lt
  have sv4 (i : Nat) : wordsVal s.mem (s₀.gpr .rcx) (p256vx.sl i) publicJointIfma.K.M.n =
      sv p256vx (s₀.gpr .rcx) s i := rfl
  have hTs := ifma_gtab hp h
  show WP isa (.seq (Joint.prep publicJointIfma (p256vx.sl U) (p256vx.sl V)).inline
    (vwindow publicJointIfma (jointDouble publicJointIfma.K)).inline) s _
  rw [jointPrep_inline]
  apply WP.seq
  refine WP.mono (jointMulPrep_ok joint_ifma_prep_layout joint_ifma_init_layout.naf.lay field point
    (jointMid_affine hc hK h) zero generator (sv4 U) (sv4 V)) fun a ⟨ia, pa, ka, ua⟩ => ?_
  have hTa : GTab (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size a := ⟨by rw [ka.rd, ka.wr]; exact hTs.1, hTs.2⟩
  refine WP.mono (vwindow_ok hL hO hcc.am3 joint_ifma_vlay joint_ifma_add_layout joint_ifma_init_layout rfl hm
    (hcc.jdbl hL) (joint_ifma_doubler hcc hL) hone honeval hc.onG hQ (fun _ => ⟨hO, by decide, hcc.am3⟩)
    (Nat.lt_trans h.u_lt nlt) (Nat.lt_trans h.v_lt nlt) (ia.to_tmv (C := p256vx.C)) pa hTa)
    fun t ⟨ct, _, _, _, ut⟩ => ?_
  exact ⟨frame_res hc ifma_frame_layout h ct (ua.trans ut), ct.point⟩

/-- The joint verifier with the loop in vectors meets the verifier's functional specification. -/
theorem jointVerify_p256_ifma_ok {s : State} (hp : VPre p256vx s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerifyWith p256vx ifmaPoints).inline s fun t =>
      (∀ r ∈ Cfg.saved.map Prod.fst, t.gpr r = s.gpr r) ∧ VPost p256vx s t := by
  have hc := p256vx_ok hI
  refine jointVerifyWith_ok hc.toBaseCfgOk hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact ifmaPoints_ok hL hT hI hO hp hM hQ hRep

/-- `ifmaPoints` leaks only the public verification inputs. -/
theorem ifmaPoints_relCT {s₀ t₀ : State} (ps : VPre p256vx s₀) (pt : VPre p256vx t₀)
    (pub : JointPublic p256vx p256GTab s₀ t₀) :
    RelCT isa (fun s t => (∃ g, Mid p256vx s₀ (s₀.gpr .rcx) g s) ∧ (∃ h, Mid p256vx t₀ (t₀.gpr .rcx) h t))
      ifmaPoints.inline (fun s t => X86_64.Taint.Agree (Taint.ofRegs [.rdi]) s t) := by
  intro s t ls lt s' t' ⟨⟨g, hs⟩, ⟨h, ht⟩⟩ es et
  have hcc := p256vx_ok hI
  have hc := hcc.toBaseCfgOk
  have hG : JointGTable p256vx publicJointIfma p256GTab 1 := .ofGTab rfl hT (by decide) (by decide) rfl
  have hK : publicJointIfma.K = p256vx.winCfg PX PY BP := rfl
  have base : s₀.gpr .rcx = t₀.gpr .rcx := pub.regs.rf.1 .rcx (by decide)
  have ht' : Mid p256vx t₀ (s₀.gpr .rcx) h t := by rw [base]; exact ht
  have fields := jointMid_field_pair hc hK (by decide +kernel) pub hs ht'
  have one := (consts_tmv hc hs.fixed).2.2
  let Q := peerPt p256vx (s₀.mem (s₀.gpr .rdi) = 4) (keyX p256vx s₀) (keyY p256vx s₀)
  have hQ : onCurve p256vx.C Q = true := peerPt_onCurve hc _ _ _
  have rep : Rep p256vx.C (tmv p256vx.C p256vx.n (s₀.gpr .rcx) s (p256vx.sl PX))
      (tmv p256vx.C p256vx.n (s₀.gpr .rcx) s (p256vx.sl PY))
      (tmv p256vx.C p256vx.n (s₀.gpr .rcx) s (p256vx.sl ONEP)) Q := by
    rw [one]
    exact peerPt_rep hL _ _ _ hs.px hs.py
  have point := jointMid_point hc hL hK hs rep
  have zero := jointMid_zero hK hs
  have genS := jointMid_generator hc hL hG hK ps hs
  have genT : JointGenerator publicJointIfma p256vx.C (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size
      (jointCombRow hc hL hG) t := by
    rw [base, pub.sym]
    exact jointMid_generator hc hL hG hK pt ht
  have hTs := ifma_gtab ps hs
  have hTt : GTab (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size t := by
    rw [base, pub.sym]
    exact ifma_gtab pt ht
  have hm : UnitMod p256vx.C.p (2 ^ (64 * publicJointIfma.K.M.n)) := unitMod_pow_two hc.p_odd _
  have hone : publicJointIfma.K.one < p256vx.C.p := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne p256vx.C.p))
  have honeval : toM p256vx.C.p (2 ^ (64 * publicJointIfma.K.M.n)) publicJointIfma.K.one = 1 := by
    change toM p256vx.C.p (2 ^ (64 * p256vx.n)) (p256vx.mont 1) = 1
    simp only [Cfg.mont, Cfg.R, Nat.one_mul]
    exact toM_one (unitMod_pow_two hc.p_odd _)
  have nlt : p256vx.C.n < 2 ^ (64 * publicJointIfma.K.M.n) := hc.n_lt
  have sv4 (a : State) (i : Nat) : wordsVal a.mem (s₀.gpr .rcx) (p256vx.sl i) publicJointIfma.K.M.n =
      sv p256vx (s₀.gpr .rcx) a i := rfl
  have u : sv p256vx (s₀.gpr .rcx) t U = sv p256vx (s₀.gpr .rcx) s U :=
    (mid_publicU ht').trans (pub.u.symm.trans (mid_publicU hs).symm)
  have v : sv p256vx (s₀.gpr .rcx) t V = sv p256vx (s₀.gpr .rcx) s V :=
    (mid_publicV ht').trans (pub.v.symm.trans (mid_publicV hs).symm)
  have checks := joint_ifma_mul_checks
  -- The scalars' digits, with the generator's table.
  have prep := (jointMulPrep_relCT (base := s₀.gpr .rcx) (T := s₀.syms p256GTab.tsym)
    (row := jointCombRow hc hL hG) (u := sv p256vx (s₀.gpr .rcx) s U) (v := sv p256vx (s₀.gpr .rcx) s V)
    joint_ifma_prep_layout joint_ifma_init_layout.naf.lay point (jointMid_affine hc hK hs) zero checks.prepG
    checks.prepQ).mono
    (P' := fun (a b : State) => (FieldPair publicJointIfma.K.M (s₀.gpr .rcx) size p256vx.C.p
        (· ∈ nafSlots publicJointIfma.K) (winRo publicJointIfma.K)
        (tmv p256vx.C publicJointIfma.K.M.n (s₀.gpr .rcx) s) a b ∧
      JointGenerator publicJointIfma p256vx.C (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size (jointCombRow hc hL hG) a ∧
      JointGenerator publicJointIfma p256vx.C (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size (jointCombRow hc hL hG) b ∧
      wordsVal a.mem (s₀.gpr .rcx) (p256vx.sl U) publicJointIfma.K.M.n = sv p256vx (s₀.gpr .rcx) s U ∧
      wordsVal a.mem (s₀.gpr .rcx) (p256vx.sl V) publicJointIfma.K.M.n = sv p256vx (s₀.gpr .rcx) s V ∧
      wordsVal b.mem (s₀.gpr .rcx) (p256vx.sl U) publicJointIfma.K.M.n = sv p256vx (s₀.gpr .rcx) s U ∧
      wordsVal b.mem (s₀.gpr .rcx) (p256vx.sl V) publicJointIfma.K.M.n = sv p256vx (s₀.gpr .rcx) s V) ∧
      GTab (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size a ∧ GTab (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size b)
    (fun _ _ h => h.1) (fun _ _ h => h)
  have prep' := prep.wp (F₁ := GTab (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size)
    (F₂ := GTab (s₀.gpr .rcx) (s₀.syms p256GTab.tsym) size)
    (fun a b ⟨⟨p, ga, gb, au, av, bu, bv⟩, ta, tb⟩ =>
      ⟨WP.mono (jointMulPrep_ok joint_ifma_prep_layout joint_ifma_init_layout.naf.lay p.1 point
          (jointMid_affine hc hK hs) zero ga au av)
        (fun x ⟨_, _, kx, _⟩ => ⟨by rw [kx.rd, kx.wr]; exact ta.1, ta.2⟩),
       WP.mono (jointMulPrep_ok joint_ifma_prep_layout joint_ifma_init_layout.naf.lay p.2 point
          (jointMid_affine hc hK hs) zero gb bu bv)
        (fun x ⟨_, _, kx, _⟩ => ⟨by rw [kx.rd, kx.wr]; exact tb.1, tb.2⟩)⟩)
  have win := vwindow_relCT (base := s₀.gpr .rcx) (T := s₀.syms p256GTab.tsym) (row := jointCombRow hc hL hG)
    (double := jointDouble publicJointIfma.K) (E₀ := tmv p256vx.C publicJointIfma.K.M.n (s₀.gpr .rcx) s)
    hL hO hcc.am3 joint_ifma_vchecks joint_ifma_vlay joint_ifma_add_layout joint_ifma_init_layout rfl hm (hcc.jdbl hL)
    (joint_ifma_doubler hcc hL) hone honeval hc.onG hQ (fun _ => ⟨hO, by decide, hcc.am3⟩) checks.cached
    checks.fixed checks.table checks.cache checks.seed checks.counter joint_ifma_zero_ct
    (Nat.lt_trans hs.u_lt nlt) (Nat.lt_trans hs.v_lt nlt)
  have ct : RelCT isa _ (.seq (Joint.prep publicJointIfma (p256vx.sl U) (p256vx.sl V))
      (vwindow publicJointIfma (jointDouble publicJointIfma.K)).inline) _ :=
    RelCT.seq (prep'.mono (fun _ _ h => h) (fun _ _ ⟨⟨p, wa, wb⟩, ta, tb⟩ => ⟨p, ⟨wa, ta⟩, wb, tb⟩)) win
  have es' : Exec isa (.seq (Joint.prep publicJointIfma (p256vx.sl U) (p256vx.sl V))
      (vwindow publicJointIfma (jointDouble publicJointIfma.K)).inline) s ls s' := by
    rw [← jointPrep_inline]; exact es
  have et' : Exec isa (.seq (Joint.prep publicJointIfma (p256vx.sl U) (p256vx.sl V))
      (vwindow publicJointIfma (jointDouble publicJointIfma.K)).inline) t lt t' := by
    rw [← jointPrep_inline]; exact et
  obtain ⟨trace, post⟩ := ct _ _ _ _ _ _
    ⟨⟨fields, genS, genT, sv4 s U, sv4 s V, (sv4 t U).trans u, (sv4 t V).trans v⟩, hTs, hTt⟩ es' et'
  refine ⟨trace, Taint.agree_ofRegs fun r hr => ?_⟩
  rw [List.mem_singleton] at hr; subst hr
  exact post.1.trans post.2.symm

/-- The joint verifier with the loop in vectors is constant time between runs from the same public
inputs. -/
theorem jointVerify_p256_ifma_public_ct :
    ConstantTime isa (VPre p256vx) (JointPublic p256vx p256GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerifyWith p256vx ifmaPoints).inline := by
  have hc := p256vx_ok hI
  refine jointVerifyWith_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact ifmaPoints_relCT hL hT hI hO ps pt pub

end

end VG.Proof.Ecdsa.Verify.X86_64
