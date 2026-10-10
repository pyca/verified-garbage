import VerifiedGarbage.Proof.Ed448.AArch64.Point56.CombStep
import VerifiedGarbage.Proof.Ed448.AArch64.Point56.Verified

/-!
# `vg_ed448_r56_comb_add` on AArch64, verified

The function meets `combAddContract` of `Spec/Ed448/Point56.lean`, with no
stack: the proof against `combF`, from `combAddFn_ok`. The sums are `affPt`
of each point with `(x : y : 1)` (`affEnv_A`, `affEnv_B`; the first addition
keeps what the second reads, `affEnv_keep`), which is `pointAdd`
(`affPt_eq`, `addPt_eq`), and the bytes kept are those no store covers
(`keeps_of_unstored`). Constant time by taint tracking: only the pointer, in
`x0`, is public, and every address is `ws` plus a constant.
-/

namespace VG.Proof.Ed448.AArch64.Point56

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Impl.X448.AArch64 (slot)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.X448.AArch64.Fast (BEnv Bnd fclob)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448.AArch64.Base (pt affEnv affPt_eq)
open VG.Spec.X448.Field56 (slotAt elemAt Bounded Res)
open VG.Spec.Ed448.Point56 (pointAt affineAt combWritten)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

def combF : Contract AArch64.isa where
  pre s := fPre s ∧ Bounded s.mem (s.gpr .x0) ∧ Res s.mem (s.gpr .x0) 19 ∧
    elemAt s.mem (s.gpr .x0) (slotAt 19) = 0
  post s s' := Bounded s'.mem (s.gpr .x0) ∧ (∀ n < 6, Res s'.mem (s.gpr .x0) n) ∧
    pointAt s'.mem (s.gpr .x0) 0 = Spec.Ed448.pointAdd (pointAt s.mem (s.gpr .x0) 0) (affineAt s.mem (s.gpr .x0) 6) ∧
    pointAt s'.mem (s.gpr .x0) 3 = Spec.Ed448.pointAdd (pointAt s.mem (s.gpr .x0) 3) (affineAt s.mem (s.gpr .x0) 8) ∧
    Spec.X448.Field56.Keeps (s.gpr .x0) combWritten s.mem s'.mem
  pub := fPub

theorem pointAt_eqN (m : Mem) (ws : Addr) (n : Nat) (x y z : Index) (hx : x.val = n) (hy : y.val = n + 1)
    (hz : z.val = n + 2) : pointAt m ws n = pt (EV m ws) x y z := by
  simp only [pointAt, pt]
  subst hx; rw [← hy, ← hz, elemAt_eq, elemAt_eq, elemAt_eq]

theorem affineAt_eq (m : Mem) (ws : Addr) (n : Nat) (x y : Index) (hx : x.val = n) (hy : y.val = n + 1) :
    affineAt m ws n = ⟨EV m ws x, EV m ws y, 1⟩ := by
  simp only [affineAt]
  subst hx; rw [← hy, elemAt_eq, elemAt_eq]

theorem fnOk_combWritten : ∀ d, fnOk d = true → d + 8 ≤ 8192 ∧ ∃ r ∈ combWritten, r.1 ≤ d ∧ d + 8 ≤ r.2 := by
  intro d hd
  simp only [fnOk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hd
  simp only [combWritten, Spec.X448.Field56.own, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, slotAt, Spec.X448.Field56.accAt, Spec.X448.Field56.accEnd]
  omega

theorem comb_arm (s : State) (hs : combF.pre s) :
    ∃ t s', Exec isa Point56.combAddFn s t s' ∧ abiPreserved s s' ∧ combF.post s s' := by
  obtain ⟨hp, hb, hr, hz⟩ := hs
  have hz' : EV s.mem (s.gpr .x0) 19 = 0 := by rw [← hz]; exact (elemAt_eq _ _ 19).symm
  obtain ⟨t, u, he, hpost, hv⟩ := combAddFn_ok (fnPre_of hp hb) hr
  obtain ⟨b, -, hres, e, hf⟩ := hpost.2.2.2.2.2.2
  obtain ⟨hg, hsp⟩ := abi_of hpost (by decide)
  refine ⟨t, u, he, ⟨hg, hsp, hv⟩, (bounded_iff _ _).mpr b,
    fun n hn => hres ⟨n, by omega⟩ hn, ?_, ?_, keeps_of_unstored fnOk_combWritten hf⟩
  · rw [pointAt_eqN _ _ 0 0 1 2 rfl rfl rfl, pointAt_eqN _ _ 0 0 1 2 rfl rfl rfl, affineAt_eq _ _ 6 6 7 rfl rfl, e]
    simp only [pt]
    rw [affEnv_keep _ _ _ _ _ _ 0 (by decide), affEnv_keep _ _ _ _ _ _ 1 (by decide),
      affEnv_keep _ _ _ _ _ _ 2 (by decide)]
    rw [show (⟨affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0)) 0, affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0)) 1,
        affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0)) 2⟩ : Spec.Ed448.Point) =
        pt (affEnv 0 1 2 6 7 (EV s.mem (s.gpr .x0))) 0 1 2 from rfl,
      VG.Proof.X448.AArch64.Base.affEnv_A, hz', affPt_eq, VG.Proof.X448.addPt_eq]
  · rw [pointAt_eqN _ _ 3 3 4 5 rfl rfl rfl, pointAt_eqN _ _ 3 3 4 5 rfl rfl rfl, affineAt_eq _ _ 8 8 9 rfl rfl, e,
      VG.Proof.X448.AArch64.Base.affEnv_B,
      affEnv_keep _ _ _ _ _ _ 3 (by decide), affEnv_keep _ _ _ _ _ _ 4 (by decide),
      affEnv_keep _ _ _ _ _ _ 5 (by decide), affEnv_keep _ _ _ _ _ _ 8 (by decide),
      affEnv_keep _ _ _ _ _ _ 9 (by decide), affEnv_keep _ _ _ _ _ _ 19 (by decide), hz', affPt_eq,
      VG.Proof.X448.addPt_eq]
    rfl

theorem comb_ct : ConstantTime isa combF.pre combF.pub Point56.combAddFn :=
  VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => ⟨hp.2, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst hr; exact hp.1⟩) (by taint_decide)

theorem combAddFn_verified :
    Verified AArch64.target Point56.combAddFn (Spec.Ed448.Point56.combAddContract AArch64.abi) :=
  Verified.of_correct comb_arm comb_ct
    { pre := by sig_implies_pre [Spec.Ed448.Point56.combAddContract, Spec.Ed448.Point56.sig,
        Spec.Ed448.Point56.zeroSlot, combF, fPre, fPub, AArch64.abi, AArch64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.Ed448.Point56.combAddContract, Spec.Ed448.Point56.sig, Spec.Ed448.Point56.zeroSlot,
          combF, fPre, fPub, AArch64.abi, AArch64.argRegs]
        exact h
      pub := by sig_implies_pub [Spec.Ed448.Point56.combAddContract, Spec.Ed448.Point56.sig,
        Spec.Ed448.Point56.zeroSlot, combF, fPre, fPub, AArch64.abi, AArch64.argRegs]
      sat := ⟨satState, by
        unfold Spec.Ed448.Point56.combAddContract
        exact Sig.contract_pre_of_check (by decide +kernel) (by
          sig_reduce [Sig.wfPre, Spec.Ed448.Point56.sig, Spec.Ed448.Point56.zeroSlot, AArch64.abi,
            AArch64.argRegs, satState]
          exact ⟨by decide, sat_bounded, sat_res 19 (by decide), sat_zero⟩)⟩ }

end VG.Proof.Ed448.AArch64.Point56
