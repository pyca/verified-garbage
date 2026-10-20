module

public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallLayout
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignArgs
import VerifiedGarbage.Proof.Dsa.AArch64.Run
import VerifiedGarbage.Proof.Framework.Contract

/-! Map the wrapper's saved arguments to the supplied-nonce signing ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

theorem random_saved_outgoing {s : State} {m : Mem} (h : RandomSaved s m) :
    ∀ i < 3, word (randomSlotsMem (randomBase s) m randomSignOutgoing) (randomBase s) (8 * i) = randomCallArg s i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · exact (random_signOutgoing_words m _ (104, 0) (by decide)).trans
      (h (104, stackArg s 0) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (128, 8) (by decide)).trans
      (h (128, stackArg s 3) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (136, 16) (by decide)).trans
      (h (136, stackArg s 4) (by simp [randomSavedValues]))

theorem random_callArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.sp = randomBase s) (hv : RandomSaved s t.mem) :
    WP isa (.block RandomSign.callArgs) t fun u =>
      u.gpr .x0 = s.gpr .x0 ∧ u.gpr .x1 = s.gpr .x1 ∧
      u.gpr .x2 = s.gpr .x3 ∧ u.gpr .x3 = s.gpr .x4 ∧
      u.gpr .x4 = s.gpr .x5 ∧ u.gpr .x5 = off (randomBase s) Random.oNonce ∧
      u.gpr .x6 = s.gpr .x6 ∧ u.gpr .x7 = s.gpr .x7 ∧
      (∀ i < 3, word u.mem (randomBase s) (8 * i) = randomCallArg s i) ∧
      RandomSaved s u.mem ∧ Outside (randomBase s) 0 40 t.mem u.mem ∧
      Keep [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x15] t u := by
  refine WP.mono (random_signCallArgs_ok hs hsp) fun u ⟨h0, h1, h2, h3, h4, h5, h6, h7, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 40 t.mem u.mem := by rw [hm]; exact random_signOutgoing_frame _ _
  exact ⟨h0.trans (hv (40, s.gpr .x0) (by simp [randomSavedValues])),
    h1.trans (hv (48, s.gpr .x1) (by simp [randomSavedValues])),
    h2.trans (hv (64, s.gpr .x3) (by simp [randomSavedValues])),
    h3.trans (hv (72, s.gpr .x4) (by simp [randomSavedValues])),
    h4.trans (hv (80, s.gpr .x5) (by simp [randomSavedValues])), h5,
    h6.trans (hv (88, s.gpr .x6) (by simp [randomSavedValues])),
    h7.trans (hv (96, s.gpr .x7) (by simp [randomSavedValues])),
    fun i hi => by rw [hm]; exact random_saved_outgoing hv i hi,
    hv.congr (fun d hd hd' => hf.word (Or.inr hd) (by omega)), hf, hk⟩

end VG.Proof.Dsa.AArch64
