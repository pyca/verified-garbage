module

public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignCallLayout
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignArgs
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel

/-! Map the wrapper's saved arguments to the supplied-nonce signing ABI. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

theorem random_saved_outgoing {s : State} {m : Mem} (h : RandomSaved s m) :
    ∀ i < 5, word (randomSlotsMem (randomBase s) m randomSignOutgoing) (randomBase s) (8 * i) = randomCallArg s i := by
  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact (random_signOutgoing_words m _ (88, 0) (by decide)).trans
      (h (88, stackArg s 0) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (96, 8) (by decide)).trans
      (h (96, stackArg s 1) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (104, 16) (by decide)).trans
      (h (104, stackArg s 2) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (128, 24) (by decide)).trans
      (h (128, stackArg s 5) (by simp [randomSavedValues]))
  · exact (random_signOutgoing_words m _ (136, 32) (by decide)).trans
      (h (136, stackArg s 6) (by simp [randomSavedValues]))

theorem random_callArgs_saved {s t : State} (hs : Scr t (randomBase s) Random.frameBytes)
    (hsp : t.gpr .rsp = randomBase s) (hv : RandomSaved s t.mem) :
    WP isa (.block RandomSign.callArgs) t fun u =>
      u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rsi = s.gpr .rsi ∧
      u.gpr .rdx = s.gpr .rcx ∧ u.gpr .rcx = s.gpr .r8 ∧
      u.gpr .r8 = s.gpr .r9 ∧ u.gpr .r9 = off (randomBase s) Random.oNonce ∧
      (∀ i < 5, word u.mem (randomBase s) (8 * i) = randomCallArg s i) ∧
      RandomSaved s u.mem ∧ Outside (randomBase s) 0 40 t.mem u.mem ∧
      Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9] t u := by
  refine WP.mono (random_signCallArgs_ok hs hsp) fun u ⟨hdi, hsi, hdx, hcx, h8, h9, hm, hk⟩ => ?_
  have hf : Outside (randomBase s) 0 40 t.mem u.mem := by rw [hm]; exact random_signOutgoing_frame _ _
  exact ⟨hdi.trans (hv (40, s.gpr .rdi) (by simp [randomSavedValues])),
    hsi.trans (hv (48, s.gpr .rsi) (by simp [randomSavedValues])),
    hdx.trans (hv (64, s.gpr .rcx) (by simp [randomSavedValues])),
    hcx.trans (hv (72, s.gpr .r8) (by simp [randomSavedValues])),
    h8.trans (hv (80, s.gpr .r9) (by simp [randomSavedValues])), h9,
    fun i hi => by rw [hm]; exact random_saved_outgoing hv i hi,
    hv.congr (fun d hd hd' => hf.word (Or.inr hd) (by omega)), hf, hk⟩

end VG.Proof.Dsa.X86_64
