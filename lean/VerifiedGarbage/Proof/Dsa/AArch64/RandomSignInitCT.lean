module

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInputs
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignEnv
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInputs
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSaved
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! Saving arguments and preparing q leaks no private key or random-tape bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64

def RandomSignInitPre (p : RandomPreparePublic) (t : State) : Prop :=
  ∃ s extra, RandomSignABI extra s ∧ t = allocated Random.frameBytes s ∧
    p = ⟨randomBase s, s.gpr .x3 + s.gpr .x5, randomQBytes s⟩

private theorem entry_prepare {p : RandomPreparePublic} {t : State} (hp : RandomSignInitPre p t) :
    WP isa (.block RandomSign.entry) t (RandomPreparePre p) := by
  obtain ⟨s, extra, h, rfl, rfl⟩ := hp
  have hsp : (allocated Random.frameBytes s).sp = randomBase s := rfl
  refine WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
    fun u ⟨hum, hk⟩ => ?_
  have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
  have hf : InScr (randomBase s) Random.frameBytes (allocated Random.frameBytes s).mem u.mem := by
    rw [hum]; exact InScr.of_outside (random_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocated Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact random_entry_values _ _ p hp
  have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .x3 + s.gpr .x5 :=
    hv (168, s.gpr .x3 + s.gpr .x5) (by simp [randomEntryValues, allocated])
  have hql : word u.mem (randomBase s) Random.oQLen = BitVec.ofNat 64 (randomQBytes s).length := by
    simpa only [Random.oQLen, random_q_length h, ofNat_toNat64] using
      hsaved (88, s.gpr .x6) (by simp [randomSavedValues])
  refine ⟨(random_alloc_scr h).congr hk.wr, hk.sp.trans hsp,
    hqu, hql, (random_initial_q h).congrK hf hk, ?_, ?_⟩
  · change 0 < (randomQBytes s).length
    rw [random_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  · change (randomQBytes s).length < 2 ^ 64
    rw [random_q_length h]
    exact (s.gpr .x6).isLt

theorem random_sign_init_ct : RelCT isa (Two RandomSignInitPre)
    (.seq (.block RandomSign.entry) Random.prepare) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := RandomPreparePre) [] ?_ (by taint_decide)
    (fun _ _ h => entry_prepare h)) random_prepare_ct
  intro _ _ _ _ _ _ h; cases h

end VG.Proof.Dsa.AArch64
