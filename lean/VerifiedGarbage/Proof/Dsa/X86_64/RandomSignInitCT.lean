module

import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareCT
public import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInputs
import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignEnv
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomPrepareCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignInputs
meta import VerifiedGarbage.Proof.Dsa.X86_64.RandomSignSaved
meta import VerifiedGarbage.Proof.Bignum.Octets

/-! Saving arguments and preparing q leaks no private key or random-tape bytes. -/
@[expose] public section
namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Dsa.X86_64

def RandomSignInitPre (p : RandomPreparePublic) (t : State) : Prop :=
  ∃ s extra, RandomSignABI extra s ∧ t = allocState Random.frameBytes s ∧
    p = ⟨randomBase s, s.gpr .rcx + s.gpr .r9, randomQBytes s⟩

private theorem entry_prepare {p : RandomPreparePublic} {t : State} (hp : RandomSignInitPre p t) :
    WP isa (.block RandomSign.entry) t (RandomPreparePre p) := by
  obtain ⟨s, extra, h, rfl, rfl⟩ := hp
  have hsp : (allocState Random.frameBytes s).gpr .rsp = randomBase s := rfl
  refine WP.mono (random_entry_ok (random_alloc_scr h) hsp (random_incoming_read h))
    fun u ⟨hum, hk⟩ => ?_
  have hsaved : RandomSaved s u.mem := by rw [hum]; exact random_saved_entry s
  have hf : InScr (randomBase s) Random.frameBytes (allocState Random.frameBytes s).mem u.mem := by
    rw [hum]; exact InScr.of_outside (random_entry_outside _ _) (by decide)
  have hv (p : Nat × BitVec 64) (hp : p ∈ randomEntryValues (allocState Random.frameBytes s) (randomBase s)) :
      word u.mem (randomBase s) p.1 = p.2 := by
    rw [hum]; exact random_entry_values _ _ p hp
  have hqu : word u.mem (randomBase s) Random.oQ = s.gpr .rcx + s.gpr .r9 :=
    hv (168, s.gpr .rcx + s.gpr .r9) (by simp [randomEntryValues, allocState, State.setReg])
  have hql : word u.mem (randomBase s) Random.oQLen = BitVec.ofNat 64 (randomQBytes s).length := by
    simpa only [Random.oQLen, random_q_length h, ofNat_toNat64] using
      hsaved (88, stackArg s 0) (by simp [randomSavedValues])
  refine ⟨(random_alloc_scr h).congr hk.2.2, (hk.gpr (by decide)).trans hsp,
    hqu, hql, (random_initial_q h).congrK hf hk, ?_, ?_⟩
  · change 0 < (randomQBytes s).length
    rw [random_q_length h]
    have hl := h.lengths
    unfold Spec.Dsa.lengthsValid at hl
    omega
  · change (randomQBytes s).length < 2 ^ 64
    rw [random_q_length h]
    exact (stackArg s 0).isLt

theorem random_sign_init_ct : RelCT isa (Two RandomSignInitPre)
    (.seq (.block RandomSign.entry) Random.prepare) (fun _ _ => True) := by
  refine RelCT.seq (two_piece (Ψ := RandomPreparePre) [.rsp] ?_ (by taint_decide)
    (fun _ _ h => entry_prepare h)) random_prepare_ct
  intro p s t hs ht r hr
  rw [List.mem_singleton] at hr
  subst r
  obtain ⟨a, _, _, rfl, hpa⟩ := hs
  obtain ⟨b, _, _, rfl, hpb⟩ := ht
  change randomBase a = randomBase b
  exact (congrArg RandomPreparePublic.B hpa).symm.trans (congrArg RandomPreparePublic.B hpb)

end VG.Proof.Dsa.X86_64
