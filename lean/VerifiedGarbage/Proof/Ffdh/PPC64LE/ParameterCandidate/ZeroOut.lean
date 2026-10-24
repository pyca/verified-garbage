module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.Base
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset

/-!
# An FFDH parameter candidate on PPC64LE: `out` zeroed

`zeroOut_ok`: `out`'s `k` bytes := 0, nothing else in memory changed.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.ParameterCandidate

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.PPC64LE

theorem zeroOut_ok {s : State} {B O : Addr} {Z k : Nat} (hs : Scr s B Z) (ho : Scr s O k)
    (h31 : s.gpr .r31 = B)
    (hO : s.mem.readW (B + BitVec.ofNat 64 16) 64 = O) (hL : s.mem.readW (B + BitVec.ofNat 64 24) 64 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hk' : k < 2 ^ 63) (hZ : 32 ≤ Z) :
    WP isa zeroOut s fun t =>
      ((∀ i < k, t.mem (off O i) = 0) ∧ Outside O 0 k s.mem t.mem) ∧ Keep [.r0, .r4, .r5] s t := by
  have hno := ho.nowrap
  unfold zeroOut
  refine WP.seq ?_
  refine WP.mono (WP.keep [.r0, .r4, .r5] (Q := fun s₂ => s₂.gpr .r4 = O ∧ s₂.gpr .r5 = BitVec.ofNat 64 k ∧
    s₂.gpr .r0 = BitVec.ofNat 64 0 ∧ s₂.mem = s.mem)
    (by simp only [Impl.MillerRabin.PPC64LE.Search.ldh, hOut, hLen]
        prun [h31, hO, hL, hs.ld (d := 16) (n := 8) (by omega_arith), hs.ld (d := 24) (n := 8) (by omega_arith)])
    (by decide)) fun s₂ ⟨⟨b4, b5, b0, m2⟩, k2⟩ => ?_
  let Inv : Nat → State → Prop := fun j t =>
    t.gpr .r4 = off O j ∧ t.gpr .r0 = BitVec.ofNat 64 0 ∧ Outside O 0 j s.mem t.mem ∧
      (∀ i < j, t.mem (off O i) = 0) ∧ Keep [.r0, .r4, .r5] s t
  refine WP.mono (wp_countdown (body := .block ([.stb .r0 .r4 0, .addi .r4 .r4 1] ++
      ([.subi .r5 .r5 1] : List Instr)))
    (cnt := .r5) (N := k) (by omega_arith) (by omega_arith) Inv (fun j hj t ⟨t4, t0, tout, tb, tk⟩ hc => ?_)
    ⟨by rw [b4]; simp [off], b0, by rw [m2]; exact Outside.refl _ _ _ _, fun _ h => absurd h (by omega_arith),
      k2⟩ b5) fun t ⟨_, _, tout, tb, tk⟩ => ⟨⟨tb, tout⟩, tk⟩
  have hst : WP isa (.block [.stb .r0 .r4 0, .addi .r4 .r4 1, .subi .r5 .r5 1]) t fun t' =>
      t' = (({ t with mem := t.mem.write (off O j) 1 ((BitVec.ofNat 64 0).setWidth 8) } :
          State).write .r4 (off O (j + 1))).write .r5 (t.gpr .r5 - BitVec.ofNat 64 1) := by
    prun [t4, t0, exec_stb (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
      (ho.congr tk.wr).st (d := j) (n := 1) (by omega_arith)]
  refine WP.mono hst fun t' e => ?_
  subst e
  have hw1 := write1_outside t.mem O (d := j) ((BitVec.ofNat 64 0).setWidth 8) (by omega_arith)
  refine ⟨⟨by gsimp, by gsimp; exact t0, ?_, ?_, ?_⟩, by gsimp⟩
  · gsimp; exact (tout.mono (Nat.le_refl _) (by omega_arith)).trans (hw1.mono (by omega_arith) (by omega_arith))
  · intro i hi
    gsimp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hw1 _ (by rw [ofs_off0 O (by omega_arith)]; omega_arith)]; exact tb i hi
    · rw [write1_self]; rfl
  · exact tk.trans' (((Keep.mem _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono

end VG.Proof.Ffdh.PPC64LE.ParameterCandidate
