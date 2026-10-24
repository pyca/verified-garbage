module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTDraw
import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.CTDraw
meta import VerifiedGarbage.Proof.RsaKeyGen.CandSpec
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# A candidate on PPC64LE: the witnesses' loop in constant time

`mr_ct`: two runs of `Witness.millerRabin` from the same public data leak
the same trace. Each iteration (`iter_ct`) tests the octets left (the same in
both runs: the same iteration), draws (`draw_ct`) and tests its status,
whose result `mc_agree` makes the same in both runs; the loop is then
`RelCT.loop` over the iterations left, which the shape of the test's result
fixes for both runs.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.PPC64LE.Taint VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (ldh sth hStat)
open VG.Proof.MillerRabin.PPC64LE (Env arr RoundImpl)
open VG.Proof.Bignum (slot)
open VG.Proof.RsaKeyGen (MrAt mrS wit)

/-- After the test of octets left. -/
def LB (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) ak.2 s ∧
    s.gpr .r5 = BitVec.ofNat 64 (if 8 * cw s0 ≤ rL s0 - 8 * cw s0 * (ak.2 + 1) then 1 else 0)

/-- After the draw, or the loop's end for want of octets. -/
def LM (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    Mid q (sB s0) (sL s0) (cw s0) (candOf s0) (rL s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (rB s0) ak.2 n s

/-- After the test of the status. -/
def LT (n : Nat) (ak : CD × Nat) (s : State) : Prop :=
  ∃ s0 q, LCtx ak.1 s0 q ∧
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) ak.2 n ∧
    Tl q (sB s0) (sL s0) (cw s0) (candOf s0) (rL s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (rB s0) ak.2 n s

theorem pins_LI {n : Nat} : Pins (LI n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, hi⟩ ⟨s0', q', C', -, hi'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel hi.prep.env hi'.prep.env _ (by simp)

theorem pins_LB {n : Nat} : Pins (LB n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, hi, -⟩ ⟨s0', q', C', -, hi', -⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel hi.prep.env hi'.prep.env _ (by simp)

theorem Mid.h31 {s t : State} {B : Addr} {L w c rl ch : Nat} {r : Spec.RsaKeyGen.Rand} {k n : Nat}
    (h : Mid s B L w c rl ch r k n t) : t.gpr .r31 = B := by
  rcases h with ⟨-, -, hi⟩ | ⟨-, -, -, -, ho⟩
  · exact hi.prep.env.h31
  · exact ho.prep.env.h31

theorem pins_LM {n : Nat} : Pins (LM n) [.r31] := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, hm⟩ ⟨s0', q', C', -, hm'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  rw [hm.h31, hm'.h31]; exact C.krel.arg C'.krel (i := 1) (by decide)

theorem avail_eval {n : Nat} : ∀ (ak : CD × Nat) (s₁ s₂ : State), LB n ak s₁ → LB n ak s₂ →
    isa.eval (.zero .d .r5) s₁ = isa.eval (.zero .d .r5) s₂ := by
  rintro ⟨a, k⟩ s₁ s₂ ⟨s0, q, C, -, -, a5⟩ ⟨s0', q', C', -, -, a5'⟩
  rw [eval_zero_ofNat _ _ (by split <;> decide) a5, eval_zero_ofNat _ _ (by split <;> decide) a5']
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  simp only [hw, C.krel.rL_eq C'.krel]

/-- One iteration. -/
theorem iter_ct (R : RoundImpl) (n : Nat) :
    RelCT isa (Two (LI n)) (.seq (.block availB) (.seq (drawI R) (.block tailB))) fun s₁ s₂ =>
      isa.eval (.zero .d .r3) s₁ = isa.eval (.zero .d .r3) s₂ ∧
        (isa.eval (.zero .d .r3) s₁ = some false → True) ∧
        (isa.eval (.zero .d .r3) s₁ = some true → ∃ m < n, Two (LI m) s₁ s₂) := by
  refine RelCT.seq (two_post (Ψ := LB n) (two_taint _ pins_LI (by taint_decide))
    fun ⟨a, k⟩ s ⟨s0, q, C, ha, hi⟩ => WP.mono (availS C.t3.lin ha hi) fun t ⟨h₁, a5⟩ =>
      ⟨s0, q, C, ha, h₁, a5⟩) (RelCT.seq (two_post (Ψ := LM n) (two_ite avail_eval
        (two_taint _ (pins_and pins_LB) (by taint_decide))
        (two_mono (Ψ := LD n) (fun ⟨a, k⟩ s ⟨⟨s0, q, C, ha, hi, a5⟩, ev⟩ => ⟨s0, q, C, ha, hi, ?_⟩) (draw_ct R)))
      fun ⟨a, k⟩ s ⟨s0, q, C, ha, hi, a5⟩ => WP.mono (mid_ok R C.t3.lin ha hi a5) fun t hm =>
        ⟨s0, q, C, ha, hm⟩) ?_)
  · dsimp only at a5 ⊢
    have hw4 := C.t3.prep.env.hw
    rw [eval_zero_ofNat _ _ (by split <;> decide) a5] at ev
    simp only [Option.some.injEq, decide_eq_false_iff_not] at ev
    rw [rB_len]
    split at ev
    · omega
    · exact absurd rfl ev
  · refine (two_post (Ψ := LT n) (two_taint _ pins_LM (by taint_decide)) fun ⟨a, k⟩ s ⟨s0, q, C, ha, hm⟩ =>
      WP.mono (tailS hm) fun t ht => ⟨s0, q, C, ha, ht⟩).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨⟨a, k⟩, ⟨s0, q, C, ha, ht⟩, ⟨s0', q', C', ha', ht'⟩, hsp⟩
    have hm := mc_agree C C' ha ha'
    rcases ht with ⟨hc, ev, ha1, hi1⟩ | ⟨hc, ev, -⟩ <;> rcases ht' with ⟨hc', ev', ha1', hi1'⟩ | ⟨hc', ev', -⟩
    · refine ⟨by rw [ev, ev'], fun _ => trivial, fun _ => ⟨n - 1, by have := hc.2.2; omega, (a, k + 1),
        ⟨s0, q, C, ha1, hi1⟩, ⟨s0', q', C', ha1', hi1'⟩, hsp⟩⟩
    · exact absurd (hm.mp hc) hc'
    · exact absurd (hm.mpr hc') hc
    · exact ⟨by rw [ev, ev'], fun _ => trivial, fun h => by rw [ev] at h; cases h⟩

/-- The loop's start: the working space prepared, from `s0`. -/
def L3 (a : CD) (s : State) : Prop := ∃ s0, LCtx a s0 s

/-- After the loop's counts are set up. -/
def L0 (a : CD) (t : State) : Prop :=
  ∃ s0 q, LCtx a s0 q ∧ St q (sB s0) (sL s0) (cw s0) (candOf s0) (rB s0) 0 t

/-- The iterations of the loop, `1` less. -/
def n0 (s0 : State) : Nat :=
  VG.Proof.RsaKeyGen.itersOf (8 * cw s0) (rB s0).length
    (VG.Proof.RsaKeyGen.shapeOf (Spec.RsaKeyGen.primalityTest (candOf s0) ((rB s0).drop (8 * cw s0))))
    (8 * cw s0) - 1

theorem LCtx.mrAt0 {a : CD} {s0 q : State} (C : LCtx a s0 q) :
    MrAt (candOf s0) (VG.Proof.RsaKeyGen.checksW (cw s0)) (lA s0) (lM s0) (8 * cw s0) (rB s0) 0 (n0 s0) := by
  have P := C.t3.lin
  have hw4 := C.t3.prep.env.hw
  obtain ⟨_, _, hwb⟩ := VG.Proof.RsaKeyGen.cand_bits (by omega : 1 ≤ cw s0) P.shape
  have hrl := rB_len s0
  have h8 := C.t3.tc.h8
  have hc := VG.Proof.RsaKeyGen.primalityTest_cand (by omega) P.shape ((rB s0).drop (8 * cw s0))
  rw [← P.hch] at hc
  exact VG.Proof.RsaKeyGen.mrAt_zero hc hwb (by omega) (by omega)

theorem n0_eq {a : CD} {s0 s0' q q' : State} (C : LCtx a s0 q) (C' : LCtx a s0' q') : n0 s0 = n0 s0' := by
  have hw : cw s0 = cw s0' := by simp only [cw, C.krel.oL_eq C'.krel]
  unfold n0
  rw [shape_eq C C', rB_len, rB_len, C.krel.rL_eq C'.krel, hw]

theorem pins_L3 : Pins L3 [.r31] := by
  rintro a s₁ s₂ ⟨s0, C⟩ ⟨s0', C'⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact env_agree C.krel C'.krel C.t3.prep.env C'.t3.prep.env _ (by simp)

/-- The witnesses' loop. -/
theorem mr_ct (R : RoundImpl) :
    RelCT isa (Two L3) (VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin R.name R.code) fun _ _ => True := by
  unfold VG.Impl.RsaKeyGen.PPC64LE.Witness.millerRabin
  refine RelCT.seq ((two_post (Ψ := L0) (two_taint _ pins_L3 (by taint_decide)) fun a s ⟨s0, C⟩ =>
    WP.mono (init_ok C.t3.prep C.t3.hu0) fun t ht => ⟨s0, s, C, ht⟩).mono (fun _ _ h => h)
      (fun s₁ s₂ ⟨a, ⟨s0, q, C, h₁⟩, ⟨s0', q', C', h₂⟩, hsp⟩ => ⟨n0 s0, (a, 0), ⟨s0, q, C, C.mrAt0, h₁⟩,
        ⟨s0', q', C', n0_eq C C' ▸ C'.mrAt0, h₂⟩, hsp⟩))
    (RelCT.exists_ fun n => RelCT.loop (fun n => Two (LI n)) (iter_ct R) n)

end VG.Proof.RsaKeyGen.PPC64LE.Cand
