module

public import VerifiedGarbage.Proof.Rsa.X86.RvTimeBase
public import VerifiedGarbage.Proof.Rsa.X86.RvHalfStep
public import VerifiedGarbage.Proof.Rsa.X86.RvNumbers
import VerifiedGarbage.Proof.Rsa.X86.RvTimeCheck
import VerifiedGarbage.Proof.Rsa.X86.RvHalving
public import VerifiedGarbage.Proof.Rsa.X86.RvMont
public import VerifiedGarbage.Proof.Rsa.X86.RvRestFacts
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Rsa.X86.RvMontStage

/-! # The halvings and the Montgomery setup leak only public data

Two runs from their numbers (`NumbersState`) over the same geometry leak the
same trace through the halving of `e d - 1` and the Montgomery setup of the
modulus.
-/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev NumbersState (g : CallGeometry) (s0 s : State) : Prop :=
  KS g.toGeo s0 (fun _ => inputValue g s0.mem 0) [aN]
    (fun _ => 2 * (product g s0.mem / 2)) [wM] (fun _ => 0) [] s

theorem halfLoop_relCT {g : Geo} (pg : PubG g) (s0 t0 : State) (A B : Nat → Nat) (m r c : Nat)
    (positive : 0 < c) (bound : c ≤ 16384) :
    RelCT isa (fun s t => HI g s0 A m c 0 s ∧ HI g t0 B r c 0 t)
      (.loop VG.Impl.Rsa.X86.RecoverRt.halfBody .ne) (fun s t => HI g s0 A m c c s ∧ HI g t0 B r c c t) :=
  fixedLoop_relCT (fun k s => HI g s0 A m c k s) (fun k t => HI g t0 B r c k t) positive
    (fun _ _ _ _ _ _ _ _ ⟨hs, ht⟩ es et => ⟨by unfold HI at hs ht; exact pub_trace pg halfBodyCheck hs ht es et, trivial⟩)
    (fun _ _ hk hs => halfBody_ok hs hk bound) (fun _ _ hk ht => halfBody_ok ht hk bound)

theorem halving_relCT (g : CallGeometry) (pg : PubG g.toGeo) (s0 t0 : State)
    (left : Inputs g s0) (right : Inputs g t0) :
    RelCT isa (fun s t => NumbersState g s0 s ∧ NumbersState g t0 t) VG.Impl.Rsa.X86.RecoverRt.halving
      (fun s t => HI g.toGeo s0 (fun _ => inputValue g s0.mem 0)
        (2 * (product g s0.mem / 2)) (countBits g) (countBits g) s ∧
        HI g.toGeo t0 (fun _ => inputValue g t0.mem 0)
        (2 * (product g t0.mem / 2)) (countBits g) (countBits g) t) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  obtain ⟨count, limit⟩ := left.countBounds
  obtain ⟨ae, ad⟩ := inputArguments left
  obtain ⟨be, bd⟩ := inputArguments right
  cases es with
  | @seq _ _ _ u _ _ _ e1 e2 =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 f2 =>
      have eq1 := pub_trace pg halfInitCheck hs ht e1 f1
      have cs := wp_result (halfInit_ok hs (by simp) rfl ae ad (by change countBits g < 2 ^ 32; omega)) e1
      have ds := wp_result (halfInit_ok ht (by simp) rfl be bd (by change countBits g < 2 ^ 32; omega)) f1
      obtain ⟨eq2, is, it⟩ := halfLoop_relCT pg s0 t0
        (fun _ => inputValue g s0.mem 0) (fun _ => inputValue g t0.mem 0)
        (2 * (product g s0.mem / 2)) (2 * (product g t0.mem / 2)) (countBits g)
        count limit _ _ _ _ _ _ ⟨cs, ds⟩ e2 f2
      exact ⟨by rw [eq1, eq2], is, it⟩

/-- `montHead`'s result, from which the Montgomery product runs. -/
theorem montHead_pre {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {m : Nat}
    (h : KS g s0 (AH A g.n m) liveH AW [wR] V [sTc, sCnt] s) (mr : MR g m s) (hm : 1 < m) :
    MulPre g mXm mXm mR2 s :=
  ⟨_, _, _, _, _, _, _, _, h, mr, by simp, by simp, by simpa [AH, upd] using hm,
    by simpa [AH, upd, mXm, mR2] using Nat.mod_lt (2 ^ (128 * g.n)) (by omega : 0 < m), by decide, by decide⟩

theorem mont_relCT {g : Geo} (pg : PubG g) {s0 t0 : State} {A B AW BW V W : Nat → Nat} {m m' : Nat}
    (vA : A aN = m) (vB : B aN = m') (bA : m < 2 ^ (64 * g.n)) (bB : m' < 2 ^ (64 * g.n))
    (oA : m % 2 = 1) (oB : m' % 2 = 1) (lA : 1 < m) (lB : 1 < m') :
    RelCT isa (fun s t => KS g s0 A [aN] AW [wR] V [sTc, sCnt] s ∧ KS g t0 B [aN] BW [wR] W [sTc, sCnt] t)
      VG.Impl.Rsa.X86.RecoverRt.mont (fun _ _ => True) := by
  intro s t tr ur sf tf ⟨hs, ht⟩ es et
  cases es with
  | @seq _ _ _ u _ _ _ e1 er =>
    cases et with
    | @seq _ _ _ v _ _ _ f1 fr =>
      have eq1 := pub_trace pg montHeadCheck hs ht e1 f1
      obtain ⟨hu, mu⟩ := wp_result (montHead_ok hs vA bA oA lA) e1
      obtain ⟨hv, mv⟩ := wp_result (montHead_ok ht vB bB oB lB) f1
      cases er with
      | @seq _ _ _ x _ _ _ e2 e3 =>
        cases fr with
        | @seq _ _ _ y _ _ _ f2 f3 =>
          have eq2 := (mmul_relCT pg (by decide) (by decide) (by decide) (by decide) mulArgs_mXm_mXm_mR2Check
            ⟨_, clrTop_mXmCheck⟩ _ _ _ _ _ _ ⟨montHead_pre hu mu lA, montHead_pre hv mv lB⟩ e2 f2).1
          obtain ⟨_, hx, _⟩ := wp_result (hu.mmul mu (o := mXm) (a := mXm) (b := mR2)
            (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)
            (by simpa [AH, upd] using lA)
            (by simpa [AH, upd, mXm, mR2] using Nat.mod_lt (2 ^ (128 * g.n)) (by omega : 0 < m))
            (by decide) (by decide)) e2
          obtain ⟨_, hy, _⟩ := wp_result (hv.mmul mv (o := mXm) (a := mXm) (b := mR2)
            (by decide) (by decide) (by decide) (by decide) (by simp) (by simp)
            (by simpa [AH, upd] using lB)
            (by simpa [AH, upd, mXm, mR2] using Nat.mod_lt (2 ^ (128 * g.n)) (by omega : 0 < m'))
            (by decide) (by decide)) f2
          have eq3 := pub_trace pg montTailCheck hx hy e3 f3
          exact ⟨by rw [eq1, eq2, eq3], trivial⟩

end VG.Proof.Rsa.X86.Recover
