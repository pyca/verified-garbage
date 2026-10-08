import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms
import VerifiedGarbage.Proof.Mont.X86_64.Cms
import VerifiedGarbage.Proof.Weierstrass.X86_64.Fprog
import VerifiedGarbage.Proof.Weierstrass.X86_64.Blocks
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacState
import VerifiedGarbage.Proof.Weierstrass.Jac

/-!
# Doubling with fused small multiples, on x86-64

`doubleCms M S` (`Impl/Weierstrass/X86_64/DoubleCms.lean`) is a doubling the
Jacobian window method can use (`doubleCms_dblOk`) for a curve with `a = -3`
whose field is P-384's (`M.sparse`, which `cms` needs):

* each step keeps the invariant `Inv` (`dstep_ok`): a field operation by
  `fop_ok`, `cms` by `cms_ok`, what its result stands for being
  `C a - D b` (`toM_cms`, with `smulN` for the small multiples);
* on distinct slots the steps compute `dblJF` (`dblCms_run`), the same
  triple as `dblJMul`.
-/

namespace VG.Proof.Weierstrass.X86_64

open VG VG.Proof.Weierstrass

/-- `k x`, `x` added `k` times. -/
def smulN {F : Type _} [Lean.Grind.CommRing F] : Nat → F → F
  | 0, _ => 0
  | k + 1, x => smulN k x + x

theorem smulN_fin {m : Nat} [NeZero m] : ∀ (k : Nat) (x : Fin m), smulN k x = Fin.ofNat m k * x
  | 0, x => by
    rw [smulN]
    apply Fin.ext
    simp [Fin.val_mul]
  | k + 1, x => by
    rw [smulN, smulN_fin k x, ofNat_add', Lean.Grind.Semiring.right_distrib]
    congr 1
    apply Fin.ext
    simp [Fin.val_mul, Fin.val_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem toM_cms {m : Nat} [NeZero m] (R C A D B : Nat) (hB : B ≤ m) :
    toM m R ((C * A + D * (m - B)) % m) = smulN C (toM m R A) - smulN D (toM m R B) := by
  have e : Fin.ofNat m (D * (m - B)) + Fin.ofNat m D * Fin.ofNat m B = 0 := by
    rw [← ofNat_mul', ← ofNat_add', ← Nat.mul_add, Nat.sub_add_cancel hB]
    apply Fin.ext
    rw [Fin.val_ofNat, Nat.mul_mod_left]
    rfl
  unfold toM
  rw [smulN_fin, smulN_fin, ofNat_mod, ofNat_add', ofNat_mul', ofNat_mul']
  rw [ofNat_mul'] at e
  grind

end VG.Proof.Weierstrass.X86_64

namespace VG.Impl.Weierstrass.X86_64

open VG.Proof.Weierstrass.X86_64 (smulN)

/-- The slot a step writes. -/
def DStep.out : DStep → Nat
  | .op f => f.out
  | .cms o _ _ _ _ => o

/-- The slots a step reads. -/
def DStep.ins : DStep → List Nat
  | .op f => f.ins
  | .cms _ _ a _ b => [a, b]

/-- `cms`'s factors are below `64`. -/
def DStep.small : DStep → Bool
  | .op _ => true
  | .cms _ C _ D _ => C < 64 && D < 64

/-- A step on environments. -/
def DStep.run {F : Type _} [Lean.Grind.CommRing F] : DStep → (Nat → F) → Nat → F
  | .op f, e => f.run e
  | .cms o C a D b, e => Function.update e o (smulN C (e a) - smulN D (e b))

/-- Steps on environments. -/
def runSteps {F : Type _} [Lean.Grind.CommRing F] (l : List DStep) (e : Nat → F) : Nat → F :=
  l.foldl (fun e st => st.run e) e

end VG.Impl.Weierstrass.X86_64

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-- Every slot a step reads holds a value: one of `V` or written before. -/
def stepsReadOk : List DStep → List Nat → Bool
  | [], _ => true
  | st :: l, V => st.ins.all (fun x => decide (x ∈ V)) && stepsReadOk l (st.out :: V)

/-- The slots holding a value after the steps. -/
def stepsValid : List DStep → List Nat → List Nat
  | [], V => V
  | st :: l, V => stepsValid l (st.out :: V)

theorem mem_stepsValid {x : Nat} :
    ∀ (l : List DStep) (V : List Nat), x ∈ V ∨ x ∈ l.map DStep.out → x ∈ stepsValid l V
  | [], V, h => by simpa [stepsValid] using h
  | st :: l, V, h => by
    refine mem_stepsValid l _ ?_
    simp only [List.map_cons, List.mem_cons] at h ⊢
    grind

/-- One step. -/
theorem dstep_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hsp : M.sparse = true)
    (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) {V : List Nat} {E : Nat → Fin m} {s : State}
    (hI : Inv M base size m Sl V E s) {st : DStep} (hsm : st.small = true) (hS : ∀ x ∈ st.out :: st.ins, Sl x)
    (hR : ∀ x ∈ st.ins, x ∈ V) :
    WP isa (.block (st.code M)) s fun s' =>
      OpKeep M base st.out s s' ∧ Inv M base size m Sl (st.out :: V) (st.run E) s' := by
  cases st with
  | op f => exact fop_ok hL hm hI hS hR
  | cms o C a D b =>
    simp only [DStep.small, Bool.and_eq_true, decide_eq_true_eq] at hsm
    simp only [DStep.out, DStep.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hS hR
    have hA := hI.lt a hR.1
    have hB := hI.lt b hR.2
    refine WP.mono (cms_ok hI.scr hI.mod hsp hsm.1 hsm.2 (hL.le o hS.1) (hL.le a hS.2.1) (hL.le b hS.2.2)
      (hL.tmp a hS.2.1) hA hB) fun s' ⟨hk, heq⟩ => ⟨hk, hI.update hL hS.1 hk ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
    · rw [heq, toM_cms _ _ _ _ _ (Nat.le_of_lt hB), hI.val a hR.1, hI.val b hR.2]

/-- Steps, a block each. -/
theorem dsteps_ok {M : Mod} {base : Addr} {size m : Nat} [NeZero m] {Sl : Nat → Prop} (hsp : M.sparse = true)
    (hL : Lay M size Sl) (hm : UnitMod m (2 ^ (64 * M.n))) :
    ∀ (l : List DStep) {V : List Nat} {E : Nat → Fin m} {s : State},
      Inv M base size m Sl V E s → (∀ st ∈ l, st.small = true) → (∀ st ∈ l, ∀ x ∈ st.out :: st.ins, Sl x) →
      stepsReadOk l V = true →
      WP isa (.block (l.map (DStep.code M)).flatten) s fun s' =>
        ProgKeep M base (l.map DStep.out) s s' ∧ Inv M base size m Sl (stepsValid l V) (runSteps l E) s'
  | [], _, _, s, hI, _, _, _ => WP.block_nil ⟨ProgKeep.refl _ _ _ s, hI⟩
  | st :: l, V, E, s, hI, hsm, hS, hR => by
    simp only [stepsReadOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    rw [List.map_cons, List.flatten_cons, WP.block_append_iff]
    refine WP.mono (dstep_ok hsp hL hm hI (hsm st (List.mem_cons_self ..)) (hS st (List.mem_cons_self ..)) hR.1)
      fun s₁ ⟨k₁, I₁⟩ => ?_
    refine WP.mono (dsteps_ok hsp hL hm l I₁ (fun st' h => hsm st' (List.mem_cons_of_mem _ h))
      (fun st' h => hS st' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨⟨fun r hr => (k₂.gpr r hr).trans (k₁.gpr r hr), k₂.rd.trans k₁.rd,
        k₂.wr.trans k₁.wr, fun x hx ht => ?_⟩, I₂⟩
    rw [List.map_cons] at hx
    rw [k₂.mem x (fun w hw => hx w (List.mem_cons_of_mem _ hw)) ht,
      k₁.mem x (hx _ (List.mem_cons_self ..)) ht]

theorem dblCms_run {F : Type _} [Lean.Grind.CommRing F] (S : RcbSlots) (p : Pt) (E : Nat → F)
    (hd : (rcbW S p).Nodup) :
    (runSteps (dblCmsSteps S p) E p.x, runSteps (dblCmsSteps S p) E p.y, runSteps (dblCmsSteps S p) E p.z) =
      dblJF (E p.x) (E p.y) (E p.z) := by
  simp only [rcbW, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases hd with ⟨⟨h01, h02, h03, h04, h05, h06, h07, h08⟩, ⟨h12, h13, h14, h15, h16, h17, h18⟩,
    ⟨h23, h24, h25, h26, h27, h28⟩, ⟨h34, h35, h36, h37, h38⟩, ⟨h45, h46, h47, h48⟩, ⟨h56, h57, h58⟩,
    ⟨h67, h68⟩, h78, _⟩
  have h10 := Ne.symm h01
  have h20 := Ne.symm h02
  have h30 := Ne.symm h03
  have h40 := Ne.symm h04
  have h50 := Ne.symm h05
  have h60 := Ne.symm h06
  have h70 := Ne.symm h07
  have h80 := Ne.symm h08
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h41 := Ne.symm h14
  have h51 := Ne.symm h15
  have h61 := Ne.symm h16
  have h71 := Ne.symm h17
  have h81 := Ne.symm h18
  have h32 := Ne.symm h23
  have h42 := Ne.symm h24
  have h52 := Ne.symm h25
  have h62 := Ne.symm h26
  have h72 := Ne.symm h27
  have h82 := Ne.symm h28
  have h43 := Ne.symm h34
  have h53 := Ne.symm h35
  have h63 := Ne.symm h36
  have h73 := Ne.symm h37
  have h83 := Ne.symm h38
  have h54 := Ne.symm h45
  have h64 := Ne.symm h46
  have h74 := Ne.symm h47
  have h84 := Ne.symm h48
  have h65 := Ne.symm h56
  have h75 := Ne.symm h57
  have h85 := Ne.symm h58
  have h76 := Ne.symm h67
  have h86 := Ne.symm h68
  have h87 := Ne.symm h78
  simp only [dblCmsSteps, runSteps, List.foldl, DStep.run, FOp.run, Function.update_apply, dblJF, smulN,
    Prod.mk.injEq, *, ite_true, ite_false]
  refine ⟨?_, ?_, ?_⟩ <;> grind

theorem dblCms_reads (S : RcbSlots) (p : Pt) : stepsReadOk (dblCmsSteps S p) [p.x, p.y, p.z] = true := by
  simp [dblCmsSteps, stepsReadOk, DStep.ins, DStep.out, FOp.ins, FOp.out]

theorem dblCms_slots {S : RcbSlots} {p : Pt} {Sl : Nat → Prop} (h : ∀ x ∈ rcbW S p, Sl x) :
    ∀ st ∈ dblCmsSteps S p, ∀ x ∈ st.out :: st.ins, Sl x := by
  intro st hst x hx
  apply h x
  simp only [dblCmsSteps, List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [DStep.out, DStep.ins, FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false] at hx <;>
    simp only [rcbW, List.mem_cons, List.not_mem_nil, or_false] <;> grind

/-- The doubling with `cms` doubles a Jacobian triple, for P-384's `p` with BMI2 and ADX. -/
theorem doubleCms_dblOk {M : Mod} {C : Curve} (hsp : M.sparse = true) (hm : UnitMod C.p (2 ^ (64 * M.n)))
    (hC : Law C) (ha : AM3 C) {S : RcbSlots} : DblOk M S C (doubleCms M S) := by
  intro base size Sl hL p hnd hSl E s hI Q hQ hJ
  refine WP.mono ((blocks_wp _).mpr (dsteps_ok hsp hL hm _ hI
    (fun st hst => by
      simp only [dblCmsSteps, List.mem_cons, List.not_mem_nil, or_false] at hst
      rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> rfl)
    (dblCms_slots hSl) (dblCms_reads S p))) fun t ⟨k, I⟩ =>
    ⟨k.mono fun x hx => ?_, _, I.sub fun x hx => ?_, InvJ.dbl' hC ha hQ hJ (dblCms_run S p E hnd)⟩
  · obtain ⟨st, hst, rfl⟩ := List.mem_map.mp hx
    exact dblCms_slots (fun _ h => h) st hst st.out (List.mem_cons_self ..)
  · apply mem_stepsValid
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> simp [dblCmsSteps, DStep.out, FOp.out]

end VG.Proof.Weierstrass.X86_64
