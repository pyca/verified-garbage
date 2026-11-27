module

public import VerifiedGarbage.Impl.X448.RISCV64
public import VerifiedGarbage.Proof.X25519.RISCV64.Field
public import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.RISCV64.Instr
public import VerifiedGarbage.Proof.X25519.Limbs
public import VerifiedGarbage.Proof.X448.Limbs32 -- shake: keep (re-exported below for the RISC-V proofs' `open`s)
import VerifiedGarbage.Proof.Framework.Range

/-! ### `X448.RISCV64.Pass`, which this module and modules that import it used -/

section

/-!
# X448 on RISCV64: carrying sums into limbs

`pass rb o src` stores at `rb + o` the 14 limbs of `Σ c_k 2^(32k) + cin`, from
the sums `c_k` that `src k` leaves in `a4` and the carry `cin` in `a5`
(`pass_ok`), with X25519's invariant (`PassInv`) and step (`carryStep_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64

theorem pass_ok {rb : Reg} {o : Nat} {src : Nat → List Instr} {s0 : State} {c : Nat → Nat}
    {cin : Nat} (hrb : rb ∉ [.a2, .a4, .a5]) (ho : o + 56 ≤ 2048)
    (hw : ∀ k < 14, InRegions s0.wr (s0.gpr rb + BitVec.ofNat 64 (o + 4 * k)) 4)
    (hal : ∀ k < 14, (s0.gpr rb + BitVec.ofNat 64 (o + 4 * k)).toNat % 4 = 0)
    (h8 : (s0.gpr .a5).toNat = cin)
    (hc : ∀ k < 14, c k + 2 ^ 32 ≤ 2 ^ 64) (hcin : cin < 2 ^ 32)
    (hsrc : ∀ k < 14, ∀ s, PassInv rb o s0 c cin k s →
      WP isa (.block (src k)) s fun s' =>
        (s'.gpr .a4).toNat = c k ∧ Rest [.a2, .a4] s s' ∧ s'.mem = s.mem) :
    WP isa (.block (pass rb o src)) s0 (PassInv rb o s0 c cin 14) := by
  have hr := not_mem3 hrb
  refine wp_range_flatMap (M := isa) (PassInv rb o s0 c cin) (fun k s hk h => ?_) 14 (Nat.le_refl _) s0
    ⟨Rest.refl _ _, by rw [h8]; rfl, Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  refine WP.append (hsrc k hk s h) fun s1 ⟨h7, hr1, hm1⟩ => ?_
  have hrb1 : s1.gpr rb = s0.gpr rb := by
    rw [hr1.gpr _ (by simp [hr.1, hr.2.1]), h.rest.gpr _ hrb]
  have h81 : s1.gpr .a5 = s.gpr .a5 := hr1.gpr _ (by decide)
  have hsum := sum_lt hc hcin hk
  refine WP.mono (carryStep_ok (a := s0.gpr rb + BitVec.ofNat 64 (o + 4 * k))
    hr.2.1 (by omega_using [ho, hk]) (by rw [hrb1]) (hal k hk)
    (by rw [hr1.wr, h.rest.wr]; exact hw k hk)
    (by rw [h7, h81, h.a5]; exact hsum)) fun s2 ⟨e8, ⟨v, hv, hm2⟩, hr2⟩ => ?_
  rw [h7, h81, h.a5] at e8 hv
  rw [hm1] at hm2
  refine ⟨h.rest.trans ((hr1.mono (by decide)).trans (hr2.mono (by decide))), by rw [e8]; rfl, ?_,
    fun j hj => ?_⟩
  · rw [hm2]
    refine (h.frame.sub fun r hr' => ⟨_, List.mem_singleton_self _, ?_⟩).writeW
      (List.mem_singleton_self _) v (Offset.contains _ (Nat.le_add_right _ _) (by omega_using []) (by omega_using [ho, hk]))
    rw [List.mem_singleton.mp hr']
    exact Region.sub_prefix (by omega_using [])
  · rw [hm2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [wd_write_other _ _ _ (by omega_using [hj]) (by omega_using [ho, hk, hj]) (by omega_using [ho, hk])]; exact h.outs j hj
    · rw [wd_write_self, hv]; rfl

end VG.Proof.X448.RISCV64

end

end

/-! ### `X448.RISCV64.Limbs`, which this module and modules that import it used -/

section

/-!
# X448 on RISCV64: numbers of 32-bit limbs

`Proof/X448/Limbs32.lean`, shared with PPC64LE, under this target's namespace,
which the proofs built on it open.
-/

public section

namespace VG.Proof.X448.RISCV64

export VG.Proof.X448.Limbs32 (pow448 pow448_eq P_eq fold448 rowAcc row_val rowAcc_lt foldC foldC_le foldC_facts foldL val32_foldL fold1 fold1C fold1_facts chain_congr fold1_congr tailL tail_facts fourP val32_fourP subC subC_facts carry_le frR freeze_facts val32_single)

end VG.Proof.X448.RISCV64

end

end

/-!
# X448 on RISCV64: field elements in the working space

A field element is 14 words at an offset `o` of the working space at `B`
(X25519's `limb`), for the number `V` and its residue `FS`.
-/

@[expose] public section

namespace VG.Proof.X448.RISCV64

open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.X448.RISCV64 VG.Proof.X25519 VG.Proof.X25519.RISCV64
open VG.Spec.X448 (P Fe)

/-- The number of the element at `o`. -/
def V (m : Mem) (B : Addr) (o : Nat) : Nat := val32 (limb m B o) 14

/-- The element at `o`. -/
def FS (m : Mem) (B : Addr) (o : Nat) : Fe := Proof.X448.toFe (V m B o)

theorem V_lt (m : Mem) (B : Addr) (o : Nat) : V m B o < 2 ^ 224 * 2 ^ 224 := by
  have := val32_lt (f := limb m B o) (n := 14) fun k _ => limb_lt m B o k
  rwa [pow448] at this

/-- The limbs of an element in a frame that does not overlap it. -/
theorem limb_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {B : Addr} {o : Nat}
    (hd : ∀ r ∈ rs, ∀ k < 14, (⟨B + BitVec.ofNat 64 (o + 4 * k), 4⟩ : Region).Disjoint r) :
    ∀ k < 14, limb m' B o k = limb m B o k := fun k hk => wd_frame hf fun r hr => hd r hr k hk

section
variable {b : Addr}

/-- A word the pass has not written yet (the pass writes `[o, o + 4k)`). -/
theorem wd_pass {s0 s : State} (hc : Ctx b s0) {o k d : Nat}
    (hf : Frame [⟨s0.gpr .a3 + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem)
    (hd : d + 4 ≤ o ∨ o + 4 * k ≤ d) (hd' : d + 4 ≤ 2048) (ho : o + 4 * k ≤ 2048) :
    wd s.mem b d = wd s0.mem b d := by
  rw [hc.a3] at hf
  exact wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega_using [hd']) (by omega_using [ho])

end

end VG.Proof.X448.RISCV64
