module
public import VerifiedGarbage.Impl.X448.PPC64LE
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field
public import VerifiedGarbage.Proof.X448.PPC64LE.Limbs
import VerifiedGarbage.Proof.X448.PPC64LE.Pass
public import VerifiedGarbage.Proof.X448.Field

import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.X25519.PPC64LE.Instr
public import VerifiedGarbage.Proof.X25519.PPC64LE.Limbs

/-!
# X448 on PPC64LE: field elements in the working space

A field element is 14 words at an offset `o` of the working space at `B`
(X25519's `limb`), for the number `V` and its residue `FS`. The carry out of
a `pass` folded in (`fold_ok`), twice (`tail_ok`).
-/

@[expose] public section

namespace VG.Proof.X448.PPC64LE

open VG VG.PPC64LE VG.Impl.X448.PPC64LE VG.Proof.X25519.PPC64LE
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
    (hf : Frame [⟨s0.gpr .r6 + BitVec.ofNat 64 o, 4 * k⟩] s0.mem s.mem)
    (hd : d + 4 ≤ o ∨ o + 4 * k ≤ d) (hd' : d + 4 ≤ 4096) (ho : o + 4 * k ≤ 4096) :
    wd s.mem b d = wd s0.mem b d := by
  rw [hc.r6] at hf
  exact wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd (by omega_using [hd']) (by omega_using [ho])

/-- The carry `c` in `r8` folded into the element at `o`: added to limbs 0
and 7, and carried. -/
theorem fold_ok {o : Nat} (ho : o + 56 ≤ 4096) {s : State} (hc : Ctx b s) {c : Nat}
    (h8 : (s.gpr .r8).toNat = c) (hc4 : c < 2 ^ 32) :
    WP isa (.block (fold o)) s fun s' =>
      Rest [.r5, .r7, .r8, .r10] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      (∀ k < 14, limb s'.mem b o k = fold1 (limb s.mem b o) c k) ∧
      (s'.gpr .r8).toNat = fold1C (limb s.mem b o) c := by
  have hl : ∀ k < 14, limb s.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨hf1, -, -⟩ := fold1_facts hl hc4
  unfold fold
  refine wp_addi (by decide) (by decide) fun s1 u1 => ?_
  have hc1 : Ctx b s1 := hc.of_rest (u1.rest (ws := [.r10]) (by decide)) (by decide)
  have e10 : (s1.gpr .r10).toNat = c := by rw [u1.gpr, BitVec.add_zero, h8]
  have h81 : (s1.gpr .r8).toNat = c := by rw [u1.other .r8 (by decide), h8]
  refine WP.mono (pass_ok (s0 := s1) (c := foldL (limb s.mem b o) c) (cin := c)
    (by decide) (by decide) ho
    (fun k hk => by rw [hc1.r6]; exact hc1.inW (by omega_using [ho, hk]))
    h81 hf1 hc4 ?_) fun s2 hp => ?_
  · intro k hk s' hp
    have hc' : Ctx b s' := hc1.of_rest hp.rest (by decide)
    have ew : wd s'.mem b (o + 4 * k) = limb s.mem b o k := by
      rw [wd_pass hc1 hp.frame (by omega_using []) (by omega_using [ho, hk]) (by omega_using [ho, hk]), ← u1.mem]; rfl
    unfold foldSrc
    refine WP.append (ldSrc_ok hc' (by omega_using [ho, hk])) fun t ⟨h7, hr, hm⟩ => ?_
    by_cases h7k : k = 7
    · simp only [h7k, ite_true]
      refine wp_add fun t1 v1 => WP.block_nil ⟨?_, (hr.trans (v1.rest (by decide))).mono (by decide), by rw [v1.mem, hm]⟩
      have e : (t.gpr .r10).toNat = c := by rw [hr.gpr _ (by decide), hp.rest.gpr _ (by decide), e10]
      have := limb_lt s.mem b o k
      rw [v1.gpr, toNat_add_lt (by rw [h7, ew, e]; omega_using [this, hc4]), h7, ew, e, foldL, h7k]; rfl
    · simp only [h7k, ite_false]
      exact WP.block_nil ⟨by rw [h7, ew, foldL]; simp only [h7k, ite_false, Nat.add_zero],
        hr.mono (by decide), hm⟩
  · refine ⟨(u1.rest (by decide)).trans (hp.rest.mono (by decide)), ?_, fun k hk => ?_, hp.r8⟩
    · have := hp.frame; rw [hc1.r6] at this; rw [← u1.mem]; exact this
    · have := hp.outs k hk; rwa [hc1.r6] at this

/-- The carry `c ≤ 4` in `r8` folded into the element at `o` twice; nothing
carries out. -/
theorem tail_ok {o : Nat} (ho : o + 56 ≤ 4096) {s : State} (hc : Ctx b s) {c : Nat}
    (h8 : (s.gpr .r8).toNat = c) (hc4 : c ≤ 4) :
    WP isa (.block (tail o)) s fun s' =>
      Rest [.r5, .r7, .r8, .r10] s s' ∧ Frame [⟨b + BitVec.ofNat 64 o, 56⟩] s.mem s'.mem ∧
      V s'.mem b o % P = (V s.mem b o + 2 ^ 224 * 2 ^ 224 * c) % P := by
  have hl : ∀ k < 14, limb s.mem b o k < 2 ^ 32 := fun k _ => limb_lt _ _ _ _
  obtain ⟨ht1, -, htv⟩ := tail_facts hl hc4
  unfold tail
  refine WP.append (fold_ok ho hc h8 (by omega_using [hc4])) fun s1 ⟨hr1, hf1, hl1, h81⟩ => ?_
  have hc1 : Ctx b s1 := hc.of_rest hr1 (by decide)
  refine WP.mono (fold_ok ho hc1 h81 (by omega_using [ht1])) fun s2 ⟨hr2, hf2, hl2, _⟩ =>
    ⟨hr1.trans hr2, hf1.trans hf2, ?_⟩
  have e : ∀ k < 14, limb s2.mem b o k = tailL (limb s.mem b o) c k := fun k hk => by
    rw [hl2 k hk, (fold1_congr hl1 _).1 k hk]; rfl
  rw [V, val32_congr e, htv]; rfl

end

end VG.Proof.X448.PPC64LE
