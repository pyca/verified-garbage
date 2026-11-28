module

-- separate module: the two-run proofs of `forsSign`'s trees, rebuilt only when their correctness changes

public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsMain
public import VerifiedGarbage.Proof.SlhDsa.AArch64.ForsCTTree
import VerifiedGarbage.Proof.Framework.Omega

/-!
# SLH-DSA (SHAKE) on AArch64: a tree of `forsSign` is constant time

A tree (`tree_ct`), in two runs at the same tree `tt` with the same
signature buffer: each run keeps its correctness invariant (`TL`); the first
block by the taint analysis, then the loop of subtrees (`subs_ct`) from the
same subtree, the heights above them (`top_ct`), the next tree by the taint
analysis.
-/

@[expose] public section

namespace VG.Proof.SlhDsa.AArch64.Fors

open VG VG.AArch64
open VG.Spec.SlhDsa
open VG.Impl.SlhDsa.AArch64 (Layout)
open VG.Impl.SlhDsa.AArch64.Fors (s)
open VG.Proof.SlhDsa.AArch64.TreeBase

variable {p : Params}

/-- After a tree's first block: the subtrees' loop's entry `t₁`, from the
tree's entry `t`. -/
abbrev TB0 (p : Params) (S SG : Addr) (pk a16 sk : List Byte) (ix : Nat → Nat) (t₀ : State) (tt : Nat)
    (t₁ : State) : Prop :=
  ∃ t, TL p S SG pk a16 sk ix t₀ tt t ∧
    SC p S SG (SG + BitVec.ofNat 64 (tt * tsl p)) (p.k * tsl p) (tt * tsl p) tt (ix tt) t₁ ∧
    ST p S (SG + BitVec.ofNat 64 (tt * tsl p)) pk a16 sk (t₁.gpr .x20).toNat tt (ix tt) t₁ 0 t₁ ∧
    T0 p S SG tt t t₁

/-- After the loop of subtrees, from its entry `t₁`. -/
abbrev TB1 (p : Params) (S SG : Addr) (pk a16 sk : List Byte) (ix : Nat → Nat) (t₀ : State) (tt : Nat)
    (w : State) : Prop :=
  ∃ t₁, TB0 p S SG pk a16 sk ix t₀ tt t₁ ∧
    ST p S (SG + BitVec.ofNat 64 (tt * tsl p)) pk a16 sk (t₁.gpr .x20).toNat tt (ix tt) t₁
      (2 ^ (p.a - s p.a)) w

section
variable {S SG : Addr} {pk a16 sk : List Byte} {ix : Nat → Nat} {t₀ : State} {tt : Nat}

theorem TB0.sp {t₁ : State} (h : TB0 p S SG pk a16 sk ix t₀ tt t₁) : t₁.sp = t₀.sp := by
  obtain ⟨t, hI, -, -, h0⟩ := h
  rw [h0.keep.sp, hI.sp]

theorem TB0.x23 {t₁ : State} (h : TB0 p S SG pk a16 sk ix t₀ tt t₁) : t₁.gpr .x23 = BitVec.ofNat 64 tt := by
  obtain ⟨t, hI, -, -, h0⟩ := h
  rw [h0.keep.gpr .x23 (by decide), hI.x23]

theorem TB1.tpre (M : MC p S SG t₀) (htt : tt < p.k) {w : State} (h : TB1 p S SG pk a16 sk ix t₀ tt w) :
    TPre p S SG (SG + BitVec.ofNat 64 (tt * tsl p)) (p.k * tsl p) (tt * tsl p) tt (tt * 2 ^ p.a) (ix tt) pk a16
      t₀.sp w := by
  obtain ⟨t₁, h0, hI⟩ := h
  have hk : (tt + 1) * p.n ≤ 1120 :=
    Nat.le_trans (Nat.mul_le_mul (show tt + 1 ≤ 35 by have := M.k35; omega) M.hz.n32) (by decide)
  have h23 := h0.x23
  have hsp := h0.sp
  obtain ⟨_, _, C, _, _⟩ := h0
  have := ST.tpre C h23 hk hI
  rwa [hsp] at this

end

/-- A tree, in two runs at the same tree with the same signature buffer and
stack pointer. -/
theorem tree_ct (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true)
    {S SG : Addr} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte} {ix₁ ix₂ : Nat → Nat} {t₀₁ t₀₂ : State}
    (M₁ : MC p S SG t₀₁) (M₂ : MC p S SG t₀₂) (hix₁ : ∀ i < p.k, ix₁ i < 2 ^ p.a)
    (hix₂ : ∀ i < p.k, ix₂ i < 2 ^ p.a) (hsp : t₀₁.sp = t₀₂.sp) {tt : Nat} (htt : tt < p.k) :
    RelCT isa (fun a b => TL p S SG pk₁ a₁ sk₁ ix₁ t₀₁ tt a ∧ TL p S SG pk₂ a₂ sk₂ ix₂ t₀₂ tt b)
      (Impl.SlhDsa.AArch64.Fors.treeBody ⟨p.n, p.len⟩ p.a p.k t4name ln T.code) fun _ _ => True := by
  have hz := M₁.hz
  unfold Impl.SlhDsa.AArch64.Fors.treeBody
  refine relSeq (c₁ := .block (t0List p.n p.a)) (B₁ := TB0 p S SG pk₁ a₁ sk₁ ix₁ t₀₁ tt)
    (B₂ := TB0 p S SG pk₂ a₂ sk₂ ix₂ t₀₂ tt)
    (ct_tree0 hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha.sp, hb.sp, hsp], fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [ha.cs .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          hb.cs .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          M₁.x19, M₂.x19]
      · rw [ha.x23, hb.x23]
      · rw [ha.x24, hb.x24]⟩)
    (fun t ht => WP.mono (tree0_ok M₁ hix₁ htt ht) fun t₁ h => ⟨t, ht, h⟩)
    (fun t ht => WP.mono (tree0_ok M₂ hix₂ htt ht) fun t₁ h => ⟨t, ht, h⟩) ?_
  refine relSeq (B₁ := TB1 p S SG pk₁ a₁ sk₁ ix₁ t₀₁ tt) (B₂ := TB1 p S SG pk₂ a₂ sk₂ ix₂ t₀₂ tt)
    (RelCT.pointwise ?_)
    (fun t₁ ⟨t, ht, C, hS, h0⟩ => WP.mono (subs_ok T t4name ln hL hLf C hS) fun w hw => ⟨t₁, ⟨t, ht, C, hS, h0⟩, hw⟩)
    (fun t₁ ⟨t, ht, C, hS, h0⟩ => WP.mono (subs_ok T t4name ln hL hLf C hS) fun w hw => ⟨t₁, ⟨t, ht, C, hS, h0⟩, hw⟩) ?_
  · rintro a b ⟨ha, hb⟩
    have hspa := ha.sp
    have hspb := hb.sp
    obtain ⟨_, _, Ca, Sa, _⟩ := ha
    obtain ⟨_, _, Cb, Sb, _⟩ := hb
    exact RelCT.mono (subs_ct hA T t4name ln hL hLf Ca Cb (by rw [hspa, hspb, hsp])
        (2 ^ (p.a - s p.a)))
      (fun x y ⟨ex, ey⟩ => by
        subst ex ey
        exact ⟨⟨0, by omega, Nat.two_pow_pos _, Sa⟩, ⟨0, by omega, Nat.two_pow_pos _, Sb⟩⟩)
      fun _ _ _ => trivial
  refine relSeq (B₁ := fun w => w.sp = t₀₁.sp) (B₂ := fun w => w.sp = t₀₁.sp)
    (RelCT.mono (top_ct hz hA hL hLf) (fun a b ⟨ha, hb⟩ =>
      ⟨ha.tpre M₁ htt, by have := hb.tpre M₂ htt; rw [← hsp] at this; exact this⟩) fun _ _ h => h)
    (fun w hw => top_sp hz hA hL hLf (hw.tpre M₁ htt))
    (fun w hw => top_sp hz hA hL hLf (by have := hw.tpre M₂ htt; rw [← hsp] at this; exact this))
    (ct_nextTree hA fun a b ⟨ha, hb⟩ => ⟨by rw [ha, hb], fun _ h => absurd h List.not_mem_nil⟩)

/-- The loop of trees, in two runs with the same signature buffer and stack
pointer: each at the same tree, the measure being the trees left. -/
theorem trees_ct (hA : As p) (T : Thash4Impl p.n) (t4name ln : String)
    (hL : Verified AArch64.target (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code) (levelsContract p))
    (hLf : (Impl.SlhDsa.AArch64.Tree.levels ⟨p.n, p.len⟩ t4name T.code).noFrames = true)
    {S SG : Addr} {pk₁ a₁ sk₁ pk₂ a₂ sk₂ : List Byte} {ix₁ ix₂ : Nat → Nat} {t₀₁ t₀₂ : State}
    (M₁ : MC p S SG t₀₁) (M₂ : MC p S SG t₀₂) (hix₁ : ∀ i < p.k, ix₁ i < 2 ^ p.a)
    (hix₂ : ∀ i < p.k, ix₂ i < 2 ^ p.a) (hsp : t₀₁.sp = t₀₂.sp) (n : Nat) :
    RelCT isa (fun a b => TI p S SG pk₁ a₁ sk₁ ix₁ t₀₁ n a ∧ TI p S SG pk₂ a₂ sk₂ ix₂ t₀₂ n b)
      (.loop (Impl.SlhDsa.AArch64.Fors.treeBody ⟨p.n, p.len⟩ p.a p.k t4name ln T.code) (.nonzero .x .x9))
      fun a b => TL p S SG pk₁ a₁ sk₁ ix₁ t₀₁ p.k a ∧ TL p S SG pk₂ a₂ sk₂ ix₂ t₀₂ p.k b :=
  relLoop (fun m => decide (m ≠ 1)) (fun m => m - 1)
    (fun m => by
      refine RelCT.mono (P := fun a b => ∃ tt, tt < p.k ∧ TL p S SG pk₁ a₁ sk₁ ix₁ t₀₁ tt a ∧
          TL p S SG pk₂ a₂ sk₂ ix₂ t₀₂ tt b) (RelCT.exists_ fun tt => ?_) ?_ fun _ _ h => h
      · by_cases htt : tt < p.k
        · exact RelCT.mono (tree_ct hA T t4name ln hL hLf M₁ M₂ hix₁ hix₂ hsp htt) (fun a b h => ⟨h.2.1, h.2.2⟩)
            fun _ _ h => h
        · exact RelCT.of_false fun a b h => htt h.1
      · rintro a b ⟨⟨tt, h₁, h₂, ha⟩, ⟨tt', h₁', _, hb⟩⟩
        exact ⟨tt, by omega, ha, by rw [show tt = tt' by omega]; exact hb⟩)
    (tree_step T t4name ln hL hLf M₁ hix₁) (tree_step T t4name ln hL hLf M₂ hix₂) n

end VG.Proof.SlhDsa.AArch64.Fors
