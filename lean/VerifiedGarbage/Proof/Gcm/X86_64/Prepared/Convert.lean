import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Load
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.SetupP
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.LoopP
import VerifiedGarbage.Impl.AesGcm.X86_64.Prepared

/-! # Converting the cached powers in place at key setup -/

namespace VG.Proof.Gcm.X86_64.Prepared
open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt ctxH hpow PowersRepr PreparedPowersRepr)
open VG.Proof.Gcm.X86_64.Stitch (in_sub_int in_rdwr storesK_ok)
open VG.Proof.Gcm.X86_64.StitchZP (hInvF ones cvtPair_ok consts_ok vinsSelf_ok)
open VG.Proof.Gcm.X86_64.StitchZR (preparedPower_eq)
open VG.Impl.Gcm.X86_64.Pclmul (revMask xInv poly)
open VG.Impl.AesGcm.X86_64.Prepared (pair convert)
open VG.Proof.Gcm.X86_64.Pclmul (const_ok)

/-- One conversion changes only its 32 bytes and temporary vector registers. -/
theorem pair_ok (k : Nat) (s : State)
    (hin : InRegions s.wr (s.gpr .rdi) 1024) (hw : (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) (hk : k < 24)
    (m0 : ∀ l < 2, s.lane .xmm0 l = revMask)
    (c8 : ∀ l < 2, s.lane .xmm8 l = xInv) (c9 : ∀ l < 2, s.lane .xmm9 l = ones) :
    WP isa (.block (pair k)) s fun s' =>
      (∀ l < 2, s'.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (256+32*k+16*l)) 128 =
        hInvF (blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 (272+32*k-16*l)))) ∧
      Frame [⟨s.gpr .rdi + BitVec.ofNat 64 (256+32*k), 32⟩] s.mem s'.mem ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .xmm7 → r ≠ .xmm10 → r ≠ .xmm12 → ∀ l < 2, s'.lane r l = s.lane r l) := by
  rw [pair, WP.block_append_iff]
  refine WP.mono (cvtPair_ok (2*k+1) .xmm12 (by decide) (by decide) (by decide) (by decide) s m0 c8 c9
    (in_sub_int (in_rdwr hin) (by omega)) (in_sub_int (in_rdwr hin) (by omega))) fun s₁ ⟨v0, v1, f₁⟩ => ?_
  refine WP.mono (storesK_ok .rdi [.xmm12] (8+k) s₁ (fun j hj => by
    rw [f₁.gpr, f₁.wr]; exact in_sub_int hin (by simp only [List.length_singleton] at hj; omega))
    (by rw [f₁.gpr]; simp only [List.length_singleton]; omega)) fun s' ⟨v, f, g, rd, wr, lanes⟩ => ?_
  rw [f₁.gpr, f₁.mem] at f
  have eo : 32*(8+k) = 256+32*k := by omega
  simp only [List.length_singleton, Nat.mul_one, eo] at f
  refine ⟨fun l hl => ?_, f, by rw [g, f₁.gpr], by rw [rd, f₁.rd], by rw [wr, f₁.wr],
    fun r h7 h10 h12 l hl => by rw [lanes, f₁.lane r (by simp [h7, h10, h12]) l hl]⟩
  have e := v 0 (by simp) l hl
  rw [f₁.gpr, Nat.add_zero, eo] at e
  rw [e]
  simp only [List.getElem_cons_zero]
  rcases (by omega : l = 0 ∨ l = 1) with rfl | rfl
  · rw [v0, BitVec.ofInt_natCast, show 256+16*(2*k+1) = 272+32*k-16*0 by omega]
  · rw [v1, BitVec.ofInt_natCast, show 240+16*(2*k+1) = 272+32*k-16*1 by omega]

/-- Only completed pairs differ from the original context. -/
structure Inv (s₀ : State) (j : Nat) (s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 32*j⟩] s₀.mem s.mem
  pairs : ∀ k < j, ∀ l < 2,
    s.mem.readW (s₀.gpr .rdi + BitVec.ofNat 64 (256+32*k+16*l)) 128 =
      hInvF (hpow (ctxH s₀.mem (s₀.gpr .rdi)) (2*k+2-l))
  m0 : ∀ l < 2, s.lane .xmm0 l = revMask
  c8 : ∀ l < 2, s.lane .xmm8 l = xInv
  c9 : ∀ l < 2, s.lane .xmm9 l = ones

/-- Advancing one pair preserves both the original suffix and the prepared prefix. -/
theorem step_ok {s₀ s : State} (hp : PowersRepr s₀.mem (s₀.gpr .rdi))
    (hin : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hw : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) {j : Nat} (hj : j < 24) (I : Inv s₀ j s) :
    WP isa (.block (pair j)) s (Inv s₀ (j+1)) := by
  refine WP.mono (pair_ok j s (by rw [I.gpr, I.wr]; exact hin)
    (by rw [I.gpr]; exact hw) hj I.m0 I.c8 I.c9) fun s' ⟨v, f, g, rd, wr, lanes⟩ => ?_
  rw [I.gpr] at v f
  have raw (l : Nat) (hl : l < 2) :
      blockAt s.mem (s₀.gpr .rdi + BitVec.ofNat 64 (272+32*j-16*l)) =
        hpow (ctxH s₀.mem (s₀.gpr .rdi)) (2*j+2-l) := by
    rw [VG.Proof.Aes.X86_64.AesNi.blockAt_frame I.frame (fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inr (by omega)) (by omega) (by omega)),
      show 272+32*j-16*l = 256+16*(2*j+1-l) by omega, hp _ (by omega)]
    congr 1; omega
  refine ⟨by rw [g, I.gpr], by rw [rd, I.rd], by rw [wr, I.wr],
    (StitchZP.frame_sub (Nat.le_refl _) (by omega) I.frame).trans
      (StitchZP.frame_sub (by omega) (by omega) f), fun k hk l hl => ?_,
    fun l hl => by rw [lanes _ (by decide) (by decide) (by decide) l hl]; exact I.m0 l hl,
    fun l hl => by rw [lanes _ (by decide) (by decide) (by decide) l hl]; exact I.c8 l hl,
    fun l hl => by rw [lanes _ (by decide) (by decide) (by decide) l hl]; exact I.c9 l hl⟩
  by_cases hkj : k = j
  · subst k
    rw [v l hl, raw l hl]
  · rw [StitchZP.keepAt f (by omega) (by omega) (by omega)]
    exact I.pairs k (by omega) l hl

/-- Convert all pairs up to `n`, in order. -/
theorem run_ok {s₀ : State} (hp : PowersRepr s₀.mem (s₀.gpr .rdi))
    (hin : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hw : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64)
    (m0 : ∀ l < 2, s₀.lane .xmm0 l = revMask)
    (c8 : ∀ l < 2, s₀.lane .xmm8 l = xInv) (c9 : ∀ l < 2, s₀.lane .xmm9 l = ones) :
    ∀ n, n ≤ 24 → WP isa (.block ((List.range n).flatMap pair)) s₀ (Inv s₀ n)
  | 0, _ => by
    rw [List.range_zero, List.flatMap_nil]
    exact WP.block_nil ⟨rfl, rfl, rfl, Frame.refl _ _, fun k hk => absurd hk (by omega), m0, c8, c9⟩
  | n+1, hn => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (run_ok hp hin hw m0 c8 c9 n (by omega)) fun s I => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact step_ok hp hin hw (by omega) I

/-- The complete key-setup conversion writes only the power table. -/
theorem convert_ok (s₀ : State) (hin : InRegions s₀.wr (s₀.gpr .rdi) 1024)
    (hw : (s₀.gpr .rdi).toNat + 1024 ≤ 2 ^ 64) (hp : PowersRepr s₀.mem (s₀.gpr .rdi)) :
    WP isa (.block convert) s₀ fun s =>
      PreparedPowersRepr s.mem (s₀.gpr .rdi) ∧
      Frame [⟨s₀.gpr .rdi + BitVec.ofNat 64 256, 768⟩] s₀.mem s.mem ∧
      (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr := by
  simp only [convert, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s₀ (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  have o₁₂ := o₁.trans o₂
  rw [WP.block_append_iff, show ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] :
    List Instr) = [.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1)] ++ [.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1)] from rfl,
    WP.block_append_iff]
  refine WP.mono (vinsSelf_ok .xmm0 s₂) fun s₃ ⟨v₃, f₃⟩ => ?_
  refine WP.mono (vinsSelf_ok .xmm1 s₃) fun s₄ ⟨v₄, f₄⟩ => ?_
  have m0 : ∀ l < 2, s₄.lane .xmm0 l = revMask := fun l hl => by
    rw [f₄.lane _ (by decide) l hl, v₃ l hl]; show s₂.xmm .xmm0 = _; rw [o₂.xmm _ (by decide), c₁]; rfl
  have m1 : ∀ l < 2, s₄.lane .xmm1 l = poly := fun l hl => by
    rw [v₄ l hl, f₃.lane _ (by decide) 0 (by decide)]; exact c₂
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₄ m1) fun s₅ ⟨c8, c9, f₅⟩ => ?_
  have g₅ : ∀ r, r ≠ .rax → s₅.gpr r = s₀.gpr r := fun r hr => by rw [f₅.gpr, f₄.gpr, f₃.gpr, o₁₂.gpr r hr]
  have mm₅ : s₅.mem = s₀.mem := by rw [f₅.mem, f₄.mem, f₃.mem, o₁₂.mem]
  have rd₅ : s₅.rd = s₀.rd := by rw [f₅.rd, f₄.rd, f₃.rd, o₁₂.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [f₅.wr, f₄.wr, f₃.wr, o₁₂.wr]
  refine WP.mono (run_ok (s₀ := s₅) (by rw [mm₅, g₅ _ (by decide)]; exact hp)
    (by rw [wr₅, g₅ _ (by decide)]; exact hin)
    (by rw [g₅ _ (by decide)]; exact hw)
    (fun l hl => by rw [f₅.lane _ (by decide) l hl]; exact m0 l hl) c8 c9 24 (Nat.le_refl _))
    fun s I => ?_
  have hH : ctxH s.mem (s₅.gpr .rdi) = ctxH s₅.mem (s₅.gpr .rdi) :=
    VG.Proof.Aes.X86_64.AesNi.blockAt_frame I.frame fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact Offset.disjoint _ (.inl (by decide)) (by decide) (by decide)
  have powers : PreparedPowersRepr s.mem (s₅.gpr .rdi) := by
    intro k hk
    rw [preparedPower_eq, preparedPower_eq, hH]
    refine ⟨?_, ?_⟩
    · simpa only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero] using I.pairs k hk 0 (by decide)
    · have v := I.pairs k hk 1 (by decide)
      rw [show 256+32*k+16*1 = 272+32*k by omega,
        show 2*k+2-1 = 2*k+1 by omega] at v
      exact v
  rw [g₅ _ (by decide)] at powers
  have f := I.frame
  rw [g₅ _ (by decide), mm₅] at f
  exact ⟨powers, f, fun r hr => by rw [I.gpr, g₅ r hr],
    by rw [I.rd, rd₅], by rw [I.wr, wr₅]⟩

end VG.Proof.Gcm.X86_64.Prepared
