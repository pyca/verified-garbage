module

public import VerifiedGarbage.Proof.Dsa.X86.RandomFrame
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# The leading byte's mask, and the check that q > 1 (x86)

`mask` leaves in `ebp` the mask of the significant bits of the public
leading byte in `edx` (`maskValue`), branching on that byte;
`prepareFinish` stores it and sets `eax = 1` exactly when q > 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.X86 VG.Impl.Dsa.X86.Random

/-- The mask `mask` selects for the leading byte `n`. -/
def maskValue (n : Nat) : BitVec 32 :=
  if n < 2 then 1 else if n < 4 then 3 else if n < 8 then 7 else
  if n < 16 then 15 else if n < 32 then 31 else if n < 64 then 63 else
  if n < 128 then 127 else 255

/-- The selected mask keeps exactly the significant bits of a nonzero byte. -/
theorem maskValue_eq (n : Nat) (hpos : 0 < n) (hbound : n < 256) :
    maskValue n = BitVec.ofNat 32 (2 ^ (n.log2 + 1) - 1) := by
  have key : ∀ k, 2 ^ k ≤ n → n < 2 ^ (k + 1) → n.log2 = k := fun k h₁ h₂ =>
    (Nat.log2_eq_iff (by omega)).mpr ⟨h₁, h₂⟩
  unfold maskValue
  split
  · rw [key 0 (show 1 ≤ n by omega) (by omega)]; rfl
  split
  · rw [key 1 (by omega) (by omega)]; rfl
  split
  · rw [key 2 (by omega) (by omega)]; rfl
  split
  · rw [key 3 (by omega) (by omega)]; rfl
  split
  · rw [key 4 (by omega) (by omega)]; rfl
  split
  · rw [key 5 (by omega) (by omega)]; rfl
  split
  · rw [key 6 (by omega) (by omega)]; rfl
  · rw [key 7 (by omega) (by omega)]; rfl

/-- One threshold of the mask. -/
theorem maskStep_ok {th bits n : Nat} (hth : th < 2 ^ 32) {s u : State} {Q : State → Prop}
    (hd : (u.gpr .edx).toNat = n) (hk : Keeps [.ebp] s u) (hm : u.mem = s.mem)
    (k : ∀ t, t.gpr .ebp = (if n < th then BitVec.ofNat 32 bits else u.gpr .ebp) →
      (t.gpr .edx).toNat = n → Keeps [.ebp] s t → t.mem = s.mem → Q t) :
    WP isa (maskStep th bits) u Q := by
  unfold maskStep
  refine WP.seq (wp_cmpi fun u₁ f₁ c₁ _ => WP.block_nil ?_)
  rw [hd, toNat_ofNat_lt hth] at c₁
  have k₁ : Keeps [.ebp] s u₁ := hk.trans (f₁.keeps _)
  by_cases h : n < th
  · refine WP.ite true (by simp only [eval, c₁, h, decide_true]) (fun _ =>
      wp_movS rfl fun u₂ v₂ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
    refine k u₂ (by rw [v₂.gpr]; simp only [h, ↓reduceIte]) (by rw [v₂.other _ (by decide), f₁.gpr, hd])
      (k₁.trans v₂.keeps) (by rw [v₂.mem, f₁.mem, hm])
  · refine WP.ite false (by simp only [eval, c₁, h, decide_false]) (fun e => Bool.noConfusion e)
      (fun _ => WP.block_nil ?_)
    exact k u₁ (by simp only [h, ↓reduceIte]; rw [f₁.gpr]) (by rw [f₁.gpr, hd]) k₁ (by rw [f₁.mem, hm])

theorem mask_ok {s : State} {n : Nat} (hd : (s.gpr .edx).toNat = n) :
    WP isa mask s fun t => t.gpr .ebp = maskValue n ∧ t.mem = s.mem ∧ Keeps [.ebp] s t := by
  unfold mask
  refine WP.seq (wp_movS rfl fun s₀ u₀ _ => WP.block_nil ?_)
  have d₀ : (s₀.gpr .edx).toNat = n := by rw [u₀.other _ (by decide), hd]
  refine WP.seq (maskStep_ok (by decide) d₀ u₀.keeps u₀.mem fun s₁ e₁ d₁ k₁ m₁ =>
    WP.seq (maskStep_ok (by decide) d₁ k₁ m₁ fun s₂ e₂ d₂ k₂ m₂ =>
    WP.seq (maskStep_ok (by decide) d₂ k₂ m₂ fun s₃ e₃ d₃ k₃ m₃ =>
    WP.seq (maskStep_ok (by decide) d₃ k₃ m₃ fun s₄ e₄ d₄ k₄ m₄ =>
    WP.seq (maskStep_ok (by decide) d₄ k₄ m₄ fun s₅ e₅ d₅ k₅ m₅ =>
    WP.seq (maskStep_ok (by decide) d₅ k₅ m₅ fun s₆ e₆ d₆ k₆ m₆ =>
    maskStep_ok (by decide) d₆ k₆ m₆ fun s₇ e₇ _ k₇ m₇ => ?_))))))
  refine ⟨?_, m₇, k₇⟩
  rw [e₇, e₆, e₅, e₄, e₃, e₂, e₁, u₀.gpr]
  rfl

/-- Store the mask, and set `eax = 1` exactly when the scan's width or
leading byte is at least two. -/
theorem prepareFinish_ok {s : State} {B : Addr} (hf : RF s B) {w : Nat} {b : Byte} (hw : w < 2 ^ 32)
    (hb : s.gpr .ebx = BitVec.ofNat 32 w) (hd : s.gpr .edx = b.setWidth 32) :
    WP isa prepareFinish s fun t =>
      t.gpr .eax = (if 2 ≤ w ∨ 2 ≤ b.toNat then 1 else 0) ∧
      t.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) ∧
      Keeps [.eax, .ebp] s t := by
  have hb8 : (b.setWidth 32).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le b.isLt (by decide : 2 ^ 8 ≤ 2 ^ 32))]
  unfold prepareFinish
  refine WP.seq (WP.mono (mask_ok (n := b.toNat) (by rw [hd, hb8])) fun s₁ ⟨e₁, m₁, k₁⟩ => ?_)
  have f₁ := hf.of_keeps k₁
  refine WP.seq (wp_storeS (f₁.ea (by decide)) (f₁.write (by decide)) fun s₂ u₂ =>
    wp_movS rfl fun s₃ u₃ _ => wp_cmpi fun s₄ g₄ c₄ _ => WP.block_nil ?_)
  have hbx : s₃.gpr .ebx = BitVec.ofNat 32 w := by
    rw [u₃.other _ (by decide), u₂.gpr, k₁.1 _ (by decide), hb]
  rw [hbx, toNat_ofNat_lt hw, show (2 : BitVec 32).toNat = 2 from rfl] at c₄
  have k₄ : Keeps [.eax, .ebp] s s₄ :=
    ((k₁.mono (by decide)).trans (u₂.keeps _)).trans ((u₃.keeps.mono (by decide)).trans (g₄.keeps _))
  have hm₄ : s₄.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) := by
    rw [g₄.mem, u₃.mem, u₂.mem, e₁, m₁]
  -- The second test, from the first's `eax`.
  have second : ∀ u : State, u.gpr .eax = (if 2 ≤ w then 1 else 0) → Keeps [.eax, .ebp] s u →
      u.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) →
      WP isa (.seq (.block [.alu .cmp .edx (.imm 2)])
        (.ite .ae (.block [.mov .eax (.imm 1)]) (.block []))) u fun t =>
        t.gpr .eax = (if 2 ≤ w ∨ 2 ≤ b.toNat then 1 else 0) ∧
        t.mem = s.mem.writeW (off B oMask) (maskValue b.toNat) ∧ Keeps [.eax, .ebp] s t := by
    intro u hu ku mu
    refine WP.seq (wp_cmpi fun u₁ g₁ c₁ _ => WP.block_nil ?_)
    rw [ku.1 _ (by decide), hd, hb8, show (2 : BitVec 32).toNat = 2 from rfl] at c₁
    have ku₁ : Keeps [.eax, .ebp] s u₁ := ku.trans (g₁.keeps _)
    by_cases h2 : 2 ≤ b.toNat
    · refine WP.ite true (by simp only [eval, c₁, Nat.not_lt.mpr h2, decide_false, Option.map_some,
        Bool.not_false]) (fun _ => wp_movS rfl fun u₂ v₂ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e)
      exact ⟨by rw [v₂.gpr]; simp only [h2, or_true, ↓reduceIte], by rw [v₂.mem, g₁.mem, mu],
        ku₁.trans (v₂.keeps.mono (by decide))⟩
    · refine WP.ite false (by simp only [eval, c₁, Nat.not_le.mp h2, decide_true, Option.map_some,
        Bool.not_true]) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_)
      refine ⟨?_, by rw [g₁.mem, mu], ku₁⟩
      rw [g₁.gpr, hu]
      by_cases hw2 : 2 ≤ w
      · simp only [hw2, true_or, ↓reduceIte]
      · simp only [hw2, h2, or_self, ↓reduceIte]
  by_cases hw2 : 2 ≤ w
  · refine WP.seq (WP.ite true (by simp only [eval, c₄, Nat.not_lt.mpr hw2, decide_false, Option.map_some,
      Bool.not_false]) (fun _ => wp_movS rfl fun s₅ u₅ _ => WP.block_nil ?_) (fun e => Bool.noConfusion e))
    exact second s₅ (by rw [u₅.gpr]; simp only [hw2, ↓reduceIte]) (k₄.trans (u₅.keeps.mono (by decide)))
      (by rw [u₅.mem, hm₄])
  · refine WP.seq (WP.ite false (by simp only [eval, c₄, Nat.not_le.mp hw2, decide_true, Option.map_some,
      Bool.not_true]) (fun e => Bool.noConfusion e) (fun _ => WP.block_nil ?_))
    exact second s₄ (by rw [g₄.gpr, u₃.gpr]; simp only [hw2, ↓reduceIte]) k₄ hm₄

end VG.Proof.Dsa.X86
