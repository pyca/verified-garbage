module

import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Parameters
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.Frame
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Body
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Locals

/-!
# Argon2 on PPC64LE: `scratch` in the derivation

`r31` points to `scratch` throughout the body. `wp_stscrw` and `wp_stscrd`
store a word or a doubleword there; `Inv.keeps` keeps the invariant and the
frame's variables through a call that writes only the first 832 bytes of
`scratch` and the calls' frames (`HPrime.Keeps`), and `repr_frame` a BLAKE2b
streaming state through writes outside it.
-/

@[expose] public section

namespace VG.Proof.Argon2.PPC64LE.Derive

open VG VG.PPC64LE
open VG.Proof.MdStream.PPC64LE (Upd Mupd wp_std wp_stw)
open VG.Spec.Blake2 (Repr b bytesAt)

/-- A BLAKE2b streaming state at `p` is kept by writes outside its 192 bytes. -/
theorem repr_frame {m m' : Mem} {rs : List Region} (f : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 192⟩ r) {h0 : Spec.Blake2.HashValue 64} {d : List Byte}
    (h : Repr b h0 m p d) : Repr b h0 m' p d :=
  Proof.Blake2.repr_congr' (by decide) (fun i hi => by
    have hi' : i < 192 := by simpa [Proof.Blake2.bufOff, Spec.Blake2.blockBytes] using hi
    exact f _ fun r hr hc => hd r hr _ (Offset.contains_base p (show i + 1 ≤ 192 by omega)
      (by omega)) hc) h

theorem finalHash_length (h0 : Spec.Blake2.HashValue 64) (d : List Byte) :
    (Spec.Blake2.finalHash b h0 d).length = 64 := by
  simp only [Spec.Blake2.finalHash, Proof.Argon2.wordList_length, Vector.length_toList]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := by
  rw [entry_wr, hp.wr]; simp

theorem mem_mem : memR s₀ ∈ (entry s₀).wr := by rw [entry_wr, hp.wr]; simp

theorem Inv.scr_in {s : State} (h : Inv s₀ s) : (⟨s.gpr .r31, 16384⟩ : Region) ∈ s.wr := by
  rw [h.r31, h.wr]; exact scr_mem hp

/-- `scratch` is outside the calls' frames. -/
theorem Inv.stk_scr {s : State} (h : Inv s₀ s) :
    (below s.sp 48).Disjoint ⟨s.gpr .r31, 16384⟩ := by
  rw [h.sp, h.r31, callR_eq]
  refine (hp.stk_all (scrR s₀) (by simp)).sub_left ?_
  have e : B s₀ = B s₀ + BitVec.ofNat 64 0 := (BitVec.add_zero _).symm
  show Region.Sub ⟨B s₀, 48⟩ _
  rw [e]; exact stk_sub (by decide)

omit hp in
/-- A part of `scratch`. -/
theorem scr_sub {o n : Nat} (h : o + n ≤ 16384) : Region.Sub ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

/-- A call that keeps the caller's registers and writes only `scratch` and
its frames keeps the invariant and the frame's variables. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : HPrime.Keeps s t) :
    Inv s₀ t ∧ ∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s d := by
  have hs : ∀ r ∈ [⟨s.gpr .r31, 832⟩, below s.sp 48],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨scrR s₀, by simp, ?_⟩
      rw [h.r31]; exact Region.sub_prefix (by decide)
    · exact ⟨callR s₀, by simp, by rw [h.sp, callR_eq]; exact fun _ h => h⟩
  refine ⟨h.step k.sp (k.regs _ (by decide)) (k.regs _ (by decide))
    (fun r hr => k.regs r (by revert hr; revert r; decide)) k.rd k.wr ?_,
    fun d h₁ h₂ => lw_keep hp k.frame hs h₁ h₂⟩
  refine k.frame.sub fun r hr => ?_
  obtain ⟨r', hr', hs'⟩ := hs r hr
  refine ⟨r', ?_, hs'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl | rfl <;> simp

/-- `stw r, o(r31)`, to `scratch`. -/
theorem wp_stscrw {s : State} (h : Inv s₀ s) {o : Nat} (ho : o + 4 ≤ 16384) (ho' : o < 2 ^ 15)
    {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (scrP s₀ + BitVec.ofNat 64 o) ((s.gpr r).setWidth 32) →
      t.gpr = s.gpr → (∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .w r .r31 o :: is)) s Q := by
  have hc : (scrR s₀).Contains (scrP s₀ + BitVec.ofNat 64 o) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_stw (a := scrP s₀ + BitVec.ofNat 64 o) ho' (by rw [h.r31])
    (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.mupd u ((Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc)) u.mem u.gpr
    (fun d h₁ h₂ => lw_keep hp f (fun r hr => ?_) h₁ h₂) f
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scrR s₀, by simp, scr_sub (by omega)⟩

/-- `std r, o(r31)`, to `scratch`. -/
theorem wp_stscrd {s : State} (h : Inv s₀ s) {o : Nat} (ho : o + 8 ≤ 16384) (ho' : o < 2 ^ 15)
    (ho4 : o % 4 = 0) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (scrP s₀ + BitVec.ofNat 64 o) (s.gpr r) →
      t.gpr = s.gpr → (∀ d, 32 ≤ d → d + 8 ≤ 336 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .d r .r31 o :: is)) s Q := by
  have hc : (scrR s₀).Contains (scrP s₀ + BitVec.ofNat 64 o) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_std (a := scrP s₀ + BitVec.ofNat 64 o) ⟨ho', ho4⟩ (by rw [h.r31])
    (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.mupd u ((Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc)) u.mem u.gpr
    (fun d h₁ h₂ => lw_keep hp f (fun r hr => ?_) h₁ h₂) f
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scrR s₀, by simp, scr_sub (by omega)⟩

/-- A store to the frame is outside `scratch`. -/
theorem loc_scr {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) {o n : Nat} (ho : o + n ≤ 16384) :
    Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 d, 8⟩ ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ :=
  (loc_disj hp h₁ h₂ (scrR s₀) (by simp)).sub_right (scr_sub ho)

omit hp in
/-- A store to the frame keeps what lies in `scratch`. -/
theorem frame_loc {m : Mem} {d : Nat} (v : BitVec 64) :
    Frame [⟨E s₀ + BitVec.ofNat 64 d, 8⟩] m (m.writeW (E s₀ + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

/-- A store to the frame keeps a streaming state in `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 336) (v : BitVec 64)
    {h0 : Spec.Blake2.HashValue 64} {data : List Byte} (h : Repr b h0 m (scrP s₀) data) :
    Repr b h0 (m.writeW (E s₀ + BitVec.ofNat 64 d) v) (scrP s₀) data :=
  repr_frame (frame_loc v) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := (loc_scr hp h₁ h₂ (o := 0) (n := 192) (by decide)).symm
    simpa using this) h

end

end VG.Proof.Argon2.PPC64LE.Derive
