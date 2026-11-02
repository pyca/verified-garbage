module

import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Parameters
public import VerifiedGarbage.Proof.Argon2.RISCV64.HPrime.Frame
import VerifiedGarbage.Proof.Blake2.Scratch
import VerifiedGarbage.Proof.Argon2.HPrime
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Body
public import VerifiedGarbage.Proof.Argon2.RISCV64.Ops
import VerifiedGarbage.Proof.Argon2.RISCV64.Derive.Locals

/-!
# Argon2 on RISC-V: `scratch` in the derivation

`s4` points to `scratch` throughout the body. `wp_stscrw` and `wp_stscrd`
store a word or a doubleword there; `Inv.keeps` keeps the invariant and the
frame's variables through a call that writes only the first 832 bytes of
`scratch` (`HPrime.Keeps`), and `repr_frame` a BLAKE2b streaming state
through writes outside it.
-/

@[expose] public section

namespace VG.Proof.Argon2.RISCV64.Derive

open VG VG.RISCV64
open VG.RISCV64.Wp (Upd Mupd wp_sd)
open VG.Proof.Argon2.RISCV64 (wp_sw)
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

/-- An offset of an aligned pointer, aligned. -/
theorem al_add {p : Addr} {o k : Nat} (hk : k ∣ 16) (hp : p.toNat % 16 % k = 0 ∨ p.toNat % k = 0)
    (ho : o % k = 0) : (p + BitVec.ofNat 64 o).toNat % k = 0 := by
  have h64 : k ∣ 2 ^ 64 := Nat.dvd_trans hk (by decide)
  have hp' : p.toNat % k = 0 := by
    rcases hp with h | h
    · rwa [Nat.mod_mod_of_dvd _ hk] at h
    · exact h
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ h64, Nat.add_mod,
    Nat.mod_mod_of_dvd _ h64, ho, hp', Nat.add_zero, Nat.zero_mod]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_mem : scrR s₀ ∈ (entry s₀).wr := by
  rw [entry_wr, hp.wr]; simp

theorem mem_mem : memR s₀ ∈ (entry s₀).wr := by rw [entry_wr, hp.wr]; simp

theorem Inv.scr_in {s : State} (h : Inv s₀ s) : (⟨s.gpr .s4, 16384⟩ : Region) ∈ s.wr := by
  rw [h.s4, h.wr]; exact scr_mem hp

omit hp in
/-- A part of `scratch`. -/
theorem scr_sub {o n : Nat} (h : o + n ≤ 16384) : Region.Sub ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ (scrR s₀) :=
  Offset.sub_base _ h

omit hp in
theorem Inv.scr_al {s : State} (h : Inv s₀ s) {o k : Nat} (hk : k ∣ 8) (ho : o % k = 0) :
    (scrP s₀ + BitVec.ofNat 64 o).toNat % k = 0 :=
  al_add (Nat.dvd_trans hk (by decide)) (.inr (Nat.mod_eq_zero_of_dvd
    (Nat.dvd_trans hk (Nat.dvd_of_mod_eq_zero h.sal)))) ho

/-- A call that keeps the caller's registers and writes only `scratch` keeps
the invariant and the frame's variables. -/
theorem Inv.keeps {s t : State} (h : Inv s₀ s) (k : HPrime.Keeps s t) :
    Inv s₀ t ∧ ∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d := by
  have hs : ∀ r ∈ [(⟨s.gpr .s4, 832⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀], Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    refine ⟨scrR s₀, by simp, ?_⟩
    rw [h.s4]; exact Region.sub_prefix (by decide)
  refine ⟨h.step k.sp (k.regs _ (by decide)) (k.regs _ (by decide)) (k.regs _ (by decide))
    (fun r hr => k.regs r (by revert hr; revert r; decide)) k.rd k.wr ?_,
    fun d h₂ => lw_keep hp k.frame hs h₂⟩
  refine k.frame.sub fun r hr => ?_
  obtain ⟨r', hr', hs'⟩ := hs r hr
  refine ⟨r', ?_, hs'⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with rfl | rfl | rfl <;> simp

/-- `sw r, o(s4)`, to `scratch`. -/
theorem wp_stscrw {s : State} (h : Inv s₀ s) {o : Nat} (ho : o + 4 ≤ 16384) (ho' : o < 2048)
    (ho4 : o % 4 = 0) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (scrP s₀ + BitVec.ofNat 64 o) ((s.gpr r).setWidth 32) →
      t.gpr = s.gpr → (∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 4⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .w r .s4 o :: is)) s Q := by
  have hc : (scrR s₀).Contains (scrP s₀ + BitVec.ofNat 64 o) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_sw (a := scrP s₀ + BitVec.ofNat 64 o) ho' (by rw [h.s4]) (h.scr_al (by decide) ho4)
    (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 4⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.mupd u ((Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc)) u.mem u.gpr
    (fun d h₂ => lw_keep hp f (fun r hr => ?_) h₂) f
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scrR s₀, by simp, scr_sub (by omega)⟩

/-- `sd r, o(s4)`, to `scratch`. -/
theorem wp_stscrd {s : State} (h : Inv s₀ s) {o : Nat} (ho : o + 8 ≤ 16384) (ho' : o < 2048)
    (ho8 : o % 8 = 0) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (scrP s₀ + BitVec.ofNat 64 o) (s.gpr r) →
      t.gpr = s.gpr → (∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .d r .s4 o :: is)) s Q := by
  have hc : (scrR s₀).Contains (scrP s₀ + BitVec.ofNat 64 o) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_sd (a := scrP s₀ + BitVec.ofNat 64 o) ho' (by rw [h.s4]) (h.scr_al (by decide) ho8)
    (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨scrP s₀ + BitVec.ofNat 64 o, 8⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.mupd u ((Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc)) u.mem u.gpr
    (fun d h₂ => lw_keep hp f (fun r hr => ?_) h₂) f
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scrR s₀, by simp, scr_sub (by omega)⟩

/-- `sd r, o(b)`, to `scratch`, through a register `b` pointing `B` bytes into it. -/
theorem wp_stscrb {s : State} (h : Inv s₀ s) {b : Reg} {B : Nat}
    (hb : s.gpr b = scrP s₀ + BitVec.ofNat 64 B) {o : Nat} (ho : B + o + 8 ≤ 16384) (ho' : o < 2048)
    (ho8 : (B + o) % 8 = 0) {r : Reg} {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.mem = s.mem.writeW (scrP s₀ + BitVec.ofNat 64 (B + o)) (s.gpr r) →
      t.gpr = s.gpr → (∀ d, d + 8 ≤ 320 → lw s₀ t d = lw s₀ s d) →
      Frame [⟨scrP s₀ + BitVec.ofNat 64 (B + o), 8⟩] s.mem t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store .d r b o :: is)) s Q := by
  have hc : (scrR s₀).Contains (scrP s₀ + BitVec.ofNat 64 (B + o)) 8 :=
    Offset.contains_base _ (by omega) (by omega)
  refine wp_sd (a := scrP s₀ + BitVec.ofNat 64 (B + o)) ho'
    (by rw [hb, BitVec.add_assoc, BitVec.ofNat_add_ofNat]) (h.scr_al (by decide) ho8)
    (by rw [h.wr]; exact ⟨scrR s₀, scr_mem hp, hc⟩) fun t u => ?_
  have f : Frame [⟨scrP s₀ + BitVec.ofNat 64 (B + o), 8⟩] s.mem t.mem := by
    rw [u.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine k t (h.mupd u ((Frame.refl _ _).writeW (r := scrR s₀) (by simp) _ hc)) u.mem u.gpr
    (fun d h₂ => lw_keep hp f (fun r hr => ?_) h₂) f
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨scrR s₀, by simp, scr_sub (by omega)⟩

/-- A store to the frame is outside `scratch`. -/
theorem loc_scr {d : Nat} (h₂ : d + 8 ≤ 320) {o n : Nat} (ho : o + n ≤ 16384) :
    Region.Disjoint ⟨E s₀ + BitVec.ofNat 64 d, 8⟩ ⟨scrP s₀ + BitVec.ofNat 64 o, n⟩ :=
  (loc_disj hp h₂ (scrR s₀) (by simp)).sub_right (scr_sub ho)

omit hp in
/-- A store to the frame keeps what lies in `scratch`. -/
theorem frame_loc {m : Mem} {d : Nat} (v : BitVec 64) :
    Frame [⟨E s₀ + BitVec.ofNat 64 d, 8⟩] m (m.writeW (E s₀ + BitVec.ofNat 64 d) v) :=
  (Frame.refl _ m).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)

/-- A store to the frame keeps a streaming state in `scratch`. -/
theorem repr_loc {m : Mem} {d : Nat} (h₂ : d + 8 ≤ 320) (v : BitVec 64)
    {h0 : Spec.Blake2.HashValue 64} {data : List Byte} (h : Repr b h0 m (scrP s₀) data) :
    Repr b h0 (m.writeW (E s₀ + BitVec.ofNat 64 d) v) (scrP s₀) data :=
  repr_frame (frame_loc v) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := (loc_scr hp h₂ (o := 0) (n := 192) (by decide)).symm
    simpa using this) h

end

end VG.Proof.Argon2.RISCV64.Derive
