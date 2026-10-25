module

public import VerifiedGarbage.Impl.Words.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Framework.RISCV64.Keep
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Stack frames of any size (RISC-V)

Untrusted: everything here is checked by Lean. `bigFrame_wp`: the body of
`bigFrame n` runs from a state `FrameAt n s` of the state `s` before it:
the same registers, memory and readable regions, the stack pointer `n`
bytes lower, and writable regions that add, to those of `s`, the frame's
bytes, an access within a 16-byte aligned chunk of it at a time
(`FrameAt.inFrame`), and its lowest 2032 bytes (or all of it) as one region
(`FrameAt.low`). If the body keeps the permissions and the stack
pointer, as all code does, the frame ends with those of `s`.
-/

@[expose] public section

namespace VG.RISCV64

open VG.Impl.Words.RISCV64

/-- The state `t` in which the body of a frame of `n` bytes starts, from `s`:
its lowest `min n 2032` bytes are one writable region. -/
structure FrameAt (n : Nat) (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  sp : t.sp = s.sp - BitVec.ofNat 64 n
  wr : ∃ ws, t.wr = ws ++ s.wr
  low : 0 < n → (⟨t.sp, min n 2032⟩ : Region) ∈ t.wr
  inFrame : ∀ o w, 0 < w → o + w ≤ n → o % 16 + w ≤ 16 →
    InRegions t.wr (t.sp + BitVec.ofNat 64 o) w

theorem FrameAt.refl (s : State) : FrameAt 0 s s :=
  ⟨rfl, rfl, rfl, by simp, ⟨[], rfl⟩, fun h => absurd h (by decide), fun _ _ h0 h _ => absurd h (by omega)⟩

/-- A frame of `k` bytes around one of `n`, from `allocd k s`. -/
theorem FrameAt.alloc {n k : Nat} {s t : State} (h : FrameAt n (allocd k s) t) (hk : k % 16 = 0)
    (hn : n % 16 = 0) (hsp : n + k ≤ s.sp.toNat) (hk' : k ≤ 2032) (hn' : n = 0 ∨ 2032 ≤ n) :
    FrameAt (n + k) s t := by
  obtain ⟨g, m, r, sp, ⟨ws, hw⟩, lo, f⟩ := h
  have hb : s.sp - BitVec.ofNat 64 k = t.sp + BitVec.ofNat 64 n := by
    rw [sp]; simp only [allocd, BitVec.sub_add_cancel]
  have hmem : (⟨s.sp - BitVec.ofNat 64 k, k⟩ : Region) ∈ t.wr := by rw [hw]; simp [allocd]
  refine ⟨g, m, r, ?_, ⟨ws ++ [⟨s.sp - BitVec.ofNat 64 k, k⟩], by rw [hw]; simp [allocd]⟩, fun hp => ?_, ?_⟩
  · rw [sp]
    apply BitVec.eq_of_toNat_eq
    simp only [allocd, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  · rcases hn' with h0 | h0
    · subst h0
      have e : s.sp - BitVec.ofNat 64 k = t.sp := by rw [hb]; simp
      rw [Nat.zero_add, Nat.min_eq_left hk', ← e]
      exact hmem
    · rw [show min (n + k) 2032 = min n 2032 by omega]
      exact lo (by omega)
  · intro o w h0 ho hc
    by_cases h1 : o + w ≤ n
    · exact f o w h0 h1 hc
    · have : n ≤ o := by omega
      refine ⟨_, hmem, ?_⟩
      rw [hb]
      exact Offset.contains _ this (by omega) (by omega)

theorem chunks_wp {body : Prog isa} :
    ∀ (q : Nat) (s : State) (Q : State → Prop), 2032 * q ≤ s.sp.toNat →
    (∀ t, FrameAt (2032 * q) s t → WP isa body t fun s₂ => Q { s₂ with sp := s.sp, wr := s.wr }) →
    WP isa (chunks q body) s Q
  | 0, s, Q, _, hb => by
    refine WP.mono (WP.rdwr (hb s (FrameAt.refl s))) fun s₂ ⟨h, _, hw, hs⟩ => ?_
    have e : { s₂ with sp := s.sp, wr := s.wr } = s₂ := by rw [← hw, ← hs]
    rwa [e] at h
  | q + 1, s, Q, hsp, hb => by
    unfold chunks
    refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega) ?_
    have hsp' : 2032 * q ≤ (allocd 2032 s).sp.toNat := by
      simp only [allocd]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
      omega
    refine chunks_wp q (allocd 2032 s) (fun x => Q (freed 2032 x)) hsp' fun t ht => ?_
    have hf := FrameAt.alloc ht (by decide) (by omega) (by omega) (by decide) (by omega)
    rw [show 2032 * q + 2032 = 2032 * (q + 1) by omega] at hf
    refine WP.mono (hb t hf) fun s₂ h => ?_
    have e : freed 2032 { s₂ with sp := (allocd 2032 s).sp, wr := (allocd 2032 s).wr } =
        { s₂ with sp := s.sp, wr := s.wr } := by
      simp only [freed, allocd, List.tail_cons, BitVec.sub_add_cancel]
    rwa [e]

theorem bigFrame_wp {n : Nat} {body : Prog isa} {s : State} {Q : State → Prop} (hn : n % 16 = 0)
    (hsp : n ≤ s.sp.toNat)
    (hb : ∀ t, FrameAt n s t → WP isa body t fun s₂ => Q { s₂ with sp := s.sp, wr := s.wr }) :
    WP isa (bigFrame n body) s Q := by
  have e : 2032 * (n / 2032) + n % 2032 = n := Nat.div_add_mod n 2032
  unfold bigFrame
  split
  · rename_i h0
    refine chunks_wp (n / 2032) s Q (by omega) fun t ht => hb t ?_
    rwa [show 2032 * (n / 2032) = n by omega] at ht
  · rename_i h0
    have hr : n % 2032 < 2032 := Nat.mod_lt _ (by decide)
    refine WP.alloc ⟨by omega, by omega, by omega⟩ (by omega) ?_
    have hsp' : 2032 * (n / 2032) ≤ (allocd (n % 2032) s).sp.toNat := by
      simp only [allocd]
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
      omega
    refine chunks_wp (n / 2032) (allocd (n % 2032) s) (fun x => Q (freed (n % 2032) x)) hsp' fun t ht => ?_
    have hf := FrameAt.alloc ht (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [e] at hf
    refine WP.mono (hb t hf) fun s₂ h => ?_
    have e : freed (n % 2032) { s₂ with sp := (allocd (n % 2032) s).sp, wr := (allocd (n % 2032) s).wr } =
        { s₂ with sp := s.sp, wr := s.wr } := by
      simp only [freed, allocd, List.tail_cons, BitVec.sub_add_cancel]
    rwa [e]

end VG.RISCV64
