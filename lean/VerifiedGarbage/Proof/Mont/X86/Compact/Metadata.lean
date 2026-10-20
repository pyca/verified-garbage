module

public import VerifiedGarbage.Proof.Mont.X86.Compact.Args
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.X86.Rt.Base

/-! # Prepared metadata is outside the compact multiplication's scratch -/

@[expose] public section
namespace VG.Proof.Mont.X86.Compact
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt

/-- Only the first 128 header bytes are needed by Montgomery multiplication. -/
structure Metadata (m : Mem) (W : Addr) (A : Nat → BitVec 32) (N S mo a b : Nat) : Prop where
  width : w32 m W 48 * 8 = 4 * N
  aIndex : (A 3).toNat < 8
  bIndex : (A 4).toNat < 8
  scratch : w32 m W 80 = (W.toNat + S) % 2 ^ 32
  modulus : w32 m W 64 = (W.toNat + mo) % 2 ^ 32
  left : w32 m W (64 + 8 * (A 3).toNat) = (W.toNat + a) % 2 ^ 32
  right : w32 m W (64 + 8 * (A 4).toNat) = (W.toNat + b) % 2 ^ 32

theorem Metadata.keep {m m' : Mem} {W : Addr} {A : Nat → BitVec 32} {N S mo a b x n : Nat}
    (h : Metadata m W A N S mo a b) (O : Outside W x n m m') (far : 128 ≤ x) :
    Metadata m' W A N S mo a b := by
  have keep : ∀ d, d + 4 ≤ 128 → w32 m' W d = w32 m W d := fun d hd => O.w32 (by omega) (by omega)
  refine ⟨?_, h.aIndex, h.bIndex, ?_, ?_, ?_, ?_⟩
  · rw [keep 48 (by decide)]; exact h.width
  · rw [keep 80 (by decide)]; exact h.scratch
  · rw [keep 64 (by decide)]; exact h.modulus
  · rw [keep _ (by have := h.aIndex; omega)]; exact h.left
  · rw [keep _ (by have := h.bIndex; omega)]; exact h.right

theorem Metadata.left_word {m : Mem} {W : Addr} {A : Nat → BitVec 32} {N S mo a b : Nat}
    (h : Metadata m W A N S mo a b) :
    m.readW (off W (64 + 8 * (A 3).toNat)) 32 = BitVec.ofNat 32 (W.toNat + a) := by
  apply BitVec.eq_of_toNat_eq
  exact h.left

theorem Metadata.right_ptr {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} {N S mo a b : Nat}
    (h : Metadata s.mem W A N S mo a b) (hw : Ws s W L) (ha : Args s W L A)
    (base : (A 0).toNat = W.toNat) (fit : 128 ≤ L) :
    WP isa (.block (Compact.operandPtr .ecx 4 .edx)) s fun u =>
      PtrAt u W .ecx b ∧ u.mem = s.mem ∧ Keeps [.ecx, .edx] s u := by
  refine WP.mono (operandPtr_ok hw ha base (by decide) (by decide) (by decide)
    (by have := h.bIndex; omega)) ?_
  rintro u ⟨P, M, K⟩
  refine ⟨?_, M, K⟩
  rw [PtrAt, P]
  exact h.right

theorem Metadata.modulus_ptr {s : State} {W : Addr} {L : Nat} {A : Nat → BitVec 32} {N S mo a b : Nat}
    (h : Metadata s.mem W A N S mo a b) (hw : Ws s W L) (ha : Args s W L A)
    (base : (A 0).toNat = W.toNat) (fit : 128 ≤ L) :
    WP isa (.block (Compact.arrayPtr .ecx 0)) s fun u =>
      PtrAt u W .ecx mo ∧ u.mem = s.mem ∧ Keeps [.ecx, .edx] s u := by
  refine WP.mono (arrayPtr_ok hw ha base (r := .ecx) (j := 0) (by omega)) ?_
  rintro u ⟨P, M, K⟩
  refine ⟨?_, M, K.mono (by decide)⟩
  rw [PtrAt, P]
  exact h.modulus

end VG.Proof.Mont.X86.Compact
