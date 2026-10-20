module
public import VerifiedGarbage.Impl.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words

import VerifiedGarbage.Proof.Bignum.X86.ReverseByteStep
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.Wp

/-! # Runtime endian conversion, with byte-exact output and memory preservation -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86
open VG.X86.Wp (ofNat_beq_zero)
open VG.Proof.Mont.X86

def byteAddr (p : BitVec 32) : Addr := p.setWidth 64

/-- The source pointer starts at the last byte; the destination starts at the first.
The address conditions also allow a caller to use subranges of a larger workspace. -/
structure ReverseCtx (s : State) (src dst : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readable : ∀ i < n, InRegions (s.rd ++ s.wr) (byteAddr (src - BitVec.ofNat 32 i)) 1
  writable : ∀ i < n, InRegions s.wr (byteAddr (dst + BitVec.ofNat 32 i)) 1
  separate : ∀ i < n, ∀ j < n,
    byteAddr (src - BitVec.ofNat 32 i) ≠ byteAddr (dst + BitVec.ofNat 32 j)
  distinct : ∀ i < n, ∀ j < n,
    byteAddr (dst + BitVec.ofNat 32 i) = byteAddr (dst + BitVec.ofNat 32 j) → i = j

structure ReverseInv (s0 : State) (src dst : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  source : s.gpr .esi = src - BitVec.ofNat 32 i
  dest : s.gpr .ebx = dst + BitVec.ofNat 32 i
  count : s.gpr .ecx = BitVec.ofNat 32 (n - i)
  copied : ∀ j < i, s.mem (byteAddr (dst + BitVec.ofNat 32 j)) =
    s0.mem (byteAddr (src - BitVec.ofNat 32 j))
  outside : ∀ a, (∀ j < i, a ≠ byteAddr (dst + BitVec.ofNat 32 j)) → s.mem a = s0.mem a
  rest : Keeps [.eax, .ebx, .esi, .ecx] s0 s

theorem reverseBody_ok {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (ctx : ReverseCtx s0 src dst n) (inv : ReverseInv s0 src dst n i s) (hi : i < n) :
    WP isa (.block reverseByteStep) s fun t =>
      ReverseInv s0 src dst n (i + 1) t ∧ t.zf = some (decide (i + 1 = n)) := by
  have hs : byteAddr (s.gpr .esi + BitVec.ofNat 32 0) =
      byteAddr (src - BitVec.ofNat 32 i) := by rw [inv.source]; simp
  have hd : byteAddr (s.gpr .ebx + BitVec.ofNat 32 0) =
      byteAddr (dst + BitVec.ofNat 32 i) := by rw [inv.dest]; simp
  have hr := ctx.readable i hi
  have hw := ctx.writable i hi
  rw [← inv.rest.2.1, ← inv.rest.2.2] at hr
  rw [← inv.rest.2.2] at hw
  refine WP.mono (reverseByteStep_ok s _ _ hs hd hr hw) ?_
  rintro t ⟨mem, dest, source, count, zero, rest⟩
  have original : s.mem (byteAddr (src - BitVec.ofNat 32 i)) =
      s0.mem (byteAddr (src - BitVec.ofNat 32 i)) :=
    inv.outside _ fun j hj => ctx.separate i hi j (by omega)
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [source, inv.source, BitVec.sub_sub]
    change src - (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [dest, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply]
    by_cases he : j = i
    · subst j; simp only [ite_true, original]
    · have ne : byteAddr (dst + BitVec.ofNat 32 j) ≠ byteAddr (dst + BitVec.ofNat 32 i) :=
        fun h => he (ctx.distinct j (by omega) i hi h)
      rw [ite_eq_right ne]
      exact inv.copied j (by omega)
  · intro a ha
    rw [mem, VG.WriteBytes.writeW8_apply, ite_eq_right (ha i (by omega))]
    exact inv.outside a fun j hj => ha j (by omega)
  · rw [zero, inv.count]
    change some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by have := ctx.countFits; omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

/-- Reverse a nonempty byte range without touching any other memory. -/
theorem reverseBytes_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (ctx : ReverseCtx s src dst n) (hn : 0 < n)
    (hs : s.gpr .esi = src) (hd : s.gpr .ebx = dst)
    (hc : s.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa reverseBytes s (ReverseInv s src dst n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ReverseInv s src dst n i t
  unfold reverseBytes
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (reverseBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change u.zf.map not = some false
      simp only [hz, he, decide_true, Option.map_some, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change u.zf.map not = some true
      simp only [hz, he, decide_false, Option.map_some, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    exact ⟨by omega, by simpa using hs, by simpa using hd,
      by simpa using hc, by intro j hj; omega, by intros; rfl, Keeps.refl _ _⟩

end VG.Proof.Bignum.X86
