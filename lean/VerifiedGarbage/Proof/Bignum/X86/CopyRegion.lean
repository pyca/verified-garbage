module

import VerifiedGarbage.Proof.Bignum.X86.ReverseRegion
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Bignum.X86.CopyByteStep
public import VerifiedGarbage.Proof.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `Bignum.X86.CopyBytes`, which this module and modules that import it used -/

section

/-! # Runtime byte copying, with byte-exact output and memory preservation -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86 VG.Impl.Bignum.X86
open VG.X86.Wp (ofNat_beq_zero)
open VG.Proof.Mont.X86

/-- The source pointer starts at the first byte; the destination starts at the first.
The address conditions also allow a caller to use subranges of a larger workspace. -/
structure CopyCtx (s : State) (src dst : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readable : ∀ i < n, InRegions (s.rd ++ s.wr) (byteAddr (src + BitVec.ofNat 32 i)) 1
  writable : ∀ i < n, InRegions s.wr (byteAddr (dst + BitVec.ofNat 32 i)) 1
  separate : ∀ i < n, ∀ j < n,
    byteAddr (src + BitVec.ofNat 32 i) ≠ byteAddr (dst + BitVec.ofNat 32 j)
  distinct : ∀ i < n, ∀ j < n,
    byteAddr (dst + BitVec.ofNat 32 i) = byteAddr (dst + BitVec.ofNat 32 j) → i = j

structure CopyInv (s0 : State) (src dst : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  source : s.gpr .esi = src + BitVec.ofNat 32 i
  dest : s.gpr .ebx = dst + BitVec.ofNat 32 i
  count : s.gpr .ecx = BitVec.ofNat 32 (n - i)
  copied : ∀ j < i, s.mem (byteAddr (dst + BitVec.ofNat 32 j)) =
    s0.mem (byteAddr (src + BitVec.ofNat 32 j))
  outside : ∀ a, (∀ j < i, a ≠ byteAddr (dst + BitVec.ofNat 32 j)) → s.mem a = s0.mem a
  rest : Keeps [.eax, .ebx, .esi, .ecx] s0 s

theorem copyBody_ok {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (ctx : CopyCtx s0 src dst n) (inv : CopyInv s0 src dst n i s) (hi : i < n) :
    WP isa (.block copyByteStep) s fun t =>
      CopyInv s0 src dst n (i + 1) t ∧ t.zf = some (decide (i + 1 = n)) := by
  have hs : byteAddr (s.gpr .esi + BitVec.ofNat 32 0) =
      byteAddr (src + BitVec.ofNat 32 i) := by rw [inv.source]; simp
  have hd : byteAddr (s.gpr .ebx + BitVec.ofNat 32 0) =
      byteAddr (dst + BitVec.ofNat 32 i) := by rw [inv.dest]; simp
  have hr := ctx.readable i hi
  have hw := ctx.writable i hi
  rw [← inv.rest.2.1, ← inv.rest.2.2] at hr
  rw [← inv.rest.2.2] at hw
  refine WP.mono (copyByteStep_ok s _ _ hs hd hr hw) ?_
  rintro t ⟨mem, dest, source, count, zero, rest⟩
  have original : s.mem (byteAddr (src + BitVec.ofNat 32 i)) =
      s0.mem (byteAddr (src + BitVec.ofNat 32 i)) :=
    inv.outside _ fun j hj => ctx.separate i hi j (by omega_using [hi, hj])
  refine ⟨⟨by omega_using [hi], ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [source, inv.source, BitVec.add_assoc]
    change src + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [dest, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi])]
    congr 1
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply]
    by_cases he : j = i
    · subst j; simp only [ite_true, original]
    · have ne : byteAddr (dst + BitVec.ofNat 32 j) ≠ byteAddr (dst + BitVec.ofNat 32 i) :=
        fun h => he (ctx.distinct j (by omega_using [hi, hj]) i hi h)
      rw [ite_eq_right ne]
      exact inv.copied j (by omega_using [hj, he])
  · intro a ha
    rw [mem, VG.WriteBytes.writeW8_apply, ite_eq_right (ha i (by omega_using []))]
    exact inv.outside a fun j hj => ha j (by omega_using [hj])
  · rw [zero, inv.count]
    change some (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega_using [hi]), ofNat_beq_zero (by have := ctx.countFits; omega_using [this])]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega_using [hi]]

/-- Copy a nonempty byte range without touching any other memory. -/
theorem copyBytes_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (ctx : CopyCtx s src dst n) (hn : 0 < n)
    (hs : s.gpr .esi = src) (hd : s.gpr .ebx = dst)
    (hc : s.gpr .ecx = BitVec.ofNat 32 n) :
    WP isa copyBytes s (CopyInv s src dst n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ CopyInv s src dst n i t
  unfold copyBytes
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (copyBody_ok ctx hi (by omega_using [hik, hk])) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change u.zf.map not = some false
      simp only [hz, he, decide_true, Option.map_some, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega_using [hk], i + 1, by omega_using [hik, hk], by omega_using [hik, hk, he], hu⟩
      change u.zf.map not = some true
      simp only [hz, he, decide_false, Option.map_some, Bool.not_false]
  · refine ⟨0, by omega_using [], hn, ?_⟩
    exact ⟨by omega_using [], by simpa using hs, by simpa using hd,
      by simpa using hc, by intro j hj; omega, by intros; rfl, Keeps.refl _ _⟩

end VG.Proof.Bignum.X86

end

end

/-! # Byte copying of ordinary disjoint byte buffers -/

@[expose] public section

namespace VG.Proof.Bignum.X86
open VG VG.X86


/-- Standard readable/writable, nonoverlapping buffers discharge all loop conditions. -/
theorem copyCtx_of_regions (s : State) (src dst : BitVec 32) {n : Nat}
    (hn : n < 2 ^ 32) (srcFit : src.toNat + n ≤ 2 ^ 32)
    (dstFit : dst.toNat + n ≤ 2 ^ 32)
    (read : InRegions (s.rd ++ s.wr) (byteAddr src) n)
    (write : InRegions s.wr (byteAddr dst) n)
    (sep : Region.Disjoint ⟨byteAddr src, n⟩ ⟨byteAddr dst, n⟩) :
    CopyCtx s src dst n := by
  have ds (j : Nat) (hj : j < n) := byteAddr_add (a := dst) (k := j) (by omega_using [dstFit, hj])
  have sc (i : Nat) (hi : i < n) :
      (⟨byteAddr src, n⟩ : Region).Contains (byteAddr src + BitVec.ofNat 64 i) 1 :=
    Offset.contains_base _ (by omega_using [hi]) (by omega_using [hn, hi])
  have dc (j : Nat) (hj : j < n) :
      (⟨byteAddr dst, n⟩ : Region).Contains (byteAddr dst + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega_using [hj]) (by omega_using [hn, hj])
  refine ⟨hn, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [byteAddr_add (by omega_using [srcFit, hi])]
    obtain ⟨r, hr, hc⟩ := read
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hn, hi])]; omega_using [hi])⟩
  · intro j hj
    rw [ds j hj]
    obtain ⟨r, hr, hc⟩ := write
    exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat _ (by omega_using [hn, hj])]; omega_using [hj])⟩
  · intro i hi j hj he
    rw [byteAddr_add (by omega_using [srcFit, hi] : src.toNat + i < 2 ^ 32), ds j hj] at he
    exact sep _ (he ▸ sc i hi) (dc j hj)
  · intro i hi j hj he
    rw [ds i hi, ds j hj] at he
    have e := congrArg (fun a => (a - byteAddr dst).toNat) he
    simpa only [Mem.sub_ofNat_toNat _ (by omega_using [hn, hi] : i < 2 ^ 64),
      Mem.sub_ofNat_toNat _ (by omega_using [hn, hj] : j < 2 ^ 64)] using e

theorem CopyInv.frame {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (inv : CopyInv s0 src dst n i s) (fit : dst.toNat + n ≤ 2 ^ 32) :
    Frame [⟨byteAddr dst, n⟩] s0.mem s.mem := by
  intro a ha
  apply inv.outside a
  intro j hj he
  apply ha ⟨byteAddr dst, n⟩ (by simp)
  rw [he, byteAddr_add (by have := inv.index; omega_using [fit, hj, this])]
  exact Offset.contains_base _ (by have := inv.index; omega_using [hj, this]) (by have := inv.index; omega_using [fit, hj, this])

end VG.Proof.Bignum.X86
