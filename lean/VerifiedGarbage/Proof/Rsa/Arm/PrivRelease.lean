module

public import VerifiedGarbage.Proof.Rsa.Arm.PrivReleaseStep
public import VerifiedGarbage.Proof.Bignum.Arm.MaskBytes
public import VerifiedGarbage.Proof.Framework.WriteBytes
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Runtime byte copying, with byte-exact output and memory preservation -/

@[expose] public section

namespace VG.Proof.Rsa.Arm
open VG VG.Arm VG.Impl.Rsa.Arm.PrivChecked
open VG.Proof.X25519.Arm (Rest ofNat_beq_zero)

/-- Both pointers start at the first byte of their ranges.
The address conditions also allow a caller to use subranges of a larger workspace. -/
structure ReleaseCtx (s : State) (src dst : BitVec 32) (n : Nat) : Prop where
  countFits : n < 2 ^ 32
  readable : ∀ i < n, InRegions (s.rd ++ s.wr) (State.addr (src + BitVec.ofNat 32 i)) 1
  writable : ∀ i < n, InRegions s.wr (State.addr (dst + BitVec.ofNat 32 i)) 1
  clearable : ∀ i < n, InRegions s.wr (State.addr (src + BitVec.ofNat 32 i)) 1
  sourceDistinct : ∀ i < n, ∀ j < n,
    State.addr (src + BitVec.ofNat 32 i) = State.addr (src + BitVec.ofNat 32 j) → i = j
  zeroReg : s.gpr .r12 = 0
  separate : ∀ i < n, ∀ j < n,
    State.addr (src + BitVec.ofNat 32 i) ≠ State.addr (dst + BitVec.ofNat 32 j)
  distinct : ∀ i < n, ∀ j < n,
    State.addr (dst + BitVec.ofNat 32 i) = State.addr (dst + BitVec.ofNat 32 j) → i = j

structure ReleaseInv (s0 : State) (src dst : BitVec 32) (n i : Nat) (s : State) : Prop where
  index : i ≤ n
  source : s.gpr .r1 = src + BitVec.ofNat 32 i
  dest : s.gpr .r0 = dst + BitVec.ofNat 32 i
  count : s.gpr .lr = BitVec.ofNat 32 (n - i)
  copied : ∀ j < i, s.mem (State.addr (dst + BitVec.ofNat 32 j)) =
    s0.mem (State.addr (src + BitVec.ofNat 32 j)) &&& (s0.gpr .r2).setWidth 8
  cleared : ∀ j < i, s.mem (State.addr (src + BitVec.ofNat 32 j)) = 0
  outside : ∀ a, (∀ j < i, a ≠ State.addr (dst + BitVec.ofNat 32 j)) →
    (∀ j < i, a ≠ State.addr (src + BitVec.ofNat 32 j)) → s.mem a = s0.mem a
  rest : Rest [.r0, .r1, .r3, .lr] s0 s

theorem releaseBody_ok {s0 s : State} {src dst : BitVec 32} {n i : Nat}
    (ctx : ReleaseCtx s0 src dst n) (inv : ReleaseInv s0 src dst n i s) (hi : i < n) :
    WP isa (.block releaseStep) s fun t =>
      ReleaseInv s0 src dst n (i + 1) t ∧ t.z = decide (i + 1 = n) := by
  have hs : State.addr (s.gpr .r1 + BitVec.ofNat 32 0) =
      State.addr (src + BitVec.ofNat 32 i) := by rw [inv.source]; simp
  have hd : State.addr (s.gpr .r0 + BitVec.ofNat 32 0) =
      State.addr (dst + BitVec.ofNat 32 i) := by rw [inv.dest]; simp
  have hr := ctx.readable i hi
  have hw := ctx.writable i hi
  rw [← inv.rest.rd, ← inv.rest.wr] at hr
  have hc := ctx.clearable i hi
  rw [← inv.rest.wr] at hw hc
  refine WP.mono (releaseStep_ok s _ _ hs hd hr hw hc ((inv.rest.gpr .r12 (by simp)).trans ctx.zeroReg)) ?_
  rintro t ⟨mem, dest, source, count, zero, rest⟩
  have original : s.mem (State.addr (src + BitVec.ofNat 32 i)) =
      s0.mem (State.addr (src + BitVec.ofNat 32 i)) :=
    inv.outside _ (fun j hj => ctx.separate i hi j (by omega))
      (fun j hj he => by have := ctx.sourceDistinct i hi j (by omega) he; omega)
  have mask := inv.rest.gpr .r2 (by simp)
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, inv.rest.trans rest⟩, ?_⟩
  · rw [source, inv.source, BitVec.add_assoc]
    change src + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [dest, inv.dest, BitVec.add_assoc]
    change dst + (BitVec.ofNat 32 i + BitVec.ofNat 32 1) = _
    rw [← BitVec.ofNat_add]
  · rw [count, inv.count]
    change BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)]
    congr 1
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply,
      ite_eq_right (Ne.symm (ctx.separate i hi j (by omega))), VG.WriteBytes.writeW8_apply]
    by_cases he : j = i
    · subst j; simp only [ite_true, original, mask]
    · have ne : State.addr (dst + BitVec.ofNat 32 j) ≠ State.addr (dst + BitVec.ofNat 32 i) :=
        fun h => he (ctx.distinct j (by omega) i hi h)
      rw [ite_eq_right ne]
      exact inv.copied j (by omega)
  · intro j hj
    rw [mem, VG.WriteBytes.writeW8_apply]
    by_cases he : j = i
    · subst j; simp only [ite_true]
    · have ne : State.addr (src + BitVec.ofNat 32 j) ≠ State.addr (src + BitVec.ofNat 32 i) :=
        fun h => he (ctx.sourceDistinct j (by omega) i hi h)
      rw [ite_eq_right ne, VG.WriteBytes.writeW8_apply, ite_eq_right (ctx.separate j (by omega) i hi)]
      exact inv.cleared j (by omega)
  · intro a ha hb
    rw [mem, VG.WriteBytes.writeW8_apply, ite_eq_right (hb i (by omega)),
      VG.WriteBytes.writeW8_apply, ite_eq_right (ha i (by omega))]
    exact inv.outside a (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
  · rw [zero, inv.count]
    change (BitVec.ofNat 32 (n - i) - BitVec.ofNat 32 1 == 0) = _
    rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega), ofNat_beq_zero (by have := ctx.countFits; omega)]
    simp only [show n - i - 1 = 0 ↔ i + 1 = n by omega]

/-- Copy a nonempty byte range without touching any other memory. -/
theorem release_ok (s : State) {src dst : BitVec 32} {n : Nat}
    (ctx : ReleaseCtx s src dst n) (hn : 0 < n)
    (hs : s.gpr .r1 = src) (hd : s.gpr .r0 = dst)
    (hc : s.gpr .lr = BitVec.ofNat 32 n) :
    WP isa release s (ReleaseInv s src dst n n) := by
  let inv := fun k t => ∃ i, i + k = n ∧ 0 < k ∧ ReleaseInv s src dst n i t
  unfold release
  refine WP.loop (M := isa) inv ?_ n s ?_
  · intro k t h
    obtain ⟨i, hik, hk, hi⟩ := h
    refine WP.mono (releaseBody_ok ctx hi (by omega)) ?_
    rintro u ⟨hu, hz⟩
    by_cases he : i + 1 = n
    · left
      refine ⟨?_, he ▸ hu⟩
      change some (!u.z) = some false
      simp only [hz, he, decide_true, Bool.not_true]
    · right
      refine ⟨?_, k - 1, by omega, i + 1, by omega, by omega, hu⟩
      change some (!u.z) = some true
      simp only [hz, he, decide_false, Bool.not_false]
  · refine ⟨0, by omega, hn, ?_⟩
    exact ⟨by omega, by simpa using hs, by simpa using hd,
      by simpa using hc, by intro j hj; omega, by intro j hj; omega, by intros; rfl, Rest.refl _ _⟩

end VG.Proof.Rsa.Arm
