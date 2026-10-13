module

public import VerifiedGarbage.Proof.Dsa.AArch64.ZeroLoop
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Fixed-length equality scans for DSA signatures and keys -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev equalByte : List Instr := [.ldrb .x3 .x1 0, .ldrb .x4 .x2 0, .logic .eor .x .x3 .x3 .x4,
  .logic .orr .x .x8 .x8 .x3, .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]

/-- Bytes loaded by `ldrb` are equal iff the bytes are. -/
theorem byte_widen_eq (m : Mem) (a b : Addr) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (m.read a 1)) = BitVec.setWidth 64 (BitVec.setWidth 32 (m.read b 1)) ↔
      m a = m b := by
  rw [zext_byte, zext_byte]
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (m a).isLt (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_trans (m b).isLt (by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; rw [h]

theorem equalByte_ok {s : State} {p q : Addr} (hp : s.gpr .x1 = p) (hq : s.gpr .x2 = q)
    (hrp : InRegions (s.rd ++ s.wr) p 1) (hrq : InRegions (s.rd ++ s.wr) q 1) :
    WP isa (.block equalByte) s fun t =>
      t.gpr .x1 = p + BitVec.ofNat 64 1 ∧ t.gpr .x2 = q + BitVec.ofNat 64 1 ∧
      t.gpr .x9 = s.gpr .x9 - BitVec.ofNat 64 1 ∧
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ s.mem p = s.mem q) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x8, .x1, .x2, .x9] s t := by
  refine WP.mono (WP.keep [.x3, .x4, .x8, .x1, .x2, .x9] (Q := fun t =>
    t.gpr .x1 = p + BitVec.ofNat 64 1 ∧ t.gpr .x2 = q + BitVec.ofNat 64 1 ∧
    t.gpr .x9 = s.gpr .x9 - BitVec.ofNat 64 1 ∧
    t.gpr .x8 = s.gpr .x8 ||| (BitVec.setWidth 64 (BitVec.setWidth 32 (s.mem.read p 1)) ^^^
      BitVec.setWidth 64 (BitVec.setWidth 32 (s.mem.read q 1))) ∧ t.mem = s.mem)
    (by unfold equalByte; brun [hp, hq, hrp, hrq]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨htp, htq, htn, ht8, htm⟩, hk⟩ => ⟨htp, htq, htn, ?_, htm, hk⟩
  rw [ht8]
  exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (BitVec.xor_eq_zero_iff.trans (byte_widen_eq _ _ _)))

/-- Both buffers are read completely, even after the first unequal byte. -/
theorem equalLoop_ok {s : State} {B p q : Addr} {Z : Nat} {as bs : List Byte}
    (hp : s.gpr .x1 = p) (hq : s.gpr .x2 = q) (hn : s.gpr .x9 = BitVec.ofNat 64 as.length)
    (ha : Src s B Z p as) (hb : Src s B Z q bs) (hlen : as.length = bs.length)
    (h1 : 0 < as.length) (h64 : as.length < 2 ^ 64) :
    WP isa (.loop (.block equalByte) (.nonzero .x .x9)) s fun t =>
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ as = bs) ∧ t.mem = s.mem ∧
      Keep [.x3, .x4, .x8, .x1, .x2, .x9] s t := by
  refine WP.mono (wp_countdown (cnt := .x9) h64 h1 (fun i t => t.gpr .x1 = p + BitVec.ofNat 64 i ∧
      t.gpr .x2 = q + BitVec.ofNat 64 i ∧
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ ∀ k (hk : k < as.length) (hk' : k < bs.length), k < i → as[k] = bs[k]) ∧
      t.mem = s.mem ∧ Keep [.x3, .x4, .x8, .x1, .x2, .x9] s t)
    (fun i hi t ⟨htp, htq, ht8, htm, hkt⟩ _ => WP.mono
      (equalByte_ok htp htq (by rw [hkt.rd, hkt.wr]; exact ha.rd i hi)
        (by rw [hkt.rd, hkt.wr]; exact hb.rd i (hlen ▸ hi)))
      fun t' ⟨h1', h2', h9', h8', hm', hk'⟩ => ⟨⟨by rw [h1', BitVec.add_assoc, BitVec.ofNat_add],
        by rw [h2', BitVec.add_assoc, BitVec.ofNat_add], by
        rw [h8', ht8, htm, ha.val i hi, hb.val i (hlen ▸ hi)]
        constructor
        · rintro ⟨⟨h0, h⟩, hab⟩
          refine ⟨h0, fun k hk hk' hki => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hki with hki | rfl
          exacts [h k hk hk' hki, hab]
        · rintro ⟨h0, h⟩
          exact ⟨⟨h0, fun k hk hk' hki => h k hk hk' (by omega)⟩, h i hi (hlen ▸ hi) (by omega)⟩,
        hm'.trans htm, (hkt.trans hk').mono (by decide)⟩, h9'⟩)
    ⟨by rw [hp]; exact (BitVec.add_zero p).symm, by rw [hq]; exact (BitVec.add_zero q).symm,
      ⟨fun h => ⟨h, fun k _ _ hk => absurd hk (Nat.not_lt_zero _)⟩, fun h => h.1⟩, rfl, Keep.refl _ _⟩ hn)
    fun t ⟨_, _, ht8, htm, hkt⟩ => ?_
  refine ⟨ht8.trans (and_congr Iff.rfl ⟨fun h => List.ext_getElem hlen fun k hk hk' => h k hk hk' hk,
    fun h k hk hk' _ => by subst h; rfl⟩), htm, hkt⟩

end VG.Proof.Dsa.AArch64
