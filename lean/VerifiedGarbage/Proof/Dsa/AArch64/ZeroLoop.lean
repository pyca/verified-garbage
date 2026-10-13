module

public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtExp
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Fixed-length bytewise zero tests for DSA acceptance masks -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev zeroByte : List Instr := [.ldrb .x3 .x1 0, .logic .orr .x .x8 .x8 .x3,
  .addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1]

/-- A byte loaded by `ldrb` is zero iff the byte is. -/
theorem byte_widen_zero (m : Mem) (a : Addr) :
    BitVec.setWidth 64 (BitVec.setWidth 32 (m.read a 1)) = 0 ↔ m a = 0 := by
  rw [zext_byte]
  constructor
  · intro h
    have he := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (m a).isLt (by decide))] at he
    exact BitVec.eq_of_toNat_eq he
  · intro h; rw [h]; rfl

theorem zeroByte_ok {s : State} {p : Addr} (hp : s.gpr .x1 = p) (hr : InRegions (s.rd ++ s.wr) p 1) :
    WP isa (.block zeroByte) s fun t =>
      t.gpr .x1 = p + BitVec.ofNat 64 1 ∧ t.gpr .x9 = s.gpr .x9 - BitVec.ofNat 64 1 ∧
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ s.mem p = 0) ∧ t.mem = s.mem ∧ Keep [.x3, .x8, .x1, .x9] s t := by
  refine WP.mono (WP.keep [.x3, .x8, .x1, .x9] (Q := fun t =>
    t.gpr .x1 = p + BitVec.ofNat 64 1 ∧ t.gpr .x9 = s.gpr .x9 - BitVec.ofNat 64 1 ∧
    t.gpr .x8 = s.gpr .x8 ||| BitVec.setWidth 64 (BitVec.setWidth 32 (s.mem.read p 1)) ∧ t.mem = s.mem)
    (by unfold zeroByte; brun [hp, hr]) (by decide) (by decide) (by decide +kernel))
    fun t ⟨⟨htp, htn, ht8, htm⟩, hk⟩ => ⟨htp, htn, ?_, htm, hk⟩
  rw [ht8]
  exact BitVec.or_eq_zero_iff.trans (and_congr Iff.rfl (byte_widen_zero _ _))

/-- A positive-length zero scan reads every byte, including leading zeros. -/
theorem zeroLoop_ok {s : State} {B p : Addr} {Z : Nat} {bs : List Byte}
    (hp : s.gpr .x1 = p) (hn : s.gpr .x9 = BitVec.ofNat 64 bs.length)
    (hs : Src s B Z p bs) (h1 : 0 < bs.length) (h64 : bs.length < 2 ^ 64) :
    WP isa (.loop (.block zeroByte) (.nonzero .x .x9)) s fun t =>
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ ∀ b ∈ bs, b = 0) ∧ t.mem = s.mem ∧
      Keep [.x3, .x8, .x1, .x9] s t := by
  refine WP.mono (wp_countdown (cnt := .x9) h64 h1 (fun i t => t.gpr .x1 = p + BitVec.ofNat 64 i ∧
      (t.gpr .x8 = 0 ↔ s.gpr .x8 = 0 ∧ ∀ k (hk : k < bs.length), k < i → bs[k] = 0) ∧ t.mem = s.mem ∧
      Keep [.x3, .x8, .x1, .x9] s t)
    (fun i hi t ⟨htp, ht8, htm, hkt⟩ _ => WP.mono
      (zeroByte_ok htp (by rw [hkt.rd, hkt.wr]; exact hs.rd i hi))
      fun t' ⟨h1', h9', h8', hm', hk'⟩ => ⟨⟨by rw [h1', BitVec.add_assoc, BitVec.ofNat_add], by
        rw [h8', ht8, htm, hs.val i hi]
        constructor
        · rintro ⟨⟨h0, h⟩, hb⟩
          refine ⟨h0, fun k hk hki => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hki with hki | rfl
          exacts [h k hk hki, hb]
        · rintro ⟨h0, h⟩
          exact ⟨⟨h0, fun k hk hki => h k hk (by omega)⟩, h i hi (by omega)⟩,
        hm'.trans htm, (hkt.trans hk').mono (by decide)⟩, h9'⟩)
    ⟨by rw [hp]; exact (BitVec.add_zero p).symm,
      ⟨fun h => ⟨h, fun k _ hk => absurd hk (Nat.not_lt_zero _)⟩, fun h => h.1⟩, rfl, Keep.refl _ _⟩ hn)
    fun t ⟨_, ht8, htm, hkt⟩ => ?_
  refine ⟨ht8.trans (and_congr Iff.rfl ⟨fun h b hb => ?_, fun h k hk _ => h _ (List.getElem_mem hk)⟩), htm, hkt⟩
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hb
  exact h k hk hk

end VG.Proof.Dsa.AArch64
