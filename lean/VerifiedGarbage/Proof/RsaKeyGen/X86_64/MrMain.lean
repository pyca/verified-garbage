module

public import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrRoundAll
import VerifiedGarbage.Proof.RsaKeyGen.Slots
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MontAll
import VerifiedGarbage.Proof.Bignum.CrtExp
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.RsaKeyGen.Table

/-!
# A candidate on x86-64: Miller–Rabin's loop

The loop's remaining witnesses from `(i, uniform)` at the offset `used` of
`rand` (`mrRest`), how it ends (`MrEnd`), and `kStat` against 4
(`statCmp_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The witnesses' loop from `(i, uniform)` at offset `used`. -/
abbrev mrRest (c ch : Nat) (r : List Byte) (i uni used : Nat) : Option (Bool × List Byte) :=
  Spec.RsaKeyGen.loop (Spec.RsaKeyGen.mrStep c ch (Spec.Rsa.splitTwos (c - 1)).1 (Spec.Rsa.splitTwos (c - 1)).2)
    (i, uni) (r.drop used)

/-- How the loop ends. -/
abbrev MrEnd (B : Addr) (Z w : Nat) (mi : BitVec 64) (c : Nat) (r : List Byte) (s₀ : State)
    (res : Option (Bool × List Byte)) (s : State) : Prop :=
  (∃ bm, MrCtx s B Z w mi c bm) ∧
  (res = none → word s.mem B (8 * kStat) = BitVec.ofNat 64 0) ∧
  (∀ b rest, res = some (b, rest) → word s.mem B (8 * kStat) = BitVec.ofNat 64 (if b then 1 else 3) ∧
    word s.mem B (8 * kUsed) = BitVec.ofNat 64 (r.length - rest.length)) ∧
  Frm B (roundRanges w) s₀.mem s.mem ∧ Keep mmRegs s₀ s

/-- `kStat` against 4. -/
theorem statCmp_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64} (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    {v : Nat} (hv : v < 2 ^ 31) (hS : word s.mem B (8 * kStat) = BitVec.ofNat 64 v) :
    WP isa (.block [.mov .rax (.mem (hdr kStat)), .alu .cmp .rax (.imm 4)]) s fun t =>
      t.zf = some (decide (v = 4)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn := hg.scr.nowrap
  have hl : InRegions (s.rd ++ s.wr) (off B (8 * kStat)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show kStat < 32 by decide); omega_arith)
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (v = 4)) ∧ t.mem = s.mem) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hS]
    exact (congrArg (fun x => (BitVec.ofNat 64 v - x == 0)) (show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl)).trans
      (ofNat_sub_beq (by omega_arith) (by decide))) rfl) fun t ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩

/-- The header words a round keeps. -/
theorem roundRanges_hdr (w : Nat) {k : Nat} (hk : k = kRand ∨ k = kLen ∨ k = kRandLen ∨ k = kChecks ∨ k = kOut ∨
    k = kUsedP) : ∀ r ∈ roundRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> hdr_disj

theorem ofNat_sub_ofNat' {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega_arith)]
  omega_arith

end VG.Proof.RsaKeyGen.X86_64
