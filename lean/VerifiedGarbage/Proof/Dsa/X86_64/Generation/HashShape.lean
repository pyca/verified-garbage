module

public import VerifiedGarbage.Proof.Dsa.Generation.PCandidate
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.HashPlan
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Rolled.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Dsa.Digest
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.PShape
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Basic
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf

/-! ### `Dsa.X86_64.Generation.PShapeArgs`, which the modules that import this one used -/

section

/-! # Native arguments for the full-width candidate shaper -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.RsaOaep.X86_64 VG.Proof.RsaOaep.X86_64

theorem pShapeArgs_ok {s : State} {F S op hp : Addr} {len count plen : Nat}
    (L : Lay s F S) {V : Nat → Byte} {W : Nat → BitVec 64} (R : Rep s.mem F S V W)
    (hop : W 0 = op) (hhp : W 4 = hp) (hn : (count + 1) * len < 2 ^ 31) (hl : plen ≤ 1024) :
    WP isa (.block (Impl.Dsa.X86_64.Generation.pShapeArgs len count plen)) s fun t =>
      t.gpr .rdi = op ∧ t.gpr .rsi = off hp ((count + 1) * len - plen) ∧
      t.gpr .rcx = BitVec.ofNat 64 plen ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * plen) ∧
      t.mem = s.mem ∧ Keep [.rdi, .rsi, .rcx, .rdx] s t := by
  refine WP.mono (WP.keep [.rdi, .rsi, .rcx, .rdx] (Q := fun t =>
      t.gpr .rdi = op ∧ t.gpr .rsi = off hp ((count + 1) * len - plen) ∧
      t.gpr .rcx = BitVec.ofNat 64 plen ∧ t.gpr .rdx = BitVec.ofNat 64 (8 * plen) ∧ t.mem = s.mem) ?_ rfl)
    fun _ ⟨⟨a, b, c, d, e⟩, hk⟩ => ⟨a, b, c, d, e, hk⟩
  have hld0 : InRegions (s.rd ++ s.wr) F 8 := by simpa [off] using L.ld (d := 0) (by decide)
  have hv0 : s.mem.readW F 64 = op := by
    simpa [off] using R.slot (d := 0) (k := 0) rfl (by decide) hop
  xrun [Impl.Dsa.X86_64.Generation.pShapeArgs, ea_sp, L.rsp,
    hld0, hv0, L.ld (d := 32) (by decide), R.slot (d := 32) (k := 4) rfl (by decide) hhp,
    sx_ofNat (show (count + 1) * len - plen < 2 ^ 31 by omega_using [hn])]
  change BitVec.setWidth 64 (BitVec.ofNat 32 plen) = BitVec.ofNat 64 plen ∧
    BitVec.setWidth 64 (BitVec.ofNat 32 (8 * plen)) = BitVec.ofNat 64 (8 * plen)
  constructor <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;>
    simp only [Nat.mod_eq_of_lt (by omega_using [hl] : plen < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [hl] : 8 * plen < 2 ^ 32)]

end VG.Proof.Dsa.X86_64.Generation

end

end

/-! # The stored hash suffix determines exactly the specified p candidate -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/Generation/HashValue.lean`, which only this module imported.
section

/-! # Decode the stored p hashes as their radix contribution sum -/

section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.Generation

theorem hash_prefix_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : X86_64.State}
    (hs : HashState p H (p.count + 1) s) (k : Nat) (hk : k ≤ p.count + 1) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off p.output ((p.count + 1 - k) * p.len)) (k * p.len)) =
      contributions (8 * p.len) (fun j => Spec.Dsa.decodeBE (p.digest H j)) k := by
  induction k with
  | zero => simp [Spec.Rsa.bytesAt, Spec.Dsa.decodeBE, contributions]
  | succ k ih =>
    have hkcount : k ≤ p.count := by omega
    have hoff : off (p.dest k) p.len = off p.output ((p.count + 1 - k) * p.len) := by
      rw [HashPlan.dest, off_off]
      congr 1
      rw [show p.count + 1 - k = p.count - k + 1 by omega, Nat.add_mul, Nat.one_mul]
    have hp : 256 ^ (k * p.len) = 2 ^ (k * (8 * p.len)) := by
      rw [pow256_eq, Nat.mul_left_comm 8 k p.len]
    rw [show (p.count + 1 - (k + 1)) * p.len = (p.count - k) * p.len by congr 1; omega,
      show (k + 1) * p.len = p.len + k * p.len by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm], bytesAt_append]
    change Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (p.dest k) p.len ++
      Spec.Rsa.bytesAt s.mem (off (p.dest k) p.len) (k * p.len)) = _
    rw [hs.hashes k (by omega), VG.Proof.Dsa.decodeBE_append, bytesAt_length, hoff, ih (by omega), hp,
      contributions_succ, Nat.add_comm]

end VG.Proof.Dsa.X86_64.Generation
end

end

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.Proof.Bignum VG.Proof.Dsa.Generation

theorem hash_complete_value {p : HashPlan} {H : Spec.Mgf1.Hash} {s : X86_64.State}
    (hs : HashState p H (p.count + 1) s) :
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem p.output ((p.count + 1) * p.len)) =
      contributions (8 * p.len) (fun j => Spec.Dsa.decodeBE (p.digest H j)) (p.count + 1) := by
  simpa [off] using
    hash_prefix_value hs (p.count + 1) (Nat.le_refl _)

theorem hash_shaped_candidate {p : HashPlan} {H : Spec.Mgf1.Hash} {s : X86_64.State}
    (hs : HashState p H (p.count + 1) s) {l plen : Nat}
    (hl : 2 ≤ l) (hlp : l = 8 * plen) (hroom : plen ≤ (p.count + 1) * p.len)
    (hcount : p.count = (l - 1) / (8 * p.len))
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * p.len) bs)
    (hsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * p.len) bs).length = 8 * p.len) (q : Nat) :
    let x := Spec.Ffdh.candidateOf l (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem
      (off p.output ((p.count + 1) * p.len - plen)) plen))
    x + 1 - x % (2 * q) = Spec.Dsa.pCandidate l (8 * p.len) q p.seed p.offset := by
  have hsuf := bytesAt_suffix_value s.mem p.output ((p.count + 1) * p.len - plen) plen
  rw [Nat.sub_add_cancel hroom, hash_complete_value hs, pow256_eq, ← hlp] at hsuf
  have hdig : (fun j => Spec.Dsa.decodeBE (p.digest H j)) = pDigest (8 * p.len) p.seed p.offset := by
    funext j
    simp only [HashPlan.digest, pDigest, p.seed_len, hhash, Nat.add_assoc]
  dsimp only
  rw [← hsuf, candidateOf_mod_width (by omega_using [hl]) (Nat.le_refl _), hdig,
    pCandidate_shaped hl hsize, hcount]

end VG.Proof.Dsa.X86_64.Generation
