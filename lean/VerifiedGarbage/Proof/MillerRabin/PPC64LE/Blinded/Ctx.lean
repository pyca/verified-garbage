module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Blinded
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The blinded Miller–Rabin loop on PPC64LE: the context

`loopRanges`: what the loop writes in the working space: the header words of
its state (`hUni`, `hUsed`, `hStat`, `hIdx`) and the round's (1, 23, 26, 29,
30), arrays 2–6 (the draw, its copy, `subMod`'s difference, and the round's),
array 8 and the round's table, arrays 11–26. `Prep.ofFrm`: the prepared
modulus survives a change of memory within them.

`BCtx`: what the loop reads and never writes: the prepared modulus `c`, the
tape at `R` (`rl` octets, readable, apart from the working space and the
round's stack), and the search's parameters in the header: the octets of a
witness `D = 8 (t + 1)`, the mask `2^b − 1` of its top word (word `t`) and
that word's offset, and the uniform witnesses needed `ch`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE.Blinded

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.MillerRabin.PPC64LE.Search VG.Impl.MillerRabin.PPC64LE.Blinded
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep)
open VG.Proof.Bignum (slot Frm word off ofs)

/-- The ranges of the working space the loop writes. -/
def loopRanges (w : Nat) : List (Nat × Nat) :=
  [(8, 8), (8 * hUni, 8), (8 * hUsed, 8), (8 * hStat, 8), (8 * hIdx, 16), (208, 8), (232, 16),
    (slot w 2, 5 * (8 * (w + 2))), (slot w 8, 8 * (w + 2)), (slot w 11, 16 * (8 * (w + 2)))]

/-- The prepared modulus survives a change of memory within `loopRanges`. -/
theorem Prep.ofFrm {s t : State} {B : Addr} {L w c : Nat} (h : Prep s B L w c) (env : Env t B (8 * L) w)
    (hf : Frm B (loopRanges w) s.mem t.mem) : Prep t B L w c := by
  have hZ := env.hZ
  have hnw := env.hs.nowrap
  have hZ' : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := hZ
  clear hZ
  refine h.keep env (fun d hd => hf.word_eq ?_ (by
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega))
    (fun j hj => ?_)
  · intro r hr
    simp only [loopRanges, hUni, hUsed, hStat, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hd with rfl | rfl | rfl | rfl | ⟨j, hj, rfl⟩ | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega
  · have hj27 : j ≤ 27 := by rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide
    have hb : slot w j + 8 * w ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_right (8 * (w + 2)) hj27
      simp only [slot, hdrBytes]
      omega
    rw [VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv, VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv]
    refine hf.wv_eq (fun r hr => ?_) hb
    simp only [loopRanges, hUni, hUsed, hStat, hIdx, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [slot, hdrBytes]) <;> omega

/-- What the loop reads and never writes. -/
structure BCtx (s : State) (B : Addr) (L w c : Nat) (R : Addr) (rl t b ch : Nat) : Prop where
  prep : Prep s B L w c
  rand : word s.mem B (8 * hRand) = R
  randLen : word s.mem B (8 * hRandLen) = BitVec.ofNat 64 rl
  k : word s.mem B (8 * hK) = BitVec.ofNat 64 (8 * (t + 1))
  top : word s.mem B (8 * hTop) = BitVec.ofNat 64 (2 ^ b - 1)
  topOff : word s.mem B (8 * hTopOff) = BitVec.ofNat 64 (8 * t)
  checks : word s.mem B (8 * hChecks) = BitVec.ofNat 64 ch
  t0 : 0 < t
  tw : t < w
  b1 : 1 ≤ b
  b64 : b ≤ 64
  shape : Spec.RsaKeyGen.bitLength (c - 1) = 64 * t + b
  ch63 : ch < 2 ^ 63
  rl64 : rl < 2 ^ 64
  rdR : ∀ i < rl, InRegions (s.rd ++ s.wr) (R + BitVec.ofNat 64 i) 1
  sepR : ∀ i < rl, ∀ x, ofs B x < 8 * L → R + BitVec.ofNat 64 i ≠ x
  sp : 176 ≤ s.sp.toNat
  stk : (below s.sp 176).Disjoint ⟨B, 8 * L⟩
  stkR : ∀ i < rl, ¬ (below s.sp 176).Contains (R + BitVec.ofNat 64 i) 1

end VG.Proof.MillerRabin.PPC64LE.Blinded
