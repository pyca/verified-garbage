module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.VerifyContractInput

/-! # Public precomputed words determine all eight of their bytes -/

@[expose] public section
namespace VG.Proof.RsaPkcs1Sig.X86.Ver
open VG

theorem bytesAt_of_words {m m' : Mem} {p : Addr} {n : Nat}
    (words : Spec.Rsa.wordsAt m p n = Spec.Rsa.wordsAt m' p n) :
    Spec.Rsa.bytesAt m p (8 * n) = Spec.Rsa.bytesAt m' p (8 * n) := by
  unfold Spec.Rsa.bytesAt
  refine List.map_congr_left ?_
  intro i hi
  have hi := List.mem_range.mp hi
  have wi : i / 8 < n := by omega
  have W := congrArg (fun xs : List (BitVec 64) => xs[i / 8]?) words
  simp only [Spec.Rsa.wordsAt, List.getElem?_map, List.getElem?_range wi, Option.map_some, Option.some.injEq] at W
  have B := congrArg (fun v : BitVec 64 => v.extractLsb' (8 * (i % 8)) 8) W
  change (m.read (p + BitVec.ofNat 64 (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 =
    (m'.read (p + BitVec.ofNat 64 (8 * (i / 8))) 8).extractLsb' (8 * (i % 8)) 8 at B
  rw [Mem.extractLsb'_read _ _ (Nat.mod_lt _ (by decide : 0 < 8)),
    Mem.extractLsb'_read _ _ (Nat.mod_lt _ (by decide : 0 < 8)), Offset.add_add,
    show 8 * (i / 8) + i % 8 = i by omega] at B
  exact B

end VG.Proof.RsaPkcs1Sig.X86.Ver
