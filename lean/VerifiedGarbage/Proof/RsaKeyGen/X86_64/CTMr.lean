import VerifiedGarbage.Proof.RsaKeyGen.X86_64.CTBase
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.MrMain

/-!
# A candidate on x86-64: constant time of Miller–Rabin, its header

What Miller–Rabin keeps public in the header of the scratch space
(`MrPub.vs`): `out`, `out_len`, `used`'s pointer, `rand` and its length,
the uniform witnesses needed, the witnesses so far and the octets read,
`w` and the arrays' bases (`MrH` and `mr_hp`).
-/

namespace VG.Proof.RsaKeyGen.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.RsaKeyGen.X86_64.Candidate VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The public data of Miller–Rabin. -/
structure MrPub where
  B : Addr
  Z : Nat
  w : Nat
  wr : List Region
  op : Addr
  up : Addr
  rP : Addr
  rl : Nat
  ch : Nat

/-- The header words Miller–Rabin keeps public, with `i` in `kI` and `u` in
`kUsed`. -/
def MrPub.vs (p : MrPub) (i u : Nat) : List (Nat × BitVec 64) :=
  [(kOut, p.op), (kLen, BitVec.ofNat 64 (8 * p.w)), (kUsedP, p.up), (kRand, p.rP),
    (kRandLen, BitVec.ofNat 64 p.rl), (kChecks, BitVec.ofNat 64 p.ch), (kI, BitVec.ofNat 64 i),
    (kUsed, BitVec.ofNat 64 u), (sW, BitVec.ofNat 64 p.w), (sArr 0, off p.B (slot p.w 0)),
    (sArr 1, off p.B (slot p.w 1)), (sArr 2, off p.B (slot p.w 2)), (sArr 3, off p.B (slot p.w 3)),
    (sArr 4, off p.B (slot p.w 4)), (sArr 5, off p.B (slot p.w 5)), (sArr 6, off p.B (slot p.w 6)),
    (sArr 7, off p.B (slot p.w 7))]

/-- Their slots. -/
def mrS : List Nat := [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed, sW, sArr 0, sArr 1, sArr 2, sArr 3,
  sArr 4, sArr 5, sArr 6, sArr 7]

theorem MrPub.vs_fst (p : MrPub) (i u : Nat) (ex : List (Nat × BitVec 64)) :
    (p.vs i u ++ ex).map (·.1) = mrS ++ ex.map (·.1) := by
  simp only [MrPub.vs, mrS, List.map_append, List.map_cons, List.map_nil]

/-- The header words Miller–Rabin keeps, but `w` and the bases. -/
structure MrH (p : MrPub) (i u : Nat) (m : Mem) : Prop where
  out : word m p.B (8 * kOut) = p.op
  len : word m p.B (8 * kLen) = BitVec.ofNat 64 (8 * p.w)
  usedP : word m p.B (8 * kUsedP) = p.up
  rand : word m p.B (8 * kRand) = p.rP
  rlen : word m p.B (8 * kRandLen) = BitVec.ofNat 64 p.rl
  chk : word m p.B (8 * kChecks) = BitVec.ofNat 64 p.ch
  ki : word m p.B (8 * kI) = BitVec.ofNat 64 i
  used : word m p.B (8 * kUsed) = BitVec.ofNat 64 u

/-- `MrH` survives changes away from its words. -/
theorem MrH.frm {p : MrPub} {i u : Nat} {m m' : Mem} {rs : List (Nat × Nat)} (h : MrH p i u m)
    (hf : Frm p.B rs m m')
    (hd : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed], ∀ r ∈ rs, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k) :
    MrH p i u m' := by
  have e : ∀ k ∈ [kOut, kLen, kUsedP, kRand, kRandLen, kChecks, kI, kUsed], word m' p.B (8 * k) = word m p.B (8 * k) :=
    fun k hk => hf.word_eq (hd k hk) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨(e _ (by simp)).trans h.out, (e _ (by simp)).trans h.len, (e _ (by simp)).trans h.usedP,
    (e _ (by simp)).trans h.rand, (e _ (by simp)).trans h.rlen, (e _ (by simp)).trans h.chk,
    (e _ (by simp)).trans h.ki, (e _ (by simp)).trans h.used⟩

/-- The header of a state in Miller–Rabin, with the words `ex` too. -/
theorem mr_hp {p : MrPub} {i u : Nat} {s : State} {mi : BitVec 64} {ex : List (Nat × BitVec 64)}
    (hg : Good s p.B p.Z p.w mi) (hw : s.wr = p.wr) (h : MrH p i u s.mem)
    (hex : ∀ e ∈ ex, word s.mem p.B (8 * e.1) = e.2) : HP p.B p.wr (p.vs i u ++ ex) s := by
  refine ⟨hg.rdi, hw, fun e he => ?_⟩
  rcases List.mem_append.mp he with he | he
  · simp only [MrPub.vs, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h.out
    · exact h.len
    · exact h.usedP
    · exact h.rand
    · exact h.rlen
    · exact h.chk
    · exact h.ki
    · exact h.used
    · exact hg.hdr.hw
    all_goals exact hg.hdr.harr _ (by decide)
  · exact hex e he

end VG.Proof.RsaKeyGen.X86_64
