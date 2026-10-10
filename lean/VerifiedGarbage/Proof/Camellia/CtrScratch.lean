import VerifiedGarbage.Spec.Camellia.Ctr
import VerifiedGarbage.Proof.Camellia.Scratch

/-!
# Camellia-CTR with its working space as an argument

`ctrScratchContract n` is `ctrContract` with a `scratch` buffer of `n`
words appended, whatever it holds (each target lays out its own), for the
frame that keeps it on the stack (`Verified.stackScratchWiped`), which
needs `ctrPost` to read the memory on return only within the function's
buffers (`ctrPostOut_local`).
-/

namespace VG.Proof.Camellia

open VG.Spec.Camellia

/-- `vg_camellia_ctr` with `scratch: *mut [u64; n]`. -/
def ctrScratchSig (n : Nat) : Sig where
  params := ctrSig.params ++ [("scratch", .array true .u64 n)]

/-- `ctrContract`, whatever `scratch` is. -/
def ctrScratchContract {M : ISA} (A : Abi M) (n : Nat) (stack : Nat := 0) : Contract M :=
  (ctrScratchSig n).contract A
    (pre := fun schedule rounds ctr data n _scratch => ctrPre A.ptrBits schedule rounds ctr data n)
    (post := fun schedule rounds ctr data n _scratch => ctrPost A.ptrBits schedule rounds ctr data n)
    (writeArgs := true) (stack := stack)

theorem ctrScratchContract_eq {M : ISA} (A : Abi M) (n stack : Nat) :
    ctrScratchContract A n stack = Sig.scratchContract A ctrSig "scratch" .u64 n
      (ctrPre A.ptrBits) (ctrPost A.ptrBits) true stack := rfl

section

variable {m₁ m₂ : Mem} {p : Addr}

private theorem bytesAt_congr' {k : Nat}
    (h : ∀ i < k, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Aes.bytesAt m₂ p k = Spec.Aes.bytesAt m₁ p k := by
  simp only [Spec.Aes.bytesAt]
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

private theorem cbcBlocksAt_congr {n : Nat}
    (h : ∀ i < 16 * n, m₂ (p + BitVec.ofNat 64 i) = m₁ (p + BitVec.ofNat 64 i)) :
    Spec.Cbc.blocksAt m₂ p n = Spec.Cbc.blocksAt m₁ p n := by
  simp only [Spec.Cbc.blocksAt]
  refine List.map_congr_left fun i hi => bytesAt_congr' fun j hj => ?_
  have := List.mem_range.mp hi
  rw [Offset.add_add]
  exact h _ (by omega)

end

variable (pb : Nat)

theorem ctrPostOut_local : ∀ vs m m₁ m₂ r, vs.length = (ctrSig.words pb).length →
    (∀ b ∈ Sig.bufs ctrSig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
    Curry.apply (ctrSig.words pb) (ctrPost pb) vs m m₁ r →
      Curry.apply (ctrSig.words pb) (ctrPost pb) vs m m₂ r
  | [_, _, ctr, data, n], m, m₁, m₂, r, _, hb, h => by
    simp only [ctrSig, Sig.bufs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Elem.size, Nat.mul_one] at hb
    have hc := agree_of hb.2.1
    have hd := agree_of hb.2.2
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrPost pb) _ m m₁ r at h
    change Curry.apply [ArgWord.addr, ArgWord.int pb, ArgWord.addr, ArgWord.addr, ArgWord.int pb]
      (ctrPost pb) _ m m₂ r
    dsimp only [Curry.apply, ctrPost, ArgWord.ofRaw] at h ⊢
    have := Nat.mod_le n.toNat (2 ^ pb)
    intro hR
    rw [cbcBlocksAt_congr (n := (n.setWidth pb).toNat) fun i hi => hd i (by
      rw [BitVec.toNat_setWidth] at hi; omega), bytesAt_congr' hc]
    exact h hR

end VG.Proof.Camellia
