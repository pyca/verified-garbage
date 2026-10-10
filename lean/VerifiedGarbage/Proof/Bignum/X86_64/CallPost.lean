import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Spec.Rsa.Contract

/-!
# RSA's postconditions do not read the return address below `rsp`

The postconditions of the RSA functions read memory only at their output
buffers (`Spec.Rsa.bytesAt`, `wordsAt`, `written`, `writtenAll`), which no
call's return address overlaps: so they hold of a run with calls if they do
of its inlined form (`Verified.of_inline`'s `hpost`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64

/-- Every byte of a writable region misses the hole. -/
theorem Clear.wr_miss {H : Region} {s : State} (hc : Clear H s) {p : Addr} {n : Nat} (hr : (⟨p, n⟩ : Region) ∈ s.wr)
    (hn : n ≤ 2 ^ 64) {i : Nat} (hi : i < n) : ¬ H.Contains (p + BitVec.ofNat 64 i) 1 :=
  hc _ (List.mem_append_right _ hr) _ (by
    simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat p (by omega)]; omega)

theorem bytesAt_overlay {H : Region} {hv m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1) :
    Spec.Rsa.bytesAt (overlay H hv m) p n = Spec.Rsa.bytesAt m p n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  simp only [overlay, h i (List.mem_range.mp hi), ite_false]

theorem wordsAt_overlay {H : Region} {hv m : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < 8 * n, ¬ H.Contains (p + BitVec.ofNat 64 i) 1) :
    Spec.Rsa.wordsAt (overlay H hv m) p n = Spec.Rsa.wordsAt m p n := by
  simp only [Spec.Rsa.wordsAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  refine overlay_readW (by decide) fun x hx => ?_
  have hx' : x = p + BitVec.ofNat 64 (8 * i + (x - (p + BitVec.ofNat 64 (8 * i))).toNat) := by
    rw [← Offset.add_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  rw [hx']
  exact h _ (by omega)

theorem written_overlay {H : Region} {hv m : Mem} {out : Addr} {n : Nat} {r : BitVec 32} {v : Option (List Byte)}
    (h : ∀ i < n, ¬ H.Contains (out + BitVec.ofNat 64 i) 1) :
    Spec.Rsa.written (overlay H hv m) out n r v ↔ Spec.Rsa.written m out n r v := by
  cases v <;> simp only [Spec.Rsa.written, bytesAt_overlay h]

theorem writtenAll_overlay {H : Region} {hv m : Mem} {outs : List (Addr × Nat)} {r : BitVec 32}
    {v : Option (List (List Byte))} (h : ∀ o ∈ outs, ∀ i < o.2, ¬ H.Contains (o.1 + BitVec.ofNat 64 i) 1) :
    Spec.Rsa.writtenAll (overlay H hv m) outs r v ↔ Spec.Rsa.writtenAll m outs r v := by
  have e : ∀ o ∈ outs, Spec.Rsa.bytesAt (overlay H hv m) o.1 o.2 = Spec.Rsa.bytesAt m o.1 o.2 :=
    fun o ho => bytesAt_overlay (h o ho)
  cases v with
  | none =>
    simp only [Spec.Rsa.writtenAll]
    exact and_congr_right fun _ => forall₂_congr fun o ho => by rw [e o ho]
  | some ys =>
    simp only [Spec.Rsa.writtenAll, List.map_congr_left e]

/-- The bytes of a writable buffer miss the hole. -/
theorem Clear.miss_wr {H : Region} {s : State} (hc : Clear H s) {p : Addr} {n : Nat}
    (hr : (⟨p, n⟩ : Region) ∈ s.wr) (hn : p.toNat + n ≤ 2 ^ 64) {k : Nat} (hk : k ≤ n) :
    ∀ i < k, ¬ H.Contains (p + BitVec.ofNat 64 i) 1 :=
  fun _ hi => Clear.wr_miss hc hr (by omega) (by omega)

theorem patch_mem (b : State) (H : Region) (hv : Mem) (u : Nat → BitVec 64) :
    (b.patch H hv u).mem = overlay H hv b.mem := rfl

end VG.Proof.Bignum.X86_64
