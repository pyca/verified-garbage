import VerifiedGarbage.Proof.Ocb.Spec
import VerifiedGarbage.Proof.Cmac.Frame
import VerifiedGarbage.Spec.Aes.Contract

/-!
# OCB: blocks in memory as AES states

Untrusted: everything here is checked by Lean. The AES functions on whole
blocks are specified on AES states (`Spec.Aes.statesAt`); OCB's blocks in
memory (`blockAtMem`) are the same bytes (`blockAtMem_of_state`,
`stateAt_of_statesAt`), on every target.
-/

namespace VG.Proof.Ocb

open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (blockAtMem)

theorem bytesAt_toList (m : Mem) (p : Addr) : bytesAt m p 16 = (Spec.Aes.stateAt m p).toList := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h₁ h₂
  simp [bytesAt, Spec.Aes.stateAt]

theorem stateAt_eq (m : Mem) (p : Addr) :
    Spec.Aes.stateAt m p = Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0 := by
  rw [blockAtMem, toBytes_ofBytes (by simp [bytesAt])]
  apply Vector.ext
  intro i hi
  simp [Spec.Aes.stateAt, bytesAt, List.getD_eq_getElem?_getD]

/-- The block at `p`, after a function of states replaced the state there. -/
theorem blockAtMem_of_state {m m' : Mem} {p : Addr} (g : Spec.Aes.State → Spec.Aes.State)
    (h : Spec.Aes.stateAt m' p = g (Spec.Aes.stateAt m p)) :
    blockAtMem m' p =
      Spec.Ocb.ofBytes (g (Vector.ofFn fun i => (Spec.Ocb.toBytes (blockAtMem m p)).getD i.1 0)).toList := by
  rw [blockAtMem, bytesAt_toList, h, stateAt_eq]

theorem stateAt_of_statesAt {m m' : Mem} {D : Addr} {n : Nat} {g : Spec.Aes.State → Spec.Aes.State}
    (h : Spec.Aes.statesAt m' D n = (Spec.Aes.statesAt m D n).map g) {i : Nat} (hi : i < n) :
    Spec.Aes.stateAt m' (D + BitVec.ofNat 64 (16 * i)) = g (Spec.Aes.stateAt m (D + BitVec.ofNat 64 (16 * i))) := by
  have := congrArg (·[i]?) h
  simpa [Spec.Aes.statesAt, hi] using this

theorem blockAtMem_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 16⟩ : Region).Disjoint r) : blockAtMem m' p = blockAtMem m p := by
  rw [blockAtMem, blockAtMem, Proof.Cmac.bytesAt_frame hf hd (by decide)]

end VG.Proof.Ocb
