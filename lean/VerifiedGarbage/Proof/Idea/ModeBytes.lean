module

import VerifiedGarbage.Proof.Idea.Memory
public import VerifiedGarbage.Proof.Modes.Ctr
public import VerifiedGarbage.Spec.Idea.Cbc
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# IDEA's blocks and schedule as the modes see them

What every target's core for the modes (`Proof/Idea/<Target>/ModeCore.lean`)
needs: a block's bytes as the modes read them (`bytesAt_eq`,
`cbcBlocksAt_eq`), `Spec.Idea.cipher` on them (`cipher_bytes`), and the
schedule at an address, which depends only on its 104 bytes
(`scheduleAt_congr_at`, `scheduleAt_frame`).
-/

@[expose] public section

namespace VG.Proof.Idea

theorem bytesAt_eq (m : Mem) (p : Addr) : Spec.Aes.bytesAt m p 8 = (Spec.Idea.blockAt m p).toList := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i _ _
  simp [Spec.Aes.bytesAt, Spec.Idea.blockAt]

theorem cbcBlocksAt_eq (m : Mem) (p : Addr) (n : Nat) :
    Spec.Idea.cbcBlocksAt m p n = Modes.blocksOf 8 m p n := by
  simp only [Spec.Idea.cbcBlocksAt, Spec.Idea.blocksAt, Modes.blocksOf, List.map_map]
  exact List.map_congr_left fun i _ => (bytesAt_eq m _).symm

theorem cipher_bytes (k : Spec.Idea.Schedule) (m : Mem) (p : Addr) :
    Spec.Idea.cipher k (Spec.Aes.bytesAt m p 8) = (Spec.Idea.cryptBlock k (Spec.Idea.blockAt m p)).toList := by
  have h : (Vector.ofFn fun i : Fin 8 => (Spec.Aes.bytesAt m p 8).getD i.val 0) = Spec.Idea.blockAt m p := by
    ext i hi; simp [Spec.Aes.bytesAt, Spec.Idea.blockAt]
  simp only [Spec.Idea.cipher, h]

/-- The schedule at `q` is the one at `p` if their 104 bytes are. -/
theorem scheduleAt_congr_at {m m' : Mem} {p q : Addr}
    (h : ∀ i < 104, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    Spec.Idea.scheduleAt m' q = Spec.Idea.scheduleAt m p := by
  apply Vector.ext
  intro i hi
  simp only [Spec.Idea.scheduleAt, Vector.getElem_ofFn]
  rw [h _ (by omega), h _ (by omega)]

theorem scheduleAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 104⟩ : Region).Disjoint r) :
    Spec.Idea.scheduleAt m' p = Spec.Idea.scheduleAt m p :=
  scheduleAt_congr_at (frame_bytes hf hd (by decide))

end VG.Proof.Idea
