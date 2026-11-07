module
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Setup

import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.RoundLoop
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Feed
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

@[expose] public section

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (stateAt serialize block)

theorem input_eq (s : State) (k : Fin 16) (j : Nat) :
    input s k j = (ctr (stateAt s.mem (s.gpr .x0)) j)[k] := by
  simp only [input, ctr, Vector.getElem_set, stateAt, Vector.getElem_ofFn, Fin.getElem_fin]
  by_cases hk : k = 12
  · subst k; rfl
  · have hk' : k.val ≠ 12 := fun e => hk (Fin.ext e)
    simp only [hk, Ne.symm hk', ite_false]

structure ChunkKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

/-- A chunk: the keystream of four blocks XORed with the 256 bytes of the
source (at `x1`) into the destination (at `x6`), which is the source or apart
from it. -/
theorem chunk_ok {sve : Bool} (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (halias : s.gpr .x1 = s.gpr .x6 ∨ (⟨s.gpr .x1, 256⟩ : Region).Disjoint ⟨s.gpr .x6, 256⟩)
    (hsrc : ∀ r j : Fin 4, InRegions (s.rd ++ s.wr)
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16)
    (hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x6 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (chunk sve) s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .x6 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x6, 256⟩] s.mem s'.mem ∧ ChunkKeep s s' := by
  apply WP.seq
  refine (setup_ok s hin).mono fun a ⟨ha, hsa, hta⟩ => ?_
  apply WP.seq
  refine (roundLoop_ok ha hta).mono fun b ⟨hb, hab⟩ => ?_
  have hsb : LoadSame s b := hsa.trans hab
  have hi : ∀ k : Fin 16, InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hsb.rd, hsb.wr, hsb.gpr _ (by decide)]; exact hin k
  apply WP.block_append
  refine (feed_ok hb hi).mono fun c ⟨hc, hbc⟩ => ?_
  have hsc := hsb.trans hbc
  have hc' : Holds (fun j => block (ctr (stateAt s.mem (s.gpr .x0)) j)) c := by
    intro k j hj
    simp only [block]
    rw [hc k j hj, input_same hsb, input_eq]
    simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  have h1 : c.gpr .x1 = s.gpr .x1 := hsc.gpr _ (by decide)
  have h6 : c.gpr .x6 = s.gpr .x6 := hsc.gpr _ (by decide)
  have hi' : ∀ r j : Fin 4, InRegions (c.rd ++ c.wr) (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [hsc.rd, hsc.wr, h1]; exact hsrc r j
  have ho : ∀ r j : Fin 4, InRegions c.wr (c.gpr .x6 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [hsc.wr, h6]; exact hout r j
  refine (finishBlocksTo_ok .x6 hc' (by rw [h1, h6]; exact halias) hi' ho).mono
    fun d ⟨hd, hf, hs⟩ => ⟨?_, ?_, ?_⟩
  · simpa only [h1, h6, hsc.mem] using hd
  · simpa only [h6, hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd, hs.wr.trans hsc.wr, hs.sp.trans hsc.sp⟩

end VG.Proof.ChaCha20.AArch64.Neon4
