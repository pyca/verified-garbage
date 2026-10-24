module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.MontPrep
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Search.RoundCall
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Setup
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Slot
import VerifiedGarbage.Proof.Mont.RangeCover
import VerifiedGarbage.Proof.Framework.Omega

/-!
# A candidate on PPC64LE: the candidate prepared

`prep_ok`: `montPrep` (`montPrep_ok`) on the layout `setup` wrote (`Lay`)
leaves the working space `Prep`ared for the rounds.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.MillerRabin.PPC64LE.Search (montPrep)
open VG.Proof.MillerRabin.PPC64LE.Search (Prep montPrep_ok mpRanges mpRegs)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)

theorem prep_ok {s : State} {B : Addr} {L w c : Nat} (h : Env s B (8 * L) w) (hl : Lay s.mem B L w)
    (hn : arr s.mem B w 0 = c) (hodd : c % 2 = 1) (h3 : 3 ≤ c) :
    WP isa montPrep s fun t => (Prep t B L w c ∧ Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t := by
  have hnw := h.hs.nowrap
  have hZ := h.hZ
  rw [slot_lin] at hZ
  refine WP.mono (montPrep_ok h hn hodd h3) fun t ⟨⟨e, n, inv, _, _, r1, r9, r10, ee, l, o⟩, k⟩ => ⟨⟨?_, o⟩, k⟩
  have ow : ∀ d, d + 8 ≤ 56 ∨ (64 ≤ d ∧ d + 8 ≤ 256) → word t.mem B d = word s.mem B d := fun d hd =>
    o.word (fun x hx => by
      simp only [mpRanges, VG.Impl.MillerRabin.PPC64LE.aE, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [slot_lin] <;> omega) (by omega)
  exact ⟨e, (ow 0 (by omega)).trans hl.len, (ow 48 (by omega)).trans hl.wW, (ow 224 (by omega)).trans hl.strideW,
    fun j hj => (ow _ (by omega)).trans (hl.arrW j hj), n, h3, hodd, inv, r1, r9, r10, ee, l⟩

end VG.Proof.RsaKeyGen.PPC64LE.Cand
