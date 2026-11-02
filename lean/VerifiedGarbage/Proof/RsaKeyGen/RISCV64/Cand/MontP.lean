module

public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.MontPrep
public import VerifiedGarbage.Proof.MillerRabin.RISCV64.Search.RoundCall
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Cand.Setup
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Layout

/-!
# A candidate on RISC-V: the candidate prepared

As on PPC64LE (`Proof/RsaKeyGen/PPC64LE/Cand/MontP.lean`): `prep_ok`,
`montPrepHi` (`montPrepHi_ok`) on the layout `setup` wrote (`Lay`) leaves the
working space `Prep`ared for the rounds.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Cand

open VG VG.RISCV64 VG.Proof.Mont
open VG.Impl.MillerRabin.RISCV64.Search (montPrepHi)
open VG.Proof.MillerRabin.RISCV64.Search (Prep montPrepHi_ok mpRanges mpRegs)
open VG.Proof.MillerRabin.RISCV64 (Env A)
open VG.Proof.Bignum (slot)

theorem prep_ok {s : State} {B : Addr} {L w c : Nat} (h : Env s B (8 * L) w) (hl : Lay s.mem B L w)
    (hn : A s.mem B w 0 = c) (hodd : c % 2 = 1) (h3 : 3 ≤ c) (hct : 2 ^ (64 * (w - 1)) < c) :
    WP isa montPrepHi s fun t => (Prep t B L w c ∧ Outs B (mpRanges w) s.mem t.mem) ∧ Keep mpRegs s t := by
  have hnw := h.hs.nowrap
  have hZ : 256 + 28 * (8 * (w + 2)) ≤ 8 * L := h.hZ
  have es : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  refine WP.mono (montPrepHi_ok h hn hodd h3 hct) fun t ⟨⟨e, n, inv, t1, r1, r9, r10, ee, l, o⟩, k⟩ => ⟨⟨?_, o⟩, k⟩
  have ow : ∀ d, d + 8 ≤ 56 ∨ (64 ≤ d ∧ d + 8 ≤ 256) →
      VG.Proof.Bignum.word t.mem B d = VG.Proof.Bignum.word s.mem B d := fun d hd =>
    (show VG.Proof.Bignum.Frm B (mpRanges w) s.mem t.mem from o).word_eq (fun x hx => by
      simp only [mpRanges, VG.Impl.MillerRabin.RISCV64.aE, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp only [es] <;> omega) (by omega)
  exact ⟨e, (ow 0 (by omega)).trans hl.len, (ow 48 (by omega)).trans hl.wW, (ow 224 (by omega)).trans hl.strideW,
    fun j hj => (ow _ (by omega)).trans (hl.arrW j hj), n, h3, hodd, inv, t1, r1, r9, r10, ee, l⟩

end VG.Proof.RsaKeyGen.RISCV64.Cand
