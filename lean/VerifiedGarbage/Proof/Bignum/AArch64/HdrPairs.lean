import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.StackArgScratch

/-!
# Multiword arithmetic on AArch64: stack arguments into the header

An entry stores its stack arguments in the header of the working space, each
by a load into `x9` and a store at `x8` (`hdrPairs_ok`).
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- Stack argument `j` into `x9`, then into header slot `i` at `x8`. -/
def hdrPair (j i : Nat) : List Instr := [.ldrSp .x9 (8 * j), .str .x .x9 .x8 (8 * i)]

/-- `hdrPair` for each `(j, i)`. -/
def hdrPairs : List (Nat × Nat) → List Instr
  | [] => []
  | p :: ps => hdrPair p.1 p.2 ++ hdrPairs ps

/-- One stack argument into the header. -/
theorem hdrPair_ok {t : State} {B : Addr} {j i : Nat} {v : BitVec 64} (h8 : t.gpr .x8 = B) (hj : j < 4096)
    (hi : i < 32) (ha : InRegions (t.rd ++ t.wr) (t.sp + BitVec.ofNat 64 (8 * j)) 8)
    (hv : t.mem.readW (t.sp + BitVec.ofNat 64 (8 * j)) 64 = v) (hw : InRegions t.wr (off B (8 * i)) 8) :
    WP isa (.block (hdrPair j i)) t fun t' => t'.mem = t.mem.writeW (off B (8 * i)) v ∧ Keep [.x9] t t' := by
  have ho : 8 * j % 8 = 0 ∧ 8 * j < 32768 := ⟨Nat.mul_mod_right _ _, by omega⟩
  exact WP.keep [.x9] (by brun [hdrPair, exec_ldrSp ho ha, hv, h8, hdr_enc hi, hw]) rfl rfl rfl

/-- The stack arguments `p.1` into the header slots `p.2`, for `p ∈ ps`. -/
theorem hdrPairs_ok {s : State} {B : Addr} : ∀ (ps : List (Nat × Nat)) (t : State),
    (∀ p ∈ ps, p.1 < 4096 ∧ p.2 < 32 ∧ InRegions (s.rd ++ s.wr) (stackArgAddr s p.1) 8 ∧
      (∀ m', Outside B 0 (8 * 32) s.mem m' → m'.readW (stackArgAddr s p.1) 64 = stackArg s p.1) ∧
      InRegions s.wr (off B (8 * p.2)) 8) →
    t.gpr .x8 = B → t.sp = s.sp → t.rd = s.rd → t.wr = s.wr → Outside B 0 (8 * 32) s.mem t.mem →
    WP isa (.block (hdrPairs ps)) t fun t' =>
      t'.mem = ps.foldl (fun m p => m.writeW (off B (8 * p.2)) (stackArg s p.1)) t.mem ∧ Keep [.x9] t t'
  | [], _, _, _, _, _, _, _ => WP.block_nil ⟨rfl, Keep.refl _ _⟩
  | p :: ps, t, hps, h8, hsp, hrd, hwr, ho => by
    obtain ⟨hj, hi, ha, hsep, hw⟩ := hps p List.mem_cons_self
    rw [show hdrPairs (p :: ps) = hdrPair p.1 p.2 ++ hdrPairs ps from rfl, WP.block_append_iff]
    refine WP.mono (hdrPair_ok h8 hj hi (by rw [hsp, hrd, hwr]; exact ha) (v := stackArg s p.1) (by rw [hsp]; exact hsep _ ho)
      (by rw [hwr]; exact hw)) fun t₁ ⟨hm, k⟩ => ?_
    refine WP.mono (hdrPairs_ok ps t₁ (fun q hq => hps q (List.mem_cons_of_mem _ hq))
      (by rw [k.gpr .x8 (by decide)]; exact h8) (by rw [k.sp]; exact hsp) (k.rd.trans hrd)
      (k.wr.trans hwr) (by rw [hm]; exact Outside.store_hdr ho (by omega) (by decide) _))
      fun t' ⟨hm', k'⟩ => ⟨by rw [hm', hm]; rfl, (k.trans k').mono (by decide)⟩

end VG.Proof.Bignum.AArch64
