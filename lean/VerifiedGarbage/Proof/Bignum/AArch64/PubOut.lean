import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.MontMul

/-!
# RSA on AArch64: the result

`outStepsArr j` writes array `j`, masked by `sMask`, as the `k` bytes of
`out` and returns the mask's low bit (`outArr_ok`); `MainPost` is what a
computation leaves.
-/

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)

/-- A header slot of the workspace at `x0`, readable. -/
theorem Good.ld {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) {i : Nat} (hi : i < 32) : InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 :=
  hg.scr.ld (by have := hdr_lt_slot w 8 hi; omega)

theorem sArr_lt {j : Nat} (hj : j < 8) : sArr j < 32 := by unfold sArr; omega

/-- Array `j`, masked, to `out`, and the mask's low bit returned. -/
def outStepsArr (j : Nat) : List (Prog isa) := [
  .block [ldh .x8 (sArr j), ldh .x1 sOut, ldh .x9 sK, .add .x .x1 .x1 .x9, ldh .x15 sMask],
  storeBE,
  .block [ldh .x0 sMask, movi .x3 1, .logic .and .x .x0 .x0 .x3]]

theorem mask_one (c : Bool) : mask c &&& BitVec.setWidth 64 (1#16) = BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

/-- Array `j` (`w = ⌈k / 8⌉` words), masked by `sMask = mask c`, as the `k`
bytes of `out`, and `c` returned. -/
theorem outArr_ok {s : State} {B : Addr} {Z k : Nat} {minv : BitVec 64} {op : Addr} {c : Bool} {j : Nat}
    (hj : j < 8) (hg : Good s B Z ((k + 7) / 8) minv) (hZ : slot ((k + 7) / 8) 8 ≤ Z) (hk1 : 1 ≤ k)
    (hk' : k < 2 ^ 31) (hO : word s.mem B (8 * sOut) = op) (hK : word s.mem B (8 * sK) = BitVec.ofNat 64 k)
    (hM : word s.mem B (8 * sMask) = mask c) (hout : ∀ i < k, InRegions s.wr (op + BitVec.ofNat 64 i) 1)
    (hsep : ∀ i < k, Z ≤ ofs B (op + BitVec.ofNat 64 i)) :
    WP isa (seqs (outStepsArr j)) s fun t =>
      (List.range k).map (fun i => t.mem (op + BitVec.ofNat 64 i)) =
        Spec.Rsa.i2osp (if c then wv s.mem B (slot ((k + 7) / 8) j) ((k + 7) / 8) else 0) k ∧
      t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧
      (∀ x, (∀ i < k, x ≠ op + BitVec.ofNat 64 i) → t.mem x = s.mem x) ∧ Keep (.x0 :: mmRegs) s t := by
  have hs := hg.scr
  have hn := hs.nowrap
  have h8 := hdr_lt_slot ((k + 7) / 8) 8 (show 31 < 32 by decide)
  have lj := slot_le (w := (k + 7) / 8) hj
  simp only [outStepsArr, seqs]
  refine WP.seq (WP.mono (WP.keep [.x1, .x8, .x9, .x15] (Q := fun t => t.gpr .x8 = off B (slot ((k + 7) / 8) j) ∧
      t.gpr .x1 = op + BitVec.ofNat 64 k ∧ t.gpr .x9 = BitVec.ofNat 64 k ∧ t.gpr .x15 = mask c ∧ t.mem = s.mem)
    (by brun [hg.x0, hdr_enc (sArr_lt hj), hdr_enc (show sOut < 32 by decide), hdr_enc (show sK < 32 by decide),
      hdr_enc (show sMask < 32 by decide), hg.ld hZ (sArr_lt hj), hg.ld hZ (show sOut < 32 by decide),
      hg.ld hZ (show sK < 32 by decide), hg.ld hZ (show sMask < 32 by decide), hg.hdr.harr j hj, hO, hK, hM])
    rfl rfl rfl) fun s₁ ⟨⟨h8', h1, h9, h15, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (storeBE_ok (hs.congr k₁.wr) h8' h1 h9 h15 hk1 hk' rfl (by omega)
    (fun i hi => by rw [k₁.wr]; exact hout i hi) hsep) fun s₂ ⟨hb, hfr, hwr, hrd, k₂⟩ => ?_)
  have hM₂ : word s₂.mem B (8 * sMask) = mask c := by
    rw [← hM, ← hm₁]
    exact Mem.readW_congr fun i hi => hfr _ fun q hq heq => by
      have := hsep q hq
      rw [← heq, ofs_off B (by unfold sMask sFn; omega)] at this
      unfold sMask sFn at this; omega
  have h0₂ : s₂.gpr .x0 = B := ((k₁.trans k₂).gpr .x0 (by decide)).trans hg.x0
  have hl₂ : InRegions (s₂.rd ++ s₂.wr) (off B (8 * sMask)) 8 := by
    rw [hrd, hwr, k₁.rd, k₁.wr]; exact hg.ld hZ (show sMask < 32 by decide)
  refine WP.mono (WP.keep [.x0, .x3] (Q := fun t => t.gpr .x0 = BitVec.ofNat 64 c.toNat ∧ t.mem = s₂.mem)
    (by brun [h0₂, hdr_enc (show sMask < 32 by decide), hM₂, mask_one, hl₂])
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨h0, hm⟩, k₃⟩ => ?_
  refine ⟨by rw [hm, hb, hm₁], h0, fun x hx => by rw [hm, hfr x hx, hm₁], ?_⟩
  exact ((k₁.trans k₂).trans k₃).mono (by decide)

end VG.Proof.Bignum.AArch64
