module

public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Bignum.Math
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.CTR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Bignum.Math
meta import Mathlib.Order.RelClasses
meta import Mathlib.Tactic.Finiteness.Attr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.CrtMath

/-!
# RSA with the CRT on AArch64: `G = 2^E mod n` is constant time

`gPow` computes in `n`'s workspace, all public: the prime's length `w_X`,
hence `K`, `D` and the bits of `D` the loop branches on, are the same in
both runs (`gPow_ct`). Its loads through the prime's base (in a header slot)
are pinned by correctness, the bits of `D` from `gBit_ok`'s invariant.
-/

@[expose] public section

namespace VG.Proof.Bignum.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Crt VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep eval_nonzero eval_zero)

/-! ## The bits of `D` -/

/-- `n`'s layout. -/
abbrev GPub.L (p : GPub) : Lay := ⟨p.B, p.Z, p.w, p.minv⟩

/-- After the top `j` bits of `D` in `gPow`'s loop. -/
def GLoop (p : GPub) (j : Nat) (t : State) : Prop :=
  ∃ s₀, GInv s₀ p.B p.Z p.w p.minv p.N (gD p.w p.wx) (gD p.w p.wx).log2 j t ∧ slot p.w 8 ≤ p.Z ∧ 2 ≤ p.w ∧
    p.w < 2 ^ 30 ∧ p.N % 2 = 1 ∧ 1 < p.N ∧ 1 ≤ p.wx ∧ p.wx ≤ p.w

/-- After the squaring of bit `j`. -/
def GB1 (q : GPub × Nat) (t : State) : Prop :=
  (Good t q.1.B q.1.Z q.1.w q.1.minv ∧ slot q.1.w 8 ≤ q.1.Z) ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧
    q.2 < (gD q.1.w q.1.wx).log2 + 1 ∧ (gD q.1.w q.1.wx).log2 < 62 ∧
    wv t.mem q.1.B (slot q.1.w Public.aY) q.1.w < wv t.mem q.1.B (slot q.1.w Public.aN) q.1.w ∧
    word t.mem q.1.B (8 * sD) = BitVec.ofNat 64 (gD q.1.w q.1.wx) ∧
    word t.mem q.1.B (8 * Public.sCnt) = BitVec.ofNat 64 (2 ^ ((gD q.1.w q.1.wx).log2 - q.2))

/-- After the test of bit `j`. -/
def GB2 (q : GPub × Nat) (t : State) : Prop :=
  (Good t q.1.B q.1.Z q.1.w q.1.minv ∧ slot q.1.w 8 ≤ q.1.Z) ∧ 2 ≤ q.1.w ∧ q.1.w < 2 ^ 30 ∧
    wv t.mem q.1.B (slot q.1.w Public.aY) q.1.w < wv t.mem q.1.B (slot q.1.w Public.aN) q.1.w ∧
    t.gpr .x3 = BitVec.ofNat 64 (gD q.1.w q.1.wx) &&& BitVec.ofNat 64 (2 ^ ((gD q.1.w q.1.wx).log2 - q.2))

/-- A count-down loop's condition after iteration `j` of `n`. -/
theorem eval_nz_count {t : State} {r : Reg} {j n : Nat} (hj : j < n) (h : (t.gpr r).toNat ≠ 0 ↔ j + 1 ≠ n) :
    isa.eval (.nonzero .x r) t = some (decide (j + 1 < n)) := by
  rw [eval_nonzero]
  congr 1
  have e : (t.gpr r != 0) = true ↔ (t.gpr r).toNat ≠ 0 := by
    rw [bne_iff_ne, ne_eq, ne_eq, ← BitVec.toNat_inj]; exact Iff.rfl
  rw [Bool.eq_iff_iff, e, h, decide_eq_true_iff]
  omega

/-- One bit of `D`: the squaring, the test and the doubling. -/
theorem gBody_ct (M : Mont) : RelCT isa (Two fun (q : GPub × Nat) s => q.2 < (gD q.1.w q.1.wx).log2 + 1 ∧
    GLoop q.1 q.2 s) (seqs (gBody M.mm)) fun _ _ => True := by
  simp only [gBody, seqs]
  -- The squaring.
  refine RelCT.seq (two_post (Ψ := GB1) (two_map (fun q => q.1.L.ws)
    (fun q s ⟨_, _, hI, hZ, _⟩ => ⟨q.1.minv, hI.good, hZ⟩) (M.ct (by unfold MmUse; decide))) ?_) ?_
  · rintro q s ⟨hj, s₀, hI, hZ, hw, hw30, -, -, hwx, hwx'⟩
    obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
    have hL : (gD q.1.w q.1.wx).log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
    have hc2 : 2 ^ ((gD q.1.w q.1.wx).log2 + 1 - q.2) / 2 = 2 ^ ((gD q.1.w q.1.wx).log2 - q.2) := by
      rw [show (gD q.1.w q.1.wx).log2 + 1 - q.2 = ((gD q.1.w q.1.wx).log2 - q.2) + 1 by omega, Nat.pow_succ,
        Nat.mul_div_cancel _ (by decide)]
    refine WP.mono (crtMmN_ok M (o := Public.aY) (a := Public.aY) (b := Public.aY) hI.good hZ hw (by omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hI.n hI.inv
      hI.ylt) fun t₁ ⟨hg₁, hn₁, _, hlt₁, _, ha₁, _⟩ => ⟨⟨hg₁, hZ⟩, hw, hw30, hj, hL, by rw [hn₁]; exact hlt₁,
        by rw [ha₁.hslot (by decide)]; exact hI.d, by rw [ha₁.hslot (by decide), hI.c, hc2]⟩
  -- The bit.
  refine RelCT.seq (two_piece (Ψ := GB2) [.x0] (pins_x0B (fun q => q.1.B) fun _ _ h => h.1.1.x0)
    (by taint_decide) ?_) ?_
  · rintro q t₁ ⟨hg₁, hw, hw30, hj, hL, hlt, hd, hc⟩
    refine WP.mono (WP.keep [.x3, .x4] (Q := fun t₂ => t₂.gpr .x3 = BitVec.ofNat 64 (gD q.1.w q.1.wx) &&&
        BitVec.ofNat 64 (2 ^ ((gD q.1.w q.1.wx).log2 - q.2)) ∧ t₂.mem = t₁.mem) (by
      brun [hg₁.1.x0, hdr_enc (show sD < 32 by decide), hdr_enc (show Public.sCnt < 32 by decide),
        hg₁.1.ld hg₁.2 (show sD < 32 by decide), hg₁.1.ld hg₁.2 (show Public.sCnt < 32 by decide), hd, hc])
      (by decide) (by decide) (by decide +kernel))
      fun t₂ ⟨⟨h3, hm⟩, k⟩ => ⟨⟨⟨hg₁.1.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg₁.1.x0, hm ▸ hg₁.1.hdr⟩,
        hg₁.2⟩, hw, hw30, by rw [hm]; exact hlt, h3⟩
  -- Doubled if it is set.
  refine RelCT.seq (R := Two fun (q : GPub × Nat) t => (Good t q.1.B q.1.Z q.1.w q.1.minv ∧ slot q.1.w 8 ≤ q.1.Z))
    (two_ite (fun q s₁ s₂ h₁ h₂ => by rw [eval_nonzero, eval_nonzero, h₁.2.2.2.2, h₂.2.2.2.2]) ?_ ?_) ?_
  · refine two_post (two_map (fun q => q.1.L) (fun _ _ h => h.1.1)
      (double_ct (by decide) (by decide) (by decide) (by decide) (by taint_decide))) fun q t h => ?_
    obtain ⟨⟨hg, hw, hw30, hlt, -⟩, -⟩ := h
    exact WP.mono (double_ok hg.1.scr hg.1.x0 hg.1.hdr hg.2 hw (by omega) (mo := Public.aN) (acc := Public.aAcc)
      (tmp := Public.aTmp) (o := Public.aY) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hlt) fun t' ⟨_, ha, k⟩ =>
        ⟨⟨hg.1.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.1.x0, ha.hdr hg.1.hdr⟩, hg.2⟩
  · exact RelCT.block_nil fun _ _ hp => two_mono (fun _ _ h => h.1.1) hp
  -- The next bit.
  exact two_taint [.x0] (pins_x0B (fun q => q.1.B) fun _ _ h => h.1.x0) (by taint_decide)

/-- The bits of `D`. -/
theorem gLoop_ct (M : Mont) : RelCT isa (Two fun p s => 0 < (gD p.w p.wx).log2 + 1 ∧ GLoop p 0 s)
    (.loop (seqs (gBody M.mm)) (.nonzero .x .x3)) (Two fun (_ : GPub) (_ : State) => True) :=
  two_loop (Φ := GLoop) (fun p => (gD p.w p.wx).log2 + 1) (gBody_ct M)
    fun p j s hj ⟨s₀, hI, hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩ => by
      obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
      have hL : (gD p.w p.wx).log2 < 62 := (Nat.log2_lt (by omega)).mpr hD1
      exact WP.mono (gBit_ok M hZ hw (by omega) (VG.Proof.Bignum.coprime_pow2 hodd _) (by omega) (by omega) hj hI)
        fun s' ⟨hI', hz⟩ => ⟨eval_nz_count hj hz, fun _ => ⟨s₀, hI', hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩,
          fun _ => trivial⟩

/-! ## `D` and its top bit -/

/-- After the load of the prime's base. -/
def GA (sl : Nat) (p : GPub) (t : State) : Prop :=
  ∃ s, GPre sl p s ∧ t.mem = s.mem ∧ Keep [.x5] s t ∧ t.gpr .x5 = p.Bx

/-- After `k` steps of the loop `x3 += w_X` while `x3 < w`. -/
def KL (p : GPub) (k : Nat) (t : State) : Prop :=
  t.gpr .x0 = p.B ∧ t.gpr .x3 = BitVec.ofNat 64 (k * p.wx) ∧ t.gpr .x5 = BitVec.ofNat 64 p.wx ∧
    t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x7 = 0 ∧ t.gpr .x8 = 1 ∧ 1 ≤ p.wx ∧ p.wx ≤ p.w ∧ p.w < 2 ^ 30

/-- After the loads of `w_X` and `w`. -/
abbrev GBk (p : GPub) (t : State) : Prop := KL p 0 t

/-- After the loop: `K w_X`. -/
def KD (p : GPub) (t : State) : Prop := t.gpr .x0 = p.B

/-- The loop `x3 += w_X` while `x3 < w`: its condition comes from a `csel`,
which the taint analysis does not follow, so it is related step by step. -/
theorem kLoop_ct : RelCT isa (Two fun p s => 0 < nChunks p.w p.wx ∧ KL p 0 s)
    (.loop (.block [.add .x .x3 .x3 .x5, .subs .x .x4 .x3 .x12, .csel .x .x4 .x7 .x8]) (.nonzero .x .x4))
    (Two KD) :=
  two_loop (Φ := KL) (fun p => nChunks p.w p.wx)
    (two_taint [.x0, .x3, .x5, .x12, .x7, .x8] (pins_of (fun (q : GPub × Nat) r => if r = .x0 then q.1.B else
      if r = .x3 then BitVec.ofNat 64 (q.2 * q.1.wx) else if r = .x5 then BitVec.ofNat 64 q.1.wx else
      if r = .x12 then BitVec.ofNat 64 q.1.w else if r = .x7 then 0 else 1) fun q s h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        obtain ⟨-, h0, h3, h5, h12, h7, h8, -⟩ := h
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact h0
        · exact h3
        · exact h5
        · exact h12
        · exact h7
        · exact h8) (by taint_decide))
    fun p k s hk ⟨h0, h3, h5, h12, h7, h8, hwx, hwx', hw⟩ => WP.mono (kStep_ok hwx (by omega) rfl hk h3 h5 h12 h7 h8)
      fun s' ⟨⟨h3', h4', _⟩, k'⟩ => ⟨eval_nz_count hk h4', fun _ => ⟨(k'.gpr .x0 (by decide)).trans h0, h3',
        (k'.gpr .x5 (by decide)).trans h5, (k'.gpr .x12 (by decide)).trans h12, (k'.gpr .x7 (by decide)).trans h7,
        (k'.gpr .x8 (by decide)).trans h8, hwx, hwx', hw⟩, fun _ => (k'.gpr .x0 (by decide)).trans h0⟩

/-- After `gHead`: `D`. -/
def GHd (sl : Nat) (p : GPub) (t : State) : Prop :=
  ∃ s, GPre sl p s ∧ t.gpr .x3 = BitVec.ofNat 64 (gD p.w p.wx) ∧
    t.mem = s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx)) ∧ Keep mmRegs s t

/-- After `D`'s top bit into `sCnt`. -/
def GTop (sl : Nat) (p : GPub) (t : State) : Prop :=
  ∃ s, GPre sl p s ∧ Good t p.B p.Z p.w p.minv ∧
    t.mem = (s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))).writeW (off p.B (8 * Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) ∧ Keep mmRegs s t

theorem gHead_eq (sl : Nat) : gHead sl = [
    .block (([ldh .x5 sl] : List Instr) ++ [ldw .x5 .x5 sW, ldh .x12 sW, movi .x3 0, movi .x7 0, movi .x8 1]),
    .loop (.block [.add .x .x3 .x3 .x5, .subs .x .x4 .x3 .x12, .csel .x .x4 .x7 .x8]) (.nonzero .x .x4),
    .block [.add .x .x3 .x3 .x5, .sub .x .x3 .x3 .x12, .lsl .x .x3 .x3 6, sth .x3 sD]] := rfl

/-- `gHead`, given that the taint analysis checks the load of the prime's
base (`by taint_decide` for a given `sl`). -/
theorem gHead_ct {sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x5 sl]) hc).isSome = true) :
    RelCT isa (Two (GPre sl)) (seqs (gHead sl)) fun _ _ => True := by
  rw [gHead_eq]
  simp only [seqs]
  refine RelCT.seq (RelCT.block_append
    (RelCT.seq (two_piece (Ψ := GA sl) [.x0] (pins_x0B (fun p => p.B) fun _ _ h => h.1.x0) hT ?_)
      (two_piece (Ψ := GBk) [.x0, .x5] (pins_of (fun p r => if r = .x0 then p.B else p.Bx) fun p s h r hr => ?_)
        (by taint_decide) ?_)))
    (RelCT.seq (kLoop_ct.mono (fun _ _ h => two_mono (fun p s h' => ⟨?_, h'⟩) h) fun _ _ h => h)
      (two_taint [.x0] (pins_x0B (fun p => p.B) fun _ _ h => h) (by taint_decide)))
  · intro p s h
    obtain ⟨hg, hZ, _, _, _, _, _, _, _, _, hsl, hX, _⟩ := id h
    exact WP.mono (WP.keep [.x5] (Q := fun t => t.gpr .x5 = p.Bx ∧ t.mem = s.mem)
      (by brun [hg.x0, hdr_enc hsl, hg.ld hZ hsl, hX]) rfl rfl rfl)
      fun t ⟨⟨h1, h2⟩, k⟩ => ⟨s, h, h2, k, h1⟩
  · obtain ⟨σ, hσ, -, k, h5⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (k.gpr .x0 (by decide)).trans hσ.1.x0
    · exact h5
  · rintro p t ⟨s, ⟨hg, hZ, _, hw30, _, _, _, _, _, _, _, _, hXw, hXr, hwx, hwx'⟩, hm, k, h5⟩
    have h0 : t.gpr .x0 = p.B := (k.gpr .x0 (by decide)).trans hg.x0
    have hXr' : InRegions (t.rd ++ t.wr) (off p.Bx (8 * sW)) 8 := by rw [k.rd, k.wr]; exact hXr
    have hW : InRegions (t.rd ++ t.wr) (off p.B (8 * sW)) 8 := by
      rw [k.rd, k.wr]; exact hg.ld hZ (show sW < 32 by decide)
    have hXw' : word t.mem p.Bx (8 * sW) = BitVec.ofNat 64 p.wx := by rw [hm]; exact hXw
    have hw' : word t.mem p.B (8 * sW) = BitVec.ofNat 64 p.w := by rw [hm]; exact hg.hdr.hw
    exact WP.mono (WP.keep [.x3, .x5, .x7, .x8, .x12] (Q := fun t' => t'.gpr .x5 = BitVec.ofNat 64 p.wx ∧
        t'.gpr .x12 = BitVec.ofNat 64 p.w ∧ t'.gpr .x3 = BitVec.ofNat 64 0 ∧ t'.gpr .x7 = 0 ∧ t'.gpr .x8 = 1)
      (by brun [ldw, h0, h5, hdr_enc (show sW < 32 by decide), hXr', hXw', hW, hw'])
      (by decide) (by decide) (by decide +kernel))
      fun t' ⟨⟨a, b, c, d, e⟩, k'⟩ => ⟨(k'.gpr .x0 (by decide)).trans h0, by rw [c, Nat.zero_mul], a, b, d, e, hwx,
        hwx', hw30⟩
  · obtain ⟨-, -, -, -, -, -, hwx, hwx', -⟩ := h'
    exact (lt_chunks (k := 0) hwx).mpr (by omega)

/-- `D`'s top bit into `sCnt`. -/
theorem gTop_ct (sl : Nat) : RelCT isa (Two (GHd sl)) (.seq topBit (.block [sth .x9 Public.sCnt]))
    (Two (GTop sl)) := by
  refine two_piece [.x3, .x0] (pins_of (fun p r => if r = .x3 then BitVec.ofNat 64 (gD p.w p.wx) else p.B)
    fun p s h r hr => ?_) (by taint_decide) ?_
  · obtain ⟨σ, hσ, h3, -, k⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h3
    · exact (k.gpr .x0 (by decide)).trans hσ.1.x0
  rintro p t₁ ⟨s, h, h3₁, hm₁, k₁⟩
  obtain ⟨hg, hZ, hw, hw30, _, _, _, _, _, _, _, _, _, _, hwx, hwx'⟩ := id h
  obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
  have hs₁ := hg.scr.congr k₁.wr
  have h0₁ : t₁.gpr .x0 = p.B := (k₁.gpr .x0 (by decide)).trans hg.x0
  refine WP.seq (WP.mono (topBit_ok h3₁ hD0 (by omega)) fun t₂ ⟨⟨h9₂, _, hm₂⟩, k₂⟩ => ?_)
  have hs₂ := hs₁.congr k₂.wr
  have h0₂ : t₂.gpr .x0 = p.B := (k₂.gpr .x0 (by decide)).trans h0₁
  refine WP.mono (WP.keep [] (Q := fun t => t.mem = t₂.mem.writeW (off p.B (8 * Public.sCnt))
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2))) (by
    brun [h0₂, hdr_enc (show Public.sCnt < 32 by decide), hs₂.st (show 8 * Public.sCnt + 8 ≤ p.Z by
      have := hdr_lt_slot p.w 8 (show Public.sCnt < 32 by decide); omega), h9₂]) (by decide) (by decide)
    (by decide +kernel)) fun t₃ ⟨hm₃, k₃⟩ => ?_
  have hm₃' : t₃.mem = (s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))).writeW
      (off p.B (8 * Public.sCnt)) (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) := by rw [hm₃, hm₂, hm₁]
  exact ⟨s, h,
    ⟨hs₂.congr k₃.wr, (k₃.gpr .x0 (by decide)).trans h0₂, by
      rw [hm₃']; exact Hdr.store (Hdr.store hg.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    hm₃', ((k₁.trans k₂).trans k₃).mono (by decide)⟩

/-- `Y := R`: the loop's start. -/
theorem gStart_ok (M : Mont) {sl : Nat} {p : GPub} {t : State} (h : GTop sl p t) :
    WP isa (M.mm Public.aY Public.aR2 Public.aOne) t fun t' => 0 < (gD p.w p.wx).log2 + 1 ∧ GLoop p 0 t' := by
  obtain ⟨s, ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2', hone, _, _, _, _, hwx, hwx'⟩, hg₃, hm₃', k₃⟩ := h
  have hnw := hg.scr.nowrap
  have hn' : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * p.w)) p.N := VG.Proof.Bignum.coprime_pow2 hodd _
  obtain ⟨hD0, hD1, -⟩ := gD_bounds hwx hwx' hw30
  have hwv₃ : ∀ j < 8, wv t.mem p.B (slot p.w j) p.w = wv s.mem p.B (slot p.w j) p.w := fun j hj => by
    rw [hm₃', hdrStore_wv _ _ _ (by decide) hj hn', hdrStore_wv _ _ _ (by decide) hj hn']
  refine WP.mono (crtMmN_ok M (N := p.N) (o := Public.aY) (a := Public.aR2) (b := Public.aOne) hg₃ hZ hw (by omega)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((hwv₃ Public.aN (by decide)).trans hn)
    (by rw [hm₃', hdrStore_word _ _ _ (by decide) (by decide) hn', hdrStore_word _ _ _ (by decide) (by decide) hn'];
        exact hinv)
    (by rw [hwv₃ Public.aOne (by decide), hone]; exact hN1))
    fun t₄ ⟨hg₄, hn₄, hinv₄, hlt₄, hm₄, ha₄, k₄⟩ => ⟨by omega, s, ?_, hZ, hw, hw30, hodd, hN1, hwx, hwx'⟩
  rw [hwv₃ Public.aR2 (by decide), hwv₃ Public.aOne (by decide), hone, Nat.mul_one] at hm₄
  have hY₄ : wv t₄.mem p.B (slot p.w Public.aY) p.w % p.N =
      2 ^ ((gD p.w p.wx) / 2 ^ ((gD p.w p.wx).log2 + 1 - 0)) * 2 ^ (64 * p.w) % p.N := by
    rw [Nat.sub_zero, Nat.div_eq_of_lt Nat.lt_log2_self, Nat.pow_zero, Nat.one_mul]
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hr2']
  have hfr₄ : Frm p.B (gRanges p.w) s.mem t₄.mem := by
    have o1 := writeW_outside s.mem p.B (BitVec.ofNat 64 (gD p.w p.wx)) (d := 8 * sD) (by unfold sD sFn; omega)
    have o2 := writeW_outside (s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx))) p.B
      (BitVec.ofNat 64 (2 ^ (gD p.w p.wx).log2)) (d := 8 * Public.sCnt) (by unfold Public.sCnt sFn; omega)
    rw [← hm₃'] at o2
    exact ((Frm.of_outside o1 (by simp [gRanges])).trans (Frm.of_outside o2 (by simp [gRanges]))).trans
      (Frm.of_arrays ha₄ (by simp [gRanges]))
  exact ⟨hg₄, hn₄, hinv₄, hlt₄, hY₄,
    by rw [ha₄.hslot (by decide), hm₃', hdrStore_hdr _ _ _ (by decide) (by decide) (by decide), word_writeW_self],
    by rw [ha₄.hslot (by decide), hm₃', word_writeW_self, Nat.sub_zero, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)],
    hfr₄, (k₃.trans k₄).mono (by decide)⟩

/-- After `gHead`, and where `gSlow` starts: `D` in slot `sD`. -/
def GSl (sl : Nat) (p : GPub) (t : State) : Prop :=
  ∃ s, GPre sl p s ∧ t.mem = s.mem.writeW (off p.B (8 * sD)) (BitVec.ofNat 64 (gD p.w p.wx)) ∧ Keep mmRegs s t

/-- `n`'s top word, which `gPow` tests. -/
def GPub.top (p : GPub) : Nat := p.N / 2 ^ (64 * (p.w - 1))

/-- After `gTest`. -/
def GT2 (sl : Nat) (p : GPub) (t : State) : Prop :=
  GSl sl p t ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧ (t.gpr .x4).toNat = p.top

/-- After `gCmp`. -/
def GT3 (sl : Nat) (p : GPub) (t : State) : Prop :=
  GSl sl p t ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x13 = BitVec.ofNat 64 (gC p.w p.wx) ∧
    t.gpr .x6 = BitVec.ofNat 64 (decide (gC p.w p.wx < p.w - 1)).toNat ∧ p.top ≠ 0

/-- Where `gFast` starts. -/
def GFs (sl : Nat) (p : GPub) (t : State) : Prop :=
  GSl sl p t ∧ t.gpr .x12 = BitVec.ofNat 64 p.w ∧ t.gpr .x13 = BitVec.ofNat 64 (gC p.w p.wx) ∧
    gC p.w p.wx < p.w - 1 ∧ p.top ≠ 0

theorem GSl.good {sl : Nat} {p : GPub} {t : State} (h : GSl sl p t) :
    Good t p.B p.Z p.w p.minv ∧ slot p.w 8 ≤ p.Z := by
  obtain ⟨s, hs, hm, k⟩ := h
  exact ⟨⟨hs.1.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hs.1.x0,
    by rw [hm]; exact Hdr.store hs.1.hdr (by decide) (by decide) _⟩, hs.2.1⟩

theorem GPre.hyp {sl : Nat} {p : GPub} {s : State} (h : GPre sl p s) : GHyp s p.B p.Z p.w p.minv p.N p.wx := by
  obtain ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2, hone, _, _, _, _, hwx, hwx'⟩ := h
  exact ⟨hg, hZ, hw, hw30, hn, hinv, hodd, hN1, hr2, hone, hwx, hwx'⟩

/-- `GSl` past a step that keeps the memory and the registers but `rs`. -/
theorem GSl.step {sl : Nat} {p : GPub} {t t' : State} {rs : List Reg} (h : GSl sl p t) (hm : t'.mem = t.mem)
    (k : Keep rs t t') (hrs : ∀ r ∈ rs, r ∈ mmRegs) : GSl sl p t' := by
  obtain ⟨s, hs, hm₀, k₀⟩ := h
  exact ⟨s, hs, hm.trans hm₀, (k₀.trans k).mono fun r hr => by
    rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · exact hrs r hr⟩

/-- `gSlow`: `D` into `x3`, its top bit, `Y := R` and the bits of `D`. -/
theorem gSlow_ct (M : Mont) (sl : Nat) : RelCT isa (Two (GSl sl)) (gSlow M.mm) fun _ _ => True := by
  rw [gSlow_eq]
  refine RelCT.seq (two_piece (Ψ := GHd sl) [.x0] (pins_x0B (fun p => p.B) fun _ _ h => h.good.1.x0)
    (by taint_decide) fun p t h => ?_) ?_
  · obtain ⟨s, hs, hm, k⟩ := h
    exact WP.mono (gLdD_ok hs.1 hs.2.1 hm k) fun t' ⟨h3, hm', k'⟩ =>
      ⟨s, hs, h3, hm'.trans hm, (k.trans k').mono (by decide)⟩
  refine RelCT.assoc (RelCT.seq (gTop_ct sl) (RelCT.seq (two_post (two_map (fun p => p.L.ws)
    (fun p s h => ?_) (M.ct (by unfold MmUse; decide))) fun p s h => gStart_ok M h)
    ((gLoop_ct M).mono (fun _ _ h => h) fun _ _ _ => trivial)))
  obtain ⟨_, ⟨_, hZ, _⟩, hg, _⟩ := h
  exact ⟨p.minv, hg, hZ⟩

/-- `gFast`: `Y := 2^D`, then `Y := R² Y R⁻¹`. -/
theorem gFast_ct (M : Mont) (sl : Nat) : RelCT isa (Two (GFs sl)) (gFast M.mm) fun _ _ => True := by
  rw [gFast_eq, setWord_eq]
  -- `x9 := 1`.
  refine RelCT.seq (two_piece (Ψ := GFs sl) [] (pins_of (fun _ _ => 0) fun _ _ _ _ hr => absurd hr List.not_mem_nil)
    (by taint_decide) fun p t h => ?_) ?_
  · refine WP.mono (WP.keep [.x9] (Q := fun t' => t'.mem = t.mem) (by brun) (by decide) (by decide)
      (by decide +kernel)) fun t' ⟨hm, k⟩ => ?_
    obtain ⟨hS, h12, h13, hc, htop⟩ := h
    exact ⟨hS.step hm k (by decide), (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13,
      hc, htop⟩
  -- `Y := 2^D`.
  refine RelCT.seq (two_post (Ψ := fun p t => Good t p.B p.Z p.w p.minv ∧ slot p.w 8 ≤ p.Z) ?_ ?_) ?_
  · refine RelCT.seq (two_piece (Ψ := fun p t => GFs sl p t ∧ t.gpr .x8 = off p.B (slot p.w Public.aY) ∧
        t.gpr .x7 = 0) [.x0] (pins_x0B (fun p => p.B) fun _ _ h => h.1.good.1.x0) (by taint_decide)
        fun p t h => ?_)
      (two_taint [.x8, .x7, .x12, .x13] (pins_of (fun p r => if r = .x8 then off p.B (slot p.w Public.aY) else
        if r = .x7 then 0 else if r = .x12 then BitVec.ofNat 64 p.w else BitVec.ofNat 64 (gC p.w p.wx))
          fun p t h r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl | rfl
            · exact h.2.1
            · exact h.2.2
            · exact h.1.2.1
            · exact h.1.2.2.1) (by taint_decide))
    obtain ⟨hg, hZ⟩ := h.1.good
    have hl : InRegions (t.rd ++ t.wr) (off p.B (8 * sArr Public.aY)) 8 :=
      hg.scr.ld (by have := hdr_lt_slot p.w 8 (show sArr Public.aY < 32 by decide); omega)
    refine WP.mono (WP.keep [.x7, .x8] (Q := fun t' => (t'.gpr .x8 = off p.B (slot p.w Public.aY) ∧
        t'.gpr .x7 = 0) ∧ t'.mem = t.mem)
      (by brun [hg.x0, hdr_enc (show sArr Public.aY < 32 by decide), hl, hg.hdr.harr Public.aY (by decide)])
      (by decide) (by decide) (by decide +kernel)) fun t' ⟨⟨⟨h8, h7⟩, hm⟩, k⟩ => ⟨?_, h8, h7⟩
    obtain ⟨hS, h12, h13, hc, htop⟩ := h
    exact ⟨hS.step hm k (by decide), (k.gpr .x12 (by decide)).trans h12, (k.gpr .x13 (by decide)).trans h13,
      hc, htop⟩
  · intro p t ⟨hS, h12, h13, hc, htop⟩
    obtain ⟨hg, hZ⟩ := hS.good
    obtain ⟨_, hs, _, _⟩ := hS
    refine WP.mono (setWord_ok hg.scr hg.x0 hg.hdr hZ h12 (by have := hs.2.2.2.1; omega) (o := Public.aY)
      (by decide) (i := gC p.w p.wx) (by omega) h13) fun t' ⟨_, ho, k⟩ => ?_
    have ha : Arrays p.B p.w [Public.aY] t.mem t'.mem :=
      Arrays.of_outside (List.mem_singleton_self _) ho (Nat.le_refl _) (Nat.le_refl _)
    exact ⟨⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, ha.hdr hg.hdr⟩, hZ⟩
  -- `Y := R² Y R⁻¹`.
  exact two_map (fun p => p.L.ws) (fun p _ h => ⟨p.minv, h.1, h.2⟩) (M.ct (by unfold MmUse; decide))

/-- `gPow sl`, given that the taint analysis checks the load of the
prime's base: its branches are on `n`'s top word and the lengths, which the
relation fixes. -/
theorem gPow_ct_of {M : Mont} {sl : Nat} {hc : VG.Taint.Hint VG.AArch64.Taint.T}
    (hT : (taint.check (Taint.ofRegs [.x0]) (.block [ldh .x5 sl]) hc).isSome = true) :
    GPowCT M sl := by
  unfold GPowCT
  rw [gPow_eq]
  refine RelCT.seqs_append (by simp [gHead]) (by simp) (RelCT.seq (two_post (Ψ := GSl sl) (gHead_ct hT)
    fun p s h => ?_) ?_)
  · obtain ⟨hg, hZ, hw, hw30, _, _, _, _, _, _, hsl, hX, hXw, hXr, hwx, hwx'⟩ := id h
    exact WP.mono (gHead_ok hg hZ hw hw30 hsl hX hXw hXr hwx hwx') fun t ⟨_, h2, h3⟩ =>
      ⟨s, h, h2, h3.mono (by decide)⟩
  show RelCT isa (Two (GSl sl)) (.seq (.block gTest) (.ite (.zero .x .x4) (gSlow M.mm)
    (.seq (.block gCmp) (.ite (.zero .x .x6) (gSlow M.mm) (gFast M.mm))))) _
  -- `n`'s top word.
  have hTct : RelCT isa (Two (GSl sl)) (.block gTest) fun _ _ => True := by
    rw [show gTest = ([ldh .x12 sW, ldh .x10 (sArr Public.aN)] : List Instr) ++
      [.lsl .x .x13 .x12 3, .subImm .x .x13 .x13 8, .add .x .x13 .x10 .x13, ld .x4 .x13] from rfl]
    refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun p t => t.gpr .x12 = BitVec.ofNat 64 p.w ∧
        t.gpr .x10 = off p.B (slot p.w Public.aN)) [.x0] (pins_x0B (fun p => p.B) fun _ _ h => h.good.1.x0)
        (by taint_decide) fun p t h => ?_)
      (two_taint [.x10, .x12] (pins_of (fun p r => if r = .x10 then off p.B (slot p.w Public.aN) else
        BitVec.ofNat 64 p.w) fun p t h r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact h.2
          · exact h.1) (by taint_decide)))
    obtain ⟨hg, hZ⟩ := h.good
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.B (8 * i)) 8 := fun i hi =>
      hg.scr.ld (by have := hdr_lt_slot p.w 8 hi; omega)
    exact WP.mono (WP.keep [.x10, .x12] (Q := fun t' => t'.gpr .x12 = BitVec.ofNat 64 p.w ∧
        t'.gpr .x10 = off p.B (slot p.w Public.aN))
      (by brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr Public.aN < 32 by decide),
        hl sW (by decide), hl (sArr Public.aN) (by decide), hg.hdr.hw, hg.hdr.harr Public.aN (by decide)])
      (by decide) (by decide) (by decide +kernel)) fun _ ⟨h', _⟩ => h'
  refine RelCT.seq (two_post (Ψ := GT2 sl) hTct fun p t h => ?_) ?_
  · obtain ⟨hg, hZ⟩ := h.good
    obtain ⟨s, hs, hm, _⟩ := id h
    have hn' : p.B.toNat + slot p.w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
    have hT := wv_top t.mem p.B (slot p.w Public.aN) p.w (by have := hs.2.2.1; omega)
    rw [hm, hdrStore_wv _ _ _ (by decide) (by decide) hn', hs.2.2.2.2.1, ← hm] at hT
    exact WP.mono (gTest_ok hg.scr hg.x0 hg.hdr hZ hs.2.2.1 (by have := hs.2.2.2.1; omega))
      fun t' ⟨h4, h12, hm', k⟩ => ⟨h.step hm' k (by decide), h12, by rw [h4, hT]; rfl⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by
      rw [eval_zero, eval_zero, gBeq_zero, gBeq_zero, h₁.2.2, h₂.2.2])
    (two_map id (fun p t h => h.1.1) (gSlow_ct M sl)) ?_
  -- `D / 64 < w - 1`.
  refine RelCT.seq (two_piece (Ψ := GT3 sl) [.x0] (pins_x0B (fun p => p.B) fun _ _ h => h.1.1.good.1.x0)
    (by taint_decide) fun p t h => ?_) ?_
  · obtain ⟨⟨hS, h12, h4⟩, hne⟩ := h
    have htop : p.top ≠ 0 := fun h0 => by
      rw [eval_zero, gBeq_zero, h4, h0] at hne; exact absurd hne (by decide)
    obtain ⟨hg, hZ⟩ := hS.good
    obtain ⟨s, hs, hm, _⟩ := id hS
    exact WP.mono (gCmp_ok hg.scr hg.x0 hZ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 h12 (by rw [hm, word_writeW_self]))
      fun t' ⟨h6, h13, h12', hm', k⟩ => ⟨hS.step hm' k (by decide), h12', h13, h6, htop⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.2.2.2.1, h₂.2.2.2.1])
    (two_map id (fun p t h => h.1.1) (gSlow_ct M sl)) (two_map id (fun p t h => ?_) (gFast_ct M sl))
  obtain ⟨⟨hS, h12, h13, h6, htop⟩, hb⟩ := h
  refine ⟨hS, h12, h13, ?_, htop⟩
  by_contra hc
  have hc' : ¬ gC p.w p.wx < p.w - 1 := hc
  rw [eval_zero, h6, decide_eq_false hc'] at hb
  exact absurd hb (by decide)

theorem gPow_ct_P (M : Mont) : GPowCT M sWsP := gPow_ct_of (by taint_decide)

theorem gPow_ct_Q (M : Mont) : GPowCT M sWsQ := gPow_ct_of (by taint_decide)

end VG.Proof.Bignum.AArch64
