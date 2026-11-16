module
public import VerifiedGarbage.Proof.Dsa.AArch64.SharedStore
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Dsa.AArch64.SharedStore
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorStepCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTDefs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Run
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # The masked store's addresses do not depend on the digit -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.SharedPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Bignum.AArch64.WindowVector
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Dsa.AArch64.SharedPower

/-- `store_ok`'s hypotheses: the digit, in `sNib`, is not among the public data. -/
def StorePre (p : XPub) (s : State) : Prop :=
  ∃ (mi : BitVec 64) (X Xc v : Nat), CExpCtx s (off p.B p.o) p.wx mi X Xc ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧
    p.wx % 8 = 0 ∧ v < 8 ∧ word s.mem (off p.B p.o) (8 * Crt.sTab) = off (off p.B p.o) (slot p.wx 8) ∧
    word s.mem (off p.B p.o) (8 * Crt.sNib) = BitVec.ofNat 64 v

def StoreLoopPre (p : XPub) (j : Nat) (s : State) : Prop :=
  ∃ s₀ mi X Xc v, StoreInv s₀ (off p.B p.o) p.wx mi X Xc v j s ∧ 8 ≤ p.wx ∧ p.wx < 2 ^ 30 ∧ v < 8 ∧
    s.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - j)

def StoreStepPre (q : XPub × Nat) (s : State) : Prop :=
  ∃ mi X Xc v, CExpCtx s (off q.1.B q.1.o) q.1.wx mi X Xc ∧ 8 * q.2 + 8 ≤ q.1.wx ∧
    word s.mem (off q.1.B q.1.o) (8 * Crt.sTab) = off (off q.1.B q.1.o) (slot q.1.wx 8) ∧
    s.gpr .x6 = BitVec.ofNat 64 (8 * (q.1.wx + 2)) ∧
    s.gpr .x17 = off (off q.1.B q.1.o) (slot q.1.wx Crt.aT + 64 * q.2) ∧
    s.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ s.v .v24 = dup2 1

theorem storeStep_pins : Pins StoreStepPre [.x0, .x17] := by
  intro q s t hs ht r hr
  obtain ⟨_, _, _, _, cs, _, _, _, ps, _⟩ := hs
  obtain ⟨_, _, _, _, ct, _, _, _, pt, _⟩ := ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact cs.good.x0.trans ct.good.x0.symm
  · exact ps.trans pt.symm

theorem storeRaw_ct : RelCT isa (Two StoreStepPre) storeRaw (fun _ _ => True) := by
  unfold storeRaw
  refine RelCT.seq (two_piece (Ψ := ScanPins 8) [.x0, .x17] storeStep_pins (by taint_decide) ?_)
    (two_taint [.x16, .x6, .x14, .x17] (scan_pins 8) (by taint_decide))
  rintro q s ⟨mi, X, Xc, v, hc, hb, ht, h6, h17, h22, h24⟩
  exact WP.mono (storeHead_ok hc hb ht h17) fun a ⟨h16, h14, _, _, _, ka⟩ =>
    ⟨h16, (ka.gpr .x6 (by decide)).trans h6, h14, (ka.gpr .x17 (by decide)).trans h17⟩

theorem storeLoop_ct :
    RelCT isa (Two fun p s => 0 < p.wx / 8 ∧ StoreLoopPre p 0 s) (.loop storeRaw (.nonzero .x .x13))
      (fun _ _ => True) := by
  refine (two_loop (Φ := StoreLoopPre) (Ψ := fun _ _ => True) (fun p : XPub => p.wx / 8)
    (two_map id ?_ storeRaw_ct) ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  · rintro ⟨p, j⟩ s ⟨hj, _, mi, X, Xc, v, hI, _⟩
    have hj' : j < p.wx / 8 := hj
    exact ⟨mi, X, Xc, v, hI.ctx, show 8 * j + 8 ≤ p.wx by omega_using [hj'], hI.tab, hI.stride, hI.ptr, hI.digit, hI.one⟩
  rintro p j s hj ⟨s₀, mi, X, Xc, v, hI, hw, hw', hv, h13⟩
  refine WP.mono ((storeRaw_wp _ _).mpr (storeStep_ok hv (by omega_using [hj]) hI)) fun t ⟨ht, hc⟩ => ?_
  have h13' : t.gpr .x13 = BitVec.ofNat 64 (p.wx / 8 - (j + 1)) := by
    rw [hc, h13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_using [hj]
  have hz : (t.gpr .x13).toNat ≠ 0 ↔ j + 1 ≠ p.wx / 8 := by
    rw [h13', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show p.wx / 8 - (j + 1) < 2 ^ 64 by omega_using [hw'])]
    omega_using [hj]
  exact ⟨eval_nz_count hj hz, fun _ => ⟨s₀, mi, X, Xc, v, ht, hw, hw', hv, h13'⟩, fun _ => trivial⟩

theorem storeSetup_ready {p : XPub} {s : State} (h : StorePre p s) :
    WP isa (.block setup) s fun t => 0 < p.wx / 8 ∧ StoreLoopPre p 0 t := by
  obtain ⟨mi, X, Xc, v, hc, hw, hw', _, hv, ht, hN⟩ := h
  refine WP.mono (setup_ok hc hw' hN) fun u ⟨⟨h6, h13, h17, h22, h24, hm⟩, ku⟩ => ?_
  have ctx := hc.of_win (by rw [hm]; exact Frm.refl _ _ _) ku.wr (ku.gpr .x0 (by decide))
  refine ⟨by omega_using [hw], u, mi, X, Xc, v, ?_, hw, hw', hv, by simpa using h13⟩
  exact ⟨ctx, by rw [hm]; exact ht, h6, by simpa using h17, h22, h24,
    Outside.refl _ _ _ _, fun _ h => by omega, Keep.refl _ _⟩

/-- The masked store leaks the same in runs with the same workspace. -/
theorem store_ct : RelCT isa (Two StorePre) store (fun _ _ => True) := by
  rw [store_eq]
  exact RelCT.seq (two_piece (Ψ := fun p s => 0 < p.wx / 8 ∧ StoreLoopPre p 0 s) [.x0]
    (pins_x0B (fun p : XPub => off p.B p.o) (fun _ _ ⟨_, _, _, _, hc, _⟩ => hc.good.x0)) (by taint_decide)
    (fun _ _ h => storeSetup_ready h)) storeLoop_ct

end VG.Proof.Dsa.AArch64.SharedPower
