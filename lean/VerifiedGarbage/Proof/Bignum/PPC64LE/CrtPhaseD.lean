module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP2
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Rsa.Octets

/-! ### `Bignum.PPC64LE.CrtRecP`, which only this module used -/

section

/-! ### `Bignum.PPC64LE.CrtRecP3`, which only this module used -/

section

/-!
# The RSA private-key operation on PPC64LE: `h`

`recP3_ok`: in `p`'s working space, `a qInv mod p` into array 4, for `a` in
array 3, `R² mod p` in array 7 and `qInv` from `X`'s array 7, by two
Montgomery multiplications.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- Two Montgomery multiplications, the second by `R² mod P`: the product. -/
theorem mont_chain {P R a q x5 x4 : Nat} (hR : Nat.Coprime R P) (h5 : x5 * R % P = a * q % P)
    (h4 : x4 * R % P = x5 * (R * R % P) % P) (h4P : x4 < P) : x4 = a * q % P := by
  obtain e : x4 * R % P = a * q * R % P := by
    rw [h4, Nat.mul_mod_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, h5, Nat.mod_mul_mod]
  rw [← Nat.mod_eq_of_lt h4P]
  exact VG.Proof.Bignum.mont_cancel hR e

/-- `recombineP`'s end, in `p`'s working space `off BX oA` (`-p⁻¹ mod 2³²` in
`r12`): `qInv` (`w_P` words of `X`'s array 7) into array 6, then
`a qInv R⁻¹ mod p` into array 5 and `a qInv mod p` into array 4. -/
theorem recP3_ok {s : State} {BX : Addr} {Z oA wP wX Pv a QI : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (off BX oA) (slot wP 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hPodd : Pv % 2 = 1)
    (ha : val32 s.mem (off BX oA) (slot wP 3) (2 * wP) = a)
    (hRR : val32 s.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv)
    (hQ : wv s.mem BX (slot wX 7) wP = QI) (hQP : QI < Pv) :
    WP isa (.seq (.block (PublicChecked.base .r14 6 ++ xb .r15 7)) (.seq copyN
      (.seq (PublicChecked.montOp 5 3 6) (PublicChecked.montOp 4 5 7)))) s fun t =>
      (val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = a * QI % Pv ∧
        Outside BX oA (slot wP 24) s.mem t.mem) ∧ Keep (.r14 :: .r15 :: Pub.montRegs) s t := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eA0 := e wP 0; have eA2 := e wP 2; have eA3 := e wP 3; have eA4 := e wP 4; have eA5 := e wP 5
  obtain eA6 := e wP 6; have eA7 := e wP 7; have eA8 := e wP 24
  obtain sX7 := slot_le (w := wX) (show 7 < 8 by decide)
  obtain hsA := hs.sub hA
  have hnA := hsA.nowrap
  obtain hA' : oA + slot wP 24 ≤ 2 ^ 64 := by omega_arith
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 6) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) 7) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (b := oA + slot wP 6) (hs.congr k12.wr) a15
    (by rw [k2.gpr _ (by decide), a14, off_off]) ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw'
    (by omega_arith) (by omega_arith) (by omega_arith)) fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  obtain o3 : Mont.Outside (off BX oA) (slot wP 6) (8 * wP) s.mem s₃.mem :=
    fun x hx => out_super out3 (by omega_arith) x hx
  obtain v6 : val32 s₃.mem (off BX oA) (slot wP 6) (2 * wP) = QI := by
    rw [Pre.val32_eq_wv, wv_off, ← hQ]; exact wv_congr2 fun i hi => hw3 i hi
  obtain v0 : val32 s₃.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o3.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  obtain v3 : val32 s₃.mem (off BX oA) (slot wP 3) (2 * wP) = a := by
    rw [o3.val32 (Or.inl (by omega_arith)) (by omega_arith), ha]
  obtain v7 : val32 s₃.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv := by
    rw [o3.val32 (Or.inr (by omega_arith)) (by omega_arith), hRR]
  obtain w0 : w32 s₃.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) :=
    o3.w32 (Or.inl (by omega_arith)) (by omega_arith)
  obtain g12 : s₃.gpr .r12 = s.gpr .r12 := k13.gpr _ (by decide)
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 5) (a := 3) (b := 6) (hsA.congr k13.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by unfold slot; omega_arith)
    ((k13.gpr _ (by decide)).trans h10) ((k13.gpr _ (by decide)).trans h29)
    ((k13.gpr _ (by decide)).trans h11) (by rw [g12]; exact h12) (by rw [g12, w0]; exact hinv)
    (by rw [v6, v0]; exact hQP)) fun s₄ ⟨⟨l5, e5, o4⟩, k4⟩ => ?_)
  obtain k14 := k13.trans k4
  rw [v0, v3, v6] at e5
  rw [v0] at l5
  obtain hpr : ∀ j, j ≠ 2 → j ≠ 3 → j ≠ 5 → j < 8 →
      ∀ r ∈ [(slot wP 2, 8 * (wP + 2)), (slot wP 3, 8 * (wP + 2)), (slot wP 5, 8 * (wP + 2))],
        slot wP j + 4 * (2 * wP) ≤ r.1 ∨ r.1 + r.2 ≤ slot wP j := by
    intro j h2 h3 h5 h8 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain s2 := slot_sep (w := wP) h2; have s3 := slot_sep (w := wP) h3; have s5 := slot_sep (w := wP) h5
    rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith
  obtain v0' : val32 s₄.mem (off BX oA) (slot wP 0) (2 * wP) = Pv := by
    rw [o4.val32 (hpr 0 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v0]
  obtain v7' : val32 s₄.mem (off BX oA) (slot wP 7) (2 * wP) = 2 ^ (64 * wP) * 2 ^ (64 * wP) % Pv := by
    rw [o4.val32 (hpr 7 (by decide) (by decide) (by decide) (by decide)) (by omega_arith), v7]
  obtain w0' : w32 s₄.mem (off BX oA) (slot wP 0) = w32 s.mem (off BX oA) (slot wP 0) := by
    rw [← w0]
    refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => o4 _ fun r hr => ?_)
    have := hpr 0 (by decide) (by decide) (by decide) (by decide) r hr
    rw [Mont.ofs_off (off BX oA) (d := slot wP 0) (i := i) (by omega_arith)]; omega_arith
  obtain g12' : s₄.gpr .r12 = s.gpr .r12 := k14.gpr _ (by decide)
  refine WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hsA.congr k14.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by unfold slot; omega_arith)
    ((k14.gpr _ (by decide)).trans h10) ((k14.gpr _ (by decide)).trans h29)
    ((k14.gpr _ (by decide)).trans h11) (by rw [g12']; exact h12) (by rw [g12', w0']; exact hinv)
    (by rw [v7', v0']; exact Nat.mod_lt _ (by omega_arith))) fun t ⟨⟨l4, e4, o5⟩, k5⟩ => ⟨⟨?_, ?_⟩, (k14.trans k5).mono⟩
  · rw [v0', v7'] at e4
    rw [v0'] at l4
    exact mont_chain (VG.Proof.Bignum.coprime_pow2 hPodd _) e5 e4 l4
  · have f4 := outs_sub o4 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) hA' (by omega_arith)
    obtain f5 := outs_sub o5 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) hA' (by omega_arith)
    exact ((out3.mono (by omega_arith) (by omega_arith)).trans f4).trans f5

end VG.Proof.Bignum.PPC64LE.Crt

end

end


/-!
# The RSA private-key operation on PPC64LE: `h` in `p`'s working space

`recombineP_ok`: `h = (m₁ + p - m₂ mod p) mod p · qInv mod p` into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `recombineP`, in `p`'s working space `off BX oA` (`P` in array 0, `m₁` in
array 4), for `m₂` the first `w_P n` words of `X`'s array 6 (`n` chunks of
`⌈k / 8⌉` words) and `qInv` in its array 7. -/
theorem recombineP_ok {pc : Bool} {s : State} {BX : Addr} {Z oA wP wX k Pv m1 m2 QI : Nat}
    (hs : Scr s BX Z) (hA : oA + slot wP 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wP) (hw' : wP < 2 ^ 31)
    (hwx : wP ≤ wX) (hwX : wX < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wP 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wP 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wP + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wP))
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k) (hk' : k < 2 ^ 40)
    (hnw : wP * nChunks ((k + 7) / 8) wP ≤ wX)
    (hP : val32 s.mem (off BX oA) (slot wP 0) (2 * wP) = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hm1 : val32 s.mem (off BX oA) (slot wP 4) (2 * wP) = m1) (hm1P : m1 < Pv)
    (hm2 : wv s.mem BX (slot wX 6) (wP * nChunks ((k + 7) / 8) wP) = m2)
    (hQ : wv s.mem BX (slot wX 7) wP = QI) (hQP : QI < Pv)
    (hR2 : pc = true → ∃ S pL b, R2C false s BX S Z wP Pv pL b) :
    WP isa (recombinePG pc) s fun t =>
      (val32 t.mem (off BX oA) (slot wP 4) (2 * wP) = (m1 + Pv - m2 % Pv) % Pv * QI % Pv ∧
        Outside BX oA (slot wP 24) s.mem t.mem) ∧ Keep recRegs s t := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eA0 := e wP 0; have eA3 := e wP 3; have eA4 := e wP 4; have eA7 := e wP 7; have eA8 := e wP 24
  obtain sX7 := slot_le (w := wX) (show 7 < 8 by decide)
  unfold recombinePG
  refine recP1_ok hs hA hXA hw2 hw' h10 h21 h29 h11 h23 h27 h28 hK hk hk' hnw hP hP2 hPodd hm1 hm2 hR2
    fun t₁ v0 v1 v4 v7 i12 iinv out1 t10 k1 => ?_
  obtain hsA := (hs.congr k1.wr).sub hA
  refine recP2a_ok (bj := 1) hsA (by unfold slot; omega_arith) (by decide) (by decide) (by decide) hw2 hw' t10
    ((k1.gpr _ (by decide)).trans h21) ((k1.gpr _ (by decide)).trans h29)
    ((k1.gpr _ (by decide)).trans h11) v0 v1 v4 (Nat.mod_lt _ (by omega_arith)) hm1P
    fun t₂ v3 out2 a10 k2 => ?_
  obtain hr2 : ∀ j, j ≠ 3 → j ≠ 4 → j < 8 →
      ∀ r ∈ [(slot wP 3, 8 * (wP + 2)), (slot wP 4, 8 * (wP + 2))],
        slot wP j + 4 * (2 * wP) ≤ r.1 ∨ r.1 + r.2 ≤ slot wP j := by
    intro j h3 h4 h8 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain s3 := slot_sep (w := wP) h3; have s4 := slot_sep (w := wP) h4
    rcases hr with rfl | rfl <;> simp only <;> omega_arith
  obtain out2' := outs_sub (S := slot wP 24) out2 (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only <;> omega_arith) (by omega_arith) (by omega_arith)
  obtain o12 := out1.trans out2'
  refine WP.mono (recP3_ok (hs.congr (k1.trans k2).wr) hA hXA hw2 hw' a10
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h29))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h11))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h27))
    ((k2.gpr _ (by decide)).trans ((k1.gpr _ (by decide)).trans h28))
    (by rw [k2.gpr _ (by decide)]; exact i12)
    (by
      rw [k2.gpr _ (by decide)]
      refine Eq.trans ?_ iinv
      refine congrArg (fun v => (v * (t₁.gpr .r12).toNat + 1) % 2 ^ 32) ?_
      refine congrArg BitVec.toNat (Mem.readW_congr fun i hi => out2 _ fun r hr => ?_)
      have := hr2 0 (by decide) (by decide) (by decide) r hr
      rw [Mont.ofs_off (off BX oA) (d := slot wP 0) (i := i) (by omega_arith)]; omega_arith)
    (by rw [out2.val32 (hr2 0 (by decide) (by decide) (by decide)) (by omega_arith), v0]) hPodd v3
    (by rw [out2.val32 (hr2 7 (by decide) (by decide) (by decide)) (by omega_arith), v7])
    (by rw [o12.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hQ) hQP)
    fun t ⟨⟨v4', out3⟩, k3⟩ => ⟨⟨v4', o12.trans out3⟩, ((k1.trans k2).trans k3).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt

end

end


/-!
# The RSA private-key operation on PPC64LE: `h`

`phaseD_ok`: `m₂` into `X`'s array 6 (`exportM2`), then, in `p`'s working
space, `h = (m₁ - m₂ mod p) qInv mod p` into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem Scr.le {s : State} {B : Addr} {Z n : Nat} (hs : Scr s B Z) (h : n ≤ Z) : Scr s B n :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega_arith, hL'⟩, by have := hs.nowrap; omega_arith⟩

/-- `exportM2`, `setupP oBP oPLen` and `recombineP`: with `q`'s working space
at `off BX oQ` (`m₂` below `256^qL` in array 4, `qL ≤ k`) and `p`'s at
`off BX oP` (`P` in array 0, `m₁ < P` in array 4), `qInv < P` in `X`'s array
7: `h` into `p`'s array 4. -/
theorem phaseD_ok {pc : Bool} {s : State} {BX : Addr} {Z oP oQ wX pL qL k Pv m1 M2 QI : Nat}
    (hs : Scr s BX Z) (hPZ : oP + slot (wsWords pL) 24 ≤ Z) (hXP : slot wX 8 ≤ oP)
    (hQZ : oQ + slot (wsWords qL) 24 ≤ Z) (hXQ : slot wX 8 ≤ oQ) (_hPQ : oP + slot (wsWords pL) 24 ≤ oQ)
    (hwP : wsWords pL ≤ wX) (hwQ : wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBP : word s.mem BX oBP = off BX oP) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hBQ : word s.mem BX oBQ = off BX oQ) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hp1 : 1 ≤ pL) (hp' : pL < 2 ^ 60) (hq1 : 1 ≤ qL)
    (hq' : qL < 2 ^ 60) (hqk : qL ≤ k) (hk' : k < 2 ^ 40)
    (hnw : wsWords pL * nChunks ((k + 7) / 8) (wsWords pL) ≤ wX)
    (hP0 : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 0) (2 * wsWords pL) = Pv) (hP2 : 2 ≤ Pv)
    (hPodd : Pv % 2 = 1) (hm1 : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) = m1)
    (hm1P : m1 < Pv) (hm2 : Mont.val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) = M2)
    (hm2b : M2 < 256 ^ qL) (hQI : Mont.val32 s.mem BX (slot wX 7) (2 * wX) = QI)
    (hQIb : QI < 2 ^ (64 * wsWords pL)) (hQP : QI < Pv)
    (hR2 : pc = true → ∃ S pL' b, R2C false s BX S Z (wsWords pL) Pv pL' b) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) (recombinePG pc))) s fun t =>
      (Mont.val32 t.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) =
          (m1 + Pv - M2 % Pv) % Pv * QI % Pv ∧
        Mont.Outs BX [(slot wX 6, 8 * wX), (oP, slot (wsWords pL) 24)] s.mem t.mem) ∧
      Keep (([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] : List Reg) ++ recRegs) s t := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eX6 := e wX 6; have eX7 := e wX 7; have eX8 := e wX 8
  obtain eP0 := e (wsWords pL) 0; have eP4 := e (wsWords pL) 4; have eP8 := e (wsWords pL) 24
  obtain eQ8 := e (wsWords qL) 24
  obtain hw2 : 2 ≤ wsWords pL := by unfold wsWords; omega_arith
  refine WP.seq (WP.mono (exportM2_ok hs hQZ hXQ hwQ hwX h23 h27 h28 hBQ hQL hq1 hq')
    fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
  -- `m₂`, below `2^(64 w_P n)`, in the words `reduceIn` reads.
  obtain hKn := le_nChunks_mul (K := (k + 7) / 8) (show 1 ≤ wsWords pL by omega_arith)
  obtain hM2n : M2 < 2 ^ (64 * (wsWords pL * nChunks ((k + 7) / 8) (wsWords pL))) := by
    refine Nat.lt_of_lt_of_le hm2b ?_
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by rw [Nat.mul_comm (wsWords pL)]; omega_arith)
  obtain hbytes : wv s₁.mem BX (slot wX 6) (wsWords pL * nChunks ((k + 7) / 8) (wsWords pL)) = M2 :=
    wv_low (by rw [← Pre.val32_eq_wv, v6, hm2]) hM2n hnw
  obtain hd : ∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d := fun d hd =>
    o1.word (Or.inl (by omega_arith)) (by omega_arith)
  refine WP.seq (WP.mono (setupP_ok (oA := oP) (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h23) (by decide)
    (by decide) (by omega_arith) (by rw [hd _ (by decide)]; exact hBP) (by rw [hd _ (by decide)]; exact hPL) hp1 hp')
    fun s₂ ⟨⟨a10, a21, a29, a11, _, m2⟩, k2⟩ => ?_)
  obtain k12 := k1.trans k2
  refine WP.mono (recombineP_ok (QI := QI) (k := k) (hs.congr k12.wr) hPZ hXP hw2 (by omega_arith) hwP hwX a10 a21
    a29 a11 ((k12.gpr _ (by decide)).trans h23) ((k12.gpr _ (by decide)).trans h27)
    ((k12.gpr _ (by decide)).trans h28) (by rw [m2, hd _ (by decide)]; exact hK) (by omega_arith) hk' hnw
    (by rw [m2, val32_off_eq o1 (Or.inr (by omega_arith)) (by omega_arith), hP0]) hP2 hPodd
    (by rw [m2, val32_off_eq o1 (Or.inr (by omega_arith)) (by omega_arith), hm1]) hm1P (by rw [m2]; exact hbytes)
    (by rw [m2, o1.wv (Or.inr (by omega_arith)) (by omega_arith)]
        exact wv_low (by rw [← Pre.val32_eq_wv]; exact hQI) hQIb hwP) hQP
    (fun hp => let ⟨S, pL', b, C⟩ := hR2 hp
      ⟨S, pL', b, (C.mono (oA := slot wX 6) (n := 8 * wX) o1 (by omega_arith) (by omega_arith)
        (by rw [k1.rd, k1.wr]) (k1.gpr _ (by decide))).of_mem m2 (by rw [k2.rd, k2.wr]) (k2.gpr _ (by decide))⟩))
    fun t ⟨⟨v4, o2⟩, k3⟩ => ⟨⟨v4, fun x hx => ?_⟩, (k12.trans k3).mono⟩
  obtain h1 := hx _ (List.mem_cons_self ..)
  obtain h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only at h1 h2
  have h1' : ofs BX x < slot wX 6 ∨ slot wX 6 + 8 * wX ≤ ofs BX x := h1
  have h2' : ofs BX x < oP ∨ oP + slot (wsWords pL) 24 ≤ ofs BX x := h2
  rw [m2] at o2
  rw [o2 x h2', o1 x h1']

end VG.Proof.Bignum.PPC64LE.Crt
