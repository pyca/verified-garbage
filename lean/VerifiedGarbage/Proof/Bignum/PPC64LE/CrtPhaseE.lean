module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtChecks
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubOut
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: the result

`phaseE_ok`: `recombineX`, then `out` and `k` from the header, and
`output`: `out` holds `q h + m₂` (or zeros) and `r3` the mask's bit.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem bmask_eq (b : Bool) : bmask b = BitVec.ofNat 64 0 - BitVec.ofNat 64 (if b then 1 else 0) := rfl

/-- `recombineX`, then the output, under the mask of `b` in `r26`. -/
theorem phaseE_ok {s : State} {BX O : Addr} {Z oP oQ pL qL wX k Qv H M2 : Nat} {b : Bool}
    (hs : Scr s BX Z) (hPZ : oP + slot (wsWords pL) 8 ≤ Z) (hXP : slot wX 8 ≤ oP)
    (hQZ : oQ + slot (wsWords qL) 8 ≤ Z) (hXQ : slot wX 8 ≤ oQ)
    (hpq : wsWords pL + wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBP : word s.mem BX oBP = off BX oP) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hBQ : word s.mem BX oBQ = off BX oQ) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hp1 : 1 ≤ pL) (hp' : pL < 2 ^ 60) (hq1 : 1 ≤ qL) (hq' : qL < 2 ^ 60)
    (hM : Mont.val32 s.mem BX (slot wX 0) (2 * wX) = 2 ^ (64 * wX) - 1)
    (hM0 : word s.mem BX (slot wX 0) = BitVec.allOnes 64)
    (hq : Mont.val32 s.mem BX (slot wX 5) (2 * wX) = Qv) (hqb : Qv < 2 ^ (64 * wsWords qL))
    (hH : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) = H)
    (hm2 : Mont.val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) = M2)
    (hO : word s.mem BX oOut = off O 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k) (hk : 1 ≤ k)
    (hkw : k ≤ 8 * wX) (ho : Scr s O k) (hsepO : ∀ x, ofs O x < k → Z ≤ ofs BX x)
    (h26 : s.gpr .r26 = bmask b) (hv : b = true → Qv * H + M2 < 256 ^ k) :
    WP isa (.seq recombineX (.seq (.block [.addi .r10 .r27 0, .addi .r29 .r28 0, .load .d .r27 .r23 oOut,
      .load .d .r28 .r23 oNLen]) PublicChecked.output)) s fun t =>
      (Spec.Rsa.bytesAt t.mem O k = Spec.Rsa.i2osp (if b then Qv * H + M2 else 0) k ∧
        t.gpr .r3 = BitVec.ofNat 64 (if b then 1 else 0) ∧
        Frame [⟨off BX 256, Z - 256⟩, ⟨O, k⟩] s.mem t.mem) ∧
      Keep (recXRegs ++ ([.r0, .r3, .r15, .r16, .r17, .r27, .r28] : List Reg)) s t := by
  have hn := hs.nowrap
  have hno := ho.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eX0 := e wX 0; have eX2 := e wX 2; have eX8 := e wX 8
  refine WP.seq (WP.mono (recombineX_ok hs hPZ hXP hQZ hXQ hpq hwX h23 h27 h28 hBP hPL hBQ hQL hp1 hp' hq1 hq'
    hM hM0 hq hqb hH hm2) fun s₁ ⟨⟨v4, o1⟩, k1⟩ => ?_)
  have O1 : Outside BX (slot wX 2) (6 * (8 * (wX + 2))) s.mem s₁.mem := by
    intro x hx
    refine o1 x fun r hr => ?_
    change ofs BX x < r.1 ∨ r.1 + r.2 ≤ ofs BX x
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    change ofs BX x < slot wX 2 ∨ slot wX 2 + 6 * (8 * (wX + 2)) ≤ ofs BX x at hx
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only <;> simp only [e] at hx ⊢ <;> omega
  have hd : ∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d := fun d hd => O1.word (Or.inl (by omega)) (by omega)
  have e0 : off BX 0 = BX := BitVec.add_zero BX
  have hO' : s₁.mem.readW BX 64 = off O 0 := by
    have h0 : word s₁.mem BX 0 = off O 0 := (hd 0 (by decide)).trans hO
    rw [← e0]; exact h0
  have ld0 : InRegions (s₁.rd ++ s₁.wr) BX 8 := by
    have e0' : Mont.off BX 0 = BX := BitVec.add_zero BX
    have := (hs.congr k1.wr).ld (show 0 + 8 ≤ Z by omega); rwa [e0'] at this
  have hK' : s₁.mem.readW (off BX 16) 64 = BitVec.ofNat 64 k := by
    show word s₁.mem BX 16 = _; rw [hd 16 (by decide)]; exact hK
  refine WP.seq (WP.mono (WP.keep [.r10, .r29, .r27, .r28] (Q := fun t =>
    t.gpr .r10 = off BX (slot wX 0) ∧ t.gpr .r29 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ t.gpr .r27 = off O 0 ∧
      t.gpr .r28 = BitVec.ofNat 64 k ∧ t.mem = s₁.mem) (by
    prun [(k1.gpr .r27 (by decide)).trans h27, (k1.gpr .r28 (by decide)).trans h28,
      (k1.gpr .r23 (by decide)).trans h23, oOut, oNLen, ld0,
      (hs.congr k1.wr).ld (show 16 + 8 ≤ Z by omega), hO', hK', BitVec.add_zero]) (by decide))
    fun s₂ ⟨⟨a10, a29, a27, a28, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (Pub.output_ok (b := b) (hs.congr k12.wr) (ho.congr k12.wr) a10 a29 a28 a27
    (by rw [k12.gpr _ (by decide), h26]) hk hkw (by omega) hsepO)
    fun t ⟨⟨hb, oo, t3⟩, k3⟩ => ⟨⟨?_, t3, ?_⟩, (k12.trans k3).mono⟩
  · cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at hb ⊢
      rw [Pub.zero_bytes hb, VG.Proof.Bignum.i2osp_zero']
    · simp only [↓reduceIte] at hb ⊢
      rw [m2] at hb
      exact Pub.out_bytes hkw v4 (hv rfl) hb
  · refine Pub.frame_two (m₁ := s₂.mem) ?_ oo (by omega)
    rw [m2]
    exact O1.mono (by omega) (by have := slot_le (w := wX) (j := 7) (by decide); simp only [e] at this ⊢; omega)

end VG.Proof.Bignum.PPC64LE.Crt
