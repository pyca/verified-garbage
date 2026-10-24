module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtAdd
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa

/-!
# The RSA private-key operation on PPC64LE: `m = q h + m₂`

`recombineX_ok`: `h` (`p`'s array 4) and `m₂` (`q`'s array 4) into `X`'s
arrays 7 and 6, `q h` (with `q` in `X`'s array 5) exactly, by a Montgomery
multiplication modulo `2^(64 w_X) - 1`, and `m₂` added, into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem prod_bound {x y z A B : Nat} (hA : 2 ≤ A) (hy : y < B) (hx : x < A) (hz : z < B) :
    y * x + z + 2 ≤ B * A := by
  have h1 : y * x ≤ (B - 1) * (A - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : (B - 1) * (A - 1) + (B - 1) = (B - 1) * A := by
    rw [Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right (B - 1) (show 0 < A by omega); omega
  have h3 : (B - 1) * A + A = B * A := by
    rw [Nat.sub_one_mul]; have : A ≤ B * A := Nat.le_mul_of_pos_left A (by omega); omega
  omega

theorem val32_off_eq {m m' : Mem} {B : Addr} {o d w a n : Nat} (h : Outside B a n m m')
    (hd : o + d + 8 * w ≤ a ∨ a + n ≤ o + d) (hd' : o + d + 8 * w ≤ 2 ^ 64) :
    val32 m' (off B o) d (2 * w) = val32 m (off B o) d (2 * w) := by
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv, wv_off, wv_off, h.wv hd hd']

/-- The registers `recombineX` writes. -/
def recXRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21,
    .r22, .r24, .r29]

/-- `recombineX`: for `h` in `p`'s array 4 and `m₂` in `q`'s (their working
spaces at `off BX oP` and `off BX oQ`, from the header with their lengths),
`q` in `X`'s array 5 (`w_X` words, at least `w_P + w_Q`) and
`M = 2^(64 w_X) - 1` in its array 0: `q h + m₂` into `X`'s array 4. -/
theorem recombineX_ok {s : State} {BX : Addr} {Z oP oQ pL qL wX Qv H M2 : Nat}
    (hs : Scr s BX Z) (hPZ : oP + slot (wsWords pL) 8 ≤ Z) (hXP : slot wX 8 ≤ oP)
    (hQZ : oQ + slot (wsWords qL) 8 ≤ Z) (hXQ : slot wX 8 ≤ oQ)
    (hpq : wsWords pL + wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBP : word s.mem BX oBP = off BX oP) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hBQ : word s.mem BX oBQ = off BX oQ) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hp1 : 1 ≤ pL) (hp' : pL < 2 ^ 60) (hq1 : 1 ≤ qL) (hq' : qL < 2 ^ 60)
    (hM : val32 s.mem BX (slot wX 0) (2 * wX) = 2 ^ (64 * wX) - 1)
    (hM0 : word s.mem BX (slot wX 0) = BitVec.allOnes 64)
    (hq : val32 s.mem BX (slot wX 5) (2 * wX) = Qv) (hqb : Qv < 2 ^ (64 * wsWords qL))
    (hH : val32 s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) = H)
    (hm2 : val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) = M2) :
    WP isa recombineX s fun t =>
      (val32 t.mem BX (slot wX 4) (2 * wX) = Qv * H + M2 ∧
        Outs BX [(slot wX 2, 8 * (wX + 2)), (slot wX 3, 8 * (wX + 2)), (slot wX 4, 8 * (wX + 2)),
          (slot wX 6, 8 * (wX + 2)), (slot wX 7, 8 * (wX + 2))] s.mem t.mem) ∧ Keep recXRegs s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eX0 := e wX 0; have eX2 := e wX 2; have eX3 := e wX 3; have eX4 := e wX 4; have eX5 := e wX 5
  have eX6 := e wX 6; have eX7 := e wX 7; have eX8 := e wX 8
  have eP4 := e (wsWords pL) 4; have eP8 := e (wsWords pL) 8
  have eQ4 := e (wsWords qL) 4; have eQ8 := e (wsWords qL) 8
  have hwP : 2 ≤ wsWords pL := by unfold wsWords; omega
  have hwQ : 2 ≤ wsWords qL := by unfold wsWords; omega
  unfold recombineX
  -- `h` into array 7.
  refine WP.seq (WP.mono (blk_ok (j := 7) (oA := oP) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt hp')) hs h23
    (by decide) (by decide) (by omega) hBP hPL hp1 hp' hwX h27 h28) fun s₁ ⟨⟨a14, a11, a22, a15, m1⟩, k1⟩ => ?_)
  refine wp_reassoc3 (WP.seq (WP.mono (xfer_ok (hs.congr k1.wr) hPZ hXP (by decide) (by omega) (by omega) hwX a14 a11 a22
    a15 ((k1.gpr _ (by decide)).trans h27) ((k1.gpr _ (by decide)).trans h28))
    fun s₂ ⟨⟨v7, out2⟩, k2⟩ => ?_))
  have k12 := k1.trans k2
  rw [m1, hH] at v7
  rw [m1] at out2
  have hdr2 : ∀ d, d + 8 ≤ 256 → word s₂.mem BX d = word s.mem BX d := fun d hd =>
    out2.word (Or.inl (by omega)) (by omega)
  -- `m₂` into array 6.
  refine WP.seq (WP.mono (blk_ok (j := 6) (oA := oQ) _ (fun t h11 _ => midQ_ok h11) (hs.congr k12.wr)
    ((k12.gpr _ (by decide)).trans h23) (by decide) (by decide) (by omega)
    (by rw [hdr2 _ (by decide)]; exact hBQ) (by rw [hdr2 _ (by decide)]; exact hQL) hq1 hq' hwX
    ((k12.gpr _ (by decide)).trans h27) ((k12.gpr _ (by decide)).trans h28))
    fun s₃ ⟨⟨b14, b11, b22, b15, m3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine wp_reassoc3 (WP.seq (WP.mono (xfer_ok (hs.congr k13.wr) hQZ hXQ (by decide) (by omega) (by omega) hwX b14 b11 b22
    b15 ((k13.gpr _ (by decide)).trans h27) ((k13.gpr _ (by decide)).trans h28))
    fun s₄ ⟨⟨v6, out4⟩, k4⟩ => ?_))
  have k14 := k13.trans k4
  rw [m3, val32_off_eq out2 (Or.inr (by omega)) (by omega), hm2] at v6
  rw [m3] at out4
  -- What arrays 0, 5 and 7 hold.
  have o4' : Mont.Outside BX (slot wX 6) (8 * wX) s₂.mem s₄.mem := fun x hx => out4 x hx
  have o2' : Mont.Outside BX (slot wX 7) (8 * wX) s.mem s₂.mem := fun x hx => out2 x hx
  have v0 : val32 s₄.mem BX (slot wX 0) (2 * wX) = 2 ^ (64 * wX) - 1 := by
    rw [o4'.val32 (Or.inl (by omega))
      (by omega), o2'.val32
      (Or.inl (by omega)) (by omega), hM]
  have w0 : word s₄.mem BX (slot wX 0) = BitVec.allOnes 64 := by
    rw [out4.word (Or.inl (by omega)) (by omega), out2.word (Or.inl (by omega)) (by omega), hM0]
  have v5 : val32 s₄.mem BX (slot wX 5) (2 * wX) = Qv := by
    rw [o4'.val32 (Or.inl (by omega))
      (by omega), o2'.val32
      (Or.inl (by omega)) (by omega), hq]
  have v7' : val32 s₄.mem BX (slot wX 7) (2 * wX) = H := by
    rw [o4'.val32 (Or.inr (by omega))
      (by omega), v7]
  -- The bound of `q h + m₂`.
  have hHb : H < 2 ^ (64 * wsWords pL) := by
    have := val32_lt s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL)
    rw [hH, show 32 * (2 * wsWords pL) = 64 * wsWords pL by omega] at this; exact this
  have hM2b : M2 < 2 ^ (64 * wsWords qL) := by
    have := val32_lt s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL)
    rw [hm2, show 32 * (2 * wsWords qL) = 64 * wsWords qL by omega] at this; exact this
  have hA2 : 2 ≤ 2 ^ (64 * wsWords pL) := Nat.one_lt_two_pow (by omega)
  have hB2 : 2 ≤ 2 ^ (64 * wsWords qL) := Nat.one_lt_two_pow (by omega)
  have hAB : 2 ^ (64 * wsWords qL) * 2 ^ (64 * wsWords pL) ≤ 2 ^ (64 * wX) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hbound := prod_bound hA2 hqb hHb hM2b
  have hAX : 2 ^ (64 * wsWords pL) * 2 ≤ 2 ^ (64 * wX) :=
    Nat.le_trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hB2) hAB
  -- `M`'s registers, `r12 := 1`.
  refine WP.seq (WP.mono (WP.keep [.r10, .r21, .r29, .r11, .r12] (Q := fun t =>
    t.gpr .r10 = off BX (slot wX 0) ∧ t.gpr .r21 = off BX (slot wX 0) ∧
      t.gpr .r29 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wX) ∧
      t.gpr .r12 = 1#64 ∧ t.mem = s₄.mem)
    (by prun [(k14.gpr .r27 (by decide)).trans h27, (k14.gpr .r28 (by decide)).trans h28, BitVec.add_zero,
      x11_val hwX]) (by decide)) fun s₅ ⟨⟨c10, _, c29, c11, c12, m5⟩, k5⟩ => ?_)
  have k15 := k14.trans k5
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hs.congr k15.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega) hwX (by omega) c10 c29 c11
    (by rw [c12]; decide) (by rw [m5, c12, w32_ones w0]; decide) (by rw [m5, v7', v0]; omega))
    fun s₆ ⟨⟨l4, e4, o6⟩, k6⟩ => ?_)
  have k16 := k15.trans k6
  rw [m5, v0] at l4 e4
  rw [m5] at o6
  rw [v5, v7'] at e4
  have x4 : val32 s₆.mem BX (slot wX 4) (2 * wX) = Qv * H :=
    mont_exact (by have := Nat.one_le_two_pow (n := 64 * wX); omega) l4 (by omega) e4
  have x6 : val32 s₆.mem BX (slot wX 6) (2 * wX) = M2 := by
    rw [o6.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega), v6]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k16.gpr _ (by decide)).trans h27)
    ((k16.gpr _ (by decide)).trans h28) 4) fun s₇ ⟨⟨a15', m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r16) (by decide) (by decide) ((k17.gpr _ (by decide)).trans h27)
    ((k17.gpr _ (by decide)).trans h28) 6) fun s₈ ⟨⟨a16', m8⟩, k8⟩ => ?_
  have k18 := k17.trans k8
  refine WP.mono (WP.keep [.r20] (Q := fun t => t.gpr .r20 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if true then 1 else 0) ∧ t.mem = s₈.mem) (by prun) (by decide))
    fun s₉ ⟨⟨a20, m9⟩, k9⟩ => ?_
  have k19 := k18.trans k9
  have hm9 : s₉.mem = s₆.mem := by rw [m9, m8, m7]
  refine WP.mono (addMask_ok (b := true) (n := 2 * wX) (dT := slot wX 4) (dM := slot wX 6) (hs.congr k19.wr)
    ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a15')) ((k9.gpr _ (by decide)).trans a16')
    ((((k7.trans k8).trans k9).gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans c11)) a20 (by omega) (by omega) (by omega)
    (by omega) (by omega)) fun t ⟨hT, outT, kT⟩ => ⟨⟨?_, ?_⟩, (k19.trans kT).mono⟩
  · rw [hT, hm9, x4, x6]
    simp only [↓reduceIte]
    rw [show 32 * (2 * wX) = 64 * wX by omega, Nat.mod_eq_of_lt (by omega)]
  · intro x hx
    rw [hm9] at outT
    have h2 := hx _ (List.mem_cons_self ..)
    have h3 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h4 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have h6 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    have h7 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    simp only at h2 h3 h4 h6 h7
    have h6' : ofs BX x < slot wX 6 ∨ slot wX 6 + 8 * (wX + 2) ≤ ofs BX x := h6
    have h7' : ofs BX x < slot wX 7 ∨ slot wX 7 + 8 * (wX + 2) ≤ ofs BX x := h7
    rw [outT x (by omega), o6 x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega), out4 x (by omega), out2 x (by omega)]

end VG.Proof.Bignum.PPC64LE.Crt
