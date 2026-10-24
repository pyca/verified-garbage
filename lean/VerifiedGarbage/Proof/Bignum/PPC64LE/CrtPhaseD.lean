module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP1
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecX
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMid
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: `h`

`phaseD_ok`: `m₂`'s bytes into `X`'s array 1 (`exportM2`), then, in `p`'s
working space, `h = (m₁ - m₂ mod p) qInv mod p` into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem Scr.le {s : State} {B : Addr} {Z n : Nat} (hs : Scr s B Z) (h : n ≤ Z) : Scr s B n :=
  ⟨let ⟨B₀, o, L, hm, hb, hL, hL'⟩ := hs.wr; ⟨B₀, o, L, hm, hb, by omega, hL'⟩, by have := hs.nowrap; omega⟩

/-- `exportM2`, `setupP oBP oPLen` and `recombineP`: with `q`'s working space
at `off BX oQ` (its registers set, `m₂` below `256^qL` in array 4) and `p`'s
at `off BX oP` (`P` in array 0, `m₁ < P` in array 4), `qInv < P` in `X`'s
array 7: `h` into `p`'s array 4. -/
theorem phaseD_ok {s : State} {BX : Addr} {Z oP oQ wX pL qL Pv m1 M2 QI : Nat}
    (hs : Scr s BX Z) (hPZ : oP + slot (wsWords pL) 8 ≤ Z) (hXP : slot wX 8 ≤ oP)
    (hQZ : oQ + slot (wsWords qL) 8 ≤ Z) (hXQ : slot wX 8 ≤ oQ) (hPQ : oP + slot (wsWords pL) 8 ≤ oQ)
    (hwP : wsWords pL ≤ wX) (hwQ : wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h10 : s.gpr .r10 = off (off BX oQ) (slot (wsWords qL) 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wsWords qL + 2))) (h23 : s.gpr .r23 = BX)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBP : word s.mem BX oBP = off BX oP) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL) (hp1 : 1 ≤ pL) (hp' : pL < 2 ^ 60) (hq1 : 1 ≤ qL)
    (hq' : qL < 2 ^ 60)
    (hP0 : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 0) (2 * wsWords pL) = Pv) (hP2 : 2 ≤ Pv)
    (hPodd : Pv % 2 = 1) (hm1 : Mont.val32 s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) = m1)
    (hm1P : m1 < Pv) (hm2 : Mont.val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) = M2)
    (hm2b : M2 < 256 ^ qL) (hQI : Mont.val32 s.mem BX (slot wX 7) (2 * wX) = QI)
    (hQIb : QI < 2 ^ (64 * wsWords pL)) (hQP : QI < Pv) :
    WP isa (.seq exportM2 (.seq (.block (setupP oBP oPLen)) recombineP)) s fun t =>
      (Mont.val32 t.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) =
          (m1 + Pv - M2 % Pv) % Pv * QI % Pv ∧
        Mont.Outs BX [(slot wX 1, qL), (oP, slot (wsWords pL) 8)] s.mem t.mem) ∧
      Keep ([.r0, .r15, .r16, .r17, .r3, .r4, .r11, .r21, .r29] ++ recRegs) s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eX1 := e wX 1; have eX2 := e wX 2; have eX7 := e wX 7; have eX8 := e wX 8
  have eP0 := e (wsWords pL) 0; have eP4 := e (wsWords pL) 4; have eP8 := e (wsWords pL) 8
  have eQ8 := e (wsWords qL) 8
  have hqw : qL ≤ 8 * wsWords qL := by unfold wsWords; omega
  have hw2 : 2 ≤ wsWords pL := by unfold wsWords; omega
  refine WP.seq (WP.mono (exportM2_ok (L := qL) (hs.sub hQZ) (Scr.le hs (show slot wX 8 ≤ Z by omega)) h10 h29
    h23 h27 h28 hQL hq1 hqw (by omega) (Nat.le_refl _) (Nat.le_refl _)
    (fun x hx => by rcases ofs_rebase BX x (o := oQ) (by omega) with ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega))
    fun s₁ ⟨⟨hb, o1⟩, k1⟩ => ?_)
  have hbytes : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₁.mem (off BX (slot wX 1)) qL) = M2 := by
    rw [Pub.out_bytes (B := off BX oQ) (d := slot (wsWords qL) 4) hqw hm2 hm2b
      (fun i hi => by rw [off_off]; exact hb i hi), VG.Proof.Rsa.os2ip_i2osp, Nat.mod_eq_of_lt hm2b]
  have hd : ∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d := fun d hd => o1.word (Or.inl (by omega)) (by omega)
  refine WP.seq (WP.mono (setupP_ok (oA := oP) (hs.congr k1.wr) ((k1.gpr _ (by decide)).trans h23) (by decide) (by decide)
    (by omega) (by rw [hd _ (by decide)]; exact hBP) (by rw [hd _ (by decide)]; exact hPL) hp1 hp')
    fun s₂ ⟨⟨a10, a21, a29, a11, _, m2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.mono (recombineP_ok (QI := QI) (hs.congr k12.wr) hPZ hXP hw2 (by omega) hwP hwX a10 a21 a29 a11
    ((k12.gpr _ (by decide)).trans h23) ((k12.gpr _ (by decide)).trans h27) ((k12.gpr _ (by decide)).trans h28)
    (by rw [m2, hd _ (by decide)]; exact hQL) hq1 (by omega)
    (by rw [m2, val32_off_eq o1 (Or.inr (by omega)) (by omega), hP0]) hP2 hPodd
    (by rw [m2, val32_off_eq o1 (Or.inr (by omega)) (by omega), hm1]) hm1P (by rw [m2]; exact hbytes)
    (by rw [m2, o1.wv (Or.inr (by omega)) (by omega)]
        exact wv_low (by rw [← Pre.val32_eq_wv]; exact hQI) hQIb hwP) hQP)
    fun t ⟨⟨v4, o2⟩, k3⟩ => ⟨⟨v4, fun x hx => ?_⟩, (k12.trans k3).mono⟩
  have h1 := hx _ (List.mem_cons_self ..)
  have h2 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only at h1 h2
  have h1' : ofs BX x < slot wX 1 ∨ slot wX 1 + qL ≤ ofs BX x := h1
  have h2' : ofs BX x < oP ∨ oP + slot (wsWords pL) 8 ≤ ofs BX x := h2
  rw [m2] at o2
  rw [o2 x h2', o1 x h1']

end VG.Proof.Bignum.PPC64LE.Crt
