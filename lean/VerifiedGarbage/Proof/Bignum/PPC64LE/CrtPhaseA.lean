module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtChecks
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtLoadX
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore

/-!
# The RSA private-key operation on PPC64LE: `X` loaded and checked

`phaseA_ok`: `loadX` and `checks`, the mask of the checks in `r26`, `p` and
`q` (or 3) and `qInv` (or 0) in `X`'s arrays 4, 5 and 7, `M` in array 0.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- The mask of the checks. -/
def crtMask (N k C P Q QI : Nat) : Bool :=
  Spec.Rsa.modulusValid N k && decide (C < N) && decide (QI < P) && decide (P * Q = N)

theorem pq_lt {P Q pL qL k w : Nat} (hP : P < 256 ^ pL) (hQ : Q < 256 ^ qL) (hp : pL < k) (hq : qL < k)
    (hw : 16 * k ≤ 64 * w) : P * Q < 2 ^ (64 * w) - 1 := by
  have h1 : P * Q < 256 ^ pL * 256 ^ qL := Nat.mul_lt_mul_of_lt_of_lt hP hQ
  rw [← Nat.pow_add, VG.Proof.Bignum.pow256_eq] at h1
  have h2 : 2 ^ (8 * (pL + qL)) * 2 ≤ 2 ^ (64 * w) := by
    rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- `checks`, in `X` as `checksA_ok` and `checksB_ok` need it. -/
theorem checks_ok {s : State} {BX Na : Addr} {Z w k : Nat} {nb : List Byte}
    (hs : Scr s BX Z) (hZ : slot w 8 ≤ Z) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h10 : s.gpr .r10 = off BX (slot w 0)) (h21 : s.gpr .r21 = off BX (slot w 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hN : word s.mem BX oN = off Na 0) (hNL : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hk : 64 ≤ k) (hk' : k ≤ 1024) (hlen : nb.length = k)
    (hrd : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1)
    (hb : ∀ i (h : i < k), s.mem (off Na i) = nb[i]'(by omega))
    (hM : Mont.val32 s.mem BX (slot w 0) (2 * w) = 2 ^ (64 * w) - 1)
    (hM0 : word s.mem BX (slot w 0) = BitVec.allOnes 64)
    (hn1 : Mont.val32 s.mem BX (slot w 1) (2 * w) = Spec.Rsa.os2ip nb)
    (h1top : word s.mem BX (slot w 1 + 8 * w) = 0) (h6top : word s.mem BX (slot w 6 + 8 * w) = 0)
    (h7top : word s.mem BX (slot w 7 + 8 * w) = 0)
    (hq : Mont.val32 s.mem BX (slot w 5) (2 * w) < 2 ^ (64 * w) - 1)
    (hpq : Mont.val32 s.mem BX (slot w 4) (2 * w) * Mont.val32 s.mem BX (slot w 5) (2 * w) < 2 ^ (64 * w) - 1) :
    WP isa checks s fun t =>
      (t.gpr .r26 = bmask (crtMask (Spec.Rsa.os2ip nb) k (Mont.val32 s.mem BX (slot w 6) (2 * w))
          (Mont.val32 s.mem BX (slot w 4) (2 * w)) (Mont.val32 s.mem BX (slot w 5) (2 * w))
          (Mont.val32 s.mem BX (slot w 7) (2 * w))) ∧
        Mont.val32 t.mem BX (slot w 4) (2 * w) = (if crtMask (Spec.Rsa.os2ip nb) k
          (Mont.val32 s.mem BX (slot w 6) (2 * w)) (Mont.val32 s.mem BX (slot w 4) (2 * w))
          (Mont.val32 s.mem BX (slot w 5) (2 * w)) (Mont.val32 s.mem BX (slot w 7) (2 * w))
          then Mont.val32 s.mem BX (slot w 4) (2 * w) else 3) ∧
        Mont.val32 t.mem BX (slot w 5) (2 * w) = (if crtMask (Spec.Rsa.os2ip nb) k
          (Mont.val32 s.mem BX (slot w 6) (2 * w)) (Mont.val32 s.mem BX (slot w 4) (2 * w))
          (Mont.val32 s.mem BX (slot w 5) (2 * w)) (Mont.val32 s.mem BX (slot w 7) (2 * w))
          then Mont.val32 s.mem BX (slot w 5) (2 * w) else 3) ∧
        Mont.val32 t.mem BX (slot w 7) (2 * w) = (if crtMask (Spec.Rsa.os2ip nb) k
          (Mont.val32 s.mem BX (slot w 6) (2 * w)) (Mont.val32 s.mem BX (slot w 4) (2 * w))
          (Mont.val32 s.mem BX (slot w 5) (2 * w)) (Mont.val32 s.mem BX (slot w 7) (2 * w))
          then Mont.val32 s.mem BX (slot w 7) (2 * w) else 0) ∧
        Outside BX (slot w 2) (6 * (8 * (w + 2))) s.mem t.mem ∧ t.gpr .r10 = off BX (slot w 0)) ∧
      Keep (checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg)) s t := by
  have hn := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  unfold checks
  refine checksA_ok (c := .seq (orThree 4) (.seq (orThree 5) (.seq (.block (PublicChecked.base .r14 7)) maskWords)))
    hs hZ hw2 hw' h23 h10 h21 h29 h11 hN hNL hk hk' hlen hrd hb hM hM0 hn1 h1top h6top h7top hq hpq
    fun t₁ t26 o2 b10 k2 => ?_
  refine WP.mono (checksB_ok (hs.congr k2.wr) hZ hw2 hw' b10
    ((k2.gpr _ (by decide)).trans h29) ((k2.gpr _ (by decide)).trans h11) t26)
    fun t ⟨⟨u4, u5, u7, o3⟩, k3⟩ => ⟨⟨(k3.gpr _ (by decide)).trans t26, ?_, ?_, ?_, ?_,
      (k3.gpr _ (by decide)).trans b10⟩, (k2.trans k3).mono⟩
  · rw [u4, o2.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega)]; rfl
  · rw [u5, o2.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega)]; rfl
  · rw [u7, o2.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega) (by omega)]; rfl
  · intro x hx
    have hx' : Mont.ofs BX x < slot w 2 ∨ slot w 2 + 6 * (8 * (w + 2)) ≤ Mont.ofs BX x := hx
    rw [o3 x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega), o2 x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega)]

/-- `loadX` and `checks`, from the header's buffers (`k` bytes of `n` and the
input, `pL` of `p` and `qInv`, `qL` of `q`, apart from the working space). -/
theorem phaseA_ok {s : State} {BX Na Pa Qa Ia QIa : Addr} {Z k pL qL : Nat}
    (hs : Scr s BX Z) (hZ : slot (2 * ((k + 7) / 8)) 8 ≤ Z) (hk : 64 ≤ k) (hk' : k ≤ 1024)
    (h23 : s.gpr .r23 = BX)
    (h10 : s.gpr .r10 = off BX (slot (2 * ((k + 7) / 8)) 0)) (h21 : s.gpr .r21 = off BX (slot (2 * ((k + 7) / 8)) 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * (2 * ((k + 7) / 8))))
    (hNa : word s.mem BX oN = off Na 0) (hK : word s.mem BX oNLen = BitVec.ofNat 64 k)
    (hPa : word s.mem BX oP = off Pa 0) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hQa : word s.mem BX oQ = off Qa 0) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hIa : word s.mem BX oIn = off Ia 0) (hQIa : word s.mem BX oQInv = off QIa 0)
    (hp : 1 ≤ pL) (hpk : pL < k) (hq : 1 ≤ qL) (hqk : qL < k)
    (rN : ∀ i < k, InRegions (s.rd ++ s.wr) (off Na i) 1) (sN : ∀ i < k, ∀ x, ofs BX x < Z → off Na i ≠ x)
    (rP : ∀ i < pL, InRegions (s.rd ++ s.wr) (off Pa i) 1) (sP : ∀ i < pL, ∀ x, ofs BX x < Z → off Pa i ≠ x)
    (rQ : ∀ i < qL, InRegions (s.rd ++ s.wr) (off Qa i) 1) (sQ : ∀ i < qL, ∀ x, ofs BX x < Z → off Qa i ≠ x)
    (rI : ∀ i < k, InRegions (s.rd ++ s.wr) (off Ia i) 1) (sI : ∀ i < k, ∀ x, ofs BX x < Z → off Ia i ≠ x)
    (rQI : ∀ i < pL, InRegions (s.rd ++ s.wr) (off QIa i) 1)
    (sQI : ∀ i < pL, ∀ x, ofs BX x < Z → off QIa i ≠ x) :
    WP isa (.seq loadX checks) s fun t =>
      (t.gpr .r26 = bmask (crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 0) (2 * (2 * ((k + 7) / 8))) =
          2 ^ (64 * (2 * ((k + 7) / 8))) - 1 ∧
        word t.mem BX (slot (2 * ((k + 7) / 8)) 0) = BitVec.allOnes 64 ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 4) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) else 3) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 5) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) else 3) ∧
        Mont.val32 t.mem BX (slot (2 * ((k + 7) / 8)) 7) (2 * (2 * ((k + 7) / 8))) =
          (if crtMask (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Na k)) k
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Ia k)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL)) (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL))
          then Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem QIa pL) else 0) ∧
        Outside BX 256 (slot (2 * ((k + 7) / 8)) 8 - 256) s.mem t.mem ∧
        t.gpr .r10 = off BX (slot (2 * ((k + 7) / 8)) 0)) ∧
      Keep (loadXRegs ++ checkRegs ++ ([.r0, .r3, .r4, .r14, .r17] : List Reg)) s t := by
  have hn := hs.nowrap
  have e : ∀ j, slot (2 * ((k + 7) / 8)) j = hdrBytes + j * (8 * (2 * ((k + 7) / 8) + 2)) := fun _ => rfl
  have e0 := e 0; have e2 := e 2; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq (WP.mono (loadX_ok hs hZ (by omega) (by omega) h23 h10 h21 h29 h11 hNa hK hPa hPL hQa hQL hIa hQIa
    (by omega) (by omega) hp (by omega) hq (by omega) rN sN rP sP rQ sQ rI sI rQI sQI)
    fun s₁ ⟨⟨v0, w0, v1, v4, v5, v6, v7, t1, t6, t7, O1, a10⟩, k1⟩ => ?_)
  have hd : ∀ d, d + 8 ≤ 256 → word s₁.mem BX d = word s.mem BX d := fun d hd => O1.word (Or.inl hd) (by omega)
  have hQb : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Qa qL) < 256 ^ qL := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem Qa qL)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hPb : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem Pa pL) < 256 ^ pL := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem Pa pL)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hw : 16 * k ≤ 64 * (2 * ((k + 7) / 8)) := by omega
  refine WP.mono (checks_ok (nb := Spec.Rsa.bytesAt s.mem Na k) (hs.congr k1.wr) hZ (by omega) (by omega)
    ((k1.gpr _ (by decide)).trans h23) a10 ((k1.gpr _ (by decide)).trans h21)
    ((k1.gpr _ (by decide)).trans h29) ((k1.gpr _ (by decide)).trans h11)
    (by rw [hd _ (by decide)]; exact hNa) (by rw [hd _ (by decide)]; exact hK) hk hk'
    (VG.Proof.Bignum.bytesAt_length _ _ _) (fun i hi => by rw [k1.rd, k1.wr]; exact rN i hi)
    (fun i hi => by
      rw [O1 _ (Or.inr ?_)]
      · simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      · by_contra hc
        exact sN i hi _ (by omega) rfl)
    v0 w0 v1 t1 t6 t7 (by rw [v5]; have := pq_lt (P := 1) (pL := 1) (by
        rw [VG.Proof.Bignum.pow256_eq]; exact Nat.one_lt_two_pow (by omega)) hQb (by omega) hqk hw; omega)
    (by rw [v4, v5]; exact pq_lt hPb hQb hpk hqk hw))
    fun t ⟨⟨t26, u4, u5, u7, o2, t10⟩, k2⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, t10⟩, (k1.trans k2).mono⟩
  · rw [t26, v6, v4, v5, v7]
  · rw [Pre.val32_eq_wv, o2.wv (Or.inl (by omega)) (by omega), ← Pre.val32_eq_wv, v0]
  · rw [o2.word (Or.inl (by omega)) (by omega), w0]
  · rw [u4, v6, v4, v5, v7]
  · rw [u5, v6, v4, v5, v7]
  · rw [u7, v6, v4, v5, v7]
  · exact O1.trans (o2.mono (by omega) (by omega))

end VG.Proof.Bignum.PPC64LE.Crt
