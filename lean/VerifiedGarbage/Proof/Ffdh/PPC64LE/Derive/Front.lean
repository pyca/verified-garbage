module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_derive_public` on PPC64LE: the front

`dpFront` saves the nonvolatile registers in the working space's header,
stores x, `x_len` and `y` in its words 8–10 (`dpHdr_ok`), sets up the
registers and g's address in `r9`. It reaches the exchange's `XB` for the
data `dxOf` of the arguments: a run of the exchange whose peer is g, whose x
is x and whose `out` is `y` (`dp_front`), keeping the bytes apart from the
working space.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Derive

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.Derive
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

/-- The public data of a run, as the exchange's: the domain, g (as the peer)
and the working space; `y` (as `out`), x's address and length. -/
def dxOf (s : State) : XD :=
  ⟨⟨s.gpr .r5, off (s.gpr .r5) (s.gpr .r7).toNat, s.gpr .r10, (s.gpr .r7).toNat, (s.gpr .r6).toNat,
    (stackArg s 0).toNat * 8, Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat,
    Spec.Rsa.bytesAt s.mem (off (s.gpr .r5) (s.gpr .r7).toNat) (s.gpr .r7).toNat⟩,
    s.gpr .r3, s.gpr .r8, (s.gpr .r9).toNat⟩

/-- The registers `dpFront` writes. -/
def frontRegs : List Reg := ([.r23, .r3, .r4, .r5] : List Reg) ++ setup0Regs ++ ([.r9] : List Reg)

/-- x, `x_len` and `y` into the header's words 8–10 at `S`, and the domain's
arguments into `r3`–`r5`. -/
theorem dpHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r3 .r23 80,
      .addi .r3 .r5 0, .addi .r4 .r6 0, .addi .r5 .r7 0] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r8 ∧ word t.mem S 72 = s.gpr .r9 ∧ word t.mem S 80 = s.gpr .r3 ∧
        t.gpr .r3 = s.gpr .r5 ∧ t.gpr .r4 = s.gpr .r6 ∧ t.gpr .r5 = s.gpr .r7 ∧
        Outside S 64 24 s.mem t.mem) ∧ Keep [.r3, .r4, .r5] s t := by
  refine WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  have i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  have i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  prun [h23, i0, i1, i2, BitVec.add_zero]
  have o0 := writeW_outside s.mem S (d := 64) (s.gpr .r8) (by omega)
  have o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r8)) S (d := 72) (s.gpr .r9) (by omega)
  have o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r8)).writeW (off S 72) (s.gpr .r9)) S (d := 80)
    (s.gpr .r3) (by omega)
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o2.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · exact ((o0.mono (by omega) (by omega)).trans (o1.mono (by omega) (by omega))).trans
      (o2.mono (by omega) (by omega))

/-- `dpFront`: the exchange's `XB` for `dxOf`, the saved registers in the
header, and the registers it writes. -/
theorem dp_front {s : State} (h : dpContract.pre s) :
    WP isa (.block dpFront) s fun t => XB (dxOf s) t ∧
      (∀ i < 18, word t.mem (s.gpr .r10) (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      (∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .r10) y < (stackArg s 0).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n) ∧
      Keep frontRegs s t := by
  obtain ⟨hsp, hrd, hwr, dOD, dOX, dOS, dOA, dDS, dXS, dSA, nwO, nwD, nwX, nwS, ⟨hk, hk'⟩, hL,
    hol, hx1, hxk, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [dxOf]
  rw [hol] at hwr dOD dOX dOS dOA nwO
  generalize hOd : s.gpr .r3 = O at hwr dOD dOX dOS dOA nwO ⊢
  generalize hDd : s.gpr .r5 = D at hrd dOD dDS nwD ⊢
  generalize hLd : (s.gpr .r6).toNat = L at hrd dOD dDS nwD hL ⊢
  generalize hkd : (s.gpr .r7).toNat = k at hk hk' hL hxk hsl hwr dOD dOX dOS dOA nwO ⊢
  generalize hXd : s.gpr .r8 = X at hrd dOX dXS nwX ⊢
  generalize hxd : (s.gpr .r9).toNat = xl at hrd dOX dXS nwX hx1 hxk ⊢
  generalize hSd : s.gpr .r10 = S at hwr dOS dDS dXS dSA nwS ⊢
  generalize hZd : (stackArg s 0).toNat * 8 = Z at hwr dOS dDS dXS dSA nwS ⊢
  have hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have hZ256 : 256 ≤ Z := by omega
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [Domain.slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (Domain.savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have hinH : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega) (by omega)⟩
  unfold dpFront
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Domain.save_ok (ws := .r10) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans hSd
  have hfr₁ : Frame [Domain.savR S] s.mem s₁.mem := hSd ▸ hS.frame
  rw [WP.block_append_iff]
  refine WP.mono (dpHdr_ok h23₁ (by rw [k1.wr]; exact hinH)) fun s₂ ⟨⟨w8, w9, w10, b3, b4, b5, o2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) (b3.trans ((k1.gpr .r5 (by decide)).trans hDd))
    (by rw [b4, k1.gpr .r6 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [b5, k1.gpr .r7 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans h23₁) hk') fun s₃ ⟨⟨a21, a27, a28, a11', a29, a10, a31, m3⟩, k3⟩ => ?_
  have k123 := k12.trans k3
  refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off D k ∧ t.mem = s₃.mem) (by prun [a21, a28])
    (by decide)) fun t ⟨⟨a9, mt⟩, kt⟩ => ?_
  have kall := k123.trans kt
  have hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep => by
    rw [mt, m3, outside_bytesAt o2 (by omega) hsep]
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => hfr₁ _ fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    have hc' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega)) _ hc
    exact hsep i (List.mem_range.mp hi) _ (by simp only [Region.Contains] at hc'; exact hc') rfl
  have sepD := sep_of_disjoint dDS (by omega)
  have rdD : ∀ i < L, InRegions (t.rd ++ t.wr) (off D i) 1 := fun i hi => by
    rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := D) (L := L) (by rw [hrd]; simp) (by omega) i hi
  have sepG : ∀ i < k, ∀ x, ofs S x < Z → off (off D k) i ≠ x := fun i hi => by
    rw [off_off']; exact sepD _ (by omega)
  have hw3 : ∀ d, word t.mem S d = word s₂.mem S d := fun d => by rw [mt, m3]
  refine ⟨⟨⟨⟨hs.congr kall.wr, (kt.gpr .r10 (by decide)).trans a10, (kt.gpr .r29 (by decide)).trans a29,
    (kt.gpr .r11 (by decide)).trans a11', (kt.gpr .r31 (by decide)).trans a31, show 4 ≤ (k + 7) / 8 by omega,
    show (k + 7) / 8 ≤ 128 by omega, hZw⟩, (kt.gpr .r21 (by decide)).trans a21,
    (kt.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁)),
    (kt.gpr .r27 (by decide)).trans a27, (kt.gpr .r28 (by decide)).trans a28,
    hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega, rdD, sepD,
    fun i (hi : i < k) => by rw [off_off']; exact rdD _ (by omega), sepG, hb3 D L sepD, hb3 (off D k) k sepG⟩,
    ⟨a9, ?_, ?_, ?_,
    fun i hi => by rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := X) (L := xl) (by rw [hrd]; simp) (by omega) i hi,
    sep_of_disjoint (L := xl) dXS (by omega), Scr.of_mem (by rw [kall.wr, hwr]; simp) nwO, Pub.sep_of_disjoint dOS,
    hx1, hxk⟩⟩, fun i hi => ?_, hb3, kall.mono (by decide)⟩
  · show word t.mem S 64 = _
    rw [hw3, w8, k1.gpr .r8 (by decide), hXd]; simp [off]
  · show word t.mem S 72 = _
    rw [hw3, w9, k1.gpr .r9 (by decide), ← hxd, VG.Proof.Bignum.ofNat_toNat64]
  · show word t.mem S 80 = _
    rw [hw3, w10, k1.gpr .r3 (by decide), hOd]; simp [off]
  · rw [hw3, o2.word (by omega) (by omega)]
    have ea : off (Domain.savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hS.saved i hi, hSd, ea]

end VG.Proof.Ffdh.PPC64LE.Derive
