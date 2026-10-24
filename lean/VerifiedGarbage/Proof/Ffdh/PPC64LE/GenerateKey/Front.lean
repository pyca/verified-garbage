module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key` on PPC64LE: the front

`gkFront` loads the working space's address from the stack, saves the
nonvolatile registers in its header, stores x, `x_len`, `y` and `rand` in its
words 8–11 (`gkHdr_ok`) and sets up the registers and g's address in `r9`: `Base` of the domain's
data `gcOf` (g as the `Y` of `Base`), keeping the bytes apart from the
working space (`gk_front`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.GenerateKey

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.GenerateKey
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Bignum (slot)

/-- The public data of a run, as `Base`'s: the domain, g and the working space. -/
def gcOf (s : State) : CD :=
  ⟨s.gpr .r7, off (s.gpr .r7) (s.gpr .r9).toNat, stackArg s 1, (s.gpr .r9).toNat, (s.gpr .r8).toNat,
    (stackArg s 2).toNat * 8, Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat,
    Spec.Rsa.bytesAt s.mem (off (s.gpr .r7) (s.gpr .r9).toNat) (s.gpr .r9).toNat⟩

/-- The registers `gkFront` writes. -/
def gkFrontRegs : List Reg := ([.r11, .r23, .r3, .r4, .r5] : List Reg) ++ setup0Regs ++ ([.r9] : List Reg)

/-- x, `x_len`, `y` and `rand` into the header's words 8–11 at `S`, and the
domain's arguments into `r3`–`r5`. -/
theorem gkHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 4, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r3 .r23 64, .store .d .r4 .r23 72, .store .d .r5 .r23 80, .store .d .r10 .r23 88,
      .addi .r3 .r7 0, .addi .r4 .r8 0, .addi .r5 .r9 0] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r3 ∧ word t.mem S 72 = s.gpr .r4 ∧ word t.mem S 80 = s.gpr .r5 ∧
        word t.mem S 88 = s.gpr .r10 ∧ t.gpr .r3 = s.gpr .r7 ∧ t.gpr .r4 = s.gpr .r8 ∧ t.gpr .r5 = s.gpr .r9 ∧
        Outside S 64 32 s.mem t.mem) ∧ Keep [.r3, .r4, .r5] s t := by
  refine WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  have i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  have i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  have i3 : InRegions s.wr (S + BitVec.ofNat 64 88) 8 := hin 3 (by decide)
  prun [h23, i0, i1, i2, i3, BitVec.add_zero]
  have o0 := writeW_outside s.mem S (d := 64) (s.gpr .r3) (by omega)
  have o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r3)) S (d := 72) (s.gpr .r4) (by omega)
  have o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r3)).writeW (off S 72) (s.gpr .r4)) S (d := 80)
    (s.gpr .r5) (by omega)
  have o3 := writeW_outside (((s.mem.writeW (off S 64) (s.gpr .r3)).writeW (off S 72) (s.gpr .r4)).writeW
    (off S 80) (s.gpr .r5)) S (d := 88) (s.gpr .r10) (by omega)
  refine ⟨?_, ?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 80 = _
    rw [o3.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · exact (((o0.mono (by omega) (by omega)).trans (o1.mono (by omega) (by omega))).trans
      (o2.mono (by omega) (by omega))).trans (o3.mono (by omega) (by omega))

/-- `gkFront`: `Base` of `gcOf`, the header's words 8–11 and the saved
registers, and the bytes apart from the working space kept. -/
theorem gk_front {s : State} (h : gkContract.pre s) :
    WP isa (.block gkFront) s fun t => Base (gcOf s) t ∧ t.gpr .r9 = off (s.gpr .r7) (s.gpr .r9).toNat ∧
      word t.mem (stackArg s 1) 64 = s.gpr .r3 ∧ word t.mem (stackArg s 1) 72 = s.gpr .r4 ∧
      word t.mem (stackArg s 1) 80 = s.gpr .r5 ∧ word t.mem (stackArg s 1) 88 = s.gpr .r10 ∧
      (∀ i < 18, word t.mem (stackArg s 1) (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      (∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n) ∧
      Keep gkFrontRegs s t := by
  obtain ⟨hsp, hrd, hwr, dXY, dXD, dXR, dXS, dXA, dYD, dYR, dYS, dYA, dDS, dRS, dSA, nwX, nwY, nwD, nwR, nwS,
    ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [gcOf]
  have hA1 : InRegions (s.rd ++ s.wr) (stackArgAddr s 1) 8 := by
    refine ⟨gkStack s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 96, 24⟩ : Region).Contains (s.sp + BitVec.ofNat 64 104) 8
    rw [show s.sp + BitVec.ofNat 64 104 = s.sp + BitVec.ofNat 64 96 + BitVec.ofNat 64 8 by rw [Offset.add_add]]
    exact Offset.contains_base _ (by omega) (by omega)
  generalize hDd : s.gpr .r7 = D at hrd dXD dYD dDS nwD ⊢
  generalize hLd : (s.gpr .r8).toNat = L at hrd dXD dYD dDS nwD hL ⊢
  generalize hkd : (s.gpr .r9).toNat = k at hk hk' hL hxl hyl hrl hsl ⊢
  generalize hSd : stackArg s 1 = S at hwr dXS dYS dDS dRS dSA nwS ⊢
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hwr dXS dYS dDS dRS dSA nwS ⊢
  have hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [Domain.slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have hinH : ∀ i < 4, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega) (by omega)⟩
  unfold gkFront
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadS1_ok s hA1) fun s₀ ⟨⟨a11, m0⟩, k0⟩ => ?_)
  have a11' : s₀.gpr .r11 = S := a11.trans hSd
  refine WP.block_append (WP.mono (save_ok (ws := .r11) (by decide) s₀ (by rw [a11', k0.wr]; exact hin))
    fun s₁ hS => ?_)
  have k1 := k0.trans hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans a11'
  have hfr₁ : Frame [Domain.savR S] s.mem s₁.mem := by rw [← m0, ← a11']; exact hS.frame
  refine WP.block_append (WP.mono (gkHdr_ok h23₁ (by rw [k1.wr]; exact hinH))
    fun s₂ ⟨⟨w8, w9, w10, w11, b3, b4, b5, o2⟩, k2⟩ => ?_)
  have k12 := k1.trans k2
  refine WP.block_append (WP.mono (setup0_ok (D := D) (L := L) (k := k) (b3.trans ((k1.gpr .r7 (by decide)).trans hDd))
    (by rw [b4, k1.gpr .r8 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [b5, k1.gpr .r9 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans h23₁) hk') fun s₃ ⟨⟨b21, b27, b28, b11, b29, b10, b31, m3'⟩, k3'⟩ => ?_)
  refine WP.mono (WP.keep [.r9] (Q := fun t => t.gpr .r9 = off D k ∧ t.mem = s₃.mem) (by prun [b21, b28])
    (by decide)) fun t ⟨⟨a9, mt⟩, kt⟩ => ?_
  have m3 : t.mem = s₂.mem := mt.trans m3'
  have k3 := k3'.trans kt
  have a21 : t.gpr .r21 = D := (kt.gpr .r21 (by decide)).trans b21
  have a27 : t.gpr .r27 = BitVec.ofNat 64 L := (kt.gpr .r27 (by decide)).trans b27
  have a28 : t.gpr .r28 = BitVec.ofNat 64 k := (kt.gpr .r28 (by decide)).trans b28
  have s11 : t.gpr .r11 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) := (kt.gpr .r11 (by decide)).trans b11
  have a29 : t.gpr .r29 = BitVec.ofNat 64 (8 * ((k + 7) / 8 + 2)) := (kt.gpr .r29 (by decide)).trans b29
  have a10 : t.gpr .r10 = off S (slot ((k + 7) / 8) 0) := (kt.gpr .r10 (by decide)).trans b10
  have a31 : t.gpr .r31 = S := (kt.gpr .r31 (by decide)).trans b31
  have kall := k12.trans k3
  have hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep => by
    rw [m3, outside_bytesAt o2 (by omega) hsep]
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
  have hw3 : ∀ d, word t.mem S d = word s₂.mem S d := fun d => by rw [m3]
  refine ⟨⟨⟨hs.congr kall.wr, a10, a29, s11, a31, show 4 ≤ (k + 7) / 8 by omega,
    show (k + 7) / 8 ≤ 128 by omega, hZw⟩, a21, (k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁),
    a27, a28, hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega, rdD, sepD,
    fun i (hi : i < k) => by rw [off_off']; exact rdD _ (by omega), sepG, hb3 D L sepD, hb3 (off D k) k sepG⟩,
    a9, ?_, ?_, ?_, ?_, fun i hi => ?_, hb3, kall.mono (by decide)⟩
  · rw [hw3, w8, k1.gpr .r3 (by decide)]
  · rw [hw3, w9, k1.gpr .r4 (by decide)]
  · rw [hw3, w10, k1.gpr .r5 (by decide)]
  · rw [hw3, w11, k1.gpr .r10 (by decide)]
  · rw [hw3, o2.word (by omega) (by omega)]
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← k0.gpr _ (saved_ne11' i hi), ← hS.saved i hi, a11', ea]

end VG.Proof.Ffdh.PPC64LE.GenerateKey
