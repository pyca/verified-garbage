module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Fn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Range
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.Save
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_check_private` on PPC64LE: the front

`cpFront` saves the nonvolatile registers in the working space's header,
stores x, `x_len` and y's address in its words 8–10 (`kpHdr_ok`), sets up
the registers and g's address in `r9`. It reaches `Base` for the domain of
`kdOf`, whose y is g, and `ExtK`: the header's words, x's and y's bytes,
readable and apart from the working space (`kp_front`), keeping the bytes
apart from the working space.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.CheckPrivate

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain VG.Impl.Ffdh.PPC64LE.CheckPrivate
open VG.Proof.Ffdh.PPC64LE.Domain VG.Proof.Ffdh.PPC64LE.Derive
open VG.Proof.Bignum (slot)

/-- The public data of a run: the domain, g (as `CD`'s y) and the working
space; x's address and length, y's address, the bound on x and whether x is
within it. -/
structure KD where
  c : CD
  X : Addr
  xl : Nat
  Yv : Addr
  b : Nat
  v : Bool

/-- x's value in `s`. -/
abbrev xvalK (d : KD) (s : State) : Nat := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem d.X d.xl)

def kdOf (s : State) : KD :=
  let c : CD := ⟨s.gpr .r3, off (s.gpr .r3) (s.gpr .r5).toNat, s.gpr .r10, (s.gpr .r5).toNat, (s.gpr .r4).toNat,
    (stackArg s 0).toNat * 8, Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat,
    Spec.Rsa.bytesAt s.mem (off (s.gpr .r3) (s.gpr .r5).toNat) (s.gpr .r5).toNat⟩
  let b := bnd s.mem (s.gpr .r3) (s.gpr .r5).toNat (s.gpr .r4).toNat c.p
  let x := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  ⟨c, s.gpr .r8, (s.gpr .r9).toNat, s.gpr .r6, b, decide (0 < x ∧ x < b)⟩

/-- What holds of x and y from the header's stores on. -/
structure ExtK (d : KD) (s : State) : Prop where
  wX : s.mem.readW (off d.c.S 64) 64 = off d.X 0
  wXL : s.mem.readW (off d.c.S 72) 64 = BitVec.ofNat 64 d.xl
  wY : s.mem.readW (off d.c.S 80) 64 = off d.Yv 0
  rdX : ∀ i < d.xl, InRegions (s.rd ++ s.wr) (off d.X i) 1
  sepX : ∀ i < d.xl, ∀ y, ofs d.c.S y < d.c.Z → off d.X i ≠ y
  rdY : ∀ i < d.c.k, InRegions (s.rd ++ s.wr) (off d.Yv i) 1
  sepY : ∀ i < d.c.k, ∀ y, ofs d.c.S y < d.c.Z → off d.Yv i ≠ y
  xl1 : 1 ≤ d.xl
  xlk : d.xl ≤ d.c.k

theorem ExtK.keep {d : KD} {s t : State} {rs : List Reg} (h : ExtK d s) (k : Keep rs s t)
    (hm : Body d.c.S d.c.w s.mem t.mem) : ExtK d t where
  wX := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 64 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wX
  wXL := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 72 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wXL
  wY := by
    have := Domain.slot_eq d.c.w 0
    show word t.mem d.c.S 80 = _
    rw [Outside.word hm (Or.inl (by omega)) (by omega)]; exact h.wY
  rdX := by rw [k.rd, k.wr]; exact h.rdX
  sepX := h.sepX
  rdY := by rw [k.rd, k.wr]; exact h.rdY
  sepY := h.sepY
  xl1 := h.xl1
  xlk := h.xlk

/-- The registers `cpFront` writes. -/
def kpFrontRegs : List Reg := ([.r23] : List Reg) ++ setup0Regs ++ ([.r9] : List Reg)

/-- x, `x_len` and y's address into the header's words 8–10 at `S`. -/
theorem kpHdr_ok {s : State} {S : Addr} (h23 : s.gpr .r23 = S)
    (hin : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8) :
    WP isa (.block ([.store .d .r8 .r23 64, .store .d .r9 .r23 72, .store .d .r6 .r23 80] : List Instr)) s fun t =>
      (word t.mem S 64 = s.gpr .r8 ∧ word t.mem S 72 = s.gpr .r9 ∧ word t.mem S 80 = s.gpr .r6 ∧
        Outside S 64 24 s.mem t.mem) ∧ Keep [] s t := by
  refine WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 64) 8 := hin 0 (by decide)
  have i1 : InRegions s.wr (S + BitVec.ofNat 64 72) 8 := hin 1 (by decide)
  have i2 : InRegions s.wr (S + BitVec.ofNat 64 80) 8 := hin 2 (by decide)
  prun [h23, i0, i1, i2, BitVec.add_zero]
  have o0 := writeW_outside s.mem S (d := 64) (s.gpr .r8) (by omega)
  have o1 := writeW_outside (s.mem.writeW (off S 64) (s.gpr .r8)) S (d := 72) (s.gpr .r9) (by omega)
  have o2 := writeW_outside ((s.mem.writeW (off S 64) (s.gpr .r8)).writeW (off S 72) (s.gpr .r9)) S (d := 80)
    (s.gpr .r6) (by omega)
  refine ⟨?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 64 = _
    rw [o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 72 = _
    rw [o2.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · exact ((o0.mono (by omega) (by omega)).trans (o1.mono (by omega) (by omega))).trans
      (o2.mono (by omega) (by omega))

/-- `cpFront`: `Base` and `ExtK` for `kdOf`, the saved registers in the
header, the bytes apart from the working space, and the registers it
writes. -/
theorem kp_front {s : State} (h : kpContract.pre s) :
    WP isa (.block cpFront) s fun t => Base (kdOf s).c t ∧ ExtK (kdOf s) t ∧
      (∀ i < 18, word t.mem (s.gpr .r10) (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      (∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (s.gpr .r10) y < (stackArg s 0).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n) ∧
      Keep kpFrontRegs s t := by
  obtain ⟨hsp, hrd, hwr, dDS, dYS, dXS, dSA, nwD, nwY, nwX, nwS, ⟨hk, hk'⟩, hL, hyl, hx1, hxk, hsl⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [kdOf]
  rw [hyl] at hrd dYS nwY
  generalize hDd : s.gpr .r3 = D at hrd dDS nwD ⊢
  generalize hLd : (s.gpr .r4).toNat = L at hrd dDS nwD hL ⊢
  generalize hkd : (s.gpr .r5).toNat = k at hk hk' hL hxk hsl hrd dYS nwY ⊢
  generalize hYd : s.gpr .r6 = Yv at hrd dYS nwY ⊢
  generalize hXd : s.gpr .r8 = X at hrd dXS nwX ⊢
  generalize hxd : (s.gpr .r9).toNat = xl at hrd dXS nwX hx1 hxk ⊢
  generalize hSd : s.gpr .r10 = S at hwr dDS dYS dXS dSA nwS ⊢
  generalize hZd : (stackArg s 0).toNat * 8 = Z at hwr dDS dYS dXS dSA nwS ⊢
  have hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have hZ256 : 256 ≤ Z := by omega
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [Domain.slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (Domain.savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have hinH : ∀ i < 3, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega) (by omega)⟩
  unfold cpFront
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Domain.save_ok (ws := .r10) (by decide) s (by rw [hSd]; exact hin)) fun s₁ hS => ?_
  have k1 := hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans hSd
  have hfr₁ : Frame [Domain.savR S] s.mem s₁.mem := hSd ▸ hS.frame
  rw [WP.block_append_iff]
  refine WP.mono (kpHdr_ok h23₁ (by rw [k1.wr]; exact hinH)) fun s₂ ⟨⟨w8, w9, w10, o2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) ((k12.gpr .r3 (by decide)).trans hDd)
    (by rw [k12.gpr .r4 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [k12.gpr .r5 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
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
  refine ⟨⟨⟨hs.congr kall.wr, (kt.gpr .r10 (by decide)).trans a10, (kt.gpr .r29 (by decide)).trans a29,
    (kt.gpr .r11 (by decide)).trans a11', (kt.gpr .r31 (by decide)).trans a31, show 4 ≤ (k + 7) / 8 by omega,
    show (k + 7) / 8 ≤ 128 by omega, hZw⟩, (kt.gpr .r21 (by decide)).trans a21,
    (kt.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans h23₁)),
    (kt.gpr .r27 (by decide)).trans a27, (kt.gpr .r28 (by decide)).trans a28,
    hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega, rdD, sepD,
    fun i (hi : i < k) => by rw [off_off']; exact rdD _ (by omega), sepG, hb3 D L sepD, hb3 (off D k) k sepG⟩,
    ⟨?_, ?_, ?_,
    fun i hi => by rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := X) (L := xl) (by rw [hrd]; simp) (by omega) i hi,
    sep_of_disjoint (L := xl) dXS (by omega),
    fun i hi => by rw [kall.rd, kall.wr]; exact rd_of_mem (s := s) (D := Yv) (L := k) (by rw [hrd]; simp) (by omega) i hi,
    sep_of_disjoint (L := k) dYS (by omega), hx1, hxk⟩, fun i hi => ?_, hb3, kall.mono (by decide)⟩
  · show word t.mem S 64 = _
    rw [hw3, w8, k1.gpr .r8 (by decide), hXd]; simp [off]
  · show word t.mem S 72 = _
    rw [hw3, w9, k1.gpr .r9 (by decide), ← hxd, VG.Proof.Bignum.ofNat_toNat64]
  · show word t.mem S 80 = _
    rw [hw3, w10, k1.gpr .r6 (by decide), hYd]; simp [off]
  · rw [hw3, o2.word (by omega) (by omega)]
    have ea : off (Domain.savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← hS.saved i hi, hSd, ea]

end VG.Proof.Ffdh.PPC64LE.CheckPrivate
