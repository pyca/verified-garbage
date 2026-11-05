module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Attempt
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: correctness

`front` saves the registers, puts the context's pointer and its three
metadata words in the header (`ctxHdr_ok`), x's, `y`'s and `rand`'s addresses
and `x_len` in its words 8–11, and sets up (`cg_front`); then p is loaded and
checked, the body cuts x to the context's width and computes `g^x mod p` by
the context's comb (`bodyC_ok`), and the registers are restored
(`cg_correct`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gcOf gkHdr_ok)
open VG.Proof.Bignum (slot)

/-- `r12 :=` the stack's `ctx` argument. -/
theorem loadC_ok (s : State) (h : InRegions (s.rd ++ s.wr) (stackArgAddr s 3) 8) :
    WP isa (.block ([.addSp .r12 120, .load .d .r12 .r12 0] : List Instr)) s fun t =>
      (t.gpr .r12 = stackArg s 3 ∧ t.mem = s.mem) ∧ Keep [.r12] s t := by
  refine WP.keep _ ?_ (by decide)
  simp only [stackArgAddr, Nat.reduceMul, Nat.reduceAdd] at h
  have ea : exec (.addSp .r12 120) s = some (s.write .r12 (s.sp + BitVec.ofNat 64 120)) := by
    simp [exec]
  prun [ea, h, BitVec.add_zero]
  rfl

/-- `ctxHdr`: the context's pointer (`r12`) and its words 0–2 into the
header's words 0–3 at `S`. -/
theorem ctxHdr_ok {s : State} {S C : Addr} (h23 : s.gpr .r23 = S) (h12 : s.gpr .r12 = C)
    (hin : ∀ i < 4, InRegions s.wr (off S (8 * i)) 8) (hrd : ∀ i < 3, InRegions (s.rd ++ s.wr) (off C (8 * i)) 8) :
    WP isa (.block ctxHdr) s fun t =>
      (word t.mem S 0 = C ∧ word t.mem S 8 = word s.mem C 0 ∧ word t.mem S 16 = word s.mem C 8 ∧
        word t.mem S 24 = word s.mem C 16 ∧ Outside S 0 32 s.mem t.mem) ∧ Keep [.r0, .r6, .r11] s t := by
  refine WP.keep _ ?_ (by decide)
  have i0 : InRegions s.wr (S + BitVec.ofNat 64 0) 8 := hin 0 (by decide)
  have i1 : InRegions s.wr (S + BitVec.ofNat 64 8) 8 := hin 1 (by decide)
  have i2 : InRegions s.wr (S + BitVec.ofNat 64 16) 8 := hin 2 (by decide)
  have i3 : InRegions s.wr (S + BitVec.ofNat 64 24) 8 := hin 3 (by decide)
  have r0 : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 0) 8 := hrd 0 (by decide)
  have r1 : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 8) 8 := hrd 1 (by decide)
  have r2 : InRegions (s.rd ++ s.wr) (C + BitVec.ofNat 64 16) 8 := hrd 2 (by decide)
  unfold ctxHdr sth
  prun [hCtx, hBits, hBytes, hRows, h23, h12, i0, i1, i2, i3, r0, r1, r2]
  have o0 := writeW_outside s.mem S (d := 0) C (by omega)
  have o1 := writeW_outside (s.mem.writeW (off S 0) C) S (d := 8) (word s.mem C 0) (by omega)
  have o2 := writeW_outside ((s.mem.writeW (off S 0) C).writeW (off S 8) (word s.mem C 0)) S (d := 16)
    (word s.mem C 8) (by omega)
  have o3 := writeW_outside (((s.mem.writeW (off S 0) C).writeW (off S 8) (word s.mem C 0)).writeW
    (off S 16) (word s.mem C 8)) S (d := 24) (word s.mem C 16) (by omega)
  refine ⟨?_, ?_, ?_, word_writeW_self _ _ _ _, ?_⟩
  · show word _ S 0 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 8 = _
    rw [o3.word (by omega) (by omega), o2.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · show word _ S 16 = _
    rw [o3.word (by omega) (by omega)]
    exact word_writeW_self _ _ _ _
  · exact (((o0.mono (by omega) (by omega)).trans (o1.mono (by omega) (by omega))).trans
      (o2.mono (by omega) (by omega))).trans (o3.mono (by omega) (by omega))

theorem saved_ne1112 : ∀ i < 18, Impl.Ffdh.PPC64LE.Domain.saved i ∉ ([.r11, .r12] : List Reg) := by decide

/-- The registers `front` writes. -/
def cgFrontRegs : List Reg := ([.r11, .r12, .r23, .r0, .r6, .r3, .r4, .r5] : List Reg) ++ setup0Regs

/-- `front`: `Base` of `gcOf`, the header's words 0–3 (the context) and
8–11, the saved registers, and the bytes apart from the working space kept. -/
theorem cg_front {s : State} (h : cgContract.pre s) :
    WP isa (.block front) s fun t => Base (gcOf s) t ∧
      word t.mem (stackArg s 1) 64 = s.gpr .r3 ∧ word t.mem (stackArg s 1) 72 = s.gpr .r4 ∧
      word t.mem (stackArg s 1) 80 = s.gpr .r5 ∧ word t.mem (stackArg s 1) 88 = s.gpr .r10 ∧
      (∀ i < 18, word t.mem (stackArg s 1) (112 + 8 * i) = s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i)) ∧
      word t.mem (stackArg s 1) 0 = stackArg s 3 ∧ word t.mem (stackArg s 1) 8 = word s.mem (stackArg s 3) 0 ∧
      word t.mem (stackArg s 1) 16 = word s.mem (stackArg s 3) 8 ∧
      word t.mem (stackArg s 1) 24 = word s.mem (stackArg s 3) 16 ∧
      (∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
        Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n) ∧
      Keep cgFrontRegs s t := by
  obtain ⟨hsp, hrd, hwr, dXY, dXD, dXR, dXS, dXC, dXA, dYD, dYR, dYS, dYC, dYA, dDS, dRS, dSC, dSA,
    nwX, nwY, nwD, nwR, nwS, nwC, ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, -, hctx⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [gcOf]
  have hcl : (stackArg s 4).toNat = 3 + 34 * (((s.gpr .r9).toNat + 7) / 8) := by
    rw [hctx.1]
    simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
    omega
  have hA : ∀ i < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s i) 8 := fun i hi => by
    refine ⟨cgStack s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    rw [show stackArgAddr s i = stackArgAddr s 0 + BitVec.ofNat 64 (8 * i) by
      simp only [stackArgAddr, Offset.add_add]; congr 2; omega]
    exact Offset.contains_base _ (by omega) (by omega)
  have hrdC : ∀ i < 3, InRegions (s.rd ++ s.wr) (off (stackArg s 3) (8 * i)) 8 := fun i hi =>
    ⟨⟨stackArg s 3, (stackArg s 4).toNat * 8⟩, List.mem_append_left _ (by rw [hrd]; simp),
      Offset.contains_base _ (by omega) (by omega)⟩
  generalize hDd : s.gpr .r7 = D at hrd dXD dYD dDS nwD ⊢
  generalize hLd : (s.gpr .r8).toNat = L at hrd dXD dYD dDS nwD hL ⊢
  generalize hkd : (s.gpr .r9).toNat = k at hk hk' hL hxl hyl hrl hsl hcl ⊢
  generalize hSd : stackArg s 1 = S at hwr dXS dYS dDS dRS dSC dSA nwS ⊢
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hwr dXS dYS dDS dRS dSC dSA nwS ⊢
  generalize hCd : stackArg s 3 = C at dXC dYC dSC nwC hrdC ⊢
  have hLk : 2 * k ≤ L ∧ L ≤ 3 * k := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega
  have hZw : slot ((k + 7) / 8) 28 ≤ Z := by rw [Domain.slot_eq]; omega_using [hsl, hZd, hk', hk]
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS
  have hin : ∀ i < 18, InRegions s.wr (off (savW S) (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp, by
    rw [off, Offset.add_add]; exact Offset.contains_base S (by omega) (by omega)⟩
  have hinH : ∀ i < 4, InRegions s.wr (off S (64 + 8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega) (by omega)⟩
  have hinC : ∀ i < 4, InRegions s.wr (off S (8 * i)) 8 := fun i hi => ⟨⟨S, Z⟩, by rw [hwr]; simp,
    Offset.contains_base S (by omega) (by omega)⟩
  -- The context, apart from the working space.
  have sepCS : ∀ i < 24, ∀ y, ofs S y < Z → off C i ≠ y := fun i hi =>
    sep_of_disjoint dSC.symm (by omega) i (by omega)
  unfold front
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadS1_ok s (hA 1 (by decide))) fun s₀ ⟨⟨a11, m0⟩, k0⟩ => ?_)
  have a11' : s₀.gpr .r11 = S := a11.trans hSd
  refine WP.block_append (WP.mono (loadC_ok s₀ (by
      rw [k0.rd, k0.wr, show stackArgAddr s₀ 3 = stackArgAddr s 3 by simp only [stackArgAddr, k0.sp]]
      exact hA 3 (by decide))) fun s₀' ⟨⟨a12, m0'⟩, k0'⟩ => ?_)
  have a12' : s₀'.gpr .r12 = C := by
    rw [a12, ← hCd]; simp only [stackArg, stackArgAddr, m0, k0.sp]
  have k00 := k0.trans k0'
  have a11'' : s₀'.gpr .r11 = S := (k0'.gpr .r11 (by decide)).trans a11'
  refine WP.block_append (WP.mono (save_ok (ws := .r11) (by decide) s₀' (by rw [a11'', k00.wr]; exact hin))
    fun s₁ hS => ?_)
  have k1 := k00.trans hS.keep
  have h23₁ : s₁.gpr .r23 = S := hS.r23.trans a11''
  have hfr₁ : Frame [Domain.savR S] s.mem s₁.mem := by rw [← m0, ← m0', ← a11'']; exact hS.frame
  have hc₁ : ∀ i < 24, s₁.mem (off C i) = s.mem (off C i) := fun i hi => hfr₁ _ fun r hr hc' => by
    rw [List.mem_singleton] at hr; subst hr
    have hc'' := (Offset.sub_base (n := 144) (k := Z) S (d := 112) (by omega)) _ hc'
    exact sepCS i hi _ (by simp only [Region.Contains] at hc''; exact hc'') rfl
  refine WP.block_append (WP.mono (ctxHdr_ok h23₁ ((hS.keep.gpr .r12 (by decide)).trans a12')
    (by rw [k1.wr]; exact hinC) (by rw [k1.rd, k1.wr]; exact hrdC)) fun s₁' ⟨⟨c0, c1, c2, c3, oc⟩, kc⟩ => ?_)
  have hCw : ∀ d, d + 8 ≤ 24 → word s₁.mem C d = word s.mem C d := fun d hd =>
    Mem.readW_congr fun i hi => by
      rw [show off C d + BitVec.ofNat 64 i = off C (d + i) by simp only [off, Offset.add_add]]
      exact hc₁ _ (by omega)
  rw [hCw 0 (by decide), hCw 8 (by decide), hCw 16 (by decide)] at *
  have k1' := k1.trans kc
  refine WP.block_append (WP.mono (gkHdr_ok ((kc.gpr .r23 (by decide)).trans h23₁) (by rw [k1'.wr]; exact hinH))
    fun s₂ ⟨⟨w8, w9, w10, w11, b3, b4, b5, o2⟩, k2⟩ => ?_)
  have k12 := k1'.trans k2
  refine WP.mono (setup0_ok (D := D) (L := L) (k := k) (b3.trans ((k1'.gpr .r7 (by decide)).trans hDd))
    (by rw [b4, k1'.gpr .r8 (by decide), ← hLd, VG.Proof.Bignum.ofNat_toNat64])
    (by rw [b5, k1'.gpr .r9 (by decide), ← hkd, VG.Proof.Bignum.ofNat_toNat64])
    ((k2.gpr .r23 (by decide)).trans ((kc.gpr .r23 (by decide)).trans h23₁)) hk')
    fun t ⟨⟨a21, a27, a28, s11, a29, a10, a31, m3⟩, k3⟩ => ?_
  have kall := k12.trans k3
  have hb3 : ∀ (Q : Addr) n, (∀ i < n, ∀ x, ofs S x < Z → off Q i ≠ x) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep => by
    rw [m3, outside_bytesAt o2 (by omega) hsep, outside_bytesAt oc (by omega) hsep]
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
  have hw2c : ∀ d, d + 8 ≤ 32 → word s₂.mem S d = word s₁'.mem S d := fun d hd =>
    o2.word (by omega) (by omega)
  refine ⟨⟨⟨hs.congr kall.wr, a10, a29, s11, a31, show 4 ≤ (k + 7) / 8 by omega,
    show (k + 7) / 8 ≤ 128 by omega, hZw⟩, a21, (k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans
      ((kc.gpr .r23 (by decide)).trans h23₁)),
    a27, a28, hk, hk', by simp only [Spec.Ffdh.domainLenValid] at hL; omega, rdD, sepD,
    fun i (hi : i < k) => by rw [off_off']; exact rdD _ (by omega), sepG, hb3 D L sepD, hb3 (off D k) k sepG⟩,
    ?_, ?_, ?_, ?_, fun i hi => ?_, by rw [hw3, hw2c 0 (by decide), c0],
    by rw [hw3, hw2c 8 (by decide), c1], by rw [hw3, hw2c 16 (by decide), c2], by rw [hw3, hw2c 24 (by decide), c3],
    hb3, kall.mono (by decide)⟩
  · rw [hw3, w8, kc.gpr .r3 (by decide), k1.gpr .r3 (by decide)]
  · rw [hw3, w9, kc.gpr .r4 (by decide), k1.gpr .r4 (by decide)]
  · rw [hw3, w10, kc.gpr .r5 (by decide), k1.gpr .r5 (by decide)]
  · rw [hw3, w11, kc.gpr .r10 (by decide), k1.gpr .r10 (by decide)]
  · rw [hw3, o2.word (by omega) (by omega), oc.word (by omega) (by omega)]
    have ea : off (savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [← k00.gpr _ (saved_ne1112 i hi), ← hS.saved i hi, a11'', ea]

end VG.Proof.Ffdh.PPC64LE.Cached
