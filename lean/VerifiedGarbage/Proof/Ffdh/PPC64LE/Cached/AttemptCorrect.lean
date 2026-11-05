module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptFn
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.Front
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.Attempt
import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.ScalarEq
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Status
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.DomainBody
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
public import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Rsa.FixedBaseCombTable
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.VettedPolicy
import VerifiedGarbage.Proof.Ffdh.KeyScalar
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

/-! ## The context's values -/

/-- Word `i` of the context. -/
theorem ctx_word {m : Mem} {C : Addr} {n i : Nat} (hi : i < n) :
    m.readW (off C (8 * i)) 64 = (Spec.Rsa.wordsAt m C n)[i]'(by simp [Spec.Rsa.wordsAt, hi]) := by
  simp [Spec.Rsa.wordsAt]

/-- `w` words of the context from word `d` that are `toWords x w`, as a number. -/
theorem ctx_val {m : Mem} {C : Addr} {n d w x : Nat} (hd : d + w ≤ n) (hx : x < 2 ^ (64 * w))
    (h : ((Spec.Rsa.wordsAt m C n).drop d).take w = Spec.Rsa.toWords x w) :
    val32 m C (8 * d) (2 * w) = x := by
  rw [Pre.val32_eq_wv, ← Nat.mod_eq_of_lt hx]
  refine VG.Proof.Bignum.wv_of_words fun i hi => ?_
  have e := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_take, hi, ↓reduceIte, List.getElem?_drop, Spec.Rsa.toWords, List.getElem?_map,
    List.getElem?_range hi, Option.map_some] at e
  rw [List.getElem?_eq_getElem (by simp [Spec.Rsa.wordsAt]; omega)] at e
  have e' := Option.some.inj e
  show (m.readW (off C (8 * d + 8 * i)) 64).toNat = _
  rw [show 8 * d + 8 * i = 8 * (d + i) by omega, ctx_word (n := n) (by omega), e', BitVec.toNat_ofNat]

/-- The context's facts the attempt reads, from its words. -/
theorem ctx_facts {m : Mem} {C : Addr} {k : Nat} {dom : List Byte}
    (h : Spec.Rsa.wordsAt m C (3 + 34 * ((k + 7) / 8)) = VG.Proof.Ffdh.generationValues k dom)
    (hp : 1 < (Spec.Ffdh.domainOf k dom).p) (hpw : (Spec.Ffdh.domainOf k dom).p < 2 ^ (64 * ((k + 7) / 8))) :
    word m C 0 = BitVec.ofNat 64 (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) ∧
    word m C 8 = BitVec.ofNat 64 ((Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) + 7) / 8) ∧
    word m C 16 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom))) ∧
    val32 m C (rowOff ((k + 7) / 8) 1) (2 * ((k + 7) / 8)) =
      2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % (Spec.Ffdh.domainOf k dom).p ∧
    ∀ a < 32, ent m C ((k + 7) / 8) a = combM (Spec.Ffdh.domainOf k dom).g (Spec.Ffdh.domainOf k dom).p ((k + 7) / 8)
      (Spec.Rsa.FixedBaseComb.exponent (Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom)) a) := by
  generalize hw : (k + 7) / 8 = w at h hpw ⊢
  have hP : 0 < (Spec.Ffdh.domainOf k dom).p := by omega
  have eh := VG.Proof.Ffdh.generationValues_headers k dom
  rw [← h] at eh
  have g : ∀ i (hi : i < 3), word m C (8 * i) = ((Spec.Rsa.wordsAt m C (3 + 34 * w)).take 3)[i]'(by
      simp [Spec.Rsa.wordsAt]; omega) := fun i hi => by
    show m.readW (off C (8 * i)) 64 = _
    rw [ctx_word (n := 3 + 34 * w) (by omega), List.getElem_take]
  refine ⟨?_, ?_, ?_, ?_, fun a ha => ?_⟩
  · have := g 0 (by decide); simp only [eh] at this; simpa using this
  · have := g 1 (by decide); simp only [eh] at this; simpa using this
  · have := g 2 (by decide); simp only [eh] at this; simpa using this
  · have em := VG.Proof.Ffdh.generationValues_montgomery k dom
    simp only [Spec.Rsa.modulusWords, hw] at em
    rw [← h] at em
    have e2 : ((Spec.Rsa.wordsAt m C (3 + 34 * w)).drop (3 + w)).take w =
        Spec.Rsa.toWords (2 ^ (128 * w) % (Spec.Ffdh.domainOf k dom).p) w := by
      have h1 : (((Spec.Rsa.wordsAt m C (3 + 34 * w)).drop 3).take (2 * w)).drop w =
          Spec.Rsa.toWords (2 ^ (128 * w) % (Spec.Ffdh.domainOf k dom).p) w := by
        rw [em]; exact List.drop_left' (VG.Proof.Rsa.FixedBaseComb.toWords_length _ _)
      rw [List.drop_take, List.drop_drop, show 2 * w - w = w by omega] at h1
      simpa only [Nat.add_comm] using h1
    rw [show rowOff w 1 = 8 * (3 + w) by unfold rowOff; omega, ctx_val (by omega) (by
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ hP) (Nat.le_of_lt hpw)) e2, ← Nat.pow_add, show 64 * w + 64 * w = 128 * w by omega]
  · have ee := VG.Proof.Ffdh.generationValues_entry k dom a ha
    simp only [Spec.Rsa.modulusWords, hw] at ee
    rw [← h] at ee
    have hfit : 3 + (2 + a) * w + w ≤ 3 + 34 * w := by
      have h' := Nat.mul_le_mul_right w (show 2 + a + 1 ≤ 34 by omega); rw [Nat.succ_mul] at h'; omega
    unfold ent
    rw [show rowOff w (a + 2) = 8 * (3 + (2 + a) * w) by unfold rowOff; rw [Nat.mul_comm w, Nat.add_comm a 2]; omega]
    exact ctx_val hfit (Nat.lt_of_lt_of_le (Nat.mod_lt _ hP) (Nat.le_of_lt hpw)) ee

/-! ## The width -/

theorem recognized_nonzero {a : Spec.Ffdh.Parameters} {bits : Nat}
    (h : Spec.Ffdh.vettedExponentBits a = some bits) : bits ≠ 0 := by
  unfold Spec.Ffdh.vettedExponentBits at h
  repeat' split at h
  all_goals cases h
  all_goals decide

theorem bitLength_le_of_lt {x n : Nat} (h : x < 2 ^ n) : Spec.RsaKeyGen.bitLength x ≤ n := by
  by_cases hx : x = 0
  · subst hx; unfold Spec.RsaKeyGen.bitLength; simp
  · have hb := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds hx).1
    by_contra hc
    have : 2 ^ n ≤ 2 ^ (Spec.RsaKeyGen.bitLength x - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- The public scalar width of valid parameters: at least 1 and at most
p's bits. -/
theorem genBits_facts {k : Nat} {dom : List Byte} (hv : Spec.Ffdh.domainValid k dom = true) :
    1 ≤ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ∧
      Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k dom) ≤ 8 * k := by
  have hv' := (VG.Proof.Ffdh.domainValid_iff k dom).mp hv
  have hbnd : 2 ≤ Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.1; simp only [Option.getD_some]; omega
  have hle : Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≤ (Spec.Ffdh.domainOf k dom).p := by
    unfold Spec.Ffdh.scalarBound
    cases hq : (Spec.Ffdh.domainOf k dom).q with
    | none => simp only [Option.getD_none]; omega
    | some q => have := (hv'.2.2 q hq).1.2.2; simp only [Option.getD_some]; omega
  have hp : (Spec.Ffdh.domainOf k dom).p < 2 ^ (8 * k) := by
    have h1 := VG.Proof.Bignum.os2ip_lt (dom.take k)
    have h2 : 256 ^ (dom.take k).length ≤ 2 ^ (8 * k) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by simp only [List.length_take]; omega)
    change Spec.Rsa.os2ip (dom.take k) < _
    omega
  have hb := VG.Proof.Ffdh.VettedPolicy.bits_le_bound (Spec.Ffdh.domainOf k dom)
  have hbl : 1 ≤ Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) := by
    have := (VG.Proof.Ffdh.KeyScalar.bitLength_bounds
      (show Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom) ≠ 0 by omega)).2
    by_contra hc
    have e : Spec.RsaKeyGen.bitLength (Spec.Ffdh.scalarBound (Spec.Ffdh.domainOf k dom)) = 0 := by omega
    rw [e] at this; omega
  refine ⟨?_, Nat.le_trans hb (bitLength_le_of_lt (Nat.lt_of_le_of_lt hle hp))⟩
  unfold Spec.Ffdh.generationScalarBits
  cases he : Spec.Ffdh.vettedExponentBits (Spec.Ffdh.domainOf k dom) with
  | none => simpa using hbl
  | some b => have := recognized_nonzero he; simp only; omega

/-! ## Correctness -/

theorem wordsAt_congr {m m' : Mem} {C : Addr} {n : Nat}
    (h : ∀ i < 8 * n, m' (C + BitVec.ofNat 64 i) = m (C + BitVec.ofNat 64 i)) :
    Spec.Rsa.wordsAt m' C n = Spec.Rsa.wordsAt m C n := by
  unfold Spec.Rsa.wordsAt
  refine List.map_congr_left fun i hi => Mem.readW_congr fun b hb => ?_
  have hi' := List.mem_range.mp hi
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  exact h _ (by omega)

theorem byte_of_bytesAt {m m' : Mem} {Q : Addr} {n : Nat} (h : Spec.Rsa.bytesAt m' Q n = Spec.Rsa.bytesAt m Q n)
    {i : Nat} (hi : i < n) : m' (Q + BitVec.ofNat 64 i) = m (Q + BitVec.ofNat 64 i) := by
  have := congrArg (fun l => l[i]?) h
  simpa [Spec.Rsa.bytesAt, hi] using this

private theorem cg_pres_not_written : ∀ r ∈ preserved, (∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i) →
    r ∉ cgFrontRegs ++ ([.r0, .r6, .r12, .r14, .r15, .r16, .r17, .r18] : List Reg) ++
      (bodyRegs ++ ([.r3] : List Reg)) := by
  decide

theorem ret_st (n : Nat) (hn : n < 2 ^ 32) : ((BitVec.ofNat 64 n).setWidth 32).toNat = n := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem cg_correct (s : State) (h : cgContract.pre s) :
    ∃ tr t, Exec isa Generate.code s tr t ∧ abiPreserved s t ∧ cgContract.post s t := by
  show WP isa Generate.code s fun t => abiPreserved s t ∧ cgContract.post s t
  have hpre := h
  obtain ⟨-, hrd, hwr, dXY, dXD, dXR, dXS, dXC, -, dYD, -, dYS, dYC, -, dDS, dRS, dSC, -, nwX, nwY, -, nwR, nwS, nwC,
    ⟨hk64, hk1024⟩, hL, hxl, hyl, hrl, hsl, hdv, hctx⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  rw [hxl] at hwr dXY dXD dXR dXS dXC nwX
  rw [hyl] at hwr dXY dYD dYS dYC nwY
  rw [hrl] at hrd dXR dRS nwR
  have hcl : (stackArg s 4).toNat = 3 + 34 * (((s.gpr .r9).toNat + 7) / 8) := by
    rw [hctx.1]
    simp only [Spec.Ffdh.generationPrecomputedWords, Spec.Rsa.FixedBaseComb.precomputedWords,
      Spec.Rsa.precomputedWords, Spec.Rsa.FixedBaseComb.entries, Spec.Rsa.FixedBaseComb.teeth, Spec.Rsa.modulusWords]
    omega
  have hctxw := hctx.2
  rw [hcl] at hrd dXC dYC dSC nwC hctxw
  generalize hkd : (s.gpr .r9).toNat = k at hk64 hk1024 hL hxl hyl hrl hsl hwr dXY dXD dXR dXS dYD dYS dRS hrd nwR
  generalize hkd' : (s.gpr .r9).toNat = k' at nwX nwY dXC dYC dSC nwC hctxw hdv hcl
  rw [hkd] at hkd'; subst hkd'
  have hin : ∀ i < 18, InRegions s.wr (off (Domain.savW (stackArg s 1)) (8 * i)) 8 := fun i hi =>
    ⟨⟨stackArg s 1, (stackArg s 2).toNat * 8⟩, by rw [hwr]; simp, by
      rw [off, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)⟩
  -- The arguments apart.
  have sepXS := sep_of_disjoint dXS (by omega)
  have sepSX : ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → k ≤ ofs (s.gpr .r3) y :=
    Pub.sep_of_disjoint dXS.symm
  have sepRX := sep_of_disjoint dXR.symm (by omega)
  have sepDX := sep_of_disjoint dXD.symm (by omega)
  have sepXO := sep_of_disjoint dXY (by omega)
  have sepOX := sep_of_disjoint dXY.symm (by omega)
  have sepOS : ∀ x, ofs (s.gpr .r5) x < k → (stackArg s 2).toNat * 8 ≤ ofs (stackArg s 1) x :=
    Pub.sep_of_disjoint dYS
  have sepSO : ∀ x, ofs (stackArg s 1) x < (stackArg s 2).toNat * 8 → k ≤ ofs (s.gpr .r5) x :=
    Pub.sep_of_disjoint dYS.symm
  have sepRS := sep_of_disjoint dRS (by omega)
  have sepCX : ∀ y, ofs (stackArg s 3) y < (3 + 34 * ((k + 7) / 8)) * 8 → k ≤ ofs (s.gpr .r3) y :=
    Pub.sep_of_disjoint dXC.symm
  have sepCS : ∀ y, ofs (stackArg s 3) y < (3 + 34 * ((k + 7) / 8)) * 8 →
      (stackArg s 2).toNat * 8 ≤ ofs (stackArg s 1) y := Pub.sep_of_disjoint dSC.symm
  have sepCSi := sep_of_disjoint dSC.symm (by omega)
  have h4 : s.gpr .r4 = BitVec.ofNat 64 k := by rw [← hxl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  unfold Generate.code
  refine WP.seq (WP.mono (cg_front hpre) fun s₁ ⟨hb, w8, w9, w10, w11, hsav, wc0, wc8, wc16, wc24, hby, k1⟩ => ?_)
  have ek : (gcOf s).k = k := hkd
  have hk := hb.k64
  have hk' := hb.k1024
  have hLk := hb.hL
  have hZ := hb.env.hZ
  have hnw := hb.env.hs.nowrap
  rw [ek] at hk hk' hLk
  have e0 := Domain.slot_eq (gcOf s).w 0
  have e28 := Domain.slot_eq (gcOf s).w 28
  refine WP.seq (WP.mono (loadP_ok hb.env hb.r21 (by rw [hb.r28, ek]) rfl (by rw [ek]; omega) (by rw [ek]; omega)
    (fun i hi => hb.rdD i (by omega)) (fun i hi => hb.sepD i (by omega))) fun s₂ ⟨⟨p2, c2, b2⟩, k2⟩ => ?_)
  have hb2 := hb.keep k2 b2
  have k12 := k1.trans k2
  -- The bytes apart from the working space.
  have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₂.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq => by
    rw [b2.bytesAt hZ hq]; exact hby Q n hq
  have sepD : ∀ i < (s.gpr .r8).toNat, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off (s.gpr .r7) i ≠ y :=
    hb.sepD
  rw [show (gcOf s).D = s.gpr .r7 from rfl, ek, hby _ _ fun i hi => sepD i (by
    rcases hLk with h | h <;> simp only [gcOf] at h <;> omega)] at p2 c2
  generalize hp : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) k) = p at p2 c2
  have hpk : p < 256 ^ k := by
    rw [← hp]; have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (s.gpr .r7) k)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hw2 : ∀ d, d + 8 ≤ 256 → word s₂.mem (stackArg s 1) d = word s₁.mem (stackArg s 1) d := fun d hd => by
    have b2' : Body (stackArg s 1) (gcOf s).w s₁.mem s₂.mem := b2
    rw [Outside.word b2' (by omega) (by omega)]
  have hL' : (s.gpr .r8).toNat = 2 * k ∨ (s.gpr .r8).toNat = 3 * k := hLk
  rw [show (gcOf s).S = stackArg s 1 from rfl, show (gcOf s).w = (k + 7) / 8 by simp only [gcOf, CD.w]; rw [hkd]] at p2
  -- The context, as `s₂` has it.
  have hcm : ∀ i < 8 * (3 + 34 * ((k + 7) / 8)), s₂.mem (stackArg s 3 + BitVec.ofNat 64 i) =
      s.mem (stackArg s 3 + BitVec.ofNat 64 i) := fun i hi =>
    byte_of_bytesAt (hsep _ (8 * (3 + 34 * ((k + 7) / 8))) fun j hj => sepCSi j (by omega)) hi
  have hlenD : k ≤ (cgDom s).length := by
    rw [VG.Proof.Bignum.bytesAt_length]; rcases hL' with h | h <;> omega
  have hmod := VG.Proof.Ffdh.domainValid_mod hdv
  have hwv : Spec.Rsa.wordsAt s.mem (stackArg s 3) (3 + 34 * ((k + 7) / 8)) =
      VG.Proof.Ffdh.generationValues k (cgDom s) := by
    have e := VG.Proof.Ffdh.generationPrecompute_eq hlenD hmod
    rw [hctxw] at e; exact Option.some.inj e
  have hwv2 : Spec.Rsa.wordsAt s₂.mem (stackArg s 3) (3 + 34 * ((k + 7) / 8)) =
      VG.Proof.Ffdh.generationValues k (cgDom s) := by rw [wordsAt_congr hcm, hwv]
  have hpd : (Spec.Ffdh.domainOf k (cgDom s)).p = p := by
    rw [VG.Proof.Ffdh.domainOf_p _ _ (by rcases hL' with h | h <;> omega), hp]
  rw [hpd] at hmod
  have hf := modulus_facts hmod
  have hpw : p < 2 ^ (64 * ((k + 7) / 8)) := Nat.lt_of_lt_of_le hpk (by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨cb, cy, cr, -, -⟩ := ctx_facts hwv (by rw [hpd]; omega) (by rw [hpd]; exact hpw)
  obtain ⟨-, -, -, cr2, cent⟩ := ctx_facts hwv2 (by rw [hpd]; omega) (by rw [hpd]; exact hpw)
  rw [hpd] at cr2 cent
  have hbits := genBits_facts hdv
  generalize hbd : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k (cgDom s)) = bits at cb cy cr cent hbits
  have hg : (Spec.Ffdh.domainOf k (cgDom s)).g = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off (s.gpr .r7) k) k) := by
    rw [VG.Proof.Ffdh.domainOf_g _ _ (by rcases hL' with h | h <;> omega), hsep _ _ fun i hi => by
      rw [off_off']; exact sepD _ (by rcases hL' with h | h <;> omega)]
  rw [hg] at cent
  generalize hD : s.gpr .r7 = D at hp sepD hsep hL' sepDX dYD dXD hrd cent hg ⊢
  generalize hL'' : (s.gpr .r8).toNat = L at hL' sepD sepDX dYD dXD hrd ⊢
  have sepG : ∀ i < k, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off (off D k) i ≠ y :=
    fun i hi => by rw [off_off']; exact sepD _ (by omega)
  -- The arguments, as the code reads them.
  generalize hS : stackArg s 1 = S at hsep sepG sepD sepXS sepSX sepRS sepOS sepSO hw2 hsav hin p2 sepCS ⊢
  generalize hS' : stackArg s 1 = S' at sepCSi hcm wc0 wc8 wc16 wc24 w8 w9 w10 w11
  rw [hS] at hS'; subst hS'
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hsep sepG sepD sepXS sepSX sepRS sepOS sepSO sepCS sepCSi
  have g23 : s₂.gpr .r23 = S := hb2.r23.trans hS
  have e2 : VG.Proof.MillerRabin.PPC64LE.Env s₂ S Z ((k + 7) / 8) := by
    have := hb2.env; rw [show (gcOf s).S = stackArg s 1 from rfl, hS] at this
    simp only [gcOf, CD.w] at this; rw [hkd, hZd] at this; exact this
  have hc2 : CtxRd s₂ S Z (stackArg s 3) ((k + 7) / 8) := by
    refine ⟨by rw [show hCtx = 0 from rfl]; exact (hw2 0 (by omega)).trans wc0, by have := nwC; unfold ctxWords; omega,
      fun d hd => ?_, fun x hx => by have := sepCS x (by unfold ctxWords at hx; omega); omega⟩
    rw [k12.rd, k12.wr]
    exact ⟨⟨stackArg s 3, (3 + 34 * ((k + 7) / 8)) * 8⟩, List.mem_append_left _ (by rw [hrd]; simp),
      Offset.contains_base _ (by unfold ctxWords at hd; omega) (by unfold ctxWords at hd; omega)⟩
  have hite : WP isa (.ite (.zero .d .r0) body (.block [.li .r3 0])) s₂ fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt
          (Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut (Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) k)
            (k - (bits + 7) / 8) (tbOf bits)))
          (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k)) p (Derive.bnd s₂.mem D k L p)) ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .r5) k = (if VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt
            (Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut (Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) k)
              (k - (bits + 7) / 8) (tbOf bits)))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k)) p (Derive.bnd s₂.mem D k L p) = 1 then
          Spec.Rsa.i2osp (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k) ^
            Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut (Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) k)
              (k - (bits + 7) / 8) (tbOf bits)) % p) k else List.replicate k 0) ∧
        Spec.Rsa.bytesAt t.mem (s.gpr .r3) k = (if VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt
            (Spec.Rsa.os2ip (VG.Proof.Ffdh.KeyScalar.cut (Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) k)
              (k - (bits + 7) / 8) (tbOf bits)))
            (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off D k) k)) p (Derive.bnd s₂.mem D k L p) = 1 then
          VG.Proof.Ffdh.KeyScalar.cut (Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) k) (k - (bits + 7) / 8) (tbOf bits)
          else List.replicate k 0)) ∧
      (∀ i < 18, word t.mem S (112 + 8 * i) = word s₂.mem S (112 + 8 * i)) ∧
      Keep (bodyRegs ++ ([.r3] : List Reg)) s₂ t := by
    refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
    · have rdR : ∀ i < k, InRegions (s₂.rd ++ s₂.wr) (off (s.gpr .r10) i) 1 := by
        rw [k12.rd, k12.wr]
        exact rd_of_mem (s := s) (D := s.gpr .r10) (L := k) (by rw [hrd]; simp) (by omega)
      refine WP.mono (bodyC_ok (s := s₂) (Z := Z) (w := (k + 7) / 8) (k := k) (L := L) (p := p) (B := S) (D := D)
        (X := s.gpr .r3) (O := s.gpr .r5) (R := s.gpr .r10) (C := stackArg s 3) (bits := bits) e2 g23
        (by rw [hb2.r21]; exact hD) (by rw [hb2.r27, ← hL'']; rfl) (by rw [hb2.r28, ek]) rfl hk hk' hL'
        (by show word s₂.mem S 64 = _; rw [hw2 64 (by omega), w8]; simp [off])
        (by show word s₂.mem S 72 = _; rw [hw2 72 (by omega), w9, h4])
        (by show word s₂.mem S 80 = _; rw [hw2 80 (by omega), w10]; simp [off])
        (by show word s₂.mem S 88 = _; rw [hw2 88 (by omega), w11]; simp [off])
        (by show word s₂.mem S 8 = _; rw [hw2 8 (by omega), wc8]; exact cb)
        (by show word s₂.mem S 16 = _; rw [hw2 16 (by omega), wc16]; exact cy)
        (by show word s₂.mem S 24 = _; rw [hw2 24 (by omega), wc24]; exact cr)
        hc2 (fun y hy => sepCX y (by unfold ctxWords at hy; omega)) cent cr2 hbits.1 hbits.2
        (fun i hi => by
          have := hb2.rdD i (show i < (s.gpr .r8).toNat by omega)
          rwa [show (gcOf s).D = s.gpr .r7 from rfl, hD] at this)
        sepD rdR
        (Scr.of_mem (by rw [k12.wr, hwr]; simp) nwX) sepXS sepSX sepRX sepDX sepXO sepOX
        (Scr.of_mem (by rw [k12.wr, hwr]; simp) nwY) sepOS sepSO p2 hf.1 hf.2 hpk)
        fun t ⟨⟨t3, ty, tx, tw⟩, kt⟩ => ⟨⟨t3, ty, tx⟩, fun i hi => tw _ (.inr (by omega)) (by omega),
          kt.mono fun r hr => List.mem_append_left _ hr⟩
    · exact absurd (c2.mpr hmod) (by simpa using hz)
  refine WP.seq (WP.mono hite fun t₅ ⟨tpost, tw, k5⟩ => ?_)
  have kall := k12.trans k5
  have hsav' : ∀ i < 18, t₅.mem.readW (off (Domain.savW S) (8 * i)) 64 =
      s.gpr (Impl.Ffdh.PPC64LE.Domain.saved i) := fun i hi => by
    have ea : off (Domain.savW S) (8 * i) = off S (112 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [ea]
    show word t₅.mem S (112 + 8 * i) = _
    rw [tw i hi, hw2 _ (by omega)]
    exact hsav i hi
  refine WP.mono (Domain.restore_ok t₅ ((k5.gpr .r23 (by decide)).trans g23) (by rw [kall.wr]; exact hin) hsav')
    fun u ⟨urs, uot, um, _, _, usp, ulr⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [usp, kall.sp], by rw [ulr, kall.lr]⟩, ?_⟩
  · by_cases hs' : ∃ i < 18, r = Impl.Ffdh.PPC64LE.Domain.saved i
    · obtain ⟨i, hi, rfl⟩ := hs'
      exact urs i hi
    · have hn : ∀ i < 18, r ≠ Impl.Ffdh.PPC64LE.Domain.saved i := fun i hi e => hs' ⟨i, hi, e⟩
      rw [uot r hn, kall.gpr r (cg_pres_not_written r hr hn)]
  · -- The bytes the code read, as the arguments' bytes.
    have eR : Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) k = Spec.Rsa.bytesAt s.mem (s.gpr .r10) k := hsep _ _ sepRS
    have eg : Spec.Rsa.bytesAt s₂.mem (off D k) k = Spec.Rsa.bytesAt s.mem (off D k) k := hsep _ _ sepG
    have eb : Derive.bnd s₂.mem D k L p = Derive.bnd s.mem D k L p := by
      unfold Derive.bnd
      by_cases hq : L = 3 * k
      · rw [ite_eq_left hq, ite_eq_left hq, hsep _ _ fun i hi => by rw [off_off']; exact sepD _ (by omega)]
      · rw [ite_eq_right hq, ite_eq_right hq]
    rw [eR, eg, eb] at tpost
    obtain ⟨t3, ty, tx⟩ := tpost
    have hlen : (Spec.Rsa.bytesAt s.mem (s.gpr .r10) k).length = k := VG.Proof.Bignum.bytesAt_length _ _ _
    have hxv := scalarC_value hlen hbits.1 hbits.2
    have hlen' : (VG.Proof.Ffdh.KeyScalar.cut (Spec.Rsa.bytesAt s.mem (s.gpr .r10) k) (k - (bits + 7) / 8)
        (tbOf bits)).length = k := by rw [VG.Proof.Ffdh.KeyScalar.cut_length _ (by omega), hlen]
    generalize hxo : VG.Proof.Ffdh.KeyScalar.cut (Spec.Rsa.bytesAt s.mem (s.gpr .r10) k) (k - (bits + 7) / 8)
      (tbOf bits) = xo at t3 ty tx hxv hlen'
    have hbd' : Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf k (Spec.Rsa.bytesAt s.mem D L)) = bits := by
      rw [← hD, ← hL'']; exact hbd
    have hdv' : Spec.Ffdh.domainValid k (Spec.Rsa.bytesAt s.mem D L) = true := by rw [← hD, ← hL'']; exact hdv
    dsimp only [cgContract, cgScalar, cgA, cgDom]
    rw [hD, hL'', hkd, hrl, Spec.Ffdh.vettedScalarOfOctets, hbd', ← hxv]
    rw [Derive.keyStatus_dom (by omega) hL' hdv', VG.Proof.Ffdh.domainOf_g _ _ (by omega),
      VG.Proof.Ffdh.domainOf_p _ _ (by omega), hp, VG.Proof.Bignum.powMod_eq]
    rw [um, uot .r3 (by decide), t3, ret_st _ (by
      unfold VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt; split <;> [decide; split <;> decide])]
    rw [ty, tx]
    refine ⟨rfl, ?_⟩
    by_cases h1 : VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt (Spec.Rsa.os2ip xo)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p (Derive.bnd s.mem D k L p) = 1
    · rw [ite_eq_left h1, ite_eq_left h1]
      simp only [VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt] at h1 ⊢
      rw [ite_eq_left h1]
      refine ⟨?_, trivial⟩
      have e := VG.Proof.Rsa.i2osp_os2ip xo
      rw [hlen'] at e
      exact e.symm
    · rw [ite_eq_right h1, ite_eq_right h1]
      simp only [VG.Proof.Ffdh.PPC64LE.GenerateKey.gkSt] at h1 ⊢
      rw [ite_eq_right h1]
      exact ⟨trivial, trivial⟩

end VG.Proof.Ffdh.PPC64LE.Cached
