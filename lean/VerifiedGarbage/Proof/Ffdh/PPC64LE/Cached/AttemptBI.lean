module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCorrect
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.GenerateKey.CT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeCorrect
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Ffdh.GenerationPrecompute
import VerifiedGarbage.Proof.Ffdh.Domain
import VerifiedGarbage.Proof.Ffdh.KeyScalar
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_ffdh_generate_key_cached` on PPC64LE: the public data, and the body's entry

The public data of an attempt (`CG`): `vg_ffdh_generate_key`'s (`GD`), with
x's range for x cut to the context's width, the context's address and the
width. `cg_toBI`: after the front, p's load and check reach the body with
what it needs (`BI`, `bodyC_ok`'s hypotheses), as `cg_correct` shows.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Ffdh.PPC64LE.Domain
open VG.Impl.Ffdh.PPC64LE.Cached VG.Impl.Ffdh.PPC64LE.Cached.Generate
open VG.Proof.Ffdh.PPC64LE.Domain
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gcOf gxOf GD)
open VG.Proof.Ffdh.KeyScalar (cut)
open VG.Proof.MillerRabin.PPC64LE (Env arr)
open VG.Proof.Bignum (slot)

/-- x's value as the attempt cuts it from `rand`'s `k` octets at `R`. -/
abbrev cgX (k bits : Nat) (m : Mem) (R : Addr) : Nat :=
  Spec.Rsa.os2ip (cut (Spec.Rsa.bytesAt m R k) (k - (bits + 7) / 8) (tbOf bits))

/-- The public data of an attempt. -/
structure CG where
  g : GD
  C : Addr
  bits : Nat

abbrev CG.c (q : CG) : CD := q.g.d.x.c

def cgOf (s : State) : CG :=
  ⟨⟨⟨gxOf s, Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p,
    decide (0 < cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) ∧
      cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) <
        Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p)⟩, s.gpr .r10⟩,
    stackArg s 3, Spec.Ffdh.generationScalarBits (cgA s)⟩

/-- What the body needs (`bodyC_ok`'s hypotheses), and x's range. -/
structure BI (S D X O R C : Addr) (Z k L p bits : Nat) (v : Bool) (s : State) : Prop where
  env : Env s S Z ((k + 7) / 8)
  h23 : s.gpr .r23 = S
  h21 : s.gpr .r21 = D
  h27 : s.gpr .r27 = BitVec.ofNat 64 L
  h28 : s.gpr .r28 = BitVec.ofNat 64 k
  hk : 64 ≤ k
  hk' : k ≤ 1024
  hL : L = 2 * k ∨ L = 3 * k
  hX : s.mem.readW (off S 64) 64 = off X 0
  hXL : s.mem.readW (off S 72) 64 = BitVec.ofNat 64 k
  hO : s.mem.readW (off S 80) 64 = off O 0
  hR : s.mem.readW (off S 88) 64 = off R 0
  hbw : s.mem.readW (off S hBits) 64 = BitVec.ofNat 64 bits
  hyw : s.mem.readW (off S hBytes) 64 = BitVec.ofNat 64 ((bits + 7) / 8)
  hRw : s.mem.readW (off S hRows) 64 = BitVec.ofNat 64 (Spec.Rsa.FixedBaseComb.rows bits)
  hCw : s.mem.readW (off S hCtx) 64 = C
  hc : CtxRd s S Z C ((k + 7) / 8)
  hsepCX : ∀ y, ofs C y < 8 * ctxWords ((k + 7) / 8) → k ≤ ofs X y
  hents : ∀ a < 32, ent s.mem C ((k + 7) / 8) a =
    combM (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off D k) k)) p ((k + 7) / 8)
      (Spec.Rsa.FixedBaseComb.exponent bits a)
  hr2 : val32 s.mem C (rowOff ((k + 7) / 8) 1) (2 * ((k + 7) / 8)) =
    2 ^ (64 * ((k + 7) / 8)) * 2 ^ (64 * ((k + 7) / 8)) % p
  hb1 : 1 ≤ bits
  hbk : bits ≤ 8 * k
  hrdD : ∀ i < L, InRegions (s.rd ++ s.wr) (off D i) 1
  hsepD : ∀ i < L, ∀ x, ofs S x < Z → off D i ≠ x
  hrdR : ∀ i < k, InRegions (s.rd ++ s.wr) (off R i) 1
  hx : Scr s X k
  hsepX : ∀ i < k, ∀ y, ofs S y < Z → off X i ≠ y
  hsepBX : ∀ y, ofs S y < Z → k ≤ ofs X y
  hsepRX : ∀ i < k, ∀ y, ofs X y < k → off R i ≠ y
  hsepDX : ∀ i < L, ∀ y, ofs X y < k → off D i ≠ y
  hsepXO : ∀ i < k, ∀ y, ofs O y < k → off X i ≠ y
  hsepOX : ∀ i < k, ∀ y, ofs X y < k → off O i ≠ y
  ho : Scr s O k
  hsepO : ∀ x, ofs O x < k → Z ≤ ofs S x
  hsepB : ∀ x, ofs S x < Z → k ≤ ofs O x
  hP : arr s.mem S ((k + 7) / 8) 0 = p
  hp2 : 2 ≤ p
  hodd : p % 2 = 1
  hpk : p < 256 ^ k
  hv : (0 < cgX k bits s.mem R ∧ cgX k bits s.mem R < Derive.bnd s.mem D k L p) ↔ v = true

/-- `BI` of the public data. -/
abbrev BIq (q : CG) (s : State) : Prop :=
  BI q.c.S q.c.D q.g.d.x.X q.g.d.x.O q.g.R q.C q.c.Z q.c.k q.c.L q.c.p q.bits q.g.d.v s

/-- After p's check: whether p is valid, the working space, and, if it is,
what the body needs. -/
def A4 (q : CG) (s : State) : Prop :=
  ((s.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid q.c.p q.c.k = true) ∧ s.gpr .r23 = q.c.S) ∧
    (s.gpr .r0 = 0 → BIq q s)

/-- The front, then p's load and check, reach the body with `BI`. -/
theorem cg_toBI {s : State} (h : cgContract.pre s) :
    WP isa (.block front) s fun s₁ => Base (gcOf s) s₁ ∧ WP isa loadP s₁ (A4 (cgOf s)) := by
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
  rw [hcl] at nwC hctxw dXC dYC dSC hrd
  refine WP.mono (cg_front hpre) fun s₁ ⟨hb, w8, w9, w10, w11, _, wc0, wc8, wc16, wc24, hby, k1⟩ => ⟨hb, ?_⟩
  have hk := hb.k64
  have hk' := hb.k1024
  have hLk := hb.hL
  have hZ := hb.env.hZ
  have e0 := Domain.slot_eq (gcOf s).w 0
  have e28 := Domain.slot_eq (gcOf s).w 28
  refine WP.mono (loadP_ok hb.env hb.r21 hb.r28 rfl hk hk' (fun i hi => hb.rdD i (by
      rcases hLk with h | h <;> omega)) (fun i hi => hb.sepD i (by rcases hLk with h | h <;> omega)))
    fun s₂ ⟨⟨p2, c2, b2⟩, k2⟩ => ?_
  have hb2 := hb.keep k2 b2
  have k12 := k1.trans k2
  have hsep : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off Q i ≠ y) →
      Spec.Rsa.bytesAt s₂.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hq => by
    rw [b2.bytesAt hZ hq]; exact hby Q n hq
  have sepD : ∀ i < (s.gpr .r8).toNat, ∀ y, ofs (stackArg s 1) y < (stackArg s 2).toNat * 8 → off (s.gpr .r7) i ≠ y :=
    hb.sepD
  have hL' : (s.gpr .r8).toNat = 2 * (s.gpr .r9).toNat ∨ (s.gpr .r8).toNat = 3 * (s.gpr .r9).toNat := hLk
  have ep : (gcOf s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by
    show Spec.Rsa.os2ip ((Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat).take (s.gpr .r9).toNat) = _
    rw [Proof.Ffdh.take_bytesAt _ _ (by omega)]
  have eD : Spec.Rsa.bytesAt s₁.mem (s.gpr .r7) (s.gpr .r9).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat := hby _ _ fun i hi => sepD i (by omega)
  rw [show (gcOf s).D = s.gpr .r7 from rfl, show (gcOf s).k = (s.gpr .r9).toNat from rfl, eD] at p2 c2
  refine ⟨⟨by show _ ↔ Spec.Rsa.modulusValid (gcOf s).p _ = true; rw [ep]; exact c2, hb2.r23⟩, fun hz => ?_⟩
  have hmodP := c2.mp hz
  show BI (stackArg s 1) (s.gpr .r7) (s.gpr .r3) (s.gpr .r5) (s.gpr .r10) (stackArg s 3)
    ((stackArg s 2).toNat * 8) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p
    (Spec.Ffdh.generationScalarBits (cgA s)) (decide (0 < cgX (s.gpr .r9).toNat
      (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) ∧
      cgX (s.gpr .r9).toNat (Spec.Ffdh.generationScalarBits (cgA s)) s.mem (s.gpr .r10) <
        Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat (gcOf s).p)) s₂
  rw [ep]
  have hlenD : (s.gpr .r9).toNat ≤ (cgDom s).length := by
    rw [VG.Proof.Bignum.bytesAt_length]; rcases hL' with h | h <;> omega
  have hmod := VG.Proof.Ffdh.domainValid_mod hdv
  have hpd : (cgA s).p = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) := by
    rw [VG.Proof.Ffdh.domainOf_p _ _ (by rcases hL' with h | h <;> omega)]
  have hbits := genBits_facts hdv
  have hwv : Spec.Rsa.wordsAt s.mem (stackArg s 3) (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)) =
      VG.Proof.Ffdh.generationValues (s.gpr .r9).toNat (cgDom s) := by
    have e := VG.Proof.Ffdh.generationPrecompute_eq hlenD hmod
    rw [hctxw] at e; exact Option.some.inj e
  have sepCSi := sep_of_disjoint dSC.symm (by omega)
  have hcm : ∀ i < 8 * (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)), s₂.mem (stackArg s 3 + BitVec.ofNat 64 i) =
      s.mem (stackArg s 3 + BitVec.ofNat 64 i) := fun i hi =>
    byte_of_bytesAt (hsep _ (8 * (3 + 34 * (((s.gpr .r9).toNat + 7) / 8))) fun j hj => sepCSi j (by omega)) hi
  have hwv2 : Spec.Rsa.wordsAt s₂.mem (stackArg s 3) (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)) =
      VG.Proof.Ffdh.generationValues (s.gpr .r9).toNat (cgDom s) := by rw [wordsAt_congr hcm, hwv]
  have hpk : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) < 256 ^ (s.gpr .r9).toNat := by
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  have hf := modulus_facts hmodP
  have hpw : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r9).toNat) <
      2 ^ (64 * (((s.gpr .r9).toNat + 7) / 8)) := Nat.lt_of_lt_of_le hpk (by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega))
  obtain ⟨cb, cy, cr, -, -⟩ := ctx_facts hwv (by rw [hpd]; omega) (by rw [hpd]; exact hpw)
  obtain ⟨-, -, -, cr2, cent⟩ := ctx_facts hwv2 (by rw [hpd]; omega) (by rw [hpd]; exact hpw)
  rw [hpd] at cr2 cent
  have hg : (cgA s).g = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₂.mem (off (s.gpr .r7) (s.gpr .r9).toNat)
      (s.gpr .r9).toNat) := by
    rw [VG.Proof.Ffdh.domainOf_g _ _ (by rcases hL' with h | h <;> omega), hsep _ _ fun i hi => by
      rw [off_off']; exact sepD _ (by rcases hL' with h | h <;> omega)]
  rw [hg] at cent
  have hw2 : ∀ d, d + 8 ≤ 256 → word s₂.mem (stackArg s 1) d = word s₁.mem (stackArg s 1) d := fun d hd => by
    have b2' : Body (stackArg s 1) (gcOf s).w s₁.mem s₂.mem := b2
    rw [Outside.word b2' (by omega) (by omega)]
  have h4 : s.gpr .r4 = BitVec.ofNat 64 (s.gpr .r9).toNat := by
    rw [← hxl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have eR : Spec.Rsa.bytesAt s₂.mem (s.gpr .r10) (s.gpr .r9).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .r10) (s.gpr .r9).toNat := hsep _ _ (sep_of_disjoint dRS (by omega))
  have eb : Derive.bnd s₂.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat =
      Derive.bnd s.mem (s.gpr .r7) (s.gpr .r9).toNat (s.gpr .r8).toNat := by
    funext P
    unfold Derive.bnd
    by_cases hq : (s.gpr .r8).toNat = 3 * (s.gpr .r9).toNat
    · rw [ite_eq_left hq, ite_eq_left hq, hsep _ _ fun i hi => by rw [off_off']; exact sepD _ (by omega)]
    · rw [ite_eq_right hq, ite_eq_right hq]
  have g23 : s₂.gpr .r23 = stackArg s 1 := hb2.r23
  have e2 : Env s₂ (stackArg s 1) ((stackArg s 2).toNat * 8) (((s.gpr .r9).toNat + 7) / 8) := hb2.env
  exact {
    env := e2
    h23 := g23
    h21 := hb2.r21
    h27 := hb2.r27
    h28 := hb2.r28
    hk := hk
    hk' := hk'
    hL := hL'
    hX := by show word s₂.mem _ 64 = _; rw [hw2 64 (by omega), w8]; simp [off]
    hXL := by show word s₂.mem _ 72 = _; rw [hw2 72 (by omega), w9, h4]
    hO := by show word s₂.mem _ 80 = _; rw [hw2 80 (by omega), w10]; simp [off]
    hR := by show word s₂.mem _ 88 = _; rw [hw2 88 (by omega), w11]; simp [off]
    hbw := by show word s₂.mem _ 8 = _; rw [hw2 8 (by omega), wc8]; exact cb
    hyw := by show word s₂.mem _ 16 = _; rw [hw2 16 (by omega), wc16]; exact cy
    hRw := by show word s₂.mem _ 24 = _; rw [hw2 24 (by omega), wc24]; exact cr
    hCw := by rw [show hCtx = 0 from rfl]; exact (hw2 0 (by omega)).trans wc0
    hc := ⟨by have := nwC; unfold ctxWords; omega, fun d hd => by
        rw [k12.rd, k12.wr]
        exact ⟨⟨stackArg s 3, (3 + 34 * (((s.gpr .r9).toNat + 7) / 8)) * 8⟩,
          List.mem_append_left _ (by rw [hrd]; simp),
          Offset.contains_base _ (by unfold ctxWords at hd; omega) (by unfold ctxWords at hd; omega)⟩,
      fun x hx => by
        have := Pub.sep_of_disjoint dSC.symm x (by
          simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs, ctxWords] at hx ⊢; omega)
        simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at this ⊢; omega⟩
    hsepCX := fun y hy => by
      have := Pub.sep_of_disjoint dXC.symm y (by
        simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs, ctxWords] at hy ⊢; omega)
      simp only [VG.Proof.Mont.ofs, VG.Proof.Bignum.ofs] at this ⊢; omega
    hents := cent
    hr2 := cr2
    hb1 := hbits.1
    hbk := hbits.2
    hrdD := hb2.rdD
    hsepD := sepD
    hrdR := by
      rw [k12.rd, k12.wr]
      exact rd_of_mem (s := s) (D := s.gpr .r10) (L := (s.gpr .r9).toNat) (by rw [hrd]; simp) (by omega)
    hx := Scr.of_mem (by rw [k12.wr, hwr]; simp) nwX
    hsepX := sep_of_disjoint dXS (by omega)
    hsepBX := Pub.sep_of_disjoint dXS.symm
    hsepRX := sep_of_disjoint dXR.symm (by omega)
    hsepDX := sep_of_disjoint dXD.symm (by omega)
    hsepXO := sep_of_disjoint dXY (by omega)
    hsepOX := sep_of_disjoint dXY.symm (by omega)
    ho := Scr.of_mem (by rw [k12.wr, hwr]; simp) nwY
    hsepO := Pub.sep_of_disjoint dYS
    hsepB := Pub.sep_of_disjoint dYS.symm
    hP := p2
    hp2 := hf.1
    hodd := hf.2
    hpk := hpk
    hv := by simp only [cgX]; rw [eR, eb, decide_eq_true_iff] }

end VG.Proof.Ffdh.PPC64LE.Cached
