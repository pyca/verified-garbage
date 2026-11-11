module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreA
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPowerA
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreR2
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: a factor's `R² mod p`

`primeA_ok`: as `vg_rsa_private_crt`'s `power` starts (`Crt.powerA_ok`), the
factor from `X`'s array `xj` into its working space's array 0,
`-p⁻¹ mod 2³²` and `R² mod p` into array 1 (`r2Fast_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE VG.Proof.Bignum.PPC64LE.Crt

/-- The registers `prime`'s head writes. -/
def primeRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r24, .r25, .r31]

/-- `prime`'s head: the factor into array 0, `-p⁻¹ mod 2³²`, and `R² mod p` from
`X`'s array 6 (`r2Fast`) under `G`. -/
theorem primeA_ok {s : State} {BX : Addr} {Z oA wA wX xj Pv W : Nat} {G : Prop} {c : Prog isa}
    {Q : State → Prop}
    (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8) (hwW : wA ≤ W) (hW' : W < 2 ^ 31) (hWX : wX = 2 * W)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wA 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hG : G → wv s.mem BX (slot wX 6) (wA * nChunks W wA) % Pv = 2 ^ (128 * W) % Pv)
    (hc : ∀ t, (G → val32 t.mem (off BX oA) (slot wA 1) (2 * wA) = 2 ^ (128 * wA) % Pv) →
      Outside BX oA (slot wA 24) s.mem t.mem → t.gpr .r10 = off (off BX oA) (slot wA 0) →
      t.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)) → t.gpr .r11 = BitVec.ofNat 64 (2 * wA) →
      Keep primeRegs s t → WP isa c t Q) :
    WP isa (.seq (.block (([.addi .r14 .r10 0] : List Instr) ++ xb .r15 xj)) (.seq copyN
      (.seq (.block (PublicChecked.minv ++ PublicChecked.base .r5 1 ++ PublicChecked.base .r8 2 ++
        PublicChecked.base .r9 3)) (.seq PrivPre.r2Fast c)))) s Q := by
  have hn' := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA0 := e wA 0; have eA1 := e wA 1; have eA4 := e wA 4; have eA8 := e wA 8; have eA24 := e wA 24
  have eX0 := e wX 0; have eX6 := e wX 6; have eX8 := e wX 8; have sXj := slot_le (w := wX) hxj
  have hsA := hs.sub hA
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14] (Q := fun t =>
    t.gpr .r14 = off BX (oA + slot wA 0) ∧ t.mem = s.mem) (by
      prun [h10, BitVec.add_zero, off_off]) rfl)
    fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) xj) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  -- The prime.
  refine WP.seq (WP.mono (copySub_ok (hs.congr k12.wr) a15 ((k2.gpr _ (by decide)).trans a14)
    ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun s₃ ⟨⟨hw3, out3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  rw [m2, m1] at hw3 out3
  have v0 : val32 s₃.mem (off BX oA) (slot wA 0) (2 * wA) = Pv := by
    rw [Pre.val32_eq_wv, wv_off, ← hP]; exact wv_congr2 fun i hi => hw3 i hi
  have hlow : (word s₃.mem (off BX oA) (slot wA 0)).toNat % 2 = 1 := by
    rw [← wv_low_mod2 _ _ _ (show 1 ≤ wA by omega_arith), ← Pre.val32_eq_wv, v0, hPodd]
  -- `-p⁻¹ mod 2³²` and the bases.
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.minv_ok (hsA.congr k13.wr) ((k13.gpr _ (by decide)).trans h10) (by omega_arith) hlow)
    fun s₄ ⟨⟨i12, iinv, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) 1) fun s₅ ⟨⟨a5, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k15.gpr _ (by decide)).trans h10)
    ((k15.gpr _ (by decide)).trans h29) 2) fun s₆ ⟨⟨a8, m6⟩, k6⟩ => ?_
  have k16 := k15.trans k6
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k16.gpr _ (by decide)).trans h10)
    ((k16.gpr _ (by decide)).trans h29) 3) fun s₇ ⟨⟨a9, m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  have hm7 : s₇.mem = s₃.mem := by rw [m7, m6, m5, m4]
  have g12 : s₇.gpr .r12 = s₄.gpr .r12 := by
    rw [k7.gpr .r12 (by decide), k6.gpr .r12 (by decide), k5.gpr .r12 (by decide)]
  -- `R² mod p`.
  have hK := nChunks_mul_lt (K := W) (w := wA) (by omega_arith) (by omega_arith)
  have hKw : wA * nChunks W wA < W + wA := by rw [Nat.mul_comm]; exact hK
  have out3' : Outside BX oA (slot wA 24) s.mem s₇.mem := by
    rw [hm7]; exact out3.mono (by omega_arith) (by omega_arith)
  refine WP.seq (WP.mono (r2Fast_ok (G := G) (W := W) (hs.congr k17.wr) hA hXA hw2 hw' hwW hW' hWX
    ((k17.gpr _ (by decide)).trans h10) ((k17.gpr _ (by decide)).trans h21) ((k17.gpr _ (by decide)).trans h29)
    ((k17.gpr _ (by decide)).trans h11) (by rw [g12]; exact i12) (by rw [g12, hm7]; exact iinv)
    ((k7.gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans a5))
    ((k17.gpr _ (by decide)).trans h27) ((k17.gpr _ (by decide)).trans h28)
    (by rw [hm7, v0]) hP2 hPodd
    (fun g => by rw [out3'.wv (Or.inl (by omega_arith)) (by omega_arith)]; exact hG g))
    fun s₈ ⟨⟨_, h1, out8, t10, t29, t11, _⟩, k8⟩ => ?_)
  exact hc s₈ (fun g => by rw [h1 g]) (out3'.trans out8) t10 t29 t11 ((k17.trans k8).mono (by decide))

theorem and_bmask (x : BitVec 64) (b : Bool) : x &&& Crt.bmask b = if b then x else 0 := by
  cases b
  · rw [show Crt.bmask false = 0#64 from rfl, BitVec.and_zero]; rfl
  · rw [show Crt.bmask true = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]; rfl

/-- The loop of `prime`'s end: the `w` words at `r15` (`d` in the working
space at `B`), and-ed with the mask of `b`, to `r30` (`o` in `pre` at `P`,
apart from the working space), both advanced past them. -/
theorem maskLoop_ok {s : State} {B P : Addr} {Z L d o w : Nat} {b : Bool} (hs : Scr s B Z)
    (hp : Scr s P L) (hsep : ∀ x, ofs P x < L → Z ≤ ofs B x)
    (h15 : s.gpr .r15 = off B d) (h30 : s.gpr .r30 = off P o) (h17 : s.gpr .r17 = BitVec.ofNat 64 w)
    (h26 : s.gpr .r26 = Crt.bmask b) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hd : d + 8 * w ≤ Z) (ho : o + 8 * w ≤ L) :
    WP isa (Precompute.countLoop .r17 [.load .d .r0 .r15 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r30 0,
      .addi .r15 .r15 8, .addi .r30 .r30 8]) s fun t =>
      ((∀ i < w, word t.mem P (o + 8 * i) = if b then word s.mem B (d + 8 * i) else 0) ∧
        t.gpr .r30 = off P (o + 8 * w) ∧ Outside P o (8 * w) s.mem t.mem) ∧ Keep [.r0, .r15, .r17, .r30] s t := by
  have hnB := hs.nowrap
  have hnP := hp.nowrap
  -- The working space's words are apart from `pre`'s.
  have keepB : ∀ {m m' : Mem} {o' n : Nat}, Outside P o' n m m' → o' + n ≤ L → ∀ e, e + 8 ≤ Z →
      word m' B e = word m B e := fun {m m' o' n} h hn e he => Mem.readW_congr fun i hi => h _ (by
    by_contra hc
    have hc' : ofs P (off B e + BitVec.ofNat 64 i) < L := by simp only [ofs] at hc ⊢; omega_arith
    have := hsep _ hc'
    rw [ofs, Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)] at this
    omega_arith)
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r15 = off B (d + 8 * i) ∧ t.gpr .r30 = off P (o + 8 * i) ∧ t.gpr .r26 = Crt.bmask b ∧
      (∀ j < i, word t.mem P (o + 8 * j) = if b then word s.mem B (d + 8 * j) else 0) ∧
      Outside P o (8 * i) s.mem t.mem ∧ Keep [.r0, .r15, .r17, .r30] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r15 0, .logic .and .r0 .r0 .r26,
      .store .d .r0 .r30 0, .addi .r15 .r15 8, .addi .r30 .r30 8] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j15, j30, j26, jw, jout, jk⟩ _ => ?_)
    ⟨by rw [h15]; rfl, by rw [h30]; rfl, h26, fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _,
      (Keep.refl [] s).mono (by decide)⟩ h17)
    fun t ⟨_, t30, _, tw, tout, tk⟩ => ⟨⟨tw, t30, tout⟩, tk⟩
  have hst : WP isa (.block [.load .d .r0 .r15 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r30 0,
      .addi .r15 .r15 8, .addi .r30 .r30 8, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r15 = off B (d + 8 * i + 8) ∧ t'.gpr .r30 = off P (o + 8 * i + 8) ∧
        t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off P (o + 8 * i)) (word t.mem B (d + 8 * i) &&& Crt.bmask b)) ∧
      Keep [.r0, .r15, .r17, .r30] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j15, j30, j26, (hs.congr jk.wr).ld (show d + 8 * i + 8 ≤ Z by omega_arith),
      (hp.congr jk.wr).st (show o + 8 * i + 8 ≤ L by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l15, l30, l17, lm⟩, lk⟩ => ⟨⟨?_, ?_, (lk.gpr _ (by decide)).trans j26, fun j hj => ?_,
    ?_, jk.trans' lk⟩, l17⟩
  · rw [l15, show d + 8 * i + 8 = d + 8 * (i + 1) by omega_arith]
  · rw [l30, show o + 8 * i + 8 = o + 8 * (i + 1) by omega_arith]
  · have wB : word t.mem B (d + 8 * i) = word s.mem B (d + 8 * i) :=
      keepB jout (by omega_arith) _ (by omega_arith)
    rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [(writeW_outside t.mem P (d := o + 8 * i) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
        jw j hj]
    · rw [word_writeW_self, wB, and_bmask]
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ P (d := o + 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- An address not in the region at `B + o` of `n` bytes is outside those
offsets. -/
theorem out_of_not {B y : Addr} {o n : Nat} (h : ¬ (⟨off B o, n⟩ : Region).Contains y 1) (ho : o < 2 ^ 64) :
    ofs B y < o ∨ o + n ≤ ofs B y := by
  simp only [Region.Contains, off] at h
  simp only [ofs]
  have h1 := (y - B).isLt
  have e1 : (y - B).toNat = (2 ^ 64 - B.toNat + y.toNat) % 2 ^ 64 := BitVec.toNat_sub _ _
  have e2 : (y - (B + BitVec.ofNat 64 o)).toNat = (2 ^ 64 - (B.toNat + o) % 2 ^ 64 + y.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 from ho)]
  rw [e2] at h
  rw [e1]
  have := B.isLt; have := y.isLt
  omega_arith

/-- The words of `prime`'s result: `R² mod p`'s, or zeros. -/
abbrev r2Word (b : Bool) (w Pv i : Nat) : BitVec 64 :=
  if b then BitVec.ofNat 64 (2 ^ (128 * w) % Pv / 2 ^ (64 * i)) else 0

/-- The registers `prime` writes. -/
def primeAllRegs : List Reg := primeRegs ++ [.r0, .r15, .r17, .r30]

/-- `prime xj`: for the factor `Pv` in `X`'s array `xj`, its working space
at `off BX oA` (set up), the mask of `b` in `r26`: `R² mod Pv`'s `w_A` words,
or zeros, to `pre` at `P + o` (`r30`), which is advanced past them; only
those words and the working space changed. -/
theorem prime_ok {s : State} {BX P : Addr} {Z L oA wA wX xj Pv o W : Nat} {b : Bool}
    (hs : Scr s BX Z) (hp : Scr s P L) (hsep : ∀ x, ofs P x < L → Z ≤ ofs BX x)
    (hA : oA + slot wA 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ wA) (hw' : wA < 2 ^ 31)
    (hwx : wA ≤ wX) (hxj : xj < 8) (hwW : wA ≤ W) (hW' : W < 2 ^ 31) (hWX : wX = 2 * W)
    (h10 : s.gpr .r10 = off (off BX oA) (slot wA 0)) (h21 : s.gpr .r21 = off (off BX oA) (slot wA 0))
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (wA + 2)))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wA))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (h30 : s.gpr .r30 = off P o) (h26 : s.gpr .r26 = Crt.bmask b) (ho : o + 8 * wA ≤ L)
    (hP : wv s.mem BX (slot wX xj) wA = Pv) (hP2 : 2 ≤ Pv) (hPodd : Pv % 2 = 1)
    (hG : b = true → wv s.mem BX (slot wX 6) (wA * nChunks W wA) % Pv = 2 ^ (128 * W) % Pv) :
    WP isa (PrivPre.prime xj) s fun t =>
      ((∀ i < wA, word t.mem P (o + 8 * i) = r2Word b wA Pv i) ∧ t.gpr .r30 = off P (o + 8 * wA) ∧
        Frame [⟨off P o, 8 * wA⟩, ⟨off BX oA, slot wA 24⟩] s.mem t.mem) ∧
      Keep primeAllRegs s t := by
  have hnB := hs.nowrap
  have hnP := hp.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA1 := e wA 1; have eA24 := e wA 24
  unfold PrivPre.prime
  refine primeA_ok (G := b = true) hs hA hXA hw2 hw' hwx hxj hwW hW' hWX h10 h21 h29 h11 h27 h28 hP hP2 hPodd hG
    fun t h1 out t10 t29 t11 kt => ?_
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) t10 t29 1) fun u ⟨⟨u15, um⟩, uk⟩ => ?_
  refine WP.mono (WP.keep [.r17] (Q := fun v => v.gpr .r17 = BitVec.ofNat 64 wA ∧ v.mem = u.mem ∧
      v.gpr .r15 = u.gpr .r15) (by
        prun [(uk.gpr _ (by decide)).trans t11, mont_ofNat_shr1 (show wA < 2 ^ 63 by omega_arith)]) rfl)
    fun v ⟨⟨v17, vm, v15⟩, vk⟩ => ?_
  have kv := (kt.trans uk).trans vk
  have hm : v.mem = t.mem := vm.trans um
  refine WP.mono (maskLoop_ok (b := b) (d := oA + slot wA 1) (o := o) (w := wA) (hs.congr kv.wr) (hp.congr kv.wr) hsep
    (by rw [v15, u15, off_off]) (by rw [kv.gpr _ (by decide)]; exact h30) v17
    (by rw [kv.gpr _ (by decide)]; exact h26) (by omega_arith) hw' (by omega_arith) ho)
    fun x ⟨⟨xw, x30, xo⟩, xk⟩ => ⟨⟨fun i hi => ?_, x30, fun y hy => ?_⟩, (kv.trans xk).mono (by decide)⟩
  · rw [xw i hi, hm]
    unfold r2Word
    split
    next hb =>
      apply BitVec.eq_of_toNat_eq
      have hw := word_of_wv t.mem (off BX oA) (slot wA 1) wA hi
      rw [← Pre.val32_eq_wv, h1 hb] at hw
      rw [show oA + slot wA 1 + 8 * i = oA + (slot wA 1 + 8 * i) by omega_arith,
        show word t.mem BX (oA + (slot wA 1 + 8 * i)) = word t.mem (off BX oA) (slot wA 1 + 8 * i) by
          simp only [word]; rw [off_off], BitVec.toNat_ofNat]
      exact hw
    next => rfl
  · have y1 := out_of_not (hy _ (List.mem_cons_self ..)) (by omega_arith)
    have y2 := out_of_not (hy _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))) (by omega_arith)
    rw [xo y y1, hm, out y y2]


end VG.Proof.Bignum.PPC64LE.PrivPre
