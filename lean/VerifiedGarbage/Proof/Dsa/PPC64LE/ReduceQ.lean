module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtReduce
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtRecP2
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtAdd

/-!
# DSA on PPC64LE: a number modulo q by Montgomery multiplications

`Verify.reduceQ` is `Crt.reduceIn`'s algorithm in the Q space, whose array 0
`Verify.chunkStepQ` takes from `r23` (`Crt.chunkStep` takes it from `r21`,
which holds `S` in DSA's code):

* `recQa_ok` and `chunkStepQ_ok`: `Crt.recP2a_ok` and `Crt.chunkStep_ok`
  for `chunkStepQ`, one chunk of 4 words;
* `reduceQ_ok`: `c mod q` into array 4, for `c` at `r30` (`r31` words), as
  `Crt.reduceIn_ok`;
* `vModQ_ok`: `v mod q`, for `v` in the P space's array 6.
-/

@[expose] public section

-- In `Crt`'s namespace, as `Crt.reduceIn_ok`, whose proof this follows.
namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE

/-- `recP2a_ok` for `Verify.chunkStepQ`'s middle, which takes array 0 from `r23`:
`(m₁ + p - b) mod p` into array 3, changing only arrays 3 and 4. -/
theorem recQa_ok {s : State} {B : Addr} {Z w Pv m1 b bj : Nat} {c : Prog isa} {Q : State → Prop}
    (hs : Scr s B Z) (hZ : slot w 8 ≤ Z) (hbj : bj < 8) (hbj3 : bj ≠ 3) (hbj4 : bj ≠ 4) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (h10 : s.gpr .r10 = off B (slot w 0)) (h23 : s.gpr .r23 = B)
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (hP : val32 s.mem B (slot w 0) (2 * w) = Pv) (hb : val32 s.mem B (slot w bj) (2 * w) = b)
    (hm1 : val32 s.mem B (slot w 4) (2 * w) = m1) (hbP : b < Pv) (hm1P : m1 < Pv)
    (hc : ∀ t, val32 t.mem B (slot w 3) (2 * w) = (m1 + Pv - b) % Pv →
      Outs B [(slot w 3, 8 * (w + 2)), (slot w 4, 8 * (w + 2))] s.mem t.mem →
      t.gpr .r10 = off B (slot w 0) → Keep [.r0, .r3, .r8, .r9, .r10, .r14, .r15, .r16, .r17, .r20, .r24] s t → WP isa c t Q) :
    WP isa (.seq (.block (PublicChecked.base .r14 4 ++ ([.add .r14 .r14 .r29, .subi .r14 .r14 16, .li .r0 0,
      .store .d .r0 .r14 0] : List Instr) ++ PublicChecked.base .r8 4 ++ PublicChecked.base .r9 3 ++
      PublicChecked.base .r10 bj)) (.seq subMod (.seq (.block (([.addi .r10 .r23 hdrBytes] : List Instr) ++
      PublicChecked.base .r15 3 ++ PublicChecked.base .r16 0)) (.seq addMask c)))) s Q := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e bj; have e1' : slot w bj + 8 * (w + 2) ≤ slot w 8 := by
    simp only [e]; have := Nat.mul_le_mul_right (8 * (w + 2)) (show bj + 1 ≤ 8 by omega_arith); rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
  have e1'' : bj < 3 ∨ 4 < bj := by omega_arith
  have e1s : slot w bj + 8 * (w + 2) ≤ slot w 3 ∨ slot w 4 + 8 * (w + 2) ≤ slot w bj := by
    rcases e1'' with h | h
    · left; simp only [e]; have := Nat.mul_le_mul_right (8 * (w + 2)) (show bj + 1 ≤ 3 by omega_arith); rw [Nat.add_mul, Nat.one_mul] at this; omega_arith
    · right; simp only [e]; have := Nat.mul_le_mul_right (8 * (w + 2)) (show 5 ≤ bj by omega_arith); omega_arith
  have e3 := e 3; have e4 := e 4; have e8 := e 8
  have hh : hdrBytes = 256 := rfl
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 4) fun s₁ ⟨⟨a14, m1'⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r14, .r0] (Q := fun t =>
    t.mem = s₁.mem.writeW (off B (slot w 4 + 8 * w)) (0 : BitVec 64)) ?_ (by decide)) fun s₂ ⟨m2', k2⟩ => ?_
  · have e16 : off B (slot w 4 + 8 * (w + 2)) - BitVec.ofNat 64 16 = off B (slot w 4 + 8 * w) := by
      rw [off, VG.Offset.add_ofNat_sub B (show 16 ≤ slot w 4 + 8 * (w + 2) by omega_arith)]; congr 2
    prun [a14, (k1.gpr .r29 (by decide)).trans h29, off_add, e16,
      (hs.congr k1.wr).st (show slot w 4 + 8 * w + 8 ≤ Z by omega_arith)]
    rfl
  have k12 := k1.trans k2
  rw [m1'] at m2'
  have ow := writeW_outside s.mem B (d := slot w 4 + 8 * w) (0 : BitVec 64) (by omega_arith)
  have ow' : Mont.Outside B (slot w 4 + 8 * w) 8 s.mem s₂.mem := by rw [m2']; exact fun x hx => ow x hx
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r8) (by decide) (by decide) ((k12.gpr _ (by decide)).trans h10)
    ((k12.gpr _ (by decide)).trans h29) 4) fun s₃ ⟨⟨a8, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h10)
    ((k13.gpr _ (by decide)).trans h29) 3) fun s₄ ⟨⟨a9, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (Pub.base_ok (rd := .r10) (by decide) (by decide) ((k14.gpr _ (by decide)).trans h10)
    ((k14.gpr _ (by decide)).trans h29) bj) fun s₅ ⟨⟨a10, m5⟩, k5⟩ => ?_
  have k15 := k14.trans k5
  have hm5 : s₅.mem = s₂.mem := by rw [m5, m4, m3]
  refine WP.seq (WP.mono (subMod_ok (n := 2 * w) (dA := slot w 4) (dT := slot w 3) (dM := slot w bj)
    (hs.congr k15.wr) ((k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans a8))
    ((k5.gpr _ (by decide)).trans a9) a10
    ((k15.gpr _ (by decide)).trans h11) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₆ ⟨⟨cc, hcc, hD, h20⟩, out6, k6⟩ => ?_)
  have k16 := k15.trans k6
  rw [hm5] at hD h20 out6
  have v1 : val32 s₂.mem B (slot w bj) (2 * w) = b := by rw [ow'.val32 (by omega_arith) (by omega_arith), hb]
  have v4 : val32 s₂.mem B (slot w 4) (2 * w) = m1 := by rw [ow'.val32 (Or.inl (by omega_arith)) (by omega_arith), hm1]
  have v0 : val32 s₂.mem B (slot w 0) (2 * w) = Pv := by rw [ow'.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  have h0 : w32 s₂.mem B (slot w 4 + 4 * (2 * w)) = 0 := by
    have := word_eq_w32 s₂.mem B (slot w 4 + 8 * w)
    rw [show Mont.word s₂.mem B (slot w 4 + 8 * w) = 0 by rw [m2']; exact word_writeW_self _ _ _ _,
      show (0 : BitVec 64).toNat = 0 from rfl, show slot w 4 + 8 * w = slot w 4 + 4 * (2 * w) by omega_arith] at this
    omega_arith
  rw [v1, v4] at hD
  rw [h0] at h20
  have out6' : Mont.Outside B (slot w 3) (4 * (2 * w)) s₂.mem s₆.mem := fun x hx => out6 x hx
  have v0' : val32 s₆.mem B (slot w 0) (2 * w) = Pv := by rw [out6'.val32 (Or.inl (by omega_arith)) (by omega_arith), v0]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r10] (Q := fun t => t.gpr .r10 = off B (slot w 0) ∧ t.mem = s₆.mem)
    (by prun [(k16.gpr .r23 (by decide)).trans h23, hdrBytes]; rw [off, show slot w 0 = 256 by unfold slot; omega_arith]) (by decide)) fun s₇ ⟨⟨a10', m7⟩, k7⟩ => ?_
  have k17 := k16.trans k7
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) a10' ((k17.gpr _ (by decide)).trans h29) 3)
    fun s₈ ⟨⟨a15, m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r16) (by decide) (by decide) ((k8.gpr _ (by decide)).trans a10')
    (((k17.trans k8).gpr _ (by decide)).trans h29) 0) fun s₉ ⟨⟨a16, m9⟩, k9⟩ => ?_
  have k19 := (k17.trans k8).trans k9
  have hm9 : s₉.mem = s₆.mem := by rw [m9, m8, m7]
  refine WP.seq (WP.mono (addMask_ok (b := decide (0 < cc)) (n := 2 * w) (dT := slot w 3) (dM := slot w 0)
    (hs.congr k19.wr) ((k9.gpr _ (by decide)).trans a15) a16 ((k19.gpr _ (by decide)).trans h11)
    (by rw [k9.gpr _ (by decide), k8.gpr _ (by decide), k7.gpr _ (by decide), h20]; simp only [decide_eq_true_eq])
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨hT, outT, kT⟩ => ?_)
  rw [hm9, v0'] at hT
  rw [hm9] at outT
  have hval : val32 t.mem B (slot w 3) (2 * w) = (m1 + Pv - b) % Pv := by
    refine subAdd_val hm1P hbP (by rw [← v0]; exact val32_lt _ _ _ _) hcc (val32_lt _ _ _ _) hD ?_
    rw [hT]; simp only [decide_eq_true_eq]
  refine hc t hval ?_ ((kT.gpr _ (by decide)).trans ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a10')))
    (k19.trans kT).mono
  intro x hx
  have h3 := hx _ (List.mem_cons_self ..)
  have h4 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h3' : ofs B x < slot w 3 ∨ slot w 3 + 8 * (w + 2) ≤ ofs B x := h3
  have h4' : ofs B x < slot w 4 ∨ slot w 4 + 8 * (w + 2) ≤ ofs B x := h4
  rw [outT x (by omega_arith), out6 x (by omega_arith), m2', ow x (by omega_arith)]

/-- Between the chunks of `reduceIn`, after `i` of them: in `p`'s working space
`off BX oA` of `w` words, `p` (`Pv`), `R² mod p` (`R2`), `p - 1`,
`q ≡ -R^(i+1)` in array 5 and `S ≡` the first `w i` words of `X`'s array 6 in
array 4; the next chunk at `r30`, the words left in `r31`. -/
structure ChunkQ (s : State) (BX : Addr) (Z oA w wX K Pv R2 i : Nat) (t : State) : Prop where
  scr : Scr t BX Z
  r10 : t.gpr .r10 = off (off BX oA) (slot w 0)
  r23 : t.gpr .r23 = off BX oA
  r29 : t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))
  r11 : t.gpr .r11 = BitVec.ofNat 64 (2 * w)
  r12 : (t.gpr .r12).toNat < 2 ^ 32
  inv : (w32 t.mem (off BX oA) (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0
  r30 : t.gpr .r30 = off BX (slot wX 6 + 8 * (w * i))
  r31 : t.gpr .r31 = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * i)
  p0 : val32 t.mem (off BX oA) (slot w 0) (2 * w) = Pv
  p1 : val32 t.mem (off BX oA) (slot w 1) (2 * w) = R2
  p8 : val32 t.mem (off BX oA) (slot w 8) (2 * w) = Pv - 1
  qlt : val32 t.mem (off BX oA) (slot w 5) (2 * w) < Pv
  q : (val32 t.mem (off BX oA) (slot w 5) (2 * w) + (2 ^ (64 * w)) ^ (i + 1)) % Pv = 0
  slt : val32 t.mem (off BX oA) (slot w 4) (2 * w) < Pv
  sv : val32 t.mem (off BX oA) (slot w 4) (2 * w) % Pv = wv s.mem BX (slot wX 6) (w * i) % Pv
  out : Outside BX oA (slot w 24) s.mem t.mem
  keep : Keep chunkRegs s t

/-- One chunk of `Verify.chunkStepQ`, as `chunkStep_ok`. -/
theorem chunkStepQ_ok {s t : State} {BX : Addr} {Z oA w wX K Pv R2 i : Nat}
    (hA : oA + slot w 24 ≤ Z) (hX : slot wX 6 + 8 * (w * nChunks K w) ≤ oA) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hK : 1 ≤ K) (hK' : K < 2 ^ 40) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1) (hR2 : R2 < Pv)
    (hR2' : R2 % Pv = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv) (hi : i < nChunks K w)
    (I : ChunkQ s BX Z oA w wX K Pv R2 i t) :
    WP isa Verify.chunkStepQ t fun u => ChunkQ s BX Z oA w wX K Pv R2 (i + 1) u ∧
      ((u.gpr .r3).toNat ≠ 0 ↔ i + 1 ≠ nChunks K w) := by
  have hn := I.scr.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5
  have e6 := e 6; have e7 := e 7; have e8 := e 8; have e9 := e 9; have e24 := e 24
  have eX6 : slot wX 6 = 256 + 6 * (8 * (wX + 2)) := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hwi : w * i + w ≤ w * nChunks K w := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have hsA := I.scr.sub hA
  -- The chunk into array 6, and `r30` past it.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) I.r10 I.r29 6) fun t₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15] (Q := fun u => u.gpr .r15 = t₁.gpr .r30 ∧ u.mem = t₁.mem) (by prun [BitVec.add_zero])
    (by decide)) fun t₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copyAdv_ok (a := slot wX 6 + 8 * (w * i)) (b := oA + slot w 6) (w := w) (I.scr.congr k12.wr)
    (by rw [a15, (k1.gpr _ (by decide)).trans I.r30]) (by rw [k2.gpr _ (by decide), a14, off_off])
    ((k12.gpr _ (by decide)).trans I.r11) (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t₃ ⟨⟨c3, o3, a15'⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (mv30_ok t₃) fun t₄ ⟨⟨a30, m4⟩, k4⟩ => ?_)
  have k14 := (k12.trans k3).trans k4
  have hm2 : t₂.mem = t.mem := by rw [m2, m1]
  rw [hm2] at c3 o3
  have o3' : Mont.Outside (off BX oA) (slot w 6) (8 * w) t.mem t₄.mem := by
    rw [m4]; exact out_rebase o3 (by omega_arith)
  have W4 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t.mem t₄.mem := o3'.mono (by omega_arith) (by omega_arith)
  -- The chunk's value.
  let C := wv s.mem BX (slot wX 6 + 8 * (w * i)) w
  have v6 : val32 t₄.mem (off BX oA) (slot w 6) (2 * w) = C := by
    rw [Pre.val32_eq_wv, wv_off, m4, wv_congr2 fun j hj => c3 j hj]
    exact I.out.wv (Or.inl (by omega_arith)) (by omega_arith)
  have v0 : val32 t₄.mem (off BX oA) (slot w 0) (2 * w) = Pv := by
    rw [W4.val32 (Or.inl (by omega_arith)) (by omega_arith), I.p0]
  have v1 : val32 t₄.mem (off BX oA) (slot w 1) (2 * w) = R2 := by
    rw [W4.val32 (Or.inl (by omega_arith)) (by omega_arith), I.p1]
  have v8 : val32 t₄.mem (off BX oA) (slot w 8) (2 * w) = Pv - 1 := by
    rw [W4.val32 (Or.inr (by omega_arith)) (by omega_arith), I.p8]
  have v5 : val32 t₄.mem (off BX oA) (slot w 5) (2 * w) = val32 t.mem (off BX oA) (slot w 5) (2 * w) :=
    o3'.val32 (Or.inl (by omega_arith)) (by omega_arith)
  have v4 : val32 t₄.mem (off BX oA) (slot w 4) (2 * w) = val32 t.mem (off BX oA) (slot w 4) (2 * w) :=
    o3'.val32 (Or.inl (by omega_arith)) (by omega_arith)
  have w0 : w32 t₄.mem (off BX oA) (slot w 0) = w32 t.mem (off BX oA) (slot w 0) :=
    W4.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have g : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r29, .r31], t₄.gpr r = t.gpr r := fun r hr =>
    k14.gpr r (by revert r hr; decide)
  -- `T := C q R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 7) (a := 6) (b := 5) (hsA.congr k14.wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g .r10 (by decide)).trans I.r10) ((g .r29 (by decide)).trans I.r29) ((g .r11 (by decide)).trans I.r11)
    (by rw [g .r12 (by decide)]; exact I.r12) (by rw [g .r12 (by decide), w0]; exact I.inv)
    (by rw [v5, v0]; exact I.qlt)) fun t₅ ⟨⟨T5, T5e, o5⟩, k5⟩ => ?_)
  rw [v0, v6, v5] at T5e
  rw [v0] at T5
  have W5 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₄.mem t₅.mem :=
    outs_work o5 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have u5 : ∀ j, j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 8 →
      val32 t₅.mem (off BX oA) (slot w j) (2 * w) = val32 t₄.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o5 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have w0' : w32 t₅.mem (off BX oA) (slot w 0) = w32 t.mem (off BX oA) (slot w 0) := by
    rw [W5.w32 (Or.inl (by omega_arith)) (by omega_arith), w0]
  have g5 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r29, .r30, .r31], t₅.gpr r = t₄.gpr r := fun r hr =>
    k5.gpr r (by revert r hr; decide)
  -- `q := q R² R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 5) (a := 5) (b := 1) (hsA.congr (k14.trans k5).wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g5 .r10 (by decide)).trans ((g .r10 (by decide)).trans I.r10))
    ((g5 .r29 (by decide)).trans ((g .r29 (by decide)).trans I.r29))
    ((g5 .r11 (by decide)).trans ((g .r11 (by decide)).trans I.r11))
    (by rw [g5 .r12 (by decide), g .r12 (by decide)]; exact I.r12)
    (by rw [g5 .r12 (by decide), g .r12 (by decide), w0']; exact I.inv)
    (by rw [u5 1 (by decide), u5 0 (by decide), v1, v0]; exact hR2)) fun t₆ ⟨⟨Q6, Q6e, o6⟩, k6⟩ => ?_)
  rw [u5 0 (by decide), v0, u5 5 (by decide), v5, u5 1 (by decide), v1] at Q6e
  rw [u5 0 (by decide), v0] at Q6
  have W6 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₅.mem t₆.mem :=
    outs_work o6 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have u6 : ∀ j, j = 0 ∨ j = 1 ∨ j = 4 ∨ j = 6 ∨ j = 7 ∨ j = 8 →
      val32 t₆.mem (off BX oA) (slot w j) (2 * w) = val32 t₅.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o6 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have g6 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r29, .r31], t₆.gpr r = t.gpr r := fun r hr => by
    rw [k6.gpr r (by revert r hr; decide), g5 r (by revert r hr; decide), g r (by revert r hr; decide)]
  have k16 := (k14.trans k5).trans k6
  have b30 : t₆.gpr .r30 = off BX (slot wX 6 + 8 * (w * i) + 8 * w) := by
    rw [k6.gpr .r30 (by decide), g5 .r30 (by decide), a30, a15']
  have hS6 : val32 t₆.mem (off BX oA) (slot w 4) (2 * w) = val32 t.mem (off BX oA) (slot w 4) (2 * w) := by
    rw [u6 4 (by decide), u5 4 (by decide), v4]
  have hT6 : val32 t₆.mem (off BX oA) (slot w 7) (2 * w) = val32 t₅.mem (off BX oA) (slot w 7) (2 * w) :=
    u6 7 (by decide)
  -- `S - T mod p` into array 3.
  refine recQa_ok (bj := 7) (hsA.congr k16.wr) (by omega_arith) (by decide) (by decide) (by decide) hw2 hw'
    ((g6 .r10 (by decide)).trans I.r10) ((g6 .r23 (by decide)).trans I.r23) ((g6 .r29 (by decide)).trans I.r29)
    ((g6 .r11 (by decide)).trans I.r11) (by rw [u6 0 (by decide), u5 0 (by decide), v0]) hT6 hS6 T5 I.slt
    fun t₇ v3 o7 a10 k7 => ?_
  have hsA7 := hsA.congr (k16.trans k7).wr
  have W7 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₆.mem t₇.mem :=
    outs_work o7 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp only [e] <;> omega_arith)
  -- Back into array 4.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) a10 ((k7.gpr _ (by decide)).trans
    ((g6 .r29 (by decide)).trans I.r29)) 4) fun t₈ ⟨⟨a14', m8⟩, k8⟩ => ?_
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) ((k8.gpr _ (by decide)).trans a10)
    ((k8.gpr _ (by decide)).trans ((k7.gpr _ (by decide)).trans ((g6 .r29 (by decide)).trans I.r29))) 3)
    fun t₉ ⟨⟨a15'', m9⟩, k9⟩ => ?_
  have k79 := (k7.trans k8).trans k9
  have r11_9 : t₉.gpr .r11 = BitVec.ofNat 64 (2 * w) := by
    rw [k79.gpr .r11 (by decide), g6 .r11 (by decide), I.r11]
  refine WP.seq (WP.mono (copySub_ok (a := slot w 3) (b := slot w 4) (w := w) (hsA7.congr (k8.trans k9).wr) a15''
    ((k9.gpr _ (by decide)).trans a14') r11_9 (by omega_arith) hw' (by omega_arith) (by omega_arith) (by omega_arith))
    fun t₁₀ ⟨⟨c10, o10⟩, k10⟩ => ?_)
  have hm9 : t₉.mem = t₇.mem := by rw [m9, m8]
  rw [hm9] at c10 o10
  refine WP.mono (tick_ok (t := t₁₀) ((k10.gpr _ (by decide)).trans r11_9) (by omega_arith)) fun u ⟨⟨b31, b3, mu⟩, ku⟩ => ?_
  have kall := (((k16.trans k79).trans k10).trans ku)
  have o10' : Mont.Outside (off BX oA) (slot w 4) (8 * w) t₇.mem u.mem := by rw [mu]; exact o10
  have W10 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t₇.mem u.mem := o10'.mono (by omega_arith) (by omega_arith)
  have Wt : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) t.mem u.mem :=
    ((W4.trans W5).trans (W6.trans W7)).trans W10
  have gu : ∀ r ∈ [Reg.r11, .r12, .r21, .r23, .r29], u.gpr r = t.gpr r := fun r hr => by
    rw [ku.gpr r (by revert r hr; decide), k10.gpr r (by revert r hr; decide), k79.gpr r (by revert r hr; decide),
      g6 r (by revert r hr; decide)]
  -- The values.
  have s4 : val32 u.mem (off BX oA) (slot w 4) (2 * w) = (val32 t.mem (off BX oA) (slot w 4) (2 * w) + Pv -
      val32 t₅.mem (off BX oA) (slot w 7) (2 * w)) % Pv := by
    rw [mu, Pre.val32_eq_wv, wv_congr2 fun j hj => c10 j hj, ← Pre.val32_eq_wv, v3]
  have q5 : val32 u.mem (off BX oA) (slot w 5) (2 * w) = val32 t₆.mem (off BX oA) (slot w 5) (2 * w) := by
    rw [o10'.val32 (Or.inr (by omega_arith)) (by omega_arith)]
    exact outs_val32 o7 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> simp only [e] <;> omega_arith)
      (by omega_arith)
  have hTC := chunk_t hR T5e I.q
  have hwi1 : w * (i + 1) = w * i + w := Nat.mul_succ _ _
  have hpow : (2 ^ (64 * w)) ^ i = 2 ^ (64 * (w * i)) := by rw [← Nat.pow_mul, Nat.mul_assoc]
  refine ⟨⟨I.scr.congr kall.wr, ?_, by rw [gu .r23 (by decide)]; exact I.r23,
    by rw [gu .r29 (by decide)]; exact I.r29, by rw [gu .r11 (by decide)]; exact I.r11,
    by rw [gu .r12 (by decide)]; exact I.r12,
    by rw [gu .r12 (by decide), Wt.w32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.inv, ?_, ?_,
    by rw [Wt.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.p0,
    by rw [Wt.val32 (Or.inl (by omega_arith)) (by omega_arith)]; exact I.p1,
    by rw [Wt.val32 (Or.inr (by omega_arith)) (by omega_arith)]; exact I.p8,
    by rw [q5]; exact Q6, by rw [q5]; exact chunk_q hR Q6e hR2' I.q,
    by rw [s4]; exact Nat.mod_lt _ (by omega_arith), ?_,
    I.out.trans (out_sub (fun x hx => Wt x hx) (by omega_arith) (by omega_arith) (by omega_arith)),
    (I.keep.trans kall).mono (by decide +kernel)⟩, ?_⟩
  · rw [ku.gpr .r10 (by decide), k10.gpr .r10 (by decide), k9.gpr .r10 (by decide), k8.gpr .r10 (by decide), a10]
  · rw [ku.gpr .r30 (by decide), k10.gpr .r30 (by decide), k79.gpr .r30 (by decide), b30, hwi1, Nat.mul_add,
      Nat.add_assoc]
  · rw [b31, k10.gpr .r31 (by decide), k79.gpr .r31 (by decide), g6 .r31 (by decide), I.r31, hwi1]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega_arith
  · rw [s4]
    refine (chunk_s T5 I.sv hTC rfl).trans ?_
    rw [hwi1, wv_add, ← hpow]
  · have hx : t₁₀.gpr .r31 - BitVec.ofNat 64 w = BitVec.ofNat 64 K - BitVec.ofNat 64 (w * (i + 1)) := by
      rw [k10.gpr .r31 (by decide), k79.gpr .r31 (by decide), g6 .r31 (by decide), I.r31, hwi1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega_arith
    rw [b3, flag_ne_zero, hx]
    exact flag_iff (by omega_arith) hK hK' (by omega_arith) hi

/-- `Verify.reduceQ`, in the working space `off BX oA` of `w` words, for `c` the
first `w n` words of `BX`'s array 6 (`n` chunks of `K` words, at `r30`, `K` in
`r31`): `c mod q` into array 4, changing only arrays 2–8. -/
theorem reduceQ_ok {s : State} {BX : Addr} {Z oA w wX K Pv Cv : Nat}
    (hs : Scr s BX Z) (hA : oA + slot w 24 ≤ Z) (hXA : slot wX 8 ≤ oA) (hw2 : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hn : w * nChunks K w ≤ wX) (hK1 : 1 ≤ K) (hK' : K < 2 ^ 40)
    (h10 : s.gpr .r10 = off (off BX oA) (slot w 0)) (h23 : s.gpr .r23 = off BX oA)
    (h29 : s.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2))) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w))
    (h30 : s.gpr .r30 = off BX (slot wX 6)) (h31 : s.gpr .r31 = BitVec.ofNat 64 K)
    (h12 : (s.gpr .r12).toNat < 2 ^ 32)
    (hinv : (w32 s.mem (off BX oA) (slot w 0) * (s.gpr .r12).toNat + 1) % 2 ^ 32 = 0)
    (hP : val32 s.mem (off BX oA) (slot w 0) (2 * w) = Pv) (hP2 : 2 ≤ Pv) (hodd : Pv % 2 = 1)
    (hR2 : val32 s.mem (off BX oA) (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv)
    (hC : wv s.mem BX (slot wX 6) (w * nChunks K w) = Cv) :
    WP isa Verify.reduceQ s fun t =>
      (val32 t.mem (off BX oA) (slot w 4) (2 * w) = Cv % Pv ∧ val32 t.mem (off BX oA) (slot w 0) (2 * w) = Pv ∧
        val32 t.mem (off BX oA) (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv ∧ (t.gpr .r12).toNat < 2 ^ 32 ∧
        (w32 t.mem (off BX oA) (slot w 0) * (t.gpr .r12).toNat + 1) % 2 ^ 32 = 0 ∧
        Outside BX oA (slot w 24) s.mem t.mem ∧ t.gpr .r10 = off (off BX oA) (slot w 0)) ∧ Keep chunkRegs s t := by
  have hn' := hs.nowrap
  have e : ∀ j, slot w j = 256 + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e2 := e 2; have e4 := e 4; have e5 := e 5; have e8 := e 8
  have e9 := e 9; have e24 := e 24
  have eX6 : slot wX 6 = 256 + 6 * (8 * (wX + 2)) := rfl
  have eX8 : slot wX 8 = 256 + 8 * (8 * (wX + 2)) := rfl
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hsA := hs.sub hA
  have hX : slot wX 6 + 8 * (w * nChunks K w) ≤ oA := by omega_arith
  -- `p` into array 8.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) h10 h29 8) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_
  refine WP.mono (WP.keep [.r15] (Q := fun u => u.gpr .r15 = off (off BX oA) (slot w 0) ∧ u.mem = s₁.mem)
    (by prun [(k1.gpr .r10 (by decide)).trans h10, BitVec.add_zero]) (by decide)) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  refine WP.seq (WP.mono (copySub_ok (a := slot w 0) (b := slot w 8) (w := w) (hsA.congr k12.wr) a15
    ((k2.gpr _ (by decide)).trans a14) ((k12.gpr _ (by decide)).trans h11) (by omega_arith) hw' (by omega_arith) (by omega_arith)
    (by omega_arith)) fun s₃ ⟨⟨c3, o3⟩, k3⟩ => ?_)
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  rw [hm2] at c3 o3
  have k13 := k12.trans k3
  have g3 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29], s₃.gpr r = s.gpr r := fun r hr =>
    k13.gpr r (by revert r hr; decide)
  have v8 : val32 s₃.mem (off BX oA) (slot w 8) (2 * w) = Pv := by
    rw [Pre.val32_eq_wv, wv_congr2 fun j hj => c3 j hj, ← Pre.val32_eq_wv, hP]
  -- `p - 1`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((g3 .r10 (by decide)).trans h10)
    ((g3 .r29 (by decide)).trans h29) 8) fun s₄ ⟨⟨b14, m4⟩, k4⟩ => ?_
  refine WP.mono (pm1_ok (hsA.congr (k13.trans k4).wr) (by omega_arith) (by omega_arith) b14 (by rw [m4]; exact v8) hodd)
    fun s₅ ⟨⟨v8', o5⟩, k5⟩ => ?_
  have k15 := (k13.trans k4).trans k5
  have O5 : Mont.Outside (off BX oA) (slot w 8) (8 * w) s.mem s₅.mem :=
    fun x hx => (o5 x (by omega_arith)).trans ((by rw [m4] : s₄.mem x = s₃.mem x).trans (o3 x hx))
  have g5 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29], s₅.gpr r = s.gpr r := fun r hr =>
    k15.gpr r (by revert r hr; decide)
  have u0 : val32 s₅.mem (off BX oA) (slot w 0) (2 * w) = Pv := by rw [O5.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
  have u1 : val32 s₅.mem (off BX oA) (slot w 1) (2 * w) = 2 ^ (128 * w) % Pv := by
    rw [O5.val32 (Or.inl (by omega_arith)) (by omega_arith), hR2]
  have uw : w32 s₅.mem (off BX oA) (slot w 0) = w32 s.mem (off BX oA) (slot w 0) :=
    O5.w32 (Or.inl (by omega_arith)) (by omega_arith)
  have hR2' : 2 ^ (128 * w) % Pv % Pv = 2 ^ (64 * w) * 2 ^ (64 * w) % Pv := by
    rw [Nat.mod_mod, ← Nat.pow_add]; congr 2; omega_arith
  -- `q := (p - 1) R² R⁻¹`.
  refine WP.seq (WP.mono (Pub.montOpN_ok (n := 9) (o := 5) (a := 1) (b := 8) (hsA.congr k15.wr) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw2 hw' (by omega_arith)
    ((g5 .r10 (by decide)).trans h10) ((g5 .r29 (by decide)).trans h29) ((g5 .r11 (by decide)).trans h11)
    (by rw [g5 .r12 (by decide)]; exact h12) (by rw [g5 .r12 (by decide), uw]; exact hinv)
    (by rw [v8', u0]; omega_arith)) fun s₆ ⟨⟨Q6, Q6e, o6⟩, k6⟩ => ?_)
  rw [u0, u1, v8'] at Q6e
  rw [u0] at Q6
  have hq0 := chunk_q0 hR (by omega_arith) Q6e hR2'
  have k16 := k15.trans k6
  have u6 : ∀ j, j = 0 ∨ j = 1 ∨ j = 8 →
      val32 s₆.mem (off BX oA) (slot w j) (2 * w) = val32 s₅.mem (off BX oA) (slot w j) (2 * w) := fun j hj =>
    outs_val32 o6 (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl) <;> rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
      (by rcases hj with rfl | rfl | rfl <;> simp only [e] <;> omega_arith)
  have W6 : Mont.Outside (off BX oA) (slot w 2) (6 * (8 * (w + 2))) s₅.mem s₆.mem :=
    outs_work o6 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> simp only [e] <;> omega_arith)
  have g6 : ∀ r ∈ [Reg.r10, .r11, .r12, .r21, .r23, .r27, .r28, .r29], s₆.gpr r = s.gpr r := fun r hr =>
    k16.gpr r (by revert r hr; decide)
  -- `S := 0`.
  refine WP.seq (WP.mono (Pub.base_ok (rd := .r14) (by decide) (by decide) ((g6 .r10 (by decide)).trans h10)
    ((g6 .r29 (by decide)).trans h29) 4) fun s₇ ⟨⟨c14, m7⟩, k7⟩ => ?_)
  refine WP.seq (WP.mono (zeroWords_ok (hsA.congr (k16.trans k7).wr) c14 ((k7.gpr _ (by decide)).trans
    ((g6 .r11 (by decide)).trans h11)) (by omega_arith) hw' (by omega_arith)) fun s₈ ⟨⟨_, z8, o8⟩, k8⟩ => ?_)
  have k18 := (k16.trans k7).trans k8
  rw [m7] at o8
  have v4 : val32 s₈.mem (off BX oA) (slot w 4) (2 * w) = 0 := by
    rw [Pre.val32_eq_wv]; exact (wv_eq_zero_iff _ _ _ _).mpr z8
  have o8' : Mont.Outside (off BX oA) (slot w 4) (8 * w) s₆.mem s₈.mem := o8
  have Wall : Mont.Outside (off BX oA) (slot w 2) (7 * (8 * (w + 2))) s.mem s₈.mem :=
    ((O5.mono (by omega_arith) (by omega_arith)).trans (W6.mono (by omega_arith) (by omega_arith))).trans (o8'.mono (by omega_arith) (by omega_arith))
  have Oall : Outside BX oA (slot w 24) s.mem s₈.mem := out_sub (fun x hx => Wall x hx) (by omega_arith) (by omega_arith) (by omega_arith)
  have g8 : ∀ r ∈ [Reg.r10, .r11, .r12, .r23, .r29, .r30, .r31], s₈.gpr r = s.gpr r := fun r hr =>
    k18.gpr r (by revert r hr; decide)
  have v5 : val32 s₈.mem (off BX oA) (slot w 5) (2 * w) = val32 s₆.mem (off BX oA) (slot w 5) (2 * w) :=
    o8'.val32 (Or.inr (by omega_arith)) (by omega_arith)
  have I0 : ChunkQ s BX Z oA w wX K Pv (2 ^ (128 * w) % Pv) 0 s₈ := by
    refine ⟨hs.congr k18.wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Oall, k18.mono (by decide)⟩
    · rw [g8 .r10 (by decide), h10]
    · rw [g8 .r23 (by decide), h23]
    · rw [g8 .r29 (by decide), h29]
    · rw [g8 .r11 (by decide), h11]
    · rw [g8 .r12 (by decide)]; exact h12
    · rw [g8 .r12 (by decide), Wall.w32 (Or.inl (by omega_arith)) (by omega_arith)]; exact hinv
    · rw [g8 .r30 (by decide), h30, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
    · rw [g8 .r31 (by decide), h31, Nat.mul_zero]; exact (BitVec.sub_zero _).symm
    · rw [Wall.val32 (Or.inl (by omega_arith)) (by omega_arith), hP]
    · rw [Wall.val32 (Or.inl (by omega_arith)) (by omega_arith), hR2]
    · rw [o8'.val32 (Or.inr (by omega_arith)) (by omega_arith), W6.val32 (Or.inr (by omega_arith)) (by omega_arith), v8']
    · rw [v5]; exact Q6
    · rw [v5]; exact hq0
    · rw [v4]; omega_arith
    · rw [v4, Nat.mul_zero]; rfl
  refine WP.mono (count_loop (cr := .r3) (nChunks_pos (by omega_arith) hK1)
    (fun j u => ChunkQ s BX Z oA w wX K Pv (2 ^ (128 * w) % Pv) j u)
    (fun j hj u I => chunkStepQ_ok hA hX hw2 hw' hK1 hK' hP2 hodd (Nat.mod_lt _ (by omega_arith)) hR2' hj I) I0)
    fun t I => ⟨⟨?_, I.p0, I.p1, I.r12, I.inv, I.out, I.r10⟩, I.keep⟩
  rw [← Nat.mod_eq_of_lt I.slt, I.sv, hC]

end VG.Proof.Bignum.PPC64LE.Crt

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE
open VG.Proof.Bignum (slot)

/-- `redPtrs`: the P space's array 6 into `r30` and its `w` words into `r31`. -/
theorem redPtrs_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hr : Regs s L key sig dig) :
    WP isa (.block Verify.redPtrs) s fun t =>
      (t.gpr .r30 = off L.S (slot L.wp 6) ∧ t.gpr .r31 = BitVec.ofNat 64 L.wp ∧ t.mem = s.mem) ∧
        Keep [.r0, .r30, .r31] s t := by
  have hw8 := hL.wp_eq
  refine WP.keep _ ?_ (by decide)
  unfold Verify.redPtrs getP
  have hpl := hL.pl
  prun [hr.r21, hr.p_eq, hdrBytes, BitVec.add_zero]
  refine ⟨?_, ?_⟩
  · have e : (BitVec.ofNat 64 L.pl + 16#64) * 6#64 + 256#64 = BitVec.ofNat 64 (slot L.wp 6) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, Lay.slot_eq]
      omega_arith
    rw [off, ← e]
    ac_rfl
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega_arith

/-- The registers `vModQ` writes. -/
def vModRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
    .r22, .r23, .r24, .r29, .r30, .r31]

/-- `vModQ`: `v mod q` into the Q space's array 4, for `v` in the P space's
array 6, q (odd) in the Q space's array 0 and `R² mod q` in its array 1; memory
changes only in the Q space's first `slot 4 24` octets, where arrays 0 and 1
are kept. -/
theorem vModQ_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h1 : arrQ s.mem L 1 = 2 ^ (128 * 4) % arrQ s.mem L 0) :
    WP isa Verify.vModQ s fun t =>
      (InQ t L ∧ Regs t L key sig dig ∧ arrQ t.mem L 4 = arrP s.mem L 6 % arrQ s.mem L 0 ∧
        arrQ t.mem L 0 = arrQ s.mem L 0 ∧ arrQ t.mem L 1 = arrQ s.mem L 1 ∧
        Outside L.S L.qOff (slot 4 24) s.mem t.mem) ∧ Keep vModRegs s t := by
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hbe := hL.buf_end
  have hpl := hL.pl
  unfold Verify.vModQ Verify.redEnter
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have hr1 := hr.keep k1 (by decide)
  refine WP.mono (redPtrs_ok hL hr1) fun s₂ ⟨⟨a30, a31, m2⟩, k2⟩ => ?_
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  have h10₂ : s₂.gpr .r10 = off L.Q (slot 4 0) := (k2.gpr .r10 (by decide)).trans q1.env.h10
  have hlow : (word s₂.mem L.Q (slot 4 0)).toNat % 2 = 1 := by
    have h1' := word_eq_w32 s₂.mem L.Q (slot 4 0)
    have h2 : val32 s₂.mem L.Q (slot 4 0) (7 + 1) =
        w32 s₂.mem L.Q (slot 4 0) + 2 ^ 32 * val32 s₂.mem L.Q (slot 4 0 + 4) 7 := rfl
    have h3 : val32 s₂.mem L.Q (slot 4 0) (7 + 1) = arrQ s.mem L 0 := by rw [hm2]
    omega_arith
  refine WP.mono (Pub.minv_ok (q1.env.hs.congr k2.wr) h10₂ (by decide) hlow) fun s₃ ⟨⟨r12lt, r12inv, m3⟩, k3⟩ => ?_
  have hm3 : s₃.mem = s.mem := by rw [m3, hm2]
  have k13 := (k1.trans k2).trans k3
  have hn : 4 * Crt.nChunks L.wp 4 = L.wp := by
    simp only [Crt.nChunks]; rcases hpl with h | h | h <;> omega_arith
  refine WP.seq (WP.mono (Crt.reduceQ_ok (BX := L.S) (Z := L.Z) (oA := L.qOff) (w := 4) (wX := L.wp) (K := L.wp)
      (Pv := arrQ s.mem L 0) (Cv := arrP s.mem L 6)
      (hs.congr k13.wr) (by simp only [Lay.bOff] at hbe; have : slot 4 24 = 1408 := rfl; omega_arith)
      (by simp only [Lay.qOff, Lay.slot_eq]; omega_arith) (by decide) (by decide) (by omega_arith)
      (by omega_arith) (by omega_arith)
      ((k3.gpr .r10 (by decide)).trans h10₂) (((k2.trans k3).gpr .r23 (by decide)).trans q1.h23)
      (((k2.trans k3).gpr .r29 (by decide)).trans q1.env.h29) (((k2.trans k3).gpr .r11 (by decide)).trans q1.env.h11)
      ((k3.gpr .r30 (by decide)).trans a30) ((k3.gpr .r31 (by decide)).trans a31)
      r12lt (by rw [m3]; exact r12inv) (by rw [hm3]) hq2 hqo (by rw [hm3]; exact h1)
      (by rw [hm3, hn, ← Pre.val32_eq_wv]))
    fun s₄ ⟨⟨v4, p0, p1, _, _, o4, a10⟩, k4⟩ => ?_)
  have g23 : s₄.gpr .r23 = L.Q :=
    (k4.gpr .r23 (by decide)).trans ((k3.gpr .r23 (by decide)).trans ((k2.gpr .r23 (by decide)).trans q1.h23))
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₄.mem)
    (by unfold Verify.redExit; prun [g23, BitVec.add_zero]) (by decide)) fun t ⟨⟨t31, mt⟩, kt⟩ => ?_
  have t21 : t.gpr .r21 = L.S := (((k13.trans k4).trans kt).gpr .r21 (by decide)).trans hr.r21
  have K := (k13.trans k4).trans kt
  rw [hm3] at o4
  refine ⟨⟨⟨⟨q1.env.hs.congr ((k2.trans k3).trans (k4.trans kt)).wr, (kt.gpr .r10 (by decide)).trans a10,
      (((k2.trans k3).trans (k4.trans kt)).gpr .r29 (by decide)).trans q1.env.h29,
      (((k2.trans k3).trans (k4.trans kt)).gpr .r11 (by decide)).trans q1.env.h11, t31, by decide, by decide, by decide⟩, t21, (kt.gpr .r23 (by decide)).trans g23⟩,
    ⟨t21, (K.gpr .r27 (by decide)).trans hr.r27, (K.gpr .r28 (by decide)).trans hr.r28,
      (K.gpr .r26 (by decide)).trans hr.r26, by rw [K.gpr .r2 (by decide)]; exact hr.pl,
      by rw [K.gpr .r2 (by decide)]; exact hr.ql⟩,
    by rw [arrQ, arr, mt]; exact v4, by rw [arrQ, arr, mt]; exact p0, by rw [arrQ, arr, mt]; exact p1.trans h1.symm,
    by rw [mt]; exact o4⟩, K.mono (by decide)⟩

end VG.Proof.Dsa.PPC64LE
