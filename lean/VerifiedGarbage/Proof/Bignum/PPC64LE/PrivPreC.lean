module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreB
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVals
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtPhaseP
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: the factors

`partB_ok`: after the checks (`A`), each factor's `R² mod p` (or zeros) to
`pre` after `n`'s values (`prime_ok`), `p`'s then `q`'s (`B`).
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- An address in the region at `B + o` of `n` bytes is at those offsets. -/
theorem in_of_contains {B y : Addr} {o n : Nat} (h : (⟨off B o, n⟩ : Region).Contains y 1) (ho : o < 2 ^ 64)
    (hn : B.toNat + o + n ≤ 2 ^ 64) : o ≤ ofs B y ∧ ofs B y < o + n := by
  simp only [Region.Contains, off] at h
  simp only [ofs]
  have e1 : (y - B).toNat = (2 ^ 64 - B.toNat + y.toNat) % 2 ^ 64 := BitVec.toNat_sub _ _
  have e2 : (y - (B + BitVec.ofNat 64 o)).toNat = (2 ^ 64 - (B.toNat + o) % 2 ^ 64 + y.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show o < 2 ^ 64 from ho)]
  rw [e2] at h
  rw [e1]
  have := B.isLt; have := y.isLt
  omega_arith

/-- A word of the working space before `oA`, after a change only to `pre`'s
segment and to the working space from `oA`. -/
theorem frame_word {m m' : Mem} {P S : Addr} {o n oA L Z PL d : Nat}
    (F : Frame [⟨off P o, n⟩, ⟨off S oA, L⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hon : o + n ≤ PL) (hd : d + 8 ≤ oA) (hZ : oA + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64)
    (hPn : P.toNat + PL ≤ 2 ^ 64) (hn0 : 0 < n) (hL0 : 0 < L) : word m' S d = word m S d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx : ofs S (off S d + BitVec.ofNat 64 i) = d + i := by
    simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by omega_arith) (by omega_arith)
    have := hsep (off S d + BitVec.ofNat 64 i) (by omega_arith)
    omega_arith
  · have := in_of_contains hc (by omega_arith) (by omega_arith)
    omega_arith

/-- A word of `pre` apart from its changed segment, after a change only to
that segment and to the working space. -/
theorem frame_word_pre {m m' : Mem} {P S : Addr} {o n oA L Z PL d : Nat}
    (F : Frame [⟨off P o, n⟩, ⟨off S oA, L⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 ≤ PL) (hZ : oA + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64)
    (hPn : P.toNat + PL ≤ 2 ^ 64) (hon : o + n ≤ PL) (hn0 : 0 < n) (hL0 : 0 < L) :
    word m' P d = word m P d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx : ofs P (off P d + BitVec.ofNat 64 i) = d + i := by
    simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by omega_arith) (by omega_arith)
    omega_arith
  · have := in_of_contains hc (by omega_arith) (by omega_arith)
    have := hsep (off P d + BitVec.ofNat 64 i) (by omega_arith)
    omega_arith

/-- A number of the working space before `oA`, after a change only to
`pre`'s segment and to the working space from `oA`. -/
theorem frame_wv {m m' : Mem} {P S : Addr} {o n oA L Z PL d k : Nat}
    (F : Frame [⟨off P o, n⟩, ⟨off S oA, L⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hon : o + n ≤ PL) (hd : d + 8 * k ≤ oA) (hZ : oA + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64)
    (hPn : P.toNat + PL ≤ 2 ^ 64) (hn0 : 0 < n) (hL0 : 0 < L) : wv m' S d k = wv m S d k :=
  wv_congr fun i hi => frame_word F hsep hon (by omega_arith) hZ hnw hPn hn0 hL0

/-- The factors' words. -/
abbrev cwP (s : State) : Nat := wsWords (cpL s)
abbrev cwQ (s : State) : Nat := wsWords (cqL s)

theorem r2Word_mask (b : Bool) (w P i : Nat) : r2Word b w (if b then P else 3) i = r2Word b w P i := by
  cases b <;> rfl

/-- The registers written up to the factors. -/
def bRegs : List Reg := aRegs ++ ([.r0, .r3, .r30] ++ [.r0, .r3, .r4, .r10, .r11, .r21, .r29]) ++ primeAllRegs

/-- What holds after the factors, from the entry state `s₀`. -/
structure B (s₀ s : State) : Prop where
  scr : Scr s (cS s₀) (cZ s₀)
  hOut : word s.mem (cS s₀) oOut = s₀.gpr .r3
  hN : word s.mem (cS s₀) oN = s₀.gpr .r5
  hNL : word s.mem (cS s₀) oNLen = s₀.gpr .r6
  r23 : s.gpr .r23 = cS s₀
  r26 : s.gpr .r26 = Crt.bmask (cb s₀)
  wP : ∀ i < cwP s₀, word s.mem (s₀.gpr .r3) (16 * cw s₀ + 8 * i) = r2Word (cb s₀) (cwP s₀) (cP s₀) i
  wQ : ∀ i < cwQ s₀, word s.mem (s₀.gpr .r3) (16 * cw s₀ + 8 * cwP s₀ + 8 * i) =
    r2Word (cb s₀) (cwQ s₀) (cQ s₀) i
  keep : Keep bRegs s₀ s
  sav : ∀ i < 18, s.mem.readW (off (Crt.savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

/-- The facts of the factors' values. -/
theorem masked_facts {s₀ : State} (hP : PF s₀) :
    (2 ≤ (if cb s₀ then cP s₀ else 3) ∧ (if cb s₀ then cP s₀ else 3) % 2 = 1 ∧
      (if cb s₀ then cP s₀ else 3) < 2 ^ (64 * cwP s₀)) ∧
    (2 ≤ (if cb s₀ then cQ s₀ else 3) ∧ (if cb s₀ then cQ s₀ else 3) % 2 = 1 ∧
      (if cb s₀ then cQ s₀ else 3) < 2 ^ (64 * cwQ s₀)) := by
  have hpw : cpL s₀ ≤ 8 * cwP s₀ := by unfold cwP wsWords; omega_arith
  have hqw : cqL s₀ ≤ 8 * cwQ s₀ := by unfold cwQ wsWords; omega_arith
  have h3p : 3 < 2 ^ (64 * cwP s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwP s₀ by unfold cwP wsWords; omega_arith))
  have h3q : 3 < 2 ^ (64 * cwQ s₀) := Nat.lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right (n := 2) (by decide)
    (show 2 ≤ 64 * cwQ s₀ by unfold cwQ wsWords; omega_arith))
  cases hb : cb s₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨⟨by decide, by decide, h3p⟩, ⟨by decide, by decide, h3q⟩⟩
  · simp only [↓reduceIte]
    have hb' : Crt.crtMask (cN s₀) (ck s₀) (Spec.Rsa.os2ip []) (cP s₀) (cQ s₀) (Spec.Rsa.os2ip []) = true := by
      rw [show Spec.Rsa.os2ip [] = 0 from rfl, crtMask_zero]; exact hb
    obtain ⟨_, _, _, _, hp1, hpo, hq1, hqo⟩ := Crt.mask_true hP.k64
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.pk) (by rw [VG.Proof.Bignum.bytesAt_length]; exact hP.qk) hb'
    exact ⟨⟨hp1, hpo, Nat.lt_of_lt_of_le (Crt.os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (Crt.pow256_le hpw)⟩,
      ⟨hq1, hqo, Nat.lt_of_lt_of_le (Crt.os2ip_lt' _ (VG.Proof.Bignum.bytesAt_length _ _ _)) (Crt.pow256_le hqw)⟩⟩

/-- The registers of `p`'s working space and where its values go, after the
first block of the factors. -/
structure B1 (s₀ t v : State) : Prop where
  r30 : v.gpr .r30 = off (s₀.gpr .r3) (16 * cw s₀)
  r10 : v.gpr .r10 = off (off (cS s₀) (slot (cwX s₀) 8)) (slot (cwP s₀) 0)
  r21 : v.gpr .r21 = off (off (cS s₀) (slot (cwX s₀) 8)) (slot (cwP s₀) 0)
  r29 : v.gpr .r29 = BitVec.ofNat 64 (8 * (cwP s₀ + 2))
  r11 : v.gpr .r11 = BitVec.ofNat 64 (2 * cwP s₀)
  mem : v.mem = t.mem
  keep : Keep ([.r30, .r3] ++ [.r0, .r3, .r4, .r10, .r11, .r21, .r29]) t v

/-- After `p`'s values (`x`) and `q`'s working space's registers (`y`). -/
structure B2 (s₀ t x y : State) : Prop where
  xw : ∀ i < cwP s₀, word x.mem (s₀.gpr .r3) (16 * cw s₀ + 8 * i) =
    r2Word (cb s₀) (cwP s₀) (if cb s₀ then cP s₀ else 3) i
  x30 : x.gpr .r30 = off (s₀.gpr .r3) (16 * cw s₀ + 8 * cwP s₀)
  xF : Frame [⟨off (s₀.gpr .r3) (16 * cw s₀), 8 * cwP s₀⟩, ⟨off (cS s₀) (slot (cwX s₀) 8), slot (cwP s₀) 24⟩]
    t.mem x.mem
  xk : Keep (([.r30, .r3] ++ [.r0, .r3, .r4, .r10, .r11, .r21, .r29]) ++ primeAllRegs) t x
  y10 : y.gpr .r10 = off (off (cS s₀) (slot (cwX s₀) 8 + slot (cwP s₀) 24)) (slot (cwQ s₀) 0)
  y21 : y.gpr .r21 = off (off (cS s₀) (slot (cwX s₀) 8 + slot (cwP s₀) 24)) (slot (cwQ s₀) 0)
  y29 : y.gpr .r29 = BitVec.ofNat 64 (8 * (cwQ s₀ + 2))
  y11 : y.gpr .r11 = BitVec.ofNat 64 (2 * cwQ s₀)
  ym : y.mem = x.mem
  yk : Keep [.r0, .r3, .r4, .r10, .r11, .r21, .r29] x y

/-- The factors' first block: `r30 := pre + 16 w`, `p`'s working space. -/
theorem partB1_ok {s₀ t : State} (hP : PF s₀) (hA : A s₀ t) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ v, B1 s₀ t v → WP isa c v Q) :
    WP isa (.seq (.block (([.load .d .r30 .r23 oOut, .load .d .r3 .r23 oNLen, .addi .r3 .r3 7, .lsr .d .r3 .r3 3,
      .lsl .r3 .r3 4, .add .r30 .r30 .r3] : List Instr) ++ setupP oBP oPLen)) c) t Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have pq := hP.pq
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have pk := hP.pk; have qk := hP.qk; have p1 := hP.p1; have q1 := hP.q1
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have dX : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have wP2 : 2 ≤ cwP s₀ := by unfold cwP wsWords; omega_arith
  have wQ2 : 2 ≤ cwQ s₀ := by unfold cwQ wsWords; omega_arith
  have eX8 := e (cwX s₀) 8; have eP24 := e (cwP s₀) 24; have eQ24 := e (cwQ s₀) 24
  obtain ⟨⟨mP2, mPo, mPb⟩, ⟨mQ2, mQo, mQb⟩⟩ := masked_facts hP
  -- `r30 := pre + 16 w`.
  have hO : t.mem.readW (off (cS s₀) 0) 64 = s₀.gpr .r3 := hA.hOut
  have hK : t.mem.readW (off (cS s₀) 16) 64 = BitVec.ofNat 64 (ck s₀) := hA.hNL.trans (ofNat_toNat64 _).symm
  have hr0' : InRegions (t.rd ++ t.wr) (off (cS s₀) 0) 8 := hA.scr.ld (d := 0) (n := 8) (by
    simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
  have hr0 : InRegions (t.rd ++ t.wr) (cS s₀) 8 := by simpa only [off, BitVec.add_zero] using hr0'
  have hr16 : InRegions (t.rd ++ t.wr) (off (cS s₀) 16) 8 := hA.scr.ld (d := 16) (n := 8) (by
    simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
  have hO' : t.mem.readW (cS s₀) 64 = s₀.gpr .r3 := by simpa only [off, BitVec.add_zero] using hO
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  rw [hKe] at hK
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r30, .r3] (Q := fun u => u.gpr .r30 = off (s₀.gpr .r3) (16 * cw s₀) ∧ u.mem = t.mem)
    (by
      have l0 := exec_load_d (s := t) (t := .r30) (n := .r23) (off := 0) (by decide) (by decide) (by rw [hA.r23]; exact hr0')
      have l16 := exec_load_d (s := t.write .r30 (s₀.gpr .r3)) (t := .r3) (n := .r23) (off := 16) (by decide)
        (by decide) (by simp only [gpr_write, reduceCtorEq, ↓reduceIte, hA.r23, rd_write, wr_write]; exact hr16)
      have hK2 : t.mem.readW (cS s₀ + 16#64) 64 = BitVec.ofNat 64 K := hK
      prun [oOut, oNLen, l0, hA.r23, l16, hO, hK2, Pre.ofNat_add7_shr3 K (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith),
        Crt.shl_ofNat (w := (K + 7) / 8) (k := 4) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)]
      rw [dw, hKe, Nat.mul_comm]) rfl) fun u ⟨⟨u30, um⟩, uk⟩ => ?_
  refine WP.mono (Crt.setupP_ok (oA := slot (cwX s₀) 8) (len := cpL s₀) (hA.scr.congr uk.wr)
    ((uk.gpr _ (by decide)).trans hA.r23) (by decide) (by decide) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
    (by rw [um]; exact hA.hBP) (by rw [um, hA.hPL]; exact (ofNat_toNat64 _).symm) hP.p1 (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith))
    fun v ⟨⟨v10, v21, v29, v11, _, vm⟩, vk⟩ => ?_
  exact hc v ⟨by rw [vk.gpr _ (by decide)]; exact u30, v10, v21, v29, v11, vm.trans um, uk.trans vk⟩

/-- `p`'s values, then `q`'s working space's registers. -/
theorem partB2_ok {s₀ t v : State} (hP : PF s₀) (hA : A s₀ t) (V : B1 s₀ t v) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ x y, B2 s₀ t x y → WP isa c y Q) :
    WP isa (.seq (PrivPre.prime 4) (.seq (.block (setupP oBQ oQLen)) c)) v Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have pq := hP.pq
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have pk := hP.pk; have qk := hP.qk; have p1 := hP.p1; have q1 := hP.q1
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have dX : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have wP2 : 2 ≤ cwP s₀ := by unfold cwP wsWords; omega_arith
  have wQ2 : 2 ≤ cwQ s₀ := by unfold cwQ wsWords; omega_arith
  have eX8 := e (cwX s₀) 8; have eP24 := e (cwP s₀) 24; have eQ24 := e (cwQ s₀) 24
  obtain ⟨⟨mP2, mPo, mPb⟩, ⟨mQ2, mQo, mQb⟩⟩ := masked_facts hP
  have u30 := V.r30; have v10 := V.r10; have v29 := V.r29; have v11 := V.r11
  have tv := V.keep
  have kv := hA.keep.trans tv
  have hmv : v.mem = t.mem := V.mem
  -- `p`'s values.
  refine WP.seq (WP.mono (prime_ok (b := cb s₀) (Pv := if cb s₀ then cP s₀ else 3) (xj := 4)
    (o := 16 * cw s₀) (wX := cwX s₀) (hA.scr.congr tv.wr) (hP.pre.congr kv.wr) hP.sepPre (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
    (Nat.le_refl _) wP2 (by unfold cwP wsWords; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by decide) v10 v29 v11
    (by rw [tv.gpr _ (by decide)]; exact hA.r27) (by rw [tv.gpr _ (by decide)]; exact hA.r28)
    u30 (by rw [tv.gpr _ (by decide)]; exact hA.r26)
    (by rw [hpl]; simp only [cwP, cw] at *; omega_arith)
    (by rw [hmv]; exact Crt.wv_low (by rw [← Pre.val32_eq_wv]; exact hA.x4) mPb (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)) mP2 mPo)
    fun x ⟨⟨xw, x30, xF⟩, xk⟩ => ?_)
  have tx := tv.trans xk
  have hPS := hP.sepPre
  -- What `p`'s values left as they were.
  have xh : ∀ d, d + 8 ≤ 256 → word x.mem (cS s₀) d = word t.mem (cS s₀) d := fun d hd => by
    rw [frame_word xF hPS (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) hn hnP (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith), hmv]
  -- `q`'s working space.
  refine WP.seq ?_
  refine WP.mono (Crt.setupP_ok (oA := slot (cwX s₀) 8 + slot (cwP s₀) 24) (len := cqL s₀) (hA.scr.congr tx.wr)
    ((tx.gpr _ (by decide)).trans hA.r23) (by decide) (by decide) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
    (by rw [xh _ (by decide)]; exact hA.hBQ) (by rw [xh _ (by decide), hA.hQL]; exact (ofNat_toNat64 _).symm)
    hP.q1 (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith))
    fun y ⟨⟨y10, y21, y29, y11, _, ym⟩, yk⟩ => ?_
  exact hc x y ⟨xw, x30, by rw [hmv] at xF; exact xF, tx, y10, y21, y29, y11, ym, yk⟩

/-- After the checks, the factors' values to `pre`. -/
theorem partB_ok {s₀ t : State} (hP : PF s₀) (hA : A s₀ t) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ u, B s₀ u → WP isa c u Q) :
    WP isa (.seq (.block (([.load .d .r30 .r23 oOut, .load .d .r3 .r23 oNLen, .addi .r3 .r3 7, .lsr .d .r3 .r3 3,
      .lsl .r3 .r3 4, .add .r30 .r30 .r3] : List Instr) ++ setupP oBP oPLen)) (.seq (PrivPre.prime 4)
      (.seq (.block (setupP oBQ oQLen)) (.seq (PrivPre.prime 5) c)))) t Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have pq := hP.pq
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have pk := hP.pk; have qk := hP.qk; have p1 := hP.p1; have q1 := hP.q1
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have dX : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have wP2 : 2 ≤ cwP s₀ := by unfold cwP wsWords; omega_arith
  have wQ2 : 2 ≤ cwQ s₀ := by unfold cwQ wsWords; omega_arith
  have eX8 := e (cwX s₀) 8; have eP24 := e (cwP s₀) 24; have eQ24 := e (cwQ s₀) 24
  obtain ⟨⟨mP2, mPo, mPb⟩, ⟨mQ2, mQo, mQb⟩⟩ := masked_facts hP
  refine partB1_ok hP hA fun v V => partB2_ok hP hA V fun x y X => ?_
  have xw := X.xw; have x30 := X.x30; have xF := X.xF; have tx := X.xk
  have kx := hA.keep.trans tx
  have y10 := X.y10; have y29 := X.y29; have y11 := X.y11; have ym := X.ym; have yk := X.yk
  have hPS := hP.sepPre
  -- What `p`'s values left as they were.
  have xh : ∀ d, d + 8 ≤ 256 → word x.mem (cS s₀) d = word t.mem (cS s₀) d := fun d hd => by
    rw [frame_word xF hPS (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) hn hnP (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)]
  have ky := kx.trans yk
  have ty := tx.trans yk
  refine WP.seq (WP.mono (prime_ok (b := cb s₀) (Pv := if cb s₀ then cQ s₀ else 3) (xj := 5)
    (o := 16 * cw s₀ + 8 * cwP s₀) (wX := cwX s₀) (hA.scr.congr ty.wr) (hP.pre.congr ky.wr) hPS (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
    (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) wQ2 (by unfold cwQ wsWords; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by decide) y10 y29 y11
    (by rw [ty.gpr _ (by decide)]; exact hA.r27) (by rw [ty.gpr _ (by decide)]; exact hA.r28)
    (by rw [yk.gpr _ (by decide), x30])
    (by rw [ty.gpr _ (by decide)]; exact hA.r26)
    (by rw [hpl]; simp only [cwP, cwQ, cw] at *; omega_arith)
    (by rw [ym, frame_wv xF hPS (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) hn hnP (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)]
        exact Crt.wv_low (by rw [← Pre.val32_eq_wv]; exact hA.x5) mQb (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)) mQ2 mQo)
    fun z ⟨⟨zw, _, zF⟩, zk⟩ => ?_)
  have kz := ky.trans zk
  have tz := ty.trans zk
  have zh : ∀ d, d + 8 ≤ 256 → word z.mem (cS s₀) d = word t.mem (cS s₀) d := fun d hd => by
    rw [frame_word zF hPS (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) hn hnP (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith), ym, xh d hd]
  have hpre_sub : ∀ {o n : Nat}, o + n ≤ (s₀.gpr .r4).toNat * 8 →
      Region.Sub ⟨off (s₀.gpr .r3) o, n⟩ (preR s₀) := fun h => Offset.sub_base _ (by omega_arith)
  have hscr_sub : ∀ {o n : Nat}, o + n ≤ cZ s₀ → Region.Sub ⟨off (cS s₀) o, n⟩ (scrR s₀) :=
    fun h => Offset.sub_base _ (by omega_arith)
  have fr : ∀ {m m' : Mem} {o n oA L : Nat}, Frame [⟨off (s₀.gpr .r3) o, n⟩, ⟨off (cS s₀) oA, L⟩] m m' →
      o + n ≤ (s₀.gpr .r4).toNat * 8 → oA + L ≤ cZ s₀ → Frame [preR s₀, scrR s₀] m m' :=
    fun F h1 h2 => F.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨preR s₀, List.mem_cons_self .., hpre_sub h1⟩
      · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), hscr_sub h2⟩
  refine hc z ⟨hA.scr.congr tz.wr, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_,
    fun i hi => ?_, kz.mono (by decide +kernel), fun i hi => ?_, ?_⟩
  · rw [zh _ (by decide), hA.hOut]
  · rw [zh _ (by decide), hA.hN]
  · rw [zh _ (by decide), hA.hNL]
  · rw [tz.gpr _ (by decide), hA.r23]
  · rw [tz.gpr _ (by decide), hA.r26]
  · rw [frame_word_pre zF hPS (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) hn hnP (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith), ym, xw i hi, r2Word_mask]
  · have := zw i hi
    rw [show 16 * cw s₀ + 8 * cwP s₀ + 8 * i = 16 * cw s₀ + 8 * cwP s₀ + 8 * i from rfl] at this
    rw [this, r2Word_mask]
  · have e : Mont.off (Crt.savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := by
      simp only [Mont.off, Crt.savW]; rw [Offset.add_add]
    have h1 := hA.sav i hi
    change z.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _
    change t.mem.readW (Mont.off (Crt.savW (cS s₀)) (8 * i)) 64 = _ at h1
    rw [e] at h1 ⊢
    change word z.mem (cS s₀) (112 + 8 * i) = _
    change word t.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [zh _ (by omega_arith)]; exact h1
  · have F1 := fr (o := 16 * cw s₀) (n := 8 * cwP s₀) (oA := slot (cwX s₀) 8) (L := slot (cwP s₀) 24)
      xF (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
    have F2 := fr (o := 16 * cw s₀ + 8 * cwP s₀) (n := 8 * cwQ s₀) (oA := slot (cwX s₀) 8 + slot (cwP s₀) 24)
      (L := slot (cwQ s₀) 24) zF (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith) (by simp (config := { failIfUnchanged := false }) only [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith)
    rw [ym] at F2
    exact (hA.frame.trans F1).trans F2

end VG.Proof.Bignum.PPC64LE.PrivPre
