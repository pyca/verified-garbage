module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PrivPreC
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreFn
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# An RSA private key's precomputed values on PPC64LE: the modulus

`partC_ok`: after the factors (`B`), `n`'s values to `pre`
(`Precompute.core`), then and-ed with the mask, and the result.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.PrivPre

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

/-- `maskN`'s loop: the `w` words at `r14` (`P`) `&=` the mask of `b`. -/
theorem maskIn_ok {s : State} {P : Addr} {L w : Nat} {b : Bool} (hp : Scr s P L)
    (h14 : s.gpr .r14 = off P 0) (h17 : s.gpr .r17 = BitVec.ofNat 64 w) (h26 : s.gpr .r26 = Crt.bmask b)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hL : 8 * w ≤ L) :
    WP isa (Precompute.countLoop .r17 [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
      .addi .r14 .r14 8]) s fun t =>
      ((∀ i < w, word t.mem P (8 * i) = if b then word s.mem P (8 * i) else 0) ∧
        Outside P 0 (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r17] s t := by
  have hnP := hp.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .r14 = off P (8 * i) ∧ t.gpr .r26 = Crt.bmask b ∧
      (∀ j < i, word t.mem P (8 * j) = if b then word s.mem P (8 * j) else 0) ∧
      (∀ j, i ≤ j → j < w → word t.mem P (8 * j) = word s.mem P (8 * j)) ∧
      Outside P 0 (8 * i) s.mem t.mem ∧ Keep [.r0, .r14, .r17] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26,
      .store .d .r0 .r14 0, .addi .r14 .r14 8] ++ ([.subi .r17 .r17 1] : List Instr)))
    (cnt := .r17) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j14, j26, jw, jr, jout, jk⟩ _ => ?_)
    ⟨by rw [h14], h26, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, Outside.refl _ _ _ _,
      (Keep.refl [] s).mono (by decide)⟩ h17)
    fun t ⟨_, _, tw, _, tout, tk⟩ => ⟨⟨tw, tout⟩, tk⟩
  have hst : WP isa (.block [.load .d .r0 .r14 0, .logic .and .r0 .r0 .r26, .store .d .r0 .r14 0,
      .addi .r14 .r14 8, .subi .r17 .r17 1]) t fun t' =>
      (t'.gpr .r14 = off P (8 * i + 8) ∧ t'.gpr .r17 = t.gpr .r17 - BitVec.ofNat 64 1 ∧
        t'.mem = t.mem.writeW (off P (8 * i)) (word t.mem P (8 * i) &&& Crt.bmask b)) ∧
      Keep [.r0, .r14, .r17] t t' := by
    refine WP.keep _ ?_ (by decide)
    prun [j14, j26, (hp.congr jk.wr).ld (show 8 * i + 8 ≤ L by omega_arith),
      (hp.congr jk.wr).st (show 8 * i + 8 ≤ L by omega_arith)]
  refine WP.mono hst fun t' ⟨⟨l14, l17, lm⟩, lk⟩ => ⟨⟨?_, (lk.gpr _ (by decide)).trans j26, fun j hj => ?_,
    fun j hj hj' => ?_, ?_, jk.trans' lk⟩, l17⟩
  · rw [l14, show 8 * i + 8 = 8 * (i + 1) by omega_arith]
  · rw [lm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [(writeW_outside t.mem P (d := 8 * i) _ (by omega_arith)).word (by omega_arith) (by omega_arith), jw j hj]
    · rw [word_writeW_self, jr j (Nat.le_refl _) hi, PrivPre.and_bmask]
  · rw [lm, (writeW_outside t.mem P (d := 8 * i) _ (by omega_arith)).word (by omega_arith) (by omega_arith),
      jr j (by omega_arith) hj']
  · rw [lm]
    exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans
      ((writeW_outside _ P (d := 8 * i) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

/-- A load of the header's word at `o` (`r23`) into `rd`. -/
theorem ldH_ok {s : State} {S : Addr} {Z o : Nat} {rd : Reg} (hs : Scr s S Z) (h23 : s.gpr .r23 = S)
    (ho : o + 8 ≤ Z) (ho' : o < 2 ^ 15 ∧ o % 4 = 0) :
    WP isa (.block [.load .d rd .r23 o]) s fun t =>
      (t.gpr rd = word s.mem S o ∧ t.mem = s.mem) ∧ Keep [rd] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    exec_load_d (show Reg.r23 ≠ .r0 by decide) ho' (by rw [h23]; exact hs.ld ho), Option.some.injEq,
    exists_eq_left', h23]
  exact ⟨⟨by simp [gpr_write], rfl⟩, Keep.write _ _ _⟩

/-- The registers `setupN` writes. -/
def nRegs : List Reg := [.r19, .r12, .r6, .r21, .r11, .r4, .r10, .r5, .r8, .r9]

/-- `setupN`, after the factors: `Precompute.core`'s registers. -/
theorem setupN_ok {s₀ u : State} (hP : PF s₀) (hB : B s₀ u) :
    WP isa (.block PrivPre.setupN) u fun v =>
      (v.gpr .r19 = s₀.gpr .r3 ∧ v.gpr .r12 = s₀.gpr .r5 ∧ v.gpr .r6 = BitVec.ofNat 64 (ck s₀) ∧
        v.gpr .r21 = cS s₀ ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧
        v.gpr .r10 = off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .r5 = off (cS s₀) (slot (cw s₀) 1) ∧
        v.gpr .r8 = off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .r9 = off (cS s₀) (slot (cw s₀) 3) ∧ v.mem = u.mem) ∧
      Keep nRegs u v := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  rw [show PrivPre.setupN = [.load .d .r19 .r23 oOut] ++ ([.load .d .r12 .r23 oN] ++ ([.load .d .r6 .r23 oNLen] ++
    [.addi .r21 .r23 0, .addi .r11 .r6 7, .lsr .d .r11 .r11 3, .lsl .r4 .r11 3, .addi .r4 .r4 16,
      .addi .r10 .r21 hdrBytes, .add .r5 .r10 .r4, .add .r8 .r5 .r4, .add .r9 .r8 .r4, .lsl .r11 .r11 1])) from rfl]
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok hB.scr hB.r23 (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oOut] at *; omega_arith) (by decide)) fun u1 ⟨⟨a19, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hB.scr.congr k1.wr) ((k1.gpr _ (by decide)).trans hB.r23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oN] at *; omega_arith) (by decide))
    fun u2 ⟨⟨a12, m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hB.scr.congr (k1.trans k2).wr) (((k1.trans k2).gpr _ (by decide)).trans hB.r23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oNLen] at *; omega_arith)
    (by decide)) fun u3 ⟨⟨a6, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have e6 : u3.gpr .r6 = BitVec.ofNat 64 K := by
    rw [a6, m2, m1, hB.hNL, ← hKe]; exact (ofNat_toNat64 _).symm
  have e23 : u3.gpr .r23 = cS s₀ := (k13.gpr _ (by decide)).trans hB.r23
  refine WP.mono (WP.keep [.r21, .r11, .r4, .r10, .r5, .r8, .r9]
    (Q := fun v => v.gpr .r21 = cS s₀ ∧ v.gpr .r11 = BitVec.ofNat 64 (2 * cw s₀) ∧
      v.gpr .r10 = off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .r5 = off (cS s₀) (slot (cw s₀) 1) ∧
      v.gpr .r8 = off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .r9 = off (cS s₀) (slot (cw s₀) 3) ∧ v.mem = u3.mem) (by
        prun [e6, e23, BitVec.add_zero, Pre.ofNat_add7_shr3 K (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith), Pre.ofNat_shl3, Pre.ofNat_shl1, hdrBytes]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
          simp only [off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat, cw, hKe] <;>
          (try congr 2) <;> omega_arith) (by decide))
    fun v ⟨⟨v21, v11, v10, v5, v8, v9, vm⟩, kv⟩ => ⟨⟨?_, ?_, ?_, v21, v11, v10, v5, v8, v9, by rw [vm, m3, m2, m1]⟩,
      (k13.trans kv).mono (by decide)⟩
  · rw [kv.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), a19, hB.hOut]
  · rw [kv.gpr _ (by decide), k3.gpr _ (by decide), a12, m1, hB.hN]
  · rw [kv.gpr _ (by decide), e6, hKe]

/-- A word of `pre` from `n`, after `core` (which writes `n`'s values in
`pre`'s first `n` bytes and arrays in the working space). -/
theorem core_word_pre {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : n ≤ d) (hd' : d + 8 ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64)
    (hPn : P.toNat + PL ≤ 2 ^ 64) : word m' P d = word m P d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx : ofs P (off P d + BitVec.ofNat 64 i) = d + i := by
    simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by unfold hdrBytes; omega_arith) (by omega_arith)
    have := hsep (off P d + BitVec.ofNat 64 i) (by omega_arith)
    omega_arith
  · simp only [Region.Contains] at hc
    simp only [ofs] at hx
    omega_arith

/-- A word of the header, after `core`. -/
theorem core_word_hdr {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : d + 8 ≤ hdrBytes) (hn : n ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64) (hL0 : 0 < L) :
    word m' S d = word m S d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx : ofs S (off S d + BitVec.ofNat 64 i) = d + i := by
    simp only [ofs, off]; rw [Offset.add_add, Mem.sub_ofNat_toNat _ (by unfold hdrBytes at hd; omega_arith)]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by unfold hdrBytes; omega_arith) (by omega_arith)
    omega_arith
  · simp only [Region.Contains] at hc
    have := hsep (off S d + BitVec.ofNat 64 i) (by simp only [ofs]; omega_arith)
    unfold hdrBytes at hd hZ
    omega_arith

/-- What holds after `n`'s values and the mask, from the entry state `s₀`. -/
structure C (s₀ s : State) : Prop where
  r3 : s.gpr .r3 = BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  nW : cb s₀ = true → Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.wordsAt s.mem (s₀.gpr .r3) (2 * cw s₀))
  nZ : cb s₀ = false → ∀ i < 2 * cw s₀, word s.mem (s₀.gpr .r3) (8 * i) = 0
  wP : ∀ i < cwP s₀, word s.mem (s₀.gpr .r3) (16 * cw s₀ + 8 * i) = r2Word (cb s₀) (cwP s₀) (cP s₀) i
  wQ : ∀ i < cwQ s₀, word s.mem (s₀.gpr .r3) (16 * cw s₀ + 8 * cwP s₀ + 8 * i) =
    r2Word (cb s₀) (cwQ s₀) (cQ s₀) i
  r23 : s.gpr .r23 = cS s₀
  keep : Keep (bRegs ++ nRegs ++ Pre.coreRegs ++ [.r14, .r17, .r0, .r3]) s₀ s
  sav : ∀ i < 18, s.mem.readW (off (Crt.savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

theorem one_and_bmask (b : Bool) : BitVec.ofNat 64 1 &&& Crt.bmask b = BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> rfl

theorem sub_len {P : Addr} {n k : Nat} (h : n ≤ k) : Region.Sub ⟨P, n⟩ ⟨P, k⟩ := fun _ hx => by
  simp only [Region.Contains] at hx ⊢; omega_arith

/-- The words of `wordsAt` from `word`s. -/
theorem wordsAt_eq {m m' : Mem} {P : Addr} {n : Nat} (h : ∀ i < n, word m P (8 * i) = word m' P (8 * i)) :
    Spec.Rsa.wordsAt m P n = Spec.Rsa.wordsAt m' P n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

local macro "oa" : tactic => `(tactic| (simp (config := { failIfUnchanged := false }) only
  [cwP, cwQ, cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes] at *; omega_arith))

/-- `pre`'s first `16 w` bytes, in a state with `s₀`'s writable regions. -/
theorem pre16 {s₀ s : State} (hP : PF s₀) (h : s.wr = s₀.wr) : Scr s (s₀.gpr .r3) (16 * cw s₀) := by
  have hpl := hP.preLen
  have hnP := hP.pre.nowrap
  exact ⟨let ⟨B0, o, L, hm, hb, hL, hL'⟩ := hP.pre.wr; ⟨B0, o, L, by rw [h]; exact hm, hb, by
      simp (config := { failIfUnchanged := false }) only [cw, ck, cpL, cqL] at *; omega_arith, hL'⟩,
      by simp (config := { failIfUnchanged := false }) only [cw, ck] at *; omega_arith⟩

/-- The working space is apart from `pre`'s first `16 w` bytes. -/
theorem sep16 {s₀ : State} (hP : PF s₀) : ∀ x, ofs (cS s₀) x < cZ s₀ → 16 * cw s₀ ≤ ofs (s₀.gpr .r3) x :=
  fun x hx => by
    have hpl := hP.preLen
    refine Nat.le_of_not_lt fun hc => ?_
    have := hP.sepPre x (by rw [hpl]; omega_arith)
    omega_arith

/-- After `n`'s values (`Precompute.core`), from the state `u` after the factors. -/
structure CC (s₀ u t : State) : Prop where
  out : Pre.preOut (nB s₀) (s₀.gpr .r3) (2 * cw s₀) (t.gpr .r3) t.mem
  frame : Frame [Pre.arrR (cS s₀) (cw s₀), ⟨s₀.gpr .r3, 16 * cw s₀⟩] u.mem t.mem
  keep : Keep (nRegs ++ Pre.coreRegs) u t

/-- After the factors, `n`'s values. -/
theorem partC1_ok {s₀ u : State} (hP : PF s₀) (hB : B s₀ u) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ t, CC s₀ u t → WP isa c t Q) :
    WP isa (.seq (.block PrivPre.setupN) (.seq Precompute.core c)) u Q := by
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  refine WP.seq (WP.mono (setupN_ok hP hB) fun v ⟨⟨v19, v12, v6, v21, v11, v10, v5, v8, v9, vm⟩, kv⟩ => ?_)
  have kBv := hB.keep.trans kv
  have bN : Spec.Rsa.bytesAt v.mem (s₀.gpr .r5) (ck s₀) = nB s₀ := by
    rw [vm]
    exact bytes_frame hB.frame hP.dN (Nat.le_of_lt (BitVec.isLt _))
  refine WP.seq (WP.mono (Pre.core_ok (hB.scr.congr kv.wr) (pre16 hP kBv.wr) dw k64 k1024 (by oa) v19 v6 v12 v10
    v5 v8 v9 v11 v21 (by rw [kBv.rd, kBv.wr]; exact hP.rN) hP.sN (sep16 hP)) fun t ⟨⟨tO, tF⟩, kt⟩ =>
    hc t ⟨by rw [bN] at tO; exact tO, by rw [vm] at tF; exact tF, kv.trans kt⟩)

/-- `maskN`'s first block: `pre` and `2 w` from the header. -/
theorem maskBlk_ok {s₀ t : State} (hP : PF s₀) (hst : Scr t (cS s₀) (cZ s₀)) (t23 : t.gpr .r23 = cS s₀)
    (hO : word t.mem (cS s₀) oOut = s₀.gpr .r3) (hK : word t.mem (cS s₀) oNLen = s₀.gpr .r6) :
    WP isa (.block [.load .d .r14 .r23 oOut, .load .d .r17 .r23 oNLen, .addi .r17 .r17 7, .lsr .d .r17 .r17 3,
      .lsl .r17 .r17 1]) t fun t3 =>
      (t3.gpr .r14 = off (s₀.gpr .r3) 0 ∧ t3.gpr .r17 = BitVec.ofNat 64 (2 * cw s₀) ∧ t3.mem = t.mem) ∧
        Keep [.r14, .r17] t t3 := by
  have hn := hP.nw; have room := hP.room; have k64 := hP.k64; have k1024 := hP.k1024
  rw [show ([.load .d .r14 .r23 oOut, .load .d .r17 .r23 oNLen, .addi .r17 .r17 7, .lsr .d .r17 .r17 3,
      .lsl .r17 .r17 1] : List Instr) = [.load .d .r14 .r23 oOut] ++ ([.load .d .r17 .r23 oNLen] ++
      [.addi .r17 .r17 7, .lsr .d .r17 .r17 3, .lsl .r17 .r17 1]) from rfl, WP.block_append_iff]
  refine WP.mono (ldH_ok hst t23 (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oOut] at *; omega_arith) (by decide)) fun t1 ⟨⟨a14, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (ldH_ok (hst.congr k1.wr) ((k1.gpr _ (by decide)).trans t23) (by simp (config := { failIfUnchanged := false }) only [cwX, cw, ck, cpL, cqL, cZ, slot, hdrBytes, oNLen] at *; omega_arith) (by decide))
    fun t2 ⟨⟨a17, m2⟩, k2⟩ => ?_
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have e17 : t2.gpr .r17 = BitVec.ofNat 64 K := by
    rw [a17, m1, hK, ← hKe]; exact (ofNat_toNat64 _).symm
  refine WP.mono (WP.keep [.r17] (Q := fun x => x.gpr .r17 = BitVec.ofNat 64 (2 * cw s₀) ∧ x.mem = t2.mem) (by
      prun [e17, Pre.ofNat_add7_shr3 K (by oa), Pre.ofNat_shl1]
      simp only [cw, hKe]) (by decide)) fun t3 ⟨⟨b17, m3⟩, k3⟩ =>
    ⟨⟨by rw [k3.gpr _ (by decide), k2.gpr _ (by decide), a14, hO]; simp [off], b17, by rw [m3, m2, m1]⟩,
      ((k1.trans k2).trans k3).mono (by decide)⟩

/-- After the factors, `n`'s values, the mask and the result. -/
theorem partC_ok {s₀ u : State} (hP : PF s₀) (hB : B s₀ u) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ v, C s₀ v → WP isa c v Q) :
    WP isa (.seq (.block PrivPre.setupN) (.seq Precompute.core (.seq PrivPre.maskN c))) u Q := by
  have hn := hP.nw
  have hnP := hP.pre.nowrap
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have hPS := hP.sepPre
  refine partC1_ok hP hB fun t T => ?_
  have hPS' := sep16 hP
  have kt := T.keep
  have th : ∀ d, d + 8 ≤ 256 → word t.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd =>
    core_word_hdr T.frame hPS hd (by rw [hpl]; omega_arith) (by oa) hn (by omega_arith)
  have tp : ∀ d, 16 * cw s₀ ≤ d → d + 8 ≤ (s₀.gpr .r4).toNat * 8 →
      word t.mem (s₀.gpr .r3) d = word u.mem (s₀.gpr .r3) d := fun d hd hd' =>
    core_word_pre T.frame hPS hd hd' (by oa) hn hnP
  have t23 : t.gpr .r23 = cS s₀ := (kt.gpr _ (by decide)).trans hB.r23
  have t26 : t.gpr .r26 = Crt.bmask (cb s₀) := (kt.gpr _ (by decide)).trans hB.r26
  have hst : Scr t (cS s₀) (cZ s₀) := hB.scr.congr kt.wr
  refine WP.seq ?_
  unfold PrivPre.maskN
  refine WP.seq (WP.mono (maskBlk_ok hP hst t23 (by rw [th _ (by decide), hB.hOut]) (by rw [th _ (by decide), hB.hNL]))
    fun t3 ⟨⟨e14, b17, m13⟩, k13⟩ => ?_)
  have hp3 : Scr t3 (s₀.gpr .r3) (16 * cw s₀) := pre16 hP ((hB.keep.trans kt).trans k13).wr
  refine WP.seq (WP.mono (maskIn_ok (b := cb s₀) hp3 e14 b17 ((k13.gpr _ (by decide)).trans t26) (by oa) (by oa)
    (Nat.le_of_eq (by omega_arith))) fun t4 ⟨⟨w4, o4⟩, k4⟩ => ?_)
  refine WP.mono (WP.keep [.r3] (Q := fun x => x.gpr .r3 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) ∧
      x.mem = t4.mem) (by
        prun [(k4.gpr _ (by decide)).trans ((k13.gpr _ (by decide)).trans t26), one_and_bmask]) (by decide))
    fun t5 ⟨⟨c3, m5⟩, k5⟩ => ?_
  have kall := (((hB.keep.trans kt).trans k13).trans k4).trans k5
  -- The words of `pre` after the mask, and the header.
  have mh : ∀ d, d + 8 ≤ 256 → word t5.mem (cS s₀) d = word u.mem (cS s₀) d := fun d hd => by
    rw [m5, VG.Proof.Bignum.PPC64LE.Outside.word_sep o4 hPS' (by omega_arith) (by oa) (by omega_arith), m13, th d hd]
  have mp : ∀ d, 16 * cw s₀ ≤ d → d + 8 ≤ (s₀.gpr .r4).toNat * 8 →
      word t5.mem (s₀.gpr .r3) d = word u.mem (s₀.gpr .r3) d := fun d hd hd' => by
    rw [m5, o4.word (Or.inr (by omega_arith)) (by omega_arith), m13, tp d hd hd']
  have mn : ∀ i < 2 * cw s₀, word t5.mem (s₀.gpr .r3) (8 * i) =
      if cb s₀ then word t.mem (s₀.gpr .r3) (8 * i) else 0 := fun i hi => by
    rw [m5, w4 i hi, m13]
  have hlen : (nB s₀).length = ck s₀ := bytesAt_length _ _ _
  have tO := T.out
  refine hc t5 ⟨c3, fun hb => ?_, fun hb i hi => by rw [mn i hi, hb]; rfl, fun i hi => ?_, fun i hi => ?_,
    (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans ((k13.gpr _ (by decide)).trans t23)),
    kall.mono (by decide +kernel), fun i hi => ?_, ?_⟩
  · have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = true := by
      have := hb; simp only [cb, privMask, Bool.and_eq_true] at this; exact this.1
    have hs : Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.toWords (cN s₀) (cw s₀) ++
        Spec.Rsa.toWords (2 ^ (128 * cw s₀) % cN s₀) (cw s₀)) := by
      simp only [Spec.Rsa.publicPrecompute, hlen, hv, Spec.Rsa.modulusWords]; rfl
    unfold Pre.preOut at tO
    rw [hs] at tO ⊢
    rw [wordsAt_eq (m' := t.mem) fun i hi => by rw [mn i hi, hb]; rfl, tO.2]
  · rw [mp _ (by omega_arith) (by rw [hpl]; oa), hB.wP i hi]
  · rw [mp _ (by omega_arith) (by rw [hpl]; oa), hB.wQ i hi]
  · have e : off (Crt.savW (cS s₀)) (8 * i) = off (cS s₀) (112 + 8 * i) := by
      simp only [off, Crt.savW]; rw [Offset.add_add]
    rw [e]
    change word t5.mem (cS s₀) (112 + 8 * i) = _
    rw [mh _ (by omega_arith)]
    have h1 := hB.sav i hi
    rw [e] at h1
    exact h1
  · have F1 : Frame [preR s₀, scrR s₀] u.mem t.mem := T.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base _ (by oa)⟩
      · exact ⟨preR s₀, List.mem_cons_self .., sub_len (by rw [hpl]; omega_arith)⟩
    have F2 : Frame [preR s₀, scrR s₀] t.mem t5.mem := by
      rw [m5, ← m13]
      refine (Pre.frame_of_outside o4 (d := 0) (L := 16 * cw s₀) (Nat.le_refl _) (by omega_arith) (Z := (s₀.gpr .r4).toNat * 8)
        (by rw [hpl]; unfold wsWords; oa) hnP).sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨preR s₀, List.mem_cons_self .., Offset.sub_base _ (by rw [hpl]; oa)⟩
    exact (hB.frame.trans F1).trans F2

end VG.Proof.Bignum.PPC64LE.PrivPre
