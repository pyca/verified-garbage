module
-- separate module: the precomputation's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

public import VerifiedGarbage.Proof.Bignum.RISCV64.PrivPreC
public import VerifiedGarbage.Proof.Bignum.RISCV64.PreCore
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreSave
import VerifiedGarbage.Proof.Bignum.RISCV64.PreFn
import VerifiedGarbage.Proof.Bignum.RISCV64.CrtMid1
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# An RSA private key's precomputed values on RISC-V: the modulus

`partC_ok`: after the factors (`B`), `n`'s values to `pre`
(`Precompute.core`), then and-ed with the mask, and the result.
-/

@[expose] public section

namespace VG.Proof.Bignum.RISCV64.PrivPre

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Bignum.RISCV64.Crt
open VG.Proof.Bignum.RISCV64
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Crt (wordsOf savW cmask and_mask)

/-- `maskN`'s loop: the `w` words at `t3` (`P`) `&=` the mask of `b` (`t1`). -/
theorem maskIn_ok {s : State} {P : Addr} {L w : Nat} {b : Bool} (hp : Scr s P L)
    (h3 : s.gpr .t3 = P) (h5 : s.gpr .t5 = BitVec.ofNat 64 w) (h1 : s.gpr .t1 = cmask b)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hL : 8 * w ≤ L) :
    WP isa (countLoop .t5 [.load .d .s0 .t3 0, .logic .and .s0 .s0 .t1, .store .d .s0 .t3 0, .addi .t3 .t3 8]) s
      fun t => ((∀ i < w, Mont.word t.mem P (8 * i) = if b then Mont.word s.mem P (8 * i) else 0) ∧
        Mont.Outside P 0 (8 * w) s.mem t.mem) ∧ Keep [.s0, .t3, .t5] s t := by
  have hnP := hp.nowrap
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = Mont.off P (8 * i) ∧ t.gpr .t1 = cmask b ∧
      (∀ j < i, Mont.word t.mem P (8 * j) = if b then Mont.word s.mem P (8 * j) else 0) ∧
      (∀ j, i ≤ j → j < w → Mont.word t.mem P (8 * j) = Mont.word s.mem P (8 * j)) ∧
      Mont.Outside P 0 (8 * i) s.mem t.mem ∧ Keep [.s0, .t3, .t5] s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s0 .t3 0, .logic .and .s0 .s0 .t1,
      .store .d .s0 .t3 0, .addi .t3 .t3 8] ++ ([.addi .t5 .t5 (-1)] : List Instr)))
    (cnt := .t5) (N := w) (by omega_arith) (by omega_arith) Inv (fun i hi t ⟨j3, j1, jw, jr, jout, jk⟩ _ => ?_)
    ⟨by rw [h3]; exact (BitVec.add_zero _).symm, h1, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl,
      Mont.Outside.refl _ _ _ _, (Keep.refl [] s).mono (by decide)⟩ h5)
    fun t ⟨_, _, tw, _, tout, tk⟩ => ⟨⟨tw, tout⟩, tk⟩
  have hw8 := Mont.writeW_outside t.mem P (d := 8 * i) (Mont.word t.mem P (8 * i) &&& cmask b) (by omega_arith)
  refine WP.mono (WP.keep [.s0, .t3, .t5] (Q := fun t' =>
    t'.mem = t.mem.writeW (Mont.off P (8 * i)) (Mont.word t.mem P (8 * i) &&& cmask b) ∧
      t'.gpr .t3 = Mont.off P (8 * (i + 1)) ∧ t'.gpr .t5 = t.gpr .t5 - BitVec.ofNat 64 1) ?_ (by rfl) (by rfl))
    fun t' ⟨⟨a, b3, c⟩, k⟩ => ⟨⟨b3, (k.gpr (by decide)).trans j1, fun j hj => ?_, fun j hj hj' => ?_, ?_,
      Keep.trans' jk k⟩, c⟩
  · brun [add_ofNat_zero, j3, j1, (hp.congr jk.2.2).ld (show 8 * i + 8 ≤ L by omega_arith),
      (hp.congr jk.2.2).al8 (show 8 * i + 8 ≤ L by omega_arith) (by omega_arith),
      (hp.congr jk.2.2).st (show 8 * i + 8 ≤ L by omega_arith)]
    rw [show 8 * i + 8 = 8 * (i + 1) by omega_arith]
  · rw [a]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [hw8.word (by omega_arith) (by omega_arith)]; exact jw j hj
    · rw [Mont.word_writeW_self, jr j (Nat.le_refl _) hi, and_mask]
  · rw [a, hw8.word (by omega_arith) (by omega_arith)]; exact jr j (by omega_arith) hj'
  · rw [a]; exact (jout.mono (Nat.le_refl _) (by omega_arith)).trans (hw8.mono (by omega_arith) (by omega_arith))

/-- The registers `setupN` writes. -/
def nRegs : List Reg := [.s5, .s7, .s8, .t0, .a1, .a7, .a2, .a5, .a6]

/-- `setupN`, after the factors: `Precompute.core`'s registers. -/
theorem setupN_ok {s₀ u : State} (hP : PF s₀) (hB : B s₀ u) :
    WP isa (.block PrivPre.setupN) u fun v =>
      (v.gpr .s5 = s₀.gpr .a0 ∧ v.gpr .s7 = s₀.gpr .a2 ∧ v.gpr .s8 = BitVec.ofNat 64 (ck s₀) ∧
        v.gpr .t0 = BitVec.ofNat 64 (cw s₀) ∧
        v.gpr .a7 = Mont.off (cS s₀) (slot (cw s₀) 0) ∧ v.gpr .a2 = Mont.off (cS s₀) (slot (cw s₀) 1) ∧
        v.gpr .a5 = Mont.off (cS s₀) (slot (cw s₀) 2) ∧ v.gpr .a6 = Mont.off (cS s₀) (slot (cw s₀) 3) ∧
        v.mem = u.mem) ∧
      Keep nRegs u v := by
  have hn := hP.nw
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have hs := hB.scr
  have z : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
  have hO : u.mem.readW (cS s₀) 64 = s₀.gpr .a0 := by rw [← z]; exact hB.hOut
  have l0 : InRegions (u.rd ++ u.wr) (cS s₀) 8 := by rw [← z]; exact hs.ld (by omega_arith)
  have hN : u.mem.readW (Mont.off (cS s₀) 8) 64 = s₀.gpr .a2 := hB.hN
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have hK : u.mem.readW (Mont.off (cS s₀) 16) 64 = BitVec.ofNat 64 K := by
    rw [← hKe]; exact hB.hNL.trans (Pre.ofNat_toNat64 _).symm
  refine WP.keep _ ?_ (by rfl) (by rfl)
  unfold PrivPre.setupN
  brun [hB.s6, add_ofNat_zero, oOut, oN, oNLen, l0, hs.al, hs.ld (show 8 + 8 ≤ cZ s₀ by omega_arith),
    hs.al8 (show 8 + 8 ≤ cZ s₀ by omega_arith) (by decide), hs.ld (show 16 + 8 ≤ cZ s₀ by omega_arith),
    hs.al8 (show 16 + 8 ≤ cZ s₀ by omega_arith) (by decide), hO, hN, hK,
    Pre.ofNat_add7_shr3 K (by omega_arith), Pre.ofNat_shl3, hdrBytes]
  rw [dw, hKe]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Mont.off, slot, hdrBytes, BitVec.add_assoc, BitVec.ofNat_add_ofNat] <;>
    congr 2 <;> omega_arith

/-- A word of `pre` from `n`, after `core` (which writes `n`'s values in
`pre`'s first `n` bytes and arrays in the working space). -/
theorem core_word_pre {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨Mont.off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : n ≤ d) (hd' : d + 8 ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64)
    (hPn : P.toNat + PL ≤ 2 ^ 64) : Mont.word m' P d = Mont.word m P d := by
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx := ofs_off' P (d := d) (i := i) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by omega_arith)
    have := hsep (Mont.off P d + BitVec.ofNat 64 i) (by change (_ - P).toNat < PL; omega_arith)
    change _ ≤ (_ - S).toNat at this
    omega_arith
  · change (_ - P).toNat + 1 ≤ n at hc
    omega_arith

/-- A word of the header, after `core`. -/
theorem core_word_hdr {m m' : Mem} {P S : Addr} {n L Z PL d : Nat}
    (F : Frame [⟨Mont.off S hdrBytes, L⟩, ⟨P, n⟩] m m') (hsep : ∀ x, ofs P x < PL → Z ≤ ofs S x)
    (hd : d + 8 ≤ hdrBytes) (hn : n ≤ PL) (hZ : hdrBytes + L ≤ Z) (hnw : S.toNat + Z ≤ 2 ^ 64) :
    Mont.word m' S d = Mont.word m S d := by
  have hh : hdrBytes = 256 := rfl
  refine Mem.readW_congr fun i hi => F _ fun r hr hc => ?_
  have hx := ofs_off' S (d := d) (i := i) (by omega_arith)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · have := in_of_contains hc (by omega_arith)
    omega_arith
  · change (_ - P).toNat + 1 ≤ n at hc
    by_contra hne
    have := hsep (Mont.off S d + BitVec.ofNat 64 i) (by change (_ - P).toNat < PL; omega_arith)
    change _ ≤ (_ - S).toNat at this
    omega_arith

/-- What holds after `n`'s values and the mask, from the entry state `s₀`. -/
structure C (s₀ s : State) : Prop where
  a0 : s.gpr .a0 = BitVec.ofNat 64 (if cb s₀ then 1 else 0)
  nW : cb s₀ = true → Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.wordsAt s.mem (s₀.gpr .a0) (2 * cw s₀))
  nZ : cb s₀ = false → ∀ i < 2 * cw s₀, Mont.word s.mem (s₀.gpr .a0) (8 * i) = 0
  wP : ∀ i < cwP s₀, Mont.word s.mem (s₀.gpr .a0) (16 * cw s₀ + 8 * i) = r2Word (cb s₀) (cwP s₀) (cP s₀) i
  wQ : ∀ i < cwQ s₀, Mont.word s.mem (s₀.gpr .a0) (16 * cw s₀ + 8 * cwP s₀ + 8 * i) =
    r2Word (cb s₀) (cwQ s₀) (cQ s₀) i
  s6 : s.gpr .s6 = cS s₀
  keep : Keep (bRegs ++ nRegs ++ Pre.coreRegs ++ [.t3, .t5, .t1] ++ [.s0, .t3, .t5] ++ [.a0]) s₀ s
  sav : ∀ i < 13, s.mem.readW (off (savW (cS s₀)) (8 * i)) 64 = s₀.gpr (Crt.saved i)
  frame : Frame [preR s₀, scrR s₀] s₀.mem s.mem

theorem one_and_cmask (b : Bool) : BitVec.ofNat 64 1 &&& cmask b = BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> decide

theorem sub_len {P : Addr} {n k : Nat} (h : n ≤ k) : Region.Sub ⟨P, n⟩ ⟨P, k⟩ := fun _ hx => by
  simp only [Region.Contains] at hx ⊢; omega_arith

/-- The words of `wordsAt` from `word`s. -/
theorem wordsAt_eq {m m' : Mem} {P : Addr} {n : Nat} (h : ∀ i < n, Mont.word m P (8 * i) = Mont.word m' P (8 * i)) :
    Spec.Rsa.wordsAt m P n = Spec.Rsa.wordsAt m' P n :=
  List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

/-- `pre`'s first `16 w` bytes, in a state with `s₀`'s writable regions. -/
theorem pre16 {s₀ s : State} (hP : PF s₀) (h : s.wr = s₀.wr) : Scr s (s₀.gpr .a0) (16 * cw s₀) := by
  have hpl := hP.preLen
  exact Crt.Scr.le (hP.pre.congr h) (by omega_arith)

/-- The working space is apart from `pre`'s first `16 w` bytes. -/
theorem sep16 {s₀ : State} (hP : PF s₀) : ∀ x, ofs (cS s₀) x < cZ s₀ → 16 * cw s₀ ≤ ofs (s₀.gpr .a0) x :=
  fun x hx => by
    have hpl := hP.preLen
    refine Nat.le_of_not_lt fun hc => ?_
    have := hP.sepPre x (by omega_arith)
    omega_arith

/-- After `n`'s values (`Precompute.core`), from the state `u` after the factors. -/
structure CC (s₀ u t : State) : Prop where
  out : Pre.preOut (nB s₀) (s₀.gpr .a0) (2 * cw s₀) (t.gpr .a0) t.mem
  frame : Frame [Pre.arrR (cS s₀) (cw s₀), ⟨s₀.gpr .a0, 16 * cw s₀⟩] u.mem t.mem
  keep : Keep (nRegs ++ Pre.coreRegs) u t

/-- After the factors, `n`'s values. -/
theorem partC1_ok {s₀ u : State} (hP : PF s₀) (hB : B s₀ u) {c : Prog isa} {Q : State → Prop}
    (hc : ∀ t, CC s₀ u t → WP isa c t Q) :
    WP isa (.seq (.block PrivPre.setupN) (.seq Precompute.core c)) u Q := by
  have room := hP.room
  have k64 := hP.k64; have k1024 := hP.k1024
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8; have eN8 := e (cw s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  refine WP.seq (WP.mono (setupN_ok hP hB) fun v ⟨⟨v5, v7, v8, v0, va7, va2, va5, va6, vm⟩, kv⟩ => ?_)
  have kBv := hB.keep.trans kv
  have bN : Spec.Rsa.bytesAt v.mem (s₀.gpr .a2) (ck s₀) = nB s₀ := by
    rw [vm]
    exact bytes_frame hB.frame hP.dN (Nat.le_of_lt (BitVec.isLt _))
  refine WP.seq (WP.mono (Pre.core_ok (hB.scr.congr kv.2.2) (pre16 hP kBv.2.2) dw k64 k1024 (by omega_arith) v5 v8 v7
    va7 va2 va5 va6 v0 (by rw [kBv.2.1, kBv.2.2]; exact hP.rN) hP.sN (sep16 hP)) fun t ⟨⟨tO, tF⟩, kt⟩ =>
    hc t ⟨by rw [bN] at tO; exact tO, by rw [vm] at tF; exact tF, kv.trans kt⟩)

/-- `maskN`'s first block. -/
abbrev maskBlk : List Instr :=
  [.load .d .t3 .s6 oOut, .load .d .t5 .s6 oNLen, .addi .t5 .t5 7, .shift .srl .d .t5 .t5 3,
    .shift .sll .d .t5 .t5 1, .load .d .t1 .s6 oMask]

/-- `maskN`'s first block, after `n`'s values: `pre`, `2 w` and the mask from
the header. -/
theorem maskBlk_ok {s₀ u t : State} (hP : PF s₀) (hB : B s₀ u) (T : CC s₀ u t) :
    WP isa (.block maskBlk) t fun x =>
      (x.gpr .t3 = s₀.gpr .a0 ∧ x.gpr .t5 = BitVec.ofNat 64 (2 * cw s₀) ∧ x.gpr .t1 = cmask (cb s₀) ∧
        x.mem = t.mem) ∧ Keep [.t3, .t5, .t1] t x := by
  have hn := hP.nw
  have room := hP.room
  have hpl := hP.preLen
  have k64 := hP.k64; have k1024 := hP.k1024
  have hPS := hP.sepPre
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8; have eN8 := e (cw s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have hh : hdrBytes = 256 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  have kt := T.keep
  have th : ∀ d, d + 8 ≤ 256 → Mont.word t.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd =>
    core_word_hdr T.frame hPS (by omega_arith) (by omega_arith) (by omega_arith) hn
  have t6 : t.gpr .s6 = cS s₀ := (kt.gpr (by decide)).trans hB.s6
  have hst : Scr t (cS s₀) (cZ s₀) := hB.scr.congr kt.2.2
  have z : Mont.off (cS s₀) 0 = cS s₀ := BitVec.add_zero _
  have hO : t.mem.readW (cS s₀) 64 = s₀.gpr .a0 := by rw [← z]; exact (th _ (by decide)).trans hB.hOut
  have l0 : InRegions (t.rd ++ t.wr) (cS s₀) 8 := by rw [← z]; exact hst.ld (by omega_arith)
  obtain ⟨K, hKe⟩ : ∃ K, ck s₀ = K := ⟨_, rfl⟩
  have hK : t.mem.readW (Mont.off (cS s₀) 16) 64 = BitVec.ofNat 64 K := by
    rw [← hKe]; exact ((th 16 (by decide)).trans hB.hNL).trans (Pre.ofNat_toNat64 _).symm
  have hM : t.mem.readW (Mont.off (cS s₀) 88) 64 = cmask (cb s₀) :=
    ((th 88 (by decide)).trans hB.hMask).trans (Crt.cmask_sub _).symm
  exact WP.keep [.t3, .t5, .t1] (Q := fun x => x.gpr .t3 = s₀.gpr .a0 ∧
      x.gpr .t5 = BitVec.ofNat 64 (2 * cw s₀) ∧ x.gpr .t1 = cmask (cb s₀) ∧ x.mem = t.mem) (by
        brun [t6, add_ofNat_zero, oOut, oNLen, oMask, l0, hst.al, hst.ld (show 16 + 8 ≤ cZ s₀ by omega_arith),
          hst.al8 (show 16 + 8 ≤ cZ s₀ by omega_arith) (by decide), hst.ld (show 88 + 8 ≤ cZ s₀ by omega_arith),
          hst.al8 (show 88 + 8 ≤ cZ s₀ by omega_arith) (by decide), hO, hK, hM,
          Pre.ofNat_add7_shr3 K (by omega_arith), Crt.ofNat_shl _ _ (show 1 < 64 by decide), Nat.reducePow]
        rw [dw, hKe]) (by rfl) (by rfl)

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
  have e : ∀ w j, slot w j = 256 + j * (8 * (w + 2)) := fun _ _ => rfl
  have eX8 := e (cwX s₀) 8; have eN8 := e (cw s₀) 8
  have hcw : cwX s₀ = 2 * cw s₀ := rfl
  have dw : cw s₀ = (ck s₀ + 7) / 8 := rfl
  have hh : hdrBytes = 256 := rfl
  have dP : cwP s₀ = wordsOf (cpL s₀) := rfl
  have dQ : cwQ s₀ = wordsOf (cqL s₀) := rfl
  have dcZ : cZ s₀ = (stackArg s₀ 1).toNat * 8 := rfl
  refine partC1_ok hP hB fun t T => ?_
  have hPS' := sep16 hP
  have kt := T.keep
  have th : ∀ d, d + 8 ≤ 256 → Mont.word t.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd =>
    core_word_hdr T.frame hPS (by omega_arith) (by omega_arith) (by omega_arith) hn
  have tp : ∀ d, 16 * cw s₀ ≤ d → d + 8 ≤ (s₀.gpr .a1).toNat * 8 →
      Mont.word t.mem (s₀.gpr .a0) d = Mont.word u.mem (s₀.gpr .a0) d := fun d hd hd' =>
    core_word_pre T.frame hPS hd hd' (by omega_arith) hn hnP
  have t6 : t.gpr .s6 = cS s₀ := (kt.gpr (by decide)).trans hB.s6
  have hst : Scr t (cS s₀) (cZ s₀) := hB.scr.congr kt.2.2
  unfold PrivPre.maskN
  refine WP.seq ?_
  refine WP.seq (WP.mono (maskBlk_ok hP hB T)     fun t3 ⟨⟨e3, b5, b1, m13⟩, k13⟩ => ?_)
  have hp3 : Scr t3 (s₀.gpr .a0) (16 * cw s₀) := pre16 hP ((hB.keep.trans kt).trans k13).2.2
  refine WP.seq (WP.mono (maskIn_ok (b := cb s₀) hp3 e3 b5 b1 (by omega_arith) (by omega_arith)
    (Nat.le_of_eq (by omega_arith))) fun t4 ⟨⟨w4, o4⟩, k4⟩ => ?_)
  refine WP.mono (WP.keep [.a0] (Q := fun x => x.gpr .a0 = BitVec.ofNat 64 (if cb s₀ then 1 else 0) ∧
      x.mem = t4.mem) (by
        brun [exec_li, (k4.gpr (by decide)).trans b1]
        exact one_and_cmask _) (by rfl) (by rfl))
    fun t5 ⟨⟨c0, m5⟩, k5⟩ => ?_
  have kall := (((hB.keep.trans kt).trans k13).trans k4).trans k5
  -- The words of `pre` after the mask, and the header.
  have mh : ∀ d, d + 8 ≤ 256 → Mont.word t5.mem (cS s₀) d = Mont.word u.mem (cS s₀) d := fun d hd => by
    rw [m5, VG.Proof.Bignum.RISCV64.Outside.word_sep o4 hPS' (by omega_arith) (by omega_arith) (by omega_arith),
      m13, th d hd]
  have mp : ∀ d, 16 * cw s₀ ≤ d → d + 8 ≤ (s₀.gpr .a1).toNat * 8 →
      Mont.word t5.mem (s₀.gpr .a0) d = Mont.word u.mem (s₀.gpr .a0) d := fun d hd hd' => by
    rw [m5, o4.word (Or.inr (by omega_arith)) (by omega_arith), m13, tp d hd hd']
  have mn : ∀ i < 2 * cw s₀, Mont.word t5.mem (s₀.gpr .a0) (8 * i) =
      if cb s₀ then Mont.word t.mem (s₀.gpr .a0) (8 * i) else 0 := fun i hi => by
    rw [m5, w4 i hi, m13]
  have hlen : (nB s₀).length = ck s₀ := VG.Proof.Bignum.bytesAt_length _ _ _
  have tO := T.out
  refine hc t5 ⟨c0, fun hb => ?_, fun hb i hi => by rw [mn i hi, hb]; rfl, fun i hi => ?_, fun i hi => ?_,
    (k5.gpr (by decide)).trans ((k4.gpr (by decide)).trans ((k13.gpr (by decide)).trans t6)),
    kall, fun i hi => ?_, ?_⟩
  · have hv : Spec.Rsa.modulusValid (cN s₀) (ck s₀) = true := by
      have := hb; simp only [cb, privMask, Bool.and_eq_true] at this; exact this.1
    have hs : Spec.Rsa.publicPrecompute (nB s₀) = some (Spec.Rsa.toWords (cN s₀) (cw s₀) ++
        Spec.Rsa.toWords (2 ^ (128 * cw s₀) % cN s₀) (cw s₀)) := by
      simp only [Spec.Rsa.publicPrecompute, hlen, hv, Spec.Rsa.modulusWords]; rfl
    unfold Pre.preOut at tO
    rw [hs] at tO ⊢
    rw [wordsAt_eq (m' := t.mem) fun i hi => by rw [mn i hi, hb]; rfl, tO.2]
  · rw [mp _ (by omega_arith) (by omega_arith), hB.wP i hi]
  · rw [mp _ (by omega_arith) (by have := Crt.wordsOf_ge (l := cqL s₀); omega_arith), hB.wQ i hi]
  · have esav : off (savW (cS s₀)) (8 * i) = Mont.off (cS s₀) (112 + 8 * i) := by
      simp only [off, Mont.off, savW]; rw [Offset.add_add]
    have h1 := hB.sav i hi
    rw [esav] at h1 ⊢
    change Mont.word t5.mem (cS s₀) (112 + 8 * i) = _
    change Mont.word u.mem (cS s₀) (112 + 8 * i) = _ at h1
    rw [mh _ (by omega_arith)]
    exact h1
  · have F1 : Frame [preR s₀, scrR s₀] u.mem t.mem := T.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, List.mem_cons_of_mem _ (List.mem_singleton_self _), Offset.sub_base _ (by omega_arith)⟩
      · exact ⟨preR s₀, List.mem_cons_self .., sub_len (by omega_arith)⟩
    have F2 : Frame [preR s₀, scrR s₀] t.mem t5.mem := by
      rw [m5, ← m13]
      refine (Pre.frame_of_outside0 o4 (L := 16 * cw s₀) (by omega_arith)).sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨preR s₀, List.mem_cons_self .., sub_len (by omega_arith)⟩
    exact (hB.frame.trans F1).trans F2

end VG.Proof.Bignum.RISCV64.PrivPre
