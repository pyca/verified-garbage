module

public import VerifiedGarbage.Proof.Ffdh.RISCV64.Cached.AttemptFn
public import VerifiedGarbage.Proof.Ffdh.RISCV64.GenerateKey.Body
public import VerifiedGarbage.Impl.Ffdh.RISCV64.Cached
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
-- separate module: the cached attempt's correctness proof is split in a chain of modules, so that a change rebuilds only the modules after it

/-!
# `vg_ffdh_generate_key_cached` on RISC-V: the front

`cgx`: the attempt's public data as `vg_ffdh_derive_public`'s (`XD`), with
`y` as `out`, x as x and g as the peer. `cgFront_ok`: the front loads the
working space's and the context's addresses from the stack, saves the
callee-saved registers, puts the context's address and its three public
words into the header's words 4–7 (`ctxHdr_ok`), then the exchange's words
0–3 and `setup`. `cgXR`: x's and `rand`'s facts.
-/

@[expose] public section

namespace VG.Proof.Ffdh.RISCV64.Cached

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.RISCV64
  VG.Impl.Ffdh.RISCV64 VG.Impl.Ffdh.RISCV64.Cached
open VG.Proof.Bignum.RISCV64
open VG.Proof.Ffdh.RISCV64
open VG.Proof.Ffdh.RISCV64.GenerateKey (XR ghdr_ok)
open VG.Proof.Ffdh.RISCV64.Derive (AR)
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Pub (savW savR)

/-- The exchange's public data of an attempt: `y` as `out`, x as x, g as the
peer. -/
def cgx (s : State) : XD :=
  ⟨s.gpr .a2, s.gpr .a4, (s.gpr .a5).toNat, (s.gpr .a6).toNat, s.gpr .a0, (s.gpr .a6).toNat,
    off (s.gpr .a4) (s.gpr .a6).toNat, stackArg s 1, (stackArg s 2).toNat * 8,
    Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat⟩

/-- An argument on the stack into a register. -/
theorem loadSk_ok (s : State) (r : Reg) (k o : Nat) (ho : o = 8 * k) (hk : 8 * k < 2048)
    (h : InRegions (s.rd ++ s.wr) (stackArgAddr s k) 8) (ha : s.sp.toNat % 16 = 0)
    (hw : writesOnly [r] (.block ([.addSp r o, .load .d r r 0] : List Instr)) = true := by rfl) :
    WP isa (.block ([.addSp r o, .load .d r r 0] : List Instr)) s fun t =>
      (t.gpr r = stackArg s k ∧ t.mem = s.mem ∧ t.sp = s.sp) ∧ Keep [r] s t := by
  refine WP.keep _ ?_ hw (by rfl)
  subst ho
  simp only [stackArgAddr] at h
  have ha' : (s.sp + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 0).toNat % 8 = 0 := by
    rw [add_ofNat_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8 * k) (by omega_arith)]
    omega_arith
  have h' : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 0) 8 := by
    rw [add_ofNat_zero]; exact h
  have ha'' : (s.sp + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0 := by rw [add_ofNat_zero] at ha'; exact ha'
  brun [exec_addSp hk, add_ofNat_zero, h, h', ha', ha'']
  simp [stackArg, stackArgAddr]

/-- `ctxHdr`: the context's address (`t1`) and its three public words into
the header's words 4–7. -/
theorem ctxHdr_ok {s : State} {S C : Addr} {Z : Nat} (hs : Scr s S Z) (hZ : 64 ≤ Z) (h6 : s.gpr .s6 = S)
    (h1 : s.gpr .t1 = C) (hrd : ∀ d, d + 8 ≤ 24 → InRegions (s.rd ++ s.wr) (off C d) 8)
    (hal : C.toNat % 8 = 0) (hCn : C.toNat + 24 ≤ 2 ^ 64) :
    WP isa (.block Generate.ctxHdr) s fun t =>
      (word t.mem S 32 = C ∧ word t.mem S 40 = word s.mem C 0 ∧ word t.mem S 48 = word s.mem C 8 ∧
        word t.mem S 56 = word s.mem C 16 ∧ Outside S 32 32 s.mem t.mem) ∧ Keep [.t2, .t3, .t4] s t := by
  have hn := hs.nowrap
  have h6' : s.gpr .s6 = off S 0 := by rw [h6]; simp [off]
  have h1' : s.gpr .t1 = off C 0 := by rw [h1]; simp [off]
  have cal : ∀ d, d % 8 = 0 → d < 24 → (off C d).toNat % 8 = 0 := fun d hd hd' => by
    have : (off C d).toNat = C.toNat + d := by
      simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := d) (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
    rw [this]; omega_arith
  have i32 := hs.st (d := 32) (n := 8) (by omega_arith)
  have i40 := hs.st (d := 40) (n := 8) (by omega_arith)
  have i48 := hs.st (d := 48) (n := 8) (by omega_arith)
  have i56 := hs.st (d := 56) (n := 8) (by omega_arith)
  have l32 := hs.al8 (d := 32) (by omega_arith) (by decide)
  have l40 := hs.al8 (d := 40) (by omega_arith) (by decide)
  have l48 := hs.al8 (d := 48) (by omega_arith) (by decide)
  have l56 := hs.al8 (d := 56) (by omega_arith) (by decide)
  have r0 := hrd 0 (by decide)
  have r8 := hrd 8 (by decide)
  have r16 := hrd 16 (by decide)
  have c0 := cal 0 (by decide) (by decide)
  have c8 := cal 8 (by decide) (by decide)
  have c16 := cal 16 (by decide) (by decide)
  have o0 := writeW_outside s.mem S (d := 32) C (by omega_arith)
  have o1 := writeW_outside (s.mem.writeW (off S 32) C) S (d := 40) (word s.mem C 0) (by omega_arith)
  have o2 := writeW_outside ((s.mem.writeW (off S 32) C).writeW (off S 40) (word s.mem C 0)) S (d := 48)
    (word s.mem C 8) (by omega_arith)
  have o3 := writeW_outside (((s.mem.writeW (off S 32) C).writeW (off S 40) (word s.mem C 0)).writeW
    (off S 48) (word s.mem C 8)) S (d := 56) (word s.mem C 16) (by omega_arith)
  refine WP.mono (WP.keep [.t2, .t3, .t4] (Q := fun t => t.mem =
      (((s.mem.writeW (off S 32) C).writeW (off S 40) (word s.mem C 0)).writeW (off S 48) (word s.mem C 8)).writeW
        (off S 56) (word s.mem C 16)) ?_ (by rfl) (by rfl))
    fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, kt⟩
  · unfold Generate.ctxHdr hCtx hBits hBytes hRows
    brun [h6', h1', i32, i40, i48, i56, l32, l40, l48, l56, r0, r8, r16, c0, c8, c16]
    simp only [Mont.word, off, BitVec.add_zero]
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith),
      o1.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith), o2.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm, o3.word (by omega_arith) (by omega_arith)]
    exact word_writeW_self _ _ _ _
  · rw [tm]; exact word_writeW_self _ _ _ _
  · rw [tm]
    exact (((o0.mono (by omega_arith) (by omega_arith)).trans (o1.mono (by omega_arith) (by omega_arith))).trans
      (o2.mono (by omega_arith) (by omega_arith))).trans (o3.mono (by omega_arith) (by omega_arith))

/-- The registers the front writes. -/
def cgFrontRegs : List Reg :=
  [.t0, .s6, .t2, .t3, .t4, .t1, .a3, .a5, .a0, .a2, .a4, .s7, .s8, .a1, .a7, .s5, .s10, .s11]

/-- The context's words in the header. -/
structure CH (S C : Addr) (m₀ m : Mem) : Prop where
  ctx : word m S 32 = C
  bits : word m S 40 = word m₀ C 0
  bytes : word m S 48 = word m₀ C 8
  rows : word m S 56 = word m₀ C 16

/-- `Generate.front`: `Base`, `AR`, `rand` in `t1`, the callee-saved
registers saved, the context's words in the header, and only the header
changed. -/
theorem cgFront_ok {s : State} (h : cgContract.pre s) :
    WP isa (.block Generate.front) s fun t =>
      Base (cgx s) t ∧ AR (cgx s) t ∧ t.gpr .t1 = s.gpr .a7 ∧
        (∀ i < 12, t.mem.readW (off (savW (stackArg s 1)) (8 * i)) 64 = s.gpr (PublicChecked.saved i)) ∧
        CH (stackArg s 1) (stackArg s 3) s.mem t.mem ∧
        Keep cgFrontRegs s t ∧ Outside (stackArg s 1) 0 256 s.mem t.mem := by
  obtain ⟨hrd, hwr, dXY, dXD, dXR, dXS, dXC, dXA, dYD, dYR, dYS, dYC, dYA, dDS, dRS, dSC, dSA, nwX, nwY, nwD,
    nwR, nwS, nwC, ⟨hk, hk'⟩, hL, hxl, hyl, hrl, hsl, hdv, hctx, alS, alC, alsp⟩ := h
  simp only [Spec.Rsa.scratchWords] at hsl
  simp only [cgx]
  have hA : ∀ k < 5, InRegions (s.rd ++ s.wr) (stackArgAddr s k) 8 := fun k hk => by
    refine ⟨cgStack s, List.mem_append_left _ (by rw [hrd]; simp), ?_⟩
    show (⟨s.sp + BitVec.ofNat 64 (8 * 0), 40⟩ : Region).Contains (s.sp + BitVec.ofNat 64 (8 * k)) 8
    simp only [Nat.mul_zero, add_ofNat_zero]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  have hCl : (stackArg s 4).toNat = Spec.Ffdh.generationPrecomputedWords (s.gpr .a6).toNat := hctx.1
  have hCw : 24 ≤ (stackArg s 4).toNat * 8 := by
    rw [hCl]; unfold Spec.Ffdh.generationPrecomputedWords; omega_arith
  have hrdC : ∀ d, d + 8 ≤ 24 → InRegions (s.rd ++ s.wr) (off (stackArg s 3) d) 8 := fun d hd =>
    ⟨⟨stackArg s 3, (stackArg s 4).toNat * 8⟩, List.mem_append_left _ (by rw [hrd]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  generalize hSd : stackArg s 1 = S at hwr dXS dYS dDS dRS dSC dSA nwS alS ⊢
  generalize hZd : (stackArg s 2).toNat * 8 = Z at hwr dXS dYS dDS dRS dSC dSA nwS ⊢
  have hZ : 256 + 128 * (s.gpr .a6).toNat ≤ Z := by omega_arith
  have hs : Scr s S Z := Scr.of_mem (by rw [hwr]; simp) nwS alS
  unfold Generate.front
  rw [show ([.addSp .t0 8, .load .d .t0 .t0 0, .addSp .t1 24, .load .d .t1 .t1 0] : List Instr) =
    ([.addSp .t0 8, .load .d .t0 .t0 0] : List Instr) ++ ([.addSp .t1 24, .load .d .t1 .t1 0] : List Instr) from rfl]
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (loadSk_ok s .t0 1 8 rfl (by decide) (hA 1 (by decide)) alsp)
    fun s₀ ⟨⟨a0', m0, p0⟩, k0⟩ => ?_)
  rw [hSd] at a0'
  refine WP.block_append (WP.mono (loadSk_ok s₀ .t1 3 24 rfl (by decide) (by rw [k0.2.1, k0.2.2, stackArgAddr, p0]; exact hA 3 (by decide))
    (by rw [p0]; exact alsp)) fun s₁ ⟨⟨a1', m1, p1⟩, k1⟩ => ?_)
  have e3 : stackArg s₀ 3 = stackArg s 3 := by simp only [stackArg, stackArgAddr, p0, m0]
  rw [e3] at a1'
  have k01 := k0.trans k1
  have hin : ∀ i < 12, InRegions s₁.wr (off (savW (s₁.gpr .t0)) (8 * i)) 8 := fun i hi => by
    rw [k1.gpr (by decide), a0', k01.2.2, hwr]
    show InRegions _ (S + BitVec.ofNat 64 128 + BitVec.ofNat 64 (8 * i)) 8
    rw [Offset.add_add]
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine WP.block_append (WP.mono (Pub.save_ok s₁ hin (fun i hi => by
    rw [k1.gpr (by decide), a0']; exact Pub.sav_al alS (by omega_arith) hi)) fun s₂ hS => ?_)
  have k12 := k01.trans hS.keep
  have h6₂ : s₂.gpr .s6 = S := hS.s6.trans ((k1.gpr (by decide)).trans a0')
  have h1₂ : s₂.gpr .t1 = stackArg s 3 := (hS.keep.gpr (by decide)).trans a1'
  have hm2 : Outside S 0 256 s.mem s₂.mem := fun y hy => by
    rw [← m0, ← m1]
    refine hS.frame y fun r hr hc => ?_
    rw [List.mem_singleton] at hr
    subst hr
    rw [k1.gpr (by decide), a0'] at hc
    have hc' := (Offset.sub_base (n := 96) (k := 256) S (d := 128) (by omega_arith)) _ hc
    simp only [Region.Contains] at hc'
    simp only [ofs] at hy
    omega_arith
  have hC2 : ∀ d, d + 8 ≤ 24 → word s₂.mem (stackArg s 3) d = word s.mem (stackArg s 3) d := fun d hd =>
    Pub.Outside.word_apart (P := stackArg s 3) (Zp := (stackArg s 4).toNat * 8) (Z := Z) (d := d) hm2
      (fun y hy => Pub.sep_of_disjoint dSC.symm y hy) (by omega_arith) (by omega_arith) nwC
  refine WP.block_append (WP.mono (ctxHdr_ok (hs.congr k12.2.2) (by omega_arith) h6₂ h1₂
    (fun d hd => by rw [k12.2.1, k12.2.2]; exact hrdC d hd) alC (by omega_arith))
    fun s₃ ⟨⟨c32, c40, c48, c56, o3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.block_append (WP.mono (ghdr_ok (hs.congr k13.2.2) (by omega_arith) ((k3.gpr (by decide)).trans h6₂))
    fun s₄ ⟨⟨w0, w8, w16, w24, b1, b3, b5, b0, b2, b4, b6, b7, b8, ba1, o4⟩, k4⟩ => ?_)
  have k14 := k13.trans k4
  refine WP.mono (Pub.setup_ok (O := s.gpr .a2) (k := (s.gpr .a6).toNat) (b0.trans (k13.gpr (by decide)))
    (by rw [ba1, k13.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq])
    ((k4.gpr (by decide)).trans ((k3.gpr (by decide)).trans h6₂)) hk') fun t ⟨⟨j10, j11, j0, j5, j7, jm⟩, k5⟩ => ?_
  have k := k14.trans k5
  have hrdt : t.rd ++ t.wr = s.rd ++ s.wr := by rw [k.2.1, k.2.2]
  have hO : Outside S 0 256 s.mem t.mem := by
    rw [jm]
    exact (hm2.trans (o3.mono (by omega_arith) (by omega_arith))).trans (o4.mono (Nat.le_refl _) (by omega_arith))
  have hOZ : Outside S 0 Z s.mem t.mem := hO.mono (Nat.le_refl _) (by omega_arith)
  have hb : ∀ (Q : Addr) n, (∀ i < n, ∀ y, ofs S y < Z → off Q i ≠ y) →
      Spec.Rsa.bytesAt t.mem Q n = Spec.Rsa.bytesAt s.mem Q n := fun Q n hsep =>
    Pub.bytes_apart (o := 0) (n := Z) hOZ (by omega_arith) hsep
  have hw4 : ∀ d, d + 8 ≤ 32 → word t.mem S d = word s₄.mem S d := fun d _ => by rw [jm]
  have hw3 : ∀ d, 32 ≤ d → d + 8 ≤ 64 → word t.mem S d = word s₃.mem S d := fun d h1 h2 => by
    rw [jm]; exact o4.word (Or.inr (by omega_arith)) (by omega_arith)
  have hLk : 2 * (s.gpr .a6).toNat ≤ (s.gpr .a5).toNat ∧ (s.gpr .a5).toNat ≤ 3 * (s.gpr .a6).toNat := by
    simp only [Spec.Ffdh.domainLenValid] at hL; omega_arith
  have sepD := Pub.ne_of_disjoint dDS (Nat.le_of_lt (s.gpr .a5).isLt)
  have rdD : ∀ i < (s.gpr .a5).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a4) i) 1 := by
    rw [hrdt]; exact rd_of_mem (by rw [hrd]; simp) (Nat.le_refl _) (BitVec.isLt _)
  have rdX : ∀ i < (s.gpr .a6).toNat, InRegions (t.rd ++ t.wr) (off (s.gpr .a0) i) 1 := fun i hi => by
    rw [hrdt]
    exact ⟨⟨s.gpr .a0, (s.gpr .a1).toNat⟩, List.mem_append_right _ (by rw [hwr]; simp),
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩
  refine ⟨⟨⟨hs.congr k.2.2, hk, hk', hLk, ?_, by rw [← hyl]; exact nwY, fun i hi => ⟨⟨s.gpr .a2, (s.gpr .a3).toNat⟩,
      by rw [k.2.2, hwr]; simp, Offset.contains_base _ (by change i < (s.gpr .a6).toNat at hi; omega_arith)
        (by change i < (s.gpr .a6).toNat at hi; omega_arith)⟩,
      fun y hy => Pub.sep_of_disjoint dYS y (by rw [hyl]; exact hy),
      rdD, sepD, fun i hi => by rw [Derive.off_off]; exact rdD _ (by change i < (s.gpr .a6).toNat at hi; omega_arith),
      fun i hi => by rw [Derive.off_off]; exact sepD _ (by change i < (s.gpr .a6).toNat at hi; omega_arith),
      rdX, fun i hi => Pub.ne_of_disjoint dXS (Nat.le_of_lt (s.gpr .a1).isLt) i
        (by change i < (s.gpr .a6).toNat at hi; omega_arith), by change 1 ≤ (s.gpr .a6).toNat; omega_arith, Nat.le_refl _,
      (by rw [hb _ _ sepD]), ?_, ?_, ?_, ?_⟩,
    by rw [k5.gpr (by decide), k4.gpr (by decide), k3.gpr (by decide)]; exact h6₂, j7,
    by rw [j5, Nat.mul_add], j0, by rw [k5.gpr (by decide), b7, k13.gpr (by decide)]; simp [off],
    by rw [k5.gpr (by decide), b8, k13.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
    by rw [j10]; simp [off], j11⟩,
    ⟨by rw [k5.gpr (by decide), b2, k13.gpr (by decide)],
      by rw [k5.gpr (by decide), b3, k13.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [k5.gpr (by decide), b4, k13.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq],
      by rw [k5.gpr (by decide), b5, k13.gpr (by decide)],
      by rw [k5.gpr (by decide), b6, k13.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩,
    by rw [k5.gpr (by decide), b1, k13.gpr (by decide)], ?_,
    ⟨by rw [hw3 32 (by decide) (by decide), c32], by rw [hw3 40 (by decide) (by decide), c40, hC2 0 (by decide)],
      by rw [hw3 48 (by decide) (by decide), c48, hC2 8 (by decide)],
      by rw [hw3 56 (by decide) (by decide), c56, hC2 16 (by decide)]⟩, k.mono (by decide), hO⟩
  · show slot (((s.gpr .a6).toNat + 7) / 8) 24 ≤ Z
    unfold slot hdrBytes; omega_arith
  · rw [hw4 0 (by decide), w0, k13.gpr (by decide)]; simp [off]
  · rw [hw4 8 (by decide), w8, k13.gpr (by decide)]; simp [off]
  · rw [hw4 16 (by decide), w16, k13.gpr (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [hw4 24 (by decide), w24, k13.gpr (by decide), k13.gpr (by decide)]; simp [off]
  · intro i hi
    have e : off (savW S) (8 * i) = off S (128 + 8 * i) := by rw [off, off, Offset.add_add]
    rw [e]
    show word t.mem S (128 + 8 * i) = _
    rw [jm, o4.word (Or.inr (by omega_arith)) (by omega_arith), o3.word (Or.inr (by omega_arith)) (by omega_arith)]
    show s₂.mem.readW (off S (128 + 8 * i)) 64 = _
    have hne1 : ∀ i < 12, PublicChecked.saved i ≠ .t1 := by decide
    rw [← e, ← (k1.gpr (by decide)).trans a0', hS.saved i hi, k1.gpr fun h => hne1 i hi (by simpa using h),
      k0.gpr fun h => Pub.saved_ne_t0 i hi (List.mem_singleton.mp h)]

end VG.Proof.Ffdh.RISCV64.Cached
