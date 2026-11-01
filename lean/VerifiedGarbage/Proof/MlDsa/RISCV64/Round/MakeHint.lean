module

import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.HighLow
public import VerifiedGarbage.Proof.MlDsa.Round.Ones
import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
import VerifiedGarbage.Proof.Framework.RISCV64.Run
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Bits
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.HighLow
meta import VerifiedGarbage.Proof.MlDsa.Round.Ones
meta import VerifiedGarbage.Proof.MlKem.RISCV64.Add
meta import VerifiedGarbage.Proof.MlDsa.RISCV64.Arith.Common
meta import VerifiedGarbage.Proof.Framework.RISCV64.Run
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.Steps
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import Init.Data.Nat.Bitwise.Basic
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.RISCV64.Common
public import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.MlDsa.RISCV64.Round.Arith
public import VerifiedGarbage.Proof.MlDsa.Round.Mem
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.RISCV64.Target

/-!
# ML-DSA on RISC-V: `vg_mldsa_make_hint`

As PPC64LE's (`Proof/MlDsa/PPC64LE/Round/MakeHint.lean`), with the count in `t4`.

The selection of `γ₂` (`sel_ok'`), then the loop for it: one symbolic
execution of its body for any pointers (`body_ok`), which stores `r₁` of
`r` to `h[i]`, reads it back and stores whether it differs from `r₁` of
`r + z mod q` (`mhBit`, `mh_val`, through `makeHint_eq`), and adds that to
the count in `r0`. The invariant says which coefficients of `h` are done and
counts their 1s (`onesTo`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round.MakeHint

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Impl.MlKem.RISCV64 (fixup)
open VG.Impl.MlDsa.RISCV64.Arith (loadImm)
open VG.Spec.MlDsa
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_writeW coeffAt_writeW_disjoint coeffAt_frame
  zipWith_get makeHint_eq mem_gamma2s hbF hbM hintIs_of_toNat onesTo onesTo_succ hintOnes_onesTo reduced_zero)
open VG.Proof.MlDsa.RISCV64.Round
open VG.Proof.MlDsa.RISCV64.Round.Bits (dMul_lt kgpr selGpr sel_ok' sel_ct consts_ok)
open VG.Proof.MlKem.RISCV64 (wp_loop_nz count_sub count_nz ptr_succ align4_add)
open VG.Proof.MlDsa.RISCV64.Arith (loadImm_q)

/-! ## Values -/

/-- What the body computes from `a` (of `r`), `b` (of `z`) and `h1` (`r₁`
of `a`, read back): whether `r₁` of `a + b mod q` differs from `h1`. -/
def mhBit (g : Nat) (a b h1 : BitVec 64) : BitVec 64 :=
  ((hbv g (fixk 8380417 (a + b - 8380417)) ^^^ h1) + 63) >>> 6

theorem xor_bit {u v : BitVec 64} (hu : u.toNat < 64) (hv : v.toNat < 64) :
    ((u ^^^ v) + 63) >>> 6 = if u = v then 0 else 1 := by
  have hx : (u ^^^ v).toNat < 64 := by rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow (n := 6) hu hv
  split <;> rename_i h
  · subst h; rw [BitVec.xor_self]; decide
  · have : u ^^^ v ≠ 0#64 := fun e => h (BitVec.xor_eq_zero_iff.mp e)
    bv_omega

theorem mh_val {g : Nat} (hg : g ∈ gamma2s) {a b : BitVec 64} (ha : a.toNat < q) (hb : b.toNat < q) :
    mhBit g a b (((hbv g a).setWidth 32).setWidth 64) =
      BitVec.ofNat 64 (decide (hbF g a.toNat % hbM g ≠ hbF g ((a.toNat + b.toNat) % q) % hbM g)).toNat := by
  have ha' := hbv_lt hg ha
  have e1 : ((hbv g a).setWidth 32).setWidth 64 = hbv g a := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hs : (fixk 8380417 (a + b - 8380417)).toNat = (a.toNat + b.toNat) % q := by
    rw [VG.Proof.MlDsa.Round.q_eq] at ha hb ⊢
    have := fixk_sub (k := 8380417) (by decide) (by decide) (x := a + b) (by bv_omega)
    rw [show (8380417 : BitVec 64) = BitVec.ofNat 64 8380417 from rfl, this, BitVec.toNat_add,
      Nat.mod_eq_of_lt (by omega : a.toNat + b.toNat < 2 ^ 64)]
  have hsq : (fixk 8380417 (a + b - 8380417)).toNat < q := by rw [hs]; exact Nat.mod_lt _ (by decide)
  unfold mhBit
  rw [e1, xor_bit (hbv_lt hg hsq) ha']
  have iff : hbv g (fixk 8380417 (a + b - 8380417)) = hbv g a ↔
      hbF g ((a.toNat + b.toNat) % q) % hbM g = hbF g a.toNat % hbM g := by
    rw [BitVec.toNat_eq, hbv_toNat hg hsq, hbv_toNat hg ha, hs]
  by_cases hc : hbF g a.toNat % hbM g = hbF g ((a.toNat + b.toNat) % q) % hbM g
  · rw [ite_eq_left (iff.mpr hc.symm), decide_eq_false (fun h' => h' hc)]; rfl
  · rw [ite_eq_right (fun e => hc (iff.mp e).symm), decide_eq_true hc]; rfl

/-! ## The loop body -/

/-- `r₁` of the coefficient at `y`, as stored. -/
def h1v (g : Nat) (m : Mem) (y : Addr) : BitVec 32 := (hbv g ((m.readW y 32).setWidth 64)).setWidth 32

/-- What an iteration does, for the memory `m1` after the first store and the
bit `v` stored. -/
def Step (s : State) (x y w c : BitVec 64) (m1 : Mem) (v : BitVec 64) (s' : State) : Prop :=
  s'.gpr .a0 = x + 4 ∧ s'.gpr .a1 = y + 4 ∧ s'.gpr .a3 = w + 4 ∧ s'.gpr .t3 = c - 1 ∧
    s'.gpr .t4 = s.gpr .t4 + v ∧ (∀ r ∈ [Reg.a2, .a7, .t1, .t2], s'.gpr r = s.gpr r) ∧
    s'.mem = m1.writeW w (v.setWidth 32) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
    s'.gpr .ra = s.gpr .ra ∧
    ∀ r ∈ preserved, s'.gpr r = s.gpr r

section
variable {g : Nat} {s : State} {x y w c : BitVec 64} (h3 : s.gpr .a0 = x) (h4 : s.gpr .a1 = y)
  (h6 : s.gpr .a3 = w) (h7 : s.gpr .t3 = c) (h5 : s.gpr .a2 = 8380417)
  (h10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)) (h11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g))
  (h12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g))
  (ix : InRegions (s.rd ++ s.wr) x 4) (iy : InRegions (s.rd ++ s.wr) y 4) (iw : InRegions (s.rd ++ s.wr) w 4)
  (ow : InRegions s.wr w 4) (ax : x.toNat % 4 = 0) (ay : y.toNat % 4 = 0) (aw : w.toNat % 4 = 0)
include h3 h4 h6 h7 h5 h10 h11 h12 ix iy iw ow ax ay aw

theorem body_ok :
    WP isa (.block (mhBody g)) s (Step s x y w c (s.mem.writeW w (h1v g s.mem y))
      (mhBit g (((s.mem.writeW w (h1v g s.mem y)).readW y 32).setWidth 64)
        (((s.mem.writeW w (h1v g s.mem y)).readW x 32).setWidth 64)
        (((s.mem.writeW w (h1v g s.mem y)).readW w 32).setWidth 64))) := by
  have hS := dShift_lt g
  crun [mhBody, hb, hbRaw, fixup, Step, mhBit, h1v, hbv, hbr, fixk, h3, h4, h5, h6, h7, h10, h11, h12,
    ix, iy, iw, ow, ax, ay, aw, hS, preserved,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, List.cons_append, List.nil_append]
  simp [Mem.writeW, Mem.readW, Mem.read]

end

/-! ## The loop -/

section
variable (s₀ : State)

abbrev Z : Addr := s₀.gpr .a0
abbrev Rp : Addr := s₀.gpr .a1
abbrev G : BitVec 32 := (s₀.gpr .a2).setWidth 32
abbrev H : Addr := s₀.gpr .a3

/-- The hint. -/
def hint (g : Nat) : Vector Bool n := Vector.zipWith (makeHint g) (polyAt s₀.mem (Z s₀)) (polyAt s₀.mem (Rp s₀))

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [pR (Z s₀), pR (Rp s₀)]
  wr : s₀.wr = [pR (H s₀)]
  dz : (pR (Z s₀)).Disjoint (pR (H s₀))
  dr : (pR (Rp s₀)).Disjoint (pR (H s₀))
  fitZ : (Z s₀).toNat + 1024 ≤ 2 ^ 64
  fitR : (Rp s₀).toNat + 1024 ≤ 2 ^ 64
  fitH : (H s₀).toNat + 1024 ≤ 2 ^ 64
  g : (G s₀).toNat ∈ gamma2s
  redZ : Reduced s₀.mem (Z s₀)
  redR : Reduced s₀.mem (Rp s₀)
  alZ : (Z s₀).toNat % 4 = 0
  alR : (Rp s₀).toNat % 4 = 0
  alH : (H s₀).toNat % 4 = 0

/-- After `i` iterations. -/
structure Inv (g : Nat) (s₀ : State) (i : Nat) (s : State) : Prop where
  r3 : s.gpr .a0 = Z s₀ + BitVec.ofNat 64 (4 * i)
  r4 : s.gpr .a1 = Rp s₀ + BitVec.ofNat 64 (4 * i)
  r6 : s.gpr .a3 = H s₀ + BitVec.ofNat 64 (4 * i)
  r7 : s.gpr .t3 = BitVec.ofNat 64 (256 - i)
  r0 : s.gpr .t4 = BitVec.ofNat 64 (onesTo (hint s₀ g) i)
  r5 : s.gpr .a2 = 8380417
  r10 : s.gpr .a7 = BitVec.ofNat 64 (dMul g)
  r11 : s.gpr .t1 = BitVec.ofNat 64 (dAdd g)
  r12 : s.gpr .t2 = BitVec.ofNat 64 (dMod g)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  lr : s.gpr .ra = s₀.gpr .ra
  pres : ∀ r ∈ preserved, s.gpr r = s₀.gpr r
  frame : Frame [pR (H s₀)] s₀.mem s.mem
  coeff : ∀ j < 256, j < i → coeffAt s.mem (H s₀) j = BitVec.ofNat 32 (hint s₀ g)[j]!.toNat

theorem bit_val {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) :
    mhBit g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64) ((coeffAt s₀.mem (Z s₀) i).setWidth 64)
      (((hbv g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64)).setWidth 32).setWidth 64) =
      BitVec.ofNat 64 (hint s₀ g)[i]!.toNat := by
  obtain ⟨ea, ha⟩ := HighLow.load_toNat hp.redR hi
  obtain ⟨eb, hb⟩ := HighLow.load_toNat hp.redZ hi
  rw [mh_val hg ha hb, hint, zipWith_get _ _ _ hi, makeHint_eq hg, ea, eb, Nat.add_comm]

theorem inv_step {g : Nat} (hg : g ∈ gamma2s) {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 256) {s : State}
    (h : Inv g s₀ i s) :
    WP isa (.block (mhBody g)) s fun s' => Inv g s₀ (i + 1) s' ∧ (s'.gpr .t3 != 0) = decide (i + 1 ≠ 256) := by
  have cZ := coeff_contains (Z s₀) (i := i) hi
  have cR := coeff_contains (Rp s₀) (i := i) hi
  have cH := coeff_contains (H s₀) (i := i) hi
  have hd : ∀ {p : Addr}, (pR p).Disjoint (pR (H s₀)) → ∀ r ∈ [pR (H s₀)], (pR p).Disjoint r :=
    fun hd r hr => by rw [List.mem_singleton] at hr; subst hr; exact hd
  -- the reads after the first store, as on entry
  have eR : (s.mem.writeW (H s₀ + BitVec.ofNat 64 (4 * i)) (h1v g s.mem (Rp s₀ + BitVec.ofNat 64 (4 * i)))).readW
      (Rp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Rp s₀) i :=
    (coeffAt_writeW_disjoint s.mem hp.dr cH hi _).trans (coeffAt_frame h.frame (hd hp.dr) hi)
  have eZ : (s.mem.writeW (H s₀ + BitVec.ofNat 64 (4 * i)) (h1v g s.mem (Rp s₀ + BitVec.ofNat 64 (4 * i)))).readW
      (Z s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Z s₀) i :=
    (coeffAt_writeW_disjoint s.mem hp.dz cH hi _).trans (coeffAt_frame h.frame (hd hp.dz) hi)
  have eH : (s.mem.writeW (H s₀ + BitVec.ofNat 64 (4 * i)) (h1v g s.mem (Rp s₀ + BitVec.ofNat 64 (4 * i)))).readW
      (H s₀ + BitVec.ofNat 64 (4 * i)) 32 = (hbv g ((coeffAt s₀.mem (Rp s₀) i).setWidth 64)).setWidth 32 := by
    rw [Mem.readW_writeW_self32, h1v, show s.mem.readW (Rp s₀ + BitVec.ofNat 64 (4 * i)) 32 = coeffAt s₀.mem (Rp s₀) i
      from coeffAt_frame h.frame (hd hp.dr) hi]
  have hv := bit_val hg hp hi
  rw [← eH, ← eR, ← eZ] at hv
  refine WP.mono (body_ok h.r3 h.r4 h.r6 h.r7 h.r5 h.r10 h.r11 h.r12 ?_ ?_ ?_ ?_ (align4_add hp.alZ i)
      (align4_add hp.alR i) (align4_add hp.alH i))
    fun s' ⟨r3, r4, r6, r7, r0, kp, m, rd, wr, sp, lr, pres⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_,
      (kp .a2 (by simp)).trans h.r5, (kp .a7 (by simp)).trans h.r10, (kp .t1 (by simp)).trans h.r11,
      (kp .t2 (by simp)).trans h.r12, rd.trans h.rd, wr.trans h.wr, sp.trans h.sp, lr.trans h.lr,
      fun r hr => (pres r hr).trans (h.pres r hr), ?_, ?_⟩, ?_⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cZ⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨_, by simp, cR⟩
  · rw [h.rd, h.wr, hp.rd, hp.wr]; exact ⟨pR (H s₀), by simp, cH⟩
  · rw [h.wr, hp.wr]; exact ⟨_, by simp, cH⟩
  · rw [r3]; exact ptr_succ _ 4 i
  · rw [r4]; exact ptr_succ _ 4 i
  · rw [r6]; exact ptr_succ _ 4 i
  · rw [r7]; exact count_sub hi
  · rw [r0, h.r0, hv, onesTo_succ, BitVec.ofNat_add]
  · rw [m]
    exact (h.frame.writeW (List.mem_singleton_self _) _ cH).writeW (List.mem_singleton_self _) _ cH
  · intro j hj hji
    rw [m, hv, show H s₀ + BitVec.ofNat 64 (4 * i) = coeffAddr (H s₀) i from rfl, coeffAt_writeW _ _ hj hi]
    by_cases e : i = j
    · subst e; rw [ite_eq_left rfl]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      cases (hint s₀ g)[i]! <;> rfl
    · rw [ite_eq_right e, coeffAt_writeW _ _ hj hi, ite_eq_right e]; exact h.coeff j hj (by omega)
  · rw [r7, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, count_sub hi]; exact count_nz hi (by decide)

/-! ## The function -/

/-- What the function leaves. -/
def Post (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.sp = s₀.sp ∧ s.gpr .ra = s₀.gpr .ra ∧
    (∀ j < 256, coeffAt s.mem (H s₀) j = BitVec.ofNat 32 (hint s₀ (G s₀).toNat)[j]!.toNat) ∧
    s.gpr .a0 = BitVec.ofNat 64 (onesTo (hint s₀ (G s₀).toNat) 256)

theorem exit_ok {s₀ s : State} {g : Nat} (hG : (G s₀).toNat = g) (h : Inv g s₀ 256 s) :
    WP isa (.block [.addi .a0 .t4 0]) s (Post s₀) := by
  subst hG
  refine Steps.WP.cons (exec_addi (by decide)) (WP.block_nil ⟨?_, h.sp, ?_, fun j hj => h.coeff j hj hj, ?_⟩)
  · intro r hr
    have : ¬r = .a0 := by revert r hr; decide
    rw [RegUpd.gpr_write_of_ne _ _ this]; exact h.pres r hr
  · rw [RegUpd.gpr_write_of_ne _ _ (by decide)]; exact h.lr
  · rw [RegUpd.gpr_write_self, show ∀ x : BitVec 64, x + BitVec.ofInt 64 0 = x from fun x => by simp]; exact h.r0

theorem correct {s₀ : State} (hp : Pre s₀) : WP isa makeHint s₀ (Post s₀) := by
  refine sel_ok' (rg := .a2) (by decide) hp.g fun g hg hG s hgpr hm hrd hwr hsp => ?_
  have e : (if g = g32 then mhLoop g32 else mhLoop g88) = mhLoop g := by
    rcases mem_gamma2s hg with rfl | rfl <;> rfl
  rw [e]
  unfold mhLoop
  simp only [loadQ, loadImm_q]
  refine WP.seq (consts_ok (Steps.WP.cons exec_lui (Steps.WP.cons (exec_addi (by decide))
    (Steps.WP.cons (exec_li (by decide)) (Steps.WP.cons (exec_li (by decide)) (WP.block_nil ?_))))))
  refine WP.seq (wp_loop_nz (Inv g s₀) (N := 256) (by decide) (fun i hi s h => inv_step hg hp hi h)
    (fun s h => exit_ok hG h) ?_)
  have e7 : sext32 ((0x7FE : BitVec 20) ++ (0 : BitVec 12)) + BitVec.ofInt 64 1 = 8380417 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrd, hwr, hsp, ?_, fun r hr => ?_,
    by rw [show _ = s.mem from rfl, hm]; exact Frame.refl _ _, fun j _ h => absurd h (by omega)⟩
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · simp [State.write]
  · simp [State.write, onesTo]
  · simp only [State.write, ite_true, ite_false, reduceCtorEq]; exact e7
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr]
  · simp [State.write, kgpr, hgpr, selGpr]
  · have : r ≠ .t0 ∧ r ≠ .a2 ∧ r ≠ .a4 ∧ r ≠ .t3 ∧ r ≠ .t4 ∧ r ≠ .a7 ∧ r ≠ .t1 ∧ r ≠ .t2 := by
      revert r hr; decide
    simp [State.write, kgpr, hgpr, selGpr, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1,
      this.2.2.2.2.2.1, this.2.2.2.2.2.2.1, this.2.2.2.2.2.2.2]

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.makeHintContract RISCV64.abi).pre s) : Pre s := by
  sig_pre [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, RISCV64.abi, RISCV64.argRegs] at h
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem onesTo_le (h : Vector Bool n) (i : Nat) : onesTo h i ≤ i := by
  unfold onesTo
  exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .a0 => 0x1000 | .a1 => 0x2000 | .a2 => 95232 | .a3 => 0x3000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem verified : Verified RISCV64.target makeHint (Spec.MlDsa.makeHintContract RISCV64.abi) := by
  refine ⟨fun s hs => ?_, sel_ct (rg := .a2) (by decide) [.a0, .a1, .a3] (by decide) (fun s₁ s₂ h => ?_)
    (by taint_decide) (by taint_decide) (by taint_decide), ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, h⟩ := correct hp
    refine ⟨t, s', he, ⟨h.1, h.2.1, h.2.2.1⟩, ?_⟩
    sig_post [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, RISCV64.abi, RISCV64.argRegs]
    refine ⟨hintIs_of_toNat fun j hj => ?_, ?_⟩
    · rw [h.2.2.2.1 j hj]; rfl
    · rw [h.2.2.2.2, hintOnes_onesTo, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      have := onesTo_le (hint s (G s).toNat) 256
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      rfl
  · sig_pub [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, RISCV64.abi, RISCV64.argRegs] at h
    refine ⟨fun r hr => ?_, h.1, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.2
    · exact h.2.2.2.1
  · refine ⟨satState, ?_⟩
    sig_apply_check
    · decide +kernel
    · sig_reduce [Spec.MlDsa.makeHintContract, Spec.MlDsa.makeHintSig, RISCV64.abi, RISCV64.argRegs]
      sig_and_intros
      all_goals first
        | trivial
        | exact reduced_zero _
        | decide +kernel

end VG.Proof.MlDsa.RISCV64.Round.MakeHint
