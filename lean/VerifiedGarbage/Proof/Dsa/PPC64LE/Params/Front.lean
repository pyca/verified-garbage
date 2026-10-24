module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Params
public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.FrameOutside
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run

/-!
# DSA domain checks on PPC64LE: the contract on the registers, and the entry

`pcContract`: `vg_dsa_check_parameters(params = r3, params_len = r4,
p_len = r5, q_len = r6, scratch = r7, scratch_len = r8)`. `pfront_ok`:
`entry` saves the nonvolatile registers in `scratch`'s header, and keeps the
domain and the lengths in registers (`Regs`, with the signature and the
digest 0, and `r2`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- `vg_dsa_check_parameters`, on the registers. -/
def pcContract : Contract isa where
  pre s :=
    let ps : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let scr : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩
    s.rd = [ps] ∧ s.wr = [scr] ∧ ps.Disjoint scr ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = 2 * (s.gpr .r5).toNat + (s.gpr .r6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r8).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = if Spec.Dsa.checkParametersBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat).map (·.toNat)

/-- A call's layout. -/
def playOf (s : State) : Lay := ⟨s.gpr .r7, (s.gpr .r8).toNat * 8, (s.gpr .r5).toNat, (s.gpr .r6).toNat⟩

/-- The layout of a call with `scratch` in `r7` and `r8`, and the lengths in `r5` and `r6`. -/
theorem playOf_ok_of {s : State} (nw : (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64)
    (hv : Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat)
    (hsw : Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (s.gpr .r8).toNat) : (playOf s).Ok := by
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [playOf]; omega, by simp only [playOf]; omega, by simp only [playOf]; omega, nw⟩

theorem playOf_ok {s : State} (h : pcContract.pre s) : (playOf s).Ok :=
  playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- The lengths into `r2`. -/
theorem pack_entry0 (x y : BitVec 64) (hx : x.toNat < 2 ^ 16) (hy : y.toNat < 2 ^ 16) :
    x + y <<< 16 = pack x.toNat y.toNat 0 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat hx hy (by decide) (by decide)]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [Nat.reducePow] at *
  omega

/-- The registers `entry` writes. -/
def pentryRegs : List Reg := [.r0, .r2, .r11, .r21, .r26, .r27, .r28]

theorem pfront_saved_ne11 : ∀ i < 19, saved i ≠ .r11 := by decide

/-- `entry`: `scratch` into `r21`, the nonvolatile registers saved in its
header, and the domain and the lengths into registers (`Regs`, `r2`). Memory
changes only in the header. -/
theorem pfront_ok_of {s : State} (hL : (playOf s).Ok) (hwr : s.wr = [⟨s.gpr .r7, (s.gpr .r8).toNat * 8⟩])
    (nw : (s.gpr .r7).toNat + (s.gpr .r8).toNat * 8 ≤ 2 ^ 64) :
    WP isa (.block Params.entry) s fun t =>
      (Regs t (playOf s) (s.gpr .r3) 0 0 ∧ ScrL t (playOf s) ∧
        t.gpr .r2 = pack (playOf s).pl (playOf s).ql 0 0 ∧
        (∀ i < 19, word t.mem (s.gpr .r7) (saveOff i) = s.gpr (saved i)) ∧
        Outside (s.gpr .r7) 0 256 s.mem t.mem) ∧ Keep pentryRegs s t := by
  have hZ := hL.z256
  have hpl : (s.gpr .r5).toNat < 2 ^ 16 := by have := hL.pl; simp only [playOf] at this; omega
  have hql : (s.gpr .r6).toNat < 2 ^ 16 := by have := hL.ql; simp only [playOf] at this; omega
  unfold Params.entry
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = s.gpr .r7 ∧ u.mem = s.mem)
    (by prun [BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a11, m1⟩, k1⟩ => ?_)
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (playOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [playOf]) nw
  have hin : ∀ i < 19, InRegions s₁.wr (off (savW (s₁.gpr .r11)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq, a11]
    exact (hscr s₁ k1.wr).st (d := 104 + 8 * i) (by simp only [playOf] at hZ ⊢; omega)
  refine WP.block_append (WP.mono (save_ok s₁ hin) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have h21 : s₂.gpr .r21 = s.gpr .r7 := hS.r21.trans a11
  have e : ∀ r, r ≠ .r11 → r ≠ .r21 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr r fun hm => by
      simp only [List.mem_append, List.mem_singleton] at hm
      exact hm.elim h1 h2
  have e3 := e .r3 (by decide) (by decide)
  have e5 := e .r5 (by decide) (by decide)
  have e6 := e .r6 (by decide) (by decide)
  refine WP.mono (WP.keep [.r27, .r28, .r26, .r0, .r2] (Q := fun t => t.gpr .r27 = s.gpr .r3 ∧
      t.gpr .r28 = 0 ∧ t.gpr .r26 = 0 ∧ t.gpr .r2 = pack (s.gpr .r5).toNat (s.gpr .r6).toNat 0 0 ∧
      t.mem = s₂.mem) (by prun [e3, e5, e6, BitVec.add_zero, pack_entry0 _ _ hpl hql]; all_goals rfl) (by decide))
    fun t ⟨⟨t27, t28, t26, t2, mt⟩, kt⟩ => ?_
  have k := k12.trans kt
  have t21 : t.gpr .r21 = s.gpr .r7 := (kt.gpr .r21 (by decide)).trans h21
  refine ⟨⟨Regs.of_pack hL t21 t27 t28 t26 t2 (by decide) (by decide), hscr t k.wr, t2, fun i hi => ?_, ?_⟩,
    k.mono (by decide)⟩
  · rw [mt]
    show s₂.mem.readW (s.gpr .r7 + BitVec.ofNat 64 (104 + 8 * i)) 64 = _
    rw [saveOff_eq, ← a11, hS.saved i hi]
    exact k1.gpr _ fun h => pfront_saved_ne11 i hi (List.mem_singleton.mp h)
  · have f2 : Outside (s.gpr .r7) 104 152 s₁.mem s₂.mem :=
      VG.Proof.Bignum.frame_outside (by rw [← a11]; exact hS.frame) (by decide)
    rw [mt, ← m1]
    exact f2.mono (Nat.zero_le _) (by decide)

theorem pfront_ok {s : State} (h : pcContract.pre s) :
    WP isa (.block Params.entry) s fun t =>
      (Regs t (playOf s) (s.gpr .r3) 0 0 ∧ ScrL t (playOf s) ∧
        t.gpr .r2 = pack (playOf s).pl (playOf s).ql 0 0 ∧
        (∀ i < 19, word t.mem (s.gpr .r7) (saveOff i) = s.gpr (saved i)) ∧
        Outside (s.gpr .r7) 0 256 s.mem t.mem) ∧ Keep pentryRegs s t :=
  pfront_ok_of (playOf_ok h) h.2.1 h.2.2.2.2.1

end VG.Proof.Dsa.PPC64LE
