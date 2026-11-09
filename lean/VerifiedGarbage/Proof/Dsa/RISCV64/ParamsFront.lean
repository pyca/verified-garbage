module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Save
public import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Impl.Dsa.RISCV64.Params
public import VerifiedGarbage.Spec.Dsa.Derive
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA domain checks on RISC-V: the contract on the registers, and the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/Params/Front.lean`). `pcContract`:
`vg_dsa_check_parameters(params = a0, params_len = a1, p_len = a2,
q_len = a3, scratch = a4, scratch_len = a5)`. `pfront_ok`: `entry` saves the
callee-saved registers and `ra` in `scratch`'s header, keeps the domain in
`s11` (`ra`, the signature elsewhere, 0) and the lengths in the header.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

/-- `vg_dsa_check_parameters`, on the registers. -/
def pcContract : Contract isa where
  pre s :=
    let ps : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let scr : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩
    s.rd = [ps] ∧ s.wr = [scr] ∧ ps.Disjoint scr ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a2).toNat (s.gpr .a3).toNat ∧
      (s.gpr .a1).toNat = 2 * (s.gpr .a2).toNat + (s.gpr .a3).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .a2).toNat ≤ (s.gpr .a5).toNat ∧
      (s.gpr .a4).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = if Spec.Dsa.checkParametersBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat).map (·.toNat) =
        (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat).map (·.toNat)

/-- A call's layout. -/
def playOf (s : State) : Lay := ⟨s.gpr .a4, (s.gpr .a5).toNat * 8, (s.gpr .a2).toNat, (s.gpr .a3).toNat⟩

/-- The layout of a call with `scratch` in `a4` and `a5`, and the lengths in `a2` and `a3`. -/
theorem playOf_ok_of {s : State} (nw : (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64)
    (hv : Spec.Dsa.lengthsValid (s.gpr .a2).toNat (s.gpr .a3).toNat)
    (hsw : Spec.Dsa.scratchWords (s.gpr .a2).toNat ≤ (s.gpr .a5).toNat) : (playOf s).Ok := by
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [playOf]; omega, by simp only [playOf]; omega, by simp only [playOf]; omega, nw⟩

theorem playOf_ok {s : State} (h : pcContract.pre s) : (playOf s).Ok :=
  playOf_ok_of h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1

/-- The lengths. -/
theorem pack_entry0 (x y : BitVec 64) (hx : x.toNat < 2 ^ 16) (hy : y.toNat < 2 ^ 16) :
    x + y <<< 16 = pack x.toNat y.toNat 0 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat hx hy (by decide) (by decide)]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  simp only [Nat.reducePow] at *
  omega

/-- The registers `entry` writes. -/
def pentryRegs : List Reg := [.t2, .s6, .s11, .ra, .t3]

/-- What `Params.entry` leaves. -/
structure PFront (s t : State) : Prop where
  regs : Regs t (playOf s) (s.gpr .a0) 0
  scr : ScrL t (playOf s)
  lens : word t.mem (s.gpr .a4) hLens = pack (playOf s).pl (playOf s).ql 0 0
  sav : ∀ i < 13, word t.mem (s.gpr .a4) (saveOff i) = s.gpr (saved i)
  out : Outside (s.gpr .a4) 0 256 s.mem t.mem

/-- `entry`: `scratch` into `s6`, the callee-saved registers and `ra` saved in
its header, the domain into `s11`, `ra := 0` and the lengths into the
header. Memory changes only in the header. -/
theorem pfront_ok_of {s : State} (hL : (playOf s).Ok) (hwr : s.wr = [⟨s.gpr .a4, (s.gpr .a5).toNat * 8⟩])
    (nw : (s.gpr .a4).toNat + (s.gpr .a5).toNat * 8 ≤ 2 ^ 64) (alS : (s.gpr .a4).toNat % 8 = 0) :
    WP isa (.block Params.entry) s fun t => PFront s t ∧ Keep pentryRegs s t := by
  have hZ := hL.z256
  have hpl : (s.gpr .a2).toNat < 2 ^ 16 := by have := hL.pl; simp only [playOf] at this; omega
  have hql : (s.gpr .a3).toNat < 2 ^ 16 := by have := hL.ql; simp only [playOf] at this; omega
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (playOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [playOf]) nw alS
  have hS := hscr s rfl
  unfold Params.entry
  refine WP.block_append (WP.block_append (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = s.gpr .a4 ∧
    u.mem = s.mem) (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_))
  have hs₁ := hscr s₁ k1.2.2
  have hin : ∀ i < 13, InRegions s₁.wr (off (savW (s.gpr .a4)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.st (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith)
  have hal : ∀ i < 13, (off (savW (s.gpr .a4)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.al8 (d := saveOff i) (by simp only [saveOff, playOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega)
  refine WP.mono (saveT2_ok s₁ a2 hin hal) fun s₂ hS₂ => ?_
  have k12 := k1.trans hS₂.keep
  have e : ∀ r, r ≠ .t2 → r ≠ .s6 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr fun hm => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact h1 hm
      · exact h1 hm
      · exact h2 hm
  have hs₂ := hscr s₂ k12.2.2
  obtain ⟨_, hal16⟩ := ScrL.hdr hs₂ hL (d := 16) (by decide) (by decide)
  have hal16' : (off (s.gpr .a4) 16).toNat % 8 = 0 := hal16
  have hst16 : InRegions s₂.wr (off (s.gpr .a4) 16) 8 := hs₂.st (d := 16) (by simp only [playOf] at hZ ⊢; omega)
  have hpk := pack_entry0 (s.gpr .a2) (s.gpr .a3) hpl hql
  refine WP.mono (WP.keep [.s11, .ra, .t3] (Q := fun t =>
      t.mem = s₂.mem.writeW (off (s.gpr .a4) 16) (pack (s.gpr .a2).toNat (s.gpr .a3).toNat 0 0) ∧
      t.gpr .s11 = s.gpr .a0 ∧ t.gpr .ra = 0) (by
        brun [hS₂.s6, e .a0 (by decide) (by decide), e .a2 (by decide) (by decide),
          e .a3 (by decide) (by decide), hLens, hst16, hal16', hpk, exec_li_zero,
          exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl))
    fun t ⟨⟨mt, t11, tra⟩, kt⟩ => ?_
  have k := k12.trans kt
  have hp16 : (playOf s).pl < 2 ^ 16 := hpl
  have hq16 : (playOf s).ql < 2 ^ 16 := hql
  have hnw : (s.gpr .a4).toNat + 256 ≤ 2 ^ 64 := by simp only [playOf] at hZ; omega
  have w16 := writeW_outside s₂.mem (s.gpr .a4) (d := 16) (pack (s.gpr .a2).toNat (s.gpr .a3).toNat 0 0)
    (by omega)
  have hlen : word t.mem (s.gpr .a4) hLens = pack (playOf s).pl (playOf s).ql 0 0 := by
    rw [mt]; exact word_writeW_self _ _ _ _
  have hlen' : word t.mem (playOf s).S hLens = pack (playOf s).pl (playOf s).ql 0 0 := hlen
  have f1 : Outside (s.gpr .a4) 128 104 s₁.mem s₂.mem :=
    VG.Proof.Bignum.frame_outside (base := s.gpr .a4) (d := 128) (len := 104) hS₂.frame (by omega)
  refine ⟨⟨⟨(kt.gpr (by decide)).trans hS₂.s6, t11, tra, by rw [hlen']; exact pack_pl hp16 hq16 (by decide) (by decide),
    by rw [hlen']; exact pack_ql hp16 hq16 (by decide) (by decide)⟩, hscr t k.2.2, hlen, fun i hi => ?_, ?_⟩,
    k.mono (by decide)⟩
  · rw [mt, w16.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)]
    show s₂.mem.readW (s.gpr .a4 + BitVec.ofNat 64 (saveOff i)) 64 = _
    rw [saveOff_eq, hS₂.saved i hi]
    exact k1.gpr fun h => saved_ne_t2 i hi (List.mem_singleton.mp h)
  · rw [mt, ← m1]
    exact (f1.mono (Nat.zero_le _) (by omega)).trans (w16.mono (Nat.zero_le _) (by omega))

end VG.Proof.Dsa.RISCV64
