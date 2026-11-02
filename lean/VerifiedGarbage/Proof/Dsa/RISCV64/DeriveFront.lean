module

public import VerifiedGarbage.Proof.Dsa.RISCV64.ParamsFront
public import VerifiedGarbage.Impl.Dsa.RISCV64.Derive
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA key derivation on RISC-V: the contract on the registers, and the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/Derive/Front.lean`). `dContract`:
`vg_dsa_derive_key(out = a0, out_len = a1, params = a2, params_len = a3,
p_len = a4, x = a5, q_len = a6, scratch = a7, scratch_len)`, `scratch_len`
on the stack. `dfront_ok`: `entry` saves the callee-saved registers and
`ra` in `scratch`'s header, keeps the domain and x in `s11` and `ra`
(`Regs`, with x as the signature), and `out` and the lengths in the header
(`Sign.hOut`, `hLens`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

/-- The argument on the stack: `scratch_len`. -/
abbrev dStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- The key `deriveKeyBytes` gives, on entry. -/
def dRes (s : State) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (s.gpr .a4).toNat (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat)

/-- `vg_dsa_derive_key`, on the registers and the stack. -/
def dContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let ps : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let xr : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let scr : Region := ⟨s.gpr .a7, (stackArg s 0).toNat * 8⟩
    s.rd = [ps, xr, dStackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint ps ∧ out.Disjoint xr ∧ out.Disjoint scr ∧ out.Disjoint (dStackArgs s) ∧
      ps.Disjoint scr ∧ xr.Disjoint scr ∧ scr.Disjoint (dStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a4).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 3 * (s.gpr .a4).toNat + 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a3).toNat = 2 * (s.gpr .a4).toNat + (s.gpr .a6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 0).toNat ∧
      (s.gpr .a7).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = Spec.Dsa.signStatus (dRes s) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat = (dRes s).getD (List.replicate (s.gpr .a1).toNat 0)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat).map (·.toNat) ++ [Spec.Dsa.signStatus (dRes s₁)] =
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat).map (·.toNat) ++ [Spec.Dsa.signStatus (dRes s₂)]

/-- A call's layout. -/
def dlayOf (s : State) : Lay := ⟨s.gpr .a7, (stackArg s 0).toNat * 8, (s.gpr .a4).toNat, (s.gpr .a6).toNat⟩

theorem dlayOf_ok {s : State} (h : dContract.pre s) : (dlayOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw, -, -⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [dlayOf]; omega, by simp only [dlayOf]; omega, by simp only [dlayOf]; omega, nw⟩

/-- The registers `Derive.entry` writes. -/
def dentryRegs : List Reg := [.t2, .s6, .s11, .ra, .t3]

/-- What `Derive.entry` leaves. -/
structure DFront (s t : State) : Prop where
  regs : Regs t (dlayOf s) (s.gpr .a2) (s.gpr .a5)
  scr : ScrL t (dlayOf s)
  lens : word t.mem (s.gpr .a7) hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0
  outw : word t.mem (s.gpr .a7) Sign.hOut = s.gpr .a0
  sav : ∀ i < 13, word t.mem (s.gpr .a7) (saveOff i) = s.gpr (saved i)
  out : Outside (s.gpr .a7) 0 256 s.mem t.mem

/-- `entry`: `scratch` into `s6`, the callee-saved registers and `ra` saved in
its header, the domain and x into `s11` and `ra`, and `out` and the lengths
into the header. Memory changes only in the header. -/
theorem dfront_ok {s : State} (h : dContract.pre s) :
    WP isa (.block Derive.entry) s fun t => DFront s t ∧ Keep dentryRegs s t := by
  have hL := dlayOf_ok h
  have hZ := hL.z256
  have hpl : (s.gpr .a4).toNat < 2 ^ 16 := by have := hL.pl; simp only [dlayOf] at this; omega
  have hql : (s.gpr .a6).toNat < 2 ^ 16 := by have := hL.ql; simp only [dlayOf] at this; omega
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, -, nw, -, -, -, -, alS, -⟩ := h
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (dlayOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [dlayOf]) nw alS
  unfold Derive.entry
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = s.gpr .a7 ∧
    u.mem = s.mem) (by brun [BitVec.add_zero]) (by rfl) (by rfl)) fun s₁ ⟨⟨a2, m1⟩, k1⟩ => ?_)
  have hs₁ := hscr s₁ k1.2.2
  have hin : ∀ i < 13, InRegions s₁.wr (off (savW (s.gpr .a7)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.st (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
  have hal : ∀ i < 13, (off (savW (s.gpr .a7)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.al8 (d := saveOff i) (by simp only [saveOff, dlayOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega)
  refine WP.block_append (WP.mono (saveT2_ok s₁ a2 hin hal) fun s₂ hS₂ => ?_)
  have k12 := k1.trans hS₂.keep
  have e : ∀ r, r ≠ .t2 → r ≠ .s6 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr fun hm => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact h1 hm
      · exact h1 hm
      · exact h2 hm
  have hs₂ := hscr s₂ k12.2.2
  obtain ⟨_, hal24⟩ := ScrL.hdr hs₂ hL (d := 24) (by decide) (by decide)
  obtain ⟨_, hal16⟩ := ScrL.hdr hs₂ hL (d := 16) (by decide) (by decide)
  have hal24' : (off (s.gpr .a7) 24).toNat % 8 = 0 := hal24
  have hal16' : (off (s.gpr .a7) 16).toNat % 8 = 0 := hal16
  have hst24 : InRegions s₂.wr (off (s.gpr .a7) 24) 8 := hs₂.st (d := 24) (by simp only [dlayOf] at hZ ⊢; omega)
  have hst16 : InRegions s₂.wr (off (s.gpr .a7) 16) 8 := hs₂.st (d := 16) (by simp only [dlayOf] at hZ ⊢; omega)
  have hpk := pack_entry0 (s.gpr .a4) (s.gpr .a6) hpl hql
  refine WP.mono (WP.keep [.s11, .ra, .t3] (Q := fun t =>
      t.mem = (s₂.mem.writeW (off (s.gpr .a7) 24) (s.gpr .a0)).writeW (off (s.gpr .a7) 16)
        (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 0) ∧
      t.gpr .s11 = s.gpr .a2 ∧ t.gpr .ra = s.gpr .a5) (by
        brun [hS₂.s6, e .a2 (by decide) (by decide), e .a0 (by decide) (by decide), e .a5 (by decide) (by decide),
          e .a4 (by decide) (by decide), e .a6 (by decide) (by decide), Sign.hOut, hLens, hst24, hal24', hst16,
          hal16', hpk, exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl))
    fun t ⟨⟨mt, t11, tra⟩, kt⟩ => ?_
  have k := k12.trans kt
  have hp16 : (dlayOf s).pl < 2 ^ 16 := hpl
  have hq16 : (dlayOf s).ql < 2 ^ 16 := hql
  have hnw : (s.gpr .a7).toNat + 256 ≤ 2 ^ 64 := by simp only [dlayOf] at hZ; omega
  have w16 := writeW_outside (s₂.mem.writeW (off (s.gpr .a7) 24) (s.gpr .a0)) (s.gpr .a7) (d := 16)
    (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 0) (by omega)
  have w24 := writeW_outside s₂.mem (s.gpr .a7) (d := 24) (s.gpr .a0) (by omega)
  have hlen : word t.mem (s.gpr .a7) hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0 := by
    rw [mt]; exact word_writeW_self _ _ _ _
  have hlen' : word t.mem (dlayOf s).S hLens = pack (dlayOf s).pl (dlayOf s).ql 0 0 := hlen
  have f1 : Outside (s.gpr .a7) 128 104 s₁.mem s₂.mem :=
    VG.Proof.Bignum.frame_outside (base := s.gpr .a7) (d := 128) (len := 104) hS₂.frame (by omega)
  refine ⟨⟨⟨(kt.gpr (by decide)).trans hS₂.s6, t11, tra, by rw [hlen']; exact pack_pl hp16 hq16 (by decide) (by decide),
    by rw [hlen']; exact pack_ql hp16 hq16 (by decide) (by decide)⟩, hscr t k.2.2, hlen, ?_, fun i hi => ?_, ?_⟩,
    k.mono (by decide)⟩
  · rw [mt, w16.word (by simp only [Sign.hOut]; omega) (by simp only [Sign.hOut]; omega)]
    exact word_writeW_self _ _ _ _
  · rw [mt, w16.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega),
      w24.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)]
    show s₂.mem.readW (s.gpr .a7 + BitVec.ofNat 64 (saveOff i)) 64 = _
    rw [saveOff_eq, hS₂.saved i hi]
    exact k1.gpr fun h => saved_ne_t2 i hi (List.mem_singleton.mp h)
  · rw [mt, ← m1]
    exact ((f1.mono (Nat.zero_le _) (by omega)).trans (w24.mono (Nat.zero_le _) (by omega))).trans
      (w16.mono (Nat.zero_le _) (by omega))

end VG.Proof.Dsa.RISCV64
