module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyFront
public import VerifiedGarbage.Impl.Dsa.RISCV64.Sign
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: the contract on the registers, and the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Front.lean`). `sContract`:
`vg_dsa_sign(out = a0, out_len = a1, key = a2, key_len = a3, p_len = a4,
nonce = a5, q_len = a6, digest = a7, digest_len, scratch, scratch_len)`, the
last three on the stack. `sfront_ok`: `entry` loads `scratch`'s address
from the stack, saves the callee-saved registers and `ra` in its header,
keeps the key and the nonce in `s11` and `ra` (`Regs`), and the digest's
address, `out` and the lengths in the header's `hDigest`, `Sign.hOut` and
`hLens`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

/-- The arguments on the stack: `digest_len`, `scratch` and `scratch_len`. -/
abbrev sStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 24⟩

/-- The signature `signBytes` gives, on entry. -/
def sRes (s : State) : Option (List Byte) :=
  Spec.Dsa.signBytes (s.gpr .a4).toNat (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .a5) (s.gpr .a6).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a7) (stackArg s 0).toNat)

/-- `vg_dsa_sign`, on the registers and the stack. -/
def sContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let key : Region := ⟨s.gpr .a2, (s.gpr .a3).toNat⟩
    let nc : Region := ⟨s.gpr .a5, (s.gpr .a6).toNat⟩
    let dg : Region := ⟨s.gpr .a7, (stackArg s 0).toNat⟩
    let scr : Region := ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩
    s.rd = [key, nc, dg, sStackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint key ∧ out.Disjoint nc ∧ out.Disjoint dg ∧ out.Disjoint scr ∧ out.Disjoint (sStackArgs s) ∧
      key.Disjoint scr ∧ nc.Disjoint scr ∧ dg.Disjoint scr ∧ scr.Disjoint (sStackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a2).toNat + (s.gpr .a3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a5).toNat + (s.gpr .a6).toNat ≤ 2 ^ 64 ∧ (s.gpr .a7).toNat + (stackArg s 0).toNat ≤ 2 ^ 64 ∧
      (stackArg s 1).toNat + (stackArg s 2).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a4).toNat (s.gpr .a6).toNat ∧
      (s.gpr .a1).toNat = 2 * (s.gpr .a6).toNat ∧
      (s.gpr .a3).toNat = 3 * (s.gpr .a4).toNat + 2 * (s.gpr .a6).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .a4).toNat ≤ (stackArg s 2).toNat ∧
      (stackArg s 1).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = Spec.Dsa.signStatus (sRes s) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .a0) (s.gpr .a1).toNat = (sRes s).getD (List.replicate (s.gpr .a1).toNat 0)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .a4).toNat (s₁.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a2) (s₁.gpr .a3).toNat) ++ [Spec.Dsa.signStatus (sRes s₁)] =
      Spec.Dsa.publicBytesLeak (s₂.gpr .a4).toNat (s₂.gpr .a6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a2) (s₂.gpr .a3).toNat) ++ [Spec.Dsa.signStatus (sRes s₂)]

/-- `vg_dsa_sign`'s contract on the registers, for a key that passes `valid`. -/
def sContractWith (valid : Nat → Nat → List Byte → Bool) : Contract isa where
  pre s := sContract.pre s ∧
    valid (s.gpr .a4).toNat (s.gpr .a6).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .a2) (s.gpr .a3).toNat) = true
  post := sContract.post
  pub := sContract.pub

/-- A call's layout. -/
def slayOf (s : State) : Lay := ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .a4).toNat, (s.gpr .a6).toNat⟩

theorem slayOf_ok {s : State} (h : sContract.pre s) : (slayOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw, -, -⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [slayOf]; omega_arith, by simp only [slayOf]; omega_arith, by simp only [slayOf]; omega_arith, nw⟩

/-- The stack's arguments lie apart from the header's word at `d`. -/
theorem stack_sep {S B : Addr} {Z d : Nat} (hd : (⟨S, Z⟩ : Region).Disjoint ⟨B, 24⟩) (hdZ : d + 8 ≤ Z)
    (hZ : Z ≤ 2 ^ 64) : Mem.Sep B 8 (off S d) 8 := by
  intro x h₁ h₂
  rw [off, Offset.lt_iff x S (by omega)] at h₂
  exact hd x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

/-- The stack's arguments are kept by a change in the header. -/
theorem stack_kept {S B : Addr} {Z : Nat} (hd : (⟨S, Z⟩ : Region).Disjoint ⟨B, 24⟩) (hZ : 256 ≤ Z)
    {m m' : Mem} (ho : Outside S 0 256 m m') : m'.readW B 64 = m.readW B 64 := by
  refine Mem.readW_congr fun i hi => ho _ (Or.inr ?_)
  by_contra hc
  have hlt := (B + BitVec.ofNat 64 i - S).isLt
  exact hd (B + BitVec.ofNat 64 i) (by simp only [Region.Contains, ofs] at hc ⊢; omega_arith)
    (by simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat B (by omega_arith)]; omega_arith)

/-- The registers `Sign.entry` writes. -/
def sentryRegs : List Reg := [.t2, .s6, .s11, .ra, .t3, .a7, .a1]

/-- What `Sign.entry` leaves. -/
structure SFront (s t : State) : Prop where
  regs : Regs t (slayOf s) (s.gpr .a2) (s.gpr .a5)
  scr : ScrL t (slayOf s)
  lens : word t.mem (stackArg s 1) hLens = pack (slayOf s).pl (slayOf s).ql 0 (min (stackArg s 0).toNat 64)
  dig : word t.mem (stackArg s 1) hDigest = s.gpr .a7
  outw : word t.mem (stackArg s 1) Sign.hOut = s.gpr .a0
  sav : ∀ i < 13, word t.mem (stackArg s 1) (saveOff i) = s.gpr (saved i)
  out : Outside (stackArg s 1) 0 256 s.mem t.mem

/-- `entry`: `scratch` (from the stack) into `s6`, the callee-saved
registers saved in its header, the key and the nonce into `s11` and `ra`,
the digest's address, `out` and the lengths into the header. Memory changes
only in the header. -/
theorem sfront_ok {s : State} (h : sContract.pre s) :
    WP isa (.block Sign.entry) s fun t => SFront s t ∧ Keep sentryRegs s t := by
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hpl : (s.gpr .a4).toNat < 2 ^ 16 := by have := hL.pl; simp only [slayOf] at this; omega_arith
  have hql : (s.gpr .a6).toNat < 2 ^ 16 := by have := hL.ql; simp only [slayOf] at this; omega_arith
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, -, dSS, -, -, -, -, nw, -, -, -, -, alS, sp16⟩ := h
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (slayOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [slayOf]) nw alS
  have hZ' : (stackArg s 2).toNat * 8 ≤ 2 ^ 64 := by omega
  have hZS : 256 ≤ (stackArg s 2).toNat * 8 := by simp only [slayOf] at hZ; exact hZ
  unfold Sign.entry
  simp only [List.append_assoc]
  -- `scratch` into `t2`.
  have hld8 : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 8) 8 :=
    ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
      simp only [Region.Contains, stackArgAddr, Nat.mul_zero, add_ofNat_zero]
      rw [show s.sp + BitVec.ofNat 64 8 - s.sp = BitVec.ofNat 64 8 by rw [BitVec.add_comm, BitVec.add_sub_cancel]]; decide⟩
  have hal8 : (s.sp + BitVec.ofNat 64 8).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hv8 : s.mem.readW (s.sp + BitVec.ofNat 64 8) 64 = stackArg s 1 := rfl
  refine WP.block_append (WP.mono (WP.keep [.t2] (Q := fun u => u.gpr .t2 = stackArg s 1 ∧ u.mem = s.mem ∧
      u.sp = s.sp) (by brun [exec_addSp (show 8 < 2048 by decide), hld8, hal8, hv8]) (by rfl) (by rfl))
    fun s₁ ⟨⟨a2, m1, sp1⟩, k1⟩ => ?_)
  have hs₁ := hscr s₁ k1.2.2
  have hin : ∀ i < 13, InRegions s₁.wr (off (savW (stackArg s 1)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.st (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
  have hal : ∀ i < 13, (off (savW (stackArg s 1)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact hs₁.al8 (d := saveOff i) (by simp only [saveOff, slayOf] at hZ ⊢; omega_arith)
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
  have sp₂ : s₂.sp = s.sp := hS₂.sp.trans sp1
  have hst8 : InRegions s₂.wr (off (stackArg s 1) 8) 8 := hs₂.st (d := 8) (by simp only [slayOf] at hZ ⊢; omega)
  have hst16 : InRegions s₂.wr (off (stackArg s 1) 16) 8 := hs₂.st (d := 16) (by simp only [slayOf] at hZ ⊢; omega)
  have hst24 : InRegions s₂.wr (off (stackArg s 1) 24) 8 := hs₂.st (d := 24) (by simp only [slayOf] at hZ ⊢; omega)
  have hal8' : (off (stackArg s 1) 8).toNat % 8 = 0 := (ScrL.hdr hs₂ hL (d := 8) (by decide) (by decide)).2
  have hal16' : (off (stackArg s 1) 16).toNat % 8 = 0 := (ScrL.hdr hs₂ hL (d := 16) (by decide) (by decide)).2
  have hal24' : (off (stackArg s 1) 24).toNat % 8 = 0 := (ScrL.hdr hs₂ hL (d := 24) (by decide) (by decide)).2
  -- `digest_len`, from the stack.
  have f1 : Outside (stackArg s 1) 128 104 s₁.mem s₂.mem :=
    VG.Proof.Bignum.frame_outside (base := stackArg s 1) (d := 128) (len := 104) hS₂.frame (by omega)
  have dSS' : (⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 24⟩ := dSS
  have hv0 : ((s₂.mem.writeW (off (stackArg s 1) 8) (s.gpr .a7)).writeW (off (stackArg s 1) 24) (s.gpr .a0)).readW
      (s.sp + BitVec.ofNat 64 0) 64 = stackArg s 0 := by
    rw [Mem.readW_writeW_sep (w := 64) (w' := 64)
        (show Mem.Sep (s.sp + BitVec.ofNat 64 0) 8 (off (stackArg s 1) 24) 8 from
          stack_sep (B := stackArgAddr s 0) dSS' (by omega) hZ') (by decide),
      Mem.readW_writeW_sep (w := 64) (w' := 64)
        (show Mem.Sep (s.sp + BitVec.ofNat 64 0) 8 (off (stackArg s 1) 8) 8 from
          stack_sep (B := stackArgAddr s 0) dSS' (by omega) hZ') (by decide),
      show s.sp + BitVec.ofNat 64 0 = stackArgAddr s 0 from rfl,
      stack_kept dSS' hZS (f1.mono (Nat.zero_le _) (by omega)), m1]
    rfl
  have hld0 : InRegions (s₂.rd ++ s₂.wr) (s.sp + BitVec.ofNat 64 0) 8 := by
    rw [k12.2.1, k12.2.2]
    exact ⟨sStackArgs s, List.mem_append_left _ (by rw [hrd]; simp), by
      simp only [Region.Contains, stackArgAddr, Nat.mul_zero]; rw [BitVec.sub_self]; decide⟩
  have hal0 : (s.sp + BitVec.ofNat 64 0).toNat % 8 = 0 := by rw [add_ofNat_zero]; omega
  have hv0' : ((s₂.mem.writeW (stackArg s 1 + BitVec.ofNat 64 8) (s.gpr .a7)).writeW
      (stackArg s 1 + BitVec.ofNat 64 24) (s.gpr .a0)).readW s.sp 64 = stackArg s 0 := by
    rw [← add_ofNat_zero s.sp]; exact hv0
  have hld0' : InRegions (s₂.rd ++ s₂.wr) s.sp 8 := by rw [← add_ofNat_zero s.sp]; exact hld0
  have hal0' : s.sp.toNat % 8 = 0 := by omega
  -- The key, the nonce, the digest's address, `out` and `digest_len`.
  refine WP.block_append (WP.mono (WP.keep [.s11, .ra, .t3, .a7] (Q := fun t =>
      t.mem = (s₂.mem.writeW (off (stackArg s 1) 8) (s.gpr .a7)).writeW (off (stackArg s 1) 24) (s.gpr .a0) ∧
      t.gpr .s11 = s.gpr .a2 ∧ t.gpr .ra = s.gpr .a5 ∧ t.gpr .a7 = stackArg s 0) (by
        brun [hS₂.s6, e .a2 (by decide) (by decide), e .a5 (by decide) (by decide), e .a7 (by decide) (by decide),
          e .a0 (by decide) (by decide), hDigest, Sign.hOut, hst8, hal8', hst24, hal24', BitVec.add_zero, sp₂,
          exec_addSp (show 0 < 2048 by decide), hld0', hal0', hv0'])
      (by decide) (by rfl)) fun s₃ ⟨⟨m3, t11, tra, ta7⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  have e3 : ∀ r, r ≠ .t2 → r ≠ .s6 → r ≠ .s11 → r ≠ .ra → r ≠ .t3 → r ≠ .a7 → s₃.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 h6 => (k3.gpr (by simp [h3, h4, h5, h6])).trans (e r h1 h2)
  have hcap := cap_eq (stackArg s 0)
  have hpk := pack_entry (s.gpr .a4) (s.gpr .a6) hpl hql (show min (stackArg s 0).toNat 64 < 2 ^ 16 by omega)
  refine WP.mono (WP.keep [.t3, .a1] (Q := fun t =>
      t.mem = s₃.mem.writeW (off (stackArg s 1) 16)
        (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 (min (stackArg s 0).toNat 64))) ?_ (by decide) (by rfl))
    fun t ⟨mt, kt⟩ => ?_
  · unfold Verify.capD
    brun [(k3.gpr (r := .s6) (by decide)).trans hS₂.s6, e3 .a4 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), e3 .a6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      ta7, hLens, k3.2.2 ▸ hst16, hal16', hcap, hpk, exec_li_zero,
      exec_li_lit (show 64 < 2048 by decide), exec_shift_d (show 6 < 64 by decide),
      exec_shift_d (show 63 < 64 by decide), exec_shift_d (show 48 < 64 by decide),
      exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]
  · have k := k13.trans kt
    have hp16 : (slayOf s).pl < 2 ^ 16 := hpl
    have hq16 : (slayOf s).ql < 2 ^ 16 := hql
    have hd16 : min (stackArg s 0).toNat 64 < 2 ^ 16 := by omega
    have hnw : (stackArg s 1).toNat + 256 ≤ 2 ^ 64 := by simp only [slayOf] at hZ; omega
    have w16 := writeW_outside s₃.mem (stackArg s 1) (d := 16)
      (pack (s.gpr .a4).toNat (s.gpr .a6).toNat 0 (min (stackArg s 0).toNat 64)) (by omega)
    have w24 := writeW_outside (s₂.mem.writeW (off (stackArg s 1) 8) (s.gpr .a7)) (stackArg s 1) (d := 24)
      (s.gpr .a0) (by omega)
    have w8 := writeW_outside s₂.mem (stackArg s 1) (d := 8) (s.gpr .a7) (by omega)
    have hlen : word t.mem (stackArg s 1) hLens =
        pack (slayOf s).pl (slayOf s).ql 0 (min (stackArg s 0).toNat 64) := by
      rw [mt]; exact word_writeW_self _ _ _ _
    have hlen' : word t.mem (slayOf s).S hLens =
        pack (slayOf s).pl (slayOf s).ql 0 (min (stackArg s 0).toNat 64) := hlen
    refine ⟨⟨⟨(kt.gpr (by decide)).trans ((k3.gpr (by decide)).trans hS₂.s6), (kt.gpr (by decide)).trans t11,
      (kt.gpr (by decide)).trans tra, by rw [hlen']; exact pack_pl hp16 hq16 (by decide) hd16,
      by rw [hlen']; exact pack_ql hp16 hq16 (by decide) hd16⟩, hscr t k.2.2, hlen, ?_, ?_, fun i hi => ?_, ?_⟩,
      k.mono (by decide)⟩
    · rw [mt, w16.word (by simp only [hDigest]; omega) (by simp only [hDigest]; omega), m3,
        w24.word (by simp only [hDigest]; omega) (by simp only [hDigest]; omega)]
      exact word_writeW_self _ _ _ _
    · rw [mt, w16.word (by simp only [Sign.hOut]; omega) (by simp only [Sign.hOut]; omega), m3]
      exact word_writeW_self _ _ _ _
    · rw [mt, w16.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega), m3,
        w24.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega),
        w8.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)]
      show s₂.mem.readW (stackArg s 1 + BitVec.ofNat 64 (saveOff i)) 64 = _
      rw [saveOff_eq, hS₂.saved i hi]
      exact k1.gpr fun h => saved_ne_t2 i hi (List.mem_singleton.mp h)
    · have o3 : Outside (stackArg s 1) 0 256 s₁.mem s₃.mem := by
        rw [m3]
        exact ((f1.mono (Nat.zero_le _) (by omega)).trans (w8.mono (Nat.zero_le _) (by omega))).trans
          (w24.mono (Nat.zero_le _) (by omega))
      rw [mt, ← m1]
      exact o3.trans (w16.mono (Nat.zero_le _) (by omega))

end VG.Proof.Dsa.RISCV64
