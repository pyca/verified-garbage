module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Save
public import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Impl.Dsa.RISCV64.Verify
public import VerifiedGarbage.Spec.Dsa.SignVerify
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: the contract on the registers, and the entry

`vContract`: `vg_dsa_verify(key = a0, key_len = a1, p_len = a2, q_len = a3,
signature = a4, signature_len = a5, digest = a6, digest_len = a7, scratch,
scratch_len)`, the last two on the stack. `front_ok`: `entry` loads
`scratch`'s address from the stack, saves the callee-saved registers and
`ra` in its header, keeps the key and the signature in `s11` and `ra`
(`Regs`), and the digest's address and the lengths in the header's
`hDigest` and `hLens`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

/-- The arguments on the stack: `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_dsa_verify`, on the registers and the stack. -/
def vContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .a0, (s.gpr .a1).toNat⟩
    let sg : Region := ⟨s.gpr .a4, (s.gpr .a5).toNat⟩
    let dg : Region := ⟨s.gpr .a6, (s.gpr .a7).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.rd = [key, sg, dg, stackArgs s] ∧ s.wr = [scr] ∧
      key.Disjoint scr ∧ sg.Disjoint scr ∧ dg.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .a0).toNat + (s.gpr .a1).toNat ≤ 2 ^ 64 ∧ (s.gpr .a4).toNat + (s.gpr .a5).toNat ≤ 2 ^ 64 ∧
      (s.gpr .a6).toNat + (s.gpr .a7).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .a2).toNat (s.gpr .a3).toNat ∧
      (s.gpr .a1).toNat = 3 * (s.gpr .a2).toNat + (s.gpr .a3).toNat ∧
      (s.gpr .a5).toNat = 2 * (s.gpr .a3).toNat ∧ Spec.Dsa.scratchWords (s.gpr .a2).toNat ≤ (stackArg s 1).toNat ∧
      (stackArg s 0).toNat % 8 = 0 ∧ s.sp.toNat % 16 = 0
  post s t :=
    ((t.gpr .a0).setWidth 32).toNat = if Spec.Dsa.verifyBytes (s.gpr .a2).toNat (s.gpr .a3).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .a0) (s.gpr .a1).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .a6) (s.gpr .a7).toNat) then 1 else 0
  pub s₁ s₂ :=
    (∀ r ∈ argRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.sp = s₂.sp ∧
      (List.range 2).map (stackArg s₁) = (List.range 2).map (stackArg s₂) ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .a2).toNat (s₁.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat) ++
        [if Spec.Dsa.verifyBytes (s₁.gpr .a2).toNat (s₁.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a0) (s₁.gpr .a1).toNat)
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a4) (s₁.gpr .a5).toNat)
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .a6) (s₁.gpr .a7).toNat) then 1 else 0] =
      Spec.Dsa.publicBytesLeak (s₂.gpr .a2).toNat (s₂.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat) ++
        [if Spec.Dsa.verifyBytes (s₂.gpr .a2).toNat (s₂.gpr .a3).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a0) (s₂.gpr .a1).toNat)
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a4) (s₂.gpr .a5).toNat)
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .a6) (s₂.gpr .a7).toNat) then 1 else 0]

/-- A call's layout. -/
def layOf (s : State) : Lay := ⟨stackArg s 0, (stackArg s 1).toNat * 8, (s.gpr .a2).toNat, (s.gpr .a3).toNat⟩

theorem layOf_ok {s : State} (h : vContract.pre s) : (layOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw, -, -⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [layOf]; omega_arith, by simp only [layOf]; omega_arith, by simp only [layOf]; omega_arith, nw⟩

/-- `capD`'s mask: all ones exactly when `x ≥ 64`. -/
theorem cap_mask (x : BitVec 64) :
    (0 : BitVec 64) - ((0 : BitVec 64) - x >>> 6) >>> 63 = if x.toNat < 64 then 0 else BitVec.allOnes 64 := by
  have hx := x.isLt
  rw [show (0 : BitVec 64) = 0#64 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_zero]
  split
  · simp only [BitVec.toNat_zero, Nat.reducePow] at *; omega
  · simp only [BitVec.toNat_allOnes, Nat.reducePow] at *; omega

/-- `capD`'s value: `min(x, 64)`. -/
theorem cap_eq (x : BitVec 64) :
    x ^^^ (x ^^^ 64#64) &&& (0 : BitVec 64) - ((0 : BitVec 64) - x >>> 6) >>> 63 =
      BitVec.ofNat 64 (min x.toNat 64) := by
  have hx := x.isLt
  rw [cap_mask]
  split
  · rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.and_zero, BitVec.xor_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.min_eq_left (by omega_arith), Nat.mod_eq_of_lt hx]
  · rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.min_eq_right (by omega_arith)]
    rfl

/-- The lengths. -/
theorem pack_entry (x y : BitVec 64) {d : Nat} (hx : x.toNat < 2 ^ 16) (hy : y.toNat < 2 ^ 16) (hd : d < 2 ^ 16) :
    x + y <<< 16 + BitVec.ofNat 64 d <<< 48 = pack x.toNat y.toNat 0 d := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat hx hy (by decide) hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at *
  omega_arith

/-- The registers `entry` writes. -/
def entryRegs : List Reg := [.t2, .s6, .s11, .ra, .t3, .a1]

/-- What `entry` leaves. -/
structure Front (s t : State) : Prop where
  regs : Regs t (layOf s) (s.gpr .a0) (s.gpr .a4)
  scr : ScrL t (layOf s)
  lens : word t.mem (stackArg s 0) hLens = pack (layOf s).pl (layOf s).ql 0 (min (s.gpr .a7).toNat 64)
  dig : word t.mem (stackArg s 0) hDigest = s.gpr .a6
  sav : ∀ i < 13, word t.mem (stackArg s 0) (saveOff i) = s.gpr (saved i)
  out : Outside (stackArg s 0) 0 256 s.mem t.mem

/-- `entry`: `scratch` (from the stack) into `s6`, the callee-saved
registers saved in its header, the key and the signature into `s11` and
`ra`, the digest's address and the lengths into the header. Memory changes
only in the header. -/
theorem front_ok {s : State} (h : vContract.pre s) :
    WP isa (.block Verify.entry) s fun t => Front s t ∧ Keep entryRegs s t := by
  have hL := layOf_ok h
  have hZ := hL.z256
  have hpl : (s.gpr .a2).toNat < 2 ^ 16 := by have := hL.pl; simp only [layOf] at this; omega_arith
  have hql : (s.gpr .a3).toNat < 2 ^ 16 := by have := hL.ql; simp only [layOf] at this; omega_arith
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, nw, -, -, -, -, alS, sp16⟩ := h
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (layOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [layOf]) nw alS
  have hS := hscr s rfl
  have hin : ∀ i < 13, InRegions s.wr (off (savW (stackArg s 0)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq]; exact hS.st (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
  have hal : ∀ i < 13, (off (savW (stackArg s 0)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact hS.al8 (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega)
  unfold Verify.entry
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (save_ok s rfl ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp),
    by simp [Region.Contains]⟩ (by omega) hin hal) fun s₁ hS₁ => ?_)
  have e : ∀ r, r ≠ .t2 → r ≠ .s6 → s₁.gpr r = s.gpr r := fun r h1 h2 =>
    hS₁.keep.gpr fun hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hm.elim h1 h2
  have hs₁ := hscr s₁ hS₁.keep.2.2
  obtain ⟨hin8, hal8⟩ := ScrL.hdr hs₁ hL (d := 8) (by decide) (by decide)
  obtain ⟨hin16, hal16⟩ := ScrL.hdr hs₁ hL (d := 16) (by decide) (by decide)
  have hst8 : InRegions s₁.wr (off (stackArg s 0) 8) 8 := hs₁.st (d := 8) (by simp only [layOf] at hZ ⊢; omega)
  have hst16 : InRegions s₁.wr (off (stackArg s 0) 16) 8 := hs₁.st (d := 16) (by simp only [layOf] at hZ ⊢; omega)
  have hal8' : (off (stackArg s 0) 8).toNat % 8 = 0 := hal8
  have hal16' : (off (stackArg s 0) 16).toNat % 8 = 0 := hal16
  have hcap := cap_eq (s.gpr .a7)
  have hpk := pack_entry (s.gpr .a2) (s.gpr .a3) hpl hql (show min (s.gpr .a7).toNat 64 < 2 ^ 16 by omega)
  refine WP.mono (WP.keep [.s11, .ra, .t3, .a1] (Q := fun t =>
      t.mem = (s₁.mem.writeW (off (stackArg s 0) 8) (s.gpr .a6)).writeW (off (stackArg s 0) 16)
        (pack (s.gpr .a2).toNat (s.gpr .a3).toNat 0 (min (s.gpr .a7).toNat 64)) ∧
      t.gpr .s11 = s.gpr .a0 ∧ t.gpr .ra = s.gpr .a4) ?_ (by decide) (by rfl)) fun t ⟨⟨mt, t11, tra⟩, kt⟩ => ?_
  · unfold Verify.capD
    brun [hS₁.s6, e .a0 (by decide) (by decide), e .a4 (by decide) (by decide), e .a6 (by decide) (by decide),
      e .a7 (by decide) (by decide), e .a2 (by decide) (by decide), e .a3 (by decide) (by decide), hDigest, hLens,
      hst8, hal8', hst16, hal16', hcap, hpk, exec_li_zero, exec_li_lit (show 64 < 2048 by decide),
      exec_shift_d (show 6 < 64 by decide), exec_shift_d (show 63 < 64 by decide),
      exec_shift_d (show 48 < 64 by decide), exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]
  · have k := hS₁.keep.trans kt
    have hp16 : (layOf s).pl < 2 ^ 16 := hpl
    have hq16 : (layOf s).ql < 2 ^ 16 := hql
    have hd16 : min (s.gpr .a7).toNat 64 < 2 ^ 16 := by omega
    have hnw : (stackArg s 0).toNat + 256 ≤ 2 ^ 64 := by simp only [layOf] at hZ; omega
    have w16 := writeW_outside (s₁.mem.writeW (off (stackArg s 0) 8) (s.gpr .a6)) (stackArg s 0) (d := 16)
      (pack (s.gpr .a2).toNat (s.gpr .a3).toNat 0 (min (s.gpr .a7).toNat 64)) (by omega)
    have w8 := writeW_outside s₁.mem (stackArg s 0) (d := 8) (s.gpr .a6) (by omega)
    have hlen : word t.mem (stackArg s 0) hLens = pack (layOf s).pl (layOf s).ql 0 (min (s.gpr .a7).toNat 64) := by
      rw [mt]; exact word_writeW_self _ _ _ _
    have f1 : Outside (stackArg s 0) 128 104 s.mem s₁.mem :=
      VG.Proof.Bignum.frame_outside (base := stackArg s 0) (d := 128) (len := 104) hS₁.frame (by omega)
    have hlen' : word t.mem (layOf s).S hLens = pack (layOf s).pl (layOf s).ql 0 (min (s.gpr .a7).toNat 64) := hlen
    refine ⟨⟨⟨(kt.gpr (by decide)).trans hS₁.s6, t11, tra, by rw [hlen']; exact pack_pl hp16 hq16 (by decide) hd16,
      by rw [hlen']; exact pack_ql hp16 hq16 (by decide) hd16⟩, hscr t k.2.2, hlen, ?_, fun i hi => ?_, ?_⟩,
      k.mono (by decide)⟩
    · rw [mt, w16.word (by simp only [hDigest]; omega) (by simp only [hDigest]; omega)]
      exact word_writeW_self _ _ _ _
    · rw [mt, w16.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega),
        w8.word (by simp only [saveOff]; omega) (by simp only [saveOff]; omega)]
      show s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 (saveOff i)) 64 = _
      rw [saveOff_eq]; exact hS₁.saved i hi
    · rw [mt]
      exact ((f1.mono (Nat.zero_le _) (by omega)).trans (w8.mono (Nat.zero_le _) (by omega))).trans
        (w16.mono (Nat.zero_le _) (by omega))

end VG.Proof.Dsa.RISCV64
