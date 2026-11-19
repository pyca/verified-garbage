module

public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyBody
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Bignum.RISCV64.PubCorrect
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.RISCV64.Save
public import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
public import VerifiedGarbage.Impl.Dsa.RISCV64.Verify
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Dsa.RISCV64.Sizes
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad

/-! ### `Dsa.RISCV64.VerifyFront`, which this module and modules that import it used -/

section

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
    s₁.sp = s₂.sp ∧ s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
      s₁.gpr .a6 = s₂.gpr .a6 ∧ s₁.gpr .a7 = s₂.gpr .a7 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
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
  · simp only [BitVec.toNat_zero, Nat.reducePow] at *; omega_arith
  · simp only [BitVec.toNat_allOnes, Nat.reducePow] at *; omega_arith

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
  obtain hL := layOf_ok h
  have hZ := hL.z256
  obtain hpl : (s.gpr .a2).toNat < 2 ^ 16 := by have := hL.pl; simp only [layOf] at this; omega_arith
  obtain hql : (s.gpr .a3).toNat < 2 ^ 16 := by have := hL.ql; simp only [layOf] at this; omega_arith
  obtain ⟨hrd, hwr, -, -, -, -, -, -, -, nw, -, -, -, -, alS, sp16⟩ := h
  obtain hscr : ∀ t : State, t.wr = s.wr → ScrL t (layOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [layOf]) nw alS
  obtain hS := hscr s rfl
  obtain hin : ∀ i < 13, InRegions s.wr (off (savW (stackArg s 0)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq]; exact hS.st (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
  obtain hal : ∀ i < 13, (off (savW (stackArg s 0)) (8 * i)).toNat % 8 = 0 := fun i hi => by
    rw [← saveOff_eq]; exact hS.al8 (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
      (by simp only [saveOff]; omega_using [])
  unfold Verify.entry
  rw [List.append_assoc, List.append_assoc]
  refine WP.block_append (WP.mono (save_ok s rfl ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp),
    by simp [Region.Contains]⟩ (by omega_using [sp16]) hin hal) fun s₁ hS₁ => ?_)
  obtain e : ∀ r, r ≠ .t2 → r ≠ .s6 → s₁.gpr r = s.gpr r := fun r h1 h2 =>
    hS₁.keep.gpr fun hm => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact hm.elim h1 h2
  obtain hs₁ := hscr s₁ hS₁.keep.2.2
  obtain ⟨hin8, hal8⟩ := ScrL.hdr hs₁ hL (d := 8) (by decide) (by decide)
  obtain ⟨hin16, hal16⟩ := ScrL.hdr hs₁ hL (d := 16) (by decide) (by decide)
  obtain hst8 : InRegions s₁.wr (off (stackArg s 0) 8) 8 := hs₁.st (d := 8) (by simp only [layOf] at hZ ⊢; omega_using [hZ])
  obtain hst16 : InRegions s₁.wr (off (stackArg s 0) 16) 8 := hs₁.st (d := 16) (by simp only [layOf] at hZ ⊢; omega_using [hZ])
  have hal8' : (off (stackArg s 0) 8).toNat % 8 = 0 := hal8
  have hal16' : (off (stackArg s 0) 16).toNat % 8 = 0 := hal16
  obtain hcap := cap_eq (s.gpr .a7)
  obtain hpk := pack_entry (s.gpr .a2) (s.gpr .a3) hpl hql (show min (s.gpr .a7).toNat 64 < 2 ^ 16 by omega_using [])
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
    obtain hd16 : min (s.gpr .a7).toNat 64 < 2 ^ 16 := by omega_using []
    obtain hnw : (stackArg s 0).toNat + 256 ≤ 2 ^ 64 := by simp only [layOf] at hZ; omega_using [hZ, nw]
    obtain w16 := writeW_outside (s₁.mem.writeW (off (stackArg s 0) 8) (s.gpr .a6)) (stackArg s 0) (d := 16)
      (pack (s.gpr .a2).toNat (s.gpr .a3).toNat 0 (min (s.gpr .a7).toNat 64)) (by omega_using [])
    obtain w8 := writeW_outside s₁.mem (stackArg s 0) (d := 8) (s.gpr .a6) (by omega_using [])
    obtain hlen : word t.mem (stackArg s 0) hLens = pack (layOf s).pl (layOf s).ql 0 (min (s.gpr .a7).toNat 64) := by
      rw [mt]; exact word_writeW_self _ _ _ _
    obtain f1 : Outside (stackArg s 0) 128 104 s.mem s₁.mem :=
      VG.Proof.Bignum.frame_outside (base := stackArg s 0) (d := 128) (len := 104) hS₁.frame (by omega_using [])
    have hlen' : word t.mem (layOf s).S hLens = pack (layOf s).pl (layOf s).ql 0 (min (s.gpr .a7).toNat 64) := hlen
    refine ⟨⟨⟨(kt.gpr (by decide)).trans hS₁.s6, t11, tra, by rw [hlen']; exact pack_pl hp16 hq16 (by decide) hd16,
      by rw [hlen']; exact pack_ql hp16 hq16 (by decide) hd16⟩, hscr t k.2.2, hlen, ?_, fun i hi => ?_, ?_⟩,
      k.mono (by decide)⟩
    · rw [mt, w16.word (by simp only [hDigest]; omega_using []) (by simp only [hDigest]; omega_using [])]
      exact word_writeW_self _ _ _ _
    · rw [mt, w16.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi]),
        w8.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi])]
      show s₁.mem.readW (stackArg s 0 + BitVec.ofNat 64 (saveOff i)) 64 = _
      rw [saveOff_eq]; exact hS₁.saved i hi
    · rw [mt]
      exact ((f1.mono (Nat.zero_le _) (by omega_using [])).trans (w8.mono (Nat.zero_le _) (by omega_using []))).trans
        (w16.mono (Nat.zero_le _) (by omega_using []))

end VG.Proof.Dsa.RISCV64

end

end

/-!
# DSA verification on RISC-V: the function

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyFn.lean`). `verify_correct`:
`vg_dsa_verify` meets `vContract`. After `entry` (`front_ok`), `checkKey`
either runs `body` (`body_ok`) or leaves 0, and `restore` gives back the
callee-saved registers and `ra` (`finish_ok`); the result is the
specification's by `Proof/Dsa/Accepted.lean`'s `verifyBytes_compute`.
`verifyLike_ok` states this for any check of the key in place of
`checkKey` that behaves as it does (for prevalidated verification).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Dsa.RISCV64

theorem ret_ofNat (c : Prop) [Decidable c] :
    ((BitVec.ofNat 64 (if c then 1 else 0)).setWidth 32).toNat = if c then 1 else 0 := by
  split <;> rfl

theorem saved_all : ∀ r ∈ preserved, ∃ i < 13, r = saved i := by decide

/-- `restore`, from a state with `S` in `s6` and `s`'s callee-saved registers
and `ra` in the saved words. -/
theorem finish_ok {s u : State} {S : Addr} (h6 : u.gpr .s6 = S)
    (hwr : ∀ i < 13, InRegions u.wr (off (savW S) (8 * i)) 8)
    (hal : ∀ i < 13, (off (savW S) (8 * i)).toNat % 8 = 0)
    (hsav : ∀ i < 13, word u.mem S (saveOff i) = s.gpr (saved i)) :
    WP isa (.block restore) u fun w =>
      ((∀ r ∈ preserved, w.gpr r = s.gpr r) ∧ w.gpr .ra = s.gpr .ra) ∧ w.gpr .a0 = u.gpr .a0 := by
  refine WP.mono (restore_ok u (v := fun i => s.gpr (saved i)) h6 hwr hal fun i hi => ?_)
    fun w ⟨wrs, wot, _⟩ => ⟨⟨fun r hr => ?_, wrs 11 (by decide)⟩, wot .a0 (by decide)⟩
  · rw [← hsav i hi]
    show u.mem.readW (off (savW S) (8 * i)) 64 = u.mem.readW (S + BitVec.ofNat 64 (saveOff i)) 64
    rw [saveOff_eq]
  · obtain ⟨i, hi, rfl⟩ := saved_all r hr
    exact wrs i hi

/-- The specification, on the key's values, r, s and the digest. -/
theorem verify_spec {pl ql : Nat} {key sg dg : List Byte} {p q g y : Nat}
    (widths : Spec.Dsa.lengthsValid pl ql) (hkl : key.length = 3 * pl + ql) (hsl : sg.length = 2 * ql)
    (hkey : Spec.Dsa.publicKeyBytes pl ql key = ⟨⟨p, q, g⟩, y, none⟩) :
    Spec.Dsa.verifyBytes pl ql key sg dg = decide ((VG.Proof.Dsa.shapeValid p q ∧
      VG.Proof.Dsa.publicChecks p q g y) ∧
      ((0 < Spec.Dsa.decodeBE (sg.take ql) ∧ Spec.Dsa.decodeBE (sg.take ql) < q) ∧
        (0 < Spec.Dsa.decodeBE (sg.drop ql) ∧ Spec.Dsa.decodeBE (sg.drop ql) < q)) ∧
      vComp p q g y (Spec.Dsa.decodeBE (dg.take (Spec.Dsa.bitLength q / 8))) (Spec.Dsa.decodeBE (sg.take ql))
        (Spec.Dsa.decodeBE (sg.drop ql)) = Spec.Dsa.decodeBE (sg.take ql)) := by
  by_cases hs : VG.Proof.Dsa.shapeValid p q
  · have h8 : Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) := by
      have := hs.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
    rw [VG.Proof.Dsa.verifyBytes_compute widths hs hkl hsl hkey rfl rfl h8]
    simp only [hs, true_and, vComp, Nat.mod_mul_mod, and_assoc]
  · rw [VG.Proof.Dsa.verifyBytes_invalid_shape (by rw [hkey]; exact hs)]
    simp only [hs, false_and, decide_false]

/-- The key's values, kept by a change in `scratch`. -/
theorem keyVals_kept {s : State} {L : Lay} {key : Addr} (hk : Src s L key (3 * L.pl + L.ql)) {m m' : Mem}
    (h : Outside L.S 0 L.Z m m') :
    pOf m' L key = pOf m L key ∧ qOf m' L key = qOf m L key ∧ gOf m' L key = gOf m L key ∧
      yOf m' L key = yOf m L key := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [pOf]; rw [(hk.take (k := L.pl) (by omega_using [])).bytes h (by omega_using [])]
  · simp only [qOf]; rw [(hk.sub (o := L.pl) (k := L.ql) (by omega_using [])).bytes h (by omega_using [])]
  · simp only [gOf]; rw [(hk.sub (o := L.pl + L.ql) (k := L.pl) (by omega_using [])).bytes h (by omega_using [])]
  · simp only [yOf]; rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega_using [])).bytes h (by omega_using [])]

/-- Verification after `Verify.entry`, with the check of the key by `X`:
`checkKey`, or, when `V` gives `KeyOk`, a setup of the working spaces that
assumes it. -/
theorem verifyLike_ok {X : Prog isa → Prog isa → Prog isa} {V : Prop}
    (hX : ∀ {u : State} {L : Lay} {key sig : Addr} {d : Nat} {Q : State → Prop} {rest fail : Prog isa},
      L.Ok → ScrL u L → Regs u L key sig → word u.mem L.S hLens = pack L.pl L.ql 0 d → d < 2 ^ 16 →
      Src u L key (3 * L.pl + L.ql) → (V → KeyOk u.mem L key) →
      (∀ t, KeyOk u.mem L key → Checked u t L key sig d → Kept L u.mem t.mem → Keep ckRegs u t →
        WP isa rest t Q) →
      (∀ t, ¬ KeyOk u.mem L key → Kept L u.mem t.mem → Regs t L key sig → ScrL t L → Keep ckRegs u t →
        WP isa fail t Q) →
      WP isa (X rest fail) u Q)
    {s : State} (h : vContract.pre s) (hV : V → KeyOk s.mem (layOf s) (s.gpr .a0)) :
    WP isa (.seq (.block Verify.entry) (.seq (X Verify.body (.block [.li .a0 0])) (.block restore))) s
      fun t => ((∀ r ∈ preserved, t.gpr r = s.gpr r) ∧ t.gpr .ra = s.gpr .ra) ∧ vContract.post s t := by
  have hL := layOf_ok h
  have hZ := hL.z256
  have hpre := h
  obtain ⟨hrd, hwr, dKS, dGS, dDS, -, nwK, nwG, nwD, -, hv, hkl, hsl, -, -, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (layOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact List.mem_append_left _ hm,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
      fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩
  have hplq : 3 * (layOf s).pl + (layOf s).ql = (s.gpr .a1).toNat := by simp only [layOf]; omega_arith
  have srcK := mkSrc (A := s.gpr .a0) (k := 3 * (layOf s).pl + (layOf s).ql) (by rw [hrd]; simp) dKS nwK
    (s.gpr .a1).isLt (by omega_arith)
  have srcG := mkSrc (A := s.gpr .a4) (k := 2 * (layOf s).ql) (by rw [hrd]; simp) dGS nwG
    (s.gpr .a5).isLt (by simp only [layOf]; omega_arith)
  have srcD := mkSrc (A := s.gpr .a6) (k := (s.gpr .a7).toNat) (by rw [hrd]; simp) dDS nwD
    (s.gpr .a7).isLt (Nat.le_refl _)
  -- The specification's values.
  have hkey := VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .a0) (pLen := (layOf s).pl) (qLen := (layOf s).ql)
    (Nat.le_of_eq hplq)
  have hsg0 : (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).take (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a4) (layOf s).ql := by
    have := VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .a4) (offset := 0) (len := (layOf s).ql)
      (total := (s.gpr .a5).toNat) (by simp only [layOf]; omega_arith)
    simp only [List.drop_zero, BitVec.add_zero] at this
    exact this
  have hsg1 : (Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat).drop (s.gpr .a3).toNat =
      Spec.Rsa.bytesAt s.mem (s.gpr .a4 + BitVec.ofNat 64 (layOf s).ql) (layOf s).ql := by
    rw [← VG.Proof.Dsa.bytesAt_slice s.mem (s.gpr .a4) (offset := (layOf s).ql) (len := (layOf s).ql)
      (total := (s.gpr .a5).toNat) (by simp only [layOf]; omega_arith)]
    refine (List.take_of_length_le ?_).symm
    simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length, layOf]; omega_arith
  refine WP.seq (WP.mono (front_ok hpre) fun s₁ ⟨F, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (layOf s) → ∀ i < 13, InRegions u.wr (off (savW (stackArg s 0)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
  have hal' : ∀ u : State, ScrL u (layOf s) → ∀ i < 13, (off (savW (stackArg s 0)) (8 * i)).toNat % 8 = 0 :=
    fun u hu i hi => by
      rw [← saveOff_eq]
      exact hu.al8 (d := saveOff i) (by simp only [saveOff, layOf] at hZ ⊢; omega_arith)
        (by simp only [saveOff]; omega_using [])
  have hsav' : ∀ u : State, Kept (layOf s) s₁.mem u.mem → ∀ i < 13,
      word u.mem (stackArg s 0) (saveOff i) = s.gpr (saved i) := fun u hu i hi =>
    (hu.word (Or.inr ⟨by simp only [saveOff, hLens]; omega_using [], by simp only [saveOff]; omega_using [hi]⟩)).trans (F.sav i hi)
  have Out₁ : Outside (layOf s).S 0 (layOf s).Z s.mem s₁.mem :=
    F.out.mono (Nat.le_refl _) (by simp only [layOf] at hZ ⊢; omega_arith)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := keyVals_kept (srcK s rfl rfl) Out₁
  have hKs : KeyOk s₁.mem (layOf s) (s.gpr .a0) ↔ KeyOk s.mem (layOf s) (s.gpr .a0) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]
  have hspec := fun dg => verify_spec (sg := Spec.Rsa.bytesAt s.mem (s.gpr .a4) (s.gpr .a5).toNat) (dg := dg) hv
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hplq.symm)
    (by rw [VG.Proof.Bignum.bytesAt_length]; exact hsl) hkey
  rw [hsg0, hsg1] at hspec
  refine WP.seq (hX hL F.scr F.regs F.lens (by omega_arith) (srcK s₁ k₁.2.1 k₁.2.2) (fun hv => hKs.mpr (hV hv))
    (fun t hK hc hkp kc => ?_)
    (fun t hn hkp hrt scrt kc => ?_))
  · have kt := k₁.trans kc
    have hKt := hKs.mp hK
    refine WP.mono (body_ok hL hK hc hkp (srcK t kt.2.1 kt.2.2) (srcG t kt.2.1 kt.2.2) (by omega_arith)
      ((srcD t kt.2.1 kt.2.2).take (Nat.min_le_left _ _))
      (by rw [hkp.word (Or.inl (by simp only [hDigest, hLens]; omega_using []))]; exact F.dig))
      fun u ⟨⟨a0u, Ku, h6u, scru⟩, ku⟩ => ?_
    refine WP.mono (finish_ok h6u (hwr' u scru) (hal' u scru) fun i hi =>
        (Ku.word (by simp only [saveOff]; omega_using []) (by simp only [saveOff]; omega_using [hi])).trans (hsav' t hkp i hi))
      fun w ⟨hab, w0⟩ => ⟨hab, ?_⟩
    show ((w.gpr .a0).setWidth 32).toNat = _
    rw [w0, a0u, ret_ofNat, hspec, VG.Proof.Dsa.RISCV64.bytesAt_take]
    simp only [decide_eq_true_eq]
    refine ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl)
    have Ot : Outside (layOf s).S 0 (layOf s).Z s.mem t.mem := Out₁.trans hkp.out
    obtain ⟨er, es, ed⟩ := sig_kept (srcG s rfl rfl) (srcD s rfl rfl) Ot
      (k := min (min (s.gpr .a7).toNat 64) (Spec.Dsa.bitLength (qOf s₁.mem (layOf s) (s.gpr .a0)) / 8))
      (by omega_arith)
    rw [er, es, ed, ep₁, eq₁, eg₁, ey₁]
    rw [show min (min (s.gpr .a7).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (layOf s) (s.gpr .a0)) / 8) =
      min (s.gpr .a7).toNat (Spec.Dsa.bitLength (qOf s.mem (layOf s) (s.gpr .a0)) / 8) by
        have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith]
    exact ⟨fun h => ⟨hKt, h⟩, fun h => h.2⟩
  · refine WP.mono (WP.keep [.a0] (Q := fun u => u.gpr .a0 = 0 ∧ u.mem = t.mem) (by brun [exec_li_zero])
      (by decide) (by rfl)) fun u ⟨⟨u0, um⟩, ku⟩ => ?_
    refine WP.mono (finish_ok ((ku.gpr (by decide)).trans hrt.s6) (hwr' u (scrt.congr ku.2.2))
      (hal' u (scrt.congr ku.2.2)) fun i hi => by rw [um]; exact hsav' t hkp i hi) fun w ⟨hab, w0⟩ => ⟨hab, ?_⟩
    show ((w.gpr .a0).setWidth 32).toNat = _
    rw [w0, u0, hspec, decide_eq_false (fun hx => hn (hKs.mpr hx.1))]
    rfl

end VG.Proof.Dsa.RISCV64
