module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Spec.Dsa.SignVerify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.FrameOutside
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubSave
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run

/-!
# DSA verification on PPC64LE: the contract on the registers, and the entry

`vContract`: `vg_dsa_verify(key = r3, key_len = r4, p_len = r5, q_len = r6,
signature = r7, signature_len = r8, digest = r9, digest_len = r10, scratch,
scratch_len)`, the last two on the stack. `front_ok`: `entry` loads
`scratch`'s address from the stack, saves the nonvolatile registers in its
header, and keeps the arguments and the lengths in registers (`Regs`, `r2`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The arguments on the stack: `scratch` and `scratch_len`. -/
abbrev stackArgs (s : State) : Region := ⟨stackArgAddr s 0, 16⟩

/-- `vg_dsa_verify`, on the registers and the stack. -/
def vContract : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let sg : Region := ⟨s.gpr .r7, (s.gpr .r8).toNat⟩
    let dg : Region := ⟨s.gpr .r9, (s.gpr .r10).toNat⟩
    let scr : Region := ⟨stackArg s 0, (stackArg s 1).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 10 ≤ 2 ^ 64 ∧ s.rd = [key, sg, dg, stackArgs s] ∧ s.wr = [scr] ∧
      key.Disjoint scr ∧ sg.Disjoint scr ∧ dg.Disjoint scr ∧ scr.Disjoint (stackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r7).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + (s.gpr .r10).toNat ≤ 2 ^ 64 ∧
      (stackArg s 0).toNat + (stackArg s 1).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r5).toNat (s.gpr .r6).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r5).toNat + (s.gpr .r6).toNat ∧
      (s.gpr .r8).toNat = 2 * (s.gpr .r6).toNat ∧ Spec.Dsa.scratchWords (s.gpr .r5).toNat ≤ (stackArg s 1).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = if Spec.Dsa.verifyBytes (s.gpr .r5).toNat (s.gpr .r6).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r3) (s.gpr .r4).toNat) (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
      (Spec.Rsa.bytesAt s.mem (s.gpr .r9) (s.gpr .r10).toNat) then 1 else 0
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      stackArg s₁ 1 = stackArg s₂ 1 ∧
      Spec.Dsa.publicBytesLeak (s₁.gpr .r5).toNat (s₁.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat) ++
        [if Spec.Dsa.verifyBytes (s₁.gpr .r5).toNat (s₁.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r3) (s₁.gpr .r4).toNat)
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r7) (s₁.gpr .r8).toNat)
          (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r9) (s₁.gpr .r10).toNat) then 1 else 0] =
      Spec.Dsa.publicBytesLeak (s₂.gpr .r5).toNat (s₂.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat) ++
        [if Spec.Dsa.verifyBytes (s₂.gpr .r5).toNat (s₂.gpr .r6).toNat
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r3) (s₂.gpr .r4).toNat)
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r7) (s₂.gpr .r8).toNat)
          (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r9) (s₂.gpr .r10).toNat) then 1 else 0]

/-- A call's layout. -/
def layOf (s : State) : Lay := ⟨stackArg s 0, (stackArg s 1).toNat * 8, (s.gpr .r5).toNat, (s.gpr .r6).toNat⟩

theorem layOf_ok {s : State} (h : vContract.pre s) : (layOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [layOf]; omega, by simp only [layOf]; omega, by simp only [layOf]; omega, nw⟩

/-- `capD`'s value: `min(x, 64)`. -/
theorem cap_eq (x : BitVec 64) :
    x ^^^ (x ^^^ 64#64) &&& 0#64 - (0#64 - x >>> 6) >>> 63 = BitVec.ofNat 64 (min x.toNat 64) := by
  have hx := x.isLt
  by_cases h : x.toNat < 64
  · have e : x >>> 6 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      simp only [BitVec.toNat_ofNat]
      omega
    rw [e, BitVec.sub_self, BitVec.zero_ushiftRight, BitVec.sub_self, BitVec.and_zero, BitVec.xor_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.min_eq_left (by omega), Nat.mod_eq_of_lt hx]
  · have e : 0#64 - (0#64 - x >>> 6) >>> 63 = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
        BitVec.toNat_allOnes]
      simp only [Nat.reducePow] at *
      omega
    rw [e, BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.min_eq_right (by omega)]
    rfl

/-- `capD`: `r4 := min(digest_len, 64)`. -/
theorem capD_ok (s : State) :
    WP isa (.block Verify.capD) s fun t =>
      (t.gpr .r4 = BitVec.ofNat 64 (min (s.gpr .r10).toNat 64) ∧ t.mem = s.mem) ∧ Keep [.r0, .r4] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold Verify.capD
  prun [cap_eq]

/-- The lengths into `r2`. -/
theorem pack_entry (x y : BitVec 64) {d : Nat} (hx : x.toNat < 2 ^ 16) (hy : y.toNat < 2 ^ 16) (hd : d < 2 ^ 16) :
    x + y <<< 16 + BitVec.ofNat 64 d <<< 48 = pack x.toNat y.toNat 0 d := by
  apply BitVec.eq_of_toNat_eq
  rw [pack_toNat hx hy (by decide) hd]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  simp only [Nat.reducePow] at *
  omega

/-- After the registers are saved: the key, the signature and the digest into
`r27`, `r28` and `r26`, and the lengths into `r2`. -/
theorem front_tail (s : State) (h5 : (s.gpr .r5).toNat < 2 ^ 16) (h6 : (s.gpr .r6).toNat < 2 ^ 16) :
    WP isa (.block (([.addi .r27 .r3 0, .addi .r28 .r7 0, .addi .r26 .r9 0] : List Instr) ++ (Verify.capD ++
      ([.lsl .r4 .r4 48, .lsl .r0 .r6 16, .add .r2 .r5 .r0, .add .r2 .r2 .r4] : List Instr)))) s fun t =>
      (t.gpr .r27 = s.gpr .r3 ∧ t.gpr .r28 = s.gpr .r7 ∧ t.gpr .r26 = s.gpr .r9 ∧
        t.gpr .r2 = pack (s.gpr .r5).toNat (s.gpr .r6).toNat 0 (min (s.gpr .r10).toNat 64) ∧ t.mem = s.mem) ∧
        Keep [.r27, .r28, .r26, .r0, .r4, .r2] s t := by
  refine WP.block_append (WP.mono (WP.keep [.r27, .r28, .r26] (Q := fun u => u.gpr .r27 = s.gpr .r3 ∧
      u.gpr .r28 = s.gpr .r7 ∧ u.gpr .r26 = s.gpr .r9 ∧ u.mem = s.mem) (by prun [BitVec.add_zero]) (by decide))
    fun u ⟨⟨a27, a28, a26, mu⟩, ku⟩ => ?_)
  refine WP.block_append (WP.mono (capD_ok u) fun v ⟨⟨b4, mv⟩, kv⟩ => ?_)
  rw [ku.gpr .r10 (by decide)] at b4
  have v5 : v.gpr .r5 = s.gpr .r5 := (kv.gpr .r5 (by decide)).trans (ku.gpr .r5 (by decide))
  have v6 : v.gpr .r6 = s.gpr .r6 := (kv.gpr .r6 (by decide)).trans (ku.gpr .r6 (by decide))
  refine WP.mono (WP.keep [.r4, .r0, .r2] (Q := fun w =>
      w.gpr .r2 = pack (s.gpr .r5).toNat (s.gpr .r6).toNat 0 (min (s.gpr .r10).toNat 64) ∧ w.mem = v.mem)
    (by prun [b4, v5, v6, pack_entry _ _ h5 h6 (show min (s.gpr .r10).toNat 64 < 2 ^ 16 by omega)]) (by decide))
    fun w ⟨⟨c2, mw⟩, kw⟩ => ⟨⟨(kw.gpr .r27 (by decide)).trans ((kv.gpr .r27 (by decide)).trans a27),
      (kw.gpr .r28 (by decide)).trans ((kv.gpr .r28 (by decide)).trans a28),
      (kw.gpr .r26 (by decide)).trans ((kv.gpr .r26 (by decide)).trans a26), c2, mw.trans (mv.trans mu)⟩,
      ((ku.trans kv).trans kw).mono (by decide)⟩

/-- The registers `entry` writes. -/
def entryRegs : List Reg := [.r0, .r2, .r4, .r11, .r21, .r26, .r27, .r28]

theorem front_saved_ne11 : ∀ i < 19, saved i ≠ .r11 := by decide

/-- `entry`: `scratch` (from the stack) into `r21`, the nonvolatile registers
saved in its header, and the arguments and lengths into registers (`Regs`,
`r2`). Memory changes only in the header. -/
theorem front_ok {s : State} (h : vContract.pre s) :
    WP isa (.block Verify.entry) s fun t =>
      (Regs t (layOf s) (s.gpr .r3) (s.gpr .r7) (s.gpr .r9) ∧ ScrL t (layOf s) ∧
        t.gpr .r2 = pack (layOf s).pl (layOf s).ql 0 (min (s.gpr .r10).toNat 64) ∧
        (∀ i < 19, word t.mem (stackArg s 0) (saveOff i) = s.gpr (saved i)) ∧
        Outside (stackArg s 0) 0 256 s.mem t.mem) ∧ Keep entryRegs s t := by
  have hL := layOf_ok h
  have hZ := hL.z256
  have hpl : (s.gpr .r5).toNat < 2 ^ 16 := by have := hL.pl; simp only [layOf] at this; omega
  have hql : (s.gpr .r6).toNat < 2 ^ 16 := by have := hL.ql; simp only [layOf] at this; omega
  obtain ⟨-, hrd, hwr, -, -, -, -, -, -, -, nw, -, -, -, -⟩ := h
  unfold Verify.entry
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (Pub.loadS_ok s ⟨stackArgs s, List.mem_append_left _ (by rw [hrd]; simp),
    by simp [Region.Contains]⟩) fun s₁ ⟨⟨a11, m1, _⟩, k1⟩ => ?_)
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (layOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [layOf]) nw
  have hin : ∀ i < 19, InRegions s₁.wr (off (savW (s₁.gpr .r11)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq, a11]
    exact (hscr s₁ k1.wr).st (d := 104 + 8 * i) (by simp only [layOf] at hZ ⊢; omega)
  refine WP.block_append (WP.mono (save_ok s₁ hin) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have h21 : s₂.gpr .r21 = stackArg s 0 := hS.r21.trans a11
  have e : ∀ r, r ≠ .r11 → r ≠ .r21 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr r fun hm => by
      simp only [List.mem_append, List.mem_singleton] at hm
      exact hm.elim h1 h2
  refine WP.mono (front_tail s₂ (by rw [e _ (by decide) (by decide)]; exact hpl)
    (by rw [e _ (by decide) (by decide)]; exact hql)) fun t ⟨⟨t27, t28, t26, t2, mt⟩, kt⟩ => ?_
  have k := k12.trans kt
  rw [e .r3 (by decide) (by decide)] at t27
  rw [e .r7 (by decide) (by decide)] at t28
  rw [e .r9 (by decide) (by decide)] at t26
  rw [e .r5 (by decide) (by decide), e .r6 (by decide) (by decide), e .r10 (by decide) (by decide)] at t2
  have t21 : t.gpr .r21 = stackArg s 0 := (kt.gpr .r21 (by decide)).trans h21
  refine ⟨⟨Regs.of_pack hL t21 t27 t28 t26 t2 (by decide) (by omega), hscr t k.wr, t2, fun i hi => ?_, ?_⟩,
    k.mono (by decide)⟩
  · rw [mt]
    show s₂.mem.readW (stackArg s 0 + BitVec.ofNat 64 (104 + 8 * i)) 64 = _
    rw [saveOff_eq, ← a11, hS.saved i hi]
    exact k1.gpr _ fun h => front_saved_ne11 i hi (List.mem_singleton.mp h)
  · have f2 : Outside (stackArg s 0) 104 152 s₁.mem s₂.mem :=
      VG.Proof.Bignum.frame_outside (by rw [← a11]; exact hS.frame) (by decide)
    rw [mt, ← m1]
    exact f2.mono (Nat.zero_le _) (by decide)

end VG.Proof.Dsa.PPC64LE
