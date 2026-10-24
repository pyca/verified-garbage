module

import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Front
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Derive
public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Bignum.FrameOutside
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Common
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.Words
public import VerifiedGarbage.Spec.Dsa.SignVerify
public import VerifiedGarbage.TCB.PPC64LE.Target

/-!
# DSA key derivation on PPC64LE: the contract on the registers, and the entry

`dContract`: `vg_dsa_derive_key(out = r3, out_len = r4, params = r5,
params_len = r6, p_len = r7, x = r8, q_len = r9, scratch = r10,
scratch_len)`, `scratch_len` on the stack. `dfront_ok`: `entry` saves the
nonvolatile registers in `scratch`'s header, and keeps the domain, x, `out`
and the lengths in registers (`Regs`, with x as the signature and `out` as
the digest, and `r2`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Impl.Bignum VG.Impl.Dsa.PPC64LE

/-- The argument on the stack: `scratch_len`. -/
abbrev dStackArgs (s : State) : Region := ⟨stackArgAddr s 0, 8⟩

/-- The key `deriveKeyBytes` gives, on entry. -/
def dRes (s : State) : Option (List Byte) :=
  Spec.Dsa.deriveKeyBytes (s.gpr .r7).toNat (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)

/-- `vg_dsa_derive_key`, on the registers and the stack. -/
def dContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .r3, (s.gpr .r4).toNat⟩
    let ps : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
    let xr : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let scr : Region := ⟨s.gpr .r10, (stackArg s 0).toNat * 8⟩
    s.sp.toNat + 32 + 8 * 9 ≤ 2 ^ 64 ∧ s.rd = [ps, xr, dStackArgs s] ∧ s.wr = [out, scr] ∧
      out.Disjoint ps ∧ out.Disjoint xr ∧ out.Disjoint scr ∧ out.Disjoint (dStackArgs s) ∧
      ps.Disjoint scr ∧ xr.Disjoint scr ∧ scr.Disjoint (dStackArgs s) ∧
      (s.gpr .r3).toNat + (s.gpr .r4).toNat ≤ 2 ^ 64 ∧ (s.gpr .r5).toNat + (s.gpr .r6).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (s.gpr .r10).toNat + (stackArg s 0).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Dsa.lengthsValid (s.gpr .r7).toNat (s.gpr .r9).toNat ∧
      (s.gpr .r4).toNat = 3 * (s.gpr .r7).toNat + 2 * (s.gpr .r9).toNat ∧
      (s.gpr .r6).toNat = 2 * (s.gpr .r7).toNat + (s.gpr .r9).toNat ∧
      Spec.Dsa.scratchWords (s.gpr .r7).toNat ≤ (stackArg s 0).toNat
  post s t :=
    ((t.gpr .r3).setWidth 32).toNat = Spec.Dsa.signStatus (dRes s) ∧
      Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r4).toNat = (dRes s).getD (List.replicate (s.gpr .r4).toNat 0)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ s₁.gpr .r4 = s₂.gpr .r4 ∧ s₁.gpr .r5 = s₂.gpr .r5 ∧
      s₁.gpr .r6 = s₂.gpr .r6 ∧ s₁.gpr .r7 = s₂.gpr .r7 ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .r10 = s₂.gpr .r10 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
      (Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r5) (s₁.gpr .r6).toNat).map (·.toNat) ++ [Spec.Dsa.signStatus (dRes s₁)] =
      (Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r5) (s₂.gpr .r6).toNat).map (·.toNat) ++ [Spec.Dsa.signStatus (dRes s₂)]

/-- A call's layout. -/
def dlayOf (s : State) : Lay := ⟨s.gpr .r10, (stackArg s 0).toNat * 8, (s.gpr .r7).toNat, (s.gpr .r9).toNat⟩

theorem dlayOf_ok {s : State} (h : dContract.pre s) : (dlayOf s).Ok := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, nw, hv, -, -, hsw⟩ := h
  simp only [Spec.Dsa.scratchWords] at hsw
  simp only [Spec.Dsa.lengthsValid] at hv
  exact ⟨by simp only [dlayOf]; omega, by simp only [dlayOf]; omega, by simp only [dlayOf]; omega, nw⟩

/-- The registers `Derive.entry` writes. -/
def dentryRegs : List Reg := [.r0, .r2, .r11, .r21, .r26, .r27, .r28]

/-- `Derive.entry`: `scratch` into `r21`, the nonvolatile registers saved in
its header, and the domain, x, `out` and the lengths into registers (`Regs`,
`r2`). Memory changes only in the header. -/
theorem dfront_ok {s : State} (h : dContract.pre s) :
    WP isa (.block Derive.entry) s fun t =>
      (Regs t (dlayOf s) (s.gpr .r5) (s.gpr .r8) (s.gpr .r3) ∧ ScrL t (dlayOf s) ∧
        t.gpr .r2 = pack (dlayOf s).pl (dlayOf s).ql 0 0 ∧
        (∀ i < 19, word t.mem (s.gpr .r10) (saveOff i) = s.gpr (saved i)) ∧
        Outside (s.gpr .r10) 0 256 s.mem t.mem) ∧ Keep dentryRegs s t := by
  have hL := dlayOf_ok h
  have hZ := hL.z256
  have hpl : (s.gpr .r7).toNat < 2 ^ 16 := by have := hL.pl; simp only [dlayOf] at this; omega
  have hql : (s.gpr .r9).toNat < 2 ^ 16 := by have := hL.ql; simp only [dlayOf] at this; omega
  obtain ⟨-, -, hwr, -, -, -, -, -, -, -, -, -, -, nw, -⟩ := h
  unfold Derive.entry
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (WP.keep [.r11] (Q := fun u => u.gpr .r11 = s.gpr .r10 ∧ u.mem = s.mem)
    (by prun [BitVec.add_zero]) (by decide)) fun s₁ ⟨⟨a11, m1⟩, k1⟩ => ?_)
  have hscr : ∀ t : State, t.wr = s.wr → ScrL t (dlayOf s) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr]; simp [dlayOf]) nw
  have hin : ∀ i < 19, InRegions s₁.wr (off (savW (s₁.gpr .r11)) (8 * i)) 8 := fun i hi => by
    rw [← saveOff_eq, a11]
    exact (hscr s₁ k1.wr).st (d := 104 + 8 * i) (by simp only [dlayOf] at hZ ⊢; omega)
  refine WP.block_append (WP.mono (save_ok s₁ hin) fun s₂ hS => ?_)
  have k12 := k1.trans hS.keep
  have h21 : s₂.gpr .r21 = s.gpr .r10 := hS.r21.trans a11
  have e : ∀ r, r ≠ .r11 → r ≠ .r21 → s₂.gpr r = s.gpr r := fun r h1 h2 =>
    k12.gpr r fun hm => by
      simp only [List.mem_append, List.mem_singleton] at hm
      exact hm.elim h1 h2
  have e3 := e .r3 (by decide) (by decide)
  have e5 := e .r5 (by decide) (by decide)
  have e7 := e .r7 (by decide) (by decide)
  have e8 := e .r8 (by decide) (by decide)
  have e9 := e .r9 (by decide) (by decide)
  refine WP.mono (WP.keep [.r27, .r28, .r26, .r0, .r2] (Q := fun t => t.gpr .r27 = s.gpr .r5 ∧
      t.gpr .r28 = s.gpr .r8 ∧ t.gpr .r26 = s.gpr .r3 ∧ t.gpr .r2 = pack (s.gpr .r7).toNat (s.gpr .r9).toNat 0 0 ∧
      t.mem = s₂.mem) (by prun [e3, e5, e7, e8, e9, BitVec.add_zero, pack_entry0 _ _ hpl hql]) (by decide))
    fun t ⟨⟨t27, t28, t26, t2, mt⟩, kt⟩ => ?_
  have k := k12.trans kt
  have t21 : t.gpr .r21 = s.gpr .r10 := (kt.gpr .r21 (by decide)).trans h21
  refine ⟨⟨Regs.of_pack hL t21 t27 t28 t26 t2 (by decide) (by decide), hscr t k.wr, t2, fun i hi => ?_, ?_⟩,
    k.mono (by decide)⟩
  · rw [mt]
    show s₂.mem.readW (s.gpr .r10 + BitVec.ofNat 64 (104 + 8 * i)) 64 = _
    rw [saveOff_eq, ← a11, hS.saved i hi]
    exact k1.gpr _ fun h => pfront_saved_ne11 i hi (List.mem_singleton.mp h)
  · have f2 : Outside (s.gpr .r10) 104 152 s₁.mem s₂.mem :=
      VG.Proof.Bignum.frame_outside (by rw [← a11]; exact hS.frame) (by decide)
    rw [mt, ← m1]
    exact f2.mono (Nat.zero_le _) (by decide)

end VG.Proof.Dsa.PPC64LE
