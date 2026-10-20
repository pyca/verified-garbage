module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.KeyScalar
public import VerifiedGarbage.Proof.Rsa.X86_64.CvStore
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # FFDH on x86-64: cutting random octets to the public scalar bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

private theorem cmov_reg (s : State) (cc : Cond) (d r : Reg) :
    execCmov cc d (.reg r) s = (eval cc s).map
      (fun c => s.setReg d (if c then s.gpr r else s.gpr d)) := by
  simp only [execCmov, readSrc, Option.bind_some]
  congr 1
  funext c
  cases c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    symm
    simp only [State.setReg]
    congr 1
    funext r'
    split <;> simp_all
  · rfl

/-- One scalar byte is written without branching on its value. -/
theorem cutBody_ok {s : State} {rp xp : Addr} {j ld k : Nat} {b : Byte} {msk : BitVec 64}
    (hj : j < k) (hk : k < 2 ^ 31) (hld : ld < k)
    (hrp : s.gpr .r10 = off rp j) (hxp : s.gpr .r11 = off xp j)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 j) (h8 : s.gpr .r8 = BitVec.ofNat 64 ld)
    (h9 : s.gpr .r9 = msk) (h14 : s.gpr .r14 = BitVec.ofNat 64 (k - j))
    (hrd : InRegions (s.rd ++ s.wr) (off rp j) 1) (hwr : InRegions s.wr (off xp j) 1)
    (hb : s.mem (off rp j) = b) :
    WP isa (.block cutBody) s fun t =>
      (t.mem = s.mem.writeW (off xp j)
        (if j < ld then (0 : Byte) else if j = ld then b &&& msk.setWidth 8 else b) ∧
      t.gpr .r10 = off rp (j + 1) ∧ t.gpr .r11 = off xp (j + 1) ∧
      t.gpr .rcx = BitVec.ofNat 64 (j + 1) ∧ t.gpr .r14 = BitVec.ofNat 64 (k - (j + 1)) ∧
      t.zf = some (decide (j + 1 = k))) ∧ Keep [.rax, .rdx, .rbx, .r10, .r11, .rcx, .r14] s t := by
  have hj64 : j < 2 ^ 64 := by omega
  have hld64 : ld < 2 ^ 64 := by omega
  have hcmp : decide ((BitVec.ofNat 64 j).toNat < (BitVec.ofNat 64 ld).toNat) = decide (j < ld) := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hld64]
  have heq : (BitVec.ofNat 64 j == BitVec.ofNat 64 ld) = decide (j = ld) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64, Nat.mod_eq_of_lt hld64] at this
      exact this
    · exact congrArg (BitVec.ofNat 64)
  refine WP.keep _ ?_ rfl
  unfold cutBody
  xrun [State.ea, at0, hrp, hxp, hcx, h8, h9, h14,
    show off rp j + BitVec.ofInt 64 0 = off rp j by simp,
    show off xp j + BitVec.ofInt 64 0 = off xp j by simp, hrd, hwr, hb, hcmp, sub_beq_zero, heq, cmov_reg, eval]
  refine ⟨?_, ?_, ?_, ofNat_add_one j, ?_, ?_⟩
  · apply congrArg (s.mem.writeW (off xp j))
    simp only [decide_eq_true_eq]
    by_cases he : j = ld
    · simp only [ite_eq_left he, ite_eq_right (show ¬ j < ld by omega)]
      simp [BitVec.setWidth_and]
    · simp only [ite_eq_right he]
      by_cases hl : j < ld <;> simp [hl, BitVec.setWidth_and]
      exact BitVec.and_allOnes
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl]
    omega
  · apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl] at this
      omega
    · intro h
      rw [show k - j = 1 by omega]
      rfl

/-- The loop invariant records the written prefix and preserves every other byte. -/
structure CutInv (s₀ : State) (rp xp : Addr) (rb : List Byte) (ld : Nat)
    (msk : BitVec 64) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .rdx, .rbx, .r10, .r11, .rcx, .r14] s₀ t
  ptrR : t.gpr .r10 = off rp j
  ptrX : t.gpr .r11 = off xp j
  cx : t.gpr .rcx = BitVec.ofNat 64 j
  count : t.gpr .r14 = BitVec.ofNat 64 (rb.length - j)
  bytes : ∀ i < j, t.mem (off xp i) =
    if i < ld then 0 else if i = ld then rb.getD i 0 &&& msk.setWidth 8 else rb.getD i 0
  frame : ∀ a, (∀ i < j, a ≠ off xp i) → t.mem a = s₀.mem a

/-- Extend the written prefix by one byte, leaving unread randomness intact. -/
theorem cutStep_ok {s₀ t : State} {rp xp : Addr} {rb : List Byte} {ld j : Nat} {msk : BitVec 64}
    (hk : rb.length < 2 ^ 31) (hj : j < rb.length) (hld : ld < rb.length)
    (h8 : s₀.gpr .r8 = BitVec.ofNat 64 ld) (h9 : s₀.gpr .r9 = msk)
    (hrd : ∀ i < rb.length, InRegions (s₀.rd ++ s₀.wr) (off rp i) 1)
    (hwr : ∀ i < rb.length, InRegions s₀.wr (off xp i) 1)
    (hb : ∀ i < rb.length, s₀.mem (off rp i) = rb.getD i 0)
    (hsep : ∀ i < rb.length, ∀ l < rb.length, off rp i ≠ off xp l)
    (h : CutInv s₀ rp xp rb ld msk j t) :
    WP isa (.block cutBody) t fun u =>
      u.zf = some (decide (j + 1 = rb.length)) ∧ CutInv s₀ rp xp rb ld msk (j + 1) u := by
  have hrd' : InRegions (t.rd ++ t.wr) (off rp j) 1 := by
    rw [h.keep.2.1, h.keep.2.2]; exact hrd j hj
  have hwr' : InRegions t.wr (off xp j) 1 := by rw [h.keep.2.2]; exact hwr j hj
  have hb' : t.mem (off rp j) = rb.getD j 0 := by
    rw [h.frame _ (fun i hi => hsep j hj i (by omega))]; exact hb j hj
  refine WP.mono (cutBody_ok hj hk hld h.ptrR h.ptrX h.cx
    ((h.keep.gpr (by decide)).trans h8) ((h.keep.gpr (by decide)).trans h9)
    h.count hrd' hwr' hb') fun u ⟨⟨hm, hrp, hxp, hcx, hcount, hz⟩, k⟩ => ?_
  refine ⟨hz, ⟨keep_trans h.keep k, hrp, hxp, hcx, hcount, ?_, ?_⟩⟩
  · intro i hi
    rw [hm, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl]
    · rw [ite_eq_right (out_ne (by omega) (by omega) he)]
      exact h.bytes i (by omega)
  · intro a ha
    rw [hm, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega))]
    exact h.frame a (fun i hi => ha i (by omega))

/-- Cut all random octets with a fixed trip count determined by the public width. -/
theorem cut_ok {s : State} {rp xp : Addr} {rb : List Byte} {ld : Nat} {msk : BitVec 64}
    (hk1 : 1 ≤ rb.length) (hk : rb.length < 2 ^ 31) (hld : ld < rb.length)
    (hrp : s.gpr .r10 = rp) (hxp : s.gpr .r11 = xp) (hcx : s.gpr .rcx = 0)
    (h8 : s.gpr .r8 = BitVec.ofNat 64 ld) (h9 : s.gpr .r9 = msk)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 rb.length)
    (hrd : ∀ i < rb.length, InRegions (s.rd ++ s.wr) (off rp i) 1)
    (hwr : ∀ i < rb.length, InRegions s.wr (off xp i) 1)
    (hb : ∀ i < rb.length, s.mem (off rp i) = rb.getD i 0)
    (hsep : ∀ i < rb.length, ∀ l < rb.length, off rp i ≠ off xp l) :
    WP isa (.loop (.block cutBody) .ne) s (CutInv s rp xp rb ld msk rb.length) :=
  wp_upto (a := 0) (by omega) (CutInv s rp xp rb ld msk)
    (fun j _ hj t ht => cutStep_ok hk hj hld h8 h9 hrd hwr hb hsep ht)
    (fun _ h => h) ⟨Keep.refl _ _, by rw [hrp]; simp, by rw [hxp]; simp,
      hcx, by simpa only [Nat.sub_zero] using h14, fun i hi => by omega, fun _ _ => rfl⟩

/-- Writing the scalar preserves every byte of the scratch workspace. -/
theorem CutInv.outside {s t : State} {B rp xp : Addr} {Z : Nat} {rb : List Byte}
    {ld : Nat} {msk : BitVec 64} (h : CutInv s rp xp rb ld msk rb.length t)
    (ho : VG.Proof.Rsa.X86_64.OutOk s B Z xp rb.length) :
    Outside B Z (2 ^ 64 - Z) s.mem t.mem := by
  intro a ha
  have ha64 : ofs B a < 2 ^ 64 := (a - B).isLt
  apply h.frame
  intro i hi he
  have hh : Z ≤ ofs B (off xp i) := ho.sep i hi
  rw [← he] at hh
  omega

/-- The cut loop preserves a disjoint input, including a previously zeroed y. -/
theorem CutInv.src_keep {s t : State} {B rp xp ip : Addr} {Z : Nat} {rb bs : List Byte}
    {ld : Nat} {msk : BitVec 64} (h : CutInv s rp xp rb ld msk rb.length t)
    (hi : Src s B Z ip bs) (ha : VG.Proof.Rsa.X86_64.Apart xp rb.length ip bs.length) :
    Src t B Z ip bs :=
  ⟨fun i hl => by rw [h.keep.2.1, h.keep.2.2]; exact hi.rd i hl,
    fun i hl => by rw [h.frame _ (fun j hj => Ne.symm (ha j hj i hl))]; exact hi.val i hl, hi.out⟩

/-- The full scalar output is exactly `KeyScalar.cut`, and can be reused as an input. -/
theorem CutInv.src {s t : State} {B rp xp : Addr} {Z : Nat} {rb : List Byte}
    {ld : Nat} {msk : BitVec 64} (h : CutInv s rp xp rb ld msk rb.length t)
    (hld : ld < rb.length) (ho : VG.Proof.Rsa.X86_64.OutOk s B Z xp rb.length) :
    Src t B Z xp (KeyScalar.cut rb ld (msk.setWidth 8)) := by
  have hl := KeyScalar.cut_length (msk.setWidth 8) hld
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨r, hr, hc⟩ := ho.wr i (by rwa [hl] at hi)
    exact ⟨r, List.mem_append_right _ (by rw [h.keep.2.2]; exact hr), hc⟩
  · intro i hi
    have hi' : i < rb.length := by rwa [hl] at hi
    rw [h.bytes i hi', KeyScalar.cut_get _ hld hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
  · intro i hi
    exact ho.sep i (by rwa [hl] at hi)

end VG.Proof.Ffdh.X86_64.GenerateKey
