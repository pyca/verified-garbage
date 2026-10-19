module

public import VerifiedGarbage.Impl.Ffdh.X86_64.GenerateKey
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
public import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Ws
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp

/-! # FFDH on x86-64: mask a rejected scalar's output -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.GenerateKey

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.Domain VG.Impl.Ffdh.X86_64.Domain.GenerateKey
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

/-- The masked prefix and unchanged remainder of a scalar buffer. -/
structure MaskInv (s₀ : State) (op : Addr) (len : Nat) (c : Bool) (j : Nat) (t : State) : Prop where
  keep : Keep [.rax, .r11, .rcx] s₀ t
  ptr : t.gpr .r11 = off op j
  count : t.gpr .rcx = BitVec.ofNat 64 (len - j)
  bytes : ∀ i < j, t.mem (off op i) = if c then s₀.mem (off op i) else 0
  frame : ∀ a, (∀ i < j, a ≠ off op i) → t.mem a = s₀.mem a

theorem maskBody_ok {s : State} {op : Addr} {j len : Nat} {c : Bool}
    (hj : j < len) (hl : len < 2 ^ 31) (hp : s.gpr .r11 = off op j)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (len - j)) (hm : s.gpr .r15 = mask c)
    (hwr : InRegions s.wr (off op j) 1) :
    WP isa (.block maskBody) s fun t =>
      (t.mem = s.mem.writeW (off op j) (if c then s.mem (off op j) else (0 : Byte)) ∧
      t.gpr .r11 = off op (j + 1) ∧ t.gpr .rcx = BitVec.ofNat 64 (len - (j + 1)) ∧
      t.zf = some (decide (j + 1 = len))) ∧ Keep [.rax, .r11, .rcx] s t := by
  have hrd : InRegions (s.rd ++ s.wr) (off op j) 1 :=
    let ⟨r, hr, hc⟩ := hwr; ⟨r, List.mem_append_right _ hr, hc⟩
  have hmByte : ((s.mem (off op j)).setWidth 64 &&& mask c).setWidth 8 =
      if c then s.mem (off op j) else 0 := by
    cases c <;> simp [mask, BitVec.setWidth_and]
    exact BitVec.and_allOnes
  refine WP.keep _ ?_ rfl
  unfold maskBody
  xrun [State.ea, at0, hp, hcx, hm,
    show off op j + BitVec.ofInt 64 0 = off op j by simp, hrd, hwr, hmByte,
    ofNat64_pred (show 1 ≤ len - j by omega) (by omega),
    ofNat64_beq_zero (show len - j - 1 < 2 ^ 64 by omega)]
  refine ⟨?_, ?_, ?_⟩
  · simp only [off, BitVec.add_assoc, ofNat_add_one]
  · rw [show len - j - 1 = len - (j + 1) by omega]
  · exact decide_eq_decide.mpr (by omega)

theorem maskStep_ok {s₀ t : State} {op : Addr} {j len : Nat} {c : Bool}
    (hj : j < len) (hl : len < 2 ^ 31) (hm : s₀.gpr .r15 = mask c)
    (hwr : ∀ i < len, InRegions s₀.wr (off op i) 1) (h : MaskInv s₀ op len c j t) :
    WP isa (.block maskBody) t fun u =>
      u.zf = some (decide (j + 1 = len)) ∧ MaskInv s₀ op len c (j + 1) u := by
  refine WP.mono (maskBody_ok hj hl h.ptr h.count ((h.keep.gpr (by decide)).trans hm)
    (by rw [h.keep.2.2]; exact hwr j hj)) fun u ⟨⟨hmem, hp, hcount, hz⟩, k⟩ => ?_
  refine ⟨hz, ⟨keep_trans h.keep k, hp, hcount, ?_, ?_⟩⟩
  · intro i hi
    rw [hmem, WriteBytes.writeW8_apply]
    by_cases he : i = j
    · subst he
      rw [ite_eq_left rfl, h.frame _ (fun i hi => out_ne (by omega) (by omega) (by omega))]
    · rw [ite_eq_right (out_ne (by omega) (by omega) he)]
      exact h.bytes i (by omega)
  · intro a ha
    rw [hmem, WriteBytes.writeW8_apply, ite_eq_right (ha j (by omega))]
    exact h.frame a (fun i hi => ha i (by omega))

/-- The mask loop writes every byte on both success and failure. -/
theorem mask_ok {s : State} {op : Addr} {len : Nat} {c : Bool}
    (hl1 : 1 ≤ len) (hl : len < 2 ^ 31) (hp : s.gpr .r11 = op)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 len) (hm : s.gpr .r15 = mask c)
    (hwr : ∀ i < len, InRegions s.wr (off op i) 1) :
    WP isa (.loop (.block maskBody) .ne) s (MaskInv s op len c len) :=
  wp_upto (a := 0) (by omega) (MaskInv s op len c)
    (fun j _ hj t ht => maskStep_ok hj hl hm hwr ht) (fun _ h => h)
    ⟨Keep.refl _ _, by rw [hp]; simp, by rw [hcx, Nat.sub_zero], fun i hi => by omega, fun _ _ => rfl⟩

end VG.Proof.Ffdh.X86_64.GenerateKey
