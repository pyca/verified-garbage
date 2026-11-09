module

public import VerifiedGarbage.Impl.Rsa.X86_64.WordReduce
public import VerifiedGarbage.Proof.Bignum.X86_64.R2wSub
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Loop

/-! # The multiply-subtract with a low input word

The existing multiword subtraction invariant carries the low input digit
unchanged through its limb steps.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86_64.WordReduce

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.R2Words
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Bignum.X86_64.R2w

theorem subHead_ok (s : State) {aM aT aD : Addr}
    (eM : s.gpr .r10 + BitVec.ofInt 64 0 = aM) (eT : s.gpr .r8 + BitVec.ofInt 64 0 = aT)
    (eD : s.gpr .rbp + BitVec.ofInt 64 8 = aD)
    (hMr : InRegions (s.rd ++ s.wr) aM 8) (hT : InRegions s.wr aT 8)
    (hD : InRegions (s.rd ++ s.wr) aD 8) :
    WP isa (.block Impl.Rsa.X86_64.WordReduce.subHead) s fun t =>
      ∃ (v : BitVec 64) (b : Bool), t.mem = s.mem.writeW aT v ∧ t.gpr .rbp = mask b ∧
        v.toNat + (s.gpr .rcx).toNat * (s.mem.readW aM 64).toNat =
          (s.mem.readW aD 64).toNat + 2 ^ 64 * ((t.gpr .r9).toNat + b.toNat) ∧
      Keep [.rax, .rdx, .rbp, .r9] s t := by
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r9] (Q := fun t =>
    ∃ (v : BitVec 64) (b : Bool), t.mem = s.mem.writeW aT v ∧ t.gpr .rbp = mask b ∧
      v.toNat + (s.gpr .rcx).toNat * (s.mem.readW aM 64).toNat =
        (s.mem.readW aD 64).toNat + 2 ^ 64 * ((t.gpr .r9).toNat + b.toNat)) ?_ rfl)
    fun t ⟨h, k⟩ => let ⟨v, b, h1, h2, h3⟩ := h; ⟨v, b, h1, h2, h3, k⟩
  unfold Impl.Rsa.X86_64.WordReduce.subHead cfToRbp
  xrun [State.ea, at0, eM, eT, eD, hMr, hT, hD]
  refine ⟨_, _, rfl, rfl, ?_⟩
  have hm := mul_toNat (s.mem.readW aM 64) (s.gpr .rcx)
  have hs := sbb_toNat (s.mem.readW aD 64)
    (BitVec.ofNat 64 ((s.mem.readW aM 64).toNat * (s.gpr .rcx).toNat)) false
  simp only [Bool.toNat_false, Nat.add_zero,
    show (BitVec.ofBool false).setWidth 64 = (0#64 : BitVec 64) from rfl, BitVec.sub_zero] at hs
  rw [Nat.mul_comm (s.gpr .rcx).toNat]
  omega_arith

theorem mulSub_ok {s : State} {B : Addr} {Z w ex em et ev : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B ex) (h10 : s.gpr .r10 = off B em) (h8 : s.gpr .r8 = off B et)
    (hbp : s.gpr .rbp = off B ev) (hV : ev + 16 ≤ Z)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hX : ex + 8 * w ≤ Z)
    (hM : em + 8 * w ≤ Z) (hT : et + 8 * (w + 1) ≤ Z)
    (sX : et + 8 * (w + 1) ≤ ex ∨ ex + 8 * w ≤ et) (sM : et + 8 * (w + 1) ≤ em ∨ em + 8 * w ≤ et) :
    WP isa Impl.Rsa.X86_64.WordReduce.mulSub s fun t => ∃ b : Bool,
      wv t.mem B et (w + 1) + (s.gpr .rcx).toNat * wv s.mem B em w =
        wv s.mem B ex w * 2 ^ 64 + (word s.mem B (ev + 8)).toNat + 2 ^ (64 * (w + 1)) * b.toNat ∧
      Outside B et (8 * (w + 1)) s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r9, .r14] s t := by
  have hn := hs.nowrap
  unfold Impl.Rsa.X86_64.WordReduce.mulSub
  refine WP.seq (WP.mono (subHead_ok s (by rw [h10]; simp [off]) (by rw [h8]; simp [off])
    (by rw [hbp]; simp [off, BitVec.add_assoc, BitVec.ofNat_add])
    (hs.ld (d := em) (by omega_arith)) (hs.st (d := et) (by omega_arith)) (hs.ld hV)) fun t₁ ⟨v, b, hm₁, hbp₁, hv₁, k₁⟩ => ?_)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = t₁.mem → Keep [.r14] t₁ t → t.cf = t₁.cf →
      MsInv s B Z ex em et (s.gpr .rcx).toNat 1 t (word s.mem B (ev + 8)).toNat := fun t h14 hm k _ => by
    refine ⟨hs.congr (k.2.2.trans k₁.2.2), (k₁.trans k).mono (by decide), h14, ?_, ⟨b, ?_, ?_⟩⟩
    · rw [hm, hm₁]
      intro x hx
      rw [writeW_outside s.mem B v (by omega_arith) x (by omega_arith)]
    · rw [k.gpr (by decide), hbp₁]
    · rw [hm, hm₁, k.gpr (by decide)]
      simp only [wv, Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.add_zero, Nat.pow_zero,
        word_writeW_self, Nat.one_mul, Nat.sub_self, Nat.zero_mul]
      exact hv₁
  refine WP.seq (WP.mono (wordLoop_ok (start := 1) (N := w) (by omega_arith) hw' (fun j t => MsInv s B Z ex em et (s.gpr .rcx).toNat j t (word s.mem B (ev + 8)).toNat)
    h0 (fun j hj1 hj t hI => msStep_ok hbx h10 h8 h12 hw' hX hM hT sX sM hj1 hj hI)) fun t₂ hI => ?_)
  obtain ⟨c, hbp₂, hval⟩ := hI.val
  have t₂bx : t₂.gpr .rbx = off B ex := (hI.keep.gpr (by decide)).trans hbx
  have t₂8 : t₂.gpr .r8 = off B et := (hI.keep.gpr (by decide)).trans h8
  have t₂12 : t₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  refine WP.mono (subTop_ok t₂ (addrm8 t₂bx t₂12 (by omega_arith)) (addr0 t₂8 t₂12) (hI.scr.ld (by omega_arith))
    (hI.scr.st (by omega_arith)) hbp₂) fun t ⟨v', c', hm, hv, k⟩ => ⟨c', ?_, ?_, (hI.keep.trans k).mono (by decide)⟩
  · have hx : t₂.mem.readW (off B (ex + 8 * (w - 1))) 64 = word s.mem B (ex + 8 * (w - 1)) :=
      hI.out.word (by omega_arith) (by omega_arith)
    rw [hx] at hv
    rw [hm, show w + 1 = w + 1 from rfl, wv_writeW_top _ _ _ _ _ (by omega_arith)]
    have ew : wv s.mem B ex w = wv s.mem B ex (w - 1) + 2 ^ (64 * (w - 1)) * (word s.mem B (ex + 8 * (w - 1))).toNat := by
      conv => lhs; rw [show w = (w - 1) + 1 by omega_arith]
      simp only [wv]
    have e1 : 2 ^ (64 * w) = 2 ^ (64 * (w - 1)) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega_arith
    have e2 : 2 ^ (64 * (w + 1)) = 2 ^ (64 * (w - 1)) * 2 ^ 64 * 2 ^ 64 := by
      rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega_arith
    rw [ew, e2]
    rw [e1] at hval ⊢
    grind
  · rw [hm]
    intro x hx
    rw [writeW_outside t₂.mem B v' (by omega_arith) x (by omega_arith)]
    exact hI.out x (by omega_arith)

end VG.Proof.Rsa.X86_64.WordReduce
