module

public import VerifiedGarbage.Proof.RsaPss.PPC64LE.Sg.Entry
import VerifiedGarbage.Proof.RsaPss.PPC64LE.Params
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.MgfArith
import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Loops
import VerifiedGarbage.Proof.RsaPkcs1Sig.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS signing on PPC64LE: the checks

Untrusted: everything here is checked by Lean. For a modulus whose first
byte is not zero, `lo` is EMSA-PSS's (`lo_eq`); `chkEm_ok` and `chkSalt_ok`:
whether `emLen < hLen + 2` and whether the salt is longer than
`emLen - hLen - 2`, in `r3`; `fail_ok`: `encFail` writes zeros to `out` and
returns 0.
-/

@[expose] public section

namespace VG.Proof.RsaPss.PPC64LE.Sg

open VG VG.PPC64LE VG.Impl.RsaPss.PPC64LE.Sign VG.WriteBytes
open VG.Impl.RsaOaep.PPC64LE (encFail)
open VG.Proof.RsaOaep.PPC64LE (Base Fits fx hiRegs Saves kR ne_zero_ltBit msgBit zero_ok slR_sub)
open VG.Proof.RsaPkcs1Sig.PPC64LE (Only wp_li wp_sub wp_subi wp_lsr wp_or wp_mov wp_nil)

/-- `lo` as a number. -/
def loN (s : State) : Nat := if (s.mem (s.gpr .r5)).toNat = 1 then 1 else 0

theorem ofNat_toNat (x : BitVec 64) : BitVec.ofNat 64 x.toNat = x := by simp

theorem loN_le (s : State) : loN s ≤ 1 := by unfold loN; split <;> omega

theorem lo_eq {s : State} (h0 : s.mem (s.gpr .r5) ≠ 0) : loS s = BitVec.ofNat 64 (loN s) := by
  have hn : (s.mem (s.gpr .r5)).toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq h)
  have := (Proof.RsaPss.PPC64LE.byte_ok _ (s.mem (s.gpr .r5)).isLt hn).1
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  exact this

section
variable {D : Nat} {s : State} (P : PreS D s)
include P

theorem Entered.only {t t' : State} {rs : List Reg} (E : Entered s t) (o : Only rs t t')
    (hrs : ∀ r ∈ rs, r ∉ .r14 :: fx ++ hiRegs ++ ([.r9] : List Reg) := by decide) : Entered s t' :=
  ⟨E.base.only (fits P) o fun r h h' => hrs r h (List.mem_append_left _ h'),
    (o.gpr .r9 fun h => hrs _ h (List.mem_append_right _ (List.mem_singleton_self _))).trans E.r9⟩

theorem k_lo (h0 : s.mem (s.gpr .r5) ≠ 0) : s.gpr .r6 - loS s = BitVec.ofNat 64 (kk s - loN s) := by
  have hk1 : 64 ≤ kk s := P.k1
  have ek : (s.gpr .r6).toNat = kk s := rfl
  have := loN_le s
  rw [lo_eq h0, ← ofNat_toNat (s.gpr .r6), Offset.ofNat_sub_ofNat (by omega)]

/-- `chkEm`: whether `emLen < hLen + 2`. -/
theorem chkEm_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD64 : H.D ≤ 64) {t : State} (E : Entered s t)
    (h0 : s.mem (s.gpr .r5) ≠ 0) :
    WP isa (.block (chkEm H)) t fun t' => Entered s t' ∧
      (t'.gpr .r3 != 0) = decide (kk s - loN s < H.D + 2) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₁ o₁ e₁ => wp_subi (h := by omega) fun t₂ o₂ e₂ => wp_lsr fun t₃ o₃ e₃ => wp_nil ?_
  have k₃ : Only [.r3] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  refine ⟨E.only P k₃, ?_⟩
  rw [e₃, e₂, e₁, Base.r15 E.base, Base.r23 E.base, k_lo P h0]
  exact ne_zero_ltBit (by omega) (by omega)

/-- `chkSalt`: whether the salt is longer than `emLen - hLen - 2`. -/
theorem chkSalt_ok {H : Impl.Hmac.Stream.PPC64LE.Hash} (hD64 : H.D ≤ 64) {t : State} (E : Entered s t)
    (h0 : s.mem (s.gpr .r5) ≠ 0) (hem : H.D + 2 ≤ kk s - loN s) :
    WP isa (.block (chkSalt H)) t fun t' => Entered s t' ∧
      (t'.gpr .r3 != 0) = decide (kk s - loN s - (H.D + 2) < (stackArg s 10).toNat) := by
  have hk2 : kk s ≤ 1024 := P.k2
  refine wp_sub fun t₅ o₅ e₅ => wp_subi (h := by omega) fun t₆ o₆ e₆ => wp_sub fun t₇ o₇ e₇ =>
    wp_lsr fun t₈ o₈ e₈ => wp_lsr fun t₉ o₉ e₉ => wp_or fun t₁₀ o₁₀ e₁₀ => wp_nil ?_
  have k₁₀ : Only [.r3, .r5] t t₁₀ := (o₅.trans (o₆.trans (o₇.trans (o₈.trans (o₉.trans o₁₀))))).mono
  refine ⟨E.only P k₁₀, ?_⟩
  rw [e₁₀, o₉.get .r3, e₉, e₈, o₈.get .r19, e₇, o₇.get .r19, e₆, o₆.get .r19, e₅, o₅.get .r19, Base.r15 E.base,
    Base.r23 E.base, Base.r19 E.base, k_lo P h0, Offset.ofNat_sub_ofNat hem, BitVec.or_comm]
  have := msgBit (x := kk s - loN s - (H.D + 2)) (y := (stackArg s 10).toNat) (by omega) (BitVec.isLt _)
  rwa [ofNat_toNat] at this

theorem oR_eq : oR s = ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by rw [oR, P.ok]

/-- `encFail`: zeros to `out`, and 0. -/
theorem fail_ok {t : State} (h : Base Ss vS s t) :
    WP isa encFail t fun t' => Saves s t' ∧ t'.rd = s.rd ∧ t'.gpr .r3 = 0 ∧
      Spec.Rsa.bytesAt t'.mem (s.gpr .r3) (kk s) = List.replicate (kk s) 0 := by
  have hk1 := P.k1; have hk2 := P.k2
  have ek : kk s = (s.gpr .r6).toNat := rfl
  refine WP.seq (WP.seq (wp_mov fun t₁ o₁ e₁ => wp_mov fun t₂ o₂ e₂ => wp_li (by decide) fun t₃ o₃ e₃ =>
    wp_nil ?_))
  have k₃ : Only [.r4, .r5, .r6] t t₃ := (o₁.trans (o₂.trans o₃)).mono
  have hout : ∀ i < kk s, InRegions t₃.wr (s.gpr .r3 + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [k₃.wr, h.wr]
    exact ⟨oR s, List.mem_cons_of_mem _ (by rw [P.hwr]; simp),
      Offset.contains_base _ (by rw [P.ok]; omega) (by have := P.wo; omega)⟩
  refine WP.mono (zero_ok (p := s.gpr .r3) (n := kk s) (b := 0) (by omega) (by omega)
    (by rw [o₃.get .r4, o₂.get .r4, e₁, Base.r16 h]) (by rw [o₃.get .r5, e₂, o₁.get .r15, Base.r15 h]; simp)
    (by rw [e₃]; rfl) hout) fun t₄ ⟨k₄, m₄⟩ => wp_li (by decide) fun t₅ o₅ e₅ => wp_nil ?_
  have hko : (kR s).Disjoint ⟨s.gpr .r3, (s.gpr .r6).toNat⟩ := by
    rw [← oR_eq P]; exact P.ko.sub_left kR_sub
  have hf : Frame [⟨s.gpr .r3, kk s⟩] t.mem t₅.mem := by
    have := Proof.RsaPkcs1Sig.frame_writeBytes t₃.mem (s.gpr .r3) (List.replicate (kk s) (0 : Byte))
    rw [List.length_replicate] at this
    rw [o₅.mem, m₄, ← k₃.mem] at *; exact this
  have K := (k₃.keep.trans (k₄.trans o₅.keep)).mono (rs' := [.r3, .r4, .r5, .r6])
  refine ⟨h.sv.keep K hf (fun r hr => by rw [List.mem_singleton.mp hr]; exact hko.sub_left (slR_sub s)),
    K.rd.trans h.rd, by rw [e₅]; rfl, ?_⟩
  have := Proof.RsaPkcs1Sig.bytesAt_writeBytes t₃.mem (s.gpr .r3) (List.replicate (kk s) (0 : Byte))
    (by simp; omega)
  rw [List.length_replicate] at this
  rw [o₅.mem, m₄, this]

end

end VG.Proof.RsaPss.PPC64LE.Sg
