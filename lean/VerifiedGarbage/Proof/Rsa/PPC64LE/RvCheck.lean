module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvEntry
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvCheck
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvLoads
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Rsa.PPC64LE.KcCk
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# `vg_rsa_recover_primes` on PPC64LE: the check of `n`

`nCheck_ok`: `r0` is 0 iff `n` is a valid modulus. `nB0 s0`: `n`'s bytes.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Rsa.PPC64LE.Recover (nCheck)

/-- `n`'s bytes. -/
abbrev nB0 (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .r7) (kK s0)

theorem len_nB0 (s0 : State) : (nB0 s0).length = kK s0 := by simp [Spec.Rsa.bytesAt]

theorem getD_of_lt {l : List Byte} {i : Nat} (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- After `check1`. -/
def NC1 (s0 t : State) : Prop :=
  RBase s0 t ∧ RArgs s0 t ∧ t.gpr .r10 = BitVec.ofNat 64 (kK s0) ∧
    (t.gpr .r0 = 0 ↔ ((nB0 s0).getD (kK s0 - 1) 0).toNat % 2 = 1) ∧
    t.gpr .r11 = BitVec.ofNat 64 ((nB0 s0).getD 0 0).toNat

/-- After `check2`. -/
def NC2 (s0 t : State) : Prop :=
  RBase s0 t ∧ RArgs s0 t ∧
    (t.gpr .r0 = 0 ↔ Spec.Rsa.modulusValid (Spec.Rsa.os2ip (nB0 s0)) (kK s0) = true)

/-- The registers `nCheck` changes. -/
abbrev ncRegs : List Reg := [.r0, .r9, .r10, .r11, .r12]

theorem nc1_ok {s0 s : State} (b : RBase s0 s) (a : RArgs s0 s) :
    WP isa (.seq (.block [.addi .r9 .r24 0, .addi .r10 .r25 0]) (.block VG.Impl.Rsa.PPC64LE.CrtValues.check1)) s
      fun u => NC1 s0 u ∧ u.mem = s.mem ∧ Keep ncRegs s u := by
  obtain ⟨-, hrd, -, -, -, -, -, -, -, -, -, -, -, -, dn, -, -, -, -, -, wn, -, -, -, ⟨hk, -⟩, -⟩ := id b.pre
  refine WP.seq (WP.mono (CrtValues.mv2_ok (s := s) (d₁ := .r9) (d₂ := .r10) (a := .r24) (b := .r25)
    (by decide) (by decide) (by decide) (by decide)) fun t3 ⟨⟨u9, u10, m3⟩, k3⟩ => ?_)
  have b3 := b.of_regs k3 m3
  have wn' : (s0.gpr .r7).toNat + kK s0 ≤ 2 ^ 64 := wn
  have hc : ∀ i < kK s0, (⟨s0.gpr .r7, kK s0⟩ : Region).Contains (off (s0.gpr .r7) i) 1 := fun i hi =>
    Offset.contains_base _ (by omega) (by omega)
  have h10 : t3.gpr .r10 = BitVec.ofNat 64 (kK s0) := by rw [u10, a.r25]; exact CrtValues.ofNat_toNat64 _
  refine WP.mono (CrtValues.check1_ok (N := s0.gpr .r7) (k := kK s0) (nb := nB0 s0)
    (by rw [u9, a.r24]; simp [off]) h10 hk (len_nB0 _)
    (fun i hi => ⟨_, List.mem_append_left _ (by rw [b3.rd, hrd]; simp), hc i hi⟩)
    (fun i hi => by
      rw [b3.frame _ (CrtValues.past_of_disjoint dn (hc i hi))]; simp [Spec.Rsa.bytesAt, off]))
    fun t4 ⟨⟨i0, i11, im⟩, k4⟩ => ⟨⟨b3.of_regs k4 im, (a.of_keep k3).of_keep k4, by rw [k4.gpr _ (by decide), h10],
      by rw [i0, getD_of_lt (l := nB0 s0) (i := kK s0 - 1) (by simp only [len_nB0, kK]; omega)],
      by rw [i11, getD_of_lt (l := nB0 s0) (i := 0) (by simp only [len_nB0, kK]; omega)]⟩,
      im.trans m3, (k3.trans k4).mono⟩

theorem nc2_ok {s0 s : State} (h : NC1 s0 s) :
    WP isa VG.Impl.Rsa.PPC64LE.CrtValues.check2 s fun u => NC2 s0 u ∧ u.mem = s.mem ∧ Keep ncRegs s u := by
  obtain ⟨b, a, h10, i0, i11⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hk, hk'⟩, -⟩ := id b.pre
  refine WP.mono (CrtValues.check2_ok h10 hk hk' (len_nB0 _)
    (by rw [i0, getD_of_lt (l := nB0 s0) (i := kK s0 - 1) (by simp only [len_nB0, kK]; omega)])
    (by rw [i11, getD_of_lt (l := nB0 s0) (i := 0) (by simp only [len_nB0, kK]; omega)]))
    fun t ⟨hv, tm, kt⟩ => ⟨⟨b.of_regs kt tm, a.of_keep kt, hv⟩, tm, kt.mono⟩

theorem nCheck_ok {s0 s : State} (b : RBase s0 s) (a : RArgs s0 s) :
    WP isa nCheck s fun u => NC2 s0 u ∧ u.mem = s.mem ∧ Keep ncRegs s u := by
  unfold nCheck VG.Impl.Rsa.PPC64LE.CrtValues.check
  refine WP.assoc (WP.seq (WP.mono (nc1_ok b a) fun u ⟨h, m, k⟩ => WP.mono (nc2_ok h)
    fun v ⟨h', m', k'⟩ => ⟨h', m'.trans m, (k.trans k').mono⟩))

end VG.Proof.Rsa.PPC64LE.Recover
