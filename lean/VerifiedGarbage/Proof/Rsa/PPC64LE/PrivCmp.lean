module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.PrivPubCall
import VerifiedGarbage.Proof.Rsa.PrivCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd

/-!
# `vg_rsa_private_checked` on PPC64LE: the comparison

The public operation's status kept in the frame (`cmpArgs_ok`, into
`AtLoop`), then the comparison of `out` with the input (`compare_ok`): the
OR of their bytes' XORs (`cmpAcc`), zero exactly if they are equal.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Priv

open VG VG.PPC64LE VG.Impl.Rsa.PPC64LE.Priv
open VG.Proof.Bignum.PPC64LE (Keep)

/-- `Late` is kept by a write of a word of the frame apart from the slots. -/
theorem Late.store {s t : State} (M : Late s t) {d : Nat} (hd : oLr + 8 ≤ d ∨ d + 8 ≤ oSave)
    (hd' : d + 8 ≤ frameBytes)
    (v : BitVec 64) {u : State} (hg : ∀ r ∈ preserved, u.gpr r = t.gpr r) (hsp : u.sp = t.sp)
    (hrd : u.rd = t.rd) (hwr : u.wr = t.wr) (hm : u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 d) v) :
    Late s u := by
  have hd1 : ∀ {e : Nat}, oSave ≤ e → e + 8 ≤ oLr + 8 →
      Region.Disjoint ⟨fb s + BitVec.ofNat 64 e, 8⟩ ⟨fb s + BitVec.ofNat 64 d, 8⟩ := fun he he' =>
    Offset.disjoint _ (by unfold oSave oLr at *; omega_arith) (by unfold oLr at he'; omega_arith)
      (by unfold frameBytes at hd'; omega_arith)
  have fw : Frame [⟨fb s + BitVec.ofNat 64 d, 8⟩] t.mem u.mem := by
    rw [hm]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  refine ⟨hsp.trans M.sp, hrd.trans M.rd, hwr.trans M.wr, (hg _ (by decide)).trans M.r24,
    (hg _ (by decide)).trans M.r25, (hg _ (by decide)).trans M.r26, (hg _ (by decide)).trans M.r27,
    (hg _ (by decide)).trans M.r28, (hg _ (by decide)).trans M.r29,
    fun r hr => (hg r (by revert r; decide)).trans (M.hi r hr), ?_,
    M.sv.frame fw fun p hp r hr => by
      rw [List.mem_singleton.mp hr]
      have := saved_offs p hp
      exact hd1 this.1 (by unfold oSave oLr at *; omega_arith), ?_⟩
  · rw [hm]; exact M.mem.writeW (List.mem_cons_self ..) _ (frame_contains s hd')
  · rw [fw.readW (Region.contains_self _ _) (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact hd1 (by decide) (by decide)) (by decide)]
    exact M.ls

/-- `m^e mod n` in `out` and the public operation's status kept in the
frame, if `n`'s values are valid. -/
abbrev pubOutM (s u : State) : Prop :=
  ∀ ws, Spec.Rsa.publicPrecompute (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) = some ws →
    Spec.Rsa.written u.mem (s.gpr .r3) (s.gpr .r6).toNat
      ((u.mem.readW (fb s + BitVec.ofNat 64 oEs) 64).setWidth 32)
      (Spec.Rsa.publicOpChecked (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat)
        (Spec.Rsa.bytesAt s.mem (s.gpr .r7) (s.gpr .r8).toNat)
        (Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat))

/-- At the comparison. -/
structure AtLoop (s u : State) : Prop extends Late s u where
  crt : crtOutM s u
  pub : pubOutM s u
  r3 : u.gpr .r3 = s.gpr .r3
  r4 : u.gpr .r4 = s.gpr .r9
  r5 : u.gpr .r5 = 0
  r6 : u.gpr .r6 = s.gpr .r6

theorem cmpArgs_ok {s t : State} (h : PreP s) (A : AtCmp s t) :
    WP isa (.block cmpArgs) t (AtLoop s) := by
  have hk := h.k2
  have ho : InRegions t.wr (fb s + BitVec.ofNat 64 oEs) 8 := by
    rw [A.wr]; exact in_fr s _ (by decide) (by decide)
  have c1 : oEs < 2 ^ 15 := by decide
  have c2 : oEs % 4 = 0 := by decide
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r12, .r3, .r4, .r5, .r6] (Q := fun u =>
    u.gpr .r3 = s.gpr .r3 ∧ u.gpr .r4 = s.gpr .r9 ∧ u.gpr .r5 = 0 ∧ u.gpr .r6 = s.gpr .r6 ∧
      u.mem = t.mem.writeW (fb s + BitVec.ofNat 64 oEs) (t.gpr .r3)) ?_ rfl)
    fun u ⟨⟨u3, u4, u5, u6, um⟩, k⟩ => ?_
  · unfold cmpArgs
    prun [exec_addSp0, A.sp, ho, c1, c2, A.r24, A.r26, A.r29, BitVec.or_self, Impl.AesGcm.PPC64LE.mov]
    rfl
  · have fw : Frame [⟨fb s + BitVec.ofNat 64 oEs, 8⟩] t.mem u.mem := by
      rw [um]; exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
    have ap : ∀ {d n : Nat}, (d + n ≤ oEs ∨ oEs + 8 ≤ d) → d + n ≤ 2 ^ 64 →
        ∀ r ∈ [(⟨fb s + BitVec.ofNat 64 oEs, 8⟩ : Region)], Region.Disjoint ⟨fb s + BitVec.ofNat 64 d, n⟩ r :=
      fun hd hn r hr => by
        rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hd hn (by decide)
    have hm : Spec.Rsa.bytesAt u.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (fb s + BitVec.ofNat 64 oM) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) fw (ap (.inr (by decide)) (by unfold oM; omega_arith)) (by omega_arith)
    have ho' : Spec.Rsa.bytesAt u.mem (s.gpr .r3) (s.gpr .r6).toNat =
        Spec.Rsa.bytesAt t.mem (s.gpr .r3) (s.gpr .r6).toNat :=
      bytes_of_frame (s := t) fw (fun r hr => by
        rw [List.mem_singleton.mp hr, show (⟨s.gpr .r3, (s.gpr .r6).toNat⟩ : Region) = oR s from outR_eq h]
        exact (h.ko.sub_left (frame_sub s (by decide))).symm) (by have := h.wo; rw [h.h4] at this; omega_arith)
    refine ⟨A.store (.inl (by decide)) (by decide) _ (fun r hr => k.gpr r (by revert r; decide)) k.sp k.rd
      k.wr um, ?_, ?_, u3, u4, u5, u6⟩
    · show Spec.Rsa.written _ _ _ _ _
      rw [fw.readW (Region.contains_self _ _) (ap (.inl (by decide)) (by decide)) (by decide)]
      exact written_congr hm A.crt
    · intro ws hw
      have := A.pub ws hw
      rw [← hm] at this
      rw [um, Mem.readW_writeW_self64, ← um]
      exact written_congr ho' this

/-- A byte, as `lbz` loads it. -/
abbrev zb (m : Mem) (a : Addr) : BitVec 64 := (m.read a 1).setWidth 64

/-- The OR of the XORs of the first `j` bytes at `a` and `b`. -/
def cmpAcc (m : Mem) (a b : Addr) : Nat → BitVec 64
  | 0 => 0
  | j + 1 => cmpAcc m a b j ||| (zb m (a + BitVec.ofNat 64 j) ^^^ zb m (b + BitVec.ofNat 64 j))

theorem zb_lt (m : Mem) (a : Addr) : (zb m a).toNat < 2 ^ 8 := by
  simp only [zb, BitVec.toNat_setWidth]
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (m.read a 1).isLt

theorem cmpAcc_lt (m : Mem) (a b : Addr) (j : Nat) : (cmpAcc m a b j).toNat < 2 ^ 8 := by
  induction j with
  | zero => simp [cmpAcc]
  | succ j ih =>
    simp only [cmpAcc, BitVec.toNat_or, BitVec.toNat_xor]
    exact Nat.or_lt_two_pow ih (Nat.xor_lt_two_pow (zb_lt _ _) (zb_lt _ _))

theorem zb_xor_eq_zero (m : Mem) (a b : Addr) : zb m a ^^^ zb m b = 0#64 ↔ m a = m b := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h; rw [← Proof.Bignum.PPC64LE.read_one' m a, ← Proof.Bignum.PPC64LE.read_one' m b]; exact congrArg (BitVec.setWidth 8) h
  · intro h
    simp only [zb]
    congr 1
    show (m.read (a + 1) 0 ++ m a) = (m.read (b + 1) 0 ++ m b)
    rw [h]; simp only [Mem.read]

theorem cmpAcc_eq_zero (m : Mem) (a b : Addr) (j : Nat) :
    cmpAcc m a b j = 0#64 ↔ ∀ i < j, m (a + BitVec.ofNat 64 i) = m (b + BitVec.ofNat 64 i) := by
  induction j with
  | zero => simp [cmpAcc]
  | succ j ih =>
    rw [cmpAcc, BitVec.or_eq_zero_iff, ih, zb_xor_eq_zero]
    constructor
    · rintro ⟨h, h'⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact h'
    · intro h; exact ⟨fun i hi => h i (by omega_arith), h j (by omega_arith)⟩

theorem add_ofNat_one (p : Addr) (j : Nat) :
    p + BitVec.ofNat 64 j + BitVec.ofNat 64 1 = p + BitVec.ofNat 64 (j + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- The comparison: the OR of the XORs of `out`'s bytes and the input's in `r5`. -/
theorem compare_ok {s t : State} (h : PreP s) (A : AtLoop s t) :
    WP isa compare t fun u => u.gpr .r5 = cmpAcc t.mem (s.gpr .r3) (s.gpr .r9) (s.gpr .r6).toNat ∧
      u.mem = t.mem ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8] t u := by
  have hk := h.k2
  have hk1 := h.k1
  let Inv : Nat → State → Prop := fun j u =>
    u.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 j ∧ u.gpr .r4 = s.gpr .r9 + BitVec.ofNat 64 j ∧
      u.gpr .r5 = cmpAcc t.mem (s.gpr .r3) (s.gpr .r9) j ∧ u.mem = t.mem ∧ Keep [.r3, .r4, .r5, .r6, .r7, .r8] t u
  refine WP.mono (Proof.Bignum.PPC64LE.wp_countdown (N := (s.gpr .r6).toNat) (by omega_arith) (by omega_arith) Inv
    (fun j hj u ⟨u3, u4, u5, um, uk⟩ hc => ?_)
    ⟨by rw [A.r3]; simp, by rw [A.r4]; simp, A.r5, rfl, Keep.refl _ _⟩ (by rw [A.r6]; simp))
    fun u ⟨_, _, u5, um, uk⟩ => ⟨u5, um, uk⟩
  have io : InRegions (u.rd ++ u.wr) (s.gpr .r3 + BitVec.ofNat 64 j) 1 := by
    rw [uk.rd, uk.wr, A.wr, h.hwr]
    exact ⟨oR s, by simp, Offset.contains_base _ (by rw [h.h4]; omega_arith) (by omega_arith)⟩
  have ii : InRegions (u.rd ++ u.wr) (s.gpr .r9 + BitVec.ofNat 64 j) 1 := by
    rw [uk.rd, A.rd, h.hrd]
    exact ⟨iR s, by simp, Offset.contains_base _ (by rw [h.h10]; omega_arith) (by omega_arith)⟩
  refine WP.mono (VG.Proof.Bignum.PPC64LE.WP.keep [.r3, .r4, .r5, .r6, .r7, .r8] (Q := fun u' =>
    u'.gpr .r3 = s.gpr .r3 + BitVec.ofNat 64 (j + 1) ∧ u'.gpr .r4 = s.gpr .r9 + BitVec.ofNat 64 (j + 1) ∧
      u'.gpr .r5 = cmpAcc t.mem (s.gpr .r3) (s.gpr .r9) (j + 1) ∧ u'.mem = u.mem ∧
      u'.gpr .r6 = u.gpr .r6 - BitVec.ofNat 64 1) ?_ rfl) fun u' ⟨⟨v3, v4, v5, vm, v6⟩, k⟩ =>
    ⟨⟨v3, v4, v5, vm.trans um, uk.trans k |>.mono⟩, v6⟩
  prun [u3, u4, u5, um, io, ii, BitVec.add_zero, add_ofNat_one, cmpAcc,
    Proof.Bignum.PPC64LE.exec_lbz' (show Reg.r3 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide),
    Proof.Bignum.PPC64LE.exec_lbz' (show Reg.r4 ≠ .r0 by decide) (show 0 < 2 ^ 15 by decide)]

end VG.Proof.Rsa.PPC64LE.Priv
