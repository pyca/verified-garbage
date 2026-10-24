module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.KSOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! # DSA parameter generation on PPC64LE: the key working space set up

`ksEnter_vp`: its registers (`ksRegs`); `ksSetup_vp`: every array zero but
`[aOne] = 1`, and the top word of every other array zero (`TopAll`), which
the division's divisor needs.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.Gen
open VG VG.PPC64LE VG.Proof.Mont
open VG.Proof.Rsa.KeyWorkspace (S arr num slot Arrs)
open VG.Proof.Rsa.PPC64LE.Keys (Ws opRegs zeroArrays_ok setOne_ok)
open VG.Impl.Rsa.PPC64LE.Keys (zeroArrays setOne stride)
open VG.Impl.Dsa.PPC64LE.Generation

/-- The arrays after the setup: all zero but `[aOne] = 1`. -/
abbrev A0 : Nat → Nat := KU (fun _ => 0) aOne 1

/-- Every array. -/
abbrev allArrs : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]

theorem allArrs_lt : ∀ j ∈ allArrs, j < nArrs := by decide

/-- The top word of every array but `aOne` is zero. -/
abbrev TopAll (G : GP) (m : Mem) : Prop := ∀ j < nArrs, j ≠ aOne → w32 m G.KB (arr G.w j + 4 * G.w) = 0

theorem ofNat_stride' (w : Nat) :
    (BitVec.ofNat 64 w + BitVec.ofNat 64 2) <<< 2 = BitVec.ofNat 64 (S w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq]
  simp only [S]
  omega

theorem ofNat_digits15 (w : Nat) (hw : w ≤ 256) :
    (BitVec.ofNat 64 nArrs * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (nArrs * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S, nArrs]
  rw [Nat.mod_eq_of_lt (show 15 * (4 * (w + 2)) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 15 * (w + 2) < 2 ^ 64 by omega)]
  omega

section
variable {G : GP} {c : Cfg} {X : State → Prop}

/-- The key working space's registers. -/
theorem ksEnter_vp : VP (St G c X) (.block (ksRegs G.pLen)) (KSt G c X) := by
  refine VP.pub (SS.pub (c := fun _ => c) fun σ s h => h.1) [] ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64
    (Taint.ofRegs [.r28]) (.block (ksRegs G.pLen)), rfl⟩ (fun _ _ _ _ _ _ _ h => absurd h (by simp))
    fun σ s ⟨h, x⟩ => ?_
  have l := h.lens
  have kb15 : kB G.pLen < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  have w15 : G.pLen / 4 < 2 ^ 15 := by rcases l with e | e | e <;> rw [e] <;> decide
  have hb : WP isa (.block (ksRegs G.pLen)) s fun u =>
      (u.gpr .r31 = G.KB ∧ u.gpr .r29 = BitVec.ofNat 64 G.w ∧ u.gpr .r30 = BitVec.ofNat 64 (S G.w) ∧
        u.mem = s.mem) ∧ VG.Proof.Bignum.PPC64LE.Keep [.r29, .r30, .r31] s u := by
    refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by rfl)
    simp only [ksRegs, stride, scr, List.cons_append, List.nil_append]
    prun [h.gi.r28, exec_addi (show Reg.r28 ≠ .r0 by decide) kb15, exec_li w15,
      exec_addi (show Reg.r29 ≠ .r0 by decide) (show 2 < 2 ^ 15 by decide), ofNat_stride']
  refine WP.mono hb fun u ⟨⟨a31, a29, a30, m⟩, k⟩ => ⟨⟨h.of_keep ⟨k.gpr, k.rd, k.wr⟩ m k.sp, x⟩, a29, a30, a31⟩

/-- Every array zeroed, then `[aOne] = 1`. -/
theorem ksSetup_vp :
    VP (KSt G c X) ksSetup (fun σ t => KSt G { c with A := A0, live := allArrs } X σ t ∧ TopAll G t.mem) := by
  refine ks_vp ⟨VG.Taint.hintOfSize VG.PPC64LE.taint 64 (Taint.ofRegs [.r28, .r29, .r30, .r31]) ksSetup, rfl⟩
    (fun σ s h => ⟨h.1.1, h.2⟩) fun σ s ⟨⟨h, x⟩, kr⟩ => ?_
  have hw := h.ws kr
  have l := h.lens
  have nw := hw.nowrap
  have wl : G.w ≤ 96 := by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide
  have w1 : 1 ≤ G.w := by simp only [GP.w]; rcases l with e | e | e <;> rw [e] <;> decide
  have fits : 160 + 4 * (nArrs * (G.w + 2)) ≤ kz G.pLen := by
    simp only [VG.Proof.Rsa.KeyWorkspace.hdr, nArrs, kz, GP.w, S]; omega
  refine h.ksWP rfl (P := fun t => (∀ j < nArrs, num t.mem G.KB G.w j = A0 j) ∧ TopAll G t.mem ∧
      (∀ d, d + 4 ≤ 160 → slot t.mem G.KB d = slot s.mem G.KB d) ∧
      VG.Proof.Bignum.PPC64LE.Keep (.r8 :: opRegs) (G.ksState s) t) ?_
    fun t ⟨a, top, sl, R⟩ hr hw' f => ⟨⟨⟨?_, x⟩, kr.of_keep (show Keep (.r8 :: opRegs) s t from ⟨R.gpr, hr, hw'⟩)⟩,
      by simpa only [GP.ksState, State.withRegions_mem] using top⟩
  swap
  · refine h.of_ks (show Keep (.r8 :: opRegs) s t from ⟨R.gpr, hr, hw'⟩) R.sp f (fun j hj => a j (allArrs_lt j hj))
      allArrs_lt (fun d hd => ?_) h.kslOk
    rw [show slot t.mem G.KB d = slot (G.ksState t).mem G.KB d from rfl, sl d (by
      have := (h.kslOk d hd).1; simp only [VG.Proof.Rsa.KeyWorkspace.hdr] at this; omega)]
    exact h.ksl d hd
  unfold ksSetup
  rw [WP.seq_iff]
  have hb : WP isa (.block [.li .r8 nArrs, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2]) (G.ksState s) fun u =>
      (u.gpr .r8 = BitVec.ofNat 64 (nArrs * (G.w + 2)) ∧ u.mem = s.mem) ∧
        VG.Proof.Bignum.PPC64LE.Keep [.r8] (G.ksState s) u := by
    refine VG.Proof.Bignum.PPC64LE.WP.keep _ ?_ (by decide)
    prun [hw.r30, exec_li (show nArrs < 2 ^ 15 by decide), ofNat_digits15 G.w (by omega)]
    rfl
  refine WP.mono hb fun u ⟨⟨u8, um⟩, ku⟩ => ?_
  have hu : Ws u G.KB (kz G.pLen) G.w nArrs := hw.of_keep ku
  rw [WP.seq_iff]
  refine WP.mono (zeroArrays_ok hu u8 (by simp only [nArrs]; omega) (by simp only [nArrs]; omega) fits)
    fun t₁ ⟨ht₁, z, out, kt⟩ => ?_
  rw [← List.append_nil (setOne aOne)]
  refine setOne_ok ht₁ (j := aOne) (by decide) (by decide) fun t ht k₈ v₈ R₈ => WP.block_nil ?_
  have zw : ∀ j < nArrs, ∀ i < G.w + 2, w32 t₁.mem G.KB (arr G.w j + 4 * i) = 0 := fun j hj i hi => by
    have hb : j * (G.w + 2) + i < nArrs * (G.w + 2) := by
      have := Nat.mul_le_mul_right (G.w + 2) (show j + 1 ≤ nArrs by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    have := z (j * (G.w + 2) + i) hb
    rw [show 160 + 4 * (j * (G.w + 2) + i) = arr G.w j + 4 * i by
      simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; grind] at this
    exact this
  have zv : ∀ j < nArrs, num t₁.mem G.KB G.w j = 0 := fun j hj =>
    VG.Proof.Bignum.PPC64LE.val32_zero fun i hi => zw j hj i (by omega)
  refine ⟨fun j hj => ?_, fun j hj hne => ?_, fun d hd => ?_, ?_⟩
  · show num _ _ _ _ = VG.Proof.Rsa.KeyWorkspace.upd (fun _ => 0) aOne 1 j
    by_cases e : j = aOne
    · subst e; rw [VG.Proof.Rsa.KeyWorkspace.upd_self, v₈, zv _ (by decide)]
    · rw [VG.Proof.Rsa.KeyWorkspace.upd_ne _ _ e, k₈.num (by simpa using Ne.symm e) (by simp)
        (ht.fit64 hj), zv _ hj]
  · rw [k₈.word (j := j) (i := G.w) (by simp only [S]; omega) (by simpa using Ne.symm hne) (by simp) (ht.fit64 hj)]
    exact zw j hj G.w (by omega)
  · rw [k₈.slot (by simp only [VG.Proof.Rsa.KeyWorkspace.hdr]; omega) (by simp)]
    show w32 t₁.mem G.KB d = w32 s.mem G.KB d
    rw [← um]
    exact out.w32 (.inl hd) (by omega)
  · exact (ku.trans (kt.trans R₈)).mono (by simp)

end

end VG.Proof.Dsa.PPC64LE.Gen
