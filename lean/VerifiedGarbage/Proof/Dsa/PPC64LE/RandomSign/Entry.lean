module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.RandomSign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on PPC64LE: the entry

`entry_ok`: from the frame's push, `entry` saves the registers and the
return address, writes `vg_dsa_sign`'s arguments on the stack, keeps the
call's data in the registers of `Ctx`, starts with no octets consumed and
eight attempts, and zeroes the nonce; memory changes in the frame only.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The frame's local variable space contains its offsets from 32 on. -/
theorem frameR_contains {L : RL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat} (h₁ : 32 ≤ d)
    (h₂ : d + n ≤ frameBytes) : (frameR frameBytes s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp, frameBytes] at hF h₂ ⊢
  rw [show L.sp - BitVec.ofNat 64 304 + 32 = off L.F 32 from rfl]
  exact VG.Offset.contains L.F h₁ (by omega) (by omega)

/-- The frame's offsets past it are the stack pointer's. -/
theorem F_add (L : RL) (d : Nat) : off L.F (frameBytes + d) = L.sp + BitVec.ofNat 64 d := by
  simp only [off, RL.F]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The octets of a region apart from the frame are kept by a change within it. -/
theorem bytes_outside {L : RL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : k ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (.inr ?_)
  have hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega) (by omega)
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

theorem add0 (x : BitVec 64) : x + BitVec.ofNat 64 0 = x := BitVec.add_zero x

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : RL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR frameBytes s₀ :: s₀.wr) : Scr t (off L.F oNonce) 32 := by
  have hF := hL.fnw
  simp only [frameBytes] at hF
  refine ⟨⟨(frameR frameBytes s₀).base, 88, 272, by rw [hw]; exact List.mem_cons_self .., ?_, by decide,
    by decide⟩, ?_⟩
  · show L.sp - BitVec.ofNat 64 304 + BitVec.ofNat 64 120 = s₀.sp - BitVec.ofNat 64 304 + 32 + BitVec.ofNat 64 88
    rw [hsp, BitVec.add_assoc]
    rfl
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega

/-- What `entry` leaves. -/
structure Entered (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 0
  r26 : t.gpr .r26 = BitVec.ofNat 64 8
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : rsContract.pre s₀) :
    WP isa (.block entry) (allocated frameBytes s₀) (Entered (rlOf s₀) s₀) := by
  have hL := rlOf_ok h
  generalize hLd : rlOf s₀ = L at hL
  have hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  have hE : (allocated frameBytes s₀).sp = L.F := by simp only [allocated, hsp]
  have hin : ∀ i < 19, InRegions (allocated frameBytes s₀).wr (off L.F (oSave + 8 * i)) 8 := fun i hi =>
    ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by simp only [oSave]; omega)
      (by simp only [oSave, frameBytes]; omega)⟩
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hin) fun t₁ h₁ => ?_
  -- The call's data.
  have eo : s₀.gpr .r3 = L.out := by rw [← hLd]; rfl
  have eu : s₀.gpr .r5 = L.used := by rw [← hLd]; rfl
  have ek : s₀.gpr .r6 = L.key := by rw [← hLd]; rfl
  have ep : s₀.gpr .r8 = BitVec.ofNat 64 L.pl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have eq : s₀.gpr .r9 = BitVec.ofNat 64 L.ql := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have ed : s₀.gpr .r10 = L.dig := by rw [← hLd]; rfl
  have a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.dl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have a1 : stackArg s₀ 1 = L.rand := by rw [← hLd]; rfl
  have a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have a3 : stackArg s₀ 3 = L.scr := by rw [← hLd]; rfl
  have a4 : stackArg s₀ 4 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  -- Memory so far changed within the frame.
  have o₀ : Outside L.F 0 8 s₀.mem (allocated frameBytes s₀).mem := by
    intro x hx
    simp only [allocated, hsp, ofs] at hx ⊢
    apply Mem.write_apply
    show ¬ (x - L.F).toNat < 8
    omega
  have o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    (o₀.mono (by omega) (by simp only [frameBytes]; omega)).trans (h₁.out.mono (by omega)
      (by simp only [oSave, frameBytes]; omega))
  -- The arguments on the stack.
  obtain ⟨-, -, hrd, -⟩ := h
  have hargs : ∀ i < 5, InRegions (t₁.rd ++ t₁.wr) (L.F + BitVec.ofNat 64 (argOff i)) 8 ∧
      t₁.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = stackArg s₀ i := fun i hi => by
    have e : L.F + BitVec.ofNat 64 (argOff i) = stackArgAddr s₀ 0 + BitVec.ofNat 64 (8 * i) := by
      rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (frameBytes + (96 + 8 * i)) by
        simp only [argOff, frameBytes]; rw [show 304 + 96 + 8 * i = 304 + (96 + 8 * i) by omega], F_add,
        stackArgAddr, hsp, show 32 + 8 * (8 + 0) = 96 by rfl, BitVec.add_assoc, BitVec.ofNat_add]
    refine ⟨?_, ?_⟩
    · rw [h₁.rd, e]
      exact ⟨rsStackArgs s₀, List.mem_append_left _ (show rsStackArgs s₀ ∈ s₀.rd by rw [hrd]; simp),
        VG.Offset.contains_base _ (by omega) (by omega)⟩
    · rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (argOff i) from rfl,
        show t₁.mem.readW (off L.F (argOff i)) 64 = word t₁.mem L.F (argOff i) from rfl,
        o₁.word (.inr (by simp only [argOff, frameBytes]; omega)) (by simp only [argOff, frameBytes]; omega)]
      show s₀.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = _
      rw [e]
      simp only [stackArg, stackArgAddr]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 + 8 * (8 + 0) + 8 * i = 32 + 8 * (8 + i) by omega]
  obtain ⟨l0, v0⟩ := hargs 0 (by decide)
  obtain ⟨l1, v1⟩ := hargs 1 (by decide)
  obtain ⟨l2, v2⟩ := hargs 2 (by decide)
  obtain ⟨l3, v3⟩ := hargs 3 (by decide)
  obtain ⟨l4, v4⟩ := hargs 4 (by decide)
  simp only [argOff, frameBytes, Nat.reduceAdd, Nat.reduceMul] at l0 v0 l1 v1 l2 v2 l3 v3 l4 v4
  have st : ∀ d, 96 ≤ d → d + 8 ≤ 120 → InRegions t₁.wr (L.F + BitVec.ofNat 64 d) 8 := fun d h₁' h₂' => by
    rw [h₁.wr]; exact ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by omega) (by simp only [frameBytes]; omega)⟩
  have hr : ∀ r, r ≠ .r0 → r ≠ .r12 → t₁.gpr r = s₀.gpr r := fun r h0 h12 => h₁.others r h0 h12
  simp only [argOff, oArgs, frameBytes, Nat.reduceAdd, Nat.reduceMul]
  refine WP.mono (WP.keep [.r3, .r4, .r5, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r30] (Q := fun t =>
    t.gpr .r18 = L.out ∧ t.gpr .r19 = L.key ∧ t.gpr .r20 = BitVec.ofNat 64 L.pl ∧ t.gpr .r21 = BitVec.ofNat 64 L.ql ∧
      t.gpr .r22 = L.dig ∧ t.gpr .r23 = L.rand ∧ t.gpr .r24 = BitVec.ofNat 64 L.rl ∧ t.gpr .r30 = L.used ∧
      t.gpr .r25 = BitVec.ofNat 64 0 ∧ t.gpr .r26 = BitVec.ofNat 64 8 ∧
      t.mem = ((t₁.mem.writeW (L.F + BitVec.ofNat 64 96) (BitVec.ofNat 64 L.dl)).writeW
        (L.F + BitVec.ofNat 64 104) L.scr).writeW (L.F + BitVec.ofNat 64 112) (BitVec.ofNat 64 L.sl))
    (by prun [h₁.r12, l0, l1, l2, l3, l4, v0, v1, v2, v3, v4, a0, a1, a2, a3, a4, st 96 (by decide) (by decide),
      st 104 (by decide) (by decide), st 112 (by decide) (by decide), hr .r3 (by decide) (by decide),
      hr .r5 (by decide) (by decide), hr .r6 (by decide) (by decide), hr .r8 (by decide) (by decide),
      hr .r9 (by decide) (by decide), hr .r10 (by decide) (by decide), eo, eu, ek, ep, eq, ed, add0])
    (by decide)) fun t₂ ⟨⟨b18, b19, b20, b21, b22, b23, b24, b30, b25, b26, bm⟩, k₂⟩ => ?_
  have k12 := h₁
  have e₂sp : t₂.sp = L.F := by rw [k₂.sp, h₁.sp, hE]
  have e₂wr : t₂.wr = frameR frameBytes s₀ :: s₀.wr := by rw [k₂.wr, h₁.wr]; rfl
  refine WP.mono (clearNonce_ok t₂ hF e₂sp (scr_nonce hL hsp e₂wr)) fun t ⟨⟨_, tz, tou⟩, k₃⟩ => ?_
  -- Memory on exit, from `t₁`'s.
  have o₂ : Outside L.F oArgs 24 t₁.mem t₂.mem := by
    rw [bm]
    exact ((writeW_outside _ L.F (d := 96) _ (by omega)).mono (by simp only [oArgs]; omega) (by simp only [oArgs]; omega)).trans
      (((writeW_outside _ L.F (d := 104) _ (by omega)).mono (by simp only [oArgs]; omega) (by simp only [oArgs]; omega)).trans
        ((writeW_outside _ L.F (d := 112) _ (by omega)).mono (by simp only [oArgs]; omega) (by simp only [oArgs]; omega)))
  have o₃ : Outside L.F 0 frameBytes s₀.mem t.mem :=
    (o₁.trans (o₂.mono (by omega) (by simp only [oArgs, frameBytes]; omega))).trans
      (tou.mono (by omega) (by simp only [oNonce, frameBytes]; omega))
  have w₃ : ∀ d, (d + 8 ≤ oArgs ∨ oNonce + 32 ≤ d) → d + 8 ≤ frameBytes →
      t.mem.readW (off L.F d) 64 = t₁.mem.readW (off L.F d) 64 := fun d hd hd' => by
    have e1 := tou.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega) (by simp only [frameBytes] at hd'; omega)
    have e2 := o₂.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega) (by simp only [frameBytes] at hd'; omega)
    exact e1.trans e2
  have g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ∉ ([.r3, .r4, .r5, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
      .r30] : List Reg) → t.gpr r = s₀.gpr r := fun r h0 h12 hr =>
    (k₃.gpr r (by simp [h0, h12])).trans ((k₂.gpr r hr).trans (h₁.others r h0 h12))
  have hw2 : ∀ d, 96 ≤ d → d + 8 ≤ 120 → t.mem.readW (off L.F d) 64 = t₂.mem.readW (off L.F d) 64 := fun d h₁' h₂' =>
    tou.word (by simp only [oNonce]; omega) (by omega)
  have sep : ∀ a b : Nat, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 2 ^ 64 → b + 8 ≤ 2 ^ 64 →
      Mem.Sep (L.F + BitVec.ofNat 64 a) 8 (L.F + BitVec.ofNat 64 b) 8 := fun a b h ha hb => VG.Offset.sep L.F h ha hb
  refine ⟨⟨k₃.sp.trans e₂sp, by rw [k₃.rd, k₂.rd, h₁.rd]; rfl, k₃.wr.trans e₂wr, g₃ .r2 (by decide) (by decide) (by decide),
    (k₃.gpr _ (by decide)).trans b18, (k₃.gpr _ (by decide)).trans b19, (k₃.gpr _ (by decide)).trans b20,
    (k₃.gpr _ (by decide)).trans b21, (k₃.gpr _ (by decide)).trans b22, (k₃.gpr _ (by decide)).trans b23,
    (k₃.gpr _ (by decide)).trans b24, (k₃.gpr _ (by decide)).trans b30, fun i hi => ?_, ?_, ?_, ?_, ?_,
    bytes_outside o₃ hL.dFK (by have := hL.nwKey; omega), bytes_outside o₃ hL.dFD (Nat.le_of_lt hL.dl),
    bytes_outside o₃ hL.dFR (Nat.le_of_lt hL.rl)⟩,
    (k₃.gpr _ (by decide)).trans b25, (k₃.gpr _ (by decide)).trans b26, tz⟩
  · rw [w₃ _ (.inr (by simp only [oSave, oNonce]; omega)) (by simp only [oSave, frameBytes]; omega)]
    exact h₁.saved i hi
  · rw [w₃ _ (.inr (by decide)) (by decide)]
    exact h₁.savedLr
  · rw [hw2 _ (by decide) (by decide), bm]
    simp only [off, oArgs]
    rw [Mem.readW_writeW_sep (sep 96 112 (by decide) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 96 104 (by decide) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  · rw [hw2 _ (by decide) (by decide), bm]
    simp only [off, oArgs, Nat.reduceAdd]
    rw [Mem.readW_writeW_sep (sep 104 112 (by decide) (by omega) (by omega)) (by decide), Mem.readW_writeW_self64]
  · rw [hw2 _ (by decide) (by decide), bm]
    simp only [off, oArgs, Nat.reduceAdd]
    rw [Mem.readW_writeW_self64]

end VG.Proof.Dsa.PPC64LE.RS
