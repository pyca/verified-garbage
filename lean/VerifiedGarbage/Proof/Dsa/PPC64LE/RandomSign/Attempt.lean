module

import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Impl.Dsa.PPC64LE.RandomSign
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
public import VerifiedGarbage.Spec.RsaPss
public import VerifiedGarbage.Proof.Dsa.RandomSignTraceResult
import VerifiedGarbage.Proof.Dsa.RandomSign
import VerifiedGarbage.Proof.Dsa.Random
import VerifiedGarbage.Proof.Dsa.RandomSignResult
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
public import VerifiedGarbage.Proof.Dsa.RandomSignRemaining
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.RandomBytes
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Call
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Save
public import VerifiedGarbage.Impl.Dsa.PPC64LE.PrevalidatedSign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Setup
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Body
import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyFn
import VerifiedGarbage.Proof.Dsa.Accepted
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubCorrect
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreWrite
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Q

/-! ### `Dsa.PPC64LE.RandomSign.Call`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.RandomSign.Sampler`, which this module and modules that import it used -/

section

/-! ### `Dsa.PPC64LE.RandomSign.Entry`, which only this module used -/

section

/-!
# Randomized DSA signing on PPC64LE: the entry

`entry_ok`: from the frame's push, `entry` saves the registers and the
return address, writes `vg_dsa_sign_prevalidated`'s arguments on the stack, keeps the
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
  exact VG.Offset.contains L.F h₁ (by omega_using [h₂]) (by omega_using [])

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
  obtain hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega_using [hi]) (by omega_using [hk, hi])
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
    omega_using [hF]

/-- What `entry` leaves. -/
structure Entered (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 0
  r26 : t.gpr .r26 = BitVec.ofNat 64 8
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : rsContract.pre s₀) :
    WP isa (.block entry) (allocated frameBytes s₀) (Entered (rlOf s₀) s₀) := by
  obtain hL := rlOf_ok h
  generalize hLd : rlOf s₀ = L at hL
  obtain hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  obtain hE : (allocated frameBytes s₀).sp = L.F := by simp only [allocated, hsp]
  obtain hin : ∀ i < 19, InRegions (allocated frameBytes s₀).wr (off L.F (oSave + 8 * i)) 8 := fun i hi =>
    ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by simp only [oSave]; omega_using [])
      (by simp only [oSave, frameBytes]; omega_using [hi])⟩
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hin) fun t₁ h₁ => ?_
  -- The call's data.
  obtain eo : s₀.gpr .r3 = L.out := by rw [← hLd]; rfl
  obtain eu : s₀.gpr .r5 = L.used := by rw [← hLd]; rfl
  obtain ek : s₀.gpr .r6 = L.key := by rw [← hLd]; rfl
  obtain ep : s₀.gpr .r8 = BitVec.ofNat 64 L.pl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain eq : s₀.gpr .r9 = BitVec.ofNat 64 L.ql := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain ed : s₀.gpr .r10 = L.dig := by rw [← hLd]; rfl
  obtain a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.dl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a1 : stackArg s₀ 1 = L.rand := by rw [← hLd]; rfl
  obtain a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  obtain a3 : stackArg s₀ 3 = L.scr := by rw [← hLd]; rfl
  obtain a4 : stackArg s₀ 4 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  -- Memory so far changed within the frame.
  obtain o₀ : Outside L.F 0 8 s₀.mem (allocated frameBytes s₀).mem := by
    intro x hx
    simp only [allocated, hsp, ofs] at hx ⊢
    apply Mem.write_apply
    show ¬ (x - L.F).toNat < 8
    omega_using [hx]
  obtain o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    (o₀.mono (by omega_using []) (by simp only [frameBytes]; omega_using [])).trans (h₁.out.mono (by omega_using [])
      (by simp only [oSave, frameBytes]; omega_using []))
  -- The arguments on the stack.
  obtain ⟨-, -, hrd, -⟩ := h
  obtain hargs : ∀ i < 5, InRegions (t₁.rd ++ t₁.wr) (L.F + BitVec.ofNat 64 (argOff i)) 8 ∧
      t₁.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = stackArg s₀ i := fun i hi => by
    obtain e : L.F + BitVec.ofNat 64 (argOff i) = stackArgAddr s₀ 0 + BitVec.ofNat 64 (8 * i) := by
      rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (frameBytes + (96 + 8 * i)) by
        simp only [argOff, frameBytes]; rw [show 304 + 96 + 8 * i = 304 + (96 + 8 * i) by omega_using []], F_add,
        stackArgAddr, hsp, show 32 + 8 * (8 + 0) = 96 by rfl, BitVec.add_assoc, BitVec.ofNat_add]
    refine ⟨?_, ?_⟩
    · rw [h₁.rd, e]
      exact ⟨rsStackArgs s₀, List.mem_append_left _ (show rsStackArgs s₀ ∈ s₀.rd by rw [hrd]; simp),
        VG.Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩
    · rw [show L.F + BitVec.ofNat 64 (argOff i) = off L.F (argOff i) from rfl,
        show t₁.mem.readW (off L.F (argOff i)) 64 = word t₁.mem L.F (argOff i) from rfl,
        o₁.word (.inr (by simp only [argOff, frameBytes]; omega_using [])) (by simp only [argOff, frameBytes]; omega_using [hi])]
      show s₀.mem.readW (L.F + BitVec.ofNat 64 (argOff i)) 64 = _
      rw [e]
      simp only [stackArg, stackArgAddr]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 32 + 8 * (8 + 0) + 8 * i = 32 + 8 * (8 + i) by omega_using []]
  obtain ⟨l0, v0⟩ := hargs 0 (by decide)
  obtain ⟨l1, v1⟩ := hargs 1 (by decide)
  obtain ⟨l2, v2⟩ := hargs 2 (by decide)
  obtain ⟨l3, v3⟩ := hargs 3 (by decide)
  obtain ⟨l4, v4⟩ := hargs 4 (by decide)
  simp only [argOff, frameBytes, Nat.reduceAdd, Nat.reduceMul] at l0 v0 l1 v1 l2 v2 l3 v3 l4 v4
  obtain st : ∀ d, 96 ≤ d → d + 8 ≤ 120 → InRegions t₁.wr (L.F + BitVec.ofNat 64 d) 8 := fun d h₁' h₂' => by
    rw [h₁.wr]; exact ⟨_, List.mem_cons_self .., frameR_contains hL hsp (by omega_using [h₁']) (by simp only [frameBytes]; omega_using [h₂'])⟩
  obtain hr : ∀ r, r ≠ .r0 → r ≠ .r12 → t₁.gpr r = s₀.gpr r := fun r h0 h12 => h₁.others r h0 h12
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
  obtain e₂sp : t₂.sp = L.F := by rw [k₂.sp, h₁.sp, hE]
  obtain e₂wr : t₂.wr = frameR frameBytes s₀ :: s₀.wr := by rw [k₂.wr, h₁.wr]; rfl
  refine WP.mono (clearNonce_ok t₂ hF e₂sp (scr_nonce hL hsp e₂wr)) fun t ⟨⟨_, tz, tou⟩, k₃⟩ => ?_
  -- Memory on exit, from `t₁`'s.
  obtain o₂ : Outside L.F oArgs 24 t₁.mem t₂.mem := by
    rw [bm]
    exact ((writeW_outside _ L.F (d := 96) _ (by omega_using [])).mono (by simp only [oArgs]; omega_using []) (by simp only [oArgs]; omega_using [])).trans
      (((writeW_outside _ L.F (d := 104) _ (by omega_using [])).mono (by simp only [oArgs]; omega_using []) (by simp only [oArgs]; omega_using [])).trans
        ((writeW_outside _ L.F (d := 112) _ (by omega_using [])).mono (by simp only [oArgs]; omega_using []) (by simp only [oArgs]; omega_using [])))
  obtain o₃ : Outside L.F 0 frameBytes s₀.mem t.mem :=
    (o₁.trans (o₂.mono (by omega_using []) (by simp only [oArgs, frameBytes]; omega_using []))).trans
      (tou.mono (by omega_using []) (by simp only [oNonce, frameBytes]; omega_using []))
  obtain w₃ : ∀ d, (d + 8 ≤ oArgs ∨ oNonce + 32 ≤ d) → d + 8 ≤ frameBytes →
      t.mem.readW (off L.F d) 64 = t₁.mem.readW (off L.F d) 64 := fun d hd hd' => by
    obtain e1 := tou.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega_using [hd]) (by simp only [frameBytes] at hd'; omega_using [hd'])
    obtain e2 := o₂.word (d := d) (by simp only [oNonce, oArgs] at hd ⊢; omega_using [hd]) (by simp only [frameBytes] at hd'; omega_using [hd'])
    exact e1.trans e2
  obtain g₃ : ∀ r, r ≠ .r0 → r ≠ .r12 → r ∉ ([.r3, .r4, .r5, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26,
      .r30] : List Reg) → t.gpr r = s₀.gpr r := fun r h0 h12 hr =>
    (k₃.gpr r (by simp [h0, h12])).trans ((k₂.gpr r hr).trans (h₁.others r h0 h12))
  obtain hw2 : ∀ d, 96 ≤ d → d + 8 ≤ 120 → t.mem.readW (off L.F d) 64 = t₂.mem.readW (off L.F d) 64 := fun d h₁' h₂' =>
    tou.word (by simp only [oNonce]; omega_using [h₂']) (by omega_using [h₂'])
  obtain sep : ∀ a b : Nat, a + 8 ≤ b ∨ b + 8 ≤ a → a + 8 ≤ 2 ^ 64 → b + 8 ≤ 2 ^ 64 →
      Mem.Sep (L.F + BitVec.ofNat 64 a) 8 (L.F + BitVec.ofNat 64 b) 8 := fun a b h ha hb => VG.Offset.sep L.F h ha hb
  refine ⟨⟨k₃.sp.trans e₂sp, by rw [k₃.rd, k₂.rd, h₁.rd]; rfl, k₃.wr.trans e₂wr, g₃ .r2 (by decide) (by decide) (by decide),
    (k₃.gpr _ (by decide)).trans b18, (k₃.gpr _ (by decide)).trans b19, (k₃.gpr _ (by decide)).trans b20,
    (k₃.gpr _ (by decide)).trans b21, (k₃.gpr _ (by decide)).trans b22, (k₃.gpr _ (by decide)).trans b23,
    (k₃.gpr _ (by decide)).trans b24, (k₃.gpr _ (by decide)).trans b30, fun i hi => ?_, ?_, ?_, ?_, ?_,
    bytes_outside o₃ hL.dFK (by have := hL.nwKey; omega_using [this]), bytes_outside o₃ hL.dFD (Nat.le_of_lt hL.dl),
    bytes_outside o₃ hL.dFR (Nat.le_of_lt hL.rl)⟩,
    (k₃.gpr _ (by decide)).trans b25, (k₃.gpr _ (by decide)).trans b26, tz⟩
  · rw [w₃ _ (.inr (by simp only [oSave, oNonce]; omega_using [])) (by simp only [oSave, frameBytes]; omega_using [hi])]
    exact h₁.saved i hi
  · rw [w₃ _ (.inr (by decide)) (by decide)]
    exact h₁.savedLr
  · rw [hw2 _ (by decide) (by decide), bm]
    simp only [off, oArgs]
    rw [Mem.readW_writeW_sep (sep 96 112 (by decide) (by omega_using []) (by omega_using [])) (by decide),
      Mem.readW_writeW_sep (sep 96 104 (by decide) (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self64]
  · rw [hw2 _ (by decide) (by decide), bm]
    simp only [off, oArgs, Nat.reduceAdd]
    rw [Mem.readW_writeW_sep (sep 104 112 (by decide) (by omega_using []) (by omega_using [])) (by decide), Mem.readW_writeW_self64]
  · rw [hw2 _ (by decide) (by decide), bm]
    simp only [off, oArgs, Nat.reduceAdd]
    rw [Mem.readW_writeW_self64]

end VG.Proof.Dsa.PPC64LE.RS

end

end


/-!
# Randomized DSA signing on PPC64LE: the sampler's data

q's octets `qbOf` (on entry); the sampler's data `seOf` for them, which are
`SE.Ok` and `SE.Q` when `q > 1`; `prepareQ_ok`: the scan of q keeps `Ctx`
and leaves its data in `r27`–`r29` (`Scanned`), from which `SEnv` follows
(`Scanned.env`), with the tape `randOf` (on entry).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (significant qSigOf)

/-- q's octets, on entry. -/
abbrev qbOf (L : RL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m (off L.key L.pl) L.ql

/-- The tape, on entry. -/
abbrev randOf (L : RL) (m : Mem) : List Byte := Spec.Rsa.bytesAt m L.rand L.rl

/-- The sampler's data. -/
def seOf (L : RL) (qb : List Byte) : SE :=
  ⟨L.F, L.rand, L.rl, off (off L.key L.pl) (L.ql - (significant qb).1), L.ql, (significant qb).1,
    maskOf (significant qb).2.toNat, qSigOf qb⟩

theorem bytesAt_drop (m : Mem) (p : Addr) {n d : Nat} (h : d ≤ n) :
    (Spec.Rsa.bytesAt m p n).drop d = Spec.Rsa.bytesAt m (off p d) (n - d) := by
  have := VG.Proof.Dsa.bytesAt_slice m p (offset := d) (len := n - d) (total := n) (by omega_using [h])
  rw [← this, List.take_of_length_le]
  simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; omega_using []

theorem qs_eq (L : RL) (m : Mem) :
    qSigOf (qbOf L m) = Spec.Rsa.bytesAt m (off (off L.key L.pl) (L.ql - (significant (qbOf L m)).1))
      (significant (qbOf L m)).1 := by
  obtain hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  rw [qSigOf, VG.Proof.Bignum.bytesAt_length, bytesAt_drop _ _ (by omega_using []),
    show L.ql - (L.ql - (significant (qbOf L m)).1) = (significant (qbOf L m)).1 by omega_using [hf]]

theorem seOf_Q {L : RL} (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) : (seOf L (qbOf L m)).Q (qbOf L m) :=
  ⟨VG.Proof.Bignum.bytesAt_length _ _ _, rfl, rfl, rfl, hq⟩

theorem seOf_ok {L : RL} (hL : L.Ok) (m : Mem) (hq : 1 < Spec.Dsa.decodeBE (qbOf L m)) :
    (seOf L (qbOf L m)).Ok := by
  obtain hQ := seOf_Q m hq
  have hW := hQ.W_pos
  obtain hf := Dsa.significant_fits (qbOf L m)
  rw [VG.Proof.Bignum.bytesAt_length] at hf
  have hqb := hL.ql
  have hpl := hL.pl
  have hk := hL.nwKey
  obtain ht : 0 < (significant (qbOf L m)).2.toNat := by
    obtain hn : (significant (qbOf L m)).2 ≠ 0 := fun h0 => by
      have := (Dsa.significant_nonzero (qbOf L m)).mpr h0
      simp only [seOf] at hW; omega_using [hW, this]
    exact Nat.pos_of_ne_zero fun h0 => hn (BitVec.eq_of_toNat_eq h0)
  obtain qoff : (off (off L.key L.pl) (L.ql - (significant (qbOf L m)).1)) =
      off L.key (L.pl + (L.ql - (significant (qbOf L m)).1)) := off_off _ _ _
  obtain qsub : Region.Sub ⟨off (off L.key L.pl) (L.ql - (significant (qbOf L m)).1), (significant (qbOf L m)).1⟩
      L.keyR := by
    rw [qoff]; exact VG.Offset.sub_base _ (by simp only [RL.kl]; omega_using [hf])
  refine ⟨hqb.2, hW, hf, maskOf_lt (significant (qbOf L m)).2.isLt ht, qSigOf_length _, hL.nwRand, hL.rl, ?_,
    hL.fnw, ?_, ?_⟩
  · simp only [seOf]
    rw [qoff, off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [RL.kl] at hk; omega_using [hk])]
    simp only [RL.kl] at hk
    rw [Nat.mod_eq_of_lt (by omega_using [hqb, hpl])]; omega_using [hf, hk]
  · exact (RL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFR (by decide)).symm
  · exact (RL.Ok.frame_disj (d := oNonce) (n := 32) hL.dFK (by decide)).symm.sub_left qsub

/-- The regions on entry, by the call's data. -/
theorem regions_eq {s₀ : State} (h : rsContract.pre s₀) :
    s₀.rd = [(rlOf s₀).keyR, (rlOf s₀).digR, (rlOf s₀).randR, rsStackArgs s₀] ∧
      s₀.wr = [(rlOf s₀).outR, (rlOf s₀).usedR, (rlOf s₀).scrR] := by
  obtain ⟨-, -, hrd, hwr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, hol, hkl, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [hrd]; simp only [rlOf, RL.keyR, RL.digR, RL.randR, RL.kl, hkl]
  · rw [hwr]; simp only [rlOf, RL.outR, RL.usedR, RL.scrR, hol]

/-- After the scan of q. -/
structure Scanned (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r27 : t.gpr .r27 = (seOf L (qbOf L s₀.mem)).qp
  r28 : t.gpr .r28 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).W
  r29 : 1 < Spec.Dsa.decodeBE (qbOf L s₀.mem) → t.gpr .r29 = BitVec.ofNat 64 (seOf L (qbOf L s₀.mem)).M

/-- q's octets as the key holds them in a state of the body. -/
theorem Ctx.qb {L : RL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    Spec.Rsa.bytesAt t.mem (off L.key L.pl) L.ql = qbOf L s₀.mem := by
  have := hL.ql
  rw [← VG.Proof.Dsa.bytesAt_slice t.mem L.key (total := L.kl) (by simp only [RL.kl]; omega_using []), hc.key,
    VG.Proof.Dsa.bytesAt_slice s₀.mem L.key (total := L.kl) (by simp only [RL.kl]; omega_using [])]

theorem prepareQ_ok {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    WP isa prepareQ t fun t' => Scanned (rlOf s₀) s₀ t' ∧
      (t'.gpr .r0 = 0 ↔ ¬ 1 < Spec.Dsa.decodeBE (qbOf (rlOf s₀) s₀.mem)) ∧ t'.mem = t.mem ∧
      Keep (([.r6, .r12] : List Reg) ++ prepRegs) t t' := by
  obtain hL := rlOf_ok h
  have hq := hL.ql
  have hp := hL.pl
  obtain ⟨hrd, -⟩ := regions_eq h
  unfold prepareQ
  refine WP.seq (WP.mono (WP.keep [.r6, .r12] (Q := fun t₁ => t₁.gpr .r12 = off (rlOf s₀).key (rlOf s₀).pl ∧
    t₁.gpr .r6 = BitVec.ofNat 64 (rlOf s₀).ql ∧ t₁.mem = t.mem) (by prun [hc.r19, hc.r20, hc.r21, add0]) (by decide))
    fun t₁ ⟨⟨a12, a6, m1⟩, k1⟩ => ?_)
  refine WP.mono (prepare_ok a12 a6 (by omega_using [hq]) hq.2 fun i hi => ?_) fun t' ⟨⟨b28, b27, b0, b29, m2⟩, k2⟩ => ?_
  · rw [k1.rd, k1.wr, hc.rd, off_off]
    exact ⟨(rlOf s₀).keyR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by simp only [RL.kl]; omega_using [hq, hi]) (by omega_using [hq, hp, hi])⟩
  obtain kk := k1.trans k2
  obtain eqb : Spec.Rsa.bytesAt t₁.mem (off (rlOf s₀).key (rlOf s₀).pl) (rlOf s₀).ql = qbOf (rlOf s₀) s₀.mem := by
    rw [m1]; exact hc.qb hL
  rw [eqb] at b28 b27 b0 b29
  obtain hdis : ∀ r ∈ ctxRegs, r ∉ ([.r6, .r12] ++ prepRegs : List Reg) := by decide
  refine ⟨⟨hc.step hL kk.sp kk.rd kk.wr (fun r hr => kk.gpr r (hdis r hr))
    (by rw [m2, m1]; exact Frame.refl _ _), b27, b28, b29⟩, b0, by rw [m2, m1], kk⟩

/-- The sampler's state, after the scan, for `q > 1`. -/
theorem Scanned.env {s₀ t : State} (h : rsContract.pre s₀) (hs : Scanned (rlOf s₀) s₀ t)
    (hq : 1 < Spec.Dsa.decodeBE (qbOf (rlOf s₀) s₀.mem)) :
    SEnv (seOf (rlOf s₀) (qbOf (rlOf s₀) s₀.mem)) (randOf (rlOf s₀) s₀.mem) t := by
  obtain hL := rlOf_ok h
  obtain hE := seOf_ok hL s₀.mem hq
  obtain ⟨hrd, -⟩ := regions_eq h
  have hc := hs.ctx
  have hW := hE.Wq
  have hk := hL.nwKey
  have hpl := hL.pl
  have hql := hL.ql
  refine ⟨hc.sp, hc.r21, hc.r23, hc.r24, hs.r27, hs.r28, hs.r29 hq, scr_nonce hL rfl hc.wr, fun i hi => ?_,
    fun i hi => ?_, hc.rand, ?_⟩
  · rw [hc.rd, hc.wr]
    exact ⟨(rlOf s₀).randR, List.mem_append_left _ (by rw [hrd]; simp),
      VG.Offset.contains_base _ (by simp only [seOf] at hi ⊢; omega_using [hi]) (by have := hL.rl; simp only [seOf] at hi; omega_using [hi, this])⟩
  · rw [hc.rd, hc.wr]
    simp only [seOf, off_off]
    simp only [seOf] at hW hi
    have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
    exact ⟨(rlOf s₀).keyR, List.mem_append_left _ (by rw [hrd]; exact List.mem_cons_self ..),
      VG.Offset.contains_base _ (by omega_using [hW, hi, ekl]) (by omega_using [hW, hpl, hql, hi])⟩
  · have := qs_eq (rlOf s₀) s₀.mem
    simp only [seOf] at this ⊢
    rw [this, off_off]
    simp only [seOf] at hW
    obtain e1 := VG.Proof.Dsa.bytesAt_slice t.mem (rlOf s₀).key (total := (rlOf s₀).kl)
      (offset := (rlOf s₀).pl + ((rlOf s₀).ql - (significant (qbOf (rlOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (rlOf s₀) s₀.mem)).1) (by simp only [RL.kl]; omega_using [hW])
    obtain e2 := VG.Proof.Dsa.bytesAt_slice s₀.mem (rlOf s₀).key (total := (rlOf s₀).kl)
      (offset := (rlOf s₀).pl + ((rlOf s₀).ql - (significant (qbOf (rlOf s₀) s₀.mem)).1))
      (len := (significant (qbOf (rlOf s₀) s₀.mem)).1) (by simp only [RL.kl]; omega_using [hW])
    rw [hc.key] at e1
    exact e1.symm.trans e2

end VG.Proof.Dsa.PPC64LE.RS

end

end

/-! ### `Dsa.PPC64LE.PrevalidatedSign.Fn`, which this module and modules that import it used -/

section

/-!
# DSA prevalidated signing on PPC64LE: the function

`psign_correct`: `vg_dsa_sign_prevalidated` meets `spContract`. The key
passes validation (`validatePrivate_spec`), so after `Sign.entry`
(`sfront_ok`), `Prevalidated.setup` leaves what `checkKey` would
(`setup_ok`), `Sign.body` signs (`sbody_ok`, with `g^x mod p = y`), and
`restore` gives back the nonvolatile registers (`sfinish_ok`); the result is
the specification's by `Proof/Dsa/Accepted.lean`'s `signBytes_compute`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Dsa.PPC64LE
open VG.Impl.Dsa.PPC64LE.Sign (hOut)

theorem psign_correct (s : State) (h' : spContract.pre s) :
    ∃ tr t, Exec isa PrevalidatedSign.sign s tr t ∧ abiPreserved s t ∧ spContract.post s t := by
  show WP isa PrevalidatedSign.sign s fun t => abiPreserved s t ∧ sContract.post s t
  obtain ⟨h, hval⟩ := h'
  have hL := slayOf_ok h
  have hZ := hL.z256
  have hql := hL.ql
  have hpre := h
  obtain ⟨-, hrd, hwr, -, -, -, dOS, -, dKS, dNS, dDS, -, nwO, nwK, nwN, nwD, -, hv, hol, hkl, -⟩ := h
  have mkSrc : ∀ {A : Addr} {n k : Nat}, (⟨A, n⟩ : Region) ∈ s.rd ++ s.wr →
      (⟨A, n⟩ : Region).Disjoint ⟨stackArg s 1, (stackArg s 2).toNat * 8⟩ → A.toNat + n ≤ 2 ^ 64 → n < 2 ^ 64 →
      k ≤ n → ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) A k :=
    fun hm hd hnw hn hk t hr hw => ⟨fun i hi => ⟨_, by rw [hr, hw]; exact hm,
      Offset.contains_base _ (by omega_arith) (by omega_arith)⟩, fun i hi => Pub.ne_of_disjoint hd (by omega_arith) i (by omega_arith)⟩
  have h4 : (s.gpr .r4).toNat = 2 * (slayOf s).ql := hol
  have h6 : (s.gpr .r6).toNat = 3 * (slayOf s).pl + 2 * (slayOf s).ql := hkl
  have srcK := mkSrc (A := s.gpr .r5) (k := 3 * (slayOf s).pl + 2 * (slayOf s).ql)
    (List.mem_append_left _ (by rw [hrd]; simp)) dKS nwK (s.gpr .r6).isLt (by omega_arith)
  have srcK3 : ∀ t : State, t.rd = s.rd → t.wr = s.wr → Src t (slayOf s) (s.gpr .r5) (3 * (slayOf s).pl + (slayOf s).ql) :=
    fun t hr hw => (srcK t hr hw).take (by omega_arith)
  have srcN := mkSrc (A := s.gpr .r8) (k := (slayOf s).ql) (List.mem_append_left _ (by rw [hrd]; simp)) dNS nwN
    (s.gpr .r9).isLt (Nat.le_refl _)
  have srcD := mkSrc (A := s.gpr .r10) (k := (stackArg s 0).toNat) (List.mem_append_left _ (by rw [hrd]; simp))
    dDS nwD (stackArg s 0).isLt (Nat.le_refl _)
  have srcO := mkSrc (A := s.gpr .r3) (k := 2 * (slayOf s).ql) (List.mem_append_right _ (by rw [hwr]; simp)) dOS nwO
    (s.gpr .r4).isLt (by omega_arith)
  have scrO : ∀ t : State, t.wr = s.wr → Scr t (s.gpr .r3) (2 * (slayOf s).ql) := fun t ht =>
    Scr.of_mem (by rw [ht, hwr, ← h4]; simp) (by omega_arith)
  -- A change in `out` keeps the saved registers.
  have outSep : ∀ {m m' : Mem}, Outside (s.gpr .r3) 0 (2 * (slayOf s).ql) m m' → ∀ i < 19,
      word m' (slayOf s).S (saveOff i) = word m (slayOf s).S (saveOff i) := fun ho i hi =>
    Outside.word_sep (Zp := 2 * (slayOf s).ql) ho (fun x hx => by
        by_contra hc
        exact (srcO s rfl rfl).sep (VG.Proof.Bignum.ofs (s.gpr .r3) x)
          (by simp only [VG.Proof.Bignum.ofs] at hc ⊢; omega_arith) x hx (off_ofs _ x))
      (by omega_arith) (by simp only [saveOff]; omega_arith) hL.nowrap
  -- The specification's values.
  have hkey : Spec.Dsa.privateKeyBytes (s.gpr .r7).toNat (s.gpr .r9).toNat
      (Spec.Rsa.bytesAt s.mem (s.gpr .r5) (s.gpr .r6).toNat) =
      ⟨⟨pOf s.mem (slayOf s) (s.gpr .r5), qOf s.mem (slayOf s) (s.gpr .r5), gOf s.mem (slayOf s) (s.gpr .r5)⟩,
        yOf s.mem (slayOf s) (s.gpr .r5), some (xOf s.mem (slayOf s) (s.gpr .r5))⟩ := by
    rw [VG.Proof.Dsa.privateKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega_arith),
      VG.Proof.Dsa.publicKeyBytes_at s.mem (s.gpr .r5) (by simp only [slayOf] at h6; omega_arith)]
    rfl
  have hspec : ∀ {n : Nat}, VG.Proof.Dsa.shapeValid (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5)) →
      Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) = 8 * n →
      sRes s = if VG.Proof.Dsa.publicChecks (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
            (gOf s.mem (slayOf s) (s.gpr .r5)) (yOf s.mem (slayOf s) (s.gpr .r5)) ∧
          SignOk (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
            (gOf s.mem (slayOf s) (s.gpr .r5)) (yOf s.mem (slayOf s) (s.gpr .r5))
            (xOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8))
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (min (stackArg s 0).toNat n)))
        then some (Spec.Dsa.encodeBE (slayOf s).ql (sigR (pOf s.mem (slayOf s) (s.gpr .r5))
              (qOf s.mem (slayOf s) (s.gpr .r5)) (gOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8))) ++
            Spec.Dsa.encodeBE (slayOf s).ql (sigS (qOf s.mem (slayOf s) (s.gpr .r5)) (xOf s.mem (slayOf s) (s.gpr .r5))
              (kOf s.mem (slayOf s) (s.gpr .r8))
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (s.gpr .r10) (min (stackArg s 0).toNat n)))
              (sigR (pOf s.mem (slayOf s) (s.gpr .r5)) (qOf s.mem (slayOf s) (s.gpr .r5))
                (gOf s.mem (slayOf s) (s.gpr .r5)) (kOf s.mem (slayOf s) (s.gpr .r8)))))
        else none := fun {n} hs hq8 => by
    have hc := VG.Proof.Dsa.signBytes_compute (n := n) (k := kOf s.mem (slayOf s) (s.gpr .r8))
      (nonce := Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (digest := Spec.Rsa.bytesAt s.mem (s.gpr .r10) (stackArg s 0).toNat) hv hs
      (by rw [VG.Proof.Bignum.bytesAt_length]; exact h6) (VG.Proof.Bignum.bytesAt_length _ _ _) hkey rfl hq8
    dsimp only at hc
    unfold sRes
    rw [hc, bytesAt_take]
    rfl
  have hP : PrivOk s.mem (slayOf s) (s.gpr .r5) := by
    have e := validatePrivate_spec (m := s.mem) (L := slayOf s) (key := s.gpr .r5) hv
    rw [show 3 * (slayOf s).pl + 2 * (slayOf s).ql = (s.gpr .r6).toNat from h6.symm] at e
    exact of_decide_eq_true (e.symm.trans hval)
  unfold PrevalidatedSign.sign
  refine WP.seq (WP.mono (sfront_ok hpre) fun s₁ ⟨⟨hr₁, scr₁, r2₁, hout₁, sav₁, out₁⟩, k₁⟩ => ?_)
  have hwr' : ∀ u : State, ScrL u (slayOf s) → ∀ i < 19, InRegions u.wr (off (savW (stackArg s 1)) (8 * i)) 8 :=
    fun u hu i hi => by
      rw [← saveOff_eq]; exact hu.st (d := 104 + 8 * i) (by simp only [slayOf] at hZ ⊢; omega_arith)
  have Out₁ : Outside (slayOf s).S 0 (slayOf s).Z s.mem s₁.mem :=
    out₁.mono (Nat.le_refl _) (by simp only [slayOf] at hZ ⊢; omega_arith)
  obtain ⟨ep₁, eq₁, eg₁, ey₁⟩ := key_kept (srcK3 s rfl rfl) Out₁
  have hKs : KeyOk s₁.mem (slayOf s) (s.gpr .r5) ↔ KeyOk s.mem (slayOf s) (s.gpr .r5) := by
    simp only [KeyOk, ep₁, eq₁, eg₁, ey₁]
  refine WP.seq (setup_ok hL scr₁ hr₁ r2₁ (by omega_arith) (srcK3 s₁ k₁.rd k₁.wr) (hKs.mpr hP.1)
    fun t hK hc Bd kc => ?_)
  have kt := k₁.trans kc
  have Kd := Kept.ofBody hL Bd
  have hKt := hKs.mp hK
  have Ot : Outside (slayOf s).S 0 (slayOf s).Z s.mem t.mem := Out₁.trans Kd.out
  have hq8 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) =
      8 * (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) := by
    have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  have hn32 : Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8 ≤ 32 := by
    have := hKt.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  have ex : xOf t.mem (slayOf s) (s.gpr .r5) = xOf s.mem (slayOf s) (s.gpr .r5) := by
    simp only [xOf]
    rw [((srcK s rfl rfl).sub (o := 3 * (slayOf s).pl + (slayOf s).ql) (k := (slayOf s).ql) (by omega_arith)).kept Ot]
  have hgx : gOf s₁.mem (slayOf s) (s.gpr .r5) ^ xOf t.mem (slayOf s) (s.gpr .r5) % pOf s₁.mem (slayOf s) (s.gpr .r5) =
      yOf s₁.mem (slayOf s) (s.gpr .r5) := by
    rw [ep₁, eg₁, ey₁, ex]; exact hP.2.2
  refine WP.mono (sbody_ok hL hK hgx hc Kd (srcK t kt.rd kt.wr) (srcN t kt.rd kt.wr) (by omega_arith)
    ((srcD t kt.rd kt.wr).take (Nat.min_le_left _ _)) ((Body.hOut Bd).trans hout₁) (scrO t kt.wr)
    (srcO t kt.rd kt.wr)) fun u ⟨⟨ob, r3u, ⟨m, Km, Om⟩, h21u, scru⟩, ku⟩ => ?_
  refine WP.mono (sfinish_ok h21u (hwr' u scru)
    (fun i hi => ((outSep Om i hi).trans (Km.sav i hi)).trans ((Kd.sav i hi).trans (sav₁ i hi)))
    (kt.trans ku)) fun w ⟨hab, w3, wm⟩ => ⟨hab, ?_⟩
  have ek : kOf t.mem (slayOf s) (s.gpr .r8) = kOf s.mem (slayOf s) (s.gpr .r8) := by
    simp only [kOf]; rw [(srcN s rfl rfl).kept Ot]
  rw [ep₁, eq₁, eg₁, ey₁, ex, ek] at ob r3u
  have ed : Spec.Rsa.bytesAt t.mem (s.gpr .r10)
      (min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) =
      Spec.Rsa.bytesAt s.mem (s.gpr .r10)
        (min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8)) := by
    rw [show min (min (stackArg s 0).toNat 64) (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) =
      min (stackArg s 0).toNat (Spec.Dsa.bitLength (qOf s.mem (slayOf s) (s.gpr .r5)) / 8) by omega_arith]
    exact ((srcD s rfl rfl).take (Nat.min_le_left _ _)).kept Ot
  rw [ed] at ob r3u
  have hres := hspec hKt.1 hq8
  simp only [hKt.2, true_and] at hres
  refine ⟨?_, ?_⟩
  · show ((w.gpr .r3).setWidth 32).toNat = _
    rw [w3, r3u, ret_ofNat, hres, signStatus_ite]
  · rw [wm, h4, ob, hres]
    split <;> rfl

end VG.Proof.Dsa.PPC64LE

end

end

/-!
# Randomized DSA signing on PPC64LE: the call of `vg_dsa_sign_prevalidated`

`callArgs` passes `out`, the key, the nonce (in the frame) and the digest,
with their lengths, and the frame holds the arguments on the stack
(`digest_len`, `scratch`, `scratch_len`), so `vg_dsa_sign_prevalidated`'s
contract on the registers (`spContract`) holds, with the regions it is given
(`signRd`, `signWr`): the key, which the frame keeps, passes validation as
on entry. `sign_ok` runs the call by `WP.call` from `psign_correct`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd

/-- The regions `vg_dsa_sign_prevalidated` may read. -/
abbrev signRd (L : RL) : List Region :=
  [L.keyR, ⟨off L.F oNonce, L.ql⟩, L.digR, ⟨off L.F oArgs, 24⟩]

/-- The regions `vg_dsa_sign_prevalidated` may write. -/
abbrev signWr (L : RL) : List Region := [L.outR, L.scrR]

/-- The registers `callArgs` writes. -/
def argRegs' : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10]

/-- The state after `callArgs`. -/
structure Args (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  r3 : t.gpr .r3 = L.out
  r4 : t.gpr .r4 = BitVec.ofNat 64 (2 * L.ql)
  r5 : t.gpr .r5 = L.key
  r6 : t.gpr .r6 = BitVec.ofNat 64 L.kl
  r7 : t.gpr .r7 = BitVec.ofNat 64 L.pl
  r8 : t.gpr .r8 = off L.F oNonce
  r9 : t.gpr .r9 = BitVec.ofNat 64 L.ql
  r10 : t.gpr .r10 = L.dig

theorem callArgs_ok {L : RL} {s₀ t : State} (hL : L.Ok) (hc : Ctx L s₀ t) :
    WP isa (.block callArgs) t fun t' => Args L s₀ t' ∧ t'.mem = t.mem ∧ Keep argRegs' t t' := by
  have hp := hL.pl
  have hq := hL.ql
  have hdis : ∀ r ∈ ctxRegs, r ∉ argRegs' := by decide
  refine WP.mono (WP.keep argRegs' (Q := fun t' => t'.gpr .r3 = L.out ∧ t'.gpr .r4 = BitVec.ofNat 64 (2 * L.ql) ∧
    t'.gpr .r5 = L.key ∧ t'.gpr .r6 = BitVec.ofNat 64 L.kl ∧ t'.gpr .r7 = BitVec.ofNat 64 L.pl ∧
    t'.gpr .r8 = off L.F oNonce ∧ t'.gpr .r9 = BitVec.ofNat 64 L.ql ∧ t'.gpr .r10 = L.dig ∧ t'.mem = t.mem)
    ?_ (by decide)) fun t' ⟨⟨a3, a4, a5, a6, a7, a8, a9, a10, am⟩, k⟩ =>
      ⟨⟨hc.step hL k.sp k.rd k.wr (fun r hr => k.gpr r (hdis r hr)) (by rw [am]; exact Frame.refl _ _),
        a3, a4, a5, a6, a7, a8, a9, a10⟩, am, k⟩
  unfold callArgs
  prun [hc.r18, hc.r19, hc.r20, hc.r21, hc.r22, hc.sp, exec_addSp (show oNonce < 2 ^ 15 by decide), add0,
    ← BitVec.ofNat_add]
  refine ⟨by congr 1; omega_using [], by simp only [RL.kl]; congr 1; omega_using []⟩

/-- The arguments' values in the state `vg_dsa_sign_prevalidated` is entered in. -/
theorem entry_gpr (t : State) (rd wr : List Region) {r : Reg} (h : r ∉ linkRegs) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := State.callEntry_gpr t h

theorem entry_stackArg (t : State) (rd wr : List Region) (i : Nat) :
    stackArg (t.callEntry.withRegions rd wr) i = t.mem.readW (t.sp + BitVec.ofNat 64 (32 + 8 * (8 + i))) 64 := rfl

/-- The signature `vg_dsa_sign_prevalidated` computes from the state `t` it is called in. -/
abbrev sresOf (L : RL) (m : Mem) : Option (List Byte) :=
  Spec.Dsa.signBytes L.pl L.ql (Spec.Rsa.bytesAt m L.key L.kl) (Spec.Rsa.bytesAt m (off L.F oNonce) L.ql)
    (Spec.Rsa.bytesAt m L.dig L.dl)

/-- `vg_dsa_sign`'s contract on the registers holds when it is called. -/
theorem sign_pre' {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    sContract.pre (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have hF := hL.fnw
  have hsw := hL.sw
  have hk := hL.nwKey
  simp only [frameBytes] at hF
  have g3 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r3) (by decide)).trans ha.r3
  have g4 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r4) (by decide)).trans ha.r4
  have g5 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r5) (by decide)).trans ha.r5
  have g6 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r6) (by decide)).trans ha.r6
  have g7 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r7) (by decide)).trans ha.r7
  have g8 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r8) (by decide)).trans ha.r8
  have g9 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r9) (by decide)).trans ha.r9
  have g10 := (entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) (r := .r10) (by decide)).trans ha.r10
  have sa0 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 0 =
      BitVec.ofNat 64 (rlOf s₀).dl := by rw [entry_stackArg, hc.sp]; exact hc.a0
  have sa1 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 1 = (rlOf s₀).scr := by
    rw [entry_stackArg, hc.sp]; exact hc.a1
  have sa2 : stackArg (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) 2 =
      BitVec.ofNat 64 (rlOf s₀).sl := by rw [entry_stackArg, hc.sp]; exact hc.a2
  have ssp : (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))).sp = (rlOf s₀).F := hc.sp
  have sargs : sStackArgs (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) =
      ⟨off (rlOf s₀).F oArgs, 24⟩ := by
    simp only [sStackArgs, stackArgAddr, ssp]; rfl
  have tn : ∀ n, n < 2 ^ 64 → (BitVec.ofNat 64 n).toNat = n := fun n hn => by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have hdl := hL.dl
  have hsl := hL.sl
  have ekl : (rlOf s₀).kl = 3 * (rlOf s₀).pl + 2 * (rlOf s₀).ql := rfl
  have nwN : (off (rlOf s₀).F oNonce).toNat + (rlOf s₀).ql ≤ 2 ^ 64 := by
    rw [off, BitVec.toNat_add, tn _ (by decide), Nat.mod_eq_of_lt (by simp only [oNonce]; omega_using [hF])]
    simp only [oNonce]; omega_using [hq, hF]
  unfold sContract
  dsimp only
  rw [g3, g4, g5, g6, g7, g8, g9, g10, sa0, sa1, sa2, sargs, ssp, tn (2 * (rlOf s₀).ql) (by omega_using [hq]),
    tn (rlOf s₀).kl (by omega_using [hp, hq, ekl]), tn (rlOf s₀).ql (by omega_using [hq]), tn (rlOf s₀).pl (by omega_using [hp]), tn _ hdl, tn _ hsl]
  refine ⟨by omega_using [hF], rfl, rfl, hL.dOK, ?_, hL.dOD, hL.dOS, ?_, hL.dKS, ?_, hL.dDS, ?_, hL.nwOut, hk, nwN, hL.nwDig,
    hL.nwScr, hL.lv, by omega_using [], by omega_using [ekl], by simp only [Spec.Dsa.scratchWords]; omega_using [hsw]⟩
  · exact (RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFO (by simp only [oNonce, frameBytes]; omega_using [hq])).symm
  · exact (RL.Ok.frame_disj (d := oArgs) (n := 24) hL.dFO (by decide)).symm
  · exact RL.Ok.frame_disj (d := oNonce) (n := (rlOf s₀).ql) hL.dFS (by simp only [oNonce, frameBytes]; omega_using [hq])
  · exact (RL.Ok.frame_disj (d := oArgs) (n := 24) hL.dFS (by decide)).symm

/-- The key passes validation, on entry. -/
theorem rs_valid {s₀ : State} (h : rsContract.pre s₀) :
    Spec.Dsa.validatePrivateKeyBytes (rlOf s₀).pl (rlOf s₀).ql
      (Spec.Rsa.bytesAt s₀.mem (rlOf s₀).key (rlOf s₀).kl) = true := by
  have hkl : (rlOf s₀).kl = (s₀.gpr .r7).toNat := by
    have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    simp only [RL.kl, rlOf]; omega_using [this]
  rw [hkl]
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- `vg_dsa_sign_prevalidated`'s contract on the registers holds when it is called. -/
theorem sign_pre {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    spContract.pre (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) := by
  refine ⟨sign_pre' h ha, ?_⟩
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  simp only [State.withRegions_mem, State.callEntry_mem]
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r9 (by decide), ha.r5, ha.r6, ha.r7, ha.r9]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega_using [hp, hq]), ha.ctx.key]
  exact rs_valid h

/-- What the call leaves. -/
structure Signed (L : RL) (s₀ : State) (t t' : State) : Prop where
  ctx : Ctx L s₀ t'
  pres : ∀ r ∈ preserved, t'.gpr r = t.gpr r
  frame : Frame (signWr L) t.mem t'.mem
  r3 : ((t'.gpr .r3).setWidth 32).toNat = Spec.Dsa.signStatus (sresOf L t.mem)
  out : Spec.Rsa.bytesAt t'.mem L.out (2 * L.ql) = (sresOf L t.mem).getD (List.replicate (2 * L.ql) 0)

/-- The regions given to `vg_dsa_sign_prevalidated` are within the caller's. -/
theorem sign_cov {s₀ t : State} (h : rsContract.pre s₀) (hc : Ctx (rlOf s₀) s₀ t) :
    Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) ∧ Covers (signWr (rlOf s₀)) t.wr := by
  have hL := rlOf_ok h
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hrd, hwr⟩ := regions_eq h
  have inF : ∀ d n, 32 ≤ d → d + n ≤ frameBytes → InRegions (t.rd ++ t.wr) (off (rlOf s₀).F d) n := fun d n h₁ h₂ =>
    ⟨_, List.mem_append_right _ (by rw [hc.wr]; exact List.mem_cons_self ..), frameR_contains hL rfl h₁ h₂⟩
  have hcov : Covers (signRd (rlOf s₀) ++ signWr (rlOf s₀)) (t.rd ++ t.wr) := by
    refine VG.Covers.of_forall fun r hr => ?_
    simp only [signRd, signWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; exact List.mem_cons_self ..)
    · exact VG.Covers.one (inF _ _ (by decide) (by simp only [oNonce, frameBytes]; omega_using [hq]))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_left _ (by rw [hc.rd, hrd]; simp)
    · exact VG.Covers.one (inF _ _ (by decide) (by decide))
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
    · exact VG.Covers.of_mem fun r' hr' => by
        simp only [List.mem_singleton] at hr'; subst hr'
        exact List.mem_append_right _ (by rw [hc.wr, hwr]; simp)
  have hcovw : Covers (signWr (rlOf s₀)) t.wr := VG.Covers.of_mem fun r hr => by
    rw [hc.wr, hwr]
    simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp
  exact ⟨hcov, hcovw⟩

/-- The result `vg_dsa_sign_prevalidated` computes, from the state the call enters. -/
theorem sres_eq {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    sRes (t.callEntry.withRegions (signRd (rlOf s₀)) (signWr (rlOf s₀))) = sresOf (rlOf s₀) t.mem := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  have hdl := hL.dl
  simp only [sRes, State.withRegions_mem, State.callEntry_mem]
  rw [g .r5 (by decide), g .r6 (by decide), g .r7 (by decide), g .r8 (by decide), g .r9 (by decide),
    g .r10 (by decide), ha.r5, ha.r6, ha.r7, ha.r8, ha.r9, ha.r10, entry_stackArg, hc.sp]
  have a0' : t.mem.readW ((rlOf s₀).F + BitVec.ofNat 64 (32 + 8 * (8 + 0))) 64 = BitVec.ofNat 64 (rlOf s₀).dl := hc.a0
  rw [a0']
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := (rlOf s₀).pl) (by omega_using [hp]), Nat.mod_eq_of_lt (a := (rlOf s₀).ql) (by omega_using [hq]),
    Nat.mod_eq_of_lt (a := (rlOf s₀).kl) (by simp only [RL.kl]; omega_using [hp, hq]), Nat.mod_eq_of_lt hdl]

theorem sign_ok {s₀ t : State} (h : rsContract.pre s₀) (ha : Args (rlOf s₀) s₀ t) :
    WP isa (.call "vg_dsa_sign_prevalidated" Impl.Dsa.PPC64LE.PrevalidatedSign.sign) t (Signed (rlOf s₀) s₀ t) := by
  have hL := rlOf_ok h
  have hc := ha.ctx
  have hp := hL.pl
  have hq := hL.ql
  obtain ⟨hcov, hcovw⟩ := sign_cov h hc
  refine WP.call (k := spContract) psign_correct (sign_pre h ha) hcov hcovw
    fun t' hrd' hwr' hsp' hf hpres _ hpost => ?_
  have hdis : ∀ r ∈ ctxRegs, r ∈ preserved := by decide
  obtain ⟨p3, pout⟩ := hpost
  have g := fun (r : Reg) (hr : r ∉ linkRegs) => entry_gpr t (signRd (rlOf s₀)) (signWr (rlOf s₀)) hr
  have es := sres_eq h ha
  rw [es] at p3 pout
  refine ⟨hc.step hL hsp' hrd' hwr' (fun r hr => hpres r (hdis r hr)) (hf.mono (by simp)), hpres, hf, p3, ?_⟩
  simp only [State.withRegions_mem, State.withRegions_gpr] at pout
  rw [State.callEntry_gpr t (r := .r3) (by decide), State.callEntry_gpr t (r := .r4) (by decide), ha.r3, ha.r4,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2 * (rlOf s₀).ql) (by omega_using [hq])] at pout
  exact pout

end VG.Proof.Dsa.PPC64LE.RS

end

end

/-! ### `Dsa.PPC64LE.RandomSign.Spec`, which this module and modules that import it used -/

section

/-!
# Randomized DSA signing on PPC64LE: the specification's input

`inpOf`: the specification's input of a call, on entry; its subgroup order
is q's octets' (`inp_q`), its draws are the sampler's (`draw_eq`), and a
nonce of zeros then the candidate is the candidate's encoding (`nonce_eq`).
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput randomSignDraw randomSignRemaining significant)

/-- The specification's input, on entry. -/
def inpOf (L : RL) (m : Mem) : RandomSignInput :=
  ⟨L.pl, L.ql, Spec.Rsa.bytesAt m L.key L.kl, Spec.Rsa.bytesAt m L.dig L.dl, randOf L m⟩

theorem inp_q {L : RL} (hL : L.Ok) (m : Mem) :
    (Spec.Dsa.privateKeyBytes L.pl L.ql (Spec.Rsa.bytesAt m L.key L.kl)).params.q =
      Spec.Dsa.decodeBE (qbOf L m) := by
  have := hL.ql
  simp only [Spec.Dsa.privateKeyBytes, Spec.Dsa.publicKeyBytes]
  rw [VG.Proof.Dsa.bytesAt_slice m L.key (by simp only [RL.kl]; omega_using [])]

theorem draw_eq {L : RL} (hL : L.Ok) (m : Mem) (u : Nat) :
    randomSignDraw (inpOf L m) u = Spec.Dsa.Random.sample (Spec.Dsa.decodeBE (qbOf L m)) 128 ((randOf L m).drop u) := by
  simp only [randomSignDraw, inpOf]
  rw [inp_q hL m]

theorem bytesAt_add' (m : Mem) (p : Addr) (a b : Nat) :
    Spec.Rsa.bytesAt m p (a + b) = Spec.Rsa.bytesAt m p a ++ Spec.Rsa.bytesAt m (off p a) b := by
  simp only [Spec.Rsa.bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, off, BitVec.add_assoc, BitVec.ofNat_add]

/-- The nonce: zeros, then a candidate `k` in its last `W` octets. -/
theorem nonce_eq {F : Addr} {m : Mem} {ql W k : Nat} (hW : W ≤ ql)
    (hz : ∀ j < ql - W, m (off F (oNonce + j)) = 0)
    (hk : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W) = k) :
    Spec.Rsa.bytesAt m (off F oNonce) ql = Spec.Dsa.encodeBE ql k := by
  have e1 : Spec.Rsa.bytesAt m (off F oNonce) (ql - W) = List.replicate (ql - W) 0 := by
    apply List.ext_getElem
    · simp [VG.Proof.Bignum.bytesAt_length]
    · intro j h₁ _
      rw [VG.Proof.Bignum.bytesAt_length] at h₁
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range, List.getElem_replicate]
      rw [show off F oNonce + BitVec.ofNat 64 j = off F (oNonce + j) by simp only [off, BitVec.add_assoc,
        BitVec.ofNat_add]]
      exact hz j h₁
  have e2 : Spec.Rsa.bytesAt m (off F oNonce) ql = List.replicate (ql - W) 0 ++
      Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W := by
    rw [show ql = (ql - W) + W by omega_using [hW], bytesAt_add', e1, Nat.add_sub_cancel]
    simp only [off, BitVec.add_assoc, BitVec.ofNat_add]
  rw [e2, ← hk, ← Dsa.decode_padding _ (ql - W)]
  have hl : (List.replicate (ql - W) 0 ++ Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W).length = ql := by
    simp [VG.Proof.Bignum.bytesAt_length]; omega_using [hW]
  have := Dsa.encodeBE_decodeBE (List.replicate (ql - W) 0 ++ Spec.Rsa.bytesAt m (off F (oNonce + (ql - W))) W)
  rw [hl] at this
  exact this.symm

end VG.Proof.Dsa.PPC64LE.RS

end

end

/-! ### `Dsa.PPC64LE.RandomSign.Finish`, which only this module used -/

section

/-!
# Randomized DSA signing on PPC64LE: after a call of `vg_dsa_sign_prevalidated`

`callFinish_ok`: a signature leaves the status 1; a zero result spends an
attempt, and leaves the status 4 while one is left, else 0.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign

theorem eval_zero_w (s : State) (r : Reg) : isa.eval (.zero .w r) s = some ((s.gpr r).setWidth 32 == 0) := by
  change VG.PPC64LE.eval (.zero .w r) s = _
  simp [VG.PPC64LE.eval, State.read, Size.bits]

theorem setWidth_beq_zero {x : BitVec 64} {st : Nat} (h : (x.setWidth 32).toNat = st) :
    (x.setWidth 32 == 0) = decide (st = 0) := by
  by_cases hs : st = 0
  · subst hs
    simp only [decide_true, beq_iff_eq]
    exact BitVec.eq_of_toNat_eq h
  · simp only [hs, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e
    rw [e] at h
    exact hs h.symm

/-- What `callFinish` leaves, after a call whose result's low word is `st`. -/
theorem callFinish_ok {s : State} {a st : Nat} (h26 : s.gpr .r26 = BitVec.ofNat 64 a) (ha : 1 ≤ a) (ha' : a ≤ 8)
    (h3 : ((s.gpr .r3).setWidth 32).toNat = st) :
    WP isa callFinish s fun t =>
      t.mem = s.mem ∧ Keep [.r26, .r31] s t ∧
        (st ≠ 0 → t.gpr .r31 = BitVec.ofNat 64 1 ∧ t.gpr .r26 = s.gpr .r26) ∧
        (st = 0 → t.gpr .r26 = BitVec.ofNat 64 (a - 1) ∧
          t.gpr .r31 = BitVec.ofNat 64 (if a - 1 = 0 then 0 else 4)) := by
  unfold callFinish
  refine WP.ite (decide (st = 0)) (by rw [eval_zero_w, setWidth_beq_zero h3]) (fun hz => ?_) (fun hz => ?_)
  · simp only [decide_eq_true_eq] at hz
    refine WP.seq (WP.mono (WP.keep [.r26] (Q := fun t => t.mem = s.mem ∧ t.gpr .r26 = BitVec.ofNat 64 (a - 1))
      (by prun [h26, VG.Offset.ofNat_sub_ofNat ha]) (by decide)) fun t₁ ⟨⟨m1, a26⟩, k1⟩ => ?_)
    refine WP.ite (decide (a - 1 ≠ 0)) (eval_nonzero_ofNat' _ _ (by omega_using [ha']) a26) (fun hn => ?_) (fun hn => ?_)
    · simp only [decide_eq_true_eq] at hn
      refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 4) (by prun)
        (by decide)) fun t ⟨⟨tm, t31⟩, k2⟩ => ⟨tm.trans m1, (k1.trans k2).mono (by decide), fun h => absurd hz h,
          fun _ => ⟨(k2.gpr _ (by decide)).trans a26, by rw [t31, ite_eq_right hn]⟩⟩
    · simp only [decide_eq_false_iff_not, Decidable.not_not] at hn
      refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = t₁.mem ∧ t.gpr .r31 = BitVec.ofNat 64 0) (by prun)
        (by decide)) fun t ⟨⟨tm, t31⟩, k2⟩ => ⟨tm.trans m1, (k1.trans k2).mono (by decide), fun h => absurd hz h,
          fun _ => ⟨(k2.gpr _ (by decide)).trans a26, by rw [t31, ite_eq_left hn]⟩⟩
  · simp only [decide_eq_false_iff_not] at hz
    refine WP.mono (WP.keep [.r31] (Q := fun t => t.mem = s.mem ∧ t.gpr .r31 = BitVec.ofNat 64 1) (by prun)
      (by decide)) fun t ⟨⟨tm, t31⟩, k⟩ => ⟨tm, k.mono (by decide), fun _ => ⟨t31, k.gpr _ (by decide)⟩,
        fun h => absurd h hz⟩

end VG.Proof.Dsa.PPC64LE.RS

end

end


/-!
# Randomized DSA signing on PPC64LE: the attempts

`attempts_ok`: from `AttInv` (the specification's remaining attempts from
`u` octets consumed, with `a` attempts left, give the result `resOf`), the
loop of attempts ends in `AttOut`: the result's status and consumption in
`r31` and `r25`, and its signature in `out` when the status is 1.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE.RS

open VG VG.PPC64LE VG.Proof.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE.Random VG.Impl.Dsa.PPC64LE.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.PPC64LE.Rnd
open VG.Proof.Dsa (RandomSignInput RandomSignResultRel randomSignDraw randomSignRemaining randomSignAttemptStatus)
open VG.Proof.Dsa.Random (sampleStatus)

/-- The result, on entry. -/
abbrev resOf (s₀ : State) : Spec.Dsa.RandomSignResult := randomSignRemaining (inpOf (rlOf s₀) s₀.mem) 0 8

/-- The sampler's data, on entry. -/
abbrev eOf (s₀ : State) : SE := seOf (rlOf s₀) (qbOf (rlOf s₀) s₀.mem)

/-- q, on entry. -/
abbrev qOf (s₀ : State) : Nat := Spec.Dsa.decodeBE (qbOf (rlOf s₀) s₀.mem)

/-- The nonce's first `q_len − W` octets are zero. -/
abbrev NZero (s₀ : State) (m : Mem) : Prop :=
  ∀ j < (rlOf s₀).ql - (eOf s₀).W, m (off (rlOf s₀).F (oNonce + j)) = 0

/-- At the head of the attempts' loop, with `a` attempts left and `u` octets consumed. -/
structure AttInv (s₀ : State) (a u : Nat) (t : State) : Prop where
  sc : Scanned (rlOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 u
  hu : u ≤ (rlOf s₀).rl
  r26 : t.gpr .r26 = BitVec.ofNat 64 a
  ha1 : 1 ≤ a
  ha8 : a ≤ 8
  zero : NZero s₀ t.mem
  rel : RandomSignResultRel (inpOf (rlOf s₀) s₀.mem) 0 (resOf s₀) u a

/-- After the attempts. -/
structure AttOut (s₀ : State) (t : State) : Prop where
  sc : Scanned (rlOf s₀) s₀ t
  r25 : t.gpr .r25 = BitVec.ofNat 64 (resOf s₀).used
  r31 : t.gpr .r31 = BitVec.ofNat 64 (resOf s₀).status
  out : (resOf s₀).status = 1 →
    Spec.Rsa.bytesAt t.mem (rlOf s₀).out (2 * (rlOf s₀).ql) =
      (resOf s₀).signature.getD (List.replicate (2 * (rlOf s₀).ql) 0)

theorem sub1_beq : ∀ st < 3, (BitVec.ofNat 64 st - BitVec.ofNat 64 1 == 0) = decide (st = 1) := by decide

theorem sub4_beq : ∀ st < 5, (BitVec.ofNat 64 st - BitVec.ofNat 64 4 == 0) = decide (st = 4) := by decide

theorem sampleStatus_some {S : Spec.Dsa.Random.Sample} : sampleStatus S = 1 ↔ S.scalar.isSome := by
  unfold sampleStatus
  split
  · simp_all
  · rename_i h; simp only [h, Option.isSome_none, Bool.false_eq_true, iff_false]; split <;> decide

/-- The registers of `Scanned` other than `Ctx`'s. -/
theorem Scanned.step {s₀ t t' : State} (hs : Scanned (rlOf s₀) s₀ t) (hc : Ctx (rlOf s₀) s₀ t')
    (h27 : t'.gpr .r27 = t.gpr .r27) (h28 : t'.gpr .r28 = t.gpr .r28) (h29 : t'.gpr .r29 = t.gpr .r29) :
    Scanned (rlOf s₀) s₀ t' :=
  ⟨hc, h27.trans hs.r27, h28.trans hs.r28, fun hq => h29.trans (hs.r29 hq)⟩

/-- A change within the nonce is one within `Ctx`'s regions. -/
theorem outside_frame {L : RL} (hL : L.Ok) {o n : Nat} (hon : o + n ≤ 32) {m m' : Mem}
    (ho : Outside L.F (oNonce + o) n m m') : Frame [L.outR, L.scrR, L.nR] m m' := by
  intro x hx
  have hF := hL.fnw
  refine ho x ?_
  obtain hn := hx L.nR (by simp)
  simp only [Region.Contains, off] at hn
  rw [VG.Offset.toNat_sub_add x L.F (by simp only [oNonce]; omega_using [])] at hn
  simp only [ofs, oNonce, frameBytes] at hn hF ⊢
  have := (x - L.F).isLt
  by_contra hc
  rw [show 2 ^ 64 - 120 + (x - L.F).toNat = (x - L.F).toNat - 120 + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega_using [])] at hn
  omega

/-- The sampler's run keeps `Scanned` and the nonce's zeros. -/
theorem sampled {s₀ t t₁ : State} {u : Nat} {S : Spec.Dsa.Random.Sample} (h : rsContract.pre s₀)
    (hs : Scanned (rlOf s₀) s₀ t) (hz : NZero s₀ t.mem) (so : SampleOut (eOf s₀) (randOf (rlOf s₀) s₀.mem) u S t t₁)
    (hq : 1 < qOf s₀) : Scanned (rlOf s₀) s₀ t₁ ∧ NZero s₀ t₁.mem := by
  obtain hL := rlOf_ok h
  obtain hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  have hW : (eOf s₀).W ≤ (eOf s₀).ql := hE.Wq
  have hql : (eOf s₀).ql ≤ 32 := hE.ql
  have hql' := hL.ql
  obtain hdis : ∀ r ∈ ctxRegs, r ∉ drawRegs := by decide
  refine ⟨hs.step (hs.ctx.step hL so.keep.sp so.keep.rd so.keep.wr (fun r hr => so.keep.gpr r (hdis r hr))
    (outside_frame hL (o := (eOf s₀).ql - (eOf s₀).W) (n := (eOf s₀).W) (by omega_using [hW, hql]) so.out))
    (so.keep.gpr _ (by decide)) (so.keep.gpr _ (by decide)) (so.keep.gpr _ (by decide)), fun j hj => ?_⟩
  have hF := hL.fnw
  obtain e : ofs (eOf s₀).F (off (rlOf s₀).F (oNonce + j)) = oNonce + j :=
    Mont.ofs_off0 _ (by simp only [oNonce, frameBytes] at hF ⊢; omega_using [hql', hj])
  obtain hj' : oNonce + j < (eOf s₀).o := by
    have e2 : (eOf s₀).ql = (rlOf s₀).ql := rfl
    simp only [SE.o]; omega_using [hj, e2]
  rw [so.out _ (.inl (by rw [e]; exact hj'))]
  exact hz j hj

theorem ctx_r3 : ∀ r ∈ ctxRegs, r ∉ ([.r3] : List Reg) := by decide

theorem ctx_r26 : ∀ r ∈ ctxRegs, r ∉ ([.r26, .r31] : List Reg) := by decide

/-- After `[subi r3 r31 4]`, the loop goes on exactly when the status is 4. -/
theorem tail_ok {t : State} {st : Nat} (h31 : t.gpr .r31 = BitVec.ofNat 64 st) (hst : st < 5) :
    WP isa (.block [.subi .r3 .r31 4]) t fun t' =>
      (isa.eval (.zero .d .r3) t' = some (decide (st = 4)) ∧ t'.mem = t.mem) ∧ Keep [.r3] t t' := by
  refine WP.keep (c := .block [.subi .r3 .r31 4]) [.r3] ?_ (by decide)
  prun [h31]
  rw [show VG.PPC64LE.eval (.zero .d .r3) (t.write .r3 (BitVec.ofNat 64 st - BitVec.ofNat 64 4)) =
    some ((t.write .r3 (BitVec.ofNat 64 st - BitVec.ofNat 64 4)).gpr .r3 == 0) from eval_zero _ _]
  gsimp; rw [sub4_beq st hst]

/-- A frame's octet is kept by the call, which writes `out` and `scratch` only. -/
theorem frame_byte {L : RL} (hL : L.Ok) {m m' : Mem} (hf : Frame (signWr L) m m') {d : Nat} (hd : d < frameBytes) :
    m' (off L.F d) = m (off L.F d) := by
  have hF := hL.fnw
  refine hf _ fun r hr hc => ?_
  obtain hin : L.frR.Contains (off L.F d) 1 := VG.Offset.contains_base _ (by omega_using [hd]) (by simp only [frameBytes] at hd; omega_using [hd])
  simp only [signWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hL.dFO _ hin hc
  · exact hL.dFS _ hin hc

/-- One attempt. -/
theorem attempt_ok {s₀ t : State} {a u : Nat} (h : rsContract.pre s₀) (hq : 1 < qOf s₀) (hi : AttInv s₀ a u t) :
    WP isa (.seq attempt (.block [.subi .r3 .r31 4])) t fun t' =>
      isa.eval (.zero .d .r3) t' = some (decide (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a = 4)) ∧
        (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a ≠ 4 → AttOut s₀ t') ∧
        (randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u a = 4 → 1 < a ∧
          AttInv s₀ (a - 1) (u + (randomSignDraw (inpOf (rlOf s₀) s₀.mem) u).used) t') := by
  obtain hL := rlOf_ok h
  obtain hE : (eOf s₀).Ok := seOf_ok hL s₀.mem hq
  obtain hQ := seOf_Q (L := rlOf s₀) s₀.mem hq
  obtain henv := hi.sc.env h hq
  have hql := hL.ql
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by have := hi.ha1; omega_using [this]⟩
  generalize hD : randomSignDraw (inpOf (rlOf s₀) s₀.mem) u = D
  obtain hD' : Spec.Dsa.Random.sample (qOf s₀) 128 ((randOf (rlOf s₀) s₀.mem).drop u) = D := by
    rw [← hD, draw_eq hL]
  obtain hDu : u + D.used ≤ (rlOf s₀).rl := by
    have := Dsa.Random.sample_used_le (qOf s₀) 128 ((randOf (rlOf s₀) s₀.mem).drop u)
    rw [hD', List.length_drop, VG.Proof.Bignum.bytesAt_length] at this
    have := hi.hu; omega_arith
  unfold attempt
  refine WP.seq (WP.seq (WP.mono (sample_ok hE hQ henv hi.r25 hi.hu) fun t₁ so => ?_))
  rw [hD'] at so
  obtain ⟨sc₁, z₁⟩ := sampled h hi.sc hi.zero so hq
  obtain hst := sampleStatus_le D
  refine WP.seq (WP.mono (WP.keep [.r3] (Q := fun t₂ => t₂.mem = t₁.mem ∧
    t₂.gpr .r3 = t₁.gpr .r31 - BitVec.ofNat 64 1) (by prun) (by decide)) fun t₂ ⟨⟨m2, a3⟩, k2⟩ => ?_)
  obtain sc₂ : Scanned (rlOf s₀) s₀ t₂ := sc₁.step (sc₁.ctx.step hL k2.sp k2.rd k2.wr
    (fun r hr => k2.gpr r (ctx_r3 r hr)) (by rw [m2]; exact Frame.refl _ _))
    (k2.gpr _ (by decide)) (k2.gpr _ (by decide)) (k2.gpr _ (by decide))
  obtain b31 : t₂.gpr .r31 = BitVec.ofNat 64 (sampleStatus D) := (k2.gpr _ (by decide)).trans so.r31
  obtain b25 : t₂.gpr .r25 = BitVec.ofNat 64 (u + D.used) := (k2.gpr _ (by decide)).trans so.r25
  obtain b26 : t₂.gpr .r26 = BitVec.ofNat 64 (a' + 1) :=
    (k2.gpr _ (by decide)).trans ((so.keep.gpr _ (by decide)).trans hi.r26)
  refine WP.ite (decide (sampleStatus D = 1)) (by rw [eval_zero, a3, so.r31, sub1_beq _ (by omega_using [hst])])
    (fun hs => ?_) (fun hs => ?_)
  · -- A nonce: the call.
    simp only [decide_eq_true_eq] at hs
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (sampleStatus_some.mp hs)
    have hdk : randomSignDraw (inpOf (rlOf s₀) s₀.mem) u = D := hD
    obtain hnonce : Spec.Rsa.bytesAt t₂.mem (off (rlOf s₀).F oNonce) (rlOf s₀).ql = Spec.Dsa.encodeBE (rlOf s₀).ql k := by
      rw [m2]
      exact nonce_eq (W := (eOf s₀).W) hE.Wq z₁ (so.cand k hk)
    refine WP.seq (WP.mono (callArgs_ok hL sc₂.ctx) fun t₃ ⟨ha3, m3, k3⟩ => ?_)
    refine WP.seq (WP.mono (sign_ok h ha3) fun t₄ sg => ?_)
    obtain es : sresOf (rlOf s₀) t₃.mem = Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql
        (inpOf (rlOf s₀) s₀.mem).key (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest := by
      simp only [sresOf, inpOf]; rw [m3, sc₂.ctx.key, sc₂.ctx.dig, hnonce]
    obtain b26' : t₄.gpr .r26 = BitVec.ofNat 64 (a' + 1) :=
      (sg.pres _ (by decide)).trans ((k3.gpr _ (by decide)).trans b26)
    obtain sc₄ : Scanned (rlOf s₀) s₀ t₄ := sc₂.step sg.ctx ((sg.pres _ (by decide)).trans (k3.gpr _ (by decide)))
      ((sg.pres _ (by decide)).trans (k3.gpr _ (by decide))) ((sg.pres _ (by decide)).trans (k3.gpr _ (by decide)))
    obtain b25' : t₄.gpr .r25 = BitVec.ofNat 64 (u + D.used) :=
      (sg.pres _ (by decide)).trans ((k3.gpr _ (by decide)).trans b25)
    obtain z₄ : NZero s₀ t₄.mem := fun j hj => by
      rw [frame_byte hL sg.frame (by simp only [oNonce, frameBytes]; omega_using [hql, hj]), m3, m2]; exact z₁ j hj
    have hr3 := sg.r3
    rw [es] at hr3
    refine WP.mono (callFinish_ok b26' (by omega_using []) hi.ha8 hr3) fun t₅ ⟨m5, k5, hs1, hs0⟩ => ?_
    obtain sc₅ : Scanned (rlOf s₀) s₀ t₅ := sc₄.step (sc₄.ctx.step hL k5.sp k5.rd k5.wr
      (fun r hr => k5.gpr r (ctx_r26 r hr)) (by rw [m5]; exact Frame.refl _ _))
      (k5.gpr _ (by decide)) (k5.gpr _ (by decide)) (k5.gpr _ (by decide))
    obtain b25'' : t₅.gpr .r25 = BitVec.ofNat 64 (u + D.used) := (k5.gpr _ (by decide)).trans b25'
    obtain hdk' : (randomSignDraw (inpOf (rlOf s₀) s₀.mem) u).scalar = some k := by rw [hD]; exact hk
    cases hsr : Spec.Dsa.signBytes (rlOf s₀).pl (rlOf s₀).ql (inpOf (rlOf s₀) s₀.mem).key
        (Spec.Dsa.encodeBE (rlOf s₀).ql k) (inpOf (rlOf s₀) s₀.mem).digest with
    | some sig =>
      obtain ⟨c31, -⟩ := hs1 (by rw [hsr]; exact Nat.one_ne_zero)
      obtain ⟨rsig, rst, ru⟩ := hi.rel.success hdk' hsr
      rw [hD] at ru
      obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 1 := by
        simp only [randomSignAttemptStatus, hdk']
        simp only [inpOf] at hsr ⊢
        simp [hsr]
      refine WP.mono (tail_ok c31 (by decide)) fun t₆ ⟨⟨ev, m6⟩, k6⟩ =>
        ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
      refine ⟨sc₅.step (sc₅.ctx.step hL k6.sp k6.rd k6.wr (fun r hr => k6.gpr r (ctx_r3 r hr))
        (by rw [m6]; exact Frame.refl _ _)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)),
        ?_, ?_, fun _ => ?_⟩
      · rw [k6.gpr _ (by decide), b25'', ← ru, Nat.zero_add]
      · rw [k6.gpr _ (by decide), c31, rst]
      · rw [m6, m5, sg.out, es, hsr, rsig]
    | none =>
      obtain ⟨c26, c31⟩ := hs0 (by rw [hsr]; rfl)
      obtain rel' := hi.rel.retry hdk' hsr
      rw [hD] at rel'
      by_cases ha0 : a' = 0
      · subst ha0
        rw [ite_eq_left rfl] at c31
        obtain ⟨-, rst, ru⟩ := rel'.exhausted
        obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (0 + 1) = 0 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr]
        refine WP.mono (tail_ok c31 (by decide)) fun t₆ ⟨⟨ev, m6⟩, k6⟩ =>
          ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; cases h4⟩
        refine ⟨sc₅.step (sc₅.ctx.step hL k6.sp k6.rd k6.wr (fun r hr => k6.gpr r (ctx_r3 r hr))
          (by rw [m6]; exact Frame.refl _ _)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)),
          ?_, ?_, fun h1 => absurd (rst ▸ h1) (by decide)⟩
        · rw [k6.gpr _ (by decide), b25'', ← ru, Nat.zero_add]
        · rw [k6.gpr _ (by decide), c31, rst]
      · rw [Nat.add_sub_cancel, ite_eq_right ha0] at c31
        obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = 4 := by
          simp only [randomSignAttemptStatus, hdk']
          simp only [inpOf] at hsr ⊢
          simp [hsr, ha0]
        refine WP.mono (tail_ok c31 (by decide)) fun t₆ ⟨⟨ev, m6⟩, k6⟩ =>
          ⟨by rw [ev, hAS], fun h => absurd hAS h, fun _ => ⟨by omega_using [ha0], ?_⟩⟩
        rw [Nat.add_sub_cancel]
        refine ⟨sc₅.step (sc₅.ctx.step hL k6.sp k6.rd k6.wr (fun r hr => k6.gpr r (ctx_r3 r hr))
          (by rw [m6]; exact Frame.refl _ _)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)) (k6.gpr _ (by decide)),
          (k6.gpr _ (by decide)).trans b25'', hDu, (k6.gpr _ (by decide)).trans (c26.trans (by rw [Nat.add_sub_cancel])), by omega_using [ha0], by have := hi.ha8; omega_using [this], ?_, rel'⟩
        intro j hj
        rw [m6, m5]; exact z₄ j hj
  · -- No nonce: the sampler's status.
    simp only [decide_eq_false_iff_not] at hs
    obtain hk : D.scalar = none := by
      cases hc : D.scalar with
      | none => rfl
      | some k => exact absurd (sampleStatus_some.mpr (by rw [hc]; rfl)) hs
    obtain ⟨rs, rst, ru⟩ := hi.rel.sample_none (hD ▸ hk)
    rw [hD] at rst ru
    obtain hAS : randomSignAttemptStatus (inpOf (rlOf s₀) s₀.mem) u (a' + 1) = sampleStatus D := by
      unfold randomSignAttemptStatus
      rw [hD]
      simp only [hk]
    refine WP.mono (WP.block_nil rfl) fun t₃ e₃ => ?_
    subst e₃
    refine WP.mono (tail_ok b31 (by omega_using [hst])) fun t₄ ⟨⟨ev, m4⟩, k4⟩ =>
      ⟨by rw [ev, hAS], fun _ => ?_, fun h4 => by rw [hAS] at h4; omega⟩
    · refine ⟨sc₂.step (sc₂.ctx.step hL k4.sp k4.rd k4.wr (fun r hr => k4.gpr r (ctx_r3 r hr))
        (by rw [m4]; exact Frame.refl _ _)) (k4.gpr _ (by decide)) (k4.gpr _ (by decide)) (k4.gpr _ (by decide)),
        ?_, ?_, fun h1 => absurd (rst ▸ h1) hs⟩
      · rw [k4.gpr _ (by decide), b25, ← ru, Nat.zero_add]
      · rw [k4.gpr _ (by decide), b31, rst]

end VG.Proof.Dsa.PPC64LE.RS
