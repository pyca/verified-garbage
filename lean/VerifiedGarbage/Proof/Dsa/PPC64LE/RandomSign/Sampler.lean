module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Ctx
public import VerifiedGarbage.Impl.Dsa.PPC64LE.RandomSign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Save
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Sample
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Prepare
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.RandomEncoding
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Random.Q

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
