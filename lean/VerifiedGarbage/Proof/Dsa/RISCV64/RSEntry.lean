module

public import VerifiedGarbage.Proof.Dsa.RISCV64.RSCtx
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# Randomized DSA signing on RISC-V: the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/RandomSign/Entry.lean`). `entry_ok`: in
the frame, `entry` saves `s0`–`s11` and `ra`, keeps `out`, `used` and the
digest's address in the frame, the key, the lengths, the tape and its
length in `s1`–`s4`, `vg_dsa_sign`'s arguments on the stack in the frame,
`s5 := 0`, `s6 := 8`, and zeroes the nonce (`Entered`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.RS

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.RandomSign
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd

/-- The frame contains its offsets. -/
theorem frameR_contains {L : RL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat}
    (h : d + n ≤ frameBytes) : (frameR s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp]
  exact VG.Offset.contains_base _ h (by simp only [frameBytes] at h; omega)

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

/-- A word of a region apart from the frame is kept by a change within it. -/
theorem readW_outside {L : RL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : 8 ≤ k) (hk' : k ≤ 2 ^ 64) : m'.readW A 64 = m.readW A 64 := by
  refine Mem.readW_congr fun i hi => ho _ (.inr ?_)
  have hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega) (by omega)
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : RL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) : Scr t (off L.F oNonce) 32 := by
  have hF := hL.fnw
  have ha := hL.fal
  simp only [frameBytes] at hF
  refine ⟨⟨(frameR s₀).base, oNonce, frameBytes, by rw [hw]; exact List.mem_cons_self .., ?_, by decide,
    by decide⟩, ?_, ?_⟩
  · simp only [hsp]
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega
  · rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := oNonce) (by decide)]
    simp only [oNonce]
    omega

/-- A word of the frame is writable and aligned. -/
theorem frame_word {L : RL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) {d : Nat} (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) :
    InRegions t.wr (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 := by
  have hF := hL.fnw
  have ha := hL.fal
  refine ⟨⟨_, by rw [hw]; exact List.mem_cons_self .., frameR_contains hL hsp hd⟩, ?_⟩
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by simp only [frameBytes] at hd; omega)]
  simp only [frameBytes] at hF hd
  omega

/-- The lengths in `s2`. -/
theorem lens_entry (pl ql : BitVec 64) (hq : ql.toNat < 65536) :
    ql <<< 16 + pl = lens pl.toNat ql.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show ql.toNat * 2 ^ 16 < 2 ^ 64 by omega)]
  omega

/-- A word of the frame past a write elsewhere in it. -/
theorem word_wW (m : Mem) (F : Addr) {d d' : Nat} (v : BitVec 64) (hd : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (h : d' + 8 ≤ 2 ^ 64) (h' : d + 8 ≤ 2 ^ 64) :
    (m.writeW (off F d') v).readW (off F d) 64 = m.readW (off F d) 64 :=
  (writeW_outside m F v h).word hd h'

/-- What `entry` leaves. -/
structure Entered (L : RL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 0
  s6 : t.gpr .s6 = BitVec.ofNat 64 8
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : rsContract.pre s₀) :
    WP isa (.block entry) (allocd frameBytes s₀) (Entered (rlOf s₀) s₀) := by
  have hL := rlOf_ok h
  generalize hLd : rlOf s₀ = L at hL
  have hsp : s₀.sp = L.sp := by rw [← hLd]; rfl
  have hF := hL.fnw
  have hF' := hF
  simp only [frameBytes] at hF'
  have hspT := hL.spTop
  have hsp16 := hL.sp16
  have hE : (allocd frameBytes s₀).sp = L.F := by simp only [allocd, hsp]
  have hwA : (allocd frameBytes s₀).wr = frameR s₀ :: s₀.wr := rfl
  have hsw : SaveW (allocd frameBytes s₀) L.F := fun i hi =>
    frame_word hL hsp hwA (by simp only [oSave, frameBytes]; omega) (by simp only [oSave]; omega)
  rw [entry, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (saveRegs_ok _ hF hE hsw) fun t₁ h₁ => ?_
  -- The call's data.
  have eo : s₀.gpr .a0 = L.out := by rw [← hLd]; rfl
  have eu : s₀.gpr .a2 = L.used := by rw [← hLd]; rfl
  have ek : s₀.gpr .a3 = L.key := by rw [← hLd]; rfl
  have ed : s₀.gpr .a7 = L.dig := by rw [← hLd]; rfl
  have el : s₀.gpr .a6 <<< 16 + s₀.gpr .a5 = lens L.pl L.ql := by
    rw [lens_entry _ _ (by have := hL.ql; rw [← hLd] at this; simp only [rlOf] at this; omega)]
    rw [← hLd]; rfl
  have a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.dl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have a1 : stackArg s₀ 1 = L.rand := by rw [← hLd]; rfl
  have a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have a3 : stackArg s₀ 3 = L.scr := by rw [← hLd]; rfl
  have a4 : stackArg s₀ 4 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have hr : ∀ r, r ≠ .t0 → t₁.gpr r = s₀.gpr r := fun r h0 => h₁.others r h0
  have o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    h₁.out.mono (by omega) (by simp only [oSave, frameBytes]; omega)
  -- The frame's words of `out`, `used` and the digest.
  have fw := fun (d : Nat) (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) => frame_word hL hsp (t := t₁)
    (by rw [h₁.wr]; rfl) hd h8
  obtain ⟨w64, l64⟩ := fw 64 (by decide) (by decide)
  obtain ⟨w72, l72⟩ := fw 72 (by decide) (by decide)
  obtain ⟨w80, l80⟩ := fw 80 (by decide) (by decide)
  obtain ⟨w0, l0⟩ := fw 0 (by decide) (by decide)
  obtain ⟨w8, l8⟩ := fw 8 (by decide) (by decide)
  obtain ⟨w16, l16⟩ := fw 16 (by decide) (by decide)
  rw [show ([.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .store .d .a7 .t0 oDig, .addi .s1 .a3 0,
      .shift .sll .d .s2 .a6 16, .add .s2 .s2 .a5, .addSp .t6 frameBytes, .load .d .s3 .t6 8,
      .load .d .s4 .t6 16, .load .d .t1 .t6 0, .load .d .t2 .t6 24, .load .d .t3 .t6 32, .store .d .t1 .t0 0,
      .store .d .t2 .t0 8, .store .d .t3 .t0 16, .li .s5 0, .li .s6 8] : List Instr) =
    [.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .store .d .a7 .t0 oDig, .addi .s1 .a3 0,
      .shift .sll .d .s2 .a6 16, .add .s2 .s2 .a5] ++ [.addSp .t6 frameBytes, .load .d .s3 .t6 8,
      .load .d .s4 .t6 16, .load .d .t1 .t6 0, .load .d .t2 .t6 24, .load .d .t3 .t6 32, .store .d .t1 .t0 0,
      .store .d .t2 .t0 8, .store .d .t3 .t0 16, .li .s5 0, .li .s6 8] from rfl, WP.block_append_iff]
  refine WP.mono (wp_sp (WP.keep [.s1, .s2] (Q := fun t =>
    t.gpr .s1 = L.key ∧ t.gpr .s2 = lens L.pl L.ql ∧
      t.mem = ((t₁.mem.writeW (off L.F oOut) L.out).writeW (off L.F oUsed) L.used).writeW (off L.F oDig) L.dig)
    (by
      brun [h₁.t0, hr .a0 (by decide), hr .a2 (by decide), hr .a3 (by decide), hr .a5 (by decide),
        hr .a6 (by decide), hr .a7 (by decide), eo, eu, ek, ed, el, oOut, oUsed, oDig, w64, l64, w72, l72, w80, l80,
        exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl))) fun t₂ ⟨⟨⟨b1, b2, bm⟩, k₂⟩, sp₂⟩ => ?_
  obtain ⟨_, _, hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstk, _⟩ := h
  have hrd' : rsStackArgs s₀ ∈ s₀.rd := by rw [hrd]; simp
  have o₂ : Outside L.F 0 frameBytes s₀.mem t₂.mem := by
    rw [bm]
    refine o₁.trans (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_).trans
      (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_).trans
        ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_))) <;> decide
  have hstk' : L.frR.Disjoint (rsStackArgs s₀) := by
    simpa only [RL.frR, RL.F, hsp, show frameBytes = rsStack from rfl] using hstk
  have hsa0 : stackArgAddr s₀ 0 = L.sp := by simp only [stackArgAddr, hsp]; exact BitVec.add_zero _
  have sw : ∀ i < 5, t₂.mem.readW (off L.F (192 + 8 * i)) 64 = stackArg s₀ i ∧
      InRegions (t₂.rd ++ t₂.wr) (off L.F (192 + 8 * i)) 8 ∧
      (off L.F (192 + 8 * i)).toNat % 8 = 0 := by
    intro i hi
    rw [show 192 + 8 * i = frameBytes + 8 * i from rfl, F_add]
    have hsub : Region.Sub ⟨L.sp + BitVec.ofNat 64 (8 * i), 8⟩ (rsStackArgs s₀) := by
      simp only [rsStackArgs, hsa0]; exact VG.Offset.sub_base _ (by omega)
    refine ⟨?_, ⟨_, List.mem_append_left _ (by rw [k₂.2.1, h₁.rd]; exact hrd'), ?_⟩, ?_⟩
    · rw [readW_outside o₂ (hstk'.sub_right hsub) (by omega) (by omega)]
      simp only [stackArg, stackArgAddr, hsp]
    · simp only [rsStackArgs, hsa0]; exact VG.Offset.contains_base _ (by omega) (by omega)
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega)]; omega
  obtain ⟨r0, i0, al0⟩ := sw 0 (by decide)
  obtain ⟨r1, i1, al1⟩ := sw 1 (by decide)
  obtain ⟨r2, i2, al2⟩ := sw 2 (by decide)
  obtain ⟨r3, i3, al3⟩ := sw 3 (by decide)
  obtain ⟨r4, i4, al4⟩ := sw 4 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at r0 i0 al0 r1 i1 al1 r2 i2 al2 r3 i3 al3 r4 i4 al4
  have hF192 : L.F + BitVec.ofNat 64 192 = off L.F 192 := rfl
  have sp₂' : t₂.sp = L.F := by rw [sp₂, h₁.sp, hE]
  have t0₂ : t₂.gpr .t0 = L.F := by rw [k₂.1 .t0 (by decide), h₁.t0]
  have wr₂ : t₂.wr = t₁.wr := k₂.2.2
  rw [← wr₂] at w0 w8 w16
  refine WP.mono (wp_sp (WP.keep [.t6, .s3, .s4, .t1, .t2, .t3, .s5, .s6] (Q := fun t =>
    t.gpr .s3 = L.rand ∧ t.gpr .s4 = BitVec.ofNat 64 L.rl ∧ t.gpr .s5 = BitVec.ofNat 64 0 ∧
      t.gpr .s6 = BitVec.ofNat 64 8 ∧
      t.mem = ((t₂.mem.writeW (off L.F 0) (BitVec.ofNat 64 L.dl)).writeW (off L.F 8) L.scr).writeW
        (off L.F 16) (BitVec.ofNat 64 L.sl))
    (by
      brun [exec_addSp (show 192 < 2048 by decide), exec_li_zero, exec_li_lit (show 8 < 2048 by decide), sp₂', t0₂, hF192, frameBytes, r0, i0, al0, r1, i1, al1, r2, i2, al2, r3, i3, al3, r4, i4, al4,
        a0, a1, a2, a3, a4, w0, l0, w8, l8, w16, l16]
      rfl) (by decide) (by rfl))) fun t₃ ⟨⟨⟨c3, c4, c5, c6, cm⟩, k₃⟩, sp₃⟩ => ?_
  have sp₃' : t₃.sp = L.F := by rw [sp₃, sp₂']
  have wr₃ : t₃.wr = frameR s₀ :: s₀.wr := by rw [k₃.2.2, wr₂, h₁.wr]; rfl
  refine WP.mono (wp_sp (clearNonce_ok t₃ hF sp₃' (scr_nonce hL hsp wr₃)))
    fun t₄ ⟨⟨⟨_, nz, o₄⟩, k₄⟩, sp₄⟩ => ?_
  -- Memory.
  have o₃ : Outside L.F 0 24 t₂.mem t₃.mem := by
    rw [cm]
    exact ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) (by decide)).trans
      (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) (by decide)).trans
        ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) (by decide)))
  have o₂' : Outside L.F 64 24 t₁.mem t₂.mem := by
    rw [bm]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      (((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
        ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)))
  have o₁₄ : Outside L.F 0 88 t₁.mem t₄.mem :=
    (o₂'.mono (Nat.zero_le _) (by decide)).trans ((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce]; omega)))
  have o₀₄ : Outside L.F 0 frameBytes s₀.mem t₄.mem :=
    o₂.trans (((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce, frameBytes]; omega))))
  have w₃ : ∀ d, d + 8 ≤ 32 → t₄.mem.readW (off L.F d) 64 = t₃.mem.readW (off L.F d) 64 := fun d hd =>
    o₄.word (by simp only [oNonce]; omega) (by omega)
  have w₄ : ∀ d, 64 ≤ d → d + 8 ≤ 88 → t₄.mem.readW (off L.F d) 64 = t₂.mem.readW (off L.F d) 64 :=
    fun d hd hd' => (o₄.word (by simp only [oNonce]; omega) (by omega)).trans
      (o₃.word (by omega) (by omega))
  have gk : ∀ r, r ∉ [Reg.t6, .s3, .s4, .t1, .t2, .t3, .s5, .s6] → r ∉ [Reg.t0, .t1] →
      t₄.gpr r = t₃.gpr r := fun r _ h => k₄.1 r h
  have g2 : ∀ r, r ∉ [Reg.t6, .s3, .s4, .t1, .t2, .t3, .s5, .s6] → r ∉ [Reg.t0, .t1] →
      t₄.gpr r = t₂.gpr r := fun r h h' => (k₄.1 r h').trans (k₃.1 r h)
  refine ⟨⟨by rw [sp₄, sp₃'], by rw [k₄.2.1, k₃.2.1, k₂.2.1, h₁.rd]; rfl,
    by rw [k₄.2.2, wr₃], by rw [g2 _ (by decide) (by decide), b1], by rw [g2 _ (by decide) (by decide), b2],
    by rw [k₄.1 _ (by decide), c3], by rw [k₄.1 _ (by decide), c4], fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, by rw [k₄.1 _ (by decide), c5], by rw [k₄.1 _ (by decide), c6], nz⟩
  · exact (o₁₄.word (by simp only [oSave]; omega) (by simp only [oSave]; omega)).trans (h₁.saved i hi)
  · exact (o₁₄.word (by simp only [oSave]; omega) (by simp only [oSave]; omega)).trans h₁.savedRa
  · rw [w₃ 0 (by decide), cm, word_wW _ _ _ (by decide) (by decide) (by decide),
      word_wW _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [w₃ 8 (by decide), cm, word_wW _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [w₃ 16 (by decide), cm, Mem.readW_writeW_self64]
  · rw [w₄ oOut (by decide) (by decide), bm, word_wW _ _ _ (by decide) (by decide) (by decide),
      word_wW _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
  · rw [w₄ oUsed (by decide) (by decide), bm, word_wW _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [w₄ oDig (by decide) (by decide), bm, Mem.readW_writeW_self64]
  · exact bytes_outside o₀₄ hL.dFK (by have := hL.nwKey; omega)
  · exact bytes_outside o₀₄ hL.dFD (by have := hL.nwDig; omega)
  · exact bytes_outside o₀₄ hL.dFR (by have := hL.nwRand; omega)

end VG.Proof.Dsa.RISCV64.RS
