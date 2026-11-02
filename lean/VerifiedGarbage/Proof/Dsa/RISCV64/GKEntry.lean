module

public import VerifiedGarbage.Proof.Dsa.RISCV64.GKCtx
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Dsa.RISCV64.RSEntry
import VerifiedGarbage.Proof.Dsa.RISCV64.Ctx
import VerifiedGarbage.Proof.Bignum.RISCV64.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA key generation on RISC-V: the entry

As on PPC64LE (`Proof/Dsa/PPC64LE/Generate/Entry.lean`). `entry_ok`: in
the frame, `entry` saves `s0`–`s11` and `ra`, keeps `out` and `used` in the
frame, the domain, the lengths, the tape, its length and `scratch` in
`s1`–`s4` and `s6`, `vg_dsa_derive_key`'s argument on the stack
(`scratch_len`) in the frame, `s5 := 0`, and zeroes the nonce (`Entered`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64.GK

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Bignum.RISCV64 VG.Impl.Dsa.RISCV64.Random
open VG.Impl.Dsa.RISCV64.Generate
open VG.Proof.Mont
open VG.Proof.Dsa.RISCV64.Rnd
open VG.Proof.Dsa.RISCV64.RS (frameR lens_entry word_wW)

/-- The frame contains its offsets. -/
theorem frameR_contains {L : GL} {s₀ : State} (hL : L.Ok) (hsp : s₀.sp = L.sp) {d n : Nat}
    (h : d + n ≤ frameBytes) : (frameR s₀).Contains (off L.F d) n := by
  have hF := hL.fnw
  simp only [frameR, hsp]
  exact VG.Offset.contains_base _ h (by simp only [frameBytes] at h; omega)

/-- The frame's offsets past it are the stack pointer's. -/
theorem F_add (L : GL) (d : Nat) : off L.F (frameBytes + d) = L.sp + BitVec.ofNat 64 d := by
  simp only [off, GL.F]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The octets of a region apart from the frame are kept by a change within it. -/
theorem bytes_outside {L : GL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : k ≤ 2 ^ 64) : Spec.Rsa.bytesAt m' A k = Spec.Rsa.bytesAt m A k := by
  simp only [Spec.Rsa.bytesAt, List.map_inj_left, List.mem_range]
  intro i hi
  refine ho _ (.inr ?_)
  have hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega) (by omega)
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- A word of a region apart from the frame is kept by a change within it. -/
theorem readW_outside {L : GL} {m m' : Mem} (ho : Outside L.F 0 frameBytes m m') {A : Addr} {k : Nat}
    (hd : L.frR.Disjoint ⟨A, k⟩) (hk : 8 ≤ k) (hk' : k ≤ 2 ^ 64) : m'.readW A 64 = m.readW A 64 := by
  refine Mem.readW_congr fun i hi => ho _ (.inr ?_)
  have hc : (⟨A, k⟩ : Region).Contains (A + BitVec.ofNat 64 i) 1 := VG.Offset.contains_base A (by omega) (by omega)
  by_contra hcon
  exact hd _ (show L.frR.Contains (A + BitVec.ofNat 64 i) 1 by
    simp only [Region.Contains, frameBytes, ofs] at hcon ⊢; omega) hc

/-- The nonce is a working space of the frame. -/
theorem scr_nonce {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
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
theorem frame_word {L : GL} {s₀ t : State} (hL : L.Ok) (hsp : s₀.sp = L.sp)
    (hw : t.wr = frameR s₀ :: s₀.wr) {d : Nat} (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) :
    InRegions t.wr (off L.F d) 8 ∧ (off L.F d).toNat % 8 = 0 := by
  have hF := hL.fnw
  have ha := hL.fal
  refine ⟨⟨_, by rw [hw]; exact List.mem_cons_self .., frameR_contains hL hsp hd⟩, ?_⟩
  rw [off, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by simp only [frameBytes] at hd; omega)]
  simp only [frameBytes] at hF hd
  omega

/-- What `entry` leaves. -/
structure Entered (L : GL) (s₀ : State) (t : State) : Prop where
  ctx : Ctx L s₀ t
  s5 : t.gpr .s5 = BitVec.ofNat 64 0
  nonce : ∀ j < 32, t.mem (off L.F (oNonce + j)) = 0

theorem entry_ok {s₀ : State} (h : gkContract.pre s₀) :
    WP isa (.block entry) (allocd frameBytes s₀) (Entered (glOf s₀) s₀) := by
  have hL := glOf_ok h
  generalize hLd : glOf s₀ = L at hL
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
  have ek : s₀.gpr .a3 = L.par := by rw [← hLd]; rfl
  have ed : s₀.gpr .a7 = L.rand := by rw [← hLd]; rfl
  have el : s₀.gpr .a6 <<< 16 + s₀.gpr .a5 = lens L.pl L.ql := by
    rw [lens_entry _ _ (by have := hL.ql; rw [← hLd] at this; simp only [glOf] at this; omega)]
    rw [← hLd]; rfl
  have a0 : stackArg s₀ 0 = BitVec.ofNat 64 L.rl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have a1 : stackArg s₀ 1 = L.scr := by rw [← hLd]; rfl
  have a2 : stackArg s₀ 2 = BitVec.ofNat 64 L.sl := by rw [← hLd]; exact (VG.Proof.Bignum.ofNat_toNat64 _).symm
  have hr : ∀ r, r ≠ .t0 → t₁.gpr r = s₀.gpr r := fun r h0 => h₁.others r h0
  have o₁ : Outside L.F 0 frameBytes s₀.mem t₁.mem :=
    h₁.out.mono (by omega) (by simp only [oSave, frameBytes]; omega)
  have fw := fun (d : Nat) (hd : d + 8 ≤ frameBytes) (h8 : d % 8 = 0) => frame_word hL hsp (t := t₁)
    (by rw [h₁.wr]; rfl) hd h8
  obtain ⟨w64, l64⟩ := fw 64 (by decide) (by decide)
  obtain ⟨w72, l72⟩ := fw 72 (by decide) (by decide)
  obtain ⟨w0, l0⟩ := fw 0 (by decide) (by decide)
  rw [show ([.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .addi .s1 .a3 0, .shift .sll .d .s2 .a6 16,
      .add .s2 .s2 .a5, .addi .s3 .a7 0, .addSp .t6 frameBytes, .load .d .s4 .t6 0, .load .d .s6 .t6 8,
      .load .d .t1 .t6 16, .store .d .t1 .t0 0, .li .s5 0] : List Instr) =
    [.store .d .a0 .t0 oOut, .store .d .a2 .t0 oUsed, .addi .s1 .a3 0, .shift .sll .d .s2 .a6 16,
      .add .s2 .s2 .a5, .addi .s3 .a7 0] ++ [.addSp .t6 frameBytes, .load .d .s4 .t6 0, .load .d .s6 .t6 8,
      .load .d .t1 .t6 16, .store .d .t1 .t0 0, .li .s5 0] from rfl, WP.block_append_iff]
  refine WP.mono (wp_sp (WP.keep [.s1, .s2, .s3] (Q := fun t =>
    t.gpr .s1 = L.par ∧ t.gpr .s2 = lens L.pl L.ql ∧ t.gpr .s3 = L.rand ∧
      t.mem = (t₁.mem.writeW (off L.F oOut) L.out).writeW (off L.F oUsed) L.used)
    (by
      brun [h₁.t0, hr .a0 (by decide), hr .a2 (by decide), hr .a3 (by decide), hr .a5 (by decide),
        hr .a6 (by decide), hr .a7 (by decide), eo, eu, ek, ed, el, oOut, oUsed, w64, l64, w72, l72,
        exec_shift_d (show 16 < 64 by decide), BitVec.add_zero]) (by decide) (by rfl)))
    fun t₂ ⟨⟨⟨b1, b2, b3, bm⟩, k₂⟩, sp₂⟩ => ?_
  obtain ⟨_, _, hrd, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hstk, _⟩ := h
  have hrd' : gkStackArgs s₀ ∈ s₀.rd := by rw [hrd]; simp
  have o₂ : Outside L.F 0 frameBytes s₀.mem t₂.mem := by
    rw [bm]
    refine o₁.trans (((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_).trans
      ((writeW_outside _ _ _ (by decide)).mono (Nat.zero_le _) ?_)) <;> decide
  have hstk' : L.frR.Disjoint (gkStackArgs s₀) := by
    simpa only [GL.frR, GL.F, hsp, show frameBytes = gkStack from rfl] using hstk
  have hsa0 : stackArgAddr s₀ 0 = L.sp := by simp only [stackArgAddr, hsp]; exact BitVec.add_zero _
  have sw : ∀ i < 3, t₂.mem.readW (off L.F (192 + 8 * i)) 64 = stackArg s₀ i ∧
      InRegions (t₂.rd ++ t₂.wr) (off L.F (192 + 8 * i)) 8 ∧
      (off L.F (192 + 8 * i)).toNat % 8 = 0 := by
    intro i hi
    rw [show 192 + 8 * i = frameBytes + 8 * i from rfl, F_add]
    have hsub : Region.Sub ⟨L.sp + BitVec.ofNat 64 (8 * i), 8⟩ (gkStackArgs s₀) := by
      simp only [gkStackArgs, hsa0]; exact VG.Offset.sub_base _ (by omega)
    refine ⟨?_, ⟨_, List.mem_append_left _ (by rw [k₂.2.1, h₁.rd]; exact hrd'), ?_⟩, ?_⟩
    · rw [readW_outside o₂ (hstk'.sub_right hsub) (by omega) (by omega)]
      simp only [stackArg, stackArgAddr, hsp]
    · simp only [gkStackArgs, hsa0]; exact VG.Offset.contains_base _ (by omega) (by omega)
    · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega)]; omega
  obtain ⟨r0, i0, al0⟩ := sw 0 (by decide)
  obtain ⟨r1, i1, al1⟩ := sw 1 (by decide)
  obtain ⟨r2, i2, al2⟩ := sw 2 (by decide)
  simp only [Nat.reduceMul, Nat.reduceAdd] at r0 i0 al0 r1 i1 al1 r2 i2 al2
  have hF192 : L.F + BitVec.ofNat 64 192 = off L.F 192 := rfl
  have sp₂' : t₂.sp = L.F := by rw [sp₂, h₁.sp, hE]
  have t0₂ : t₂.gpr .t0 = L.F := by rw [k₂.1 .t0 (by decide), h₁.t0]
  have wr₂ : t₂.wr = t₁.wr := k₂.2.2
  rw [← wr₂] at w0
  refine WP.mono (wp_sp (WP.keep [.t6, .s4, .s6, .t1, .s5] (Q := fun t =>
    t.gpr .s4 = BitVec.ofNat 64 L.rl ∧ t.gpr .s6 = L.scr ∧ t.gpr .s5 = BitVec.ofNat 64 0 ∧
      t.mem = t₂.mem.writeW (off L.F 0) (BitVec.ofNat 64 L.sl))
    (by
      brun [exec_addSp (show 192 < 2048 by decide), exec_li_zero, sp₂', t0₂, hF192, frameBytes, r0, i0, al0,
        r1, i1, al1, r2, i2, al2, a0, a1, a2, w0, l0]
      rfl) (by decide) (by rfl))) fun t₃ ⟨⟨⟨c4, c6, c5, cm⟩, k₃⟩, sp₃⟩ => ?_
  have sp₃' : t₃.sp = L.F := by rw [sp₃, sp₂']
  have wr₃ : t₃.wr = frameR s₀ :: s₀.wr := by rw [k₃.2.2, wr₂, h₁.wr]; rfl
  refine WP.mono (wp_sp (clearNonce_ok t₃ hF sp₃' (scr_nonce hL hsp wr₃)))
    fun t₄ ⟨⟨⟨_, nz, o₄⟩, k₄⟩, sp₄⟩ => ?_
  -- Memory.
  have o₃ : Outside L.F 0 8 t₂.mem t₃.mem := by
    rw [cm]; exact writeW_outside _ _ _ (by decide)
  have o₂' : Outside L.F 64 16 t₁.mem t₂.mem := by
    rw [bm]
    exact ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide)).trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  have o₁₄ : Outside L.F 0 88 t₁.mem t₄.mem :=
    (o₂'.mono (Nat.zero_le _) (by decide)).trans ((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce]; omega)))
  have o₀₄ : Outside L.F 0 frameBytes s₀.mem t₄.mem :=
    o₂.trans (((o₃.mono (Nat.zero_le _) (by decide)).trans
      (o₄.mono (Nat.zero_le _) (by simp only [oNonce, frameBytes]; omega))))
  have w₄ : ∀ d, 64 ≤ d → d + 8 ≤ 88 → t₄.mem.readW (off L.F d) 64 = t₂.mem.readW (off L.F d) 64 :=
    fun d hd hd' => (o₄.word (by simp only [oNonce]; omega) (by omega)).trans
      (o₃.word (by omega) (by omega))
  have g2 : ∀ r, r ∉ [Reg.t6, .s4, .s6, .t1, .s5] → r ∉ [Reg.t0, .t1] →
      t₄.gpr r = t₂.gpr r := fun r h h' => (k₄.1 r h').trans (k₃.1 r h)
  refine ⟨⟨by rw [sp₄, sp₃'], by rw [k₄.2.1, k₃.2.1, k₂.2.1, h₁.rd]; rfl,
    by rw [k₄.2.2, wr₃], by rw [g2 _ (by decide) (by decide), b1], by rw [g2 _ (by decide) (by decide), b2],
    by rw [g2 _ (by decide) (by decide), b3], by rw [k₄.1 _ (by decide), c4], by rw [k₄.1 _ (by decide), c6],
    fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [k₄.1 _ (by decide), c5], nz⟩
  · exact (o₁₄.word (by simp only [oSave]; omega) (by simp only [oSave]; omega)).trans (h₁.saved i hi)
  · exact (o₁₄.word (by simp only [oSave]; omega) (by simp only [oSave]; omega)).trans h₁.savedRa
  · rw [show t₄.mem.readW (off L.F 0) 64 = t₃.mem.readW (off L.F 0) 64 from
      o₄.word (d := 0) (by simp only [oNonce]; omega) (by omega), cm, Mem.readW_writeW_self64]
  · rw [w₄ oOut (by decide) (by decide), bm, word_wW _ _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self64]
  · rw [w₄ oUsed (by decide) (by decide), bm, Mem.readW_writeW_self64]
  · exact bytes_outside o₀₄ hL.dFK (by have := hL.nwPar; omega)
  · exact bytes_outside o₀₄ hL.dFR (by have := hL.nwRand; omega)
end VG.Proof.Dsa.RISCV64.GK
