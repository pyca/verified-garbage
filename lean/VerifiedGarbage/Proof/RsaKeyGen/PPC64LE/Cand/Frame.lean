module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Cand.Pre
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Candidate
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Framework.PPC64LE.StackScratch
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Rsa.PPC64LE.CvBase
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.Syms

/-!
# A candidate on PPC64LE: the frames and the entry

The 400 bytes below the stack pointer on entry, from `cB s0` up: the 176
bytes the round's calls use, then the frame of 176 bytes from `cB + 176`
(the stack pointer of the body: its back chain and header, then `r14`–`r31`
saved from `cB + 208`), then the frame of 48 bytes holding the return
address (at `cB + 384`). `Bx s0 s`: what holds through the body, from the
initial state `s0`: the stack pointer and the permissions, the return address
and the saved registers in the frames, and memory elsewhere but in `out`,
`used`, `scratch` and the stack as `s0`'s. `entry_ok`: the entry's saves and
moves.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.PPC64LE.Cand

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.RsaKeyGen.PPC64LE.Candidate (entry saved frameBytes)

/-- The lowest byte of the stack used. -/
abbrev cB (s0 : State) : Addr := s0.sp - BitVec.ofNat 64 400

/-- The `i`-th register saved. -/
def savedR (i : Nat) : Reg := saved.getD i .r14

/-- The state the body starts from: the return address in `r0`, pushed, and
the frame allocated. -/
def started (s0 : State) : State := allocated 176 (pushed .r0 (s0.write .r0 s0.lr))

/-- The writable regions of the body. -/
abbrev bodyWr (s0 : State) : List Region :=
  ⟨off (cB s0) 208, 144⟩ :: ⟨off (cB s0) 384, 16⟩ :: s0.wr

theorem sp_eq (s0 : State) {d : Nat} (hd : d ≤ 400) :
    s0.sp - BitVec.ofNat 64 d = off (cB s0) (400 - d) := by
  simp only [off, cB]
  rw [← Offset.ofNat_sub_ofNat hd, Offset.sub_add_sub_cancel]

/-- What holds through the body. -/
structure Bx (s0 s : State) : Prop where
  pre : CIn s0
  sp : s.sp = off (cB s0) 176
  rd : s.rd = s0.rd
  wr : s.wr = bodyWr s0
  out : Frame [cO s0, cU s0, cS s0, cF s0] s0.mem s.mem
  lr : s.mem.readW (off (cB s0) 384) 64 = s0.lr
  sv : ∀ i < 18, s.mem.readW (off (cB s0) (208 + 8 * i)) 64 = s0.gpr (savedR i)
  r2 : s.gpr .r2 = s0.gpr .r2


theorem entry_eq : entry = ([.addSp .r11 0, .store .d .r14 .r11 32, .store .d .r15 .r11 40,
    .store .d .r16 .r11 48, .store .d .r17 .r11 56, .store .d .r18 .r11 64, .store .d .r19 .r11 72,
    .store .d .r20 .r11 80, .store .d .r21 .r11 88, .store .d .r22 .r11 96, .store .d .r23 .r11 104,
    .store .d .r24 .r11 112, .store .d .r25 .r11 120, .store .d .r26 .r11 128, .store .d .r27 .r11 136,
    .store .d .r28 .r11 144, .store .d .r29 .r11 152, .store .d .r30 .r11 160, .store .d .r31 .r11 168,
    .addi .r23 .r3 0, .addi .r24 .r4 0, .addi .r25 .r5 0, .addi .r21 .r6 0, .addi .r30 .r7 0,
    .addi .r18 .r8 0, .addi .r19 .r9 0, .addi .r26 .r10 0] : List Instr) ++
    ([.addSp .r27 320, .load .d .r27 .r27 0, .addSp .r31 328, .load .d .r31 .r31 0, .addSp .r11 336,
      .load .d .r11 .r11 0, .li .r28 0] : List Instr) := rfl

/-- What holds when the body starts. -/
structure St0 (s0 s : State) : Prop where
  pre : CIn s0
  sp : s.sp = off (cB s0) 176
  rd : s.rd = s0.rd
  wr : s.wr = bodyWr s0
  out : Frame [cF s0] s0.mem s.mem
  lr : s.mem.readW (off (cB s0) 384) 64 = s0.lr
  gpr : ∀ r, r ≠ .r0 → s.gpr r = s0.gpr r

/-- The memory after the first `k` saves. -/
def saveMem (s0 : State) (m : Mem) : Nat → Mem
  | 0 => m
  | k + 1 => (saveMem s0 m k).writeW (off (cB s0) (208 + 8 * k)) (s0.gpr (savedR k))

theorem cB_fit {s0 : State} (h : CIn s0) : (cB s0).toNat + 400 ≤ 2 ^ 64 := by
  have := h.spLo
  simp only [cB, BitVec.toNat_sub_of_le (show BitVec.ofNat 64 400 ≤ s0.sp by
    rw [BitVec.le_def, BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat]
  have := s0.sp.isLt
  omega

/-- A word at an offset of the frames, through a write of another. -/
theorem fr_sep (m : Mem) (B : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (off B e) v).readW (off B d) 64 = m.readW (off B d) 64 :=
  Mem.readW_writeW_sep (Offset.sep B h hd he) (by decide)

theorem saveMem_sv (s0 : State) (m : Mem) :
    ∀ k ≤ 18, ∀ i < k, (saveMem s0 m k).readW (off (cB s0) (208 + 8 * i)) 64 = s0.gpr (savedR i)
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, i, hi => by
    rw [saveMem]
    by_cases e : i = k
    · subst e; exact Mem.readW_writeW_self64 _ _ _
    · rw [fr_sep _ _ _ (by omega) (by omega) (by omega)]
      exact saveMem_sv s0 m k (by omega) i (by omega)

theorem saveMem_rd (s0 : State) (m : Mem) {d : Nat} (hd : 352 ≤ d) (hd' : d + 8 ≤ 2 ^ 64) :
    ∀ k ≤ 18, (saveMem s0 m k).readW (off (cB s0) d) 64 = m.readW (off (cB s0) d) 64
  | 0, _ => rfl
  | k + 1, hk => by
    rw [saveMem, fr_sep _ _ _ (by omega) hd' (by omega)]
    exact saveMem_rd s0 m hd hd' k (by omega)

theorem saveMem_frame {s0 : State} (h : CIn s0) (m : Mem) : ∀ k ≤ 18, Frame [cF s0] m (saveMem s0 m k)
  | 0, _ => Frame.refl _ _
  | k + 1, hk => by
    have := cB_fit h
    rw [saveMem]
    exact (saveMem_frame h m k (by omega)).writeW (r := cF s0) (by simp) _
      (by show (⟨cB s0, 400⟩ : Region).Contains (cB s0 + BitVec.ofNat 64 (208 + 8 * k)) 8
          exact Offset.contains_base _ (by omega) (by omega))

/-- The stack argument `i < 3` is readable, at `cB + 496 + 8 i`. -/
theorem argAddr (s0 : State) (i : Nat) : stackArgAddr s0 i = off (cB s0) (496 + 8 * i) := by
  show s0.sp + BitVec.ofNat 64 (32 + 8 * (8 + i)) = s0.sp - BitVec.ofNat 64 400 + BitVec.ofNat 64 (496 + 8 * i)
  rw [show 496 + 8 * i = 400 + (32 + 8 * (8 + i)) by omega]
  rw [show BitVec.ofNat 64 (400 + (32 + 8 * (8 + i))) = BitVec.ofNat 64 400 + BitVec.ofNat 64 (32 + 8 * (8 + i))
    from (BitVec.ofNat_add_ofNat _ _).symm, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The pointers and lengths after the entry. -/
structure Regs (s0 s : State) : Prop where
  r23 : s.gpr .r23 = s0.gpr .r3
  r24 : s.gpr .r24 = s0.gpr .r4
  r25 : s.gpr .r25 = s0.gpr .r5
  r21 : s.gpr .r21 = s0.gpr .r6
  r30 : s.gpr .r30 = s0.gpr .r7
  r18 : s.gpr .r18 = s0.gpr .r8
  r19 : s.gpr .r19 = s0.gpr .r9
  r26 : s.gpr .r26 = s0.gpr .r10
  r27 : s.gpr .r27 = PPC64LE.stackArg s0 0
  r31 : s.gpr .r31 = PPC64LE.stackArg s0 1
  r11 : s.gpr .r11 = PPC64LE.stackArg s0 2
  r28 : s.gpr .r28 = 0

theorem entry_ok {s0 s : State} (h : St0 s0 s) :
    WP isa (.block entry) s fun t => Bx s0 t ∧ Regs s0 t := by
  have hp := h.pre
  have hf := cB_fit hp
  have hw : ∀ d, 208 ≤ d → d + 8 ≤ 352 → InRegions s.wr (off (cB s0) d) 8 := fun d h1 h2 =>
    ⟨_, by rw [h.wr]; exact List.mem_cons_self, Offset.contains _ h1 (by omega) (by omega)⟩
  rw [entry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11, .r18, .r19, .r21, .r23, .r24, .r25, .r26, .r30] (Q := fun t =>
      t.mem = saveMem s0 s.mem 18 ∧ t.gpr .r23 = s0.gpr .r3 ∧ t.gpr .r24 = s0.gpr .r4 ∧
      t.gpr .r25 = s0.gpr .r5 ∧ t.gpr .r21 = s0.gpr .r6 ∧ t.gpr .r30 = s0.gpr .r7 ∧ t.gpr .r18 = s0.gpr .r8 ∧
      t.gpr .r19 = s0.gpr .r9 ∧ t.gpr .r26 = s0.gpr .r10) ?_ (by decide))
    fun t ⟨⟨m, a23, a24, a25, a21, a30, a18, a19, a26⟩, k⟩ => ?_
  · prun [VG.Proof.Rsa.PPC64LE.CrtValues.exec_addSp, h.sp, BitVec.add_zero, hw 208 (by decide) (by decide),
      hw 216 (by decide) (by decide),
      hw 224 (by decide) (by decide),
      hw 232 (by decide) (by decide),
      hw 240 (by decide) (by decide),
      hw 248 (by decide) (by decide),
      hw 256 (by decide) (by decide),
      hw 264 (by decide) (by decide),
      hw 272 (by decide) (by decide),
      hw 280 (by decide) (by decide),
      hw 288 (by decide) (by decide),
      hw 296 (by decide) (by decide),
      hw 304 (by decide) (by decide),
      hw 312 (by decide) (by decide),
      hw 320 (by decide) (by decide),
      hw 328 (by decide) (by decide),
      hw 336 (by decide) (by decide),
      hw 344 (by decide) (by decide)]
    rw [h.gpr .r14 (by decide), h.gpr .r15 (by decide), h.gpr .r16 (by decide), h.gpr .r17 (by decide), h.gpr .r18 (by decide), h.gpr .r19 (by decide), h.gpr .r20 (by decide), h.gpr .r21 (by decide), h.gpr .r22 (by decide), h.gpr .r23 (by decide), h.gpr .r24 (by decide), h.gpr .r25 (by decide), h.gpr .r26 (by decide), h.gpr .r27 (by decide), h.gpr .r28 (by decide), h.gpr .r29 (by decide), h.gpr .r30 (by decide), h.gpr .r31 (by decide), h.gpr .r3 (by decide), h.gpr .r4 (by decide), h.gpr .r5 (by decide), h.gpr .r6 (by decide), h.gpr .r7 (by decide), h.gpr .r8 (by decide), h.gpr .r9 (by decide), h.gpr .r10 (by decide)]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hsp : t.sp = off (cB s0) 176 := k.sp.trans h.sp
  have hrd : t.rd = s0.rd := k.rd.trans h.rd
  have fA : (cA s0).Disjoint (cF s0) := hp.FA.symm
  have hA : cA s0 = ⟨off (cB s0) 496, 24⟩ := by rw [cA, argAddr, Nat.mul_zero, Nat.add_zero]
  have ra : ∀ i < 3, InRegions (t.rd ++ t.wr) (off (cB s0) (496 + 8 * i)) 8 := fun i hi =>
    ⟨cA s0, List.mem_append_left _ (by rw [hrd]; exact hp.rA),
      by rw [hA]; exact Offset.contains _ (by omega) (by omega) (by omega)⟩
  have va : ∀ i < 3, t.mem.readW (off (cB s0) (496 + 8 * i)) 64 = PPC64LE.stackArg s0 i := fun i hi => by
    rw [m, saveMem_rd s0 s.mem (by omega) (by omega) 18 (by decide), PPC64LE.stackArg, argAddr]
    exact h.out.readW (r := cA s0) (by rw [hA]; exact Offset.contains _ (by omega) (by omega) (by omega))
      (by simp only [List.mem_singleton, forall_eq]; exact fA) (by decide)
  have va0 := va 0 (by decide)
  have va1 := va 1 (by decide)
  have va2 := va 2 (by decide)
  have ra0 := ra 0 (by decide)
  have ra1 := ra 1 (by decide)
  have ra2 := ra 2 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at va0 va1 va2 ra0 ra1 ra2
  refine WP.mono (WP.keep [.r27, .r31, .r11, .r28] (Q := fun u => u.mem = t.mem ∧
      u.gpr .r27 = PPC64LE.stackArg s0 0 ∧ u.gpr .r31 = PPC64LE.stackArg s0 1 ∧
      u.gpr .r11 = PPC64LE.stackArg s0 2 ∧ u.gpr .r28 = 0) ?_ (by decide))
    fun u ⟨⟨um, u27, u31, u11, u28⟩, ku⟩ => ?_
  · prun [VG.Proof.Rsa.PPC64LE.CrtValues.exec_addSp, hsp, BitVec.add_zero, ra0, ra1, ra2, va0, va1, va2]
    rfl
  · have ks := ku.sp.trans hsp
    refine ⟨⟨hp, ks, ku.rd.trans hrd, ku.wr.trans (k.wr.trans h.wr), ?_, ?_, fun i hi => ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, u27, u31, u11, u28⟩⟩
    · rw [um, m]
      exact (h.out.trans (saveMem_frame hp s.mem 18 (by decide))).mono (by simp)
    · rw [um, m, saveMem_rd s0 s.mem (by omega) (by omega) 18 (by decide)]; exact h.lr
    · rw [um, m]; exact saveMem_sv s0 s.mem 18 (by decide) i hi
    · rw [ku.gpr _ (by decide), k.gpr _ (by decide), h.gpr _ (by decide)]
    all_goals first
      | (rw [ku.gpr _ (by decide)]; with_reducible assumption)

/-! ## The frames -/

theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

theorem started_mem (s0 : State) : (started s0).mem =
    ((s0.mem.writeW (off (cB s0) 352) s0.sp).writeW (off (cB s0) 384) s0.lr).writeW (off (cB s0) 176)
      (s0.sp - 48) := by
  show ((s0.mem.write (s0.sp - 48) 8 s0.sp).write (s0.sp - 48 + 32) 8 s0.lr).write
    (s0.sp - 48 - BitVec.ofNat 64 176) 8 (s0.sp - 48) = _
  have h₁ : s0.sp - 48 = off (cB s0) 352 := by simp only [off, cB]; bv_omega
  have h₂ : s0.sp - 48 + 32 = off (cB s0) 384 := by simp only [off, cB]; bv_omega
  have h₃ : s0.sp - 48 - BitVec.ofNat 64 176 = off (cB s0) 176 := by simp only [off, cB]; bv_omega
  rw [h₃, h₂, write8, write8, write8, ← h₁]

theorem started_ok {s0 : State} (h : CIn s0) : St0 s0 (started s0) := by
  have hf := cB_fit h
  have inF : ∀ d, d + 8 ≤ 400 → (cF s0).Contains (off (cB s0) d) (64 / 8) := fun d hd =>
    Offset.contains_base _ (by omega) (by omega)
  refine ⟨h, ?_, rfl, ?_, ?_, ?_, fun r hr => ?_⟩
  · show s0.sp - 48 - BitVec.ofNat 64 176 = off (cB s0) 176
    simp only [off, cB]; bv_omega
  · show (⟨s0.sp - 48 - BitVec.ofNat 64 176 + 32, 176 - 32⟩ : Region) :: ⟨s0.sp - 48 + 32, 16⟩ :: s0.wr = _
    have h₁ : s0.sp - 48 - BitVec.ofNat 64 176 + 32 = off (cB s0) 208 := by simp only [off, cB]; bv_omega
    have h₂ : s0.sp - 48 + 32 = off (cB s0) 384 := by simp only [off, cB]; bv_omega
    rw [h₁, h₂]
  · rw [started_mem]
    exact (((Frame.refl _ _).writeW (r := cF s0) (by simp) _ (inF 352 (by decide))).writeW (r := cF s0) (by simp) _
      (inF 384 (by decide))).writeW (r := cF s0) (by simp) _ (inF 176 (by decide))
  · rw [started_mem, fr_sep _ _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self64]
  · show (s0.write .r0 s0.lr).gpr r = s0.gpr r
    simp [State.write, hr]

/-- `Bx` through code that keeps the stack pointer and the permissions, and
writes only `out`, `used`, `scratch` and the stack below the frame. -/
theorem Bx.step {s0 s t : State} (h : Bx s0 s) (sp : t.sp = s.sp) (rd : t.rd = s.rd) (wr : t.wr = s.wr)
    (f : Frame [cO s0, cU s0, cS s0, below (off (cB s0) 176) 176] s.mem t.mem) (r2 : t.gpr .r2 = s.gpr .r2) :
    Bx s0 t := by
  have hp := h.pre
  have hf := cB_fit hp
  have bF : below (off (cB s0) 176) 176 = ⟨cB s0, 176⟩ := by
    simp only [below, off, BitVec.add_sub_cancel]
  have dF : ∀ d, 176 ≤ d → d + 8 ≤ 400 → ∀ r ∈ [cO s0, cU s0, cS s0, below (off (cB s0) 176) 176],
      Region.Disjoint ⟨off (cB s0) d, 8⟩ r := by
    intro d h1 h2 r hr
    have sub : Region.Sub ⟨off (cB s0) d, 8⟩ (cF s0) := Offset.sub_base _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.Fo.sub_left sub
    · exact hp.Fu.sub_left sub
    · exact hp.FS.sub_left sub
    · rw [bF]; exact Offset.disjoint_base _ (by omega) (by omega)
  have rdW : ∀ d, 176 ≤ d → d + 8 ≤ 400 → t.mem.readW (off (cB s0) d) 64 = s.mem.readW (off (cB s0) d) 64 :=
    fun d h1 h2 => f.readW (Region.contains_self _ _) (dF d h1 h2) (by decide)
  refine ⟨hp, sp.trans h.sp, rd.trans h.rd, wr.trans h.wr, ?_, ?_, fun i hi => ?_, r2.trans h.r2⟩
  · refine h.out.trans (f.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨cF s0, by simp, by rw [bF]; exact Region.sub_prefix (by decide)⟩
  · rw [rdW 384 (by decide) (by decide)]; exact h.lr
  · rw [rdW _ (by omega) (by omega)]; exact h.sv i hi

theorem restore_eq : VG.Impl.RsaKeyGen.PPC64LE.Candidate.restore = ([.addSp .r11 0, .load .d .r14 .r11 32, .load .d .r15 .r11 40, .load .d .r16 .r11 48, .load .d .r17 .r11 56, .load .d .r18 .r11 64, .load .d .r19 .r11 72, .load .d .r20 .r11 80, .load .d .r21 .r11 88, .load .d .r22 .r11 96, .load .d .r23 .r11 104, .load .d .r24 .r11 112, .load .d .r25 .r11 120, .load .d .r26 .r11 128, .load .d .r27 .r11 136, .load .d .r28 .r11 144, .load .d .r29 .r11 152, .load .d .r30 .r11 160, .load .d .r31 .r11 168] : List Instr) := rfl

/-- `restore`: the saved registers from the frame. -/
theorem restore_ok {s0 s : State} (h : Bx s0 s) :
    WP isa (.block VG.Impl.RsaKeyGen.PPC64LE.Candidate.restore) s fun t =>
      (∀ i < 18, t.gpr (savedR i) = s0.gpr (savedR i)) ∧ t.mem = s.mem ∧ t.gpr .r3 = s.gpr .r3 ∧
        t.gpr .r2 = s.gpr .r2 ∧ t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.lr = s.lr := by
  have hf := cB_fit h.pre
  have rd : ∀ d, 208 ≤ d → d + 8 ≤ 352 → InRegions (s.rd ++ s.wr) (off (cB s0) d) 8 := fun d h1 h2 =>
    ⟨_, List.mem_append_right _ (by rw [h.wr]; exact List.mem_cons_self), Offset.contains _ h1 (by omega) (by omega)⟩
  have sv0 : s.mem.readW (off (cB s0) 208) 64 = s0.gpr .r14 := h.sv 0 (by decide)
  have sv1 : s.mem.readW (off (cB s0) 216) 64 = s0.gpr .r15 := h.sv 1 (by decide)
  have sv2 : s.mem.readW (off (cB s0) 224) 64 = s0.gpr .r16 := h.sv 2 (by decide)
  have sv3 : s.mem.readW (off (cB s0) 232) 64 = s0.gpr .r17 := h.sv 3 (by decide)
  have sv4 : s.mem.readW (off (cB s0) 240) 64 = s0.gpr .r18 := h.sv 4 (by decide)
  have sv5 : s.mem.readW (off (cB s0) 248) 64 = s0.gpr .r19 := h.sv 5 (by decide)
  have sv6 : s.mem.readW (off (cB s0) 256) 64 = s0.gpr .r20 := h.sv 6 (by decide)
  have sv7 : s.mem.readW (off (cB s0) 264) 64 = s0.gpr .r21 := h.sv 7 (by decide)
  have sv8 : s.mem.readW (off (cB s0) 272) 64 = s0.gpr .r22 := h.sv 8 (by decide)
  have sv9 : s.mem.readW (off (cB s0) 280) 64 = s0.gpr .r23 := h.sv 9 (by decide)
  have sv10 : s.mem.readW (off (cB s0) 288) 64 = s0.gpr .r24 := h.sv 10 (by decide)
  have sv11 : s.mem.readW (off (cB s0) 296) 64 = s0.gpr .r25 := h.sv 11 (by decide)
  have sv12 : s.mem.readW (off (cB s0) 304) 64 = s0.gpr .r26 := h.sv 12 (by decide)
  have sv13 : s.mem.readW (off (cB s0) 312) 64 = s0.gpr .r27 := h.sv 13 (by decide)
  have sv14 : s.mem.readW (off (cB s0) 320) 64 = s0.gpr .r28 := h.sv 14 (by decide)
  have sv15 : s.mem.readW (off (cB s0) 328) 64 = s0.gpr .r29 := h.sv 15 (by decide)
  have sv16 : s.mem.readW (off (cB s0) 336) 64 = s0.gpr .r30 := h.sv 16 (by decide)
  have sv17 : s.mem.readW (off (cB s0) 344) 64 = s0.gpr .r31 := h.sv 17 (by decide)
  refine WP.mono (WP.keep [.r11, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31] (Q := fun t =>
      (∀ i < 18, t.gpr (savedR i) = s0.gpr (savedR i)) ∧ t.mem = s.mem) ?_ (by decide))
    fun t ⟨⟨a, b⟩, k⟩ => ⟨a, b, k.gpr _ (by decide), k.gpr _ (by decide), k.sp, k.rd, k.wr, k.lr⟩
  rw [restore_eq]
  prun [VG.Proof.Rsa.PPC64LE.CrtValues.exec_addSp, h.sp, BitVec.add_zero, rd 208 (by decide) (by decide), rd 216 (by decide) (by decide), rd 224 (by decide) (by decide), rd 232 (by decide) (by decide), rd 240 (by decide) (by decide), rd 248 (by decide) (by decide), rd 256 (by decide) (by decide), rd 264 (by decide) (by decide), rd 272 (by decide) (by decide), rd 280 (by decide) (by decide), rd 288 (by decide) (by decide), rd 296 (by decide) (by decide), rd 304 (by decide) (by decide), rd 312 (by decide) (by decide), rd 320 (by decide) (by decide), rd 328 (by decide) (by decide), rd 336 (by decide) (by decide), rd 344 (by decide) (by decide), sv0, sv1, sv2, sv3, sv4, sv5, sv6, sv7, sv8, sv9, sv10, sv11, sv12, sv13, sv14, sv15, sv16, sv17]
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
      i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The body between the entry and the restore. -/
def mid (trial : Prog isa) (name : String) (round : Prog isa) : Prog isa :=
  .seq VG.Impl.RsaKeyGen.PPC64LE.Candidate.zeroOut
    (.seq (.block (VG.Impl.MillerRabin.PPC64LE.Search.geFlag .r5 .r27 .r24))
      (.ite (.zero .d .r5) VG.Impl.RsaKeyGen.PPC64LE.Candidate.finNone
        (VG.Impl.RsaKeyGen.PPC64LE.Candidate.main trial name round)))

theorem wp_seq3 {a b c d : Prog isa} {s : State} {P Q : State → Prop} (h : WP isa (.seq a (.seq b c)) s P)
    (k : ∀ u, P u → WP isa d u Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  rw [WP.seq_iff] at h ⊢
  refine WP.mono h fun x hx => ?_
  rw [WP.seq_iff] at hx ⊢
  refine WP.mono hx fun y hy => ?_
  rw [WP.seq_iff]
  exact WP.mono hy k

/-- The whole function, from what the body between the entry and the
restore does. -/
theorem code_ok {s0 : State} (h : CIn s0) {trial round : Prog isa} {name : String} {Q : BitVec 64 → Mem → Prop}
    (hm : ∀ s, Bx s0 s → Regs s0 s → s.syms = s0.syms →
      WP isa (mid trial name round) s fun u => Bx s0 u ∧ Q (u.gpr .r3) u.mem) :
    WP isa (VG.Impl.RsaKeyGen.PPC64LE.Candidate.code trial name round) s0
      fun t => abiPreserved s0 t ∧ Q (t.gpr .r3) t.mem := by
  have st := started_ok h
  have hlo := h.spLo
  have hf := cB_fit h
  unfold VG.Impl.RsaKeyGen.PPC64LE.Candidate.code
  refine WP.seq (WP.of_runBlock ⟨s0.write .r0 s0.lr,
    (by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mflr]), ?_⟩)
  refine WP.seq (WP.frame (by show 48 ≤ s0.sp.toNat; omega) (WP.alloc (by decide)
    (by show 176 ≤ (s0.sp - 48).toNat
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; show 48 ≤ s0.sp.toNat; omega)]
        show 176 ≤ s0.sp.toNat - 48; omega) ?_))
  show WP isa (.seq (.block VG.Impl.RsaKeyGen.PPC64LE.Candidate.entry) (.seq _ (.seq _ (.seq _ _)))) (started s0) _
  refine WP.seq (WP.mono_syms (entry_ok st) fun s ⟨bs, rs⟩ sy => ?_)
  refine wp_seq3 (hm s bs rs sy) fun u ⟨bu, qu⟩ => ?_
  refine WP.mono (restore_ok bu) fun v ⟨sv, vm, v3, v2, vsp, _, _, _⟩ => ?_
  -- The frames' pops and `mtlr`.
  refine WP.of_runBlock ⟨_, (by simp only [runBlock_cons, runStep_some, runBlock_nil, exec_mtlr]; rfl), ?_⟩
  have spv : v.sp = off (cB s0) 176 := vsp.trans bu.sp
  have e1 : (freed 176 v).sp = off (cB s0) 352 := by
    show v.sp + BitVec.ofNat 64 176 = _; rw [spv, off_add]
  refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_⟩
  · have h0 : r ≠ .r0 := fun e => by subst e; exact absurd hr (by decide)
    show ((freed 176 v).write .r0 _).gpr r = _
    simp only [State.write, h0, ↓reduceIte]
    show v.gpr r = s0.gpr r
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · rw [v2]; exact bu.r2
    all_goals first
      | exact sv 0 (by decide) | exact sv 1 (by decide) | exact sv 2 (by decide) | exact sv 3 (by decide)
      | exact sv 4 (by decide) | exact sv 5 (by decide) | exact sv 6 (by decide) | exact sv 7 (by decide)
      | exact sv 8 (by decide) | exact sv 9 (by decide) | exact sv 10 (by decide) | exact sv 11 (by decide)
      | exact sv 12 (by decide) | exact sv 13 (by decide) | exact sv 14 (by decide) | exact sv 15 (by decide)
      | exact sv 16 (by decide) | exact sv 17 (by decide)
  · show (freed 176 v).sp + 48 = s0.sp
    rw [e1]; simp only [off, cB]; bv_omega
  · show (freed 176 v).mem.read ((freed 176 v).sp + 32) 8 = s0.lr
    rw [e1, show off (cB s0) 352 + 32 = off (cB s0) 384 from off_add _ _ 32, read8]
    show v.mem.readW _ 64 = _
    rw [vm]; exact bu.lr
  · show Q (((freed 176 v).write .r0 ((freed 176 v).mem.read ((freed 176 v).sp + 32) 8)).gpr .r3) (freed 176 v).mem
    simp only [State.write, show Reg.r3 ≠ Reg.r0 by decide, ↓reduceIte]
    show Q (v.gpr .r3) v.mem
    rw [vm, v3]; exact qu

end VG.Proof.RsaKeyGen.PPC64LE.Cand
