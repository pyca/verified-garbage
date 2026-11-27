module

public import VerifiedGarbage.Impl.Ffdh.X86.Domain
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.StageR
import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Import
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue

/-!
# FFDH on i686: the operations on the wide slots

What the stages of the FFDH functions change: the ranges `fR` (the working
space but the saved registers' words, up to `need`). The operations of a
context (`stR len 0`: the header's first two words, the first nine wide
slots and the table) keep the FFDH slots 9 to 19 and the header from word 2
on (`opsKeep`); a number written into one wide slot keeps the others
(`slotKeep`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Bignum.X86 VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop} {s : State} {base : Addr} {bytes len : Nat}
  {args : Nat → BitVec 32}

/-- The ranges a stage changes: the working space up to `need`, but the saved registers' words. -/
abbrev fR (len : Nat) : List (Nat × Nat) := [(0, 32), (48, CrtRt.need len - 48)]

/-- A range within those of `fR`. -/
abbrev InF (len : Nat) (p : Nat × Nat) : Prop :=
  p.1 + p.2 ≤ 32 ∨ (48 ≤ p.1 ∧ p.1 + p.2 ≤ CrtRt.need len)

theorem fR_widenR {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameR base sp ws) m m')
    (hw : ∀ p ∈ ws, InF len p) : Frame (frameR base sp (fR len)) m m' :=
  frameR_widen F fun p hp => by
    rcases hw p hp with e | e
    · exact ⟨(0, 32), by simp, by omega_using [], by omega_using [e]⟩
    · exact ⟨(48, CrtRt.need len - 48), by simp, by dsimp only; omega_using [e], by dsimp only; omega_using [e]⟩

/-- The regions a stage may change: those of the operations (`frameR`), and the 176 bytes below `sp`,
room for a call of a callee that copies the 76 bytes of arguments below its return address and
calls the operations. -/
def frameF (base : Addr) (sp : BitVec 32) (ws : List (Nat × Nat)) : List Region :=
  below sp 176 :: frameR base sp ws

/-- The 176 bytes below `sp` that a stage may change are apart from the working space. -/
structure RoomF (sp : BitVec 32) (base : Addr) (size : Nat) : Prop where
  low : 176 ≤ sp.toNat
  apart : Region.Disjoint (below sp 176) ⟨base, size⟩

theorem RoomF.call {sp : BitVec 32} {size : Nat} (R : RoomF sp base size) : CallRoom sp base size :=
  ⟨by have := R.low; omega, R.apart.sub_left (VG.X86.below_sub (by decide) R.low)⟩

theorem frameF_of {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameR base sp ws) m m') :
    Frame (frameF base sp ws) m m' :=
  F.mono fun _ hr => List.mem_cons_of_mem _ hr

theorem frameF_mono {sp : BitVec 32} {ws ws' : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameF base sp ws) m m')
    (h : ∀ p ∈ ws, p ∈ ws' := by decide) : Frame (frameF base sp ws') m m' :=
  F.mono fun r hr => by
    simp only [frameF, frameR, List.mem_cons, List.mem_map] at hr ⊢
    rcases hr with rfl | rfl | ⟨p, hp, rfl⟩
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr ⟨p, h p hp, rfl⟩)

theorem frameF_widen {sp : BitVec 32} {ws ws' : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameF base sp ws) m m')
    (hw : ∀ p ∈ ws, ∃ q ∈ ws', q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2) : Frame (frameF base sp ws') m m' :=
  F.sub fun r hr => by
    simp only [frameF, frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | rfl | ⟨p, hp, rfl⟩
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · obtain ⟨q, hq, h1, h2⟩ := hw p hp
      exact ⟨⟨off base q.1, q.2⟩,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩)), VG.Offset.sub base h1 h2⟩

theorem fF_widen {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameF base sp ws) m m')
    (hw : ∀ p ∈ ws, InF len p) : Frame (frameF base sp (fR len)) m m' :=
  F.sub fun r hr => by
    simp only [frameF, frameR, List.mem_cons, List.mem_map] at hr
    rcases hr with rfl | rfl | ⟨p, hp, rfl⟩
    · exact ⟨_, List.mem_cons_self .., fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · obtain ⟨q, hq, h1, h2⟩ : ∃ q ∈ fR len, q.1 ≤ p.1 ∧ p.1 + p.2 ≤ q.1 + q.2 := by
        rcases hw p hp with e | e
        · exact ⟨(0, 32), by simp, by omega_using [], by omega_using [e]⟩
        · exact ⟨(48, CrtRt.need len - 48), by simp, by dsimp only; omega_using [e], by dsimp only; omega_using [e]⟩
      exact ⟨⟨off base q.1, q.2⟩,
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩)), VG.Offset.sub base h1 h2⟩

theorem fR_widen {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameR base sp ws) m m')
    (hw : ∀ p ∈ ws, InF len p) : Frame (frameF base sp (fR len)) m m' :=
  fF_widen (frameF_of F) hw

/-- A number apart from the ranges keeps its value. -/
theorem frameF_val32 {sp : BitVec 32} {ws : List (Nat × Nat)} {m m' : Mem} (F : Frame (frameF base sp ws) m m')
    (R : RoomF sp base bytes) (nw : base.toNat + bytes ≤ 2 ^ 32) {d k : Nat} (hd : d + 4 * k ≤ bytes)
    (hws : ∀ p ∈ ws, d + 4 * k ≤ p.1 ∨ p.1 + p.2 ≤ d) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    val32 m' base d k = val32 m base d k := by
  rw [← VG.Proof.Bignum.read_eq_val32, ← VG.Proof.Bignum.read_eq_val32]
  refine congrArg BitVec.toNat (F.read (r := ⟨off base d, 4 * k⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by omega_using [nw, hd]))
  obtain sub : Region.Sub ⟨off base d, 4 * k⟩ ⟨base, bytes⟩ := by
    have := Offset.sub base (d := d) (n := 4 * k) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [hd])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this
  simp only [frameF, frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | rfl | ⟨p, hp, rfl⟩
  · exact (R.apart.sub_right sub).symm
  · exact (R.call.apart.sub_right sub).symm
  · have := hws p hp
    have := hfit p hp
    exact Offset.disjoint base (by omega_arith) (by omega_using [nw, hd]) (by omega_using [nw, this])

/-- The inputs hold after a stage that changes registers but `edi` and `esp`, and memory in its ranges. -/
theorem in_keepFF (h : In Ex base bytes len args s) {t : State} {regs : List Reg} (K : Keeps regs s t)
    (di : .edi ∉ regs) (sp : .esp ∉ regs) (RF : RoomF (s.gpr .esp) base bytes) {ws : List (Nat × Nat)}
    (F : Frame (frameF base (s.gpr .esp) ws) s.mem t.mem) (hfit : ∀ p ∈ ws, p.1 + p.2 ≤ bytes) :
    In Ex base bytes len args t := by
  have low := RF.low
  have top := h.top
  have esp : t.gpr .esp = s.gpr .esp := K.1 _ sp
  refine ⟨h.scratch.of_keeps K di sp, h.lower, h.upper, fun i hi => ⟨(h.stack i hi).stack.keep K sp, ?_⟩,
    h.outLen, by rw [esp]; exact h.room, by rw [esp]; exact h.top, h.need, h.hbase, h.hbytes,
    by rw [K.2.1, K.2.2]; exact h.extra⟩
  have A := h.stack i hi
  rw [← A.value]
  unfold VG.Proof.Dsa.X86.stackValue
  rw [show VG.Proof.Dsa.X86.stackAddress t i = VG.Proof.Dsa.X86.stackAddress s i by
    simp only [VG.Proof.Dsa.X86.stackAddress, esp]]
  have ea : (VG.Proof.Dsa.X86.stackAddress s i).toNat = (s.gpr .esp).toNat + (4 + 4 * i) := by
    simp only [VG.Proof.Dsa.X86.stackAddress, addr, VG.Proof.Bignum.X86.PublicRt.setWidth_toNat,
      BitVec.toNat_add, BitVec.toNat_ofNat]
    omega_using [top, hi]
  refine F.readW (r := ⟨VG.Proof.Dsa.X86.stackAddress s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [frameF, frameR, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | rfl | ⟨p, hp, rfl⟩
  · have eb : ((s.gpr .esp - BitVec.ofNat 32 176).setWidth 64).toNat = (s.gpr .esp).toNat - 176 := by
      rw [VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega_using [low])]
    exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 176) (.inl (by dsimp only; rw [eb, ea]; omega_using [low]))
      (by dsimp only; rw [eb]; omega_using []) (by dsimp only; rw [ea]; omega_using [hi])).symm
  · have eb : ((s.gpr .esp - BitVec.ofNat 32 96).setWidth 64).toNat = (s.gpr .esp).toNat - 96 := by
      rw [VG.Proof.Bignum.X86.PublicRt.setWidth_toNat, VG.X86.sub_toNat (by omega_using [low])]
    exact (Region.disjoint_of_le (r₁ := below (s.gpr .esp) 96) (.inl (by dsimp only; rw [eb, ea]; omega_using [low]))
      (by dsimp only; rw [eb]; omega_using []) (by dsimp only; rw [ea]; omega_using [hi])).symm
  · refine A.stack.apart.sub_right ?_
    have := hfit p hp
    have := Offset.sub base (d := p.1) (n := p.2) (e := 0) (k := bytes) (Nat.zero_le _) (by omega_using [this])
    simpa only [off, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using this

theorem fR_fit (h : In Ex base bytes len args s) : ∀ p ∈ fR len, p.1 + p.2 ≤ bytes := by
  have := h.need
  have : 48 ≤ CrtRt.need len := by simp only [CrtRt.need, numBase]; omega_using []
  intro p hp
  simp only [fR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> dsimp only <;> omega_arith

theorem fR_of_outside (h : In Ex base bytes len args s) {sp : BitVec 32} {a n : Nat} {m m' : Mem}
    (O : Outside base a n m m') (hw : InF len (a, n)) : Frame (frameF base sp (fR len)) m m' := by
  have := fR_fit h
  have bl := h.bytes_lt
  have : a + n ≤ bytes := by
    rcases hw with e | e
    · have := this (0, 32) (by simp); dsimp only at *; omega_using [e, this]
    · have := this (48, CrtRt.need len - 48) (by simp); dsimp only at *; omega_using [e, this]
  exact fR_widen (frameR_of_outside O (by omega_using [bl, this]) (List.mem_singleton_self _))
    fun p hp => by rw [List.mem_singleton.mp hp]; exact hw

theorem fR_of_outsideR (h : In Ex base bytes len args s) {sp : BitVec 32} {a n : Nat} {m m' : Mem}
    (O : Outside base a n m m') (hw : InF len (a, n)) : Frame (frameR base sp (fR len)) m m' := by
  have := fR_fit h
  have bl := h.bytes_lt
  have : a + n ≤ bytes := by
    rcases hw with e | e
    · have := this (0, 32) (by simp); dsimp only at *; omega_using [e, this]
    · have := this (48, CrtRt.need len - 48) (by simp); dsimp only at *; omega_using [e, this]
  exact fR_widenR (frameR_of_outside O (by omega_using [bl, this]) (List.mem_singleton_self _))
    fun p hp => by rw [List.mem_singleton.mp hp]; exact hw

/-- The ranges of the operations of a context, within `fR`. -/
theorem stR_inF (h : In Ex base bytes len args s) : ∀ p ∈ stR len 0, InF len p := by
  have T := h.table_fit .wide
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  have t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega_using []
  have e28 : lo len (.slot .wide 28) = numBase + 28 * st len .wide := rfl
  have := h.slot_fit .wide (j := 27) (by decide)
  intro p hp
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> (try dsimp only) <;> omega

/-- A wide slot from 9 to 19. -/
theorem hi_fit {j : Nat} (hj9 : 9 ≤ j) (hj : j ≤ 19) :
    lo len (.slot .wide 9) ≤ lo len (.slot .wide j) ∧
      lo len (.slot .wide j) + st len .wide ≤ lo len (.slot .wide 20) := by
  have e : lo len (.slot .wide j) = numBase + j * st len .wide := rfl
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) hj9
  have := Nat.mul_le_mul_right (st len .wide) (show j + 1 ≤ 20 by omega_using [hj])
  rw [Nat.succ_mul] at this
  omega_arith

/-- The operations of a context keep the wide slots 9 to 19 and the header's words from 8 on. -/
theorem opsKeep (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (stR len 0)) m m') (R : CallRoom sp base bytes) {d k : Nat}
    (hd : (lo len (.slot .wide 9) ≤ d ∧ d + 4 * k ≤ lo len (.slot .wide 20)) ∨ (8 ≤ d ∧ d + 4 * k ≤ numBase)) :
    val32 m' base d k = val32 m base d k := by
  have T := h.table_fit .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  have t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega_using []
  refine frameR_val32 F R h.scratch.nowrap (by omega_using [hd, T, e20, t0, t16]) ?_ (stR_fit h (by decide))
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem opsKeepF (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameF base sp (stR len 0)) m m') (R : RoomF sp base bytes) {d k : Nat}
    (hd : (lo len (.slot .wide 9) ≤ d ∧ d + 4 * k ≤ lo len (.slot .wide 20)) ∨ (8 ≤ d ∧ d + 4 * k ≤ numBase)) :
    val32 m' base d k = val32 m base d k := by
  have T := h.table_fit .wide
  have e9 : lo len (.slot .wide 9) = numBase + 9 * st len .wide := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have t0 : te len .wide 0 = lo len (.slot .wide 20) := by simp [te]
  have z0 : lo len (.slot .wide 0) = numBase := sl_zero len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  have t16 : te len .wide 16 = te len .wide 0 + 16 * bc len .wide := by simp only [te]; omega_using []
  refine frameF_val32 F R h.scratch.nowrap (by omega_using [hd, T, e20, t0, t16]) ?_ (stR_fit h (by decide))
  intro q hq
  simp only [stR, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- The value of a wide slot from 9 to 19 after the operations of a context. -/
theorem opsKeep_sv (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (stR len 0)) m m') (R : CallRoom sp base bytes) {j : Nat} (hj9 : 9 ≤ j)
    (hj : j ≤ 19) : sv m' base len .wide j = sv m base len .wide j := by
  have := hi_fit (len := len) hj9 hj
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  exact opsKeep h F R (.inl ⟨this.1, by omega_using [this, bw, est]⟩)

/-- A header word from 8 on after the operations of a context. -/
theorem opsKeep_w32 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (stR len 0)) m m') (R : CallRoom sp base bytes) {d : Nat} (hd : 8 ≤ d)
    (hd' : d + 4 ≤ numBase) : w32 m' base d = w32 m base d := by
  rw [← w32_val32_one, ← w32_val32_one]
  exact opsKeep h F R (.inr ⟨hd, by omega_using [hd']⟩)

/-- A number written into one wide slot keeps another. -/
theorem slotKeep (h : In Ex base bytes len args s) {m m' : Mem} {a b : Nat} (hb : b ≤ 19)
    (hab : a ≠ b) (O : Outside base (lo len (.slot .wide a)) (bc len .wide) m m') :
    sv m' base len .wide b = sv m base len .wide b := by
  have bw := bc_eq_cwc len .wide
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  exact wide_keep h hb hab (by omega_using [est]) (by omega_using [bw, est]) O

/-- A number written into a wide slot keeps the header. -/
theorem slotKeep_w32 (h : In Ex base bytes len args s) {m m' : Mem} {a d : Nat}
    (O : Outside base (lo len (.slot .wide a)) (bc len .wide) m m') (hd : d + 4 ≤ numBase) :
    w32 m' base d = w32 m base d := by
  have e : lo len (.slot .wide a) = numBase + a * st len .wide := rfl
  have nb : numBase = 3336 := rfl
  have bl := h.bytes_lt
  exact O.w32 (.inl (by omega_using [hd, e])) (by omega_using [hd, nb])

/-- A wide slot written, within `fR`. -/
theorem slot_inF {a n : Nat} (ha : a ≤ 27) (hn : n ≤ st len .wide) :
    InF len (lo len (.slot .wide a), n) := by
  have e : lo len (.slot .wide a) = numBase + a * st len .wide := rfl
  have := Nat.mul_le_mul_right (st len .wide) (show a + 1 ≤ 28 by omega_using [ha])
  rw [Nat.succ_mul] at this
  have nb : numBase = 3336 := rfl
  have en : CrtRt.need len = numBase + 28 * st len .wide := rfl
  exact .inr ⟨by omega, by omega⟩

end VG.Proof.Ffdh.X86
