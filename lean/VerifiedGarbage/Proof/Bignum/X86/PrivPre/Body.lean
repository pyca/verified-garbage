module

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.ABI
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.AllocFrame
public import VerifiedGarbage.Proof.Framework.X86.Wp
public import VerifiedGarbage.Impl.Bignum.X86.PrivPre
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `vg_rsa_private_precompute` on x86: the state of its body

From the entry state `s`, the body runs with `esp` at its frame of 96 bytes
and changes memory only in `pre`, the working space and the `stackBytes`
bytes below the entry's `esp` (`Body`). Every address on the stack is an
offset of `bot s`, the lowest of those bytes: the callees' stack and return
address below 100, the frame from 100, the return address at 196 and the
arguments from 200.
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Proof.Dsa.X86 (argumentPointer)
open VG.Impl.Bignum.X86.PrivPre (stackAt incoming)

/-- The lowest byte of the stack the function uses. -/
abbrev bot (s : State) : Addr := (s.gpr .esp).setWidth 64 - BitVec.ofNat 64 stackBytes
abbrev preR (s : State) : Region := ⟨argumentPointer s 0, (arg s 1).toNat * 8⟩
abbrev wsR (s : State) : Region := ⟨argumentPointer s 8, (arg s 9).toNat * 8⟩
abbrev topR (s : State) : Region := ⟨bot s, stackBytes⟩
/-- The regions the body writes. -/
abbrev bodyW (s : State) : List Region := [preR s, wsR s, topR s]

/-- The address `d` bytes into the frame. -/
abbrev slot (s : State) (d : Nat) : Addr := bot s + BitVec.ofNat 64 (100 + d)

/-- The frame's region, as `allocFrame` adds it. -/
abbrev frameR (s : State) : Region :=
  ⟨(s.gpr .esp - BitVec.ofNat 32 Impl.Bignum.X86.PrivPre.frameBytes).setWidth 64, Impl.Bignum.X86.PrivPre.frameBytes⟩

structure Body (s t : State) : Prop where
  sp : t.gpr .esp = s.gpr .esp - BitVec.ofNat 32 Impl.Bignum.X86.PrivPre.frameBytes
  rd : t.rd = s.rd
  wr : t.wr = frameR s :: s.wr
  frame : Frame (bodyW s) s.mem t.mem

section
variable {s t : State}

theorem bot_toNat (A : PPABI s) : (bot s).toNat = (s.gpr .esp).toNat - 196 := by
  have l := A.stackLow
  simp only [stackBytes] at l
  rw [bot, stackBytes, ← VG.X86.Taint.sub_setWidth l, BitVec.toNat_setWidth, sub_toNat l,
    Nat.mod_eq_of_lt (by have := (s.gpr .esp).isLt; omega)]

theorem esp_off (A : PPABI s) {a b : Nat} (ha : a ≤ 196) (hb : b ≤ a + 40) :
    ((s.gpr .esp - BitVec.ofNat 32 a) + BitVec.ofNat 32 b).setWidth 64 =
      bot s + BitVec.ofNat 64 (196 - a + b) := by
  have l := A.stackLow
  have u := A.stackBound
  simp only [stackBytes] at l
  have x := (s.gpr .esp).isLt
  have e1 : (s.gpr .esp - BitVec.ofNat 32 a).toNat = (s.gpr .esp).toNat - a := sub_toNat (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, e1, BitVec.toNat_add, bot_toNat A, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := b) (by omega), Nat.mod_eq_of_lt (a := 196 - a + b) (by omega),
    Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat - a + b) (by omega),
    Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat - a + b) (by omega),
    Nat.mod_eq_of_lt (a := (s.gpr .esp).toNat - 196 + (196 - a + b)) (by omega)]
  omega

theorem frame_base (A : PPABI s) : frameR s = ⟨bot s + BitVec.ofNat 64 100, 96⟩ := by
  have := esp_off A (a := 96) (b := 0) (by decide) (by decide)
  simp only [BitVec.add_zero] at this
  simp only [frameR, Impl.Bignum.X86.PrivPre.frameBytes, Region.mk.injEq, and_true]
  exact this

theorem esp_bot (A : PPABI s) : (s.gpr .esp).setWidth 64 = bot s + BitVec.ofNat 64 196 := by
  have := esp_off A (a := 0) (b := 0) (by decide) (by decide)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero, BitVec.add_zero] using this

theorem argAddr_bot (A : PPABI s) {i : Nat} (hi : i < 10) :
    argAddr s i = bot s + BitVec.ofNat 64 (200 + 4 * i) := by
  have := esp_off A (a := 0) (b := 4 + 4 * i) (by decide) (by omega)
  simp only [BitVec.sub_zero] at this
  rw [argAddr, this]
  congr 2; omega

theorem slot_ea (A : PPABI s) (B : Body s t) {d : Nat} (hd : d < 96) : t.ea (stackAt d) = slot s d := by
  simp only [State.ea, stackAt, B.sp, Impl.Bignum.X86.PrivPre.frameBytes]
  rw [esp_off A (by decide) (by omega)]

theorem incoming_ea (A : PPABI s) (B : Body s t) {i : Nat} (hi : i < 10) : t.ea (incoming i) = argAddr s i := by
  simp only [State.ea, incoming, stackAt, B.sp, Impl.Bignum.X86.PrivPre.frameBytes]
  rw [esp_off A (by decide) (by omega), argAddr_bot A hi]
  congr 2; omega

theorem Body.start : Body s (allocFrame Impl.Bignum.X86.PrivPre.frameBytes s) :=
  ⟨allocFrame_esp _ _, rfl, rfl, Frame.refl _ _⟩

theorem Body.next {u : State} (B : Body s t) (sp : u.gpr .esp = t.gpr .esp) (rd : u.rd = t.rd)
    (wr : u.wr = t.wr) (F : Frame (bodyW s) t.mem u.mem) : Body s u :=
  ⟨sp.trans B.sp, rd.trans B.rd, wr.trans B.wr, B.frame.trans F⟩

/-- The arguments' region lies apart from what the body writes. -/
theorem args_apart (A : PPABI s) : ∀ r ∈ bodyW s, (⟨argAddr s 0, 40⟩ : Region).Disjoint r := by
  intro r hr
  simp only [bodyW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact A.preArgs.symm
  · exact A.wsArgs.symm
  · have := A.belowArgs.symm
    simpa only [topR, bot] using this

theorem Body.argValue (A : PPABI s) (B : Body s t) {i : Nat} (hi : i < 10) :
    t.mem.readW (argAddr s i) 32 = arg s i := by
  refine B.frame.readW (r := ⟨argAddr s 0, 40⟩) ?_ (args_apart A) (by decide)
  rw [argAddr_bot A hi, argAddr_bot A (by decide : 0 < 10)]
  exact Offset.contains _ (by omega) (by omega) (by omega)

theorem Body.readArg (A : PPABI s) (B : Body s t) {i : Nat} (hi : i < 10) :
    readSrc t (.mem (incoming i)) = some (arg s i) := by
  show t.load32 (t.ea (incoming i)) = _
  rw [incoming_ea A B hi]
  have hin : InRegions (t.rd ++ t.wr) (argAddr s i) 4 := by
    refine ⟨⟨argAddr s 0, 40⟩, ?_, ?_⟩
    · rw [B.wr, A.wr]; simp
    · rw [argAddr_bot A hi, argAddr_bot A (by decide : 0 < 10)]
      exact Offset.contains _ (by omega) (by omega) (by omega)
  simp only [State.load32, hin, ite_true, B.argValue A hi]

/-- `mov [esp + d], r` in the frame. -/
theorem wp_slot {is : List Instr} {Q : State → Prop} {r : Reg} (A : PPABI s) (B : Body s t) {d : Nat}
    (hd : d + 4 ≤ 96)
    (k : ∀ u, Body s u → Mupd t u (t.mem.writeW (slot s d) (t.gpr r)) → WP isa (.block is) u Q) :
    WP isa (.block (.store (stackAt d) r :: is)) t Q := by
  have hw : InRegions t.wr (slot s d) 4 := by
    refine ⟨frameR s, by rw [B.wr]; exact List.mem_cons_self .., ?_⟩
    rw [frame_base A]
    exact Offset.contains _ (by omega) (by omega) (by omega)
  refine wp_storeS (slot_ea A B (by omega)) hw fun u M => k u ?_ M
  refine B.next (by rw [M.gpr]) M.rd M.wr ?_
  rw [M.mem]
  refine (Frame.refl _ _).writeW (r := topR s) (by simp) _ ?_
  exact Offset.contains_base _ (by simp only [stackBytes]; omega) (by omega)

end
end VG.Proof.Bignum.X86.PrivPre
