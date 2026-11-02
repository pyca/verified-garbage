module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyRuntime
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Workspace
public import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Entry
public import VerifiedGarbage.Proof.Rsa.X86.InvLoop
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Framework.X86.CallWith
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.StackRange
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyInverseFrame

import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Verified
import VerifiedGarbage.Proof.RsaKeyGen.X86.Inverse.Framed
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Mont.Halve32
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.Address
import VerifiedGarbage.Proof.Framework.Covers
public import VerifiedGarbage.Proof.RsaKeyGen.Contract
/-! # The key's calls of `vg_rsa_keygen_inverse`, at the width of each inversion -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/Inverse/Post.lean`, which only this module imported.
section

/-! # What `vg_rsa_keygen_inverse`'s postcondition tells its caller -/

section
namespace VG.Proof.RsaKeyGen.X86.Inverse
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (kw)
open VG.Proof.Rsa.X86.Keys (num)

theorem post_of {s t : State} (post : contract.post s t) :
    (∀ i, i < size s → ¬ Proof.RsaKeyGen.inverseWrites (len s) i →
      t.mem (base s + BitVec.ofNat 64 i) = s.mem (base s + BitVec.ofNat 64 i)) ∧
    num t.mem (base s) (kw (len s)) 1 =
      Nat.gcd (num s.mem (base s) (kw (len s)) 0) (num s.mem (base s) (kw (len s)) 8) ∧
    (num s.mem (base s) (kw (len s)) 8 : Int) ∣
      (num t.mem (base s) (kw (len s)) 3 : Int) * num s.mem (base s) (kw (len s)) 0 -
        num t.mem (base s) (kw (len s)) 1 ∧
    num t.mem (base s) (kw (len s)) 3 < num s.mem (base s) (kw (len s)) 8 := by
  sig_post [contract, inverseStack, Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig,
    abi, argSlots, argVal, argBytes] at post
  simp only [← inverseNum_num]
  exact post

end VG.Proof.RsaKeyGen.X86.Inverse
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Rsa.X86.KeyRt (RtWs kw)
open VG.Proof.Rsa.X86.Keys (Keep num invArrs invSlots)
open VG.Impl.Rsa.X86.Keys (aM aNM aZero)
open VG.Impl.RsaKeyGen.X86.KeyRuntime

def invArgs : List Reg := [.eax, .ecx, .edi]

/-- The callee's view: its arguments, and the working space it may write. -/
def invEntry (B : Addr) (L : Nat) (s : State) : State :=
  (pushed invArgs s).callEntry.withRegions [⟨argAddr (pushed invArgs s).callEntry 0, 12⟩] [⟨B, L⟩]

structure InvArguments (B : Addr) (len words : Nat) (s : State) : Prop where
  base : s.gpr .edi = BitVec.ofNat 32 B.toNat
  wsLen : s.gpr .ecx = BitVec.ofNat 32 words
  length : s.gpr .eax = BitVec.ofNat 32 len

theorem invEntry_arg {B : Addr} {L len words : Nat} {s : State}
    (A : InvArguments B len words s) (fit : 16 ≤ (s.gpr .esp).toNat) {i : Nat} (index : i < 3) :
    arg (invEntry B L s) i = BitVec.ofNat 32 (if i = 0 then B.toNat else if i = 1 then words else len) := by
  rw [invEntry, arg_withRegions, callEntry_arg (rs := invArgs) (s := s) fit (by decide : Reg.esp ∉ invArgs) index]
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases casesI with rfl | rfl | rfl <;>
    simp only [invArgs, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      List.getElem_cons_zero, List.getElem_cons_succ, ↓reduceIte, A.base, A.wsLen, A.length] <;> rfl

theorem invEntry_frame {B : Addr} {L : Nat} {s : State} (fit : 16 ≤ (s.gpr .esp).toNat) :
    Frame [below (s.gpr .esp) 16] s.mem (invEntry B L s).mem :=
  callEntry_frame (rs := invArgs) fit (by decide : Reg.esp ∉ invArgs)

/-- A frame below the stack pointer, apart from the workspace, leaves its numbers. -/
theorem frame_num {m m' : Mem} {B : Addr} {Z w j : Nat} {r : Region}
    (F : Frame [r] m m') (far : (⟨B, Z⟩ : Region).Disjoint r) (nowrap : B.toNat + Z ≤ 2 ^ 32)
    (fit : VG.Proof.Rsa.X86.Keys.arr w j + VG.Proof.Rsa.X86.Keys.S w ≤ Z) :
    num m' B w j = num m B w j := by
  apply val32_congr_at
  intro i hi
  unfold w32
  congr 1
  apply F.readW (r := ⟨B, Z⟩) _ (by intro r' hr; obtain rfl := List.mem_singleton.mp hr; exact far) (by decide)
  unfold VG.Proof.Rsa.X86.Keys.S at fit
  exact Offset.contains_base _ (by omega) (by omega)

theorem invEntry_pre {s : State} {B : Addr} {Z a words : Nat}
    (A : InvArguments B a words s) (nowrap : B.toNat + Z ≤ 2 ^ 32)
    (lenLow : 1 ≤ a) (lenHigh : a ≤ 1024) (wordsEq : words = 35 + 15 * ((a + 7) / 8))
    (fits : VG.Proof.Rsa.X86.Keys.arr (kw a) 15 ≤ Z)
    (fit : 52 ≤ (s.gpr .esp).toNat) (far : (⟨B, Z⟩ : Region).Disjoint (below (s.gpr .esp) 52))
    (odd : num s.mem B (kw a) aM % 2 = 1) (large : 1 < num s.mem B (kw a) aM)
    (v : num s.mem B (kw a) 1 = num s.mem B (kw a) aM) (x₁ : num s.mem B (kw a) 2 = 1)
    (x₂ : num s.mem B (kw a) 3 = 0)
    (negated : num s.mem B (kw a) aNM + num s.mem B (kw a) aM = 2 ^ (32 * kw a))
    (zero : num s.mem B (kw a) aZero = 0) :
    VG.Proof.RsaKeyGen.X86.Inverse.contract.pre (invEntry B (8 * words) s) := by
  have sa := fun {i} (hi : i < 3) => invEntry_arg (L := 8 * words) A (by omega) hi
  have ptrBound : B.toNat < 2 ^ 32 := by
    have : 0 < Z := by unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at fits; omega
    omega
  have wordsBound : words < 2 ^ 32 := by omega
  have aBound : a < 2 ^ 32 := by omega
  have sp : (invEntry B (8 * words) s).gpr .esp = s.gpr .esp - 16#32 := by
    change (pushed invArgs s).callEntry.gpr .esp = _
    exact callEntry_esp' invArgs s
  have ar : argAddr (invEntry B (8 * words) s) 0 = (s.gpr .esp - 12#32).setWidth 64 := by
    rw [invEntry, argAddr_withRegions]
    exact callEntry_argAddr0 invArgs s
  have rd : (invEntry B (8 * words) s).rd = [⟨argAddr (invEntry B (8 * words) s) 0, 12⟩] := by
    rw [invEntry, State.withRegions_rd, argAddr_withRegions]
  have wr : (invEntry B (8 * words) s).wr = [⟨B, 8 * words⟩] := rfl
  have sa0 : arg (invEntry B (8 * words) s) 0 = BitVec.ofNat 32 B.toNat := sa (by decide)
  have sa1 : arg (invEntry B (8 * words) s) 1 = BitVec.ofNat 32 words := sa (by decide)
  have sa2 : arg (invEntry B (8 * words) s) 2 = BitVec.ofNat 32 a := sa (by decide)
  have ptr : (BitVec.ofNat 32 B.toNat).setWidth 64 = B := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt B.isLt
  have F := invEntry_frame (B := B) (L := 8 * words) (s := s) (by omega)
  generalize eu : invEntry B (8 * words) s = u at *
  sig_pre [VG.Proof.RsaKeyGen.X86.Inverse.contract, VG.Proof.RsaKeyGen.X86.Inverse.inverseStack,
    Proof.RsaKeyGen.inverseContract, Proof.RsaKeyGen.inverseSig, abi, argSlots, argVal, argBytes, stackBelow]
  simp only [sa0, sa1, sa2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordsBound, Nat.mod_eq_of_lt ptrBound,
    Nat.mod_eq_of_lt aBound, ptr, rd, wr, sp, ar]
  have espBound := (s.gpr .esp).isLt
  have e16 : (s.gpr .esp - 16#32).toNat = (s.gpr .esp).toNat - 16 := sub_toNat (by omega)
  have nat12 : ((s.gpr .esp - 12#32).setWidth 64).toNat = (s.gpr .esp).toNat - 12 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have nat16 : ((s.gpr .esp - 16#32).setWidth 64).toNat = (s.gpr .esp).toNat - 16 := by
    rw [BitVec.toNat_setWidth, e16]
    exact Nat.mod_eq_of_lt (by omega)
  have reserved : (s.gpr .esp - 16#32).setWidth 64 - 36#64 = (s.gpr .esp - 52#32).setWidth 64 := by
    rw [← Taint.sub_setWidth (by rw [e16]; omega : 36 ≤ (s.gpr .esp - 16#32).toNat)]
    congr 1
    rw [BitVec.sub_sub]
    rfl
  have nat52 : ((s.gpr .esp - 52#32).setWidth 64).toNat = (s.gpr .esp).toNat - 52 := by
    rw [BitVec.toNat_setWidth, sub_toNat fit]
    exact Nat.mod_eq_of_lt (by omega)
  have size : words * 8 ≤ Z := by
    unfold VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S VG.Impl.Rsa.X86.Keys.hdr at fits
    simp only [kw, Spec.Rsa.modulusWords] at fits
    omega
  have wsSub : (⟨B, words * 8⟩ : Region).Sub ⟨B, Z⟩ := Region.sub_prefix size
  have argSub : (⟨(s.gpr .esp - 12#32).setWidth 64, 12⟩ : Region).Sub (below (s.gpr .esp) 52) :=
    below_sub (by decide) fit
  have retSub : (⟨(s.gpr .esp - 16#32).setWidth 64, 4⟩ : Region).Sub (below (s.gpr .esp) 52) :=
    fun x hx => below_sub (by decide : 16 ≤ 52) fit x ((Region.sub_prefix (by decide : 4 ≤ 16)) x hx)
  have resSub : (⟨(s.gpr .esp - 16#32).setWidth 64 - 36#64, 36⟩ : Region).Sub (below (s.gpr .esp) 52) := by
    rw [reserved]
    exact Region.sub_prefix (by decide : 36 ≤ 52)
  have ws := far.sub_left wsSub
  have frameFar : (⟨B, Z⟩ : Region).Disjoint (below (s.gpr .esp) 16) := far.sub_right (below_sub (by decide) fit)
  have arrFit {j : Nat} (hj : j < 15) :
      VG.Proof.Rsa.X86.Keys.arr (kw a) j + VG.Proof.Rsa.X86.Keys.S (kw a) ≤ Z :=
    Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_end hj) fits
  have value {j : Nat} (hj : j < 15) : Proof.RsaKeyGen.inverseNum u.mem B a j = num s.mem B (kw a) j := by
    rw [VG.Proof.RsaKeyGen.X86.Inverse.inverseNum_num]
    exact frame_num F frameFar nowrap (arrFit hj)
  refine ⟨by rw [e16]; omega, by rw [e16]; omega, trivial, by rw [Nat.mul_comm], ws.sub_right argSub,
    (ws.sub_right retSub).symm,
    Offset.disjoint_of_le (by simp only [nat16, nat12]; omega) (by simp only [nat12]; omega),
    (ws.sub_right resSub).symm,
    by rw [reserved]; exact Offset.disjoint_of_le (by simp only [nat52, nat12]; omega) (by simp only [nat12]; omega),
    by omega, lenLow, lenHigh, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Proof.RsaKeyGen.inverseBytes; omega
  · rw [value (by decide)]; exact odd
  · rw [value (by decide)]; exact large
  · rw [value (by decide), value (by decide)]; exact v
  · rw [value (by decide)]; exact x₁
  · rw [value (by decide)]; exact x₂
  · rw [value (by decide), value (by decide)]
    unfold aNM aM at negated
    rw [negated]
    simp only [kw, Spec.Rsa.modulusWords, Proof.RsaKeyGen.inverseBytes]
    congr 1; omega
  · rw [value (by decide)]; exact zero

/-- The arguments' block: `eax` the length argument, `ecx` the words of working space the callee
uses, `35 + 15 ⌈a / 8⌉`. -/
theorem callSetup_ok {s : State} {L : VG.Impl.Rsa.X86.KeyRt.Lay} {a : Nat} {Q : State → Prop}
    (src : readSrc s (.mem (VG.Impl.Rsa.X86.KeyRt.argOp L.len)) = some (BitVec.ofNat 32 a)) (ha : a ≤ 1024)
    (k : ∀ u, Keeps [.eax, .ecx, .edx] s u → u.mem = s.mem → u.gpr .eax = BitVec.ofNat 32 a →
      u.gpr .ecx = BitVec.ofNat 32 (35 + 15 * ((a + 7) / 8)) → Q u) :
    WP isa (.block [.mov .eax (.mem (VG.Impl.Rsa.X86.KeyRt.argOp L.len)), .mov .ecx (.reg .eax),
      .alu .add .ecx (.imm 7), .shift .shr .ecx 3, .mov .edx (.reg .ecx), .alu .add .ecx (.reg .ecx),
      .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
      .alu .sub .ecx (.reg .edx), .alu .add .ecx (.imm 35)]) s Q := by
  refine wp_movS src fun u₁ U₁ _ => wp_movS rfl fun u₂ U₂ _ => wp_addS rfl fun u₃ U₃ _ =>
    wp_shr ⟨by decide, by decide⟩ fun u₄ U₄ _ => wp_movS rfl fun u₅ U₅ _ => wp_addS rfl fun u₆ U₆ _ =>
    wp_addS rfl fun u₇ U₇ _ => wp_addS rfl fun u₈ U₈ _ => wp_addS rfl fun u₉ U₉ _ =>
    wp_subS rfl fun u₁₀ U₁₀ _ => wp_addS rfl fun u₁₁ U₁₁ _ => WP.block_nil ?_
  have aBound : a < 2 ^ 32 := by omega
  have e₂ : (u₂.gpr .ecx).toNat = a := by
    rw [U₂.gpr, U₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt aBound]
  have e₃ : (u₃.gpr .ecx).toNat = a + 7 := by
    rw [U₃.gpr, BitVec.toNat_add, e₂]
    exact Nat.mod_eq_of_lt (by change a + 7 < 2 ^ 32; omega)
  have e₄ : (u₄.gpr .ecx).toNat = (a + 7) / 8 := by
    rw [U₄.gpr, BitVec.toNat_ushiftRight, e₃, Nat.shiftRight_eq_div_pow]
  have d₅ : (u₅.gpr .edx).toNat = (a + 7) / 8 := by rw [U₅.gpr]; exact e₄
  have e₅ : (u₅.gpr .ecx).toNat = (a + 7) / 8 := by rw [U₅.other _ (by decide)]; exact e₄
  have e₆ : (u₆.gpr .ecx).toNat = 2 * ((a + 7) / 8) := by
    rw [U₆.gpr, BitVec.toNat_add, e₅]; omega
  have e₇ : (u₇.gpr .ecx).toNat = 4 * ((a + 7) / 8) := by
    rw [U₇.gpr, BitVec.toNat_add, e₆]; omega
  have e₈ : (u₈.gpr .ecx).toNat = 8 * ((a + 7) / 8) := by
    rw [U₈.gpr, BitVec.toNat_add, e₇]; omega
  have e₉ : (u₉.gpr .ecx).toNat = 16 * ((a + 7) / 8) := by
    rw [U₉.gpr, BitVec.toNat_add, e₈]; omega
  have d₉ : (u₉.gpr .edx).toNat = (a + 7) / 8 := by
    rw [U₉.other _ (by decide), U₈.other _ (by decide), U₇.other _ (by decide), U₆.other _ (by decide)]
    exact d₅
  have e₁₀ : (u₁₀.gpr .ecx).toNat = 15 * ((a + 7) / 8) := by
    rw [U₁₀.gpr, BitVec.toNat_sub, e₉, d₉]; omega
  have e₁₁ : (u₁₁.gpr .ecx).toNat = 35 + 15 * ((a + 7) / 8) := by
    rw [U₁₁.gpr, BitVec.toNat_add, e₁₀]
    exact (Nat.mod_eq_of_lt (by change 15 * ((a + 7) / 8) + 35 < 2 ^ 32; omega)).trans (Nat.add_comm _ _)
  have K : Keeps [.eax, .ecx, .edx] s u₁₁ :=
    (U₁.keeps.mono (by decide)).trans ((U₂.keeps.mono (by decide)).trans ((U₃.keeps.mono (by decide)).trans
      ((U₄.keeps.mono (by decide)).trans ((U₅.keeps.mono (by decide)).trans ((U₆.keeps.mono (by decide)).trans
      ((U₇.keeps.mono (by decide)).trans ((U₈.keeps.mono (by decide)).trans ((U₉.keeps.mono (by decide)).trans
      ((U₁₀.keeps.mono (by decide)).trans (U₁₁.keeps.mono (by decide)))))))))))
  refine k u₁₁ K ?_ ?_ ?_
  · rw [U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem, U₇.mem, U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  · rw [U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide),
      U₇.other _ (by decide), U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr]
  · apply BitVec.eq_of_toNat_eq
    rw [e₁₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem code_noSp : NoSp VG.Impl.RsaKeyGen.X86.Inverse.code := by
  intro i hi
  have e : instrs VG.Impl.RsaKeyGen.X86.Inverse.code = .push [.ebx, .ebp, .esi, .edi] ::
      (instrs (.seq (.block (VG.Impl.Rsa.X86.KeyRt.restoreEdi VG.Impl.RsaKeyGen.X86.Inverse.lay))
        (.seq (VG.Impl.Rsa.X86.KeyRt.inverse VG.Impl.RsaKeyGen.X86.Inverse.lay)
          (.block VG.Impl.Mont.X86.Compact.restoreRegs))) ++ [.pop .ebx 4]) := rfl
  rw [e] at hi
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | hi | rfl
  · rfl
  · exact VG.Proof.RsaKeyGen.X86.Inverse.inner_noSp i hi
  · rfl

theorem code_stack : stackUse VG.Impl.RsaKeyGen.X86.Inverse.code = 16 := rfl

/-- The bytes the callee may write lie in the ranges an inversion's frame names. -/
theorem writes_ranges {a W i : Nat} (hka : kw a = W) (hw : Proof.RsaKeyGen.inverseWrites a i) :
    ¬ ∀ r ∈ VG.Proof.RsaKeyGen.X86.Key.inverseRanges W invSlots, i < r.1 ∨ r.1 + r.2 ≤ i := by
  intro out
  simp only [VG.Proof.RsaKeyGen.X86.Key.inverseRanges, invSlots, VG.Impl.Rsa.X86.Keys.sOdd,
    VG.Impl.Rsa.X86.Keys.sB, VG.Impl.Rsa.X86.Keys.sC, VG.Impl.Rsa.X86.Keys.hdr, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at out
  simp only [kw, Spec.Rsa.modulusWords] at hka
  unfold Proof.RsaKeyGen.inverseWrites Proof.RsaKeyGen.inverseBytes at hw
  rcases hw with ⟨lo, hi⟩ | ⟨j, hj, lo, hi⟩
  · omega
  · have le := Nat.mul_le_mul_right (8 * ((a + 7) / 8) + 8) (show j + 1 ≤ 15 by omega)
    have := out.1
    omega

/-- What a call of the inverse needs of the state it is made from. -/
structure InvReady (B : Addr) (Z n N : Nat) (w : Width) (s : State) : Prop where
  ws : Ws s B Z n N
  bound : 15 ≤ N
  width : w ≠ .correction
  odd : num s.mem B (w.words n) aM % 2 = 1
  large : 1 < num s.mem B (w.words n) aM
  v : num s.mem B (w.words n) 1 = num s.mem B (w.words n) aM
  x₁ : num s.mem B (w.words n) 2 = 1
  x₂ : num s.mem B (w.words n) 3 = 0
  negated : num s.mem B (w.words n) aNM + num s.mem B (w.words n) aM = 2 ^ (32 * w.words n)
  zero : num s.mem B (w.words n) aZero = 0

/-- The words of working space the callee uses, for a length argument `a`. -/
abbrev invWords (a : Nat) : Nat := 35 + 15 * ((a + 7) / 8)

/-- The state the arguments' block leaves: `esp` is `p`, and the length argument `a`. -/
structure CallAt (B : Addr) (Z n N : Nat) (w : Width) (p : BitVec 32) (a : Nat) (u : State) : Prop where
  ready : InvReady B Z n N w u
  sp : u.gpr .esp = p
  len : a ≤ 1024
  words : kw a = w.words n
  eax : u.gpr .eax = BitVec.ofNat 32 a
  ecx : u.gpr .ecx = BitVec.ofNat 32 (invWords a)

theorem InvReady.keep {B : Addr} {Z n N : Nat} {w : Width} {s u : State} {rs : List Reg}
    (R : InvReady B Z n N w s) (K : Keeps rs s u) (mem : u.mem = s.mem)
    (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : InvReady B Z n N w u := by
  exact ⟨R.ws.keep K (fun x _ => congrFun mem x) edi esp, R.bound, R.width, by rw [mem]; exact R.odd,
    by rw [mem]; exact R.large, by rw [mem]; exact R.v, by rw [mem]; exact R.x₁, by rw [mem]; exact R.x₂,
    by rw [mem]; exact R.negated, by rw [mem]; exact R.zero⟩

theorem args_ok {B : Addr} {Z n N : Nat} {w : Width} {s : State} (R : InvReady B Z n N w s) :
    WP isa (.block (inverseArgs w)) s fun u =>
      ∃ a, CallAt B Z n N w (s.gpr .esp) a u ∧ Keeps [.eax, .ecx, .edx] s u ∧ u.mem = s.mem := by
  have Hw := shrinkRt (R.ws.runtime R.width) R.bound
  obtain ⟨a, ha, hka, LA⟩ := Hw.lenArg
  have toLen : w.lay.toLen a = a := by cases w <;> rfl
  rw [toLen, kw_words R.ws.width] at hka
  exact callSetup_ok (L := w.lay) LA.readSrc ha fun u Ku mu eax ecx =>
    ⟨a, ⟨R.keep Ku mu, Ku.1 .esp (by decide), ha, hka, eax, ecx⟩, Ku, mu⟩

theorem CallAt.fits {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) : VG.Proof.Rsa.X86.Keys.arr (kw a) 15 ≤ Z := by
  have Hw := shrinkRt (C.ready.ws.runtime C.ready.width) C.ready.bound
  have := Hw.ws.fits
  rwa [kw_words C.ready.ws.width, ← C.words] at this

theorem CallAt.size {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) : 8 * invWords a ≤ Z := by
  have fits := C.fits
  unfold VG.Proof.Rsa.X86.Keys.arr VG.Proof.Rsa.X86.Keys.S VG.Impl.Rsa.X86.Keys.hdr at fits
  simp only [kw, Spec.Rsa.modulusWords] at fits
  unfold invWords
  omega

theorem CallAt.ptrBound {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) : B.toNat < 2 ^ 32 := by
  have := C.fits
  have := C.ready.ws.old.workspace.nowrap
  unfold VG.Proof.Rsa.X86.Keys.arr VG.Impl.Rsa.X86.Keys.hdr at *
  omega

theorem CallAt.lenLow {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) : 1 ≤ a := by
  have Hw := shrinkRt (C.ready.ws.runtime C.ready.width) C.ready.bound
  have wpos : 0 < kw a := by
    rw [C.words]
    have := Hw.ws.wpos
    rwa [kw_words C.ready.ws.width] at this
  by_contra c
  rw [show a = 0 by omega] at wpos
  exact absurd wpos (by decide)

theorem CallAt.args {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) : InvArguments B a (invWords a) u := by
  refine ⟨?_, C.ecx, C.eax⟩
  apply BitVec.eq_of_toNat_eq
  rw [C.ready.ws.old.workspace.edi_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt C.ptrBound]

theorem CallAt.entry_eq {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) :
    (pushed invArgs u).callEntry.withRegions [⟨(below p 12).base, 12⟩] [⟨B, 8 * invWords a⟩] =
      invEntry B (8 * invWords a) u := by
  unfold invEntry
  rw [callEntry_argAddr0, C.sp]
  rfl

theorem CallAt.callPre {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) :
    CallPre VG.Proof.RsaKeyGen.X86.Inverse.contract invArgs [⟨(below p 12).base, 12⟩]
      [⟨B, 8 * invWords a⟩] u := by
  have R := C.ready
  have nowrap := R.ws.old.workspace.nowrap
  have D := R.ws.deep
  have lowSp : 52 ≤ (u.gpr .esp).toNat := D.1
  have pre := invEntry_pre C.args nowrap C.lenLow C.len rfl C.fits lowSp (deep_disjoint D nowrap)
    (by rw [C.words]; exact R.odd) (by rw [C.words]; exact R.large) (by rw [C.words]; exact R.v)
    (by rw [C.words]; exact R.x₁) (by rw [C.words]; exact R.x₂) (by rw [C.words]; exact R.negated)
    (by rw [C.words]; exact R.zero)
  have size := C.size
  have wsIn : InRegions u.wr B (8 * invWords a) :=
    ⟨_, R.ws.old.workspace.wr, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  refine ⟨by rw [C.entry_eq]; exact pre, ?_, ?_⟩
  · apply Covers.append_left
    · apply Covers.of_mem
      intro r mem
      obtain rfl := List.mem_singleton.mp mem
      rw [← C.sp]
      exact List.mem_append_right _ List.mem_cons_self
    · exact Covers.one (by
        obtain ⟨r, hr, hc⟩ := wsIn
        exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ hr), hc⟩)
  · exact Covers.one (by
      obtain ⟨r, hr, hc⟩ := wsIn
      exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩)

theorem call_ok {B : Addr} {Z n N : Nat} {w : Width} {p : BitVec 32} {a : Nat} {u : State}
    (C : CallAt B Z n N w p a u) :
    WP isa inverseCall u fun t =>
      Ws t B Z n N ∧
      OutsS B p (VG.Proof.RsaKeyGen.X86.Key.inverseRanges (w.words n) invSlots) u.mem t.mem ∧
      num t.mem B (w.words n) 1 = Nat.gcd (num u.mem B (w.words n) 0) (num u.mem B (w.words n) aM) ∧
      (num u.mem B (w.words n) aM : Int) ∣
        (num t.mem B (w.words n) 3 : Int) * num u.mem B (w.words n) 0 - num t.mem B (w.words n) 1 ∧
      num t.mem B (w.words n) 3 < num u.mem B (w.words n) aM ∧
      Keeps [.eax, .ecx, .edx] u t ∧ Frame [⟨B, Z⟩, below p 52] u.mem t.mem := by
  have R := C.ready
  have h := R.ws
  have nowrap := h.old.workspace.nowrap
  have D := h.deep
  have far := deep_disjoint D nowrap
  have lowSp : 52 ≤ (u.gpr .esp).toNat := D.1
  have spU := C.sp
  have hka := C.words
  have ptrBound := C.ptrBound
  have size := C.size
  have wsW : VG.Proof.Rsa.X86.Keys.Ws u B Z (w.words n) 15 := by
    have := (shrinkRt (h.runtime R.width) R.bound).ws
    rwa [kw_words h.width] at this
  have A := C.args
  refine WP.callWith VG.Proof.RsaKeyGen.X86.Inverse.verified.1 code_noSp (by decide : invArgs ≠ [])
    (by decide : Reg.esp ∉ invArgs) (by rw [code_stack]; change 32 ≤ _; omega) C.callPre ?_
  intro t rdT wrT saved frame post
  obtain ⟨e₂, mem₂, post⟩ := post
  rw [C.entry_eq] at post
  obtain ⟨inside, gcd, bezout, lt⟩ := VG.Proof.RsaKeyGen.X86.Inverse.post_of post
  have fit16 : 16 ≤ (u.gpr .esp).toNat := by omega
  have wordsBound : invWords a < 2 ^ 32 := by have := C.len; omega
  have arg0 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 0) (by decide)
  have arg1 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 1) (by decide)
  have arg2 := invEntry_arg (L := 8 * invWords a) A fit16 (i := 2) (by decide)
  simp only [↓reduceIte, Nat.reduceEqDiff] at arg0 arg1 arg2
  have baseE : VG.Proof.RsaKeyGen.X86.Inverse.base (invEntry B (8 * invWords a) u) = B := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.base
    rw [arg0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ptrBound]
    exact Nat.mod_eq_of_lt B.isLt
  have sizeE : VG.Proof.RsaKeyGen.X86.Inverse.size (invEntry B (8 * invWords a) u) = 8 * invWords a := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.size
    rw [arg1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordsBound]
  have lenE : VG.Proof.RsaKeyGen.X86.Inverse.len (invEntry B (8 * invWords a) u) = a := by
    unfold VG.Proof.RsaKeyGen.X86.Inverse.len
    rw [arg2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := C.len; omega)]
  simp only [baseE, sizeE, lenE, hka, mem₂] at inside gcd bezout lt
  have FE := invEntry_frame (B := B) (L := 8 * invWords a) fit16
  have farU : (⟨B, Z⟩ : Region).Disjoint (below (u.gpr .esp) 16) :=
    far.sub_right (below_sub (by decide) lowSp)
  have entryNum {j : Nat} (hj : j < 15) :
      num (invEntry B (8 * invWords a) u).mem B (w.words n) j = num u.mem B (w.words n) j :=
    frame_num FE farU nowrap (Nat.le_trans (VG.Proof.Rsa.X86.Keys.arr_end hj) wsW.fits)
  rw [entryNum (j := 0) (by decide), entryNum (j := 8) (by decide)] at gcd bezout
  rw [entryNum (j := 8) (by decide)] at lt
  have Kt : Keeps [.eax, .ecx, .edx] u t := by
    refine ⟨?_, rdT, wrT⟩
    intro r hr
    apply saved r
    cases r <;> simp [calleeSaved] at hr ⊢
  have stackFrame : Frame [⟨B, Z⟩, below p 52] u.mem t.mem := by
    refine frame.sub fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix size⟩
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      rw [code_stack, ← spU]
      exact below_sub (by decide) lowSp
  refine ⟨h.keepBelow Kt (by rw [spU]; exact stackFrame), ?_, gcd, bezout, lt, Kt, stackFrame⟩
  intro x hx hz
  by_cases hin : (⟨B, 8 * invWords a⟩ : Region).Contains x 1
  · have hi : ofs B x < 8 * invWords a := by
      simp only [Region.Contains] at hin
      unfold ofs
      omega
    have changed := inside (ofs B x) hi fun c => writes_ranges hka c hx
    have back : B + BitVec.ofNat 64 (ofs B x) = x := by
      unfold ofs
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm]
      exact BitVec.sub_add_cancel x B
    rw [back] at changed
    rw [changed]
    apply FE x
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact farU x (Region.sub_prefix size x hin)
  · apply frame x
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hin
    · intro c
      apply hz
      rw [code_stack] at c
      rw [← spU]
      exact below_sub (by decide) lowSp x c

theorem callInverse_ok {B : Addr} {Z n N : Nat} {w : Width} {s : State} (R : InvReady B Z n N w s) :
    WP isa (callInverse w) s fun t =>
      Ws t B Z n N ∧
      OutsS B (s.gpr .esp) (VG.Proof.RsaKeyGen.X86.Key.inverseRanges (w.words n) invSlots) s.mem t.mem ∧
      num t.mem B (w.words n) 1 = Nat.gcd (num s.mem B (w.words n) 0) (num s.mem B (w.words n) aM) ∧
      (num s.mem B (w.words n) aM : Int) ∣
        (num t.mem B (w.words n) 3 : Int) * num s.mem B (w.words n) 0 - num t.mem B (w.words n) 1 ∧
      num t.mem B (w.words n) 3 < num s.mem B (w.words n) aM ∧
      Keeps [.eax, .ecx, .edx] s t ∧ Frame [⟨B, Z⟩, below (s.gpr .esp) 52] s.mem t.mem := by
  unfold callInverse
  refine WP.seq (WP.mono (args_ok R) fun u ⟨a, C, Ku, mu⟩ => ?_)
  refine WP.mono (call_ok C) fun t ⟨ht, O, gcd, bezout, lt, Kt, F⟩ => ?_
  rw [mu] at O gcd bezout lt F
  exact ⟨ht, O, gcd, bezout, lt, Ku.trans Kt, F⟩

end VG.Proof.RsaKeyGen.X86.KeyRuntime
