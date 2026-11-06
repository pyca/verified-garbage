module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Search.Data
public import VerifiedGarbage.Impl.RsaKeyGen.Arm.Search
public import VerifiedGarbage.Proof.Framework.Arm.CallF
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Rc2.PairMem

/-! # The search's entry (ARMv7): the push, and the loop's first state -/

@[expose] public section

namespace VG.Proof.RsaKeyGen.Arm.Search

open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)
open VG.Proof.Ffdh.Arm (withRest_all)
open VG.Impl.RsaKeyGen.Arm.Search
open VG.Spec.RsaKeyGen (primeSearch primeEntropy primeLimit)

namespace SearchInput

variable {p : SearchPublic} {o : State}

theorem len_valid (h : SearchInput p o) : 32 ≤ p.len ∧ p.len ≤ 512 := by
  have hv := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← h.2]; unfold Spec.RsaKeyGen.primeLenValid at hv; exact ⟨hv.1, hv.2.1⟩

theorem remaining_le (h : SearchInput p o) : p.remaining ≤ 32768 := by
  have hr := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv := h.len_valid
  rw [← h.2] at hv ⊢
  unfold primeLimit at hr
  change searchRemaining o ≤ 32768
  split at hr <;> simp only [searchOfState] at hv <;> omega

/-- The `n` bytes `a` below the stack pointer are in the search's stack. -/
theorem stack_sub (_h : SearchInput p o) {a n : Nat} (ha : a ≤ stackUse) (hn : stackUse - a + n ≤ stackUse) :
    Region.Sub ⟨State.addr o.sp - BitVec.ofNat 64 a, n⟩ (inStack o) :=
  Offset.sub_below _ ha hn

end SearchInput

theorem sub_add_ofNat (x : BitVec 32) (k d : Nat) :
    x - BitVec.ofNat 32 k + BitVec.ofNat 32 (k + d) = x + BitVec.ofNat 32 d := by
  rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]

/-- The push changes only the search's stack. -/
theorem push_frame {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Frame (changes o) o.mem (pushed pushRegs o).mem := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  refine (FrameStack.pushed_frameA (rs := pushRegs) hroom).sub fun r hr => ?_
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨inStack o, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
  change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
  rw [FrameStack.addr_sub' hroom]
  exact h.stack_sub (by decide) (by decide)

theorem push_saved {p : SearchPublic} {o : State} (h : SearchInput p o) :
    Saved (pushed pushRegs o).mem p.S1 o := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  have top := h.1.2.1
  let sp := o.sp - BitVec.ofNat 32 40
  have bound : sp.toNat + 40 ≤ 2 ^ 32 := by
    rw [show sp = o.sp - BitVec.ofNat 32 40 from rfl, FrameStack.sub_toNat' hroom]; omega
  have address (k : Nat) (hk : k < 40) : State.addr (sp + BitVec.ofNat 32 k) = off (State.addr sp) k :=
    VG.Arm.addr_add (by omega)
  have memEq : (pushed pushRegs o).mem = Spill.saveMem o.mem (State.addr sp) o.gpr slots := by
    change storeWords o.mem sp _ = _
    simp only [storeWords, List.map_cons, List.map_nil, Spill.saveMem]
    simp only [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, Offset.add_add]
    rw [address 4 (by decide), address 8 (by decide), address 12 (by decide), address 16 (by decide),
      address 20 (by decide), address 24 (by decide), address 28 (by decide), address 32 (by decide),
      address 36 (by decide)]
    simp only [off, BitVec.add_zero]
  have hS : p.S1 = sp := by rw [SearchPublic.S1, h.sp_eq]
  unfold Saved
  rw [memEq, hS]
  exact Spill.saveMem_saved (lo := 0) (hi := 40) (State.addr sp) o.gpr o.mem slots (by decide)

theorem low_half {m : Mem} {a : Addr} {n : Nat} (h : m.readW a 64 = BitVec.ofNat 64 n) :
    m.readW a 32 = BitVec.ofNat 32 n := by
  rw [← VG.Proof.Rc2.Word32.readW64_lo, h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

theorem entry_ok {p : SearchPublic} {o : State} (h : SearchInput p o) :
    WP isa (.block entry) (pushed pushRegs o) (SearchLive p o 0 p.remaining) := by
  have hroom : 40 ≤ o.sp.toNat := Nat.le_trans (by decide) h.1.1
  have top := h.1.2.1
  have hf := push_frame h
  have hS : p.S1 = o.sp - BitVec.ofNat 32 40 := by rw [SearchPublic.S1, h.sp_eq]
  -- the state pointer, a stack argument
  have a68 : State.addr (o.sp - BitVec.ofNat 32 40 + BitVec.ofNat 32 68) = stackArgAddr o 7 := by
    rw [show (68 : Nat) = 40 + 4 * 7 from rfl, sub_add_ofNat]; rfl
  have r68 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (stackArgAddr o 7) 4 := by
    refine ⟨inArgs o, List.mem_append_left _ (by rw [h.rd]; simp [inReads]), ?_⟩
    have e : stackArgAddr o 7 = stackArgAddr o 0 + BitVec.ofNat 64 28 := by
      simp only [stackArgAddr, Nat.mul_zero, BitVec.add_zero]
      exact VG.Arm.addr_add (by omega)
    rw [e]; exact Offset.contains_base _ (by decide) (by decide)
  have v68 : (pushed pushRegs o).mem.readW (stackArgAddr o 7) 32 = p.stp := by
    rw [h.arg_frame hf (by decide), ← h.2]; rfl
  -- the low half of the state's first word
  have hst : (inState o).Disjoint (FrameStack.belowA o.sp 40) := by
    have hd := h.stack_disjoint (r := inState o) (by simp [inWrites])
    refine fun x hx hy => hd x ?_ hx
    have hsub : Region.Sub (FrameStack.belowA o.sp 40) (inStack o) := by
      change Region.Sub ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ _
      rw [FrameStack.addr_sub' hroom]; exact h.stack_sub (by decide) (by decide)
    exact hsub x hy
  have stp : inState o = ⟨State.addr p.stp, 32⟩ := by rw [← h.2]; rfl
  have nstp : p.stp.toNat + 32 ≤ 2 ^ 32 := by rw [← h.2]; exact h.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have a0 : State.addr (p.stp + BitVec.ofNat 32 0) = State.addr p.stp := by rw [BitVec.add_zero]
  have r0 : InRegions (o.rd ++ ⟨State.addr (o.sp - BitVec.ofNat 32 40), 40⟩ :: o.wr) (State.addr p.stp) 4 := by
    refine ⟨inState o, List.mem_append_right _ (by rw [h.wr]; simp [inWrites]), ?_⟩
    rw [stp]
    simpa using Offset.contains_base (State.addr p.stp) (d := 0) (n := 4) (k := 32) (by decide) (by decide)
  have v0 : (pushed pushRegs o).mem.readW (State.addr p.stp) 32 = BitVec.ofNat 32 p.remaining := by
    have hpf := FrameStack.pushed_frameA (rs := pushRegs) hroom
    have e := hpf.readW (r := inState o) (a := State.addr p.stp) (w := 32)
      (by rw [stp]; simpa using Offset.contains_base (State.addr p.stp) (d := 0) (n := 4) (k := 32) (by decide) (by decide))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact hst) (by decide)
    rw [e]
    have hw : o.mem.readW (State.addr p.stp) 64 = BitVec.ofNat 64 p.remaining := by
      rw [← h.2]; change o.mem.readW (State.addr (stackArg o 7)) 64 = BitVec.ofNat 64 (searchRemaining o)
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact low_half hw
  refine WP.mono (withRest_all [.r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12] (Q := fun t =>
      t.gpr .r4 = o.gpr .r0 ∧ t.gpr .r5 = o.gpr .r1 ∧ t.gpr .r6 = o.gpr .r2 ∧ t.gpr .r7 = o.gpr .r3 ∧
      t.gpr .r8 = 0 ∧ t.gpr .r9 = BitVec.ofNat 32 p.remaining ∧ t.gpr .r11 = 4 ∧
      t.mem = (pushed pushRegs o).mem) ?_ (by rfl) (by rfl)) fun t ⟨⟨h4, h5, h6, h7, h8, h9, h11, hm⟩, k⟩ => ?_
  · unfold entry arg pushBytes
    ffrun [pushed_gpr, pushed_sp, pushed_rd, pushed_wr, a68, r68, v68, a0, r0, v0, show 4 * pushRegs.length = 40 from rfl]
  · have hlen : (o.gpr .r1) = BitVec.ofNat 32 p.len := by
      rw [← h.2]; change o.gpr .r1 = BitVec.ofNat 32 (o.gpr .r1).toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine ⟨⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Nat.zero_le _, Nat.le_refl _, h8, h9, h11⟩
    · rw [k.rd]; rfl
    · rw [k.wr, pushed_wr, hS]; rfl
    · rw [k.sp, pushed_sp, hS]; rfl
    · rw [h4, ← h.2]; rfl
    · rw [h5, hlen]
    · rw [h6, ← h.2]; rfl
    · rw [h7, ← h.2]; rfl
    · rw [hm]; exact push_saved h
    · rw [hm]; exact hf

end VG.Proof.RsaKeyGen.Arm.Search
