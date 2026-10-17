module

public import VerifiedGarbage.Proof.Rsa.Arm.RvTop1
public import VerifiedGarbage.Proof.Bignum.Arm.PcEntry
public import VerifiedGarbage.Proof.Bignum.Arm.ModulusCheck
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # `vg_rsa_recover_primes` on ARMv7: the entry (`entry_ok`) -/

@[expose] public section

namespace VG.Proof.Rsa.Arm.Recover
open VG VG.Arm VG.Proof.Mont VG.Impl.Rsa.Arm.Recover VG.Proof.Bignum.Arm
open VG.Proof.X25519.Arm (Upd Mupd Rest wp_str)

/-- A region apart from both parts of `[a, a + 88)`. -/
theorem disj88 {r : Region} {a : Addr} (h1 : r.Disjoint ⟨a, 56⟩) (h2 : r.Disjoint ⟨a + BitVec.ofNat 64 56, 32⟩) :
    r.Disjoint ⟨a, 88⟩ := by
  intro x hx hc
  simp only [Region.Contains] at hc
  by_cases hlt : (x - a).toNat < 56
  · exact h1 x hx (by simp only [Region.Contains]; omega)
  · refine h2 x hx ?_
    simp only [Region.Contains]
    have := (Offset.lt_iff x a (d := 56) (n := 32) (by decide)).mpr ⟨by omega, by omega⟩
    omega

section
variable {s : State}

theorem CIn.sp' (h : CIn s) : State.addr (s.sp - BitVec.ofNat 32 56) = State.addr s.sp - 56#64 :=
  FrameStack.addr_sub' h.spLo

theorem CIn.argAddr (h : CIn s) {i : Nat} (hi : i < 8) :
    off (State.addr (s.sp - BitVec.ofNat 32 56)) (56 + 4 * i) = stackArgAddr s i := by
  have := h.spLo; have := h.spHi
  simp only [stackArgAddr, off]
  rw [h.sp', addr_add (by omega), ← Offset.add_add, BitVec.sub_add_cancel]

/-- The memory after the push and the entry. -/
abbrev entryMem (s : State) : Mem :=
  (pcPushed s).mem.writeW (off (State.addr (s.sp - BitVec.ofNat 32 56)) 4) (s.gpr .r0)

theorem CIn.frameE (h : CIn s) : Frame [cF s] s.mem (entryMem s) := by
  have f := FrameStack.pushed_frameA (rs := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (s := s) h.spLo
  have e : FrameStack.belowA s.sp (4 * 14) = cF s := by
    show (⟨State.addr (s.sp - BitVec.ofNat 32 56), 56⟩ : Region) = _
    rw [h.sp']
  rw [show [Reg.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr].length = 14 from rfl, e] at f
  refine f.writeW (r := cF s) (List.mem_singleton_self _) _ ?_
  simp only [Region.Contains, off]
  rw [h.sp', Offset.add_sub_cancel_left, BitVec.toNat_ofNat]; decide

/-- The entry: `p` saved, and Z iff `n` is valid. -/
theorem entry_run (h : CIn s) :
    WP isa (.block entry) (pcPushed s) fun u => u.sp = s.sp - BitVec.ofNat 32 56 ∧ u.rd = s.rd ∧
      u.wr = (pcPushed s).wr ∧ u.mem = entryMem s ∧
      u.z = Spec.Rsa.modulusValid (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr (stackArg s 0))
        (stackArg s 1).toNat)) (stackArg s 1).toNat := by
  have spLo := h.spLo; have spHi := h.spHi
  have sp' : (pcPushed s).sp = s.sp - BitVec.ofNat 32 56 := rfl
  have spN : (s.sp - BitVec.ofNat 32 56).toNat = s.sp.toNat - 56 := FrameStack.sub_toNat' spLo
  unfold entry
  simp only [List.cons_append, List.nil_append]
  refine wp_stackAddr (r := .r12) (d := 0) (by decide) fun u1 h1 => ?_
  have stackW : (⟨State.addr (pcPushed s).sp, 56⟩ : Region) ∈ (pcPushed s).wr := List.mem_cons_self
  refine wp_str (a := off (State.addr (s.sp - BitVec.ofNat 32 56)) 4) (by decide)
    (by rw [h1.gpr, BitVec.add_zero, sp']; exact addr_add (by simp only [oP]; omega))
    ⟨_, by rw [h1.wr]; exact stackW, Offset.contains_base _ (by decide) (by decide)⟩ fun u2 m2 => ?_
  have mem2 : u2.mem = entryMem s := by rw [m2.mem, h1.mem, h1.other _ (by decide)]; rfl
  have eA : cA s = ⟨State.addr s.sp, 32⟩ := by simp [cA, stackArgAddr]
  have ei : ∀ i < 8, stackArgAddr s i = State.addr s.sp + BitVec.ofNat 64 (4 * i) := fun i hi => by
    simp only [stackArgAddr]; exact addr_add (by omega)
  have fr := h.frameE
  have argRead : ∀ i < 8, InRegions (u2.rd ++ u2.wr) (stackArgAddr s i) 4 := fun i hi => by
    refine ⟨cA s, List.mem_append_left _ (by rw [m2.rd, h1.rd]; show cA s ∈ s.rd; rw [h.rd]; simp), ?_⟩
    rw [eA, ei i hi]; exact Offset.contains_base _ (by omega) (by omega)
  have argVal : ∀ i < 8, u2.mem.readW (stackArgAddr s i) 32 = stackArg s i := fun i hi => by
    rw [mem2]
    refine fr.readW (r := ⟨stackArgAddr s i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    refine h.FA.symm.sub_left ?_
    rw [eA, ei i hi]; exact Offset.sub_base _ (by omega)
  have spA : ∀ i < 8, State.addr (u2.sp + BitVec.ofNat 32 (56 + 4 * i)) = stackArgAddr s i := fun i hi => by
    rw [m2.sp, h1.sp, sp', ← h.argAddr hi]
    simp only [off]; exact addr_add (by rw [FrameStack.sub_toNat' spLo]; omega)
  refine wp_loadStack (d := aoN) (a := stackArgAddr s 0) (by decide) (spA 0 (by decide)) (argRead 0 (by decide))
    fun u3 h3 => ?_
  refine wp_loadStack (d := aoK) (a := stackArgAddr s 1) (by decide) (by rw [h3.sp]; exact spA 1 (by decide))
    (by rw [h3.rd, h3.wr]; exact argRead 1 (by decide)) fun u4 h4 => ?_
  have hk := h.valid
  simp only [Spec.Rsa.lenValid] at hk
  have readN : InRegions (u4.rd ++ u4.wr) (State.addr (stackArg s 0)) (stackArg s 1).toNat :=
    ⟨cN s, List.mem_append_left _ (by rw [h4.rd, h3.rd, m2.rd, h1.rd]; show cN s ∈ s.rd; rw [h.rd]; simp),
      Region.contains_self _ _⟩
  refine WP.mono (modulusCheck_ok u4 (src := stackArg s 0) (k := (stackArg s 1).toNat) hk.1 hk.2 h.fn readN
    (by rw [h4.other _ (by decide), h3.gpr, argVal 0 (by decide)])
    (by rw [h4.gpr, h3.mem, argVal 1 (by decide)]; simp)) fun t ⟨z, m, r⟩ => ?_
  have mt : t.mem = entryMem s := by rw [m, h4.mem, h3.mem, mem2]
  refine ⟨by rw [r.sp, h4.sp, h3.sp, m2.sp, h1.sp]; rfl, by rw [r.rd, h4.rd, h3.rd, m2.rd, h1.rd]; rfl,
    by rw [r.wr, h4.wr, h3.wr, m2.wr, h1.wr], mt, ?_⟩
  rw [z, h4.mem, h3.mem, mem2]
  congr 2
  exact VG.Proof.Rsa.Arm.CrtValues.bytes_frame fr (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.Fn.symm) (by omega)

end

end VG.Proof.Rsa.Arm.Recover
