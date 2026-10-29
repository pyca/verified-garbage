module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Arguments
public import VerifiedGarbage.Proof.RsaKeyGen.Slots
public import VerifiedGarbage.Proof.RsaKeyGen.Table
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Contract

/-! # The attempt's precondition, at the callee's entry -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.Generation (writeController writeController_word controllerValue allocated)
open VG.Proof.Ffdh.X86_64.GenerateKey (gkPre)

/-- The regions the attempt reads: the domain, `p_len` octets of the tape at
`used`, and its stack arguments. -/
def callReads (p : KeyPublic) (used : Nat) : List Region :=
  [⟨p.dp, p.dlen⟩, ⟨p.rp + BitVec.ofNat 64 used, p.len⟩, ⟨p.sp - 40, 40⟩]

/-- The regions the attempt writes: `x`, `y` and the working space. -/
def callWrites (p : KeyPublic) : List Region := [⟨p.xp, p.len⟩, ⟨p.yp, p.len⟩, ⟨p.B, p.Z⟩]

theorem callValues_bound (p : KeyPublic) (used : Nat) : ∀ e ∈ callValues p used, e.1 < 16 := by
  simp only [callValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

/-- The callee's entry, as the call makes it. -/
abbrev callState (p : KeyPublic) (used : Nat) (u : State) : State :=
  u.callEntry.withRegions (callReads p used) (callWrites p)

theorem call_rsp {p : KeyPublic} {used : Nat} {u : State} (hu : u.gpr .rsp = p.sp - 40) :
    (callState p used u).gpr .rsp = p.sp - 40 - 8 := by
  simp only [State.withRegions_gpr, State.callEntry_rsp, hu]

theorem call_argAddr {p : KeyPublic} {used : Nat} {u : State} (hu : u.gpr .rsp = p.sp - 40) :
    stackArgAddr (callState p used u) 0 = p.sp - 40 := by
  simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hu]
  exact BitVec.sub_add_cancel _ _

theorem call_arg {p : KeyPublic} {used : Nat} {s u : State} (hu : u.gpr .rsp = p.sp - 40)
    (hs : s.gpr .rsp = p.sp)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used)) (j : Nat) (hj : j < 5) :
    stackArg (callState p used u) j = controllerValue (callValues p used) j
      (word s.mem (p.sp - 40) (8 * j)) := by
  have ha : stackArgAddr (callState p used u) j = p.sp - 40 + BitVec.ofNat 64 (8 * j) := by
    simp only [stackArgAddr, State.withRegions_gpr, State.callEntry_rsp, hu]
    rw [show 8 * (j + 1) = 8 + 8 * j by omega, BitVec.ofNat_add, ← BitVec.add_assoc,
      show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.sub_add_cancel]
  have e1 : p.sp - 40 - 8 + BitVec.ofNat 64 (8 + 8 * j) = p.sp - 40 + BitVec.ofNat 64 (8 * j) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      BitVec.sub_add_cancel]
  have sep : Mem.Sep (p.sp - 40 + BitVec.ofNat 64 (8 * j)) (64 / 8) (p.sp - 40 - 8) (64 / 8) := by
    have := Offset.sep (p.sp - 40 - 8) (d := 8 + 8 * j) (n := 8) (e := 0) (k := 8)
      (.inr (by omega)) (by omega_using [hj]) (by decide)
    rw [e1, BitVec.add_zero] at this
    exact this
  unfold stackArg
  rw [ha, State.withRegions_mem, State.callEntry_mem, hu, Mem.readW_writeW_sep sep (by decide), hm, hs]
  exact writeController_word _ _ _ (callValues_bound p used) j (by omega_using [hj])

end VG.Proof.Ffdh.X86_64.KeyGeneration
