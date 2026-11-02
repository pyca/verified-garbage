module

public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.Bignum.Arm.CallStack
public import VerifiedGarbage.Proof.Bignum.Arm.MontCallEntry
public import VerifiedGarbage.Impl.Bignum.Arm.MontCall
public import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Arm.MontCallArgs
import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! # Ready arithmetic arguments for the shared callable kernel -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.FrameStack VG.Proof.Mont
open VG.Proof.Rsa.Mont (arrAt numAt Operand)
open VG.Proof.X25519.Arm (Rest)

theorem montCallArgs_input (s u : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s) (hb : Operand b)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0)
    (eq : WorkspaceEq (State.addr base) (8 * len) s.mem u.mem)
    (ptrU : u.gpr .r0 = base) (outU : u.gpr .r2 = BitVec.ofNat 32 o)
    (aU : u.gpr .r3 = BitVec.ofNat 32 a)
    (memU : u.mem = s.mem.writeW (State.addr (allocated 8 s).sp) (BitVec.ofNat 32 b))
    (restU : Rest [.r1, .r2, .r3, .r12, .lr] (allocated 8 s) u) :
    CallInput base len w o a b u := by
  let A := allocated 8 s
  have fit8 : 8 ≤ s.sp.toNat := by have := cs.fit; omega
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have endM := array_end_le (w := w) (j := 0) (k := 8) (by decide)
  have argsWs : Workspace A base (8 * len) :=
    ⟨h.workspace.nowrap, List.mem_cons_of_mem _ h.workspace.writable⟩
  refine ⟨argsWs.congr restU.wr, eq.layout h.layout,
    (eq.width (by omega)).trans h.width, ptrU, outU, aU, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [restU.sp, memU]; exact Mem.readW_writeW_self32 _ _ _
  · change ((u.mem.readW (off (State.addr base) (arrAt w 0)) 64).toNat *
      (u.mem.readW (off (State.addr base) 56) 64).toNat + 1) % 2 ^ 64 = 0
    rw [eq.word (d := arrAt w 0) (bits := 64) (by omega), eq.word (d := 56) (bits := 64) (by omega)]
    exact h.inverse
  · rw [eq.number fits hb.1, eq.number fits (by decide : 0 < 8)]; exact operand
  · rw [restU.sp]; change 40 ≤ (s.sp - BitVec.ofNat 32 8).toNat
    rw [sub_toNat' fit8]; have := cs.fit; omega
  · rw [restU.rd, restU.wr, restU.sp]
    exact ⟨⟨State.addr A.sp, 8⟩, List.mem_append_right _ List.mem_cons_self,
      by change (⟨State.addr A.sp, 8⟩ : Region).Contains (State.addr A.sp) 4
         simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
  · rw [restU.sp]
    exact cs.separate.sub_left (belowA_inner (a := 40) (k := 8) (by decide) cs.fit)
  · have fit40 : 40 ≤ u.sp.toNat := by
      rw [restU.sp]
      change 40 ≤ (s.sp - BitVec.ofNat 32 8).toNat
      rw [sub_toNat' fit8]
      have := cs.fit
      omega
    rw [belowA, addr_sub' fit40]
    exact Offset.below_disjoint _ (by decide)

/-- Argument setup supplies the complete callee precondition in the caller's
allocated argument frame. -/
theorem montCallArgs_ready (s : State) {base : BitVec 32} {len w o a b : Nat}
    (h : ArithmeticReady base len w s) (cs : CallStack base len s)
    (ho : Operand o) (ha : Operand a) (hb : Operand b)
    (operand : numAt s.mem (State.addr base) w b < numAt s.mem (State.addr base) w 0) :
    WP isa (.block (VG.Impl.Bignum.Arm.MontCall.opArgs o a b)) (allocated 8 s)
      (CallInput base len w o a b) := by
  let A := allocated 8 s
  have fit8 : 8 ≤ s.sp.toNat := by have := cs.fit; omega
  have fits : arrAt w 8 ≤ 8 * len := h.width ▸ h.layout.2.2.1
  have size : 256 ≤ 8 * len := by simp only [arrAt, Proof.Rsa.Mont.hdrBytes] at fits; omega
  have argsWs : Workspace A base (8 * len) :=
    ⟨h.workspace.nowrap, List.mem_cons_of_mem _ h.workspace.writable⟩
  have argsWrite : InRegions A.wr (State.addr A.sp) 4 :=
    ⟨⟨State.addr A.sp, 8⟩, List.mem_cons_self,
      by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; decide⟩
  have argsFit : A.sp.toNat + 8 ≤ 2 ^ 32 := by
    change (s.sp - BitVec.ofNat 32 8).toNat + 8 ≤ 2 ^ 32
    rw [sub_toNat' fit8]; have := s.sp.isLt; omega
  have argSub : Region.Sub ⟨State.addr A.sp, 4⟩ (belowA s.sp 48) :=
    fun x hx => belowA_sub (a := 8) (by decide) cs.fit x (Region.sub_prefix (by decide) x hx)
  have argSep := cs.separate.sub_left argSub
  refine WP.mono (montCallArgs_ok A argsWs (by omega) h.ptr argsFit argsWrite ho.1 ha.1 hb.1) ?_
  rintro u ⟨ptrU, outU, aU, memU, frameU, restU⟩
  have eq := WorkspaceEq.of_frame (by have := h.workspace.nowrap; omega : 8 * len < 2 ^ 64)
    frameU (by intro r hr; have er := List.mem_singleton.mp hr; subst r; exact argSep.symm)
  exact montCallArgs_input s u h cs hb operand eq ptrU outU aU memU restU

end VG.Proof.Bignum.Arm
