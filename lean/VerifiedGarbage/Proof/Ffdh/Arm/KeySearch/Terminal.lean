module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Controller
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Terminal and entropy-request writes clear the full packed-u64 request,
including an arbitrary high half present in the incoming controller state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

def terminalMem (m : Mem) (base : BitVec 32) (status : BitVec 32) : Mem :=
  ((writeLow m base [(0, 0), (1, 0), (3, 0)]).writeW (off (State.addr base) 28) (0#32)).writeW
    (off (State.addr base) 112) status

theorem terminal_ok (s : State) {base : BitVec 32} {status : Nat}
    (h : Controller base s) (statusBound : status = 1 ∨ status = 3) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.terminal status)) s fun t =>
      t.mem = terminalMem s.mem base (BitVec.ofNat 32 status) ∧ Rest [.r10, .r11] s t := by
  refine withRest [.r10, .r11] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block (VG.Impl.Ffdh.Arm.KeySearch.terminal status) : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  have addr28 : State.addr (s.gpr .r4 + BitVec.ofNat 32 28) = off (State.addr base) 28 := by
    rw [h.ptr]
    exact VG.Arm.addr_add (by have := h.space.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.KeySearch.terminal VG.Impl.Ffdh.Arm.KeySearch.stf terminalMem writeLow
  simp only [List.foldl_cons, List.foldl_nil]
  rcases statusBound with rfl | rfl <;>
    ffrun [h.addr (by decide : 0 < 16), h.addr (by decide : 1 < 16), h.addr (by decide : 3 < 16), h.addr (by decide : 14 < 16),
      h.write (by decide : 0 < 16), h.write (by decide : 1 < 16), h.write (by decide : 3 < 16), h.write (by decide : 14 < 16),
      addr28, h.space.write (off := 28) (by decide)]
  all_goals rfl

def requestMem (m : Mem) (base : BitVec 32) : Mem :=
  ((writeLow m base [(3, lowWord m base 2)]).writeW (off (State.addr base) 28) (0#32)).writeW
    (off (State.addr base) 112) (0#32)

theorem requestBlock_ok (s : State) {base : BitVec 32} (h : Controller base s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r10 2, .mov .r11 (.imm 0),
      VG.Impl.Ffdh.Arm.KeySearch.stf .r10 3, .str .r11 .r4 28, VG.Impl.Ffdh.Arm.KeySearch.stf .r11 14]) s fun t =>
      t.mem = requestMem s.mem base ∧ Rest [.r10, .r11] s t := by
  refine withRest [.r10, .r11] ?_ (by
    intro r hr i hi
    have checked : (instrs (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r10 2, .mov .r11 (.imm 0),
      VG.Impl.Ffdh.Arm.KeySearch.stf .r10 3, .str .r11 .r4 28, VG.Impl.Ffdh.Arm.KeySearch.stf .r11 14] : Prog isa)).all
        (fun i => !(clobbers i r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have f := List.all_eq_true.mp checked i hi
    cases hc : clobbers i r <;> simp_all) (by rfl)
  have addr28 : State.addr (s.gpr .r4 + BitVec.ofNat 32 28) = off (State.addr base) 28 := by
    rw [h.ptr]
    exact VG.Arm.addr_add (by have := h.space.nowrap; omega)
  unfold VG.Impl.Ffdh.Arm.KeySearch.ldf VG.Impl.Ffdh.Arm.KeySearch.stf requestMem writeLow lowWord
  simp only [List.foldl_cons, List.foldl_nil]
  ffrun [h.addr (by decide : 2 < 16), h.addr (by decide : 3 < 16), h.addr (by decide : 14 < 16),
    h.read (by decide : 2 < 16), h.write (by decide : 3 < 16), h.write (by decide : 14 < 16),
    addr28, h.space.write (off := 28) (by decide)]
  rfl

end VG.Proof.Ffdh.Arm.KeySearch
