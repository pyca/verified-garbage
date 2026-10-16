module

public import VerifiedGarbage.Proof.Bignum.Arm.CrtBuffers
public import VerifiedGarbage.Proof.Bignum.Arm.SavedOperandState
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Immutable AAPCS arguments across private RSA workspace switches

Slots 0, 8 and 48 are mutable. Output, length and incoming source arguments
remain fixed throughout the private computation.
-/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

structure CrtCallStack (g : CrtGeometry) (s : State) : Prop where
  nowrap : s.sp.toNat + 112 ≤ 2 ^ 32
  readable : InRegions (s.rd ++ s.wr) (off (State.addr s.sp) 56) 56
  writable : (⟨State.addr s.sp, 56⟩ : Region) ∈ s.wr
  separate : Region.Disjoint ⟨State.addr s.sp, 112⟩ ⟨State.addr g.base, g.size⟩
  output : s.mem.readW (off (State.addr s.sp) 4) 32 = g.output
  count : s.mem.readW (off (State.addr s.sp) 12) 32 = BitVec.ofNat 32 g.length
  pointer : ∀ i : Fin 6, s.mem.readW (off (State.addr s.sp) (56 + 8 * i.val)) 32 = g.source i.succ
  length : ∀ i : Fin 6, s.mem.readW (off (State.addr s.sp) (60 + 8 * i.val)) 32 = BitVec.ofNat 32 (g.sourceLength i.succ)

def crtMutable (g : CrtGeometry) (sp : BitVec 32) : List Region :=
  [⟨State.addr g.base, g.size⟩, ⟨State.addr sp, 4⟩, ⟨off (State.addr sp) 8, 4⟩, ⟨off (State.addr sp) 48, 4⟩]

theorem CrtCallStack.read {g : CrtGeometry} {s : State} (h : CrtCallStack g s) {d : Nat}
    (fit : d + 4 ≤ 112) (side : d + 4 ≤ 56 ∨ 56 ≤ d := by omega) :
    InRegions (s.rd ++ s.wr) (off (State.addr s.sp) d) 4 := by
  rcases side with low | high
  · exact ⟨_, List.mem_append_right _ h.writable, Offset.contains_base _ low (by omega)⟩
  · have read := CallLay.inRegions_sub (off := d - 56) h.readable (l := 4) (by omega) (by decide)
    rw [Offset.add_add, show 56 + (d - 56) = d by omega] at read
    exact read

theorem CrtCallStack.write {g : CrtGeometry} {s : State} (h : CrtCallStack g s) {d : Nat}
    (fit : d + 4 ≤ 56) : InRegions s.wr (off (State.addr s.sp) d) 4 :=
  ⟨_, h.writable, Offset.contains_base _ fit (by omega)⟩

theorem CrtCallStack.word_kept {g : CrtGeometry} {s t : State} {d : Nat}
    (h : CrtCallStack g s) (frame : Frame (crtMutable g s.sp) s.mem t.mem)
    (fit : d + 4 ≤ 112) (safe : d = 4 ∨ d = 12 ∨ 56 ≤ d) :
    t.mem.readW (off (State.addr s.sp) d) 32 = s.mem.readW (off (State.addr s.sp) d) 32 := by
  apply frame.readW (r := ⟨off (State.addr s.sp) d, 4⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  simp only [crtMutable, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.separate.sub_left (Offset.sub_base _ fit)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)

theorem CrtCallStack.after_frame {g : CrtGeometry} {s t : State} {rs : List Reg}
    (h : CrtCallStack g s) (frame : Frame (crtMutable g s.sp) s.mem t.mem) (rest : Rest rs s t) :
    CrtCallStack g t := by
  refine ⟨by rw [rest.sp]; exact h.nowrap,
    by rw [rest.rd, rest.wr, rest.sp]; exact h.readable,
    by rw [rest.wr, rest.sp]; exact h.writable,
    by rw [rest.sp]; exact h.separate, ?_, ?_, ?_, ?_⟩
  · rw [rest.sp, h.word_kept frame (d := 4) (by decide) (by simp)]; exact h.output
  · rw [rest.sp, h.word_kept frame (d := 12) (by decide) (by simp)]; exact h.count
  · intro i
    rw [rest.sp, h.word_kept frame (d := 56 + 8 * i.val) (by have := i.isLt; omega) (by omega)]
    exact h.pointer i
  · intro i
    rw [rest.sp, h.word_kept frame (d := 60 + 8 * i.val) (by have := i.isLt; omega) (by omega)]
    exact h.length i

end VG.Proof.Bignum.Arm
