import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PackedBank
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Table

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

def tailRegs : List VReg := [.v18,.v19,.v25,.v26,.v4] ++ liveRegs

def tailBase (len : Nat) : Reg := if len=2 then .x7 else .x8

structure TailRoots (s : State) (z : Nat → Nat → Nat → Int) : Prop where
  q : ∀ e < 4, vword (s.v .v16) e = 8380417#32
  range : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4, 0 ≤ z g len e ∧ z g len e < 8380417
  read : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ b ∈ [0,16],
    InRegions (s.rd++s.wr) (s.gpr (tailBase len)+BitVec.ofNat 64 (32*g+b)) 16
  root : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (s.mem.read (s.gpr (tailBase len)+BitVec.ofNat 64 (32*g)) 16) e =
      BitVec.ofInt 32 (z g len e)
  reciprocal : ∀ g < 4, ∀ len, len=1 ∨ len=2 → ∀ e < 4,
    vword (s.mem.read (s.gpr (tailBase len)+BitVec.ofNat 64 (32*g+16)) 16) e =
      BitVec.ofInt 32 (Optimized.reciprocal (z g len e))

theorem TailRoots.keep_of {vs : List VReg} {s t : State} {z : Nat → Nat → Nat → Int} (h : TailRoots s z)
    (hc : VChg vs s t) (hq : VReg.v16 ∉ vs) : TailRoots t z := by
  refine ⟨?_,h.range,?_,?_,?_⟩
  · intro e he
    rw [hc.get .v16 hq]
    exact h.q e he
  · simpa only [hc.rd,hc.wr,hc.gpr] using h.read
  · simpa only [hc.mem,hc.gpr] using h.root
  · simpa only [hc.mem,hc.gpr] using h.reciprocal

theorem TailRoots.keep {s t : State} {z : Nat → Nat → Nat → Int} (h : TailRoots s z)
    (hc : VChg tailRegs s t) : TailRoots t z := h.keep_of hc (by decide)

theorem GoodRen.packedClobs_mem {r : Ren} (hr : GoodRen r) (i j : Fin 8) :
    packedClobs r i j ⊆ tailRegs := by
  intro v hv
  simp only [packedClobs,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · exact List.mem_append_right _ hr.free
  · exact List.mem_append_right _ (hr.data i)
  · exact List.mem_append_right _ (hr.data j)

theorem tailGroup_ok (r : Ren) (g : Fin 4) (len : Nat) (hlen : len=1 ∨ len=2)
    (hr : GoodRen r) {s : State} {rest : List Instr} {Q : State → Prop}
    {values : Vector (BitVec 128) 8} {z : Nat → Nat → Nat → Int}
    (hbank : Bank s r.data values) (hconst : TailRoots s z)
    (k : ∀ t, VChg tailRegs s t → TailRoots t z →
      Bank t r.data (packedValues values ⟨2*g.val,by omega⟩ ⟨2*g.val+1,by omega⟩ len (z g.val len)) →
      WP isa (.block rest) t Q) :
    WP isa (.block (rootAt (tailBase len) g.val ++
      renInnerPair r.data[2*g.val] r.data[2*g.val+1] r.free len ++ rest)) s Q := by
  let i : Fin 8 := ⟨2*g.val,by omega⟩
  let j : Fin 8 := ⟨2*g.val+1,by omega⟩
  rw [List.append_assoc]
  refine rootAt_ok (tailBase len) g.val (by omega) ?_
    (hconst.read g.val g.isLt len hlen 16 (by simp)) fun s₁ hc₁ hz₁ hb₁ => ?_
  · simpa only [Nat.add_zero] using hconst.read g.val g.isLt len hlen 0 (by simp)
  · have hp : ∀ v ∈ liveRegs, v ∉ [VReg.v18,.v19] := by decide
    have bank₁ : Bank s₁ r.data values := by
      intro a
      rw [hc₁.get _ (hp _ (hr.data a))]
      exact hbank a
    have hq₁ : ∀ e < 4, vword (s₁.v .v16) e = 8380417#32 := by
      intro e he
      rw [hc₁.get .v16]
      exact hconst.q e he
    refine packedBank_ok r i j len (by intro h; have := congrArg Fin.val h; simp only [i,j] at this; omega)
      hr bank₁ (hconst.range g.val g.isLt len hlen) ?_ ?_ hq₁ fun s₂ hc₂ hb₂ => ?_
    · rw [hz₁]
      exact hconst.root g.val g.isLt len hlen
    · rw [hb₁]
      exact hconst.reciprocal g.val g.isLt len hlen
    · have hc : VChg tailRegs s s₂ := VChg.mono (hc₁.trans hc₂) (by
        intro v hv
        rcases List.mem_append.mp hv with h | h
        · have hs : [VReg.v18,.v19] ⊆ tailRegs := by decide
          exact hs h
        · exact hr.packedClobs_mem i j h)
      exact k s₂ hc (hconst.keep hc) hb₂

end VG.Proof.MlDsa.AArch64.Optimized
