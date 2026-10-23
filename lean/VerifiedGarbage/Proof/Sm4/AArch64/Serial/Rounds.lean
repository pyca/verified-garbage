module

public import VerifiedGarbage.Proof.Sm4.AArch64.Serial.Round
import VerifiedGarbage.Proof.Framework.Interleave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # The 32 serial SM4 rounds -/

@[expose] public section

namespace VG.Proof.Sm4.AArch64.Serial

open VG VG.AArch64 VG.Impl.Sm4.AArch64.Serial
open VG.Proof.Sm4 (sround quad quads)

def written : List Reg := [.x6,.x7,.x8,.x9,.x10,.x11]

def steps (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) : Nat → BitVec 32 :=
  (List.range n).foldl (fun z i => sround .enc (K i) (i%4) z) x

theorem steps_succ (K : Nat → BitVec 32) (n : Nat) (x : Nat → BitVec 32) :
    steps K (n+1) x = sround .enc (K n) (n%4) (steps K n x) := by
  simp only [steps,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem sround_congr (k : BitVec 32) {a w : Nat} {x y : Nat → BitVec 32}
    (ha : a < 4) (h : ∀ j < 4, x j = y j) (hw : w < 4) :
    sround .enc k a x w = sround .enc k a y w := by
  unfold sround
  split
  · rw [h a ha,h _ (Nat.mod_lt _ (by decide)),h _ (Nat.mod_lt _ (by decide)),
      h _ (Nat.mod_lt _ (by decide))]
  · exact h w hw

theorem steps_congr (K L : Nat → BitVec 32) (n : Nat) (x y : Nat → BitVec 32)
    (hk : ∀ i < n, K i = L i) (hx : ∀ j < 4, x j = y j) :
    ∀ w < 4, steps K n x w = steps L n y w := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    intro w hw
    rw [steps_succ,steps_succ,hk n (by omega)]
    exact sround_congr _ (Nat.mod_lt _ (by decide)) (ih (fun i hi => hk i (by omega))) hw

theorem wordReg_mem : ∀ j < 4, wordReg j ∈ written := by decide

theorem rounds_run (s : State) (n : Nat) (hn : n ≤ 32)
    (hc : Constants s) (ht : Table s)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 4) :
    ∃ t, runBlock isa ((List.range n).flatMap round) s = some t ∧
      (∀ w < 4, words t w = steps
        (fun i => s.mem.readW (s.gpr .x5 + BitVec.ofNat 64 (256+4*i)) 32) n (words s) w) ∧
      Constants t ∧ Table t ∧
      (∀ r, r ∉ written → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  induction n with
  | zero => exact ⟨s,rfl,fun _ _ => rfl,hc,ht,fun _ _ => rfl,rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨a,ae,aw,ac,atab,ag,am,ard,awr,asp⟩ := ih (by omega)
    have ab : a.gpr .x5 = s.gpr .x5 := ag _ (by decide)
    have ar : InRegions (a.rd ++ a.wr) (a.gpr .x5 + BitVec.ofNat 64 (256+4*n)) 4 := by
      rw [ard,awr,ab]
      exact hr n (by omega)
    obtain ⟨b,be,bw,bc,bt,bg,bm,brd,bwr,bsp⟩ := round_run (by omega) ac atab ar
    refine ⟨b,?_,?_,bc,bt,?_,bm.trans am,brd.trans ard,bwr.trans awr,bsp.trans asp⟩
    · rw [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        VG.Interleave.runBlock_append,ae,Option.bind_some,be]
    · intro w hw
      rw [bw w hw,am,ab,steps_succ]
      exact sround_congr _ (Nat.mod_lt _ (by decide)) aw hw
    · intro r hr
      have hreg : r ≠ wordReg (n%4) := fun he => hr (he ▸ wordReg_mem _ (Nat.mod_lt _ (by decide)))
      have h10 : r ≠ .x10 := fun he => hr (by simp [written,he])
      have h11 : r ≠ .x11 := fun he => hr (by simp [written,he])
      exact (bg r hreg h10 h11).trans (ag r hr)

theorem steps_quads (K : Nat → BitVec 32) (x : Nat → BitVec 32) (n : Nat) :
    steps K (4*n) x = quads .enc K n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [steps,VG.Proof.Sm4.range_four,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change sround .enc (K (4*n+3)) ((4*n+3)%4)
      (sround .enc (K (4*n+2)) ((4*n+2)%4)
        (sround .enc (K (4*n+1)) ((4*n+1)%4)
          (sround .enc (K (4*n)) ((4*n)%4) (steps K (4*n) x)))) = _
    rw [ih,show (4*n)%4 = 0 by omega,show (4*n+1)%4 = 1 by omega,
      show (4*n+2)%4 = 2 by omega,show (4*n+3)%4 = 3 by omega]
    rfl

end VG.Proof.Sm4.AArch64.Serial
