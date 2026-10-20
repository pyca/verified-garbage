module
public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec

import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Out
import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Arith

/-! # CBD2's sequential polynomial stores -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64 VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Cbd16 (out words half)

structure Stores (s0 : State) (p : Addr) (G : Nat → BitVec 32) (n : Nat) (s : State) : Prop where
  keep : Keep [] s0 s
  gpr : s.gpr = s0.gpr
  out : CoeffsUpTo s.mem p n G (fun i => coeffAt s0.mem p i)
  frame : Frame [polyRegion p] s0.mem s.mem
  q : Lanes (s.v .v16) fun _ => 3329
  c : Lanes (s.v .v17) fun _ => 3327
  zero : s.v .v22 = 0

theorem Stores.vchg {s0 s t : State} {p : Addr} {G : Nat → BitVec 32} {n : Nat}
    (h : Stores s0 p G n s) {rs : List VReg} (hc : VChg rs s t)
    (h16 : .v16 ∉ rs := by decide) (h17 : .v17 ∉ rs := by decide)
    (h22 : .v22 ∉ rs := by decide) (hp : ∀ r ∈ preservedV, r ∉ rs := by decide +kernel) :
    Stores s0 p G n t :=
  ⟨h.keep.trans (hc.keep hp), hc.gpr.trans h.gpr, by rw [hc.mem]; exact h.out,
   by rw [hc.mem]; exact h.frame, by rw [hc.get _ h16]; exact h.q,
   by rw [hc.get _ h17]; exact h.c, by rw [hc.get _ h22]; exact h.zero⟩

section
variable {rest : List Instr} {Q : State → Prop}

theorem store {s0 s : State} {p : Addr} {G : Nat → BitVec 32} {n off : Nat}
    {part : VPermOp} (h : Stores s0 p G n s)
    (hn : n+4 ≤ 256) (ho : off%16=0 ∧ off < 4096*16)
    (hp : s.gpr .x1 + BitVec.ofNat 64 off = coeffAddr p n)
    (hw : s.wr = [polyRegion p]) {f : Nat → Nat}
    (hx : Lanes (VPermOp.eval part .h8 (s.v .v5) (s.v .v22)) f)
    (hf : ∀ e < 4, f e ≤ 4)
    (hg : ∀ e < 4, (G (n+e)).toNat = (f e+3327)%3329)
    (k : ∀ t, Stores s0 p G (n+4) t →
      (∀ r, r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) → WP isa (.block rest) t Q) :
    WP isa (.block (out off part ++ rest)) s Q := by
  have hin : InRegions s.wr (coeffAddr p n) 16 := by
    rw [hw]
    exact in_regions (List.mem_singleton_self _) (contains_off (by omega) (by decide))
  refine out_ok ho hp hin h.q h.c hx hf fun t x hc hp' hv hm hx' => ?_
  refine k t ⟨h.keep.trans hc, hp'.trans h.gpr, ?_, ?_, ?_, ?_, ?_⟩ hv
  · rw [hm]
    exact h.out.write16 hn fun e he => BitVec.eq_of_toNat_eq ((hx' e he).trans (hg e he).symm)
  · rw [hm]; exact frame16 h.frame hn x
  · rw [hv .v16 (by decide) (by decide)]; exact h.q
  · rw [hv .v17 (by decide) (by decide)]; exact h.c
  · rw [hv .v22 (by decide) (by decide)]; exact h.zero


theorem words_ok {s0 s : State} {p : Addr} {G : Nat → BitVec 32} {n off : Nat}
    {part : VPermOp} (h : Stores s0 p G n s)
    (hn : n+8 ≤ 256) (ho : off%16=0 ∧ off+16 < 4096*16)
    (hp : s.gpr .x1 + BitVec.ofNat 64 off = coeffAddr p n)
    (hw : s.wr = [polyRegion p]) {f : Nat → Nat}
    (hx : ∀ e < 8, (vhalf (VPermOp.eval part .b16 (s.v .v4) 0) e).toNat = f e)
    (hf : ∀ e < 8, f e ≤ 4)
    (hg : ∀ e < 8, (G (n+e)).toNat = (f e+3327)%3329)
    (k : ∀ t, Stores s0 p G (n+8) t →
      (∀ r, r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) → WP isa (.block rest) t Q) :
    WP isa (.block (words off part ++ rest)) s Q := by
  unfold words
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_vop rfl fun s1 h1 => ?_
  have hs1 := h.vchg h1.chg
  have hl : ∀ e < 8, (vhalf (s1.v .v5) e).toNat = f e := by
    intro e he; rw [h1.v,h.zero]; exact hx e he
  have hz : ∀ e < 8, vhalf (s1.v .v22) e = 0 := by
    intro e _; rw [hs1.zero]; simp [vhalf]
  refine store hs1 (by omega) ⟨ho.1,by omega⟩
    (by rw [h1.gpr]; exact hp) (by rw [h1.wr]; exact hw)
    (fun e he => ((VG.Proof.MlKem.AArch64.Ntt16.vword_zip_zero hz he).1).trans (hl e (by omega)))
    (fun e he => hf e (by omega)) (fun e he => hg e (by omega)) fun s2 hs2 hv2 => ?_
  have hl2 : ∀ e < 8, (vhalf (s2.v .v5) e).toNat = f e := by
    intro e he; rw [hv2 .v5 (by decide) (by decide)]; exact hl e he
  have hz2 : ∀ e < 8, vhalf (s2.v .v22) e = 0 := by
    intro e _; rw [hs2.zero]; simp [vhalf]
  refine store hs2 (by omega) ⟨by omega,ho.2⟩ ?_ ?_
    (fun e he => ((VG.Proof.MlKem.AArch64.Ntt16.vword_zip_zero hz2 he).2).trans (hl2 (4+e) (by omega)))
    (fun e he => hf (4+e) (by omega)) ?_ fun t ht hv3 => ?_
  · rw [hs2.gpr,← h.gpr, BitVec.ofNat_add,← BitVec.add_assoc,hp]
    exact coeffAddr_step p n
  · rw [hs2.keep.wr,← h.keep.wr]; exact hw
  · intro e he; simpa only [Nat.add_assoc] using hg (4+e) (by omega)
  · refine k t (by simpa only [Nat.add_assoc] using ht) ?_
    intro r h5 h6 h7
    rw [hv3 r h6 h7,hv2 r h6 h7,h1.get r h5]


theorem half_ok {s0 s : State} {p : Addr} {G : Nat → BitVec 32} {n off : Nat}
    {part : VPermOp} (h : Stores s0 p G n s)
    (hn : n+16 ≤ 256) (ho : off%16=0 ∧ off+48 < 4096*16)
    (hp : s.gpr .x1 + BitVec.ofNat 64 off = coeffAddr p n)
    (hw : s.wr = [polyRegion p]) {f : Nat → Nat}
    (hx : ∀ e < 16, (vbyte (VPermOp.eval part .b16 (s.v .v2) (s.v .v3)) e).toNat = f e)
    (hf : ∀ e < 16, f e ≤ 4)
    (hg : ∀ e < 16, (G (n+e)).toNat = (f e+3327)%3329)
    (k : ∀ t, Stores s0 p G (n+16) t →
      (∀ r, r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) → WP isa (.block rest) t Q) :
    WP isa (.block (half off part ++ rest)) s Q := by
  unfold half
  simp only [List.cons_append, List.nil_append, List.append_assoc]
  refine wp_vop rfl fun s1 h1 => ?_
  have hs1 := h.vchg h1.chg
  have hl : ∀ e < 16, (vbyte (s1.v .v4) e).toNat = f e := by
    intro e he; rw [h1.v]; exact hx e he
  refine words_ok hs1 (by omega) ⟨ho.1,by omega⟩
    (by rw [h1.gpr]; exact hp) (by rw [h1.wr]; exact hw)
    (fun e he => ((half_zip_zero (s1.v .v4) he).1).trans (hl e (by omega)))
    (fun e he => hf e (by omega)) (fun e he => hg e (by omega)) fun s2 hs2 hv2 => ?_
  have hl2 : ∀ e < 16, (vbyte (s2.v .v4) e).toNat = f e := by
    intro e he; rw [hv2 .v4 (by decide) (by decide) (by decide)]; exact hl e he
  refine words_ok hs2 (by omega) ⟨by omega,by omega⟩ ?_ ?_
    (fun e he => ((half_zip_zero (s2.v .v4) he).2).trans (hl2 (8+e) (by omega)))
    (fun e he => hf (8+e) (by omega)) ?_ fun t ht hv3 => ?_
  · rw [hs2.gpr,← h.gpr, BitVec.ofNat_add,← BitVec.add_assoc,hp]
    exact coeffAddr_off p n 8
  · rw [hs2.keep.wr,← h.keep.wr]; exact hw
  · intro e he; simpa only [Nat.add_assoc] using hg (8+e) (by omega)
  · refine k t (by simpa only [Nat.add_assoc] using ht) ?_
    intro r h4 h5 h6 h7
    rw [hv3 r h5 h6 h7,hv2 r h5 h6 h7,h1.get r h4]

end
end VG.Proof.MlKem.AArch64.Cbd16
