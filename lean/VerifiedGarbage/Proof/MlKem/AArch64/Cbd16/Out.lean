module
public import VerifiedGarbage.Impl.MlKem.AArch64.Cbd16
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.Rc4.AArch64.Vec


/-! # Canonical reduction and storage of CBD2 lanes -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Cbd16
open VG VG.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Cbd16 (out)

section
variable {rest : List Instr} {Q : State → Prop}

theorem out_ok {s : State} {off : Nat} {part : VPermOp} {a : Addr} {f : Nat → Nat}
    (ho : off % 16 = 0 ∧ off < 4096 * 16)
    (ha : s.gpr .x1 + BitVec.ofNat 64 off = a) (hin : InRegions s.wr a 16)
    (hq : Lanes (s.v .v16) fun _ => 3329)
    (hc : Lanes (s.v .v17) fun _ => 3327)
    (hx : Lanes (VPermOp.eval part .h8 (s.v .v5) (s.v .v22)) f)
    (hf : ∀ e < 4, f e ≤ 4)
    (k : ∀ t x, Keep [] s t → t.gpr = s.gpr →
      (∀ r, r ≠ .v6 → r ≠ .v7 → t.v r = s.v r) →
      t.mem = s.mem.write a 16 x → Lanes x (fun e => (f e+3327)%3329) →
      WP isa (.block rest) t Q) : WP isa (.block (out off part ++ rest)) s Q := by
  refine wp_vop rfl fun s1 h1 => wp_vop rfl fun s2 h2 => ?_
  have hl : Lanes (s2.v .v6) (fun e => f e+3327) := by
    rw [h2.v]
    refine (lanes_add (by rw [h1.v]; exact hx) (by rw [h1.get .v17]; exact hc)).congr ?_
    intro e he
    have := hf e he
    omega
  refine vcsub_ok (by decide) (by rw [h2.get .v16,h1.get .v16]; exact hq) hl
    (fun e he => by have := hf e he; omega) fun s3 h3 hl3 => ?_
  refine wp_strq (a := a) ho (by rw [h3.gpr,h2.gpr,h1.gpr]; exact ha)
    (by rw [h3.wr,h2.wr,h1.wr]; exact hin) fun s4 h4 => ?_
  refine k s4 (s3.v .v6) (((h1.keep.trans h2.keep).trans h3.keep).trans h4.keep)
    (by rw [h4.gpr,h3.gpr,h2.gpr,h1.gpr]) ?_ ?_ hl3
  · intro r h6 h7
    rw [h4.v,h3.get r (by simp [h6,h7]),h2.get r h6,h1.get r h6]
  · rw [h4.mem,h3.mem,h2.mem,h1.mem]

end
end VG.Proof.MlKem.AArch64.Cbd16
