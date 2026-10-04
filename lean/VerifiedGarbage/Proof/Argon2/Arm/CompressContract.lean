import VerifiedGarbage.Proof.Argon2.Arm.Words
import VerifiedGarbage.Proof.Framework.Arm.Spill
import VerifiedGarbage.TCB.Arm.Target

/-!
# Argon2 compression on ARMv7: the contract of the proof

`compressArm`: the contract the proof is written against (and the derivation
uses for its calls); `Spec.Argon2.compressContract` implies it
(`Proof/Argon2/Arm/CompressVerified.lean`). `Pre` names the facts of its
precondition.
-/

namespace VG.Proof.Argon2.Arm

open VG VG.Arm VG.Spec.Argon2
open VG.Proof.Sha512.Arm (A A_eq contains_A)

/-- `vg_argon2_compress(x = r0, y = r1, out = r2, scratch = r3)`: reads the two
input blocks, writes the output block and 4096 bytes of scratch. -/
def compressArm : Contract Arm.isa where
  pre s :=
    let x : Region := ⟨State.addr (s.gpr .r0), 1024⟩
    let y : Region := ⟨State.addr (s.gpr .r1), 1024⟩
    let out : Region := ⟨State.addr (s.gpr .r2), 1024⟩
    let scratch : Region := ⟨State.addr (s.gpr .r3), 4096⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
    out.Disjoint scratch ∧ x.Disjoint out ∧ x.Disjoint scratch ∧ y.Disjoint out ∧ y.Disjoint scratch ∧
    (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 1024 ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 4096 ≤ 2 ^ 32
  post s s' := blockAt s'.mem (State.addr (s.gpr .r2)) =
    compress (blockAt s.mem (State.addr (s.gpr .r0))) (blockAt s.mem (State.addr (s.gpr .r1)))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

section
variable (s₀ : State)

abbrev xp : BitVec 32 := s₀.gpr .r0
abbrev yp : BitVec 32 := s₀.gpr .r1
abbrev op : BitVec 32 := s₀.gpr .r2
abbrev scr : BitVec 32 := s₀.gpr .r3
abbrev xR : Region := ⟨State.addr (xp s₀), 1024⟩
abbrev yR : Region := ⟨State.addr (yp s₀), 1024⟩
abbrev outR : Region := ⟨State.addr (op s₀), 1024⟩
abbrev scrR : Region := ⟨State.addr (scr s₀), 4096⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [xR s₀, yR s₀]
  wr : s₀.wr = [outR s₀, scrR s₀]
  out_scr : (outR s₀).Disjoint (scrR s₀)
  x_out : (xR s₀).Disjoint (outR s₀)
  x_scr : (xR s₀).Disjoint (scrR s₀)
  y_out : (yR s₀).Disjoint (outR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  x_fits : (xp s₀).toNat + 1024 ≤ 2 ^ 32
  y_fits : (yp s₀).toNat + 1024 ≤ 2 ^ 32
  out_fits : (op s₀).toNat + 1024 ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 4096 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : compressArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem scr_contains {d : Nat} (hd : d + 4 ≤ 4096) : (scrR s₀).Contains (A (scr s₀) d) 4 :=
  contains_A hp.scr_fits hd

theorem out_wr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions s.wr (A (op s₀) d) 4 :=
  ⟨outR s₀, by simp [hw, hp.wr], contains_A hp.out_fits hd⟩

theorem scr_wr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions s.wr (A (scr s₀) d) 4 :=
  ⟨scrR s₀, by simp [hw, hp.wr], contains_A hp.scr_fits hd⟩

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (A (scr s₀) d) 4 :=
  VG.Proof.Sha512.Arm.mem_rd (hp.scr_wr hw hd)

theorem in_x {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (A (xp s₀) d) 4 :=
  ⟨xR s₀, by simp [hrd, hp.rd], contains_A hp.x_fits hd⟩

theorem in_y {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (A (yp s₀) d) 4 :=
  ⟨yR s₀, by simp [hrd, hp.rd], contains_A hp.y_fits hd⟩

/-- A word of `x` is unchanged while only `out` and `scratch` are written. -/
theorem x_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (A (xp s₀) d) 32 = s₀.mem.readW (A (xp s₀) d) 32 := by
  refine hf.readW (r := xR s₀) (contains_A hp.x_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.x_out, hp.x_scr⟩

theorem y_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (A (yp s₀) d) 32 = s₀.mem.readW (A (yp s₀) d) 32 := by
  refine hf.readW (r := yR s₀) (contains_A hp.y_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.y_out, hp.y_scr⟩

/-- A word of `scratch` is unchanged while only `out` is written. -/
theorem scr_frame {m m' : Mem} (hf : Frame [outR s₀] m m') {d : Nat} (hd : d + 4 ≤ 4096) :
    m'.readW (A (scr s₀) d) 32 = m.readW (A (scr s₀) d) 32 := by
  refine hf.readW (r := scrR s₀) (contains_A hp.scr_fits hd) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact hp.out_scr.symm

end Pre

end VG.Proof.Argon2.Arm
