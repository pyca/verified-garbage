module

public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Sha3.Compl
public import VerifiedGarbage.Impl.Sha3.RISCV64
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RISCV64.Straight
meta import VerifiedGarbage.Proof.Sha3.Compl
meta import VerifiedGarbage.Impl.Sha3.RISCV64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Offset

/-!
# Keccak-f[1600] on RISC-V: a round, by evaluation

As on PPC64LE (`Proof/Sha3/PPC64LE/Round.lean`): a round (`round s d k`) is
checked by evaluating its code over the ANF domain (`Bitslice.Anf`, with
`Straight.eval`): the lanes of the state at `s`, as stored (complemented,
`Compl.cmpl`), are atoms `0–24`, and row 4 of it is in `rowReg` on entry.
The rotations are pairs of shifts, which the evaluator combines. ι's load
of the round constant (`8k(s0)`, a third memory area) splits the round in
two: it loads atom 25 into `t6` and XORs it into `t0`. `check` then
compares what the round stores at `d`, and leaves in `rowReg`, with the
round computed from the specification (`Compl.specP`), and `round_ok` turns
that into a statement about the machine. The two rounds of an iteration
(`check₀`, `check₁`) are each checked once.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Round

open VG VG.RISCV64 VG.RISCV64.Straight VG.Bitslice.Anf VG.Impl.Sha3.RISCV64
open VG.Proof.Sha3.Compl (specP)

/-- The registers of row 4 between rounds. -/
def rowReg (x : Nat) : Reg := [Reg.a2, .a3, .a4, .a5, .a6].getD x .a2

/-- The output state at `d` (slots), the input state at `s` (external words). -/
def cfg (s d : Reg) : Cfg := { base := d, slots := 25, ext := s, exts := 25 }

def ext (k : Nat) : Option Poly := some (atom k)

/-- On entry, row 4 of the input in `rowReg`. -/
def env₀ : Straight.Env Poly :=
  { reg := fun r => if r = .a2 then some (.v (atom 20)) else if r = .a3 then some (.v (atom 21))
      else if r = .a4 then some (.v (atom 22)) else if r = .a5 then some (.v (atom 23))
      else if r = .a6 then some (.v (atom 24)) else none
    slot := fun _ => none }

/-- The output, and row 4 of it in `rowReg`. -/
def post (e : Straight.Env Poly) : Bool :=
  (List.range 25).all (fun j => e.slot j == some (specP j)) &&
    (List.range 5).all fun x => e.reg (rowReg x) == some (.v (specP (20 + x)))

/-- The round from `s` to `d`, with ι (the round constant, atom 25, loaded into
`t6` and XORed into `t0`) between `roundA` and `roundB`. -/
def check (s d : Reg) : Bool :=
  match Straight.eval anf (cfg s d) ext (roundA s) env₀ with
  | none => false
  | some e₁ => match e₁.reg .t0 with
    | some (.v a) => Straight.check anf (cfg s d) ext (roundB s d)
        ((e₁.setReg .t6 (.v (atom 25))).setReg .t0 (.v (pxor a (atom 25)))) post
    | _ => false

theorem of_check {s d : Reg} (h : check s d = true) :
    ∃ e₁ a, Straight.eval anf (cfg s d) ext (roundA s) env₀ = some e₁ ∧ e₁.reg .t0 = some (.v a) ∧
      Straight.check anf (cfg s d) ext (roundB s d)
        ((e₁.setReg .t6 (.v (atom 25))).setReg .t0 (.v (pxor a (atom 25)))) post = true := by
  unfold check at h
  split at h
  · cases h
  · rename_i e₁ he₁
    split at h
    · rename_i a ha
      exact ⟨e₁, a, he₁, ha, h⟩
    · cases h

/-- The registers a round keeps: the pointers, the loop's register, `s1`,
and the callee-saved registers and return address it does not use. -/
def kept : List Reg :=
  [.a0, .a1, .s0, .s1, .ra, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- The round's instructions write none of `kept`. -/
def keeps (s d : Reg) : Bool :=
  (roundA s ++ roundB s d).all fun i => kept.all fun r => Straight.dst i != some r

theorem env₀_reg {r : Reg} {a : Val Poly} (h : env₀.reg r = some a) :
    ∃ x < 5, r = rowReg x ∧ a = .v (atom (20 + x)) := by
  simp only [env₀] at h
  cases r <;> simp at h <;> subst h
  · exact ⟨0, by decide, rfl, rfl⟩
  · exact ⟨1, by decide, rfl, rfl⟩
  · exact ⟨2, by decide, rfl, rfl⟩
  · exact ⟨3, by decide, rfl, rfl⟩
  · exact ⟨4, by decide, rfl, rfl⟩

open VG.Proof.Sha3 (Lanes laneAddr outState)
open VG.Proof.Sha3.Compl (cmpl msk maskP eval_specP)

abbrev KState := Spec.Sha3.State
abbrev Lane := Spec.Sha3.Lane

theorem cmpl_get (A : KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] = A[i] ^^^ msk i := by
  simp [cmpl]

theorem anfRel_fun (V : Nat → Lane) : ∀ (a : Poly) (x y : BitVec 64), AnfRel V a x → AnfRel V a y → x = y :=
  fun _ _ _ h₁ h₂ => h₁.symm.trans h₂

/-- A round from the state at `s` to the state at `d`: on lanes kept
complemented (`cmpl`), with row 4 in `rowReg` before and after. -/
theorem round_ok {sR dR : Reg} (hc : check sR dR = true) (hk : keeps sR dR = true)
    (hsk : sR ∈ kept) (hdk : dR ∈ kept) (k : Nat) (hk8 : 8 * k < 2048)
    {s : State} {A : KState} {rc : Lane} {src dst : Addr}
    (hs : s.gpr sR = src) (hd : s.gpr dR = dst)
    (hsal : src.toNat % 8 = 0) (hdal : dst.toNat % 8 = 0)
    (hrcal : (s.gpr .s0 + BitVec.ofNat 64 (8 * k)).toNat % 8 = 0)
    (he : Proof.Sha3.Env s.rd s.wr src dst (s.gpr .s0 + BitVec.ofNat 64 (8 * k)))
    (hA : Lanes s.mem src (cmpl A))
    (hrow : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl A)[20 + x])
    (hrc : s.mem.readW (s.gpr .s0 + BitVec.ofNat 64 (8 * k)) 64 = rc) :
    WP isa (.block (round sR dR k)) s fun s' =>
      Lanes s'.mem dst (cmpl (outState A rc)) ∧
      (∀ x (hx : x < 5), s'.gpr (rowReg x) = (cmpl (outState A rc))[20 + x]) ∧
      Frame [⟨dst, 200⟩] s.mem s'.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      ∀ r ∈ kept, s'.gpr r = s.gpr r := by
  obtain ⟨e₁, a, he₁, ha, hchk⟩ := of_check hc
  obtain ⟨e₃, he₃, hpost⟩ := Straight.of_check _ _ _ hchk
  let V : Nat → Lane := fun i => if i = 25 then rc else s.mem.readW (wordAddr src i) 64
  have hV : ∀ i (hi : i < 25), V i = A[i] ^^^ msk i := fun i hi => by
    simp only [V, show i ≠ 25 by omega, ite_false]
    rw [← cmpl_get A hi]; exact hA i hi
  have hV25 : V 25 = rc := by simp [V]
  have hok : Ok (cfg sR dR) s :=
    { slotIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hd]; exact he.dst_out j hj
      extIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hs]; exact he.src_in j hj
      baseAl := by simp only [cfg]; rw [hd]; exact hdal
      extAl := by simp only [cfg]; rw [hs]; exact hsal
      slots := by simp only [cfg]; decide
      sep := fun j hj i hi => by
        simp only [cfg] at hj hi ⊢; rw [hd, hs]
        exact Region.Disjoint.sep he.dst_src (Proof.Sha3.lane_contains dst hj)
          (Proof.Sha3.lane_contains src hi) }
  have hrel : Rel (AnfRel V) (cfg sR dR) ext env₀ s :=
    { reg := fun r a h => by
        obtain ⟨x, hx, rfl, rfl⟩ := env₀_reg h
        simp only [ValRel, AnfRel, eval_atom, V, show 20 + x ≠ 25 by omega, ite_false]
        rw [hrow x hx]; exact hA _ (by omega)
      slot := fun _ _ _ h => by cases h
      ext := fun j a hj h => by
        simp only [ext, Option.some.injEq] at h; subst h
        simp only [cfg] at hj ⊢
        simp only [AnfRel, eval_atom, V, show j ≠ 25 by omega, ite_false, hs] }
  obtain ⟨s₁, hs₁, p₁⟩ := Straight.run (anf_sound V) (anfRel_fun V) hok hrel he₁
  have hk' : ∀ r ∈ kept, (roundA sR).all (fun i => Straight.dst i != some r) = true ∧
      (roundB sR dR).all (fun i => Straight.dst i != some r) = true := fun r hr => by
    simp only [keeps, List.all_append, Bool.and_eq_true, List.all_eq_true] at hk
    exact ⟨List.all_eq_true.mpr fun i hi => hk.1 i hi r hr, List.all_eq_true.mpr fun i hi => hk.2 i hi r hr⟩
  have k₁ : ∀ r ∈ kept, s₁.gpr r = s.gpr r := fun r hr =>
    p₁.other r (by rw [(hk' r hr).1]; decide)
  -- ι
  have hrcp : s₁.gpr .s0 + BitVec.ofNat 64 (8 * k) = s.gpr .s0 + BitVec.ofNat 64 (8 * k) := by
    rw [k₁ .s0 (by decide)]
  have hrc₁ : s₁.mem.readW (s.gpr .s0 + BitVec.ofNat 64 (8 * k)) 64 = rc := by
    rw [p₁.frame.readW (Region.contains_self _ _) ?_ (by decide), hrc]
    simp only [slotRegion, cfg, List.mem_singleton, forall_eq, hd]
    exact he.dst_rc.symm
  have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s.gpr .s0 + BitVec.ofNat 64 (8 * k)) 8 := by
    rw [p₁.rd, p₁.wr]; exact he.rc_in
  let s₂ := s₁.write .t6 rc
  let s₃ := s₂.write .t0 (s₂.gpr .t0 ^^^ s₂.gpr .t6)
  have hexec : runBlock isa (iota k) s₁ = some s₃ := by
    simp only [iota, T, runBlock_cons, runStep_some, runBlock_nil, isa,
      exec_load_d hk8 (by rw [hrcp]; exact hrcal) (by rw [hrcp]; exact hin₁), hrcp, hrc₁, exec_logic]
    rfl
  have hr0 : ValRel (AnfRel V) (.v (atom 25)) rc := by simp only [ValRel, AnfRel, eval_atom, hV25]
  have hr11 : ValRel (AnfRel V) (.v (pxor a (atom 25))) (s₁.gpr .t0 ^^^ rc) := by
    have := p₁.rel.reg _ _ ha
    simp only [ValRel, AnfRel] at this ⊢
    rw [eval_pxor, eval_atom, hV25, this]
  have hb₁ : ∀ r, r = Reg.t6 ∨ r = .t0 → r ≠ (cfg sR dR).base ∧ r ≠ (cfg sR dR).ext := by
    rintro r (rfl | rfl) <;> simp only [cfg] <;> refine ⟨fun h => ?_, fun h => ?_⟩ <;> subst h <;>
      simp_all [kept]
  have p₂ := post_write p₁.ok p₁.rel hr0 (hb₁ .t6 (.inl rfl)).1 (hb₁ .t6 (.inl rfl)).2
  have p₂' := post_write p₂.ok p₂.rel (v := s₂.gpr .t0 ^^^ s₂.gpr .t6) (by
      simp only [s₂, State.write, show Reg.t0 ≠ .t6 by decide, ite_false, ite_true]; exact hr11)
    (hb₁ .t0 (.inr rfl)).1 (hb₁ .t0 (.inr rfl)).2
  obtain ⟨s₄, hs₄, p₄⟩ := Straight.run (anf_sound V) (anfRel_fun V) p₂'.ok p₂'.rel he₃
  have hbase : s₄.gpr dR = dst := by
    have := p₄.base.trans (p₂'.base.trans (p₂.base.trans p₁.base))
    simp only [cfg] at this; rw [this, hd]
  unfold round
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.of_runBlock ⟨s₁, hs₁, WP.of_runBlock ⟨s₃, hexec, WP.of_runBlock ⟨s₄, hs₄, ?_⟩⟩⟩
  simp only [post, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hpost
  refine ⟨fun i hi => ?_, fun x hx => ?_, ?_, p₄.rd.trans (p₂'.rd.trans (p₂.rd.trans p₁.rd)),
    p₄.wr.trans (p₂'.wr.trans (p₂.wr.trans p₁.wr)), p₄.sp.trans (p₂'.sp.trans (p₂.sp.trans p₁.sp)),
    fun r hr => ?_⟩
  · have h := p₄.rel.slot i _ (by simp only [cfg]; exact hi) (hpost.1 i hi)
    simp only [AnfRel, eval_specP hV hV25 hi, cfg, hbase] at h
    exact h.symm
  · have h := p₄.rel.reg _ _ (hpost.2 x hx)
    simp only [ValRel, AnfRel, eval_specP hV hV25 (show 20 + x < 25 by omega)] at h
    exact h.symm
  · have f₁ := p₁.frame
    have f₄ := p₄.frame
    have hb₂ : s₃.gpr dR = dst := by
      have := p₂'.base.trans (p₂.base.trans p₁.base); simp only [cfg] at this; rw [this, hd]
    simp only [slotRegion, cfg, hd] at f₁ f₄
    rw [hb₂] at f₄
    exact f₁.trans f₄
  · have h0 : r ≠ .t6 := fun h => by subst h; simp [kept] at hr
    have h11 : r ≠ .t0 := fun h => by subst h; simp [kept] at hr
    rw [p₄.other r (by rw [(hk' r hr).2]; decide), p₂'.other r h11, p₂.other r h0, k₁ r hr]

deriving instance Lean.ToExpr for Poly

/- `specP` reads the tables of `sD` and `sB`, so that the kernel evaluates each of their
values once, not once for each lane that uses it. -/
materialize_table Compl.sD 5
materialize_table Compl.sB 5 5
materialize_table specP 25

theorem check₀ : check .a0 .a1 = true := by lit_decide
theorem check₁ : check .a1 .a0 = true := by lit_decide
theorem keeps₀ : keeps .a0 .a1 = true := by decide +kernel
theorem keeps₁ : keeps .a1 .a0 = true := by decide +kernel

end VG.Proof.Sha3.RISCV64.Round
