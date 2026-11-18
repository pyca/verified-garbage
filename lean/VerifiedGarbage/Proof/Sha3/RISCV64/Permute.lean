module

public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
import VerifiedGarbage.Proof.Sha3.Stream
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Words64
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Sha3.Contract
meta import VerifiedGarbage.TCB.RISCV64.Target
meta import VerifiedGarbage.Proof.Framework.RISCV64.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Wp
meta import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
meta import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Exec
meta import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
meta import VerifiedGarbage.Proof.Framework.RISCV64.Words64
meta import VerifiedGarbage.Proof.Framework.RISCV64.Inline
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Framework.PowLit
meta import VerifiedGarbage.Spec.Sha3.Contract
meta import VerifiedGarbage.TCB.RISCV64.Isa
meta import VerifiedGarbage.TCB.Artifact
meta import VerifiedGarbage.Proof.Framework.PowLit
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
public import VerifiedGarbage.Proof.Sha3.Compl
public import VerifiedGarbage.Impl.Sha3.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Sha3.ComplLit
meta import VerifiedGarbage.Proof.Framework.RISCV64.Straight
meta import VerifiedGarbage.Proof.Sha3.Compl
meta import VerifiedGarbage.Impl.Sha3.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Sha3.ComplLit

/-! ### `Sha3.RISCV64.Round`, which only this module used -/

section

/-!
# Keccak-f[1600] on RISC-V: a round, by evaluation

As on PPC64LE (`Proof/Sha3/PPC64LE/Stream/Verified.lean`): a round (`round s d k`) is
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
    simp only [V, show i ≠ 25 by omega_using [hi], ite_false]
    rw [← cmpl_get A hi]; exact hA i hi
  have hV25 : V 25 = rc := by simp [V]
  have hok : Ok (cfg sR dR) s :=
    { slotIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hd]; exact he.dst_out j hj
      extIn := fun j hj => by simp only [cfg] at hj ⊢; rw [hs]; exact he.src_in j hj
      baseAl := fun _ => by simp only [cfg]; rw [hd]; exact hdal
      extAl := fun _ => by simp only [cfg]; rw [hs]; exact hsal
      slots := by simp only [cfg]; decide
      sep := fun j hj i hi => by
        simp only [cfg] at hj hi ⊢; rw [hd, hs]
        exact Region.Disjoint.sep he.dst_src (Proof.Sha3.lane_contains dst hj)
          (Proof.Sha3.lane_contains src hi) }
  have hrel : Rel (AnfRel V) (cfg sR dR) ext env₀ s :=
    { reg := fun r a h => by
        obtain ⟨x, hx, rfl, rfl⟩ := env₀_reg h
        simp only [ValRel, AnfRel, eval_atom, V, show 20 + x ≠ 25 by omega_using [hx], ite_false]
        rw [hrow x hx]; exact hA _ (by omega_using [hx])
      slot := fun _ _ _ h => by cases h
      ext := fun j a hj h => by
        simp only [ext, Option.some.injEq] at h; subst h
        simp only [cfg] at hj ⊢
        simp only [AnfRel, eval_atom, V, show j ≠ 25 by omega_using [hj], ite_false, hs] }
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
    simp only [ValRel, AnfRel, eval_specP hV hV25 (show 20 + x < 25 by omega_using [hx])] at h
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

theorem check₀ : check .a0 .a1 = true := by lit_decide
theorem check₁ : check .a1 .a0 = true := by lit_decide
theorem keeps₀ : keeps .a0 .a1 = true := by decide +kernel
theorem keeps₁ : keeps .a1 .a0 = true := by decide +kernel

end VG.Proof.Sha3.RISCV64.Round

end

end

/-! ### `Sha3.RISCV64.Contract`, which this module and modules that import it used -/

section

/-!
# SHA-3 on RISC-V: the contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/Sha3/Contract.lean`, which
imply these, with the arguments where the psABI passes them. The
permutation keeps its working space in a frame of 608 bytes below the stack
pointer (`Impl.Sha3.RISCV64.frameBytes`); the streaming functions keep the
registers they save in a frame of their own above it
(`Impl.Sha3.RISCV64.Stream.frameBytes`, `padBytes`), and the permutation's
scratch space in a frame between the two, around its call (`scratchBytes`).
-/

@[expose] public section

namespace VG.Proof.Sha3

open Spec.Sha3

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_f1600(state: *mut [u64; 25], scratch: *mut
[u64; 64])`: applies Keccak-f[1600] to the state at `state`.

The code may read and write `state` (200 bytes) and `scratch` (512 bytes,
whose contents on exit are unspecified), which may not overlap each other,
nor the 608 bytes below the stack pointer (its frame), which do not wrap
around. The stack pointer is 16-byte aligned. The pointers are public; the
state is secret. -/
def permuteRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let scratch : Region := ⟨s.gpr .a1, 512⟩
    let stack : Region := ⟨s.sp - 608, 608⟩
    s.rd = [] ∧ s.wr = [state, scratch] ∧ state.Disjoint scratch ∧
    s.sp.toNat % 16 = 0 ∧ 608 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint scratch
  post s s' := stateAt s'.mem (s.gpr .a0) = keccakF (stateAt s.mem (s.gpr .a0))
  pub s₁ s₂ := s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_absorb(state = a0, rate = a1, pos = a2,
data = a3, len = a4) -> a0`: absorbs `data` into the streaming state
(`Repr`) and returns the new position in the block.

The code may read `data`, and read and write `state` (200 bytes), which do
not overlap each other or the 1168 bytes below the stack pointer (its frame
and the permutation's), which do not wrap around. The stack pointer is
16-byte aligned. `rate` is one of `rates`, and `pos < rate`. -/
def absorbRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - 1168, 1168⟩
    s.rd = [data] ∧ s.wr = [state] ∧ data.Disjoint state ∧
    s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧
    (s.gpr .a1).toNat ∈ rates ∧ (s.gpr .a2).toNat < (s.gpr .a1).toNat
  post s s' :=
    (∀ msg, Repr s.mem (s.gpr .a0) (s.gpr .a1).toNat msg →
      (s.gpr .a2).toNat = msg.length % (s.gpr .a1).toNat →
      Repr s'.mem (s.gpr .a0) (s.gpr .a1).toNat
        (msg ++ bytesAt s.mem (s.gpr .a3) (s.gpr .a4).toNat)) ∧
    (s'.gpr .a0).toNat = ((s.gpr .a2).toNat + (s.gpr .a4).toNat) % (s.gpr .a1).toNat
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- `absorbRISCV64` with a working space `scratch` (`a5`, 640 bytes, 8-byte
aligned) that the code may write and leaves unchanged: SHA-3's `update`,
which runs `absorb` with its frames on the stack and does not touch
`scratch`.

The code may read `data`, and read and write `state` (200 bytes) and
`scratch`, none of which overlap each other or the 1168 bytes below the
stack pointer (`absorb`'s frames), which do not wrap around, nor does
`scratch`. The stack pointer is 16-byte aligned. `rate` is one of `rates`,
and `pos < rate`. -/
def absorbScrRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let data : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let scratch : Region := ⟨s.gpr .a5, 640⟩
    let stack : Region := ⟨s.sp - 1168, 1168⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    (s.gpr .a5).toNat % 8 = 0 ∧ (s.gpr .a5).toNat + 640 ≤ 2 ^ 64 ∧
    s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .a1).toNat ∈ rates ∧ (s.gpr .a2).toNat < (s.gpr .a1).toNat
  post s s' := absorbRISCV64.post s s' ∧
    ∀ a, Region.Contains ⟨s.gpr .a5, 640⟩ a 1 → s'.mem a = s.mem a
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.gpr .a5 = s₂.gpr .a5 ∧
    s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_pad(state = a0, rate = a1, pos = a2,
suffix = a3)`: absorbs the padding (with the low byte of `suffix`) into the
streaming state.

The code may read and write `state` (200 bytes), which does not overlap the
1136 bytes below the stack pointer (its frame and the permutation's), which
do not wrap around. The stack pointer is 16-byte aligned. `rate` is one of
`rates`, and `pos < rate`. -/
def padRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let stack : Region := ⟨s.sp - 1136, 1136⟩
    s.rd = [] ∧ s.wr = [state] ∧
    s.sp.toNat % 16 = 0 ∧ 1136 ≤ s.sp.toNat ∧ stack.Disjoint state ∧
    (s.gpr .a1).toNat ∈ rates ∧ (s.gpr .a2).toNat < (s.gpr .a1).toNat
  post s s' := ∀ msg, Repr s.mem (s.gpr .a0) (s.gpr .a1).toNat msg →
    (s.gpr .a2).toNat = msg.length % (s.gpr .a1).toNat →
    stateAt s'.mem (s.gpr .a0) =
      absorb (s.gpr .a1).toNat (pad (s.gpr .a1).toNat ((s.gpr .a3).setWidth 8) msg)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧ s₁.sp = s₂.sp

open VG.RISCV64 in
/-- RISC-V contract for `vg_keccak_squeeze(state = a0, rate = a1, pos = a2,
out = a3, outlen = a4) -> a0`: writes `outlen` bytes of output from byte
`pos` on to `out`, and returns the position after them, leaving a state from
which the output continues.

The code may read and write `state` (200 bytes) and `out` (`outlen` bytes),
which do not overlap each other or the 1168 bytes below the stack pointer
(its frame and the permutation's), which do not wrap around. The stack
pointer is 16-byte aligned. `rate` is one of `rates`, and `pos ≤ rate`. -/
def squeezeRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 200⟩
    let out : Region := ⟨s.gpr .a3, (s.gpr .a4).toNat⟩
    let stack : Region := ⟨s.sp - 1168, 1168⟩
    s.rd = [] ∧ s.wr = [state, out] ∧ state.Disjoint out ∧
    s.sp.toNat % 16 = 0 ∧ 1168 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧
    (s.gpr .a1).toNat ∈ rates ∧ (s.gpr .a2).toNat ≤ (s.gpr .a1).toNat
  post s s' :=
    bytesAt s'.mem (s.gpr .a3) (s.gpr .a4).toNat =
      squeezeFrom (s.gpr .a1).toNat (stateAt s.mem (s.gpr .a0)) (s.gpr .a2).toNat (s.gpr .a4).toNat ∧
    (s'.gpr .a0).toNat ≤ (s.gpr .a1).toNat ∧
    ∀ d, squeezeFrom (s.gpr .a1).toNat (stateAt s'.mem (s.gpr .a0)) (s'.gpr .a0).toNat d =
      squeezeFrom (s.gpr .a1).toNat (stateAt s.mem (s.gpr .a0))
        ((s.gpr .a2).toNat + (s.gpr .a4).toNat) d
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
    s₁.gpr .a3 = s₂.gpr .a3 ∧ s₁.gpr .a4 = s₂.gpr .a4 ∧ s₁.sp = s₂.sp

end VG.Proof.Sha3

end

end

/-!
# Keccak-f[1600] on RISC-V: the whole function

The structure of the PPC64LE proof (`Proof/Sha3/PPC64LE/Stream/Verified.lean`), in a
frame on the stack (`WP.alloc`): the prologue saves `s0` and `s1`, stores
the round constants (`movImm64_ok`) and copies the state into the frame a
byte at a time, complementing the lanes `complLanes` (`loadLE64_ok`); each
iteration of the loop is two rounds (`Round.round_ok`, by evaluation); the
epilogue copies the state back a byte at a time, complementing those lanes
back (`storeLE64_ok`), and restores the registers.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64
open VG.Spec.Sha3 (stateAt keccakF rnd RC)
open VG.Proof.Sha3 (Lanes laneAddr lane_contains foldl_succ)
open VG.Proof.Sha3.RISCV64.Round (rowReg kept round_ok check₀ check₁ keeps₀ keeps₁)
open VG.Proof.Sha3.Compl (cmpl msk)

abbrev KState := Spec.Sha3.State
/-! ## The precondition -/

section
variable (s₀ : State)

/-- The frame's base. -/
abbrev F : Addr := s₀.sp - BitVec.ofNat 64 608
abbrev st : Addr := s₀.gpr .a0
abbrev scr : Addr := s₀.gpr .a1
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev scrR : Region := ⟨scr s₀, 512⟩
abbrev frR : Region := ⟨F s₀, 608⟩
/-- Frame offset `d`. -/
abbrev off (d : Nat) : Addr := F s₀ + BitVec.ofNat 64 d
abbrev A₀ : KState := stateAt s₀.mem (st s₀)
/-- The writable regions in the frame. -/
abbrev W : List Region := [frR s₀, stR s₀, scrR s₀]

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, scrR s₀]
  st_scr : (stR s₀).Disjoint (scrR s₀)
  al : s₀.sp.toNat % 16 = 0
  sp : 608 ≤ s₀.sp.toNat
  fr_st : (frR s₀).Disjoint (stR s₀)
  fr_scr : (frR s₀).Disjoint (scrR s₀)

theorem pre_of (s₀ : State) (h : Proof.Sha3.permuteRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

namespace Pre
variable {s₀ : State} (h : Pre s₀)
include h

theorem F_toNat : (F s₀).toNat = s₀.sp.toNat - 608 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; have := h.sp; omega_using [this]),
    BitVec.toNat_ofNat]

theorem F_al : (F s₀).toNat % 16 = 0 := by
  rw [h.F_toNat]; have := h.al; have := h.sp; omega_arith

theorem al_off {d : Nat} (hd : d % 8 = 0) (hd' : d < 2 ^ 32) : (off s₀ d).toNat % 8 = 0 :=
  al8 h.F_al hd hd'

theorem fr_st' : ∀ r ∈ [frR s₀], (stR s₀).Disjoint r := by
  intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact h.fr_st.symm

end Pre

theorem in_fr (s₀ : State) {d : Nat} (hd : d + 8 ≤ 608) : InRegions (W s₀) (off s₀ d) 8 :=
  ⟨frR s₀, List.mem_cons_self .., Offset.contains_base _ hd (by omega_using [hd])⟩

theorem in_st (s₀ : State) {i : Nat} (hi : i < 25) : InRegions (W s₀) (laneAddr (st s₀) i) 8 :=
  ⟨stR s₀, by simp, lane_contains _ hi⟩

theorem off_add (s₀ : State) (a b : Nat) : off s₀ a + BitVec.ofNat 64 b = off s₀ (a + b) := by
  simp only [off]; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem laneAddr_off (s₀ : State) (a i : Nat) : laneAddr (off s₀ a) i = off s₀ (a + 8 * i) :=
  off_add s₀ a (8 * i)

/-- Frame words at separate offsets. -/
theorem rw_off (s₀ : State) (m : Mem) {d e : Nat} (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 32)
    (he : e + 8 ≤ 2 ^ 32) (v : BitVec 64) :
    (m.writeW (off s₀ d) v).readW (off s₀ e) 64 = m.readW (off s₀ e) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ (by omega_using [h]) (by omega_using [he]) (by omega_using [hd])) (by decide)

theorem frame_off {s₀ : State} {m m' : Mem} (hf : Frame [frR s₀] m m') {d : Nat} (hd : d + 8 ≤ 608)
    (v : BitVec 64) : Frame [frR s₀] m (m'.writeW (off s₀ d) v) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ hd (by omega_using [hd]))

/-! ## The frame's contents -/

/-- The saved registers, and the round constants. -/
def Aux (s₀ : State) (m : Mem) : Prop :=
  m.readW (off s₀ 592) 64 = s₀.gpr .s0 ∧ m.readW (off s₀ 600) 64 = s₀.gpr .s1 ∧
    ∀ j < 24, m.readW (off s₀ (8 * j)) 64 = RC j

/-- Writes to a region disjoint from the constants and the saved registers keep them. -/
theorem Aux.frame {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {R : Region}
    (hR : ∀ d, (d + 8 ≤ 192 ∨ 592 ≤ d) → d + 8 ≤ 608 → Region.Disjoint ⟨off s₀ d, 8⟩ R)
    (hf : Frame [R] m m') : Aux s₀ m' := by
  have e : ∀ d, (d + 8 ≤ 192 ∨ 592 ≤ d) → d + 8 ≤ 608 → m'.readW (off s₀ d) 64 = m.readW (off s₀ d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (by simpa using hR d h₁ h₂) (by decide)
  refine ⟨?_, ?_, fun j hj => ?_⟩
  · rw [e 592 (by omega_using []) (by omega_using [])]; exact h.1
  · rw [e 600 (by omega_using []) (by omega_using [])]; exact h.2.1
  · rw [e (8 * j) (by omega_using [hj]) (by omega_using [hj])]; exact h.2.2 j hj

/-- The copies of the state in the frame, at offsets 192 and 392, are
disjoint from the constants and the saved registers. -/
theorem copy_disjoint (s₀ : State) {a : Nat} (ha : a = 192 ∨ a = 392) {d : Nat}
    (hd : d + 8 ≤ 192 ∨ 592 ≤ d) (hd' : d + 8 ≤ 608) :
    Region.Disjoint ⟨off s₀ d, 8⟩ ⟨off s₀ a, 200⟩ :=
  Offset.disjoint _ (by omega_using [ha, hd]) (by omega_using [hd']) (by omega_using [ha])

/-! ## The prologue -/

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    {s : State} (hg : s.gpr = s₀.gpr) (hrd : s.rd = []) (hwr : s.wr = W s₀) (hsp : s.sp = F s₀)
    (hm : s.mem = s₀.mem)
    (k : ∀ s', s'.gpr .t6 = F s₀ → s'.gpr .s1 = st s₀ → s'.rd = [] → s'.wr = W s₀ →
      s'.sp = F s₀ → s'.mem.readW (off s₀ 592) 64 = s₀.gpr .s0 →
      s'.mem.readW (off s₀ 600) 64 = s₀.gpr .s1 → Frame [frR s₀] s₀.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  simp only [save, List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  have h6 : s₁.gpr .t6 = F s₀ := by rw [u₁.gpr, hsp]; exact BitVec.add_zero _
  refine wp_sd (by decide) (a := off s₀ 592) (by rw [h6]) (hp.al_off (by decide) (by decide))
    (by rw [u₁.wr, hwr]; exact in_fr s₀ (by decide)) fun s₂ g₂ => ?_
  refine wp_sd (by decide) (a := off s₀ 600) (by rw [g₂.gpr, h6])
    (hp.al_off (by decide) (by decide))
    (by rw [g₂.wr, u₁.wr, hwr]; exact in_fr s₀ (by decide)) fun s₃ g₃ => ?_
  refine wp_mv fun s₄ u₄ => ?_
  have g₂₃ : s₃.gpr = s₁.gpr := by rw [g₃.gpr, g₂.gpr]
  refine k s₄ (by rw [u₄.other _ (by decide), g₂₃, h6]) (by rw [u₄.gpr, g₂₃, u₁.other _ (by decide), hg])
    (by rw [u₄.rd, g₃.rd, g₂.rd, u₁.rd, hrd]) (by rw [u₄.wr, g₃.wr, g₂.wr, u₁.wr, hwr])
    (by rw [u₄.sp, g₃.sp, g₂.sp, u₁.sp, hsp]) ?_ ?_ ?_
  · rw [u₄.mem, g₃.mem, g₂.mem, rw_off s₀ _ (by omega_using []) (by omega_using []) (by omega_using []),
      Mem.readW_writeW_self64, u₁.other _ (by decide), hg]
  · rw [u₄.mem, g₃.mem, Mem.readW_writeW_self64, g₂.gpr, u₁.other _ (by decide), hg]
  · rw [u₄.mem, g₃.mem, g₂.mem, u₁.mem, hm]
    exact frame_off (frame_off (Frame.refl _ _) (by omega_using []) _) (by omega_using []) _

/-! ## The round constants -/

/-- The fold of `Spec.Sha3.RC` on any seven bits, as `rcBuild` builds it. -/
theorem rc_fold (b0 b1 b2 b3 b4 b5 b6 : Bool) :
    (List.range 7).foldl (fun RC j => if [b0, b1, b2, b3, b4, b5, b6].getD j false then
        RC ||| (1#64 <<< (2 ^ j - 1)) else RC) 0 =
      ((BitVec.ofNat 64 ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 8 else 0) +
          (if b3 then 128 else 0)) |||
        (if b4 then 1#64 <<< 15 else 0)) ||| (if b5 then 1#64 <<< 31 else 0)) |||
        (if b6 then 1#64 <<< 63 else 0) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> decide

/-- `RC k` as `rcBuild` builds it: the four low bits as a number, then bits
15, 31 and 63. -/
theorem rc_eq (k : Nat) :
    RC k = ((BitVec.ofNat 64 (rcLo k) ||| (if rcBit k 4 then 1#64 <<< 15 else 0)) |||
      (if rcBit k 5 then 1#64 <<< 31 else 0)) ||| (if rcBit k 6 then 1#64 <<< 63 else 0) :=
  rc_fold (rcBit k 0) (rcBit k 1) (rcBit k 2) (rcBit k 3) (rcBit k 4) (rcBit k 5) (rcBit k 6)

theorem rcLo_lt (k : Nat) : rcLo k < 2048 := by
  unfold rcLo; split <;> split <;> split <;> split <;> omega_using []

/-- `orIf`: `t0 |= r` if `b`. -/
theorem orIf_ok {b : Bool} {r : Reg} {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' .t0 (s.gpr .t0 ||| (if b then s.gpr r else 0)) → WP isa (.block is) s' Q) :
    WP isa (.block (orIf b r ++ is)) s Q := by
  cases b
  · exact k s ⟨by simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  · exact WP.cons exec_logic (by simpa using k _ (Upd.write _ _ _))

/-- `rcHigh`: bits 15, 31 and 63 in `t3`, `t4` and `t5`. -/
theorem rcHigh_ok {s : State} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .t3 = 1#64 <<< 15 → s'.gpr .t4 = 1#64 <<< 31 → s'.gpr .t5 = 1#64 <<< 63 →
      (∀ r, r ≠ .t3 → r ≠ .t4 → r ≠ .t5 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (rcHigh ++ is)) s Q := by
  simp only [rcHigh, List.cons_append, List.nil_append]
  refine WP.cons exec_lui ?_
  have u₁ := Upd.write s .t3 (sext32 ((8 : BitVec 20) ++ (0 : BitVec 12)))
  generalize s.write .t3 _ = s₁ at u₁ ⊢
  refine wp_li (imm := 1) (by decide) fun s₂ u₂ => Steps.wp_sll (by decide) fun s₃ u₃ =>
    Steps.wp_sll (by decide) fun s₄ u₄ => ?_
  have e4 : s₄.gpr .t4 = 1#64 <<< 31 := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr]
  refine k s₄ ?_ e4 ?_ (fun r h3 h4 h5 => ?_) ?_ ?_ ?_ ?_
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; decide
  · rw [u₄.gpr, u₃.gpr, u₂.gpr]; decide
  · rw [u₄.other r h5, u₃.other r h4, u₂.other r h4, u₁.other r h3]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- `rcBuild k`: `RC k` in `t0`, from bits 15, 31 and 63 in `t3`–`t5`. -/
theorem rcBuild_ok (k : Nat) {s : State} (h3 : s.gpr .t3 = 1#64 <<< 15) (h4 : s.gpr .t4 = 1#64 <<< 31)
    (h5 : s.gpr .t5 = 1#64 <<< 63) {is : List Instr} {Q : State → Prop}
    (kk : ∀ s', s'.gpr .t0 = RC k → (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block is) s' Q) :
    WP isa (.block (rcBuild k ++ is)) s Q := by
  simp only [rcBuild, List.cons_append, List.append_assoc]
  refine wp_li (rcLo_lt k) fun s₁ u₁ => orIf_ok fun s₂ u₂ => orIf_ok fun s₃ u₃ =>
    orIf_ok fun s₄ u₄ => kk s₄ ?_ (fun r h => ?_) ?_ ?_ ?_ ?_
  · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), u₁.other _ (by decide),
      h3, h4, h5, rc_eq]
  · rw [u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  · rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [u₄.sp, u₃.sp, u₂.sp, u₁.sp]

/-- During the stores of the round constants. -/
def RcInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .t6 = F s₀ ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    s.mem.readW (off s₀ 592) 64 = s₀.gpr .s0 ∧ s.mem.readW (off s₀ 600) 64 = s₀.gpr .s1 ∧
    (∀ j < k, s.mem.readW (off s₀ (8 * j)) 64 = RC j) ∧ Frame [frR s₀] s₀.mem s.mem

/-- `t3`–`t5` hold bits 15, 31 and 63. -/
def High (s : State) : Prop :=
  s.gpr .t3 = 1#64 <<< 15 ∧ s.gpr .t4 = 1#64 <<< 31 ∧ s.gpr .t5 = 1#64 <<< 63

theorem rcs_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : RcInv s₀ 0 s) :
    WP isa (.block rcStores) s (RcInv s₀ 24) := by
  unfold rcStores
  refine rcHigh_ok fun s₁ e3 e4 e5 o m rd wr sp => ?_
  obtain ⟨h6, h1, hrd, hwr, hsp, v₁, v₂, _, hf⟩ := hs
  refine WP.mono (wp_range_flatMap (M := isa) (fun k s => RcInv s₀ k s ∧ High s)
    (fun k s' hk ⟨⟨h6, h1, hrd, hwr, hsp, v₁, v₂, hv, hf⟩, e3, e4, e5⟩ => ?_) 24 (Nat.le_refl _) s₁
    ⟨⟨by rw [o _ (by decide) (by decide) (by decide), h6],
      by rw [o _ (by decide) (by decide) (by decide), h1], by rw [rd, hrd], by rw [wr, hwr],
      by rw [sp, hsp], by rw [m, v₁], by rw [m, v₂], fun j hj => absurd hj (Nat.not_lt_zero _),
      by rw [m]; exact hf⟩, e3, e4, e5⟩) fun _ h => h.1
  refine rcBuild_ok k e3 e4 e5 fun s₁ g₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  refine wp_sd (by omega_using [hk]) (a := off s₀ (8 * k)) (by rw [o₁ _ (by decide), h6])
    (hp.al_off (by omega_using []) (by omega_using [hk])) (by rw [wr₁, hwr]; exact in_fr s₀ (by omega_using [hk])) fun s₂ g₂ => ?_
  refine WP.block_nil ⟨⟨by rw [g₂.gpr, o₁ _ (by decide), h6],
    by rw [g₂.gpr, o₁ _ (by decide), h1], by rw [g₂.rd, rd₁, hrd],
    by rw [g₂.wr, wr₁, hwr], by rw [g₂.sp, sp₁, hsp], ?_, ?_, fun j hj => ?_, ?_⟩,
    by rw [g₂.gpr, o₁ _ (by decide), e3], by rw [g₂.gpr, o₁ _ (by decide), e4],
    by rw [g₂.gpr, o₁ _ (by decide), e5]⟩
  · rw [g₂.mem, rw_off s₀ _ (by omega_using [hk]) (by omega_using [hk]) (by omega_using []), m₁, v₁]
  · rw [g₂.mem, rw_off s₀ _ (by omega_using [hk]) (by omega_using [hk]) (by omega_using []), m₁, v₂]
  · rw [g₂.mem]
    by_cases e : j = k
    · subst e; rw [Mem.readW_writeW_self64, g₁]
    · rw [rw_off s₀ _ (by omega_using [e]) (by omega_using [hk]) (by omega_using [hk, hj]), m₁]; exact hv j (by omega_using [hj, e])
  · rw [g₂.mem, m₁]; exact frame_off hf (by omega_using [hk]) _

/-- `laneReg` is none of the registers the copies use besides. -/
theorem laneReg_ne : ∀ i < 25, laneReg i ≠ .t1 ∧ laneReg i ≠ .t2 ∧ laneReg i ≠ .s1 ∧ laneReg i ≠ .t6 := by
  decide

theorem laneReg_row : ∀ x < 5, laneReg (20 + x) = rowReg x := by decide

theorem laneReg_ne_row : ∀ i < 25, ∀ x < 5, 20 + x < i → laneReg i ≠ rowReg x := by decide

theorem row_ne : ∀ x < 5, rowReg x ≠ .t1 ∧ rowReg x ≠ .t2 := by decide

/-- A NOT of lane `i` if it is kept complemented. -/
theorem cmplLane_ok {s : State} {r : Reg} {i : Nat} {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' r (s.gpr r ^^^ msk i) → WP isa (.block is) s' Q) :
    WP isa (.block (cmplLane r i ++ is)) s Q := by
  unfold cmplLane
  split
  · rename_i hc
    have e : msk i = BitVec.allOnes 64 := by simp only [msk, hc, ite_true]
    exact wp_not fun s' u => k s' (e ▸ u)
  · rename_i hc
    have e : msk i = 0 := by simp only [msk, hc, Bool.false_eq_true, ite_false]
    exact k s ⟨by rw [e]; simp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-- During the copies of the lanes into the frame. -/
def CInv (s₀ : State) (k : Nat) (s : State) : Prop :=
  s.gpr .t6 = F s₀ ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    Aux s₀ s.mem ∧ Frame [frR s₀] s₀.mem s.mem ∧
    (∀ j (hj : j < 25), j < k → s.mem.readW (off s₀ (192 + 8 * j)) 64 = (cmpl (A₀ s₀))[j]) ∧
    ∀ x (hx : x < 5), 20 + x < k → s.gpr (rowReg x) = (cmpl (A₀ s₀))[20 + x]

theorem lane₀ (s₀ : State) {m : Mem} (hp : Pre s₀) (hf : Frame [frR s₀] s₀.mem m) {i : Nat}
    (hi : i < 25) : m.readW (laneAddr (st s₀) i) 64 = (A₀ s₀)[i] := by
  rw [hf.readW (lane_contains _ hi) hp.fr_st' (by decide)]
  simp [Spec.Sha3.stateAt, laneAddr]

theorem copyIns_ok {s₀ : State} (hp : Pre s₀) (s : State) (hs : CInv s₀ 0 s) :
    WP isa (.block ((List.range 25).flatMap copyIn)) s (CInv s₀ 25) := by
  refine wp_range_flatMap (M := isa) (CInv s₀)
    (fun i s' hi ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow⟩ => ?_) 25 (Nat.le_refl _) s hs
  obtain ⟨n1, n2, ns, n6⟩ := laneReg_ne i hi
  unfold copyIn
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (Words64.loadLE64_ok (d := laneReg i) (tmp := .t1) (tmp2 := .t2) (n := .s1)
    (off := 8 * i) ns (by decide) n1 (by decide) (by decide) n2 (by omega_using [hi])
    (by rw [hrd, hwr, h1]; exact in_st s₀ hi)) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr (laneReg i) = (cmpl (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, h1, ← laneAddr, lane₀ s₀ hp hf hi, Round.cmpl_get _ hi]
  have g6 : s₂.gpr .t6 = F s₀ := by
    rw [u₂.other _ (Ne.symm n6), u₁.other _ (Ne.symm n6) (by decide) (by decide), h6]
  refine wp_sd (by simp only [stOff]; omega_using [hi]) (a := off s₀ (192 + 8 * i)) (by rw [g6]; rfl) (hp.al_off (by omega_using []) (by omega_using [hi]))
    (by rw [u₂.wr, u₁.wr, hwr]; exact in_fr s₀ (by omega_using [hi])) fun s₃ g₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [g₃.gpr, g6], by rw [g₃.gpr, u₂.other _ (Ne.symm ns), u₁.other _ (Ne.symm ns)
      (by decide) (by decide), h1], by rw [g₃.rd, u₂.rd, u₁.rd, hrd], by rw [g₃.wr, u₂.wr, u₁.wr, hwr],
    by rw [g₃.sp, u₂.sp, u₁.sp, hsp], ?_, ?_, fun j hj hji => ?_, fun x hx hxi => ?_⟩
  · rw [g₃.mem, m₂]
    exact haux.frame (fun d h₁ h₂ => copy_disjoint s₀ (.inl rfl) h₁ h₂ |>.sub_right
      (Offset.sub _ (by omega_using []) (by omega_using [hi]))) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _))
  · rw [g₃.mem, m₂]; exact frame_off hf (by omega_using [hi]) _
  · rw [g₃.mem, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [rw_off s₀ _ (by omega_using [e]) (by omega_using [hi]) (by omega_using [hj])]; exact hl j hj (by omega_using [hji, e])
  · rw [g₃.gpr]
    by_cases e : 20 + x = i
    · subst e; rw [← laneReg_row x hx]; exact hv
    · have hne : rowReg x ≠ laneReg i := fun h => laneReg_ne_row i hi x hx (by omega_using [hxi, e]) h.symm
      have hrn := row_ne x hx
      rw [u₂.other _ hne, u₁.other _ hne hrn.1 hrn.2]
      exact hrow x hx (by omega_using [hxi, e])

/-- A lane of an 8-byte aligned state is aligned. -/
theorem al_lane {p : Addr} (h : p.toNat % 8 = 0) (i : Nat) : (laneAddr p i).toNat % 8 = 0 := by
  rw [laneAddr, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_using [h]

/-- `x & 7` is zero exactly when `x` is 8-byte aligned. -/
theorem and7 (x : BitVec 64) : (x &&& BitVec.ofInt 64 7 == 0) = decide (x.toNat % 8 = 0) := by
  have e : (x &&& BitVec.ofInt 64 7).toNat = x.toNat % 8 := by
    rw [BitVec.toNat_and, show (BitVec.ofInt 64 7).toNat = 2 ^ 3 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  by_cases h : x.toNat % 8 = 0
  · rw [decide_eq_true h, beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by rw [e, h]; rfl)
  · rw [decide_eq_false h]
    exact beq_false_of_ne fun h' => h (by rw [← e, h']; rfl)

/-- The copies into the frame of an 8-byte aligned state. -/
theorem copyInsA_ok {s₀ : State} (hp : Pre s₀) (hal : (st s₀).toNat % 8 = 0) (s : State) (hs : CInv s₀ 0 s) :
    WP isa (.block ((List.range 25).flatMap copyInA)) s (CInv s₀ 25) := by
  refine wp_range_flatMap (M := isa) (CInv s₀)
    (fun i s' hi ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow⟩ => ?_) 25 (Nat.le_refl _) s hs
  obtain ⟨n1, n2, ns, n6⟩ := laneReg_ne i hi
  unfold copyInA ld
  rw [List.cons_append]
  refine wp_ld (by omega_using [hi]) (a := laneAddr (st s₀) i) (by rw [h1]) (al_lane hal i)
    (by rw [hrd, hwr]; exact in_st s₀ hi) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr (laneReg i) = (cmpl (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, lane₀ s₀ hp hf hi, Round.cmpl_get _ hi]
  have g6 : s₂.gpr .t6 = F s₀ := by
    rw [u₂.other _ (Ne.symm n6), u₁.other _ (Ne.symm n6), h6]
  refine wp_sd (by simp only [stOff]; omega_using [hi]) (a := off s₀ (192 + 8 * i)) (by rw [g6]; rfl) (hp.al_off (by omega_using []) (by omega_using [hi]))
    (by rw [u₂.wr, u₁.wr, hwr]; exact in_fr s₀ (by omega_using [hi])) fun s₃ g₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [g₃.gpr, g6], by rw [g₃.gpr, u₂.other _ (Ne.symm ns), u₁.other _ (Ne.symm ns), h1],
    by rw [g₃.rd, u₂.rd, u₁.rd, hrd], by rw [g₃.wr, u₂.wr, u₁.wr, hwr],
    by rw [g₃.sp, u₂.sp, u₁.sp, hsp], ?_, ?_, fun j hj hji => ?_, fun x hx hxi => ?_⟩
  · rw [g₃.mem, m₂]
    exact haux.frame (fun d h₁ h₂ => copy_disjoint s₀ (.inl rfl) h₁ h₂ |>.sub_right
      (Offset.sub _ (by omega_using []) (by omega_using [hi]))) ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Region.contains_self _ _))
  · rw [g₃.mem, m₂]; exact frame_off hf (by omega_using [hi]) _
  · rw [g₃.mem, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [rw_off s₀ _ (by omega_using [e]) (by omega_using [hi]) (by omega_using [hj])]; exact hl j hj (by omega_using [hji, e])
  · rw [g₃.gpr]
    by_cases e : 20 + x = i
    · subst e; rw [← laneReg_row x hx]; exact hv
    · have hne : rowReg x ≠ laneReg i := fun h => laneReg_ne_row i hi x hx (by omega_using [hxi, e]) h.symm
      rw [u₂.other _ hne, u₁.other _ hne]
      exact hrow x hx (by omega_using [hxi, e])

/-! ## The rounds -/

/-- The rounds' invariant, before iteration `j` (round `2j`): the state,
with the lanes `complLanes` complemented, in the frame at offset 192, and
its row 4 in `rowReg`. -/
structure LInv (s₀ : State) (j : Nat) (s : State) : Prop where
  a0 : s.gpr .a0 = off s₀ 192
  a1 : s.gpr .a1 = off s₀ 392
  s0 : s.gpr .s0 = off s₀ (16 * j)
  s1 : s.gpr .s1 = st s₀
  rd : s.rd = []
  wr : s.wr = W s₀
  sp : s.sp = F s₀
  state : Lanes s.mem (off s₀ 192) (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))
  row : ∀ x (hx : x < 5), s.gpr (rowReg x) = (cmpl ((List.range (2 * j)).foldl rnd (A₀ s₀)))[20 + x]
  aux : Aux s₀ s.mem
  frame : Frame [frR s₀] s₀.mem s.mem

theorem pointers_ok {s₀ : State} {s : State} (hs : CInv s₀ 25 s) :
    WP isa (.block pointers) s (LInv s₀ 0) := by
  obtain ⟨h6, h1, hrd, hwr, hsp, haux, hf, hl, hrow⟩ := hs
  simp only [pointers]
  refine wp_addSp (by decide) fun s₁ u₁ => wp_addSp (by decide) fun s₂ u₂ => wp_mv fun s₃ u₃ =>
    WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hsp]; rfl,
    by rw [u₃.other _ (by decide), u₂.gpr, u₁.sp, hsp]; rfl,
    by rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h6]; exact (BitVec.add_zero _).symm,
    by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h1],
    by rw [u₃.rd, u₂.rd, u₁.rd, hrd], by rw [u₃.wr, u₂.wr, u₁.wr, hwr],
    by rw [u₃.sp, u₂.sp, u₁.sp, hsp], fun i hi => ?_, fun x hx => ?_, m₃ ▸ haux, m₃ ▸ hf⟩
  · rw [m₃, laneAddr_off]; exact hl i hi (by omega_using [hi])
  · have : rowReg x ≠ .s0 ∧ rowReg x ≠ .a1 ∧ rowReg x ≠ .a0 := by revert x; decide
    rw [u₃.other _ this.1, u₂.other _ this.2.1, u₁.other _ this.2.2]
    exact hrow x hx (by omega_using [hx])

/-- Where a round reads and writes. -/
theorem env (s₀ : State) {a b : Nat} (ha : a = 192 ∧ b = 392 ∨ a = 392 ∧ b = 192)
    {r : Nat} (hr : r < 24) :
    Proof.Sha3.Env [] (W s₀) (off s₀ a) (off s₀ b) (off s₀ (8 * r)) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, in_fr s₀ (by omega_using [hr]), Offset.disjoint _ (by omega_using [ha]) (by omega_using [ha])
    (by omega_using [ha]), Offset.disjoint _ (by omega_using [ha, hr]) (by omega_using [ha]) (by omega_using [hr])⟩
  · rw [laneAddr_off]; exact in_fr s₀ (by omega_using [ha, hi])
  · rw [laneAddr_off]; exact in_fr s₀ (by omega_using [ha, hi])

theorem foldl_two (A : KState) (j : Nat) :
    (List.range (2 * (j + 1))).foldl rnd A = rnd (rnd ((List.range (2 * j)).foldl rnd A) (2 * j)) (2 * j + 1) := by
  rw [show 2 * (j + 1) = 2 * j + 1 + 1 by omega_using [], foldl_succ, foldl_succ]

theorem off_ne (s₀ : State) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (off s₀ a != off s₀ b) = !decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    exact Offset.add_ofNat_ne _ ha hb h

/-- The round's writes keep the frame's constants and saved registers. -/
theorem aux_round {s₀ : State} {m m' : Mem} (h : Aux s₀ m) {b : Nat} (hb : b = 192 ∨ b = 392)
    (hf : Frame [⟨off s₀ b, 200⟩] m m') : Aux s₀ m' :=
  h.frame (fun _ h₁ h₂ => copy_disjoint s₀ hb h₁ h₂) hf

theorem frame_round {s₀ : State} {m m' : Mem} (hf₀ : Frame [frR s₀] s₀.mem m) {b : Nat}
    (hb : b + 200 ≤ 608) (hf : Frame [⟨off s₀ b, 200⟩] m m') : Frame [frR s₀] s₀.mem m' :=
  hf₀.trans (hf.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨frR s₀, List.mem_singleton_self _, Offset.sub_base _ hb⟩)

/-- Two rounds, from iteration `j`. -/
theorem body_ok {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 12) {s : State} (hL : LInv s₀ j s) :
    WP isa (.block body) s fun s' =>
      eval (.ne .s0 .a0) s' = some (!decide (j + 1 = 12)) ∧ LInv s₀ (j + 1) s' := by
  unfold body
  rw [WP.block_append_iff, WP.block_append_iff]
  have he₀ := env s₀ (a := 192) (b := 392) (.inl ⟨rfl, rfl⟩) (r := 2 * j) (by omega_using [hj])
  have he₁ := env s₀ (a := 392) (b := 192) (.inr ⟨rfl, rfl⟩) (r := 2 * j + 1) (by omega_using [hj])
  have ea₀ : s.gpr .s0 + BitVec.ofNat 64 (8 * 0) = off s₀ (8 * (2 * j)) := by
    rw [hL.s0, off_add, show 16 * j + 8 * 0 = 8 * (2 * j) by omega_using []]
  refine WP.mono (round_ok check₀ keeps₀ (by decide) (by decide) 0 (by decide) (rc := RC (2 * j))
    (src := off s₀ 192) (dst := off s₀ 392) hL.a0 hL.a1 (hp.al_off (by decide) (by decide))
    (hp.al_off (by decide) (by decide)) (by rw [ea₀]; exact hp.al_off (by omega_using []) (by omega_using [hj]))
    (by rw [hL.rd, hL.wr, ea₀]; exact he₀) hL.state hL.row
    (by rw [ea₀]; exact hL.aux.2.2 (2 * j) (by omega_using [hj]))) fun s₁ ⟨l₁, w₁, f₁, rd₁, wr₁, sp₁, k₁⟩ => ?_
  have aux₁ : Aux s₀ s₁.mem := aux_round hL.aux (.inr rfl) f₁
  have ea₁ : s₁.gpr .s0 + BitVec.ofNat 64 (8 * 1) = off s₀ (8 * (2 * j + 1)) := by
    rw [k₁ .s0 (by decide), hL.s0, off_add, show 16 * j + 8 * 1 = 8 * (2 * j + 1) by omega_using []]
  refine WP.mono (round_ok check₁ keeps₁ (by decide) (by decide) 1 (by decide) (rc := RC (2 * j + 1))
    (src := off s₀ 392) (dst := off s₀ 192)
    (by rw [k₁ .a1 (by decide)]; exact hL.a1) (by rw [k₁ .a0 (by decide)]; exact hL.a0)
    (hp.al_off (by decide) (by decide)) (hp.al_off (by decide) (by decide))
    (by rw [ea₁]; exact hp.al_off (by omega_using []) (by omega_using [hj]))
    (by rw [rd₁, wr₁, hL.rd, hL.wr, ea₁]; exact he₁) l₁ w₁
    (by rw [ea₁]; exact aux₁.2.2 (2 * j + 1) (by omega_using [hj]))) fun s₂ ⟨l₂, w₂, f₂, rd₂, wr₂, sp₂, k₂⟩ => ?_
  have h0 : s₂.gpr .s0 = off s₀ (16 * j) := by rw [k₂ .s0 (by decide), k₁ .s0 (by decide), hL.s0]
  refine wp_addi (by decide) fun s₃ u₃ => WP.block_nil ⟨?_, ?_⟩
  · have e0 : s₃.gpr .s0 = off s₀ (16 * (j + 1)) := by
      rw [u₃.gpr, h0, off_add, show 16 * j + 16 = 16 * (j + 1) by omega_using []]
    have e1 : s₃.gpr .a0 = off s₀ 192 := by
      rw [u₃.other _ (by decide), k₂ .a0 (by decide), k₁ .a0 (by decide), hL.a0]
    show some (s₃.gpr .s0 != s₃.gpr .a0) = _
    rw [e0, e1, off_ne s₀ (by omega_using [hj]) (by omega_using [])]
    have : (16 * (j + 1) = 192) ↔ (j + 1 = 12) := by omega_using []
    simp only [this]
  · have keep : ∀ r ∈ kept, r ≠ .s0 → s₃.gpr r = s.gpr r := fun r hr h1 => by
      rw [u₃.other r h1, k₂ r hr, k₁ r hr]
    have hst : cmpl (Proof.Sha3.outState (Proof.Sha3.outState ((List.range (2 * j)).foldl rnd (A₀ s₀))
        (RC (2 * j))) (RC (2 * j + 1))) = cmpl ((List.range (2 * (j + 1))).foldl rnd (A₀ s₀)) := by
      rw [Proof.Sha3.outState_eq, Proof.Sha3.outState_eq, foldl_two]
    rw [hst] at l₂ w₂
    have hrow : ∀ x < 5, rowReg x ≠ .s0 := by decide
    refine ⟨by rw [keep .a0 (by decide) (by decide), hL.a0],
      by rw [keep .a1 (by decide) (by decide), hL.a1],
      by rw [u₃.gpr, h0, off_add, show 16 * j + 16 = 16 * (j + 1) by omega_using []],
      by rw [keep .s1 (by decide) (by decide), hL.s1],
      by rw [u₃.rd, rd₂, rd₁, hL.rd], by rw [u₃.wr, wr₂, wr₁, hL.wr], by rw [u₃.sp, sp₂, sp₁, hL.sp],
      by rw [u₃.mem]; exact l₂, fun x hx => ?_, ?_, ?_⟩
    · rw [u₃.other _ (hrow x hx)]; exact w₂ x hx
    · rw [u₃.mem]; exact aux_round aux₁ (.inl rfl) f₂
    · rw [u₃.mem]
      exact frame_round (frame_round hL.frame (by omega_using []) f₁) (by omega_using []) f₂

/-! ## The epilogue -/

/-- During the copies of the lanes back into the state, from the state `sL`
the rounds leave. -/
def EInv (s₀ sL : State) (k : Nat) (s : State) : Prop :=
  s.gpr .a0 = off s₀ 192 ∧ s.gpr .s1 = st s₀ ∧ s.rd = [] ∧ s.wr = W s₀ ∧ s.sp = F s₀ ∧
    Frame [stR s₀] sL.mem s.mem ∧
    ∀ j (hj : j < 25), j < k → s.mem.readW (laneAddr (st s₀) j) 64 = (keccakF (A₀ s₀))[j]

theorem cmpl_msk (A : KState) {i : Nat} (hi : i < 25) : (cmpl A)[i] ^^^ msk i = A[i] := by
  rw [Round.cmpl_get _ hi, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem copyOuts_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) (s : State)
    (hs : EInv s₀ sL 0 s) : WP isa (.block ((List.range 25).flatMap copyOut)) s (EInv s₀ sL 25) := by
  have hX : Lanes sL.mem (off s₀ 192) (cmpl (keccakF (A₀ s₀))) := hL.state
  refine wp_range_flatMap (M := isa) (EInv s₀ sL)
    (fun i s' hi ⟨h0, h1, hrd, hwr, hsp, hf, hl⟩ => ?_) 25 (Nat.le_refl _) s hs
  unfold copyOut ld
  rw [List.cons_append]
  refine wp_ld (by omega_using [hi]) (a := off s₀ (192 + 8 * i)) (by rw [h0, off_add])
    (hp.al_off (by omega_using []) (by omega_using [hi])) (by rw [hrd, hwr]; exact in_fr s₀ (by omega_using [hi])) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr .t0 = (keccakF (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, ← laneAddr_off, hf.readW (lane_contains _ hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := 192) (n := 200) (k := 608) (by omega_using [])))
      (by decide), hX i hi, cmpl_msk _ hi]
  have g1 : s₂.gpr .s1 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h1]
  refine WP.mono (Words64.storeLE64_ok (v := .t0) (tmp := .t1) (tmp2 := .t2) (n := .s1) (off := 8 * i)
    (by decide) (by decide) (by decide) (by decide) (by omega_using [hi])
    (by rw [u₂.wr, u₁.wr, hwr, g1]; exact in_st s₀ hi)) fun s₃ ⟨o₃, m₃, rd₃, wr₃, sp₃⟩ => ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [o₃ _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h0],
    by rw [o₃ _ (by decide) (by decide), g1], by rw [rd₃, u₂.rd, u₁.rd, hrd],
    by rw [wr₃, u₂.wr, u₁.wr, hwr], by rw [sp₃, u₂.sp, u₁.sp, hsp], ?_, fun j hj hji => ?_⟩
  · rw [m₃, g1, m₂]
    exact hf.writeW (List.mem_singleton_self _) _ (lane_contains _ hi)
  · rw [m₃, g1, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [Mem.readW_writeW_sep (Proof.Sha3.lane_sep _ hj hi e) (by decide)]
      exact hl j hj (by omega_using [hji, e])

/-- The copies back into an 8-byte aligned state. -/
theorem copyOutsA_ok {s₀ : State} (hp : Pre s₀) (hal : (st s₀).toNat % 8 = 0) {sL : State}
    (hL : LInv s₀ 12 sL) (s : State) (hs : EInv s₀ sL 0 s) :
    WP isa (.block ((List.range 25).flatMap copyOutA)) s (EInv s₀ sL 25) := by
  have hX : Lanes sL.mem (off s₀ 192) (cmpl (keccakF (A₀ s₀))) := hL.state
  refine wp_range_flatMap (M := isa) (EInv s₀ sL)
    (fun i s' hi ⟨h0, h1, hrd, hwr, hsp, hf, hl⟩ => ?_) 25 (Nat.le_refl _) s hs
  unfold copyOutA ld
  rw [List.cons_append]
  refine wp_ld (by omega_using [hi]) (a := off s₀ (192 + 8 * i)) (by rw [h0, off_add])
    (hp.al_off (by omega_using []) (by omega_using [hi])) (by rw [hrd, hwr]; exact in_fr s₀ (by omega_using [hi])) fun s₁ u₁ => ?_
  refine cmplLane_ok fun s₂ u₂ => ?_
  have hv : s₂.gpr .t0 = (keccakF (A₀ s₀))[i] := by
    rw [u₂.gpr, u₁.gpr, ← laneAddr_off, hf.readW (lane_contains _ hi) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := 192) (n := 200) (k := 608) (by omega_using [])))
      (by decide), hX i hi, cmpl_msk _ hi]
  have g1 : s₂.gpr .s1 = st s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h1]
  refine wp_sd (by omega_using [hi]) (a := laneAddr (st s₀) i) (by rw [g1]) (al_lane hal i)
    (by rw [u₂.wr, u₁.wr, hwr]; exact in_st s₀ hi) fun s₃ g₃ => WP.block_nil ?_
  have m₂ : s₂.mem = s'.mem := by rw [u₂.mem, u₁.mem]
  refine ⟨by rw [g₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h0],
    by rw [g₃.gpr, g1], by rw [g₃.rd, u₂.rd, u₁.rd, hrd],
    by rw [g₃.wr, u₂.wr, u₁.wr, hwr], by rw [g₃.sp, u₂.sp, u₁.sp, hsp], ?_, fun j hj hji => ?_⟩
  · rw [g₃.mem, m₂]
    exact hf.writeW (List.mem_singleton_self _) _ (lane_contains _ hi)
  · rw [g₃.mem, m₂]
    by_cases e : j = i
    · subst e; rw [Mem.readW_writeW_self64, hv]
    · rw [Mem.readW_writeW_sep (Proof.Sha3.lane_sep _ hj hi e) (by decide)]
      exact hl j hj (by omega_using [hji, e])

/-- The copies back, by either of the copies `outs`, then the registers restored. -/
theorem epiTail_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) {outs : List Instr}
    (hc : WP isa (.block outs) sL (EInv s₀ sL 25)) :
    WP isa (.block (outs ++ restore)) sL fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) := by
  rw [WP.block_append_iff]
  refine WP.mono hc fun s₁ ⟨h0, h1, hrd, hwr, hsp, hf, hl⟩ => ?_
  have hfr : ∀ d, d + 8 ≤ 608 → s₁.mem.readW (off s₀ d) 64 = sL.mem.readW (off s₀ d) 64 := fun d hd =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.fr_st.sub_left (Offset.sub_base (F s₀) (d := d) (n := 8) (k := 608) hd)) (by decide)
  unfold restore
  refine wp_ld (by decide) (a := off s₀ 592) (by rw [h0, off_add]; rfl) (hp.al_off (by decide) (by decide))
    (by rw [hrd, hwr]; exact in_fr s₀ (by decide)) fun s₂ u₂ => ?_
  refine wp_ld (by decide) (a := off s₀ 600) (by rw [u₂.other _ (by decide), h0, off_add]; rfl)
    (hp.al_off (by decide) (by decide)) (by rw [u₂.rd, u₂.wr, hrd, hwr]; exact in_fr s₀ (by decide))
    fun s₃ u₃ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [u₃.other _ (by decide), u₂.gpr, hfr 592 (by decide)]; exact hL.aux.1
  · rw [u₃.gpr, u₂.mem, hfr 600 (by decide)]; exact hL.aux.2.1
  · rw [u₃.sp, u₂.sp, hsp]
  · rw [u₃.wr, u₂.wr, hwr]
  · apply Vector.ext
    intro i hi
    simp only [Spec.Sha3.stateAt, Vector.getElem_ofFn, u₃.mem, u₂.mem]
    exact hl i hi hi

theorem epilogue_ok {s₀ : State} (hp : Pre s₀) {sL : State} (hL : LInv s₀ 12 sL) :
    WP isa epilogue sL fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) := by
  unfold epilogue
  refine WP.seq (Wp.WP.cons (exec_logicImm (imm := 7) (by decide)) (WP.block_nil ?_))
  let s₁ := sL.write .t0 (sL.gpr .s1 &&& BitVec.ofInt 64 7)
  have hL₁ : LInv s₀ 12 s₁ := ⟨by simp [s₁, State.write, hL.a0], by simp [s₁, State.write, hL.a1],
    by simp [s₁, State.write, hL.s0], by simp [s₁, State.write, hL.s1], hL.rd, hL.wr, hL.sp, hL.state,
    fun x hx => by
      have : rowReg x ≠ .t0 := by revert x; decide
      simp only [s₁, State.write, this, ite_false]; exact hL.row x hx, hL.aux, hL.frame⟩
  have e0 : EInv s₀ s₁ 0 s₁ := ⟨hL₁.a0, hL₁.s1, hL₁.rd, hL₁.wr, hL₁.sp, Frame.refl _ _,
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.ite (M := isa) (decide ((st s₀).toNat % 8 = 0))
    (by show some (s₁.gpr .t0 == 0) = _; simp only [s₁, State.write, ite_true, hL.s1]; rw [and7])
    (fun h => ?_) (fun _ => ?_)
  · exact WP.mono (epiTail_ok hp hL₁ (copyOutsA_ok hp (of_decide_eq_true h) hL₁ s₁ e0)) fun _ h => h
  · exact WP.mono (epiTail_ok hp hL₁ (copyOuts_ok hp hL₁ s₁ e0)) fun _ h => h

/-- Registers that no instruction of code without calls writes keep their
values, as a postcondition. -/
theorem WP.gprs' {c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa c s Q) {rs : List Reg}
    (hc : ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r) (hn : c.noCalls = true) :
    WP isa c s fun s' => Q s' ∧ ∀ r ∈ rs, s'.gpr r = s.gpr r := by
  obtain ⟨t, s', he, hq⟩ := h
  exact ⟨t, s', he, hq, fun r hr => Exec.gpr (hc r hr) he (.inl hn)⟩

theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) (allocd 608 s₀) fun s => CInv s₀ 0 s ∧ s.gpr .t0 = st s₀ &&& BitVec.ofInt 64 7 := by
  unfold setup
  simp only [List.append_assoc]
  refine save_ok hp (s := allocd 608 s₀) rfl hp.rd (by simp only [allocd, hp.wr]) rfl rfl
    fun s₁ h6 h1 hrd hwr hsp v₁ v₂ hf => ?_
  rw [WP.block_append_iff]
  refine WP.mono (rcs_ok hp s₁ ⟨h6, h1, hrd, hwr, hsp, v₁, v₂, fun _ h => absurd h (Nat.not_lt_zero _),
    hf⟩) fun s₂ ⟨g6, g1, grd, gwr, gsp, w₁, w₂, wc, gf⟩ => ?_
  refine Wp.WP.cons (exec_logicImm (imm := 7) (by decide)) (WP.block_nil ⟨⟨?_, ?_, grd, gwr, gsp, ⟨w₁, w₂, wc⟩, gf,
    fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ h => absurd h (by omega_using [])⟩, ?_⟩)
  · simp [State.write, g6]
  · simp [State.write, g1]
  · simp [State.write, g1]

/-- The copy into the frame, by either copy, and the rounds' pointers. -/
theorem copyIns'_ok {s₀ : State} (hp : Pre s₀) {s : State} (hs : CInv s₀ 0 s)
    (h0 : s.gpr .t0 = st s₀ &&& BitVec.ofInt 64 7) : WP isa copyIns s (LInv s₀ 0) := by
  unfold copyIns
  refine WP.ite (M := isa) (decide ((st s₀).toNat % 8 = 0))
    (by show some (s.gpr .t0 == 0) = _; rw [h0, and7]) (fun h => ?_) (fun _ => ?_)
  · rw [WP.block_append_iff]
    exact WP.mono (copyInsA_ok hp (of_decide_eq_true h) s hs) fun _ h => pointers_ok h
  · rw [WP.block_append_iff]
    exact WP.mono (copyIns_ok hp s hs) fun _ h => pointers_ok h

theorem main_ok {s₀ : State} (hp : Pre s₀) :
    WP isa main (allocd 608 s₀) fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = F s₀ ∧ s'.wr = W s₀ ∧
        stateAt s'.mem (st s₀) = keccakF (A₀ s₀) := by
  unfold main
  refine WP.seq (WP.mono (setup_ok hp) fun s₀' ⟨hc, h0⟩ => ?_)
  refine WP.seq (WP.mono (copyIns'_ok hp hc h0) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := LInv s₀ 12) ?_ fun s₂ h₂ => epilogue_ok hp h₂)
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = 12 - j ∧ j < 12 ∧ LInv s₀ j s
  refine WP.loop (M := isa) Inv (fun n s ⟨j, hn, hj, hL⟩ => ?_) 12 s₁ ⟨0, rfl, by omega_using [], h₁⟩
  refine WP.mono (body_ok hp hj hL) fun s' ⟨he, hl⟩ => ?_
  by_cases hlast : j + 1 = 12
  · exact .inl ⟨by show eval (.ne .s0 .a0) s' = _; rw [he, hlast]; rfl, hlast ▸ hl⟩
  · exact .inr ⟨by show eval (.ne .s0 .a0) s' = _; rw [he]; simp [hlast],
      12 - (j + 1), by omega_using [hn, hj], j + 1, rfl, by omega_using [hj, hlast], hl⟩

/-- The callee-saved registers the code never writes, and the return address. -/
def untouched : List Reg := [.ra, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11]

/-- `untouched.all fun r => o != some r` as one `match`, which the kernel
evaluates faster. -/
def keepsU : Option Reg → Bool
  | some .ra | some .s2 | some .s3 | some .s4 | some .s5 | some .s6 | some .s7 | some .s8
  | some .s9 | some .s10 | some .s11 => false
  | _ => true

theorem untouched_keep : main.allInstrs (fun i => keepsU (dstOf i)) = true := by
  decide +kernel

theorem main_noCalls : main.noCalls = true := by decide +kernel

theorem untouched_ok : ∀ r ∈ untouched, ∀ i ∈ instrs main, dstOf i ≠ some r := by
  intro r hr i hi e
  have h := List.all_eq_true.mp ((Code.allInstrs_eq _ _).symm.trans untouched_keep) i hi
  rw [e] at h
  simp only [untouched, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepsU] at h

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa permute s₀ fun s' =>
      s'.gpr .s0 = s₀.gpr .s0 ∧ s'.gpr .s1 = s₀.gpr .s1 ∧ s'.sp = s₀.sp ∧
        (∀ r ∈ untouched, s'.gpr r = s₀.gpr r) ∧ Proof.Sha3.permuteRISCV64.post s₀ s' := by
  have hm := WP.gprs' (main_ok hp) untouched_ok main_noCalls
  refine WP.alloc (n := 608) ⟨by decide, by decide, by decide⟩ hp.sp (WP.mono hm
    fun s₂ ⟨⟨h0, h1, hsp, hwr, hst⟩, hu⟩ m u f => ?_)
  refine ⟨h0, h1, ?_, fun r hr => hu r hr, ?_⟩
  · show s₂.sp + BitVec.ofNat 64 608 = s₀.sp
    rw [hsp, BitVec.sub_add_cancel]
  · -- The `free` loses the frame's bytes, which lie apart from the state.
    simp only [Proof.Sha3.permuteRISCV64, freed]
    refine Eq.trans ?_ hst
    exact Proof.Sha3.stateAt_congr fun i hi => lost_byte f (R := stR s₀) hp.fr_st.symm hi

theorem preserved_split : ∀ r ∈ preserved, r = .s0 ∨ r = .s1 ∨ r ∈ untouched := by decide

theorem permute_correct (s : State) (hs : Proof.Sha3.permuteRISCV64.pre s) :
    ∃ t s', Exec isa Impl.Sha3.RISCV64.permute s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteRISCV64.post s s' := by
  obtain ⟨t, s', he, h0, h1, hsp, hu, h₂⟩ := correct (pre_of s hs)
  refine ⟨t, s', he, ⟨fun r hr => ?_, hsp, hu .ra (by decide)⟩, h₂⟩
  rcases preserved_split r hr with rfl | rfl | h
  exacts [h0, h1, hu r h]

end VG.Proof.Sha3.RISCV64
