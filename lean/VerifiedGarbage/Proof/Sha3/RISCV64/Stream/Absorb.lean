module

-- separate module: as `Absorb`, `Pad` and `Squeeze`, whose proofs cost more than their imports,
-- apart from `Verified`, which composes them
public import VerifiedGarbage.Proof.Framework.RISCV64.Spill
import VerifiedGarbage.Proof.Sha3.Arith
import VerifiedGarbage.Proof.Sha3.Lanes
public import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RISCV64.Wp
public import VerifiedGarbage.Proof.Framework.RISCV64.Words64
public import VerifiedGarbage.Proof.Sha3.Stream
public import VerifiedGarbage.Proof.Framework.RISCV64.Alloc
public import VerifiedGarbage.Spec.Sha3.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
public import VerifiedGarbage.Impl.Sha3.RISCV64.Stream
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.RISCV64.Call
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Proof.Framework.RISCV64.CallAny
public import VerifiedGarbage.Proof.Sha3.Contract
public import VerifiedGarbage.Proof.Framework.RISCV64.Taint
import VerifiedGarbage.Proof.Sha3.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.Inline
import VerifiedGarbage.Proof.Framework.RISCV64.Steps
import VerifiedGarbage.Proof.Framework.Range
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

/-! ### `Sha3.RISCV64.Permute`, which this module and modules that import it used -/

section

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

private theorem rc_fold_bits (bit : Nat → Bool) :
    (List.range 7).foldl (fun acc j => if bit j then acc ||| (1#64 <<< (2 ^ j - 1)) else acc) 0 =
      ((BitVec.ofNat 64 ((if bit 0 then 1 else 0) + (if bit 1 then 2 else 0) +
          (if bit 2 then 8 else 0) + (if bit 3 then 128 else 0)) |||
        (if bit 4 then 1#64 <<< 15 else 0)) ||| (if bit 5 then 1#64 <<< 31 else 0)) |||
        (if bit 6 then 1#64 <<< 63 else 0) :=
  rc_fold (bit 0) (bit 1) (bit 2) (bit 3) (bit 4) (bit 5) (bit 6)

/-- `RC k` as `rcBuild` builds it: the four low bits as a number, then bits
15, 31 and 63. -/
theorem rc_eq (k : Nat) :
    RC k = ((BitVec.ofNat 64 (rcLo k) ||| (if rcBit k 4 then 1#64 <<< 15 else 0)) |||
      (if rcBit k 5 then 1#64 <<< 31 else 0)) ||| (if rcBit k 6 then 1#64 <<< 63 else 0) :=
  rc_fold_bits (rcBit k)

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

end

end

/-! ### `Sha3.RISCV64.Stream.Absorb`, which this module and modules that import it used -/

section

/-! ### `Sha3.RISCV64.Stream.Common`, which this module and modules that import it used -/

section

/-! ### `Sha3.RISCV64.Call`, which this module and modules that import it used -/

section

/-!
# SHA-3 on RISC-V: calling the permutation

The streaming functions call `vg_keccak_f1600` (which allocates a frame of
its own, `WP.callAny`) on the state at `s2`, with a frame of 512 bytes
allocated around the call as its scratch space (`permuteAt_ok`).
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Spec.Sha3 (stateAt keccakF)

theorem permute_sdepth : sdepth Impl.Sha3.RISCV64.permute = 608 := by decide +kernel

/-- Calling `vg_keccak_f1600` on the state at `a0`, with scratch space at
`a1`, the stack pointer: the callee-saved registers are kept, and memory
changes only in the state, the scratch space and the 608 bytes below. -/
theorem call_ok {s : State} {st : Addr} (h0 : s.gpr .a0 = st) (h1 : s.gpr .a1 = s.sp)
    (hal : s.sp.toNat % 16 = 0) (hsp : 608 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp, 512⟩) (d₂ : Region.Disjoint ⟨s.sp - 608, 608⟩ ⟨st, 200⟩)
    (hw : Covers [⟨st, 200⟩, ⟨s.sp, 512⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨s.sp, 512⟩, ⟨s.sp - 608, 608⟩] s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa (.call "vg_keccak_f1600" Impl.Sha3.RISCV64.permute) s Q := by
  have c0 : s.callEntry.gpr .a0 = st := (State.callEntry_gpr _ (by decide)).trans h0
  have c1 : s.callEntry.gpr .a1 = s.sp := (State.callEntry_gpr _ (by decide)).trans h1
  refine WP.callAny (k := Proof.Sha3.permuteRISCV64) permute_correct
    (rd := []) (wr := [⟨st, 200⟩, ⟨s.sp, 512⟩]) ?_ ?_ hw ?_ (by rw [permute_sdepth]; decide)
  · simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.withRegions_sp, State.callEntry_sp, c0, c1]
    exact ⟨trivial, trivial, d₁, hal, hsp, d₂,
      Offset.base_disjoint_below s.sp (n := 608) (k := 512) (by omega_using []) |>.symm⟩
  · intro a n h
    obtain ⟨r, hr, hc⟩ := hw a n (by simpa using h)
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · intro s' hrd hwr hsp' hf hcs hpost
    simp only [Proof.Sha3.permuteRISCV64, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    rw [permute_sdepth] at hf
    exact hQ s' hrd hwr hsp' hcs (by simpa using hf) hpost

theorem preserved_a0_a1 : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 := by decide

/-- The writable regions with a frame pushed: the state is still in them. -/
theorem covers_push {wr : List Region} {st f : Addr} (hw : Covers [⟨st, 200⟩] wr) :
    Covers [⟨st, 200⟩, ⟨f, 512⟩] (⟨f, 512⟩ :: wr) := by
  intro a n ⟨r, hr, hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · obtain ⟨r', hr', hc'⟩ := hw a n ⟨_, List.mem_singleton_self _, hc⟩
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · exact ⟨_, List.mem_cons_self .., hc⟩

/-- The scratch frame of 512 bytes below `sp`, and the permutation's 608
below it. -/
theorem scratch_sp {sp : Addr} (hal : sp.toNat % 16 = 0) (hsp : 1120 ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 512).toNat % 16 = 0 ∧ 608 ≤ (sp - BitVec.ofNat 64 512).toNat ∧
      sp - BitVec.ofNat 64 512 - 608 = sp - BitVec.ofNat 64 1120 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [hsp]),
    BitVec.toNat_ofNat]
  refine ⟨by omega_using [hal, hsp], by omega_using [hsp], ?_⟩
  rw [BitVec.sub_sub]; rfl

/-- A call in a frame of 512 bytes of scratch space: what holds after it,
from what the call ensures. -/
theorem scratch_post {s s' : State} {st : Addr} {m : Mem} {u : Nat → BitVec 64}
    (wr₂ : s'.wr = ⟨s.sp - BitVec.ofNat 64 512, 512⟩ :: s.wr) (sp₂ : s'.sp = s.sp - BitVec.ofNat 64 512)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp - BitVec.ofNat 64 512, 512⟩)
    (f' : Frame [⟨st, 200⟩, ⟨s.sp - BitVec.ofNat 64 512, 512⟩, ⟨s.sp - BitVec.ofNat 64 1120, 608⟩]
      s.mem s'.mem)
    (fl : Frame [⟨s.sp - BitVec.ofNat 64 512, 512⟩] s'.mem m) :
    let t : State := { freed 512 s' with mem := m, unknowns := u }
    t.rd = s'.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧ t.gpr = s'.gpr ∧
      Frame [⟨st, 200⟩, ⟨s.sp - BitVec.ofNat 64 512, 512⟩, ⟨s.sp - BitVec.ofNat 64 1120, 608⟩] s.mem t.mem ∧
      stateAt t.mem st = stateAt s'.mem st := by
  intro t
  refine ⟨by simp only [t, freed], ?_, ?_, by simp only [t, freed], ?_, ?_⟩
  · simp only [t, freed, wr₂, List.tail_cons]
  · simp only [t, freed, sp₂, BitVec.sub_add_cancel]
  · exact f'.trans (fl.mono fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · exact Proof.Sha3.stateAt_congr fun i hi => lost_byte fl d₁ hi

/-- `permuteAt`: calling `vg_keccak_f1600` on the state at `s2`, with scratch
space in a frame of its own, the 512 bytes below the stack pointer. -/
theorem permuteAt_ok {s : State} {st : Addr} (h1 : s.gpr .s2 = st)
    (hal : s.sp.toNat % 16 = 0) (hsp : 1120 ≤ s.sp.toNat)
    (d₁ : Region.Disjoint ⟨st, 200⟩ ⟨s.sp - BitVec.ofNat 64 512, 512⟩)
    (d₂ : Region.Disjoint ⟨s.sp - BitVec.ofNat 64 1120, 608⟩ ⟨st, 200⟩)
    (hw : Covers [⟨st, 200⟩] s.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) →
      Frame [⟨st, 200⟩, ⟨s.sp - BitVec.ofNat 64 512, 512⟩, ⟨s.sp - BitVec.ofNat 64 1120, 608⟩]
        s.mem s'.mem →
      stateAt s'.mem st = keccakF (stateAt s.mem st) → Q s') :
    WP isa permuteAt s Q := by
  obtain ⟨al', sp', e'⟩ := scratch_sp hal hsp
  unfold permuteAt scratchBytes mov
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by omega_using [hsp]) ?_
  refine WP.seq (wp_mv fun s₁ u₁ => wp_addSp (by decide) fun s₂ u₂ => WP.block_nil ?_)
  obtain sp₂ : s₂.sp = s.sp - BitVec.ofNat 64 512 := by rw [u₂.sp, u₁.sp]; rfl
  obtain hm : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]; rfl
  obtain wr₂ : s₂.wr = ⟨s.sp - BitVec.ofNat 64 512, 512⟩ :: s.wr := by rw [u₂.wr, u₁.wr]; rfl
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, u₁.rd]; rfl
  refine call_ok (st := st) (by rw [u₂.other _ (by decide), u₁.gpr]; exact h1)
    (by rw [u₂.gpr, sp₂, u₁.sp]; exact BitVec.add_zero _) (by rw [sp₂]; exact al')
    (by rw [sp₂]; exact sp') (by rw [sp₂]; exact d₁) (by rw [sp₂, e']; exact d₂)
    (by rw [sp₂, wr₂]; exact covers_push hw) fun s' rd' wr' sp'' cs' f' e'' => ?_
  intro m u fl
  rw [sp₂, e', hm] at f'
  obtain ⟨hr', hw', hs', hg', hf', hst⟩ := scratch_post (u := u) (wr'.trans wr₂) (sp''.trans sp₂) d₁ f' fl
  refine hQ _ (hr'.trans (rd'.trans rd₂)) hw' hs' (fun r hr => ?_) hf' (by rw [hst, e'', hm])
  rw [hg']
  exact (cs' r hr).trans ((u₂.other _ (preserved_a0_a1 r hr).2).trans (u₁.other _ (preserved_a0_a1 r hr).1))

end VG.Proof.Sha3.RISCV64

end

end

/-!
# The SHA-3 sponge on RISC-V: the frame of `absorb` and `squeeze`

`absorb` and `squeeze` run in a frame of 48 bytes (`withLoop`): the saved
return address and `s2`–`s6`. Below it, the permutation's scratch space is a
frame of 512 bytes around its call (`permuteAt`), and below that the
permutation's own frame: they use the 1168 bytes below the stack pointer
(`K`). `setup_ok` saves the registers, `Saved` says the frame still holds
them, and `epilogue_ok` returns the position and restores them.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream

section
variable (s₀ : State)

/-- The stack below the stack pointer that the function and the permutation use. -/
abbrev K : Addr := s₀.sp - BitVec.ofNat 64 1168
abbrev KR : Region := ⟨K s₀, 1168⟩
/-- The frame's base. -/
abbrev B : Addr := s₀.sp - BitVec.ofNat 64 48
/-- The frame's region. -/
abbrev BR : Region := ⟨B s₀, 48⟩

end

/-- The stack pointer: aligned, with room for the frames. -/
structure Stk (s₀ : State) : Prop where
  al : s₀.sp.toNat % 16 = 0
  sp : 1168 ≤ s₀.sp.toNat

/-- The parts of the stack used. -/
theorem sub_K (s₀ : State) {d n : Nat} (h : d + n ≤ 1168) :
    Region.Sub ⟨K s₀ + BitVec.ofNat 64 d, n⟩ (KR s₀) :=
  Offset.sub_base _ h

namespace Stk
variable {s₀ : State} (hk : Stk s₀)
include hk

theorem B_eq : B s₀ = K s₀ + BitVec.ofNat 64 1120 := by
  have := hk.sp
  simp only [B, K]; bv_omega

theorem B_toNat : (B s₀).toNat = s₀.sp.toNat - 48 := by
  have := hk.sp
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega_using [this]), BitVec.toNat_ofNat]

theorem B_al : (B s₀).toNat % 16 = 0 := by
  rw [hk.B_toNat]; have := hk.al; have := hk.sp; omega_arith

theorem B_1120 : 1120 ≤ (B s₀).toNat := by rw [hk.B_toNat]; have := hk.sp; omega_using [this]

theorem below_eq : B s₀ - BitVec.ofNat 64 1120 = K s₀ := by
  rw [hk.B_eq]; exact BitVec.add_sub_cancel _ _

theorem B_off (d : Nat) : B s₀ + BitVec.ofNat 64 d = K s₀ + BitVec.ofNat 64 (1120 + d) := by
  rw [hk.B_eq, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem scr_eq : B s₀ - BitVec.ofNat 64 512 = K s₀ + BitVec.ofNat 64 608 := by
  have := hk.sp
  simp only [B, K]; bv_omega

theorem scr_sub : Region.Sub ⟨B s₀ - BitVec.ofNat 64 512, 512⟩ (KR s₀) := by
  rw [hk.scr_eq]; exact sub_K s₀ (by omega_using [])

theorem below_sub : Region.Sub ⟨B s₀ - BitVec.ofNat 64 1120, 608⟩ (KR s₀) := by
  rw [hk.below_eq]; simpa using sub_K s₀ (d := 0) (n := 608) (by omega_using [])

/-- A slot of the saved registers. -/
theorem slot_sub {d : Nat} (h' : d + 8 ≤ 48) :
    Region.Sub ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ (KR s₀) := by
  rw [hk.B_off]; exact sub_K s₀ (by omega)

/-- The slots of the saved registers are not in the permutation's scratch
space. -/
theorem slot_scr {d : Nat} (h' : d + 8 ≤ 48) :
    Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ ⟨B s₀ - BitVec.ofNat 64 512, 512⟩ := by
  rw [hk.scr_eq, hk.B_off]; exact Offset.disjoint _ (.inr (by omega_using [])) (by omega_using [h']) (by omega_using [])

theorem slot_below {d : Nat} (h' : d + 8 ≤ 48) :
    Region.Disjoint ⟨B s₀ + BitVec.ofNat 64 d, 8⟩ ⟨B s₀ - BitVec.ofNat 64 1120, 608⟩ := by
  rw [hk.below_eq, hk.B_off]; exact Offset.disjoint_base _ (by omega) (by omega_using [h'])

end Stk

/-! ## Saving the registers -/

theorem saved_bound : ∀ p ∈ saved, p.2 + 8 ≤ 48 ∧ p.2 % 8 = 0 := by decide

/-- The frame at `b` holds the caller's registers `g`. -/
def Saved (b : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ p ∈ saved, m.readW (b + BitVec.ofNat 64 p.2) 64 = g p.1

/-- Writes outside the slots keep them. -/
theorem Saved.frame {b : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved b g m) {rs : List Region}
    (hd : ∀ d, d + 8 ≤ 48 → ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 d, 8⟩ r)
    (hf : Frame rs m m') : Saved b g m' := fun p hp => by
  have := saved_bound p hp
  rw [hf.readW (Region.contains_self _ _) (hd _ this.1) (by decide)]
  exact h p hp

theorem readW_writeW_off (m : Mem) (b : Addr) (v : BitVec 64) {d e : Nat}
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d < 2 ^ 32) (he : e < 2 ^ 32) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 =
      m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [hd]) (by omega_using [he])) (by decide)

theorem save_eq : save = [.addSp .t0 0, .store .d .ra .t0 0, .store .d .s2 .t0 8,
    .store .d .s3 .t0 16, .store .d .s4 .t0 24, .store .d .s5 .t0 32, .store .d .s6 .t0 40] := rfl

/-- Saving the registers in the frame at the stack pointer. -/
theorem save_ok {rest : List Instr} {s : State} {Q : State → Prop} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, d + 8 ≤ 48 → InRegions s.wr (s.sp + BitVec.ofNat 64 d) 8)
    (k : ∀ s', (∀ r, r ≠ .t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Saved s.sp s.gpr s'.mem → Frame [⟨s.sp, 48⟩] s.mem s'.mem →
      WP isa (.block rest) s' Q) :
    WP isa (.block (save ++ rest)) s Q := by
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine wp_addSp (by decide) fun s₀ u₀ => ?_
  obtain g0 : s₀.gpr .t0 = s.sp := by rw [u₀.gpr]; exact BitVec.add_zero _
  have o : ∀ r, r ≠ .t0 → s₀.gpr r = s.gpr r := u₀.other
  obtain st : ∀ d, d % 8 = 0 → d + 8 ≤ 48 → ∀ s' : State, s'.gpr .t0 = s.sp →
      s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions s'.wr (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₂ s' h₀ hw => ⟨by rw [h₀], al8 hal hd (by omega_using [h₂]), by rw [hw]; exact hin d h₂⟩
  obtain hc : ∀ d, d + 8 ≤ 48 →
      (⟨s.sp, 48⟩ : Region).Contains (s.sp + BitVec.ofNat 64 d) (64 / 8) :=
    fun d h₂ => Offset.contains_base _ h₂ (by omega_using [h₂])
  obtain ⟨a1, l1, i1⟩ := st 0 (by decide) (by omega_using []) s₀ g0 u₀.wr
  refine wp_sd (by decide) a1 l1 i1 fun s₁ g₁ => ?_
  obtain ⟨a2, l2, i2⟩ := st 8 (by decide) (by omega_using []) s₁ (by rw [g₁.gpr, g0])
    (by rw [g₁.wr, u₀.wr])
  refine wp_sd (by decide) a2 l2 i2 fun s₂ g₂ => ?_
  obtain ⟨a3, l3, i3⟩ := st 16 (by decide) (by omega_using []) s₂ (by rw [g₂.gpr, g₁.gpr, g0])
    (by rw [g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a3 l3 i3 fun s₃ g₃ => ?_
  obtain ⟨a4, l4, i4⟩ := st 24 (by decide) (by omega_using []) s₃
    (by rw [g₃.gpr, g₂.gpr, g₁.gpr, g0]) (by rw [g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a4 l4 i4 fun s₄ g₄ => ?_
  obtain ⟨a5, l5, i5⟩ := st 32 (by decide) (by omega_using []) s₄
    (by rw [g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, g0]) (by rw [g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a5 l5 i5 fun s₅ g₅ => ?_
  obtain ⟨a6, l6, i6⟩ := st 40 (by decide) (by omega_using []) s₅
    (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr, g0])
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
  refine wp_sd (by decide) a6 l6 i6 fun s₆ g₆ => ?_
  obtain gg : s₆.gpr = s₀.gpr := by rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, g₁.gpr]
  obtain hm : s₆.mem = (((((s.mem.writeW (s.sp + BitVec.ofNat 64 0) (s.gpr .ra)).writeW
      (s.sp + BitVec.ofNat 64 8) (s.gpr .s2)).writeW (s.sp + BitVec.ofNat 64 16) (s.gpr .s3)).writeW
      (s.sp + BitVec.ofNat 64 24) (s.gpr .s4)).writeW (s.sp + BitVec.ofNat 64 32) (s.gpr .s5)).writeW
      (s.sp + BitVec.ofNat 64 40) (s.gpr .s6) := by
    rw [g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₁.mem, u₀.mem, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr,
      g₁.gpr, o _ (by decide), o _ (by decide), o _ (by decide), o _ (by decide), o _ (by decide),
      o _ (by decide)]
  refine k s₆ (fun r hr => by rw [gg, o r hr])
    (by rw [g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, g₁.rd, u₀.rd])
    (by rw [g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, g₁.wr, u₀.wr])
    (by rw [g₆.sp, g₅.sp, g₄.sp, g₃.sp, g₂.sp, g₁.sp, u₀.sp]) (fun p hp => ?_) ?_
  · rw [hm]
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := omega_using []) only [Mem.readW_writeW_self64, readW_writeW_off]
  · rw [hm]
    exact ((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hc 0 (by omega_using []))).writeW
      (List.mem_singleton_self _) _ (hc 8 (by omega_using []))).writeW (List.mem_singleton_self _) _
      (hc 16 (by omega_using []))).writeW (List.mem_singleton_self _) _
      (hc 24 (by omega_using []))).writeW (List.mem_singleton_self _) _
      (hc 32 (by omega_using []))).writeW (List.mem_singleton_self _) _ (hc 40 (by omega_using []))

theorem restore_eq : restore = [.addSp .t0 0, .load .d .ra .t0 0, .load .d .s2 .t0 8,
    .load .d .s3 .t0 16, .load .d .s4 .t0 24, .load .d .s5 .t0 32, .load .d .s6 .t0 40] := rfl

/-- Returning the position and restoring the registers from the frame at the
stack pointer. -/
theorem epilogue_ok {s : State} {g : Reg → BitVec 64} (hal : s.sp.toNat % 16 = 0)
    (hin : ∀ d, d + 8 ≤ 48 → InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 d) 8)
    (hsv : Saved s.sp g s.mem) {Q : State → Prop}
    (k : ∀ s', s'.gpr .a0 = s.gpr .s4 → (∀ p ∈ saved, s'.gpr p.1 = g p.1) →
      (∀ r, r ∉ saved.map Prod.fst → r ≠ .a0 → r ≠ .t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → Q s') :
    WP isa (.block (mov .a0 .s4 :: restore)) s Q := by
  refine wp_mv fun s₀ u₀ => ?_
  rw [restore_eq]
  refine wp_addSp (by decide) fun s₁ u₁ => ?_
  obtain g1 : s₁.gpr .t0 = s.sp := by rw [u₁.gpr, u₀.sp]; exact BitVec.add_zero _
  obtain v : ∀ r d, (r, d) ∈ saved → s.mem.readW (s.sp + BitVec.ofNat 64 d) 64 = g r :=
    fun r d h => hsv (r, d) h
  obtain ld : ∀ d, d % 8 = 0 → d + 8 ≤ 48 → ∀ s' : State, s'.gpr .t0 = s.sp →
      s'.rd = s.rd → s'.wr = s.wr →
      s'.gpr .t0 + BitVec.ofNat 64 d = s.sp + BitVec.ofNat 64 d ∧
      (s.sp + BitVec.ofNat 64 d).toNat % 8 = 0 ∧ InRegions (s'.rd ++ s'.wr) (s.sp + BitVec.ofNat 64 d) 8 :=
    fun d hd h₂ s' h₀ hr hw => ⟨by rw [h₀], al8 hal hd (by omega_using [h₂]), by rw [hr, hw]; exact hin d h₂⟩
  obtain rd₁ : s₁.rd = s.rd := by rw [u₁.rd, u₀.rd]
  obtain wr₁ : s₁.wr = s.wr := by rw [u₁.wr, u₀.wr]
  obtain m₁ : s₁.mem = s.mem := by rw [u₁.mem, u₀.mem]
  obtain ⟨a1, l1, i1⟩ := ld 0 (by decide) (by omega_using []) s₁ g1 rd₁ wr₁
  refine wp_ld (by decide) a1 l1 i1 fun s₂ u₂ => ?_
  obtain ⟨a2, l2, i2⟩ := ld 8 (by decide) (by omega_using []) s₂
    (by rw [u₂.other _ (by decide), g1]) (by rw [u₂.rd, rd₁]) (by rw [u₂.wr, wr₁])
  refine wp_ld (by decide) a2 l2 i2 fun s₃ u₃ => ?_
  obtain ⟨a3, l3, i3⟩ := ld 16 (by decide) (by omega_using []) s₃
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), g1]) (by rw [u₃.rd, u₂.rd, rd₁])
    (by rw [u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a3 l3 i3 fun s₄ u₄ => ?_
  obtain ⟨a4, l4, i4⟩ := ld 24 (by decide) (by omega_using []) s₄
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g1])
    (by rw [u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a4 l4 i4 fun s₅ u₅ => ?_
  obtain ⟨a5, l5, i5⟩ := ld 32 (by decide) (by omega_using []) s₅
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g1])
    (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a5 l5 i5 fun s₆ u₆ => ?_
  obtain ⟨a6, l6, i6⟩ := ld 40 (by decide) (by omega_using []) s₆
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g1])
    (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
  refine wp_ld (by decide) a6 l6 i6 fun s₇ u₇ => WP.block_nil ?_
  obtain mm : ∀ (x : State), x.mem = s₁.mem → x.mem = s.mem := fun x h => h.trans m₁
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine k s₇ ?_ (fun p hp => ?_) (fun r hr h0 ht => ?_) m₇
    (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
    (by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, u₀.sp])
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
      u₀.gpr]
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, m₁, v .ra 0 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.other _ (by decide), u₃.gpr, u₂.mem, m₁, v .s2 8 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem,
        u₂.mem, m₁, v .s3 16 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, u₂.mem, m₁,
        v .s4 24 (by simp [saved])]
    · rw [u₇.other _ (by decide), u₆.gpr, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁,
        v .s5 32 (by simp [saved])]
    · rw [u₇.gpr, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁, v .s6 40 (by simp [saved])]
  · simp only [saved, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hr
    rw [u₇.other _ h6, u₆.other _ h5, u₅.other _ h4, u₄.other _ h3, u₃.other _ h2, u₂.other _ h1,
      u₁.other _ ht, u₀.other _ h0]

/-! ## The test for a lane -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

private theorem wp_or {d n m : Reg} (k : ∀ s', Upd s s' d (s.gpr n ||| s.gpr m) → WP isa (.block is) s' Q) :
    WP isa (.block (.logic .or d n m :: is)) s Q :=
  WP.cons exec_logic (k _ (Upd.write _ _ _))

private theorem wp_andi7 {d n : Reg} (k : ∀ s', Upd s s' d (s.gpr n &&& 7) → WP isa (.block is) s' Q) :
    WP isa (.block (.logicImm .and d n 7 :: is)) s Q :=
  WP.cons (exec_logicImm (by decide)) (k _ (Upd.write _ _ _))

private theorem wp_sltu {d n m : Reg}
    (k : ∀ s', Upd s s' d (if s.gpr n < s.gpr m then 1 else 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.sltu d n m :: is)) s Q :=
  WP.cons exec_sltu (k _ (Upd.write _ _ _))

end

private theorem and7_eq_zero {x : BitVec 64} (h : x &&& 7 = 0) : x.toNat % 8 = 0 := by
  obtain h' := congrArg BitVec.toNat h
  rwa [BitVec.toNat_and, show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at h'

/-- `laneCheck`, from `s2` = `st`, `s4` = `j` and `s6` = `n`: it changes only
`t1`–`t4`, leaves `st + j` in `t2`, leaves `t1 = 0` only if `j` and `st + j`
are multiples of 8 and `n ≥ 8`, and `t4 = 0` only if `s5` is a multiple of 8. -/
theorem laneCheck_ok {s : State} {st : Addr} {j n : Nat} (h2 : s.gpr .s2 = st)
    (h4 : s.gpr .s4 = BitVec.ofNat 64 j) (h6 : s.gpr .s6 = BitVec.ofNat 64 n) (hj : j < 2 ^ 64)
    (hn : n < 2 ^ 64) :
    WP isa (.block laneCheck) s fun s' =>
      (∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) ∧
      s'.gpr .t2 = st + BitVec.ofNat 64 j ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.sp = s.sp ∧
      (s'.gpr .t1 = 0 → j % 8 = 0 ∧ (st + BitVec.ofNat 64 j).toNat % 8 = 0 ∧ 8 ≤ n) ∧
      (s'.gpr .t4 = 0 → (s.gpr .s5).toNat % 8 = 0) := by
  unfold laneCheck
  refine wp_add fun s₁ u₁ => wp_or fun s₂ u₂ => wp_andi7 fun s₃ u₃ =>
    wp_li (by decide) fun s₄ u₄ => wp_sltu fun s₅ u₅ => wp_or fun s₆ u₆ =>
    wp_andi7 fun s₇ u₇ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [u₇.other r h4, u₆.other r h1, u₅.other r h3, u₄.other r h4, u₃.other r h1,
        u₂.other r h1, u₁.other r h2]
  obtain ht2 : s₇.gpr .t2 = st + BitVec.ofNat 64 j := by
    rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h2, h4]
  refine ⟨g, ht2, by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem],
    by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp], fun hz => ?_, fun hz => ?_⟩
  · have e6 : s₄.gpr .s6 = BitVec.ofNat 64 n := by
      rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide), h6]
    obtain e4 : s₁.gpr .s4 = BitVec.ofNat 64 j := by rw [u₁.other _ (by decide), h4]
    obtain e2 : s₁.gpr .t2 = st + BitVec.ofNat 64 j := by rw [u₁.gpr, h2, h4]
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₅.gpr, u₄.gpr,
      u₄.other _ (by decide), u₃.gpr, u₂.gpr, e6, e4, e2] at hz
    obtain ⟨ha, hb⟩ := BitVec.or_eq_zero_iff.mp hz
    rw [BitVec.and_or_distrib_right] at ha
    obtain ⟨h₁, h₃⟩ := BitVec.or_eq_zero_iff.mp ha
    obtain h₃' := and7_eq_zero h₃
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj] at h₃'
    refine ⟨h₃', and7_eq_zero h₁, ?_⟩
    by_cases hl : BitVec.ofNat 64 n < 8#64
    · rw [ite_eq_left hl] at hb; exact absurd hb (by decide)
    · rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] at hl
      exact Nat.le_of_not_lt hl
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)] at hz
    exact and7_eq_zero hz

/-- `loadData`: the lane at `a` (`s5`) into `t1`, changing only `t1`, `t3` and
`t4`. -/
theorem loadData_ok {al : Bool} {rest : List Instr} {s : State} {Q : State → Prop} {a : Addr}
    (h5 : s.gpr .s5 = a) (hal : al = true → a.toNat % 8 = 0) (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', Words64.Upd3 s s' .t1 .t3 .t4 (s.mem.readW a 64) → WP isa (.block rest) s' Q) :
    WP isa (.block (loadData al ++ rest)) s Q := by
  cases al
  · rw [loadData, ite_eq_right (by decide), WP.block_append_iff]
    obtain ea : s.gpr .s5 + BitVec.ofNat 64 0 = a := by rw [h5]; simp
    refine WP.mono (Words64.loadLE64_ok (d := .t1) (tmp := .t3) (tmp2 := .t4) (n := .s5) (off := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [ea]; exact hin)) fun s' u => k s' ?_
    rw [ea] at u; exact u
  · rw [loadData, ite_eq_left rfl]
    exact wp_ld (a := a) (by decide) (by rw [h5]; simp) (hal rfl) hin fun s' u =>
      k s' ⟨u.gpr, fun r h1 _ _ => u.other r h1, u.mem, u.rd, u.wr, u.sp⟩

/-- `storeData`: `t1` to the lane at `a` (`s5`), changing only `t3` and `t4`. -/
theorem storeData_ok {al : Bool} {rest : List Instr} {s : State} {Q : State → Prop} {a : Addr}
    (h5 : s.gpr .s5 = a) (hal : al = true → a.toNat % 8 = 0) (hout : InRegions s.wr a 8)
    (k : ∀ s', (∀ r, r ≠ .t3 → r ≠ .t4 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW a (s.gpr .t1) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      WP isa (.block rest) s' Q) :
    WP isa (.block (storeData al ++ rest)) s Q := by
  cases al
  · rw [storeData, ite_eq_right (by decide), WP.block_append_iff]
    obtain ea : s.gpr .s5 + BitVec.ofNat 64 0 = a := by rw [h5]; simp
    refine WP.mono (Words64.storeLE64_ok (v := .t1) (tmp := .t3) (tmp2 := .t4) (n := .s5) (off := 0)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by rw [ea]; exact hout))
      fun s' ⟨g, m, rd, wr, sp⟩ => k s' g (by rw [m, ea]) rd wr sp
  · rw [storeData, ite_eq_left rfl]
    exact wp_sd (a := a) (by decide) (by rw [h5]; simp) (hal rfl) hout fun s' u =>
      k s' (fun r _ _ => by rw [u.gpr]) u.mem u.rd u.wr u.sp

end VG.Proof.Sha3.RISCV64.Stream

end

end

/-!
# The SHA-3 sponge on RISC-V: `absorb`

The structure of the PPC64LE proof (`Proof/Sha3/PPC64LE/Stream/Absorb.lean`),
a lane (`body_word`) or a byte (`body_byte`) at a time, in the frame of
`Stream/Common.lean`.
-/

@[expose] public section

namespace VG.Proof.Sha3.RISCV64.Stream.Absorb

open VG VG.RISCV64 VG.RISCV64.Wp VG.Impl.Sha3.RISCV64.Stream
open VG.Proof.Sha3.RISCV64 VG.Proof.Sha3.RISCV64.Stream
open VG.Proof.Sha3 (Rep rep_append xorByte stateAt_xorByte ofNat_beq_zero sub_beq_zero sub_ofNat
  xor_setWidth writeW8_apply bytesAt_succ bytesAt_length toNat_ofNat_lt xorAt xorAt_single byteOf_xorAt
  byteOf_stateAt writeW64_byte)
open VG.Spec.Sha3 (stateAt keccakF bytesAt rates)

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev st : Addr := s₀.gpr .a0
abbrev rt : Nat := (s₀.gpr .a1).toNat
abbrev pos : Nat := (s₀.gpr .a2).toNat
abbrev dp : Addr := s₀.gpr .a3
abbrev len : Nat := (s₀.gpr .a4).toNat
abbrev stR : Region := ⟨st s₀, 200⟩
abbrev dR : Region := ⟨dp s₀, len s₀⟩
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dp s₀) c

/-- The messages the initial state and position represent. -/
def Msg (msg : List Byte) : Prop :=
  stateAt s₀.mem (st s₀) = Rep (rt s₀) msg ∧ pos s₀ = msg.length % rt s₀

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀]
  wr : s₀.wr = [stR s₀]
  d_st : (dR s₀).Disjoint (stR s₀)
  stk : Stk s₀
  k_st : (KR s₀).Disjoint (stR s₀)
  k_d : (KR s₀).Disjoint (dR s₀)
  rate : rt s₀ ∈ rates
  pos_lt : pos s₀ < rt s₀

theorem pre_of {s₀ : State} (h : Proof.Sha3.absorbRISCV64.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, ⟨h4, h5⟩, h6, h7, h8, h9⟩

theorem Pre.rt_pos {s₀ : State} (hp : Pre s₀) : 0 < rt s₀ ∧ rt s₀ ≤ 168 := by
  obtain h := Proof.Sha3.rate_bounds hp.rate
  omega_using [h]

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 64 := (s₀.gpr .a4).isLt

/-- The callee-saved registers our code never writes. -/
abbrev untouched : List Reg := [.s0, .s1, .s7, .s8, .s9, .s10, .s11]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = [dR s₀]
  wr : s.wr = [BR s₀, stR s₀]
  sp : s.sp = B s₀
  s2 : s.gpr .s2 = st s₀
  s3 : s.gpr .s3 = s₀.gpr .a1
  s5 : s.gpr .s5 = dp s₀ + BitVec.ofNat 64 c
  s6 : s.gpr .s6 = BitVec.ofNat 64 (len s₀ - c)
  frame : Frame [stR s₀, KR s₀] s₀.mem s.mem
  saved : Saved (B s₀) s₀.gpr s.mem
  untouched : ∀ r ∈ untouched, s.gpr r = s₀.gpr r

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv (s₀ : State) (c : Nat) (s : State) : Prop extends Common s₀ c s where
  s4 : s.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)
  repr : ∀ msg, Msg s₀ msg → stateAt s.mem (st s₀) = Rep (rt s₀) (msg ++ D s₀ c)

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre s₀) {c : Nat} {s : State} (h : Common s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dp s₀ + BitVec.ofNat 64 i) = s₀.mem (dp s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.k_d.symm⟩) (Nat.le_of_lt (len_lt s₀)) hi

/-! ## The prologue -/

theorem prologue_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.block setup) (allocd 48 s₀) (Inv s₀ 0) := by
  have hk := hp.stk
  unfold setup
  refine save_ok (s := allocd 48 s₀) hk.B_al (fun d hd₂ => ⟨BR s₀, List.mem_cons_self ..,
      Offset.contains_base _ (by omega_using [hd₂]) (by omega_using [hd₂])⟩)
    fun s₁ g₁ rd₁ wr₁ sp₁ sv₁ f₁ => ?_
  refine wp_mv fun s₂ u₂ => wp_mv fun s₃ u₃ => wp_mv fun s₄ u₄ => wp_mv fun s₅ u₅ =>
    wp_mv fun s₆ u₆ => WP.block_nil ?_
  obtain hm : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain f₁' : Frame [stR s₀, KR s₀] s₀.mem s₁.mem :=
    f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨KR s₀, by simp, by
        rw [show (allocd 48 s₀).sp = B s₀ from rfl, hk.B_eq]; exact sub_K s₀ (by omega_using [])⟩
  obtain g : ∀ r, r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h => g₁ r h
  refine ⟨⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hm]; exact f₁', by rw [hm]; exact sv₁,
      fun r hr => ?_⟩, ?_, fun msg ⟨hs, _⟩ => ?_⟩
  · rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]; exact hp.rd
  · rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]; simp only [allocd, hp.wr]
  · rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]; rfl
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g _ (by decide)]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide)]; simp
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide), Nat.sub_zero]; simp [len]
  · have : r ≠ .s2 ∧ r ≠ .s3 ∧ r ≠ .s4 ∧ r ≠ .s5 ∧ r ≠ .s6 ∧ r ≠ .t0 := by revert r; decide
    rw [u₆.other _ this.2.2.2.2.1, u₅.other _ this.2.2.2.1, u₄.other _ this.2.2.1,
      u₃.other _ this.2.1, u₂.other _ this.1, g _ this.2.2.2.2.2]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g _ (by decide), Nat.add_zero,
      Nat.mod_eq_of_lt hp.pos_lt]
    simp [pos]
  · rw [hm, show D s₀ 0 = [] by simp [bytesAt], List.append_nil, ← hs]
    exact Proof.Sha3.stateAt_congr fun i hi =>
      f₁.bytes (R := stR s₀) (by
        simpa using (hp.k_st.sub_left (by
          rw [show (allocd 48 s₀).sp = B s₀ from rfl, hk.B_eq]; exact sub_K s₀ (by omega_using []))).symm)
        (by show 200 ≤ 2 ^ 64; decide) hi

/-! ## One iteration -/

/-- The byte at position `j` XORed in. -/
theorem body_byte {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa (.block absorbByte) s fun s' =>
      Common s₀ (c + 1) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 1) ∧
      stateAt s'.mem (st s₀) = xorByte (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (s₀.mem (dp s₀ + BitVec.ofNat 64 c)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain hl := len_lt s₀
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj ⊢
  obtain hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  obtain hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 1 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj])⟩
  refine wp_lbu (t := .t1) (a := dp s₀ + BitVec.ofNat 64 c) (by decide) (by rw [hI.s5]; simp)
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc, hl])⟩ fun s₁ u₁ => ?_
  refine wp_add fun s₂ u₂ => ?_
  obtain ea : s₂.gpr .t2 + BitVec.ofNat 64 0 = st s₀ + BitVec.ofNat 64 j := by
    rw [u₂.gpr, u₁.other _ (by decide), u₁.other _ (by decide), hI.s2, hr3]; simp
  refine wp_lbu (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide) ea
    (hsin _ (by simp [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₃ u₃ => ?_
  refine wp_xor fun s₄ u₄ => ?_
  refine wp_sb (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide)]; exact ea)
    (hsin _ (by simp [u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₅ g₅ => ?_
  refine wp_addi (by decide) fun s₆ u₆ => wp_addi (by decide) fun s₇ u₇ =>
    wp_subi (imm := 1) (by decide) fun s₈ u₈ => WP.block_nil ?_
  obtain hv : (s₄.gpr .t1).setWidth 8 =
      s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j) := by
    rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, u₃.gpr, u₂.mem, u₁.mem,
      xor_setWidth, hI.data hp hc]
  obtain hm₈ : s₈.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j)
      (s₀.mem (dp s₀ + BitVec.ofNat 64 c) ^^^ s.mem (st s₀ + BitVec.ofNat 64 j)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, g₅.mem, hv, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hf : Frame [stR s₀] s.mem s₈.mem := by
    rw [hm₈]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  obtain g : ∀ r, r ≠ .t1 → r ≠ .t2 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 →
      s₈.gpr r = s.gpr r := fun r h1 h2 h3 h4 h33 h5 => by
    rw [u₈.other r h5, u₇.other r h33, u₆.other r h4, g₅.gpr, u₄.other r h1, u₃.other r h3,
      u₂.other r h2, u₁.other r h1]
  obtain h3 : s₈.gpr .s4 = BitVec.ofNat 64 (j + 1) := by
    rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr3, ← BitVec.ofNat_add]
  refine ⟨⟨by omega_using [hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, g₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, g₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₈.sp, u₇.sp, u₆.sp, g₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s5, BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), g₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hI.s6, sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame (fun d h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_st.sub_left (hp.stk.slot_sub h₂)) hf
  · have hne : r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · refine stateAt_xorByte (by omega_using [hr₁, hj]) ?_ fun i hi hij => ?_
    · rw [hm₈, writeW8_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), BitVec.xor_comm]
    · rw [hm₈, writeW8_apply, ite_eq_right_of_eq_false _ _
        (eq_false (VG.Proof.Sha3.ne_of_lt200 hi (by omega_using [hr₁, hj]) hij))]

/-- The bytes `c … c + n - 1` of the data follow the first `c`. -/
theorem bytesAt_add (m : Mem) (p : Addr) (c : Nat) :
    ∀ n, bytesAt m p (c + n) = bytesAt m p c ++ bytesAt m (p + BitVec.ofNat 64 c) n
  | 0 => by simp [bytesAt]
  | n + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m p c n, bytesAt_succ, List.append_assoc,
      BitVec.add_assoc, ← BitVec.ofNat_add]

theorem rate_mod8 {r : Nat} (h : r ∈ rates) : r % 8 = 0 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- A lane of a state in memory written: its 8 bytes XORed with `bs`. -/
theorem stateAt_write_lane {m : Mem} {p : Addr} {j : Nat} (hj : j + 8 ≤ 200) {v : BitVec 64}
    {bs : List Byte} (hbs : bs.length = 8)
    (hv : ∀ d < 8, v.extractLsb' (8 * d) 8 = m (p + BitVec.ofNat 64 (j + d)) ^^^ bs.getD d 0) :
    stateAt (m.writeW (p + BitVec.ofNat 64 j) v) p = xorAt (stateAt m p) j bs :=
  Proof.Sha3.ext_bytes fun i hi => by
    rw [byteOf_xorAt _ _ _ hi, byteOf_stateAt _ _ hi, byteOf_stateAt _ _ hi, hbs]
    by_cases c : j ≤ i ∧ i < j + 8
    · rw [ite_eq_left c, show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1],
        writeW64_byte _ _ _ (by omega_using [c]), hv _ (by omega_using [c]), Nat.add_sub_cancel' c.1,
        show p + BitVec.ofNat 64 j + BitVec.ofNat 64 (i - j) = p + BitVec.ofNat 64 i by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_cancel' c.1]]
    · rw [ite_eq_right c, Mem.writeW, Mem.write_apply]
      rw [Offset.sub_toNat' _ (by omega_using [hj]) (by omega_using [hi])]
      split <;> omega_arith

/-- The lane of data at `c` XORed into the lane at position `j`, both
aligned. -/
theorem body_word {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c + 8 ≤ len s₀) {s : State}
    (hI : Inv s₀ c s) (hj8 : (pos s₀ + c) % rt s₀ % 8 = 0)
    (ht2 : s.gpr .t2 = st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀))
    (hal : (st s₀ + BitVec.ofNat 64 ((pos s₀ + c) % rt s₀)).toNat % 8 = 0)
    {al : Bool} (hdal : al = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) :
    WP isa (.block (absorbLane al)) s fun s' =>
      Common s₀ (c + 8) s' ∧ s'.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + 8) ∧
      stateAt s'.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) 8) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hl := len_lt s₀
  have h8 := rate_mod8 hp.rate
  have hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  generalize hjd : (pos s₀ + c) % rt s₀ = j at hj hj8 ht2 hal ⊢
  have hj' : j + 8 ≤ rt s₀ := by omega_using [h8, hj, hj8]
  have hr3 : s.gpr .s4 = BitVec.ofNat 64 j := by rw [hI.s4, hjd]
  have hsin : ∀ rs : List Region, stR s₀ ∈ rs → InRegions rs (st s₀ + BitVec.ofNat 64 j) 8 :=
    fun rs h => ⟨stR s₀, h, Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj])⟩
  unfold absorbLane
  refine loadData_ok (a := dp s₀ + BitVec.ofNat 64 c) (by rw [hI.s5]) hdal
    ⟨dR s₀, by simp [hI.rd], Offset.contains_base _ (by omega_using [hc]) (by omega_using [hc, hl])⟩ fun s₁ u₁ => ?_
  refine wp_ld (t := .t3) (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₁.rd, u₁.wr, hI.rd, hI.wr])) fun s₂ u₂ => ?_
  refine wp_xor fun s₃ u₃ => ?_
  refine wp_sd (a := st s₀ + BitVec.ofNat 64 j) (by decide)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), ht2]; simp) hal
    (hsin _ (by simp [u₃.wr, u₂.wr, u₁.wr, hI.wr])) fun s₄ g₄ => ?_
  refine wp_addi (by decide) fun s₅ u₅ => wp_addi (by decide) fun s₆ u₆ =>
    wp_subi (imm := 8) (by decide) fun s₇ u₇ => WP.block_nil ?_
  have hv : s₃.gpr .t1 = s.mem.readW (dp s₀ + BitVec.ofNat 64 c) 64 ^^^
      s.mem.readW (st s₀ + BitVec.ofNat 64 j) 64 := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem]
  have hm₇ : s₇.mem = s.mem.writeW (st s₀ + BitVec.ofNat 64 j) (s₃.gpr .t1) := by
    rw [u₇.mem, u₆.mem, u₅.mem, g₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hf : Frame [stR s₀] s.mem s₇.mem := by
    rw [hm₇]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega_using [hr₁, hj]) (by omega_using [hr₁, hj]))
  have g : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .s5 → r ≠ .s4 → r ≠ .s6 → r ≠ .t4 →
      s₇.gpr r = s.gpr r := fun r h1 h3 h4 h33 h5 h6 => by
    rw [u₇.other r h5, u₆.other r h33, u₅.other r h4, g₄.gpr, u₃.other r h1, u₂.other r h3,
      u₁.other r h1 h3 h6]
  have h3 : s₇.gpr .s4 = BitVec.ofNat 64 (j + 8) := by
    rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hr3,
      ← BitVec.ofNat_add]
  refine ⟨⟨by omega_using [hc], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_⟩, h3, ?_⟩
  · rw [u₇.rd, u₆.rd, u₅.rd, g₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₇.wr, u₆.wr, u₅.wr, g₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [u₇.sp, u₆.sp, u₅.sp, g₄.sp, u₃.sp, u₂.sp, u₁.sp, hI.sp]
  · rw [g .s2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s2]
  · rw [g .s3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hI.s3]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s5,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), g₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide) (by decide) (by decide), hI.s6,
      sub_ofNat (by omega_using [hc]), Nat.sub_sub]
  · exact hI.frame.trans (hf.mono (by simp))
  · exact hI.saved.frame (fun d h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_st.sub_left (hp.stk.slot_sub h₂)) hf
  · have hne : r ≠ .t1 ∧ r ≠ .t3 ∧ r ≠ .s5 ∧ r ≠ .s4 ∧ r ≠ .s6 ∧ r ≠ .t4 := by revert r; decide
    rw [g r hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2]
    exact hI.untouched r hr
  · rw [hm₇]
    refine stateAt_write_lane (by omega_using [hr₁, hj]) (bytesAt_length _ _ _) fun d hd => ?_
    rw [hv, BitVec.extractLsb'_xor, Mem.readW, Mem.readW, BitVec.setWidth_eq, BitVec.setWidth_eq,
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_using [hd]),
      Mem.extractLsb'_read _ _ (show d < 64 / 8 by omega_using [hd]),
      BitVec.xor_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 1
    simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd,
      Option.map_some, Option.getD_some]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, hI.data hp (by omega_using [hc, hd])]

theorem keep_preserved : ∀ r ∈ untouched, r ∈ preserved := by decide

/-- The permutation if the block is complete, after `n` bytes of data that
fit in it. -/
theorem full_ok {s₀ : State} (hp : Pre s₀) {c n : Nat} (hn : 0 < n)
    (hfit : (pos s₀ + c) % rt s₀ + n ≤ rt s₀) {s s₁ : State}
    (hI : Inv s₀ c s) (hC : Common s₀ (c + n) s₁)
    (h3 : s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n))
    (hst : stateAt s₁.mem (st s₀) = xorAt (stateAt s.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) :
    WP isa permuteIfFull s₁ (Inv s₀ (c + n)) := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  have hk := hp.stk
  obtain hlen : ∀ msg, Msg s₀ msg → (msg ++ D s₀ c).length % rt s₀ = (pos s₀ + c) % rt s₀ :=
    fun msg ⟨_, hpm⟩ => by rw [List.length_append, bytesAt_length, hpm, Nat.mod_add_mod]
  obtain hrep : ∀ msg, Msg s₀ msg → Rep (rt s₀) (msg ++ D s₀ (c + n)) =
      if (pos s₀ + c) % rt s₀ + n = rt s₀ then keccakF (stateAt s₁.mem (st s₀))
      else stateAt s₁.mem (st s₀) := fun msg hm => by
    rw [D, bytesAt_add, ← List.append_assoc, rep_append hr₀ (by omega_using [hr₁]) _ _
      (by rw [bytesAt_length]; exact hn) (by rw [bytesAt_length, hlen msg hm]; exact hfit),
      hlen msg hm, bytesAt_length, hst, hI.repr msg hm]
  obtain hpc : (pos s₀ + (c + n)) % rt s₀ = if (pos s₀ + c) % rt s₀ + n = rt s₀ then 0
      else (pos s₀ + c) % rt s₀ + n := by
    obtain e := Nat.div_add_mod (pos s₀ + c) (rt s₀)
    rw [show pos s₀ + (c + n) = (pos s₀ + c) + n by omega_using []]
    generalize (pos s₀ + c) % rt s₀ = j at e hfit ⊢
    generalize (pos s₀ + c) / rt s₀ = q at e
    rw [← e]
    split
    · rw [Nat.add_assoc, ‹j + n = rt s₀›, ← Nat.mul_succ, Nat.mul_mod_right]
    · rw [Nat.add_assoc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega_arith)]
  unfold permuteIfFull
  refine WP.seq (wp_sub fun s₂ u₂ => WP.block_nil ?_)
  obtain hC₂ : Common s₀ (c + n) s₂ :=
    { hC with rd := u₂.rd.trans hC.rd, wr := u₂.wr.trans hC.wr, sp := u₂.sp.trans hC.sp
              s2 := (u₂.other _ (by decide)).trans hC.s2, s3 := (u₂.other _ (by decide)).trans hC.s3
              s5 := (u₂.other _ (by decide)).trans hC.s5, s6 := (u₂.other _ (by decide)).trans hC.s6
              frame := u₂.mem ▸ hC.frame, saved := u₂.mem ▸ hC.saved
              untouched := fun r hr => (u₂.other r (by revert r; decide)).trans (hC.untouched r hr) }
  obtain hz : isa.eval (.zero .t1) s₂ = some (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) := by
    show eval (.zero .t1) s₂ = _
    rw [eval_zero, u₂.gpr, h3, hC.s3, sub_beq_zero (by have := (s₀.gpr .a1).isLt; omega_using [hfit, hr₁])]
  refine WP.ite (decide ((pos s₀ + c) % rt s₀ + n = rt s₀)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.seq (wp_li (by decide) fun s₃ u₃ => WP.block_nil ?_)
    obtain sp₃ : s₃.sp = B s₀ := by rw [u₃.sp, hC₂.sp]
    refine permuteAt_ok (st := st s₀) (by rw [u₃.other _ (by decide), hC₂.s2])
      (by rw [sp₃]; exact hk.B_al) (by rw [sp₃]; exact hk.B_1120)
      (by rw [sp₃]; exact (hp.k_st.sub_left hk.scr_sub).symm)
      (by rw [sp₃]; exact hp.k_st.sub_left hk.below_sub)
      (by
        rw [u₃.wr, hC₂.wr]
        apply Covers.of_sub
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact ⟨stR s₀, by simp, 0, by simp, by simp⟩)
      fun s₄ rd₄ wr₄ sp₄ cs₄ f₄ e₄ => ?_
    rw [sp₃] at f₄
    have hm₃ : s₃.mem = s₂.mem := u₃.mem
    refine ⟨⟨hC₂.c_le, by rw [rd₄, u₃.rd, hC₂.rd], by rw [wr₄, u₃.wr, hC₂.wr], by rw [sp₄, sp₃],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s2],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s3],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s5],
      by rw [cs₄ _ (by decide), u₃.other _ (by decide), hC₂.s6], ?_, ?_,
      fun r hr => by rw [cs₄ _ (keep_preserved r hr), u₃.other _ (by revert r; decide),
        hC₂.untouched r hr]⟩, ?_, fun msg hm => ?_⟩
    · rw [hm₃] at f₄
      exact hC₂.frame.trans (f₄.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨stR s₀, by simp, fun _ h => h⟩
        · exact ⟨KR s₀, by simp, hk.scr_sub⟩
        · exact ⟨KR s₀, by simp, hk.below_sub⟩)
    · rw [hm₃] at f₄
      refine hC₂.saved.frame (fun d h₂ r hr => ?_) f₄
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.k_st.sub_left (hk.slot_sub h₂)
      · exact hk.slot_scr h₂
      · exact hk.slot_below h₂
    · rw [cs₄ _ (by decide), u₃.gpr, hpc, ite_eq_left_of_eq_true _ _ (eq_true hb)]
    · rw [e₄, hm₃, u₂.mem, hrep msg hm, ite_eq_left_of_eq_true _ _ (eq_true hb)]
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.block_nil { hC₂ with s4 := ?_, repr := fun msg hm => ?_ }
    · rw [u₂.other _ (by decide), h3, hpc, ite_eq_right_of_eq_false _ _ (eq_false hb)]
    · rw [u₂.mem, hrep msg hm, ite_eq_right_of_eq_false _ _ (eq_false hb)]

theorem body_ok {s₀ : State} (hp : Pre s₀) {c : Nat} (hc : c < len s₀) {s : State}
    (hI : Inv s₀ c s) :
    WP isa absorbBody s fun s' => ∃ c', c < c' ∧ c' ≤ len s₀ ∧ Inv s₀ c' s' := by
  have ⟨hr₀, hr₁⟩ := hp.rt_pos
  obtain h8 := rate_mod8 hp.rate
  obtain hj : (pos s₀ + c) % rt s₀ < rt s₀ := Nat.mod_lt _ hr₀
  obtain hl := len_lt s₀
  unfold absorbBody
  refine WP.seq (WP.mono (laneCheck_ok hI.s2 hI.s4 hI.s6 (by omega_using [hr₁, hj]) (by omega_using [hl]))
    fun s₇ ⟨oth, ht2, m₇, rd₇, wr₇, sp₇, hz, hd⟩ => ?_)
  obtain o : ∀ r, r ≠ .t1 ∧ r ≠ .t2 ∧ r ≠ .t3 ∧ r ≠ .t4 → s₇.gpr r = s.gpr r :=
    fun r h => oth r h.1 h.2.1 h.2.2.1 h.2.2.2
  obtain hI₇ : Inv s₀ c s₇ :=
    { c_le := hI.c_le, rd := rd₇.trans hI.rd, wr := wr₇.trans hI.wr, sp := sp₇.trans hI.sp
      s2 := (o _ (by decide)).trans hI.s2, s3 := (o _ (by decide)).trans hI.s3
      s5 := (o _ (by decide)).trans hI.s5, s6 := (o _ (by decide)).trans hI.s6
      frame := m₇ ▸ hI.frame, saved := m₇ ▸ hI.saved
      untouched := fun r hr => (o r (by revert r; decide)).trans (hI.untouched r hr)
      s4 := (o _ (by decide)).trans hI.s4
      repr := fun msg hm => by rw [m₇]; exact hI.repr msg hm }
  refine WP.seq (WP.mono (Q := fun (s₁ : State) => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
      c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
      s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
      stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
        (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n)) ?_
    fun s₁ ⟨n, hn, hfit, hcn, hC, h3, hst⟩ => WP.mono (full_ok hp hn hfit hI₇ hC h3 hst)
      fun s' h => ⟨c + n, by omega_using [hn], hcn, h⟩)
  unfold step
  refine WP.ite (s₇.gpr .t1 == 0) (by show eval (.zero .t1) s₇ = _; rw [eval_zero])
    (fun hb => ?_) (fun _ => ?_)
  · obtain ⟨m8, al, l8⟩ := hz (by simpa using hb)
    obtain lane : ∀ b : Bool, (b = true → (dp s₀ + BitVec.ofNat 64 c).toNat % 8 = 0) →
        WP isa (.block (absorbLane b)) s₇ fun s₁ => ∃ n, 0 < n ∧ (pos s₀ + c) % rt s₀ + n ≤ rt s₀ ∧
          c + n ≤ len s₀ ∧ Common s₀ (c + n) s₁ ∧
          s₁.gpr .s4 = BitVec.ofNat 64 ((pos s₀ + c) % rt s₀ + n) ∧
          stateAt s₁.mem (st s₀) = xorAt (stateAt s₇.mem (st s₀)) ((pos s₀ + c) % rt s₀)
            (bytesAt s₀.mem (dp s₀ + BitVec.ofNat 64 c) n) := fun b hb =>
      WP.mono (body_word hp (by omega_using [l8]) hI₇ m8 ht2 al hb)
        fun s₁ ⟨hC, h3, hst⟩ => ⟨8, by decide, by omega_using [h8, hj, m8], by omega_using [l8], hC, h3, hst⟩
    refine WP.ite (s₇.gpr .t4 == 0) (by show eval (.zero .t4) s₇ = _; rw [eval_zero])
      (fun hb4 => lane true fun _ => ?_) (fun _ => lane false fun h => absurd h (by decide))
    rw [← hI.s5]; exact hd (by simpa using hb4)
  · refine WP.mono (body_byte hp hc hI₇) fun s₁ ⟨hC, h3, hst⟩ =>
      ⟨1, by decide, by omega_using [hj], by omega_using [hc], hC, h3, ?_⟩
    rw [hst]
    simp [bytesAt, xorAt_single]

/-! ## The whole function -/

theorem preserved_split : ∀ r ∈ preserved, r ∈ saved.map Prod.fst ∨ r ∈ untouched := by decide

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa absorb s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha3.absorbRISCV64.post s₀ s' := by
  have hk := hp.stk
  obtain hl := len_lt s₀
  have ⟨hr₀, _⟩ := hp.rt_pos
  unfold absorb withLoop frameBytes
  refine WP.alloc ⟨by decide, by decide, by decide⟩ (by have := hk.sp; omega_using [this]) ?_
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (len s₀)) ?_ fun s₂ hI₂ => ?_)
  · refine WP.ite (decide (len s₀ = 0))
      (by show eval (.zero .s6) s₁ = _
          rw [eval_zero, hI.s6, Nat.sub_zero, ofNat_beq_zero (by omega_using [hl])])
      (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hI)
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.loop (M := isa) (fun n s => ∃ c, n = len s₀ - c ∧ c < len s₀ ∧ Inv s₀ c s) ?_
        (len s₀) s₁ ⟨0, rfl, by omega_using [hb], hI⟩
      rintro n s ⟨c, rfl, hcl, hI⟩
      refine WP.mono (body_ok hp hcl hI) fun s' ⟨c', hcc, hcl', hI'⟩ => ?_
      obtain hz : isa.eval (.nonzero .s6) s' = some (decide (len s₀ - c' ≠ 0)) := by
        show eval (.nonzero .s6) s' = _
        rw [eval_nonzero, hI'.s6, bne, ofNat_beq_zero (by omega_using [hl])]
        simp
      by_cases he : len s₀ - c' = 0
      · refine .inl ⟨by rw [hz]; simp [he], ?_⟩
        rwa [show c' = len s₀ by omega_using [hcl', he]] at hI'
      · exact .inr ⟨by rw [hz]; simp [he], len s₀ - c', by omega_using [hcl, hcc], c', rfl, by omega_using [he], hI'⟩
  · refine epilogue_ok (g := s₀.gpr) (by rw [hI₂.sp]; exact hk.B_al)
      (fun d hd₂ => by
        rw [hI₂.rd, hI₂.wr, hI₂.sp]
        exact ⟨BR s₀, by simp, Offset.contains_base _ (by omega_using [hd₂]) (by omega_using [hd₂])⟩)
      (by rw [hI₂.sp]; exact hI₂.saved) fun s' h0 hsv hother hm hrd hwr hsp mL _ fl => ?_
    refine ⟨⟨fun r hr => ?_, ?_, ?_⟩, fun msg hR hpm => ?_, ?_⟩
    · show s'.gpr r = _
      rcases preserved_split r hr with h | h
      · obtain ⟨p, hp', rfl⟩ := List.mem_map.mp h
        exact hsv p hp'
      · rw [hother r (by revert r; decide) (by revert r; decide) (by revert r; decide)]
        exact hI₂.untouched r h
    · show s'.sp + BitVec.ofNat 64 48 = s₀.sp
      rw [hsp, hI₂.sp, BitVec.sub_add_cancel]
    · exact hsv (.ra, 0) (by decide)
    · -- The `free` loses the frame's bytes, which lie apart from the state.
      rw [Proof.Sha3.repr_iff, Proof.Sha3.stateAt_congr (m := s'.mem) fun i hi =>
        lost_byte fl (R := stR s₀) (hp.k_st.symm.sub_right (Offset.sub_below _ (by decide) (by decide))) hi, hm]
      exact hI₂.repr msg ⟨hR, hpm⟩
    · simp only [freed]
      rw [h0, hI₂.s4, toNat_ofNat_lt (by have := Nat.mod_lt (pos s₀ + len s₀) hr₀; omega_arith)]

end VG.Proof.Sha3.RISCV64.Stream.Absorb

end

end
