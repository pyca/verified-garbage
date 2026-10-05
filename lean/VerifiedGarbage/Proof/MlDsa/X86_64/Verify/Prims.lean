import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.SampleCT
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Spec.MlDsa.Contract
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
import VerifiedGarbage.Proof.MlKem.X86_64.Sample4Impl
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Base`. -/
section

/-!
# ML-DSA verification on x86-64: moves, layouts and calls

* The moves of a call's arguments (`glue_ok`): each argument register holds
  the argument's value (`Arg.val`: a pointer's address `pa`, or an integer).
* Layouts (`Lay`): the function keeps the address of each buffer it works in
  (its arguments and its working space) in a callee-saved register; a
  layout lists these registers with the lengths of their buffers, which are
  apart from the stack, and from each other where one of them is written
  (only `scratch`, in `rbx`: the inputs may overlap each other). A pointer
  (a register and an offset) into a buffer, and two pointers apart, are
  checked by evaluation (`inB`, `sepB`).
* What a piece of code leaves (`PostB`): the permissions, the registers of
  the layout and the stack pointer, and memory but within the regions it
  writes and the 32 bytes of stack below `rsp` (its calls' return
  addresses).
* A call of verified code, with the moves of its arguments before it
  (`callAt_ok`, `callAt_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.Sha3 (bytesAt)

/-! ## Moves -/

/-- The address of the pointer `p` in `s`. -/
abbrev pa (s : State) (p : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Addr := s.gpr p.1 + BitVec.ofNat 64 p.2

/-- The registers the moves of arguments write. -/
abbrev argRegs : List Reg := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

theorem argRegs_cs : ∀ r ∈ calleeSaved, r ∉ VG.Proof.MlDsa.X86_64.Verify.argRegs := by decide

/-- The value of an argument. -/
def _root_.VG.Impl.MlDsa.X86_64.Verify.Arg.val (s : State) : VG.Impl.MlDsa.X86_64.Verify.Arg → BitVec 64
  | .ptr p => VG.Proof.MlDsa.X86_64.Verify.pa s p
  | .imm v => BitVec.ofNat 64 v

/-- An argument whose moves `glue` makes: a pointer with an offset that fits
an immediate, based in a register the moves do not write, or an integer of
at most 31 bits. -/
def _root_.VG.Impl.MlDsa.X86_64.Verify.Arg.Ok : VG.Impl.MlDsa.X86_64.Verify.Arg → Prop
  | .ptr p => p.2 < 2 ^ 31 ∧ p.1 ∉ VG.Proof.MlDsa.X86_64.Verify.argRegs
  | .imm v => v < 2 ^ 31

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : BitVec.signExtend 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem sw_ofNat {n : Nat} (h : n < 2 ^ 32) : BitVec.setWidth 64 (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth64, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

theorem arg_ok (d : Reg) (a : VG.Impl.MlDsa.X86_64.Verify.Arg) (ha : a.Ok) (s : State) :
    WP isa (.block (a.instrs d)) s fun s' => (s'.gpr d = a.val s ∧ s'.mem = s.mem) ∧ Keep [d] s s' := by
  refine WP.keep _ ?_ (by cases a <;> cases d <;> rfl)
  cases a with
  | ptr p => simp only [Arg.instrs, Arg.val]; xrun [VG.Proof.MlDsa.X86_64.Verify.sx_ofNat ha.1]
  | imm v => simp only [Arg.instrs, Arg.val]; xrun [VG.Proof.MlDsa.X86_64.Verify.sw_ofNat (show v < 2 ^ 32 by have : v < 2 ^ 31 := ha; omega)]

/-- The moves of the arguments `as`, to distinct registers. -/
theorem glue_ok : ∀ (as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)), (∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs) → (as.map (·.1)).Nodup →
    ∀ s : State, WP isa (.block (glue as)) s fun s' =>
      ((∀ a ∈ as, s'.gpr a.1 = a.2.val s) ∧ s'.mem = s.mem) ∧ Keep (as.map (·.1)) s s'
  | [], _, _, s => WP.block_nil ⟨⟨fun _ h => absurd h List.not_mem_nil, rfl⟩, Keep.refl _ _⟩
  | (d, a) :: as, hok, hnd, s => by
    simp only [glue]
    rw [WP.block_append_iff]
    have ha := hok (d, a) (List.mem_cons_self ..)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.arg_ok d a ha.1 s) fun s₁ ⟨⟨hd, hm⟩, k₁⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok as (fun b hb => hok b (List.mem_cons_of_mem _ hb)) hnd.2 s₁)
      fun s₂ ⟨⟨hv, hm₂⟩, k₂⟩ => ⟨⟨fun b hb => ?_, hm₂.trans hm⟩, (k₁.trans k₂).mono fun r hr => ?_⟩
    · have hval : ∀ c : VG.Impl.MlDsa.X86_64.Verify.Arg, c.Ok → c.val s₁ = c.val s := fun c hc => by
        cases c with
        | ptr p => simp only [Arg.val, VG.Proof.MlDsa.X86_64.Verify.pa]; rw [k₁.gpr (fun h => hc.2 (by
            simp only [List.mem_singleton] at h; rw [h]; exact ha.2))]
        | imm v => rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [k₂.gpr hnd.1, hd]
      · rw [hv b hb, hval b.2 (hok b (List.mem_cons_of_mem _ hb)).1]
    · rcases List.mem_append.mp hr with hr | hr
      · simp only [List.mem_singleton] at hr; rw [hr]; exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ hr

/-- The moves of the arguments, which write only argument registers. -/
theorem glue_ok' {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs) (hnd : (as.map (·.1)).Nodup)
    (s : State) : WP isa (.block (glue as)) s fun s' =>
      ((∀ a ∈ as, s'.gpr a.1 = a.2.val s) ∧ s'.mem = s.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Verify.argRegs s s' :=
  WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok as hok hnd s) fun _ ⟨h, k⟩ => ⟨h, k.mono fun r hr => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr; exact (hok a ha).2⟩


/-! ## What a piece leaves -/

/-- The registers the function keeps the addresses of its buffers in. -/
abbrev bases : List Reg := [.rbx, .rbp, .r12, .r13]

/-- The registers of the buffers the function writes (`scratch`): a buffer
it only reads may overlap another such buffer, but not one of these. -/
abbrev wRegs : List Reg := [.rbx]

/-- What a call leaves: the permissions and the callee-saved registers, and
memory changed only within `W` and the stack. -/
structure Post (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  cs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame (W ++ [below (s.gpr .rsp) 32]) s.mem s'.mem

/-- What a piece of code leaves: the permissions, the registers `bases` and
the stack pointer, and memory but within `W` and the stack. -/
structure PostB (s s' : State) (W : List Region) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bs : ∀ r ∈ VG.Proof.MlDsa.X86_64.Verify.bases, s'.gpr r = s.gpr r
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame (W ++ [below (s.gpr .rsp) 32]) s.mem s'.mem

theorem Post.rsp {s s' : State} {W : List Region} (h : VG.Proof.MlDsa.X86_64.Verify.Post s s' W) : s'.gpr .rsp = s.gpr .rsp :=
  h.cs .rsp (by decide)

theorem Post.b {s s' : State} {W : List Region} (h : VG.Proof.MlDsa.X86_64.Verify.Post s s' W) : VG.Proof.MlDsa.X86_64.Verify.PostB s s' W :=
  ⟨h.rd, h.wr, fun r hr => h.cs r (by
    simp only [VG.Proof.MlDsa.X86_64.Verify.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide), h.rsp, h.frame⟩

theorem PostB.refl (s : State) (W : List Region) : VG.Proof.MlDsa.X86_64.Verify.PostB s s W :=
  ⟨rfl, rfl, fun _ _ => rfl, rfl, Frame.refl _ _⟩

theorem PostB.trans {s s₁ s₂ : State} {W₁ W₂ W : List Region} (h₁ : VG.Proof.MlDsa.X86_64.Verify.PostB s s₁ W₁) (h₂ : VG.Proof.MlDsa.X86_64.Verify.PostB s₁ s₂ W₂)
    (hw₁ : ∀ r ∈ W₁, r ∈ W) (hw₂ : ∀ r ∈ W₂, r ∈ W) : VG.Proof.MlDsa.X86_64.Verify.PostB s s₂ W := by
  refine ⟨h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, fun r hr => (h₂.bs r hr).trans (h₁.bs r hr),
    h₂.rsp.trans h₁.rsp, ?_⟩
  have f₂ := h₂.frame
  rw [h₁.rsp] at f₂
  refine (h₁.frame.mono fun r hr => ?_).trans (f₂.mono fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₁ r hr), List.mem_append_right _ hr]
  · rcases List.mem_append.mp hr with hr | hr
    exacts [List.mem_append_left _ (hw₂ r hr), List.mem_append_right _ hr]

/-- A block that keeps the registers `bases` and `rsp` and the permissions,
and writes within `W`. -/
theorem postB_of_keep {rs : List Reg} {s s' : State} {W : List Region} (k : Keep rs s s')
    (hrs : ∀ r ∈ .rsp :: VG.Proof.MlDsa.X86_64.Verify.bases, r ∉ rs) (hf : Frame W s.mem s'.mem) : VG.Proof.MlDsa.X86_64.Verify.PostB s s' W :=
  ⟨k.2.1, k.2.2, fun r hr => k.gpr (hrs r (List.mem_cons_of_mem _ hr)), k.gpr (hrs _ (List.mem_cons_self ..)),
    hf.mono fun _ hr => List.mem_append_left _ hr⟩

theorem PostB.pa {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.X86_64.Verify.PostB s s' W) {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} (h : p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) :
    VG.Proof.MlDsa.X86_64.Verify.pa s' p = VG.Proof.MlDsa.X86_64.Verify.pa s p := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.pa, hP.bs _ h]

/-! ## Checks -/

/-- The `len` bytes at `p` lie within the buffer of its register in the layout `bs`. -/
def inB (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) : Bool :=
  match bs.lookup p.1 with
  | some n => decide (p.2 + len ≤ n)
  | none => false

/-- The `l` bytes at `p` and the `k` bytes at `q` lie within their buffers,
apart: in different buffers, one of them written, or in the same buffer. -/
def sepB (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.X86_64.Verify.Ptr) (l : Nat) (q : VG.Impl.MlDsa.X86_64.Verify.Ptr) (k : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.inB bs p l && VG.Proof.MlDsa.X86_64.Verify.inB bs q k &&
    ((p.1 != q.1 && (decide (p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.wRegs) || decide (q.1 ∈ VG.Proof.MlDsa.X86_64.Verify.wRegs))) ||
      (p.1 == q.1 && (decide (p.2 + l ≤ q.2) || decide (q.2 + k ≤ p.2))))

theorem lookup_mem : ∀ {bs : List (Reg × Nat)} {r : Reg} {n : Nat}, bs.lookup r = some n → (r, n) ∈ bs
  | [], _, _, h => by simp [List.lookup] at h
  | (r', n') :: bs, r, n, h => by
    unfold List.lookup at h
    by_cases e : r = r'
    · subst e
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self ..
    · have : (r == r') = false := by simp [e]
      rw [this] at h
      exact List.mem_cons_of_mem _ (VG.Proof.MlDsa.X86_64.Verify.lookup_mem h)

theorem inB_spec {bs : List (Reg × Nat)} {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB bs p l = true) :
    ∃ n, (p.1, n) ∈ bs ∧ p.2 + l ≤ n := by
  unfold VG.Proof.MlDsa.X86_64.Verify.inB at h
  split at h
  · rename_i n hn; exact ⟨n, VG.Proof.MlDsa.X86_64.Verify.lookup_mem hn, of_decide_eq_true h⟩
  · cases h

theorem sepB_spec {bs : List (Reg × Nat)} {p q : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l k : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.sepB bs p l q k = true) :
    VG.Proof.MlDsa.X86_64.Verify.inB bs p l = true ∧ VG.Proof.MlDsa.X86_64.Verify.inB bs q k = true ∧
      ((p.1 ≠ q.1 ∧ (p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.wRegs ∨ q.1 ∈ VG.Proof.MlDsa.X86_64.Verify.wRegs)) ∨ (p.1 = q.1 ∧ (p.2 + l ≤ q.2 ∨ q.2 + k ≤ p.2))) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.sepB, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## Regions -/

theorem inRegions_sub {X : List Region} {a : Addr} {n off l : Nat} (h : InRegions X a n) (hl : off + l ≤ n)
    (hn : n < 2 ^ 64) : InRegions X (a + BitVec.ofNat 64 off) l := by
  obtain ⟨r, hr, hc⟩ := h
  refine ⟨r, hr, ?_⟩
  simp only [Region.Contains] at hc ⊢
  rw [show a + BitVec.ofNat 64 off - r.base = (a - r.base) + BitVec.ofNat 64 off by bv_omega, BitVec.toNat_add,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega)]
  have := Nat.mod_le ((a - r.base).toNat + off) (2 ^ 64)
  omega

/-! ## Layouts -/

/-- The buffers of `rbs` (read) and `wbs` (written), at the addresses in
their registers: small, apart from each other (where one is written) and
from the stack, not wrapping around, and permitted. -/
structure Lay (rbs wbs : List (Reg × Nat)) (s : State) : Prop where
  small : ∀ b ∈ rbs ++ wbs, b.2 < 2 ^ 31
  dj : ∀ b ∈ rbs ++ wbs, ∀ b' ∈ rbs ++ wbs, b.1 ≠ b'.1 → (b.1 ∈ VG.Proof.MlDsa.X86_64.Verify.wRegs ∨ b'.1 ∈ VG.Proof.MlDsa.X86_64.Verify.wRegs) →
    Region.Disjoint ⟨s.gpr b.1, b.2⟩ ⟨s.gpr b'.1, b'.2⟩
  stk : ∀ b ∈ rbs ++ wbs, (below (s.gpr .rsp) 32).Disjoint ⟨s.gpr b.1, b.2⟩
  nw : ∀ b ∈ rbs ++ wbs, (s.gpr b.1).toNat + b.2 ≤ 2 ^ 64
  rd : ∀ b ∈ rbs ++ wbs, InRegions (s.rd ++ s.wr) (s.gpr b.1) b.2
  wr : ∀ b ∈ wbs, InRegions s.wr (s.gpr b.1) b.2
  ret : ∀ b ∈ rbs ++ wbs, (Region.mk (s.gpr .rsp) 8).Disjoint ⟨s.gpr b.1, b.2⟩
  bs : ∀ b ∈ rbs ++ wbs, b.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases
  sp32 : 32 ≤ (s.gpr .rsp).toNat

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s)
include L

theorem Lay.sub {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) :
    ∃ n, (p.1, n) ∈ rbs ++ wbs ∧ Region.Sub ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ ⟨s.gpr p.1, n⟩ := by
  obtain ⟨n, hm, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec h
  exact ⟨n, hm, sub_offset' hl (by have := L.small _ hm; omega)⟩

theorem Lay.disj {p q : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l k : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.sepB (rbs ++ wbs) p l q k = true) :
    Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ ⟨VG.Proof.MlDsa.X86_64.Verify.pa s q, k⟩ := by
  obtain ⟨hp, hq, hs⟩ := VG.Proof.MlDsa.X86_64.Verify.sepB_spec h
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec hp
  obtain ⟨m, hm, hk⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec hq
  have sn := L.small _ hn
  have sm := L.small _ hm
  rcases hs with ⟨e, hw⟩ | ⟨e, hs⟩
  · exact ((L.dj _ hn _ hm e hw).sub_left (sub_offset' hl (by omega))).sub_right (sub_offset' hk (by omega))
  · show Region.Disjoint ⟨s.gpr p.1 + _, l⟩ ⟨s.gpr q.1 + _, k⟩
    rw [← e]
    rcases hs with h1 | h2
    · exact off_disj h1 (by omega)
    · exact (off_disj h2 (by omega)).symm

theorem Lay.stkD {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) :
    (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.stk _ hn).sub_right hsub

theorem Lay.retD {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) :
    (Region.mk (s.gpr .rsp) 8).Disjoint ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ := by
  obtain ⟨n, hn, hsub⟩ := L.sub h
  exact (L.ret _ hn).sub_right hsub

theorem Lay.nwp {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) : (VG.Proof.MlDsa.X86_64.Verify.pa s p).toNat + l ≤ 2 ^ 64 := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec h
  have h1 := L.nw _ hn
  have h2 := L.small _ hn
  simp only at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p.2) (by omega)]
  have := Nat.mod_le ((s.gpr p.1).toNat + p.2) (2 ^ 64)
  omega

theorem Lay.inR {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) : InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Verify.pa s p) l := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec h
  exact VG.Proof.MlDsa.X86_64.Verify.inRegions_sub (L.rd (p.1, n) hn) hl (by have := L.small _ hn; omega)

theorem Lay.inW {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB wbs p l = true) : InRegions s.wr (VG.Proof.MlDsa.X86_64.Verify.pa s p) l := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec h
  exact VG.Proof.MlDsa.X86_64.Verify.inRegions_sub (L.wr (p.1, n) hn) hl (by have := L.small _ (List.mem_append_right _ hn); omega)

theorem Lay.cR {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) : Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩] (s.rd ++ s.wr) :=
  Covers.one (L.inR h)

theorem Lay.cW {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB wbs p l = true) : Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩] s.wr :=
  Covers.one (L.inW h)

theorem Lay.post {s' : State} {W : List Region} (hP : VG.Proof.MlDsa.X86_64.Verify.PostB s s' W) : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s' := by
  have e : ∀ b ∈ rbs ++ wbs, s'.gpr b.1 = s.gpr b.1 := fun b hb => hP.bs _ (L.bs b hb)
  refine ⟨L.small, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    fun b hb => ?_, L.bs, by rw [hP.rsp]; exact L.sp32⟩
  · rw [e b hb, e b' hb']; exact L.dj b hb b' hb' hne hw
  · rw [e b hb, hP.rsp]; exact L.stk b hb
  · rw [e b hb]; exact L.nw b hb
  · rw [e b hb, hP.rd, hP.wr]; exact L.rd b hb
  · rw [e b (List.mem_append_right _ hb), hP.wr]; exact L.wr b hb
  · rw [e b hb, hP.rsp]; exact L.ret b hb

end

/-! ## What is kept -/

/-- The region of `w.2` bytes at the pointer `w.1`. -/
abbrev toR (s : State) (w : VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat) : Region := ⟨VG.Proof.MlDsa.X86_64.Verify.pa s w.1, w.2⟩

/-- `PostB`, with the regions written given as pointers. -/
abbrev PPostB (s s' : State) (ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)) : Prop := VG.Proof.MlDsa.X86_64.Verify.PostB s s' (ws.map (VG.Proof.MlDsa.X86_64.Verify.toR s))

theorem map_toR_post {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.X86_64.Verify.PostB s s' W) {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)}
    (h : ∀ w ∈ ws, w.1.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) : ws.map (VG.Proof.MlDsa.X86_64.Verify.toR s') = ws.map (VG.Proof.MlDsa.X86_64.Verify.toR s) :=
  List.map_congr_left fun w hw => by simp only [VG.Proof.MlDsa.X86_64.Verify.toR, hP.pa (h w hw)]

theorem PPostB.trans {s s₁ s₂ : State} {ws₁ ws₂ ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (h₁ : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₁ ws₁)
    (h₂ : VG.Proof.MlDsa.X86_64.Verify.PPostB s₁ s₂ ws₂) (hcs : ∀ w ∈ ws₂, w.1.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) (hw₁ : ∀ w ∈ ws₁, w ∈ ws)
    (hw₂ : ∀ w ∈ ws₂, w ∈ ws) : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₂ ws := by
  have h₂' : VG.Proof.MlDsa.X86_64.Verify.PostB s₁ s₂ (ws₂.map (VG.Proof.MlDsa.X86_64.Verify.toR s)) := by rw [← VG.Proof.MlDsa.X86_64.Verify.map_toR_post h₁ hcs]; exact h₂
  refine PostB.trans h₁ h₂' (fun r hr => ?_) fun r hr => ?_
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₁ w hw)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw₂ w hw)

theorem PPostB.mono {s s' : State} {ws ws' : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (h : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hw : ∀ w ∈ ws, w ∈ ws') :
    VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws' :=
  PostB.trans (PostB.refl s []) h (fun _ h => absurd h List.not_mem_nil) fun r hr => by
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hr; exact List.mem_map_of_mem (hw w hw')

/-- The `l` bytes at `p` lie in the layout, apart from the regions `ws`, and
`p`'s register is one of `bases`. -/
def keepB (bs : List (Reg × Nat)) (ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)) (p : VG.Impl.MlDsa.X86_64.Verify.Ptr) (l : Nat) : Bool :=
  decide (p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) && VG.Proof.MlDsa.X86_64.Verify.inB bs p l && ws.all fun w => VG.Proof.MlDsa.X86_64.Verify.sepB bs p l w.1 w.2

theorem keepB_nil {bs : List (Reg × Nat)} {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Verify.keepB bs ws p l = true) : VG.Proof.MlDsa.X86_64.Verify.keepB bs [] p l = true := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.keepB, Bool.and_eq_true, List.all_nil, and_true] at hc ⊢
  exact hc.1

theorem keepB_nil_of {bs : List (Reg × Nat)} {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (hb : p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) (h : VG.Proof.MlDsa.X86_64.Verify.inB bs p l = true) :
    VG.Proof.MlDsa.X86_64.Verify.keepB bs [] p l = true := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.keepB, Bool.and_eq_true, List.all_nil, and_true, decide_eq_true_eq]
  exact ⟨hb, h⟩

theorem keepB_bs {bs : List (Reg × Nat)} {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Verify.keepB bs ws p l = true) : p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.keepB, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

section
variable {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)}
  {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat}
include L

theorem Lay.fdisj (hc : VG.Proof.MlDsa.X86_64.Verify.keepB (rbs ++ wbs) ws p l = true) :
    ∀ r ∈ ws.map (VG.Proof.MlDsa.X86_64.Verify.toR s) ++ [below (s.gpr .rsp) 32], Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ r := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.keepB, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨_, hin⟩, hall⟩ := hc
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    exact L.disj (hall w hw)
  · rw [List.mem_singleton] at hr
    subst hr
    exact (L.stkD hin).symm

theorem Lay.keepBytes (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hc : VG.Proof.MlDsa.X86_64.Verify.keepB (rbs ++ wbs) ws p l = true) :
    bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s' p) l = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) l := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Verify.keepB_bs hc)]
  have hin : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.keepB, Bool.and_eq_true] at hc; exact hc.1.2
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec hin
  exact Proof.MlKem.bytesAt_frame hP.frame (L.fdisj hc) (by have := L.small _ hn; omega)

theorem Lay.keepPoly {f : Spec.MlDsa.Poly} (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hc : VG.Proof.MlDsa.X86_64.Verify.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Spec.MlDsa.PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) f) : Spec.MlDsa.PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s' p) f := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Verify.keepB_bs hc)]
  exact Proof.MlDsa.Verify.polyIs_frame hP.frame (L.fdisj hc) h

theorem Lay.keepPolyAt (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hc : VG.Proof.MlDsa.X86_64.Verify.keepB (rbs ++ wbs) ws p 1024 = true) :
    Spec.MlDsa.polyAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s' p) = Spec.MlDsa.polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Verify.keepB_bs hc)]
  exact Proof.MlDsa.Verify.polyAt_frame hP.frame (L.fdisj hc)

theorem Lay.keepRed (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hc : VG.Proof.MlDsa.X86_64.Verify.keepB (rbs ++ wbs) ws p 1024 = true)
    (h : Spec.MlDsa.Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p)) : Spec.MlDsa.Reduced s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s' p) := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Verify.keepB_bs hc)]
  exact Proof.MlDsa.Verify.reduced_frame hP.frame (L.fdisj hc) h

theorem Lay.keepHint {k : Nat} {h : List (Vector Bool Spec.MlDsa.n)} (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws)
    (hc : VG.Proof.MlDsa.X86_64.Verify.keepB (rbs ++ wbs) ws p (1024 * k) = true)
    (hh : Spec.MlDsa.HintIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) k h) : Spec.MlDsa.HintIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s' p) k h := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Verify.keepB_bs hc)]
  have hin : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p (1024 * k) = true := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.keepB, Bool.and_eq_true] at hc; exact hc.1.2
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec hin
  exact Proof.MlDsa.Verify.hintIs_frame hP.frame (by have := L.small _ hn; omega) (L.fdisj hc) hh

theorem Lay.keepW (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hc : VG.Proof.MlDsa.X86_64.Verify.keepB (rbs ++ wbs) ws p 8 = true) :
    s'.mem.readW (VG.Proof.MlDsa.X86_64.Verify.pa s' p) 64 = s.mem.readW (VG.Proof.MlDsa.X86_64.Verify.pa s p) 64 := by
  rw [hP.pa (VG.Proof.MlDsa.X86_64.Verify.keepB_bs hc)]
  exact hP.frame.readW (Region.contains_self _ _) (L.fdisj hc) (by decide)

end

/-- The return address is kept by code that writes within the layout and the stack. -/
theorem Lay.keepRet {rbs wbs : List (Reg × Nat)} {s s' : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)}
    (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hin : ∀ w ∈ ws, VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) w.1 w.2 = true) :
    s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  refine hP.frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    obtain ⟨n, hn, hsub⟩ := L.sub (hin w hw)
    exact (L.ret _ hn).sub_right hsub
  · rw [List.mem_singleton] at hr; subst hr
    intro x h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    bv_omega

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Call`. -/
section

/-!
# ML-DSA verification on x86-64: calls

A call of verified code, with the moves of its arguments before it
(`callAt_ok`), leaves the permissions and the callee-saved registers as they
were, and changes memory only within the buffers it writes and the 32 bytes of
stack below `rsp` (`Post`); two runs whose arguments agree and whose callee's
public data agree leak the same (`callAt_tr`). A callee may be verified
against its contract with any stack up to 16 bytes: its precondition follows
from the one with 16 (`pre_stack`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64

/-! ## Blocks that access no memory -/

theorem execBlock_nomem {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) :
    ∀ {s s' : State} {t : List Leak}, execBlock isa is s = some (s', t) → t = [] := by
  induction is with
  | nil => intro s s' t e; simp [execBlock] at e; exact e.2
  | cons i is ih =>
    intro s s' t e
    simp only [execBlock] at e
    split at e
    · cases e
    · obtain ⟨⟨s₂, t₂⟩, e₂, he⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at he
      rw [← he.2, show addrs i s = [] from h i (List.mem_cons_self ..) s,
        ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) e₂]
      rfl

/-- A block that accesses no memory leaks nothing. -/
theorem block_nomem_tr {is : List Instr} (h : ∀ i ∈ is, ∀ s, isa.addrs i s = []) {P : State → State → Prop} :
    RelCT isa P (.block is) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' _ e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  exact ⟨(VG.Proof.MlDsa.X86_64.Verify.execBlock_nomem h e₁).trans (VG.Proof.MlDsa.X86_64.Verify.execBlock_nomem h e₂).symm, trivial⟩

theorem glue_nomem : ∀ (as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)), ∀ i ∈ glue as, ∀ s, isa.addrs i s = []
  | [], _, h, _ => absurd h List.not_mem_nil
  | (d, a) :: as, i, h, s => by
    simp only [glue] at h
    rcases List.mem_append.mp h with h | h
    · cases a <;> simp only [Arg.instrs, List.mem_cons, List.not_mem_nil, or_false] at h <;>
        rcases h with rfl | rfl <;> rfl
    · exact VG.Proof.MlDsa.X86_64.Verify.glue_nomem as i h s

/-! ## Calls -/

/-- The arguments of a call, in their registers. -/
abbrev Args (as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)) (s s1 : State) : Prop :=
  ((∀ a ∈ as, s1.gpr a.1 = a.2.val s) ∧ s1.mem = s.mem) ∧ Keep VG.Proof.MlDsa.X86_64.Verify.argRegs s s1

theorem callAt_ok {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hd : c.depth ≤ 3) {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs)
    (hnd : (as.map (·.1)).Nodup) {s : State} {rd wr : List Region}
    (hpre : ∀ s1, VG.Proof.MlDsa.X86_64.Verify.Args as s s1 → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt n c as) s fun s' => VG.Proof.MlDsa.X86_64.Verify.Post s s' wr ∧
      ∃ s1, VG.Proof.MlDsa.X86_64.Verify.Args as s s1 ∧ ∃ s₂ : State, s₂.mem = s'.mem ∧
        (∀ r, r ≠ .rsp → s₂.gpr r = s'.gpr r) ∧ k.post (s1.callEntry.withRegions rd wr) s₂ := by
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok hnd s) fun s1 h1 => ?_)
  have hm := h1.1.2
  have k1 := h1.2
  refine WP.call hv hsp (by omega) (hpre s1 h1) (by rw [k1.2.1, k1.2.2]; exact hc)
    (by rw [k1.2.2]; exact hw) fun s' hrd hwr hcs hf _ hpost => ⟨⟨hrd.trans k1.2.1, hwr.trans k1.2.2,
      fun r hr => by rw [hcs r hr, k1.gpr (VG.Proof.MlDsa.X86_64.Verify.argRegs_cs r hr)], ?_⟩, s1, h1, hpost⟩
  have hsp1 : s1.gpr .rsp = s.gpr .rsp := k1.gpr (by decide)
  rw [hm, hsp1] at hf
  exact Frame.below_mono hf (by omega) (by omega)

/-- The trace of the moves then a call, from two runs where the moves are
the same and the callee's public data agree. -/
theorem callAt_tr {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs)
    (hnd : (as.map (·.1)).Nodup) {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → VG.Proof.MlDsa.X86_64.Verify.Args as x x1 → VG.Proof.MlDsa.X86_64.Verify.Args as y y1 → ∃ rd₁ wr₁ rd₂ wr₂ : List Region,
      k.pre (x1.callEntry.withRegions rd₁ wr₁) ∧ k.pre (y1.callEntry.withRegions rd₂ wr₂) ∧
      k.pub (x1.callEntry.withRegions rd₁ wr₁) (y1.callEntry.withRegions rd₂ wr₂) ∧
      Covers (rd₁ ++ wr₁) (x.rd ++ x.wr) ∧ Covers wr₁ x.wr ∧
      Covers (rd₂ ++ wr₂) (y.rd ++ y.wr) ∧ Covers wr₂ y.wr ∧ x.gpr .rsp = y.gpr .rsp) :
    RelCT isa P (callAt n c as) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ VG.Proof.MlDsa.X86_64.Verify.Args as x x1 ∧ VG.Proof.MlDsa.X86_64.Verify.Args as y y1)
      (VG.Proof.MlDsa.X86_64.Verify.block_nomem_tr (VG.Proof.MlDsa.X86_64.Verify.glue_nomem as)) (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok hnd x, VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩)
    (RelCT.callEx hv hct fun x1 y1 ⟨x, y, hp, h1, h2⟩ => by
      obtain ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, pub, c₁, w₁, c₂, w₂, e⟩ := hP x y x1 y1 hp h1 h2
      exact ⟨rd₁, wr₁, rd₂, wr₂, p₁, p₂, pub, by rw [h1.2.2.1, h1.2.2.2]; exact c₁, by rw [h1.2.2.2]; exact w₁,
        by rw [h2.2.2.1, h2.2.2.2]; exact c₂, by rw [h2.2.2.2]; exact w₂,
        by rw [h1.2.gpr (by decide), h2.2.gpr (by decide), e]⟩)

/-! ## The callee's stack -/

theorem stackBelow_sub (sp : Addr) {n : Nat} (hn : n ≤ 16) :
    ∀ r ∈ stackBelow sp n, Region.Sub r (below sp 16) := by
  intro r hr
  match n, hr with
  | m + 1, hr =>
    simp only [stackBelow, List.mem_singleton] at hr
    subst hr
    exact below_sub (by omega) (by omega)

/-- A contract with a stack of at most 16 bytes asks no more than with 16. -/
theorem pre_stack {sig : Sig} {pre : Curry (sig.words X86_64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post X86_64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words X86_64.abi.ptrBits) (Mem → List Nat))} {n : Nat} (hn : n ≤ 16) {s : State}
    (h : (sig.contract X86_64.abi pre post wa 16 leak).pre s) : (sig.contract X86_64.abi pre post wa n leak).pre s := by
  unfold Sig.contract at h ⊢
  dsimp only at h ⊢
  generalize X86_64.abi.args ((sig.words X86_64.abi.ptrBits).map (·.bits X86_64.abi.ptrBits)) = o at h ⊢
  cases o with
  | none => exact h
  | some vals =>
    obtain ⟨hwf, hrd, hwr, hpw, hres, hnw, hpre⟩ := h
    refine ⟨?_, hrd, hwr, hpw, fun r hr a ha => ?_, hnw, hpre⟩
    · simp only [X86_64.abi] at hwf ⊢
      split at hwf
      · rw [VG.Proof.MlKem.X86_64.ifp ‹_›]
        rcases n with _ | n
        · trivial
        · exact Nat.le_trans hn hwf
      · rw [VG.Proof.MlKem.X86_64.ifn ‹_›]
        refine ⟨?_, hwf.2⟩
        rcases n with _ | n
        · trivial
        · exact Nat.le_trans hn hwf.1
    · simp only [X86_64.abi, List.mem_cons] at hr hres
      rcases hr with rfl | hr
      · exact hres _ (.inl rfl) a ha
      · exact (hres _ (.inr (List.mem_singleton_self _)) a ha).sub_left (VG.Proof.MlDsa.X86_64.Verify.stackBelow_sub _ hn r hr)

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Entry`. -/
section

/-!
# ML-DSA verification on x86-64: entry to a callee

What a callee's contract needs on its entry, from the layout of the caller:
that its buffers are apart from its return address and the 16 bytes of stack
below it, and from each other, and that they read on entry as they did before
the call (`Ent`). And what the callees must be (`CalleeOk`): correct and
constant time under their contracts with 16 bytes of stack (24 for
`vg_mldsa_rej_ntt_poly4`), not writing the stack pointer, calling at most
three deep, and never loading MXCSR.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## Callees -/

/-- A callee: correct and constant time under the contract `k` (a shared
contract), not writing `rsp`, calling at most three deep, loading MXCSR only
to restore it (`ctlOk`), and never writing the stack pointer (which its
callers' artifacts check). -/
structure CalleeOk (c : Prog isa) (k : Contract isa) : Prop where
  correct : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s'
  ct : ConstantTime isa k.pre k.pub c
  nosp : NoSp c
  depth : c.depth ≤ 3
  ctl : ctlOk c = true
  spSafe : c.all (fun i => !isa.writesSp i) = true

/-- A callee verified against its shared contract with at most 16 bytes of stack. -/
theorem CalleeOk.of_verified {c : Prog isa} {sig : Sig} {pre : Curry (sig.words X86_64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post X86_64.abi.ptrBits} {wa : Bool}
    {leak : Option (Curry (sig.words X86_64.abi.ptrBits) (Mem → List Nat))} {n : Nat}
    (h : Verified X86_64.target c (sig.contract X86_64.abi pre post wa n leak)) (hn : n ≤ 16)
    (hsp : NoSp c) (hd : c.depth ≤ 3) (hmx : ctlOk c = true)
    (hss : c.all (fun i => !isa.writesSp i) = true) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk c (sig.contract X86_64.abi pre post wa 16 leak) :=
  ⟨fun s hs => h.1 s (VG.Proof.MlDsa.X86_64.Verify.pre_stack hn hs),
    fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => h.2.1 s₁ s₂ t₁ t₂ s₁' s₂' (VG.Proof.MlDsa.X86_64.Verify.pre_stack hn h₁) (VG.Proof.MlDsa.X86_64.Verify.pre_stack hn h₂) hp e₁ e₂,
    hsp, hd, hmx, hss⟩

/-! ## Entry

A callee's precondition, evaluated, is stated on the state of the call
instruction: its stack pointer is 8 below the caller's, and its memory the
caller's with the return address written below it. -/

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s)
include L

theorem Lay.sp16 : 16 ≤ (s.gpr .rsp - 8).toNat := by
  have := L.sp32
  rw [BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]
  omega

theorem Lay.ret8 {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) :
    Region.Disjoint ⟨s.gpr .rsp - 8, 8⟩ ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ := by
  refine (L.stkD h).sub_left ?_
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = (x - (s.gpr .rsp - 8)) + 24 by bv_omega, BitVec.toNat_add]
  have : (24 : BitVec 64).toNat = 24 := rfl
  omega

theorem Lay.stk16 {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) :
    Region.Disjoint ⟨s.gpr .rsp - 8 - 16, 16⟩ ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ := by
  refine (L.stkD h).sub_left ?_
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = (x - (s.gpr .rsp - 8 - 16)) + 8 by bv_omega, BitVec.toNat_add]
  have : (8 : BitVec 64).toNat = 8 := rfl
  omega

theorem Lay.sp24 : 24 ≤ (s.gpr .rsp - 8).toNat := by
  have := L.sp32
  rw [BitVec.toNat_sub, show (8 : BitVec 64).toNat = 8 from rfl]
  omega

theorem Lay.stk24 {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) :
    Region.Disjoint ⟨s.gpr .rsp - 8 - 24, 24⟩ ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩ := by
  refine (L.stkD h).sub_left ?_
  intro x hx
  simp only [Region.Contains] at hx ⊢
  rw [show x - (s.gpr .rsp - BitVec.ofNat 64 32) = x - (s.gpr .rsp - 8 - 24) by bv_omega]
  omega

theorem Lay.wbytes {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) (v : BitVec 64) :
    ∀ i < l, (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s p + BitVec.ofNat 64 i) = s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p + BitVec.ofNat 64 i) :=
  fun i hi => Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (R := ⟨VG.Proof.MlDsa.X86_64.Verify.pa s p, l⟩) (by
      simp only [List.mem_singleton, forall_eq]
      exact ((L.stkD h).sub_left (below_sub (by omega) (by omega))).symm)
    (by have := L.nwp h; simp; omega) hi

theorem Lay.wbytesAt {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) (v : BitVec 64) :
    bytesAt (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s p) l = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) l :=
  Proof.MlKem.bytesAt_congr (L.wbytes h v)

theorem Lay.wpolyAt {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) :
    polyAt (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s p) = polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) :=
  Proof.MlDsa.Verify.polyAt_congr (L.wbytes h v)

theorem Lay.wnatPolyAt {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) :
    natPolyAt (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s p) = natPolyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) :=
  Proof.MlDsa.Verify.natPolyAt_congr (L.wbytes h v)

theorem Lay.wcoeffAt {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) {i : Nat} (hi : i < n) :
    coeffAt (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s p) i = coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) i :=
  Proof.MlDsa.Verify.coeffAt_congr (L.wbytes h v) hi

theorem Lay.whintAt {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) :
    hintAt (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s p) 1 = hintAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p) 1 := by
  unfold hintAt
  refine List.map_congr_left fun i hi => ?_
  have : i = 0 := by rw [List.mem_range] at hi; omega
  subst this
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, Nat.mul_zero, Nat.zero_add]
  rw [L.wcoeffAt h v hj]

theorem Lay.wreduced {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p 1024 = true) (v : BitVec 64) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s p)) :
    Reduced (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s p) :=
  Proof.MlDsa.Verify.reduced_congr (L.wbytes h v) hr

end

/-- The values of the arguments after their moves. -/
theorem Args.reg {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Verify.Args as s s1) {r : Reg} {a : VG.Impl.MlDsa.X86_64.Verify.Arg} (ha : (r, a) ∈ as) :
    s1.gpr r = a.val s := h.1.1 _ ha

theorem Args.r0 {r : Reg} {a : VG.Impl.MlDsa.X86_64.Verify.Arg} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Verify.Args ((r, a) :: as) s s1) :
    s1.gpr r = a.val s := h.1.1 _ (List.mem_cons_self ..)

theorem Args.r1 {r r1 : Reg} {a a1 : VG.Impl.MlDsa.X86_64.Verify.Arg} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.X86_64.Verify.Args ((r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem Args.r2 {r r1 r2 : Reg} {a a1 a2 : VG.Impl.MlDsa.X86_64.Verify.Arg} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.X86_64.Verify.Args ((r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem Args.r3 {r r1 r2 r3 : Reg} {a a1 a2 a3 : VG.Impl.MlDsa.X86_64.Verify.Arg} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.X86_64.Verify.Args ((r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))

theorem Args.r4 {r r1 r2 r3 r4 : Reg} {a a1 a2 a3 a4 : VG.Impl.MlDsa.X86_64.Verify.Arg} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.X86_64.Verify.Args ((r4, a4) :: (r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_self ..)))))

theorem Args.r5 {r r1 r2 r3 r4 r5 : Reg} {a a1 a2 a3 a4 a5 : VG.Impl.MlDsa.X86_64.Verify.Arg} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State}
    (h : VG.Proof.MlDsa.X86_64.Verify.Args ((r5, a5) :: (r4, a4) :: (r3, a3) :: (r2, a2) :: (r1, a1) :: (r, a) :: as) s s1) : s1.gpr r = a.val s :=
  h.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))))))

theorem Args.rsp {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} {s s1 : State} (h : VG.Proof.MlDsa.X86_64.Verify.Args as s s1) : s1.gpr .rsp = s.gpr .rsp :=
  h.2.gpr (by decide)

theorem imm32 {v : Nat} (h : v < 2 ^ 32) : (BitVec.setWidth 32 (BitVec.ofNat 64 v)).toNat = v := by
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem imm64 {v : Nat} (h : v < 2 ^ 64) : (BitVec.ofNat 64 v).toNat = v := by
  simp only [BitVec.toNat_ofNat]; omega

/-- Two states whose layout registers and stack pointer agree. -/
def SameB (x y : State) : Prop := (∀ r ∈ VG.Proof.MlDsa.X86_64.Verify.bases, x.gpr r = y.gpr r) ∧ x.gpr .rsp = y.gpr .rsp

theorem SameB.pa {x y : State} (h : VG.Proof.MlDsa.X86_64.Verify.SameB x y) {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hp : p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) : VG.Proof.MlDsa.X86_64.Verify.pa x p = VG.Proof.MlDsa.X86_64.Verify.pa y p := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.pa, h.1 _ hp]

/-- The buffers of a layout: small, in the registers `bases`. -/
def LayOk (bs : List (Reg × Nat)) : Prop := ∀ b ∈ bs, b.2 < 2 ^ 31 ∧ b.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases

theorem Lay.ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs) :=
  fun b hb => ⟨L.small b hb, L.bs b hb⟩

theorem ptr_ok {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat}
    (h : VG.Proof.MlDsa.X86_64.Verify.inB bs p l = true) : (Arg.ptr p).Ok := by
  obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec h
  refine ⟨by have := (L _ hn).1; simp only at this; omega, fun h' => ?_⟩
  have := (L _ hn).2
  simp only at this
  revert h' this
  generalize p.1 = r
  cases r <;> decide

theorem ptr_bs {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat}
    (h : VG.Proof.MlDsa.X86_64.Verify.inB bs p l = true) : p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases := by
  obtain ⟨n, hn, _⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec h
  exact (L _ hn).2

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Hash`. -/
section

/-!
# ML-DSA verification on x86-64: `H(a ‖ b)` through the sponge

`hash2 a la b lb out len` zeroes the Keccak state at `scratch`, absorbs the
`la` bytes at `a` and the `lb` bytes at `b`, pads with SHAKE's suffix and
squeezes `len` bytes to `out`: `H(a ‖ b, len)` (`hash2_ok`), leaking only the
addresses (`hash2_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates Repr squeezeFrom)

/-! ## The checks -/

/-- The state and the working space of the sponge, apart, writable. -/
def kChk (bs wbs : List (Reg × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 && VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 && VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 && VG.Proof.MlDsa.X86_64.Verify.inB wbs (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 &&
    VG.Proof.MlDsa.X86_64.Verify.inB wbs (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640

/-- A piece to absorb, apart from the sponge. -/
def pieceChk (bs : List (Reg × Nat)) (p : VG.Impl.MlDsa.X86_64.Verify.Ptr) (l : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs p l (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 && VG.Proof.MlDsa.X86_64.Verify.sepB bs p l (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 && VG.Proof.MlDsa.X86_64.Verify.inB bs p l

/-- The output, apart from the sponge, writable. -/
def outChk (bs wbs : List (Reg × Nat)) (p : VG.Impl.MlDsa.X86_64.Verify.Ptr) (l : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs p l (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 && VG.Proof.MlDsa.X86_64.Verify.sepB bs p l (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 && VG.Proof.MlDsa.X86_64.Verify.inB bs p l && VG.Proof.MlDsa.X86_64.Verify.inB wbs p l

/-- The checks of `hash2`. -/
def hashChk (bs wbs : List (Reg × Nat)) (a : VG.Impl.MlDsa.X86_64.Verify.Ptr) (la : Nat) (b : VG.Impl.MlDsa.X86_64.Verify.Ptr) (lb : Nat) (out : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.kChk bs wbs && VG.Proof.MlDsa.X86_64.Verify.pieceChk bs a la && VG.Proof.MlDsa.X86_64.Verify.pieceChk bs b lb && VG.Proof.MlDsa.X86_64.Verify.outChk bs wbs out len &&
    VG.Proof.MlDsa.X86_64.Verify.keepB bs [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200)] a la && VG.Proof.MlDsa.X86_64.Verify.keepB bs [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200)] b lb && VG.Proof.MlDsa.X86_64.Verify.keepB bs [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200), (VG.Impl.MlDsa.X86_64.Verify.sc 200, 640)] b lb &&
    decide (la < 136) && decide (0 < la)

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s)
include L

theorem kChk_spec (h : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true) :
    Region.Disjoint ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0), 200⟩ ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 200), 640⟩ ∧ (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0), 200⟩ ∧
      (below (s.gpr .rsp) 32).Disjoint ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 200), 640⟩ ∧ Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0), 200⟩] s.wr ∧
      Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 200), 640⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := h
  exact ⟨L.disj c1, L.stkD c2, L.stkD c3, L.cW c4, L.cW c5⟩

end

/-! ## Zeroing the state -/

theorem kzero_ok (s : State) (hw : Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0), 200⟩] s.wr) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Verify.kzero) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200)] ∧ s'.gpr .r15 = s.gpr .r15 ∧ stateAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) = Spec.Sha3.zero := by
  rw [VG.Impl.MlDsa.X86_64.Verify.kzero, ← List.singleton_append, WP.block_append_iff]
  refine WP.mono (WP.keep [.rax] (Q := fun s1 => s1.mem = s.mem ∧ s1.gpr .rax = 0) (by xrun) (by decide))
    fun s1 ⟨⟨hm, hax⟩, k1⟩ => ?_
  have hbx : s1.gpr .rbx = s.gpr .rbx := k1.gpr (by decide)
  refine WP.mono (zeroSt_ok .rbx 0 s1 hax fun i hi => ?_) fun s2 ⟨hz, hf, k2⟩ => ?_
  · rw [k1.2.2, hbx]
    exact hw _ _ ⟨_, List.mem_singleton_self _, contains_offset' (by omega) (by omega)⟩
  · rw [hbx] at hz hf
    exact ⟨VG.Proof.MlDsa.X86_64.Verify.postB_of_keep (k1.trans k2) (by decide) (by rw [← hm]; exact hf), (k1.trans k2).gpr (by decide), hz⟩

/-! ## The calls -/

theorem r15_call {s s1 s' : State} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args as s s1)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s1.gpr r) : s'.gpr .r15 = s.gpr .r15 :=
  (hcs _ (by decide)).trans (h1.2.gpr (by decide))

abbrev kabsArgs (src : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len rate pos : Nat) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc 0)), (.rsi, .imm rate), (.rdx, .imm pos), (.rcx, .ptr src), (.r8, .imm len), (.r9, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc 200))]

theorem kabs_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true)
    {src : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len pos : Nat} (hp : VG.Proof.MlDsa.X86_64.Verify.pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.kabs src len 136 pos) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200), (VG.Impl.MlDsa.X86_64.Verify.sc 200, 640)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ msg, Repr s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) 136 msg → pos = msg.length % 136 →
        Repr s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) 136 (msg ++ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s src) len) := by
  obtain ⟨d1, k1, k2, w1, w2⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec L hk
  simp only [VG.Proof.MlDsa.X86_64.Verify.pieceChk, Bool.and_eq_true] at hp
  obtain ⟨⟨p1, p2⟩, p3⟩ := hp
  have hS := L.ok
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec p3; have := (hS _ hn).1; omega
  have ha : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.kabsArgs src len 136 pos, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    have c0 : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 = true := by
      simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at hk; exact hk.1.1.1.2
    have c1 : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 = true := by
      simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at hk; exact hk.1.1.2
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c0, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩, ⟨show pos < 2 ^ 31 by omega, by decide⟩,
      ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS p3, by decide⟩, ⟨hlen, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c1, by decide⟩⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok' ha (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.kabsArgs src len 136 pos) s s1) => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  have kk : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 16).Disjoint R :=
    fun h => by rw [hsp]; exact h.sub_left (below_sub (by omega) (by omega))
  refine absorb_call ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, hpos, by omega, d1, (L.disj p1),
    (L.disj p2), kk k1, kk (L.stkD p3), kk k2⟩
    (by rw [h1.2.2.1, h1.2.2.2]; exact Covers.append_left (L.cR p3) (Covers.right (Covers.cons w1 w2)))
    (by rw [h1.2.2.2]; exact Covers.cons w1 w2) (fun s' hrd hwr hcs hf hR _ => ?_)
  have hb : ∀ r ∈ VG.Proof.MlDsa.X86_64.Verify.bases, s'.gpr r = s.gpr r := by
    intro r hr
    simp only [VG.Proof.MlDsa.X86_64.Verify.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hcs r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
      h1.2.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
  refine ⟨⟨hrd.trans h1.2.2.1, hwr.trans h1.2.2.2, hb, by rw [hcs _ (by decide), hsp], ?_⟩, VG.Proof.MlDsa.X86_64.Verify.r15_call h1 hcs,
    fun msg hm hpo => ?_⟩
  · have f1 : Frame ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0), 200⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 200), 640⟩] ++ [below (s.gpr .rsp) 16]) s.mem s'.mem := by
      rw [← h1.1.2, ← hsp]; exact hf
    exact Frame.below_mono (a := 16) (b := 32) f1 (by omega) (by omega)
  · rw [← h1.1.2] at hm ⊢
    exact hR msg hm hpo

abbrev kpadArgs (rate pos suffix : Nat) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc 0)), (.rsi, .imm rate), (.rdx, .imm pos), (.rcx, .imm suffix), (.r8, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc 200))]

theorem postB_call {s s1 s' : State} {as : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args as s s1) {W : List Region}
    (hrd : s'.rd = s1.rd) (hwr : s'.wr = s1.wr) (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s1.gpr r)
    (hf : Frame (W ++ [below (s.gpr .rsp) 16]) s.mem s'.mem) : VG.Proof.MlDsa.X86_64.Verify.PostB s s' W := by
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  refine ⟨hrd.trans h1.2.2.1, hwr.trans h1.2.2.2, fun r hr => ?_, by rw [hcs _ (by decide), hsp],
    Frame.below_mono (a := 16) (b := 32) hf (by omega) (by omega)⟩
  simp only [VG.Proof.MlDsa.X86_64.Verify.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [hcs r (by rcases hr with rfl | rfl | rfl | rfl <;> decide),
    h1.2.gpr (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]

theorem kpad_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true)
    {pos : Nat} (hpos : pos < 136) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.kpad 136 pos 0x1f) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200), (VG.Impl.MlDsa.X86_64.Verify.sc 200, 640)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ msg, Repr s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) 136 msg → pos = msg.length % 136 →
        stateAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) = Spec.Sha3.absorb 136 (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix msg) := by
  obtain ⟨d1, k1, k2, w1, w2⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec L hk
  have hS := L.ok
  have c0 : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at hk; exact hk.1.1.1.2
  have c1 : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at hk; exact hk.1.1.2
  have ha : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.kpadArgs 136 pos 0x1f, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c0, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩, ⟨show pos < 2 ^ 31 by omega, by decide⟩,
      ⟨show 0x1f < 2 ^ 31 by decide, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c1, by decide⟩⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok' ha (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.kpadArgs 136 pos 0x1f) s s1) => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  have kk : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 16).Disjoint R :=
    fun h => by rw [hsp]; exact h.sub_left (below_sub (by omega) (by omega))
  refine pad_call ⟨h1.r0, h1.r1, h1.r2, h1.r4, by decide, hpos, d1, kk k1, kk k2⟩
    (by rw [h1.2.2.1, h1.2.2.2]; exact Covers.append_left Covers.nil (Covers.right (Covers.cons w1 w2)))
    (by rw [h1.2.2.2]; exact Covers.cons w1 w2) (fun s' hrd hwr hcs hf hR => ⟨VG.Proof.MlDsa.X86_64.Verify.postB_call h1 hrd hwr hcs ?_, VG.Proof.MlDsa.X86_64.Verify.r15_call h1 hcs, ?_⟩)
  · rw [← h1.1.2, ← hsp]; exact hf
  · intro msg hm hpo
    rw [← h1.1.2] at hm
    have := hR msg hm hpo
    simp only [Arg.val] at this
    rw [this, h1.r3]
    rfl

abbrev ksqzArgs (rate : Nat) (dst : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc 0)), (.rsi, .imm rate), (.rdx, .imm 0), (.rcx, .ptr dst), (.r8, .imm len), (.r9, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc 200))]

theorem ksqz_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true)
    {out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len : Nat} (ho : VG.Proof.MlDsa.X86_64.Verify.outChk (rbs ++ wbs) wbs out len = true) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.ksqz 136 out len) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200), (out, len), (VG.Impl.MlDsa.X86_64.Verify.sc 200, 640)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s out) len = squeezeFrom 136 (stateAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0))) 0 len := by
  obtain ⟨d1, k1, k2, w1, w2⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec L hk
  simp only [VG.Proof.MlDsa.X86_64.Verify.outChk, Bool.and_eq_true] at ho
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, o4⟩ := ho
  have hS := L.ok
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec o3; have := (hS _ hn).1; omega
  have c0 : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at hk; exact hk.1.1.1.2
  have c1 : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at hk; exact hk.1.1.2
  have ha : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.ksqzArgs 136 out len, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c0, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩, ⟨show 0 < 2 ^ 31 by decide, by decide⟩,
      ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS o3, by decide⟩, ⟨hlen, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c1, by decide⟩⟩
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok' ha (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.ksqzArgs 136 out len) s s1) => ?_)
  have hsp : s1.gpr .rsp = s.gpr .rsp := h1.rsp
  have kk : ∀ {R : Region}, (below (s.gpr .rsp) 32).Disjoint R → (below (s1.gpr .rsp) 16).Disjoint R :=
    fun h => by rw [hsp]; exact h.sub_left (below_sub (by omega) (by omega))
  refine squeeze_call ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, by decide, by omega, (L.disj o1).symm, d1,
    L.disj o2, kk k1, kk (L.stkD o3), kk k2⟩
    (by rw [h1.2.2.1, h1.2.2.2]; exact Covers.append_left Covers.nil (Covers.right (Covers.cons w1 (Covers.cons (L.cW o4) w2))))
    (by rw [h1.2.2.2]; exact Covers.cons w1 (Covers.cons (L.cW o4) w2)) (fun s' hrd hwr hcs hf hR => ⟨VG.Proof.MlDsa.X86_64.Verify.postB_call h1 hrd hwr hcs ?_, VG.Proof.MlDsa.X86_64.Verify.r15_call h1 hcs, ?_⟩)
  · rw [← h1.1.2, ← hsp]; exact hf
  · simp only [Arg.val] at hR
    rw [hR, h1.1.2]

/-! ## The hash -/

theorem squeezeFrom_zero (rate : Nat) (S : Spec.Sha3.State) (d : Nat) :
    squeezeFrom rate S 0 d = Spec.Sha3.squeeze rate S d := by
  simp only [squeezeFrom, Spec.Sha3.squeeze, Nat.zero_add, List.drop_zero]

theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) : Repr mem p rate [] := by
  show stateAt mem p = Proof.Sha3.Rep rate []
  rw [Proof.Sha3.rep_nil, h]

theorem hash2_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a b out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {la lb len : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Verify.hashChk (rbs ++ wbs) wbs a la b lb out len = true) :
    WP isa (hash2 a la b lb out len) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200), (VG.Impl.MlDsa.X86_64.Verify.sc 200, 640), (out, len)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s out) len = H (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) la ++ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s b) lb) len := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.hashChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, pa'⟩, pb⟩, ho⟩, ka⟩, kb⟩, kb'⟩, hla⟩, hla0⟩ := hc
  obtain ⟨_, _, _, w0, _⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec L hk
  unfold hash2
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.kzero_ok s w0) fun s₁ ⟨hP₁, f₁, hz⟩ => ?_)
  have L₁ := L.post hP₁
  have e1 : VG.Proof.MlDsa.X86_64.Verify.pa s₁ (VG.Impl.MlDsa.X86_64.Verify.sc 0) = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0) := hP₁.pa (by decide)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.kabs_ok L₁ hk pa' (pos := 0) (by decide)) fun s₂ ⟨hP₂, f₂, hR₂⟩ => ?_)
  have L₂ := L₁.post hP₂
  have e2 : VG.Proof.MlDsa.X86_64.Verify.pa s₂ (VG.Impl.MlDsa.X86_64.Verify.sc 0) = VG.Proof.MlDsa.X86_64.Verify.pa s₁ (VG.Impl.MlDsa.X86_64.Verify.sc 0) := hP₂.pa (by decide)
  have hR₂' := hR₂ [] (by rw [e1]; exact VG.Proof.MlDsa.X86_64.Verify.repr_nil hz) rfl
  rw [List.nil_append, L.keepBytes hP₁ ka] at hR₂'
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.kabs_ok L₂ hk pb (pos := la % 136) (Nat.mod_lt _ (by decide))) fun s₃ ⟨hP₃, f₃, hR₃⟩ => ?_)
  have L₃ := L₂.post hP₃
  have e3 : VG.Proof.MlDsa.X86_64.Verify.pa s₃ (VG.Impl.MlDsa.X86_64.Verify.sc 0) = VG.Proof.MlDsa.X86_64.Verify.pa s₂ (VG.Impl.MlDsa.X86_64.Verify.sc 0) := hP₃.pa (by decide)
  have hR₃' := hR₃ _ (by rw [e2]; exact hR₂') (by rw [Proof.MlKem.bytesAt_length])
  rw [L₁.keepBytes hP₂ kb', L.keepBytes hP₁ kb] at hR₃'
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.kpad_ok L₃ hk (pos := (la + lb) % 136) (Nat.mod_lt _ (by decide))) fun s₄ ⟨hP₄, f₄, hS₄⟩ => ?_)
  have L₄ := L₃.post hP₄
  have e4 : VG.Proof.MlDsa.X86_64.Verify.pa s₄ (VG.Impl.MlDsa.X86_64.Verify.sc 0) = VG.Proof.MlDsa.X86_64.Verify.pa s₃ (VG.Impl.MlDsa.X86_64.Verify.sc 0) := hP₄.pa (by decide)
  have hS := hS₄ _ (by rw [e3]; exact hR₃') (by rw [List.length_append, Proof.MlKem.bytesAt_length,
    Proof.MlKem.bytesAt_length])
  have hob : out.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.outChk, Bool.and_eq_true] at ho; exact VG.Proof.MlDsa.X86_64.Verify.ptr_bs L.ok ho.1.2
  have eo : VG.Proof.MlDsa.X86_64.Verify.pa s₄ out = VG.Proof.MlDsa.X86_64.Verify.pa s out := by rw [hP₄.pa hob, hP₃.pa hob, hP₂.pa hob, hP₁.pa hob]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.ksqz_ok L₄ hk ho) fun s₅ ⟨hP₅, f₅, h₅⟩ => ⟨?_, by rw [f₅, f₄, f₃, f₂, f₁], ?_⟩
  · refine PPostB.trans (PPostB.trans (PPostB.trans (PPostB.trans hP₁ hP₂ (ws := [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200), (VG.Impl.MlDsa.X86_64.Verify.sc 200, 640)])
      (by decide) (by simp) (by simp)) hP₃ (by decide) (fun w hw => hw) (fun w hw => hw)) hP₄ (by decide)
      (fun w hw => hw) (fun w hw => hw)) hP₅ ?_ (by simp) (by simp)
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨by decide, hob, by decide⟩
  · rw [← eo, h₅, e4, hS, VG.Proof.MlDsa.X86_64.Verify.squeezeFrom_zero]
    rfl

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.HashCT`. -/
section

/-!
# ML-DSA verification on x86-64: the sponge leaks only addresses

Two runs in the same layout (`LRel`: layouts whose registers and stack pointer
agree) stay in it across code that keeps the layout (`LRel.step`), and `hash2`
leaks the same in both (`hash2_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt stateAt rates Repr squeezeFrom)

/-- Two runs in the layout, with the same layout registers and stack pointer. -/
def LRel (rbs wbs : List (Reg × Nat)) (x y : State) : Prop := VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y

theorem SameB.post {x y x' y' : State} {W₁ W₂ : List Region} (h : VG.Proof.MlDsa.X86_64.Verify.SameB x y) (hx : VG.Proof.MlDsa.X86_64.Verify.PostB x x' W₁)
    (hy : VG.Proof.MlDsa.X86_64.Verify.PostB y y' W₂) : VG.Proof.MlDsa.X86_64.Verify.SameB x' y' :=
  ⟨fun r hr => by rw [hx.bs r hr, hy.bs r hr, h.1 r hr], by rw [hx.rsp, hy.rsp, h.2]⟩

theorem LRel.post {rbs wbs : List (Reg × Nat)} {x y x' y' : State} {W₁ W₂ : List Region} (h : VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs x y)
    (hx : VG.Proof.MlDsa.X86_64.Verify.PostB x x' W₁) (hy : VG.Proof.MlDsa.X86_64.Verify.PostB y y' W₂) : VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs x' y' :=
  ⟨h.1.post hx, h.2.1.post hy, h.2.2.post hx hy⟩

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem LRel.step {rbs wbs : List (Reg × Nat)} {c : Prog isa}
    (htr : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs) c fun _ _ => True)
    (hok : ∀ x, VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x → WP isa c x fun x' => ∃ W, VG.Proof.MlDsa.X86_64.Verify.PostB x x' W) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs) c (VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, VG.Proof.MlDsa.X86_64.Verify.PostB x x' W) (fun x y h => ⟨hok x h.1, hok y h.2.1⟩)
    fun _ _ _ _ h ⟨_, hx⟩ ⟨_, hy⟩ => h.post hx hy

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P :=
  RelCT.postDep (VG.Proof.MlDsa.X86_64.Verify.block_nomem_tr fun _ hi => absurd hi List.not_mem_nil) (F := fun x x' => x' = x)
    (fun _ _ _ => ⟨WP.block_nil rfl, WP.block_nil rfl⟩) fun _ _ _ _ h hx hy => hx ▸ hy ▸ h

theorem kzero_tr {P : State → State → Prop} (h : ∀ x y, P x y → x.gpr .rbx = y.gpr .rbx) :
    RelCT isa P (.block VG.Impl.MlDsa.X86_64.Verify.kzero) fun _ _ => True :=
  taintRel [.rbx] (fun x y hp r hr => by simp only [List.mem_singleton] at hr; subst hr; exact h x y hp)
    (by taint_decide)

/-! ## The calls -/

theorem k_in {bs wbs : List (Reg × Nat)} (hk : VG.Proof.MlDsa.X86_64.Verify.kChk bs wbs = true) :
    VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc 0) 200 = true ∧ VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc 200) 640 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.kChk, Bool.and_eq_true] at hk; exact ⟨hk.1.1.1.2, hk.1.1.2⟩

theorem kk16 {s s1 : State} (hsp : s1.gpr .rsp = s.gpr .rsp) {R : Region} (h : (below (s.gpr .rsp) 32).Disjoint R) :
    (below (s1.gpr .rsp) 16).Disjoint R := by
  rw [hsp]; exact h.sub_left (below_sub (by omega) (by omega))

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true)
include L hk

theorem kabs_args {src : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len pos : Nat} (hp : VG.Proof.MlDsa.X86_64.Verify.pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136)
    {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.kabsArgs src len 136 pos) s s1) :
    AbsorbArgs s1 (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) (VG.Proof.MlDsa.X86_64.Verify.pa s src) (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 200)) 136 pos len := by
  obtain ⟨d1, k1, k2, _, _⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec L hk
  simp only [VG.Proof.MlDsa.X86_64.Verify.pieceChk, Bool.and_eq_true] at hp
  obtain ⟨⟨p1, p2⟩, p3⟩ := hp
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec p3; have := (L.ok _ hn).1; omega
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, hpos, by omega, d1, L.disj p1, L.disj p2,
    VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp k1, VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp (L.stkD p3), VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp k2⟩

theorem kpad_args {pos : Nat} (hpos : pos < 136) {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.kpadArgs 136 pos 0x1f) s s1) :
    PadArgs s1 (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 200)) 136 pos := by
  obtain ⟨d1, k1, k2, _, _⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec L hk
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r4, by decide, hpos, d1, VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp k1, VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp k2⟩

theorem ksqz_args {out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len : Nat} (ho : VG.Proof.MlDsa.X86_64.Verify.outChk (rbs ++ wbs) wbs out len = true) {s1 : State}
    (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.ksqzArgs 136 out len) s s1) :
    SqueezeArgs s1 (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 0)) (VG.Proof.MlDsa.X86_64.Verify.pa s out) (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc 200)) 136 0 len := by
  obtain ⟨d1, k1, k2, _, _⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec L hk
  simp only [VG.Proof.MlDsa.X86_64.Verify.outChk, Bool.and_eq_true] at ho
  obtain ⟨⟨⟨o1, o2⟩, o3⟩, _⟩ := ho
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec o3; have := (L.ok _ hn).1; omega
  exact ⟨h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, by decide, by decide, by omega, (L.disj o1).symm, d1,
    L.disj o2, VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp k1, VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp (L.stkD o3), VG.Proof.MlDsa.X86_64.Verify.kk16 h1.rsp k2⟩

end


/-- A pointer's value agrees in two runs in the same layout. -/
theorem LRel.val {rbs wbs : List (Reg × Nat)} {x y : State} (h : VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs x y) {p : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat}
    (hin : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) p l = true) : (Arg.ptr p).val x = (Arg.ptr p).val y :=
  h.2.2.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs h.1.ok hin)

theorem kabs_aok {bs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk bs wbs = true) {src : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len pos : Nat}
    (hp : VG.Proof.MlDsa.X86_64.Verify.pieceChk bs src len = true) (hpos : pos < 136) : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.kabsArgs src len 136 pos, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.pieceChk, Bool.and_eq_true] at hp
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec hp.2; have := (hS _ hn).1; omega
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS (VG.Proof.MlDsa.X86_64.Verify.k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show pos < 2 ^ 31 by omega, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hp.2, by decide⟩, ⟨hlen, by decide⟩,
    ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS (VG.Proof.MlDsa.X86_64.Verify.k_in hk).2, by decide⟩⟩

theorem kpad_aok {bs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk bs wbs = true) {pos : Nat} (hpos : pos < 136) :
    ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.kpadArgs 136 pos 0x1f, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS (VG.Proof.MlDsa.X86_64.Verify.k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show pos < 2 ^ 31 by omega, by decide⟩, ⟨show 0x1f < 2 ^ 31 by decide, by decide⟩,
    ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS (VG.Proof.MlDsa.X86_64.Verify.k_in hk).2, by decide⟩⟩

theorem ksqz_aok {bs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk bs wbs = true) {out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len : Nat}
    (ho : VG.Proof.MlDsa.X86_64.Verify.outChk bs wbs out len = true) : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.ksqzArgs 136 out len, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.outChk, Bool.and_eq_true] at ho
  have hlen : len < 2 ^ 31 := by
    obtain ⟨n, hn, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec ho.1.2; have := (hS _ hn).1; omega
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS (VG.Proof.MlDsa.X86_64.Verify.k_in hk).1, by decide⟩, ⟨show 136 < 2 ^ 31 by decide, by decide⟩,
    ⟨show 0 < 2 ^ 31 by decide, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS ho.1.2, by decide⟩, ⟨hlen, by decide⟩,
    ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS (VG.Proof.MlDsa.X86_64.Verify.k_in hk).2, by decide⟩⟩

theorem kabs_tr {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true) {src : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len pos : Nat}
    (hp : VG.Proof.MlDsa.X86_64.Verify.pieceChk (rbs ++ wbs) src len = true) (hpos : pos < 136) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs) (VG.Impl.MlDsa.X86_64.Verify.kabs src len 136 pos) fun _ _ => True := by
  have hp' := hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.pieceChk, Bool.and_eq_true] at hp'
  have p3 := hp'.2
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr (k := Proof.Sha3.absorbX86_64) Proof.Sha3.X86_64.Stream.Absorb.absorb_correct
    Proof.Sha3.X86_64.Stream.Absorb.absorb_ct (VG.Proof.MlDsa.X86_64.Verify.kabs_aok hS hk hp hpos)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  · obtain ⟨_, _, _, w1, w2⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec h.1 hk
    obtain ⟨_, _, _, w1', w2'⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec h.2.1 hk
    refine ⟨_, _, _, _, absorb_pre (VG.Proof.MlDsa.X86_64.Verify.kabs_args h.1 hk hp hpos h1), absorb_pre (VG.Proof.MlDsa.X86_64.Verify.kabs_args h.2.1 hk hp hpos h2), ?_,
      Covers.append_left (h.1.cR p3) (Covers.right (Covers.cons w1 w2)), Covers.cons w1 w2,
      Covers.append_left (h.2.1.cR p3) (Covers.right (Covers.cons w1' w2')), Covers.cons w1' w2', h.2.2.2⟩
    simp only [Proof.Sha3.absorbX86_64, State.withRegions_gpr, State.callEntry_rsp,
      State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
      State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]
    rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h2.r5, h1.rsp, h2.rsp,
      h.val (VG.Proof.MlDsa.X86_64.Verify.k_in hk).1, h.val (VG.Proof.MlDsa.X86_64.Verify.k_in hk).2, h.val p3, h.2.2.2]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


theorem kpad_tr {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true) {pos : Nat}
    (hpos : pos < 136) : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs) (VG.Impl.MlDsa.X86_64.Verify.kpad 136 pos 0x1f) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr (k := Proof.Sha3.padX86_64) Proof.Sha3.X86_64.Stream.Pad.pad_correct
    Proof.Sha3.X86_64.Stream.Pad.pad_ct (VG.Proof.MlDsa.X86_64.Verify.kpad_aok hS hk hpos)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  obtain ⟨_, _, _, w1, w2⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec h.1 hk
  obtain ⟨_, _, _, w1', w2'⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec h.2.1 hk
  refine ⟨_, _, _, _, pad_pre (VG.Proof.MlDsa.X86_64.Verify.kpad_args h.1 hk hpos h1), pad_pre (VG.Proof.MlDsa.X86_64.Verify.kpad_args h.2.1 hk hpos h2), ?_,
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1 w2)), Covers.cons w1 w2,
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1' w2')), Covers.cons w1' w2', h.2.2.2⟩
  simp only [Proof.Sha3.padX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide)]
  rw [h1.r0, h1.r1, h1.r2, h1.r4, h2.r0, h2.r1, h2.r2, h2.r4, h1.rsp, h2.rsp,
    h.val (VG.Proof.MlDsa.X86_64.Verify.k_in hk).1, h.val (VG.Proof.MlDsa.X86_64.Verify.k_in hk).2, h.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ksqz_tr {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) (hk : VG.Proof.MlDsa.X86_64.Verify.kChk (rbs ++ wbs) wbs = true)
    {out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len : Nat} (ho : VG.Proof.MlDsa.X86_64.Verify.outChk (rbs ++ wbs) wbs out len = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs) (VG.Impl.MlDsa.X86_64.Verify.ksqz 136 out len) fun _ _ => True := by
  have ho' := ho
  simp only [VG.Proof.MlDsa.X86_64.Verify.outChk, Bool.and_eq_true] at ho'
  obtain ⟨⟨⟨_, _⟩, o3⟩, o4⟩ := ho'
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr (k := Proof.Sha3.squeezeX86_64) Proof.Sha3.X86_64.Stream.Squeeze.squeeze_correct
    Proof.Sha3.X86_64.Stream.Squeeze.squeeze_ct (VG.Proof.MlDsa.X86_64.Verify.ksqz_aok hS hk ho)
    (by simp only [List.map_cons, List.map_nil]; decide) fun x y x1 y1 h h1 h2 => ?_
  obtain ⟨_, _, _, w1, w2⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec h.1 hk
  obtain ⟨_, _, _, w1', w2'⟩ := VG.Proof.MlDsa.X86_64.Verify.kChk_spec h.2.1 hk
  refine ⟨_, _, _, _, squeeze_pre (VG.Proof.MlDsa.X86_64.Verify.ksqz_args h.1 hk ho h1), squeeze_pre (VG.Proof.MlDsa.X86_64.Verify.ksqz_args h.2.1 hk ho h2), ?_,
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1 (Covers.cons (h.1.cW o4) w2))),
    Covers.cons w1 (Covers.cons (h.1.cW o4) w2),
    Covers.append_left Covers.nil (Covers.right (Covers.cons w1' (Covers.cons (h.2.1.cW o4) w2'))),
    Covers.cons w1' (Covers.cons (h.2.1.cW o4) w2'), h.2.2.2⟩
  simp only [Proof.Sha3.squeezeX86_64, State.withRegions_gpr, State.callEntry_rsp,
    State.callEntry_gpr _ (show Reg.rdi ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rsi ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.rdx ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.rcx ≠ .rsp by decide),
    State.callEntry_gpr _ (show Reg.r8 ≠ .rsp by decide), State.callEntry_gpr _ (show Reg.r9 ≠ .rsp by decide)]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.r5, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h2.r5, h1.rsp, h2.rsp,
    h.val (VG.Proof.MlDsa.X86_64.Verify.k_in hk).1, h.val (VG.Proof.MlDsa.X86_64.Verify.k_in hk).2, h.val o3, h.2.2.2]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hash2_tr {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {a b out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {la lb len : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Verify.hashChk (rbs ++ wbs) wbs a la b lb out len = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.LRel rbs wbs) (hash2 a la b lb out len) fun _ _ => True := by
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.hashChk, Bool.and_eq_true, decide_eq_true_eq] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk, pa'⟩, pb⟩, ho⟩, _⟩, _⟩, _⟩, hla⟩, _⟩ := hc'
  unfold hash2
  refine RelCT.seq (LRel.step (VG.Proof.MlDsa.X86_64.Verify.kzero_tr fun x y h => h.2.2.1 _ (by decide))
    fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Verify.kzero_ok x (VG.Proof.MlDsa.X86_64.Verify.kChk_spec Lx hk).2.2.2.1) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (VG.Proof.MlDsa.X86_64.Verify.kabs_tr hS hk pa' (by decide))
    fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Verify.kabs_ok Lx hk pa' (by decide)) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (VG.Proof.MlDsa.X86_64.Verify.kabs_tr hS hk pb (Nat.mod_lt _ (by decide)))
    fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Verify.kabs_ok Lx hk pb (Nat.mod_lt _ (by decide))) fun _ h => ⟨_, h.1⟩) ?_
  refine RelCT.seq (LRel.step (VG.Proof.MlDsa.X86_64.Verify.kpad_tr hS hk (Nat.mod_lt _ (by decide)))
    fun x Lx => WP.mono (VG.Proof.MlDsa.X86_64.Verify.kpad_ok Lx hk (Nat.mod_lt _ (by decide))) fun _ h => ⟨_, h.1⟩) ?_
  exact VG.Proof.MlDsa.X86_64.Verify.ksqz_tr hS hk ho

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Blocks`. -/
section

/-!
# ML-DSA verification on x86-64: the blocks between the calls

A byte store (`setB_ok`), a copy (`copy_ok`), the mask of a sampler's output
by its result (`mask_ok`: unchanged if 1, zero if 0), and the updates of the
result in `r15` (`and15_ok`, `mov15_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## A byte -/

theorem b8_ofNat {v : Nat} (_hv : v < 256) :
    BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.ofNat 32 v)) = BitVec.ofNat 8 v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem setB_ok (p : VG.Impl.MlDsa.X86_64.Verify.Ptr) (v : Nat) (hr : p.1 ≠ .rax) (hv : v < 256) (s : State)
    (hw : InRegions s.wr (VG.Proof.MlDsa.X86_64.Verify.pa s p) 1) :
    WP isa (.block (VG.Impl.MlDsa.X86_64.Verify.setB p v)) s fun s' =>
      s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Verify.pa s p) (BitVec.ofNat 8 v) ∧ Keep [.rax] s s' := by
  refine WP.mono (WP.keep [.rax] (Q := fun s' => s'.mem = s.mem.writeW (VG.Proof.MlDsa.X86_64.Verify.pa s p) (BitVec.ofNat 8 v)) ?_ (by rfl))
    fun s' ⟨h, k⟩ => ⟨h, k⟩
  unfold VG.Impl.MlDsa.X86_64.Verify.setB
  have e : s.ea (VG.Impl.MlKem.X86_64.at_ p.1 p.2) = VG.Proof.MlDsa.X86_64.Verify.pa s p := ea_at s p.1 p.2
  xrun [hw, hr, VG.Proof.MlDsa.X86_64.Verify.b8_ofNat hv, e]

/-! ## A copy -/

theorem b8b (x : Byte) : BitVec.setWidth 8 (BitVec.setWidth 64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem copyBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1) (h1 : InRegions s.wr (s.gpr .rdi) 1) :
    WP isa (.block [.movzx8 .rax (VG.Impl.MlKem.X86_64.at_ .rsi 0), .store8 (VG.Impl.MlKem.X86_64.at_ .rdi 0) .rax, .alu .add .rdi (.imm 1),
      .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem (s.gpr .rsi)) ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧
        s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdi, .rsi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1, VG.Proof.MlDsa.X86_64.Verify.b8b]

theorem inRegions_byte {rs : List Region} {a : Addr} {n k : Nat} (h : InRegions rs a n) (hk : k < n)
    (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 k) 1 := by
  obtain ⟨r, hr, hc⟩ := h
  exact ⟨r, hr, hc.byte (by rw [Mem.sub_ofNat_toNat a (by omega)]; exact hk)⟩

abbrev copyArgs (dst src : VG.Impl.MlDsa.X86_64.Verify.Ptr) (n : Nat) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr dst), (.rsi, .ptr src), (.rcx, .imm n)]

theorem copy_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {dst src : VG.Impl.MlDsa.X86_64.Verify.Ptr} {n : Nat}
    (hn0 : 0 < n) (hsd : VG.Proof.MlDsa.X86_64.Verify.sepB (rbs ++ wbs) src n dst n = true) (hw : VG.Proof.MlDsa.X86_64.Verify.inB wbs dst n = true) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.copy dst src n) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(dst, n)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s dst) n = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s src) n := by
  have hsd' := VG.Proof.MlDsa.X86_64.Verify.sepB_spec hsd
  have hS := L.ok
  have hn : n < 2 ^ 31 := by
    obtain ⟨m, hm, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec hsd'.1; have := (hS _ hm).1; omega
  have hok : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.copyArgs dst src n, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hsd'.2.1, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hsd'.1, by decide⟩, ⟨hn, by decide⟩⟩
  have hrd := L.inR hsd'.1
  have hwr := L.inW hw
  have hdj := L.disj hsd
  unfold VG.Impl.MlDsa.X86_64.Verify.copy
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s)
    fun s1 (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.copyArgs dst src n) s s1) => ?_)
  refine WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega) hn0 (fun k s' =>
      s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s dst + BitVec.ofNat 64 k ∧ s'.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s src + BitVec.ofNat 64 k ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Frame [⟨VG.Proof.MlDsa.X86_64.Verify.pa s dst, n⟩] s.mem s'.mem ∧
      (∀ j < k, s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s dst + BitVec.ofNat 64 j) = s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s src + BitVec.ofNat 64 j)) ∧
      Keep VG.Proof.MlDsa.X86_64.Verify.argRegs s s')
    (fun k hk s' ⟨hdi, hsi, hrd', hwr', hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [h1.r0]; simp [Arg.val], by rw [h1.r1]; simp [Arg.val], h1.2.2.1, h1.2.2.2,
      by rw [h1.1.2]; exact Frame.refl _ _, fun j hj => absurd hj (Nat.not_lt_zero _), h1.2⟩ (by rw [h1.r2]; rfl))
    fun s' ⟨_, _, _, _, hf, hc, kk⟩ => ⟨VG.Proof.MlDsa.X86_64.Verify.postB_of_keep kk (by decide) (by simpa using hf), kk.gpr (by decide), ?_⟩
  · refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyBody_ok s' (by rw [hrd', hwr', hsi]; exact VG.Proof.MlDsa.X86_64.Verify.inRegions_byte hrd hk (by omega))
      (by rw [hwr', hdi]; exact VG.Proof.MlDsa.X86_64.Verify.inRegions_byte hwr hk (by omega))) fun s'' ⟨⟨hm, hdi', hsi', hcx, hz⟩, k'⟩ =>
        ⟨⟨by rw [hdi', hdi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add],
          by rw [hsi', hsi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add],
          k'.2.1.trans hrd', k'.2.2.trans hwr', ?_, fun j hj => ?_, (kk.trans k').mono (by decide)⟩, hcx, hz⟩
    · rw [hm, hdi]
      exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
    · have hsrc : s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s src + BitVec.ofNat 64 k) = s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s src + BitVec.ofNat 64 k) :=
        hf.bytes (R := ⟨VG.Proof.MlDsa.X86_64.Verify.pa s src, n⟩) (by simpa using hdj) (show n ≤ 2 ^ 64 by omega) hk
      rw [hm, hdi, hsi, VG.WriteBytes.writeW8_apply]
      by_cases e : j = k
      · subst e; rw [VG.Proof.MlKem.X86_64.ifp rfl, hsrc]
      · rw [VG.Proof.MlKem.X86_64.ifn (fun h => e (by have := congrArg BitVec.toNat h; simp at this; omega)), hc j (by omega)]
  · simp only [bytesAt]
    exact List.map_congr_left fun i hi => hc i (List.mem_range.mp hi)


/-! ## The mask -/

theorem maskPre_ok (s : State) :
    WP isa (.block [.mov32 .rdx (.imm 0), .alu32 .sub .rdx (.reg .rax)]) s fun s' =>
      (s'.mem = s.mem ∧ (s'.gpr .rdx).setWidth 32 = 0 - (s.gpr .rax).setWidth 32) ∧ Keep [.rdx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

theorem maskBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 4) (h1 : InRegions s.wr (s.gpr .rdi) 4) :
    WP isa (.block [.mov32 .rax (.mem (VG.Impl.MlKem.X86_64.at_ .rdi 0)), .alu32 .and .rax (.reg .rdx), .store32 (VG.Impl.MlKem.X86_64.at_ .rdi 0) .rax,
      .alu .add .rdi (.imm 4), .alu .sub .rcx (.imm 1)]) s fun s' =>
      (s'.mem = s.mem.writeW (s.gpr .rdi) (s.mem.readW (s.gpr .rdi) 32 &&& (s.gpr .rdx).setWidth 32) ∧
        s'.gpr .rdi = s.gpr .rdi + 4 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.gpr .rdx = s.gpr .rdx ∧
        s'.zf = some (s.gpr .rcx - 1 == 0)) ∧ Keep [.rax, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun [h0, h1]

theorem coeffAt_writeW' (m : Mem) (p : Addr) {N i j : Nat} (hN : 4 * N ≤ 2 ^ 64) (hi : i < N) (hj : j < N)
    (v : BitVec 32) :
    coeffAt (m.writeW (p + BitVec.ofNat 64 (4 * j)) v) p i = if j = i then v else coeffAt m p i := by
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

/-- The mask of the `N` coefficients from `a` by `eax`: each `∧ -eax`. -/
theorem maskN_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr} {N : Nat} (hN0 : 0 < N)
    (hN : N < 2 ^ 29) (hi : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) a (4 * N) = true) (hw : VG.Proof.MlDsa.X86_64.Verify.inB wbs a (4 * N) = true) :
    WP isa (mask a N) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(a, 4 * N)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ i < N, coeffAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) i = coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) := by
  have hS := L.ok
  have hok : ∀ x ∈ ([(.rdi, .ptr a), (.rcx, .imm N)] : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)), x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hi, by decide⟩, ⟨show N < 2 ^ 31 by omega, by decide⟩⟩
  have hrd := L.inR hi
  have hwr := L.inW hw
  unfold mask
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.maskPre_ok s) fun s₀ ⟨⟨hm₀, hd₀⟩, k₀⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok _ hok (by simp only [List.map_cons, List.map_nil]; decide) s₀)
    fun s1 ⟨⟨hv1, hm1⟩, k1⟩ => ?_
  have hb := VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS hi
  have nb : a.1 ∉ [Reg.rdx] := by
    simp only [List.mem_singleton]; intro h; rw [h] at hb; exact absurd hb (by decide)
  have e1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s a := by
    rw [hv1 _ (List.mem_cons_self ..)]; simp only [Arg.val, VG.Proof.MlDsa.X86_64.Verify.pa]; rw [k₀.gpr nb]
  have e2 : s1.gpr .rcx = BitVec.ofNat 64 N := hv1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hd1 : (s1.gpr .rdx).setWidth 32 = 0 - (s.gpr .rax).setWidth 32 := by rw [k1.gpr (by simp), hd₀]
  have k01 : Keep [.rdx, .rdi, .rcx] s s1 := (k₀.trans k1).mono (by simp)
  have hm01 : s1.mem = s.mem := hm1.trans hm₀
  refine WP.mono (wp_countdown (cnt := .rcx) (N := N) (by omega) hN0 (fun k s' =>
      s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s a + BitVec.ofNat 64 (4 * k) ∧ (s'.gpr .rdx).setWidth 32 = 0 - (s.gpr .rax).setWidth 32 ∧
      Frame [⟨VG.Proof.MlDsa.X86_64.Verify.pa s a, 4 * N⟩] s.mem s'.mem ∧
      (∀ i < N, coeffAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) i =
        if i < k then coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) else coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) i) ∧
      Keep [.rdx, .rdi, .rcx, .rax] s s')
    (fun k hk s' ⟨hdi, hdx, hf, hc, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [e1]; simp, hd1, by rw [hm01]; exact Frame.refl _ _, fun i _ => by rw [hm01, VG.Proof.MlKem.X86_64.ifn (Nat.not_lt_zero _)],
      k01.mono (by simp)⟩ e2)
    fun s' ⟨_, _, hf, hc, kk⟩ => ⟨VG.Proof.MlDsa.X86_64.Verify.postB_of_keep kk (by decide) (by simpa using hf),
      kk.gpr (by decide), fun i hi => by rw [hc i hi, VG.Proof.MlKem.X86_64.ifp hi]⟩
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.maskBody_ok s' (by rw [kk.2.1, kk.2.2, hdi]; exact VG.Proof.MlDsa.X86_64.Verify.inRegions_sub hrd (by omega) (by omega))
      (by rw [kk.2.2, hdi]; exact VG.Proof.MlDsa.X86_64.Verify.inRegions_sub hwr (by omega) (by omega)))
    fun s'' ⟨⟨hm, hdi', hcx, hdx', hz⟩, k'⟩ => ⟨⟨?_, by rw [hdx', hdx], ?_, fun i hi => ?_,
      (kk.trans k').mono (by simp)⟩, hcx, hz⟩
  · rw [hdi', hdi, show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add,
      show 4 * k + 4 = 4 * (k + 1) by omega]
  · rw [hm, hdi]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_offset' (by omega) (by omega))
  · have hck : s'.mem.readW (VG.Proof.MlDsa.X86_64.Verify.pa s a + BitVec.ofNat 64 (4 * k)) 32 = coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) k := by
      have := hc k (by omega)
      rw [VG.Proof.MlKem.X86_64.ifn (Nat.lt_irrefl _)] at this
      exact this
    rw [hm, hdi, hck, hdx, VG.Proof.MlDsa.X86_64.Verify.coeffAt_writeW' _ _ (N := N) (by omega) hi (by omega)]
    by_cases e : k = i
    · subst e; rw [VG.Proof.MlKem.X86_64.ifp rfl, VG.Proof.MlKem.X86_64.ifp (Nat.lt_succ_self _)]
    · rw [VG.Proof.MlKem.X86_64.ifn e, hc i hi]
      by_cases h' : i < k
      · rw [VG.Proof.MlKem.X86_64.ifp h', VG.Proof.MlKem.X86_64.ifp (by omega)]
      · rw [VG.Proof.MlKem.X86_64.ifn h', VG.Proof.MlKem.X86_64.ifn (by omega)]

/-- The mask of the polynomial at `a` by `eax`: each coefficient `∧ -eax`. -/
theorem mask_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr}
    (hi : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) a 1024 = true) (hw : VG.Proof.MlDsa.X86_64.Verify.inB wbs a 1024 = true) :
    WP isa (mask a) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(a, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      ∀ i < n, coeffAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) i = coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) i &&& (0 - (s.gpr .rax).setWidth 32) :=
  VG.Proof.MlDsa.X86_64.Verify.maskN_ok L (N := 256) (by decide) (by decide) hi hw

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallArith`. -/
section

/-!
# ML-DSA verification on x86-64: calls of the arithmetic primitives

For each call of `vg_mldsa_ntt`, `vg_mldsa_inv_ntt` (`ipAt`),
`vg_mldsa_multiply_ntt`, `vg_mldsa_multiply_add_ntt` and `vg_mldsa_sub`: what
it needs of the layout (a check evaluated on the pointers, `…Chk`), what it
does (`…_ok`), and that two runs whose layout registers agree leak the same
(`…_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def ipChk (bs : List (Reg × Nat)) (wbs : List (Reg × Nat)) (f : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs f 1024 (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 1024 && VG.Proof.MlDsa.X86_64.Verify.inB wbs f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB wbs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 1024

abbrev ipArgs (f : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr f), (.rsi, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS))]

theorem ip_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.ipChk bs wbs f = true) :
    ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.ipArgs f, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.ipChk, Bool.and_eq_true] at hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L hc.1.1.1.2, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L hc.1.1.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr}
  (hc : VG.Proof.MlDsa.X86_64.Verify.ipChk (rbs ++ wbs) wbs f = true)
include L hc

theorem ip_cov : Covers ([] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.ipChk, Bool.and_eq_true] at hc
  exact ⟨Covers.right (Covers.cons (L.cW hc.1.2) (L.cW hc.2)), Covers.cons (L.cW hc.1.2) (L.cW hc.2)⟩

theorem ip_pre {t : Poly → Poly} (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.ipArgs f) s s1) :
    (inPlaceContract X86_64.abi (t : Poly → Poly) 16).pre
      (s1.callEntry.withRegions [] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 1024⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.ipChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s f := h1.r0
  have g2 : s1.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) := h1.r1
  sig_pre [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3,
    L.wreduced c2 _ hr⟩

end

theorem ipAt_ok {t : Poly → Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.ipChk (rbs ++ wbs) wbs f = true)
    (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) :
    WP isa (callAt n c (VG.Proof.MlDsa.X86_64.Verify.ipArgs f)) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(f, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f) (t (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f))) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.ip_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.ip_pre L hc hr h1) (VG.Proof.MlDsa.X86_64.Verify.ip_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.ip_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have g1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s f := h1.r0
  have c2 : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) f 1024 = true := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.ipChk, Bool.and_eq_true] at hc; exact hc.1.1.1.2
  sig_post [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [g1, hm, h1.rsp, h1.1.2, L.wpolyAt c2] at hq
  exact hq

theorem ipAt_tr {t : Poly → Poly} {n : String} {c : Prog isa} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk c (inPlaceContract X86_64.abi t 16))
    {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.ipChk (rbs ++ wbs) wbs f = true)
    {P : State → State → Prop}
    (hP : ∀ x y, P x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y f) ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa P (callAt n c (VG.Proof.MlDsa.X86_64.Verify.ipArgs f)) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.ip_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  · intro x y x1 y1 hp h1 h2
    obtain ⟨Lx, Ly, rx, ry, e⟩ := hP x y hp
    refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.ip_pre Lx hc rx h1, VG.Proof.MlDsa.X86_64.Verify.ip_pre Ly hc ry h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.ip_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.ip_cov Lx hc).2,
      (VG.Proof.MlDsa.X86_64.Verify.ip_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.ip_cov Ly hc).2, e.2⟩
    have hb : f.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases := by
      simp only [VG.Proof.MlDsa.X86_64.Verify.ipChk, Bool.and_eq_true] at hc; exact VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS hc.1.1.1.2
    sig_pub [inPlaceContract, inPlaceSig, X86_64.abi, VG.X86_64.argRegs]
    rw [h1.r0, h2.r0, h1.r1,
      h2.r1, h1.rsp, h2.rsp]
    exact ⟨by rw [e.2], by simp only [Arg.val]; rw [e.pa hb], by simp only [Arg.val]; rw [e.pa (by decide)]⟩


/-! ## Products -/

def mulChk (bs wbs : List (Reg × Nat)) (h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs h 1024 f 1024 && VG.Proof.MlDsa.X86_64.Verify.sepB bs h 1024 g 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs h 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs g 1024 &&
    VG.Proof.MlDsa.X86_64.Verify.inB wbs h 1024

abbrev mulArgs (h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr h), (.rsi, .ptr f), (.rdx, .ptr g)]

theorem mul_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.mulChk bs wbs h f g = true) :
    ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.mulArgs h f g, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c3, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c4, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c5, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr}
  (hc : VG.Proof.MlDsa.X86_64.Verify.mulChk (rbs ++ wbs) wbs h f g = true)
include L hc

theorem mul_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s g, 1024⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  exact ⟨Covers.append_left (Covers.cons (L.cR c4) (L.cR c5)) (L.cR c3), L.cW c6⟩

theorem mul_pre (hf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g)) {s1 : State}
    (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.mulArgs h f g) s s1) :
    (mulContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s g, 1024⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s h := h1.r0
  have g2 : s1.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s f := h1.r1
  have g3 : s1.gpr .rdx = VG.Proof.MlDsa.X86_64.Verify.pa s g := h1.r2
  sig_pre [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4, L.ret8 c5, L.stk16 c3, L.stk16 c4,
    L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, L.wreduced c4 _ hf, L.wreduced c5 _ hg⟩

theorem mulAdd_pre (hh : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s h)) (hf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g))
    {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.mulArgs h f g) s s1) :
    (mulAddContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s g, 1024⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s h := h1.r0
  have g2 : s1.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s f := h1.r1
  have g3 : s1.gpr .rdx = VG.Proof.MlDsa.X86_64.Verify.pa s g := h1.r2
  sig_pre [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4, L.ret8 c5, L.stk16 c3, L.stk16 c4,
    L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, L.wreduced c3 _ hh, L.wreduced c4 _ hf, L.wreduced c5 _ hg⟩

end

theorem mulAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.mul (mulContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.mulChk (rbs ++ wbs) wbs h f g = true)
    (hf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.mulAt P h f g) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(h, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s h) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g))) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.mul_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.mul_pre L hc hf hg h1) (VG.Proof.MlDsa.X86_64.Verify.mul_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.mul_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c4⟩, c5⟩, _⟩ := hc
  sig_post [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c4, L.wpolyAt c5] at hq
  exact hq

theorem mulAddAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.mulAdd (mulAddContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.mulChk (rbs ++ wbs) wbs h f g = true)
    (hh : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s h)) (hf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.mulAddAt P h f g) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(h, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s h) (VG.Spec.MlDsa.add (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s h)) (multiplyNTT (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g)))) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.mul_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.mulAdd_pre L hc hh hf hg h1) (VG.Proof.MlDsa.X86_64.Verify.mul_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.mul_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_post [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c3, L.wpolyAt c4, L.wpolyAt c5] at hq
  exact hq

theorem mul_pub {x y x1 y1 : State} {h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hb : h.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases ∧ f.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases ∧ g.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) (e : VG.Proof.MlDsa.X86_64.Verify.SameB x y)
    (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.mulArgs h f g) x x1) (h2 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.mulArgs h f g) y y1) :
    x1.gpr .rsp - 8 = y1.gpr .rsp - 8 ∧ x1.gpr .rdi = y1.gpr .rdi ∧ x1.gpr .rsi = y1.gpr .rsi ∧
      x1.gpr .rdx = y1.gpr .rdx := by
  rw [h1.r0, h1.r1, h1.r2, h2.r0, h2.r1, h2.r2]
  simp only [Arg.val]
  refine ⟨?_, e.pa hb.1, e.pa hb.2.1, e.pa hb.2.2⟩
  rw [h1.rsp, h2.rsp, e.2]

theorem mulAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.mul (mulContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.mulChk (rbs ++ wbs) wbs h f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y g)) ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (VG.Impl.MlDsa.X86_64.Verify.mulAt P h f g) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.mul_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.mul_pre Lx hc rx.1 rx.2 h1, VG.Proof.MlDsa.X86_64.Verify.mul_pre Ly hc ry.1 ry.2 h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.mul_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.mul_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.mul_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.mul_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [mulContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  exact VG.Proof.MlDsa.X86_64.Verify.mul_pub ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3, VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c4, VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c5⟩ e h1 h2

theorem mulAddAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.mulAdd (mulAddContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {h f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.mulChk (rbs ++ wbs) wbs h f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧
      (Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x h) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y h) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y g)) ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (VG.Impl.MlDsa.X86_64.Verify.mulAddAt P h f g) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.mul_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.mulAdd_pre Lx hc rx.1 rx.2.1 rx.2.2 h1, VG.Proof.MlDsa.X86_64.Verify.mulAdd_pre Ly hc ry.1 ry.2.1 ry.2.2 h2, ?_,
    (VG.Proof.MlDsa.X86_64.Verify.mul_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.mul_cov Lx hc).2, (VG.Proof.MlDsa.X86_64.Verify.mul_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.mul_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.mulChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [mulAddContract, mulSig, X86_64.abi, VG.X86_64.argRegs]
  exact VG.Proof.MlDsa.X86_64.Verify.mul_pub ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3, VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c4, VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c5⟩ e h1 h2

/-! ## Subtraction -/

def subChk (bs wbs : List (Reg × Nat)) (f g : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs f 1024 g 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs g 1024 && VG.Proof.MlDsa.X86_64.Verify.inB wbs f 1024

abbrev subArgs (f g : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr f), (.rsi, .ptr g)]

theorem sub_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.subChk bs wbs f g = true) :
    ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.subArgs f g, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c2, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c3, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f g : VG.Impl.MlDsa.X86_64.Verify.Ptr}
  (hc : VG.Proof.MlDsa.X86_64.Verify.subChk (rbs ++ wbs) wbs f g = true)
include L hc

theorem sub_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s g, 1024⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c3) (L.cR c2), L.cW c4⟩

theorem sub_pre (hf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g)) {s1 : State}
    (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.subArgs f g) s s1) :
    (subContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s g, 1024⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s f := h1.r0
  have g2 : s1.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s g := h1.r1
  sig_pre [subContract, accSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3,
    L.wreduced c2 _ hf, L.wreduced c3 _ hg⟩

end

theorem subAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.sub (subContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.subChk (rbs ++ wbs) wbs f g = true)
    (hf : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (hg : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g)) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.subAt P f g) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(f, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f) (VG.Spec.MlDsa.sub (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s g))) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.sub_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.sub_pre L hc hf hg h1) (VG.Proof.MlDsa.X86_64.Verify.sub_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.sub_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [VG.Proof.MlDsa.X86_64.Verify.subChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  sig_post [subContract, accSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wpolyAt c2, L.wpolyAt c3] at hq
  exact hq

theorem subAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.sub (subContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {f g : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.subChk (rbs ++ wbs) wbs f g = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ (Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x f) ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x g)) ∧
      (Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y g)) ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (VG.Impl.MlDsa.X86_64.Verify.subAt P f g) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.sub_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.sub_pre Lx hc rx.1 rx.2 h1, VG.Proof.MlDsa.X86_64.Verify.sub_pre Ly hc ry.1 ry.2 h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.sub_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.sub_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.sub_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.sub_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.subChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [subContract, accSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h2.r0, h2.r1, h1.rsp, h2.rsp, e.2]
  simp only [Arg.val]
  exact ⟨trivial, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c2), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3)⟩

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallSample`. -/
section

/-!
# ML-DSA verification on x86-64: calls of the samplers

The calls of `vg_mldsa_rej_ntt_poly` (seed at `SB`) and
`vg_mldsa_sample_in_ball`: what they need of the layout (`…Chk`), what they do
(`…_ok`: the result in `eax`, and the sampled polynomial, as `Outcome`), and
that two runs whose layout registers and seeds agree leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The 32-bit result of a function, in `rax`. -/
abbrev res (s : State) : BitVec 32 := (s.gpr .rax).setWidth 32

/-! ## `RejNTTPoly` -/

def rejChk (bs wbs : List (Reg × Nat)) (a : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 34 a 1024 && VG.Proof.MlDsa.X86_64.Verify.sepB bs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 34 (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048 && VG.Proof.MlDsa.X86_64.Verify.sepB bs a 1024 (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048 &&
    VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 34 && VG.Proof.MlDsa.X86_64.Verify.inB bs a 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048 && VG.Proof.MlDsa.X86_64.Verify.inB wbs a 1024 && VG.Proof.MlDsa.X86_64.Verify.inB wbs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048

abbrev rejArgs (a : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB)), (.rsi, .ptr a), (.rdx, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS))]

theorem rej_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.rejChk bs wbs a = true) :
    ∀ x ∈ VG.Proof.MlDsa.X86_64.Verify.rejArgs a, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c4, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c5, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c6, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr}
  (hc : VG.Proof.MlDsa.X86_64.Verify.rejChk (rbs ++ wbs) wbs a = true)
include L hc

theorem rej_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB), 34⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 2048⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, c7⟩, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rej_pre {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.rejArgs a) s s1) :
    (rejNTTContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB), 34⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s a, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 2048⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) := h1.r0
  have g2 : s1.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s a := h1.r1
  have g3 : s1.gpr .rdx = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) := h1.r2
  sig_pre [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.disj c2, L.disj c3, L.ret8 c4, L.ret8 c5, L.ret8 c6, L.stk16 c4,
    L.stk16 c5, L.stk16 c6, L.nwp c4, L.nwp c5, L.nwp c6⟩

end

theorem rejNttAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.rejNtt (rejNTTContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.rejChk (rbs ++ wbs) wbs a = true) :
    WP isa (rejNttAt P a) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(a, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 2048)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (VG.Proof.MlDsa.X86_64.Verify.res s' = 1 → Reduced s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a)) ∧
      Outcome (fun b => rejNTTPoly b.rejNTT (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB)) 34)) (VG.Proof.MlDsa.X86_64.Verify.res s') (polyAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a)) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.rej_args L.ok hc) (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.rej_pre L hc h1) (VG.Proof.MlDsa.X86_64.Verify.rej_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.rej_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [VG.Proof.MlDsa.X86_64.Verify.rejChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, _⟩, _⟩ := hc
  sig_post [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val] at hq
  rw [L.wbytesAt c4] at hq
  exact hq

theorem rejNttAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.rejNtt (rejNTTContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.rejChk (rbs ++ wbs) wbs a = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y ∧
      bytesAt x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB)) 34 = bytesAt y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB)) 34) :
    RelCT isa Q (rejNttAt P a) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.rej_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, e, eb⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.rej_pre Lx hc h1, VG.Proof.MlDsa.X86_64.Verify.rej_pre Ly hc h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.rej_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.rej_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.rej_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.rej_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.rejChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc'
  sig_pub [rejNTTContract, rejNTTSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h2.r0, h2.r1, h2.r2, h1.1.2, h2.1.2, h1.rsp, h2.rsp]
  simp only [Arg.val]
  rw [Lx.wbytesAt c4, Ly.wbytesAt c4, eb]
  exact ⟨by rw [e.2], rfl, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c4), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c5), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c6)⟩

/-! ## `RejNTTPoly` four times -/

def rej4Chk (bs wbs : List (Reg × Nat)) (a w : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs (VG.Impl.MlDsa.X86_64.Verify.sc oSB4) 136 a 4096 && VG.Proof.MlDsa.X86_64.Verify.sepB bs (VG.Impl.MlDsa.X86_64.Verify.sc oSB4) 136 w 8192 && VG.Proof.MlDsa.X86_64.Verify.sepB bs a 4096 w 8192 &&
    VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc oSB4) 136 && VG.Proof.MlDsa.X86_64.Verify.inB bs a 4096 && VG.Proof.MlDsa.X86_64.Verify.inB bs w 8192 && VG.Proof.MlDsa.X86_64.Verify.inB wbs a 4096 && VG.Proof.MlDsa.X86_64.Verify.inB wbs w 8192

abbrev rej4Args (a w : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)), (.rsi, .ptr a), (.rdx, .ptr w)]

theorem rej4_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {a w : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.rej4Chk bs wbs a w = true) :
    ∀ x ∈ VG.Proof.MlDsa.X86_64.Verify.rej4Args a w, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.rej4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c4, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c5, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c6, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a w : VG.Impl.MlDsa.X86_64.Verify.Ptr}
  (hc : VG.Proof.MlDsa.X86_64.Verify.rej4Chk (rbs ++ wbs) wbs a w = true)
include L hc

theorem rej4_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oSB4), 136⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s w, 8192⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s w, 8192⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.rej4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, c7⟩, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

theorem rej4_pre {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.rej4Args a w) s s1) :
    (rejNTT4Contract X86_64.abi 24).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oSB4), 136⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s a, 4096⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s w, 8192⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.rej4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  have g1 : s1.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oSB4) := h1.r0
  have g2 : s1.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s a := h1.r1
  have g3 : s1.gpr .rdx = VG.Proof.MlDsa.X86_64.Verify.pa s w := h1.r2
  sig_pre [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  rw [g1, g2, g3, h1.rsp]
  exact ⟨L.sp24, rfl, rfl, L.disj c1, L.disj c2, L.disj c3, L.ret8 c4, L.ret8 c5, L.ret8 c6, L.stk24 c4,
    L.stk24 c5, L.stk24 c6, L.nwp c4, L.nwp c5, L.nwp c6⟩

end

theorem Lay.wseed4 {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s)
    (h : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) (VG.Impl.MlDsa.X86_64.Verify.sc oSB4) 136 = true) (v : BitVec 64) {k : Nat} (hk : k < 4) :
    seed4 (s.mem.writeW (s.gpr .rsp - 8) v) (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)) k = seed4 s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)) k := by
  unfold seed4
  refine Proof.MlKem.bytesAt_congr fun i hi => ?_
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact L.wbytes h v (34 * k + i) (by omega)

theorem rej4At_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.rej4 (rejNTT4Contract X86_64.abi 24)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a w : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.rej4Chk (rbs ++ wbs) wbs a w = true) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.rej4At P a w) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(a, 4096), (w, 8192)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (VG.Proof.MlDsa.X86_64.Verify.res s' = 1 → ∀ k < 4, Reduced s'.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k)) ∧
      ((VG.Proof.MlDsa.X86_64.Verify.res s' = 1 ∧ ∀ k < 4, ∃ b : Bounds, rejNTTPoly b.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)) k) =
          some (polyAt s'.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k))) ∨
        (VG.Proof.MlDsa.X86_64.Verify.res s' = 0 ∧ ∃ k < 4, rejNTTPoly minBounds.rejNTT (seed4 s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)) k) = none)) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.rej4_args L.ok hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.rej4_pre L hc h1) (VG.Proof.MlDsa.X86_64.Verify.rej4_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.rej4_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  simp only [VG.Proof.MlDsa.X86_64.Verify.rej4Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, _⟩, _⟩ := hc
  sig_post [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val] at hq
  obtain ⟨hr, ho⟩ := hq
  refine ⟨hr, ?_⟩
  rcases ho with ⟨h1', hb⟩ | ⟨h0, k, hk, hn⟩
  · exact .inl ⟨h1', fun k hk => by rw [← L.wseed4 c4 _ hk]; exact hb k hk⟩
  · exact .inr ⟨h0, k, hk, by rw [← L.wseed4 c4 _ hk]; exact hn⟩

theorem rej4At_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.rej4 (rejNTT4Contract X86_64.abi 24)) {rbs wbs : List (Reg × Nat)}
    (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {a w : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.rej4Chk (rbs ++ wbs) wbs a w = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y ∧
      bytesAt x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)) 136 = bytesAt y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)) 136) :
    RelCT isa Q (VG.Impl.MlDsa.X86_64.Verify.rej4At P a w) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.rej4_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, e, eb⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.rej4_pre Lx hc h1, VG.Proof.MlDsa.X86_64.Verify.rej4_pre Ly hc h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.rej4_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.rej4_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.rej4_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.rej4_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.rej4Chk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc'
  sig_pub [rejNTT4Contract, rejNTT4Sig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h2.r0, h2.r1, h2.r2, h1.1.2, h2.1.2, h1.rsp, h2.rsp]
  simp only [Arg.val]
  rw [Lx.wbytesAt c4, Ly.wbytesAt c4, eb]
  exact ⟨by rw [e.2], rfl, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c4), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c5), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c6)⟩

/-! ## `SampleInBall` -/

def ballChk (bs wbs : List (Reg × Nat)) (ct : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) (c : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs ct len c 1024 && VG.Proof.MlDsa.X86_64.Verify.sepB bs ct len (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048 && VG.Proof.MlDsa.X86_64.Verify.sepB bs c 1024 (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048 &&
    VG.Proof.MlDsa.X86_64.Verify.inB bs ct len && VG.Proof.MlDsa.X86_64.Verify.inB bs c 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048 && VG.Proof.MlDsa.X86_64.Verify.inB wbs c 1024 && VG.Proof.MlDsa.X86_64.Verify.inB wbs (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS) 2048

abbrev ballArgs (ct : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len tau : Nat) (c : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr ct), (.rsi, .imm len), (.rdx, .imm tau), (.rcx, .ptr c), (.r8, .ptr (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS))]

theorem ball_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {ct c : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len tau : Nat}
    (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.X86_64.Verify.ballChk bs wbs ct len c = true) :
    ∀ x ∈ VG.Proof.MlDsa.X86_64.Verify.ballArgs ct len tau c, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.ballChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c4, by decide⟩, ⟨show len < 2 ^ 31 by omega, by decide⟩, ⟨show tau < 2 ^ 31 by omega, by decide⟩,
    ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c5, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c6, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {ct c : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len tau : Nat}
  (hp : (len, tau) ∈ ballParams) (hc : VG.Proof.MlDsa.X86_64.Verify.ballChk (rbs ++ wbs) wbs ct len c = true)
include L hc

omit hp in
theorem ball_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s ct, len⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s c, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 2048⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s c, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 2048⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.ballChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, c7⟩, c8⟩ := hc
  exact ⟨Covers.append_left (L.cR c4) (Covers.right (Covers.cons (L.cW c7) (L.cW c8))), Covers.cons (L.cW c7) (L.cW c8)⟩

include hp in
theorem ball_pre {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.ballArgs ct len tau c) s s1) :
    (sampleInBallContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s ct, len⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s c, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS), 2048⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.ballChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc
  have hl : len < 2 ^ 31 ∧ tau < 2 ^ 31 := by
    simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp; omega
  sig_pre [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.rsp]
  simp only [Arg.val]
  rw [VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega), VG.Proof.MlDsa.X86_64.Verify.imm32 (show tau < 2 ^ 32 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.disj c2, L.disj c3, L.ret8 c4, L.ret8 c5, L.ret8 c6,
    L.stk16 c4, L.stk16 c5, L.stk16 c6, L.nwp c4, L.nwp c5, L.nwp c6, hp⟩

end

theorem ballAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.ball (sampleInBallContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {ct c : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len tau : Nat} (hp : (len, tau) ∈ ballParams)
    (hc : VG.Proof.MlDsa.X86_64.Verify.ballChk (rbs ++ wbs) wbs ct len c = true) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.ballAt P ct len tau c) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(c, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 2048)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (VG.Proof.MlDsa.X86_64.Verify.res s' = 1 → Reduced s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s c)) ∧
      Outcome (fun b => (VG.Spec.MlDsa.sampleInBall tau b.ball (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s ct) len)).map toRq) (VG.Proof.MlDsa.X86_64.Verify.res s')
        (polyAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s c)) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.ball_args L.ok hp hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.ball_pre L hp hc h1) (VG.Proof.MlDsa.X86_64.Verify.ball_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.ball_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.ballChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, c4⟩, _⟩, _⟩, _⟩, _⟩ := hc'
  have hl : len < 2 ^ 31 ∧ tau < 2 ^ 31 := by
    simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp; omega
  sig_post [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val] at hq
  rw [VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega), VG.Proof.MlDsa.X86_64.Verify.imm32 (show tau < 2 ^ 32 by omega), L.wbytesAt c4] at hq
  exact hq

theorem ballAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.ball (sampleInBallContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {ct c : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len tau : Nat} (hp : (len, tau) ∈ ballParams)
    (hc : VG.Proof.MlDsa.X86_64.Verify.ballChk (rbs ++ wbs) wbs ct len c = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y ∧
      bytesAt x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x ct) len = bytesAt y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y ct) len) :
    RelCT isa Q (VG.Impl.MlDsa.X86_64.Verify.ballAt P ct len tau c) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.ball_args hS hp hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hq h1 h2
  obtain ⟨Lx, Ly, e, eb⟩ := hQ x y hq
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.ball_pre Lx hp hc h1, VG.Proof.MlDsa.X86_64.Verify.ball_pre Ly hp hc h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.ball_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.ball_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.ball_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.ball_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.ballChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨_, c4⟩, c5⟩, c6⟩, _⟩, _⟩ := hc'
  have hl : len < 2 ^ 31 := by
    simp only [ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp; omega
  sig_pub [sampleInBallContract, sampleInBallSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h1.1.2, h2.1.2, h1.rsp, h2.rsp]
  simp only [Arg.val]
  rw [VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega), Lx.wbytesAt c4, Ly.wbytesAt c4, eb]
  exact ⟨by rw [e.2], rfl, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c4), trivial, trivial, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c5), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c6)⟩

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CallPack`. -/
section

/-!
# ML-DSA verification on x86-64: calls of the rounding and encoding primitives

The calls of `vg_mldsa_use_hint`, `vg_mldsa_simple_bit_pack`,
`vg_mldsa_bit_unpack`, `vg_mldsa_unpack_t1`, `vg_mldsa_hint_bit_unpack` and
`vg_mldsa_norm_lt`: what they need of the layout (`…Chk`), what they do
(`…_ok`), and that two runs whose layout registers agree (and, for
`vg_mldsa_hint_bit_unpack`, the encoded hint) leak the same (`…_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem gamma2s_lt {g : Nat} (h : g ∈ gamma2s) : g < 2 ^ 31 := by
  simp only [gamma2s, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide

/-! ## `UseHint` -/

def uhChk (bs wbs : List (Reg × Nat)) (h r out : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs h 1024 out 1024 && VG.Proof.MlDsa.X86_64.Verify.sepB bs r 1024 out 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs h 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs r 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs out 1024 &&
    VG.Proof.MlDsa.X86_64.Verify.inB wbs out 1024

abbrev uhArgs (h r : VG.Impl.MlDsa.X86_64.Verify.Ptr) (g2 : Nat) (out : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr h), (.rsi, .ptr r), (.rdx, .imm g2), (.rcx, .ptr out)]

theorem uh_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {h r out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {g2 : Nat} (hg : g2 ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Verify.uhChk bs wbs h r out = true) : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.uhArgs h r g2 out, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.uhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c3, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c4, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.gamma2s_lt hg, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c5, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {h r out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {g2 : Nat}
  (hc : VG.Proof.MlDsa.X86_64.Verify.uhChk (rbs ++ wbs) wbs h r out = true)
include L hc

theorem uh_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s r, 1024⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s out, 1024⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s out, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.uhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  exact ⟨Covers.append_left (Covers.cons (L.cR c3) (L.cR c4)) (L.cR c5), L.cW c6⟩

theorem uh_pre (hg : g2 ∈ gamma2s) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s r)) {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.uhArgs h r g2 out) s s1) :
    (useHintContract X86_64.abi 16).pre
      (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, 1024⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.pa s r, 1024⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s out, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.uhChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  sig_pre [useHintContract, useHintSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.rsp, h1.1.2]
  simp only [Arg.val]
  rw [VG.Proof.MlDsa.X86_64.Verify.imm32 (show g2 < 2 ^ 32 by have := VG.Proof.MlDsa.X86_64.Verify.gamma2s_lt hg; omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.disj c2, L.ret8 c3, L.ret8 c4,
    L.ret8 c5, L.stk16 c3, L.stk16 c4, L.stk16 c5, L.nwp c3, L.nwp c4, L.nwp c5, hg, L.wreduced c4 _ hr⟩

end

theorem useHintAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.useHint (useHintContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {h r out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {g2 : Nat} (hg : g2 ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Verify.uhChk (rbs ++ wbs) wbs h r out = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s r)) :
    WP isa (useHintAt P h r g2 out) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(out, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      NatPolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s out) (Vector.zipWith (fun hj rj => (VG.Spec.MlDsa.useHint g2 hj rj).toNat)
        ((hintAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s h) 1).headD (Vector.replicate n false)) (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s r))) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.uh_args L.ok hg hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.uh_pre L hc hg hr h1) (VG.Proof.MlDsa.X86_64.Verify.uh_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.uh_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.uhChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, _⟩, _⟩ := hc'
  sig_post [useHintContract, useHintSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [VG.Proof.MlDsa.X86_64.Verify.imm32 (show g2 < 2 ^ 32 by have := VG.Proof.MlDsa.X86_64.Verify.gamma2s_lt hg; omega), L.whintAt c3, L.wpolyAt c4] at hq
  exact hq

theorem useHintAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.useHint (useHintContract X86_64.abi 16)) {rbs wbs : List (Reg × Nat)}
    (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {h r out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {g2 : Nat} (hg : g2 ∈ gamma2s)
    (hc : VG.Proof.MlDsa.X86_64.Verify.uhChk (rbs ++ wbs) wbs h r out = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x r) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y r) ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (useHintAt P h r g2 out) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.uh_args hS hg hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.uh_pre Lx hc hg rx h1, VG.Proof.MlDsa.X86_64.Verify.uh_pre Ly hc hg ry h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.uh_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.uh_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.uh_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.uh_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.uhChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨_, c3⟩, c4⟩, c5⟩, _⟩ := hc'
  sig_pub [useHintContract, useHintSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h2.r0, h2.r1, h2.r2, h2.r3, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c4), by first | rfl | trivial, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c5)⟩

/-! ## `SimpleBitPack` -/

def sbpChk (bs wbs : List (Reg × Nat)) (f out : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs f 1024 out len && VG.Proof.MlDsa.X86_64.Verify.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs out len && VG.Proof.MlDsa.X86_64.Verify.inB wbs out len

abbrev sbpArgs (f : VG.Impl.MlDsa.X86_64.Verify.Ptr) (b : Nat) (out : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr f), (.rsi, .imm b), (.rdx, .ptr out), (.rcx, .imm len)]

theorem sbp_small {b len : Nat} (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) :
    b < 2 ^ 31 ∧ len < 2 ^ 31 := by
  simp only [simpleBitPackBounds, List.mem_cons, List.not_mem_nil, or_false] at hb
  subst hl
  rcases hb with rfl | rfl | rfl <;> decide

theorem sbp_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {f out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.X86_64.Verify.sbpChk bs wbs f out len = true) :
    ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.sbpArgs f b out len, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.sbpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  have := VG.Proof.MlDsa.X86_64.Verify.sbp_small hb hl
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c2, by decide⟩, ⟨this.1, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c3, by decide⟩, ⟨this.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {b len : Nat}
  (hc : VG.Proof.MlDsa.X86_64.Verify.sbpChk (rbs ++ wbs) wbs f out len = true)
include L hc

theorem sbp_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s out, len⟩]) (s.rd ++ s.wr) ∧ Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s out, len⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.sbpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem sbp_pre (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b)
    (hf : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f) i).toNat ≤ b) {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.sbpArgs f b out len) s s1) :
    (simpleBitPackContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s out, len⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.sbpChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have hs := VG.Proof.MlDsa.X86_64.Verify.sbp_small hb hl
  sig_pre [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.rsp, h1.1.2]
  simp only [Arg.val]
  rw [VG.Proof.MlDsa.X86_64.Verify.imm32 (show b < 2 ^ 32 by omega), VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2,
    L.stk16 c3, L.nwp c2, L.nwp c3, hb, hl, fun i hi => by rw [L.wcoeffAt c2 _ hi]; exact hf i hi⟩

end

theorem sbpAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.simpleBitPack (simpleBitPackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.X86_64.Verify.sbpChk (rbs ++ wbs) wbs f out len = true)
    (hf : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f) i).toNat ≤ b) :
    WP isa (sbpAt P f b out len) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(out, len)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      bytesAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s out) len = VG.Spec.MlDsa.simpleBitPack (natPolyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) b := by
  have hs := VG.Proof.MlDsa.X86_64.Verify.sbp_small hb hl
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.sbp_args L.ok hb hl hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.sbp_pre L hc hb hl hf h1) (VG.Proof.MlDsa.X86_64.Verify.sbp_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.sbp_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.sbpChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [VG.Proof.MlDsa.X86_64.Verify.imm32 (show b < 2 ^ 32 by omega), VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega), L.wnatPolyAt c2] at hq
  exact hq

theorem sbpAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.simpleBitPack (simpleBitPackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {f out : VG.Impl.MlDsa.X86_64.Verify.Ptr} {b len : Nat}
    (hb : b ∈ simpleBitPackBounds) (hl : len = 32 * bitlen b) (hc : VG.Proof.MlDsa.X86_64.Verify.sbpChk (rbs ++ wbs) wbs f out len = true)
    {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ (∀ i < n, (coeffAt x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x f) i).toNat ≤ b) ∧
      (∀ i < n, (coeffAt y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y f) i).toNat ≤ b) ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (sbpAt P f b out len) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.sbp_args hS hb hl hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.sbp_pre Lx hc hb hl rx h1, VG.Proof.MlDsa.X86_64.Verify.sbp_pre Ly hc hb hl ry h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.sbp_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.sbp_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.sbp_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.sbp_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.sbpChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [simpleBitPackContract, simpleBitPackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h2.r0, h2.r1, h2.r2, h2.r3, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c2), by first | rfl | trivial, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3), by first | rfl | trivial⟩

/-! ## `BitUnpack` -/

def buChk (bs wbs : List (Reg × Nat)) (v : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) (f : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs v len f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs v len && VG.Proof.MlDsa.X86_64.Verify.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB wbs f 1024

abbrev buArgs (v : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len a b : Nat) (f : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr v), (.rsi, .imm len), (.rdx, .imm a), (.rcx, .imm b), (.r8, .ptr f)]

theorem bu_small {a b len : Nat} (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) :
    a < 2 ^ 31 ∧ b < 2 ^ 31 ∧ len < 2 ^ 31 := by
  simp only [bitPackParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab
  subst hl
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem bu_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len a b : Nat}
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Verify.buChk bs wbs v len f = true) :
    ∀ x ∈ VG.Proof.MlDsa.X86_64.Verify.buArgs v len a b f, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.buChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  have := VG.Proof.MlDsa.X86_64.Verify.bu_small hab hl
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c2, by decide⟩, ⟨this.2.2, by decide⟩, ⟨this.1, by decide⟩, ⟨this.2.1, by decide⟩,
    ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c3, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len a b : Nat}
  (hc : VG.Proof.MlDsa.X86_64.Verify.buChk (rbs ++ wbs) wbs v len f = true)
include L hc

theorem bu_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s v, len⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.buChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem bu_pre (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) {s1 : State}
    (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.buArgs v len a b f) s s1) :
    (bitUnpackContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s v, len⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.buChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have hs := VG.Proof.MlDsa.X86_64.Verify.bu_small hab hl
  sig_pre [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.rsp]
  simp only [Arg.val]
  rw [VG.Proof.MlDsa.X86_64.Verify.imm32 (show a < 2 ^ 32 by omega), VG.Proof.MlDsa.X86_64.Verify.imm32 (show b < 2 ^ 32 by omega), VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2,
    L.stk16 c3, L.nwp c2, L.nwp c3, hab, hl⟩

end

theorem bitUnpackAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.bitUnpack (bitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len a b : Nat}
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Verify.buChk (rbs ++ wbs) wbs v len f = true) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.bitUnpackAt P v len a b f) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(f, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f) (toRq (VG.Spec.MlDsa.bitUnpack (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s v) len) a b)) := by
  have hs := VG.Proof.MlDsa.X86_64.Verify.bu_small hab hl
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.bu_args L.ok hab hl hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.bu_pre L hc hab hl h1) (VG.Proof.MlDsa.X86_64.Verify.bu_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.bu_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.buChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [VG.Proof.MlDsa.X86_64.Verify.imm32 (show a < 2 ^ 32 by omega), VG.Proof.MlDsa.X86_64.Verify.imm32 (show b < 2 ^ 32 by omega), VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega),
    L.wbytesAt c2] at hq
  exact hq

theorem bitUnpackAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.bitUnpack (bitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len a b : Nat}
    (hab : (a, b) ∈ bitPackParams) (hl : len = 32 * bitlen (a + b)) (hc : VG.Proof.MlDsa.X86_64.Verify.buChk (rbs ++ wbs) wbs v len f = true)
    {Q : State → State → Prop} (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (VG.Impl.MlDsa.X86_64.Verify.bitUnpackAt P v len a b f) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.bu_args hS hab hl hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.bu_pre Lx hc hab hl h1, VG.Proof.MlDsa.X86_64.Verify.bu_pre Ly hc hab hl h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.bu_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.bu_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.bu_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.bu_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.buChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [bitUnpackContract, bitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c2), by first | rfl | trivial, by first | rfl | trivial,
    by first | rfl | trivial, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3)⟩

/-! ## `t₁ · 2ᵈ` -/

def t1Chk (bs wbs : List (Reg × Nat)) (v f : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs v 320 f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB bs v 320 && VG.Proof.MlDsa.X86_64.Verify.inB bs f 1024 && VG.Proof.MlDsa.X86_64.Verify.inB wbs f 1024

abbrev t1Args (v f : VG.Impl.MlDsa.X86_64.Verify.Ptr) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr v), (.rsi, .ptr f)]

theorem t1_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.t1Chk bs wbs v f = true) :
    ∀ x ∈ VG.Proof.MlDsa.X86_64.Verify.t1Args v f, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.t1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c2, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c3, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr}
  (hc : VG.Proof.MlDsa.X86_64.Verify.t1Chk (rbs ++ wbs) wbs v f = true)
include L hc

theorem t1_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s v, 320⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩]) (s.rd ++ s.wr) ∧ Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.t1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem t1_pre {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.t1Args v f) s s1) :
    (unpackT1Contract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s v, 320⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.t1Chk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  sig_pre [unpackT1Contract, unpackT1Sig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.rsp]
  exact ⟨L.sp16, rfl, rfl, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2, L.stk16 c3, L.nwp c2, L.nwp c3⟩

end

theorem unpackT1At_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.unpackT1 (unpackT1Contract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.t1Chk (rbs ++ wbs) wbs v f = true) :
    WP isa (unpackT1At P v f) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(f, 1024)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      PolyIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f) ((simpleBitUnpack (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s v) 320) t1Max).map
        fun c => ofInt (c * 2 ^ d : Nat)) := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.t1_args L.ok hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.t1_pre L hc h1) (VG.Proof.MlDsa.X86_64.Verify.t1_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.t1_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, _, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.t1Chk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [unpackT1Contract, unpackT1Sig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, hm, h1.rsp, h1.1.2] at hq
  simp only [Arg.val] at hq
  rw [L.wbytesAt c2] at hq
  exact hq

theorem unpackT1At_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.unpackT1 (unpackT1Contract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {v f : VG.Impl.MlDsa.X86_64.Verify.Ptr} (hc : VG.Proof.MlDsa.X86_64.Verify.t1Chk (rbs ++ wbs) wbs v f = true)
    {Q : State → State → Prop} (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (unpackT1At P v f) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.t1_args hS hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.t1_pre Lx hc h1, VG.Proof.MlDsa.X86_64.Verify.t1_pre Ly hc h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.t1_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.t1_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.t1_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.t1_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.t1Chk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [unpackT1Contract, unpackT1Sig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h2.r0, h2.r1, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c2), e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3)⟩

/-! ## `HintBitUnpack` -/

def huChk (bs wbs : List (Reg × Nat)) (y : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len : Nat) (h : VG.Impl.MlDsa.X86_64.Verify.Ptr) (hlen : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB bs y len h (hlen * 4) && VG.Proof.MlDsa.X86_64.Verify.inB bs y len && VG.Proof.MlDsa.X86_64.Verify.inB bs h (hlen * 4) && VG.Proof.MlDsa.X86_64.Verify.inB wbs h (hlen * 4)

abbrev huArgs (y : VG.Impl.MlDsa.X86_64.Verify.Ptr) (len omega : Nat) (h : VG.Impl.MlDsa.X86_64.Verify.Ptr) (hlen : Nat) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) :=
  [(.rdi, .ptr y), (.rsi, .imm len), (.rdx, .imm omega), (.rcx, .ptr h), (.r8, .imm hlen)]

/-- The arguments of `vg_mldsa_hint_bit_unpack` for the parameters `(ω, k)`. -/
def HuPar (len omega hlen : Nat) : Prop :=
  (omega, len - omega) ∈ hintParams ∧ omega ≤ len ∧ hlen = 256 * (len - omega)

instance (len omega hlen : Nat) : Decidable (VG.Proof.MlDsa.X86_64.Verify.HuPar len omega hlen) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem hu_small {len omega hlen : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.HuPar len omega hlen) :
    len < 2 ^ 31 ∧ omega < 2 ^ 31 ∧ hlen < 2 ^ 31 := by
  obtain ⟨hp, hl, hh⟩ := h
  simp only [hintParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
  omega

theorem hu_args {bs wbs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {y h : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len omega hlen : Nat}
    (hp : VG.Proof.MlDsa.X86_64.Verify.HuPar len omega hlen) (hc : VG.Proof.MlDsa.X86_64.Verify.huChk bs wbs y len h hlen = true) :
    ∀ x ∈ VG.Proof.MlDsa.X86_64.Verify.huArgs y len omega h hlen, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.huChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc
  have := VG.Proof.MlDsa.X86_64.Verify.hu_small hp
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c2, by decide⟩, ⟨this.1, by decide⟩, ⟨this.2.1, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L c3, by decide⟩,
    ⟨this.2.2, by decide⟩⟩

section
variable {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {y h : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len omega hlen : Nat}
  (hc : VG.Proof.MlDsa.X86_64.Verify.huChk (rbs ++ wbs) wbs y len h hlen = true)
include L hc

theorem hu_cov : Covers ([⟨VG.Proof.MlDsa.X86_64.Verify.pa s y, len⟩] ++ [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, hlen * 4⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, hlen * 4⟩] s.wr := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.huChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨_, c2⟩, c3⟩, c4⟩ := hc
  exact ⟨Covers.append_left (L.cR c2) (L.cR c3), L.cW c4⟩

theorem hu_pre (hp : VG.Proof.MlDsa.X86_64.Verify.HuPar len omega hlen) {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.huArgs y len omega h hlen) s s1) :
    (hintBitUnpackContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s y, len⟩] [⟨VG.Proof.MlDsa.X86_64.Verify.pa s h, hlen * 4⟩]) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.huChk, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, _⟩ := hc
  have hs := VG.Proof.MlDsa.X86_64.Verify.hu_small hp
  sig_pre [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h1.rsp]
  simp only [Arg.val]
  rw [VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega), VG.Proof.MlDsa.X86_64.Verify.imm32 (show omega < 2 ^ 32 by omega), VG.Proof.MlDsa.X86_64.Verify.imm64 (show hlen < 2 ^ 64 by omega)]
  exact ⟨L.sp16, by first | rfl | trivial, by first | rfl | trivial, L.disj c1, L.ret8 c2, L.ret8 c3, L.stk16 c2,
    L.stk16 c3, L.nwp c2, L.nwp c3, hp.1, hp.2.1, hp.2.2⟩

end

theorem hintUnpackAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.hintUnpack (hintBitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {y h : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len omega hlen : Nat}
    (hp : VG.Proof.MlDsa.X86_64.Verify.HuPar len omega hlen) (hc : VG.Proof.MlDsa.X86_64.Verify.huChk (rbs ++ wbs) wbs y len h hlen = true) :
    WP isa (hintUnpackAt P y len omega h hlen) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(h, hlen * 4)] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      match VG.Spec.MlDsa.hintBitUnpack omega (len - omega) (bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s y) len) with
      | some hint => VG.Proof.MlDsa.X86_64.Verify.res s' = 1 ∧ HintIs s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s h) (len - omega) hint
      | none => VG.Proof.MlDsa.X86_64.Verify.res s' = 0 := by
  have hs := VG.Proof.MlDsa.X86_64.Verify.hu_small hp
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.hu_args L.ok hp hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.hu_pre L hc hp h1) (VG.Proof.MlDsa.X86_64.Verify.hu_cov L hc).1 (VG.Proof.MlDsa.X86_64.Verify.hu_cov L hc).2)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.huChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, _⟩, _⟩ := hc'
  sig_post [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.r2, h1.r3, hm, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val] at hq
  rw [VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega), VG.Proof.MlDsa.X86_64.Verify.imm32 (show omega < 2 ^ 32 by omega), L.wbytesAt c2] at hq
  exact hq

theorem hintUnpackAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.hintUnpack (hintBitUnpackContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {y h : VG.Impl.MlDsa.X86_64.Verify.Ptr} {len omega hlen : Nat}
    (hp : VG.Proof.MlDsa.X86_64.Verify.HuPar len omega hlen) (hc : VG.Proof.MlDsa.X86_64.Verify.huChk (rbs ++ wbs) wbs y len h hlen = true)
    {Q : State → State → Prop} (hQ : ∀ x x', Q x x' → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x' ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x x' ∧
      bytesAt x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x y) len = bytesAt x'.mem (VG.Proof.MlDsa.X86_64.Verify.pa x' y) len) :
    RelCT isa Q (hintUnpackAt P y len omega h hlen) fun _ _ => True := by
  have hs := VG.Proof.MlDsa.X86_64.Verify.hu_small hp
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.hu_args hS hp hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x x' x1 y1 hq h1 h2
  obtain ⟨Lx, Ly, e, eb⟩ := hQ x x' hq
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.hu_pre Lx hc hp h1, VG.Proof.MlDsa.X86_64.Verify.hu_pre Ly hc hp h2, ?_, (VG.Proof.MlDsa.X86_64.Verify.hu_cov Lx hc).1, (VG.Proof.MlDsa.X86_64.Verify.hu_cov Lx hc).2,
    (VG.Proof.MlDsa.X86_64.Verify.hu_cov Ly hc).1, (VG.Proof.MlDsa.X86_64.Verify.hu_cov Ly hc).2, e.2⟩
  have hc' := hc
  simp only [VG.Proof.MlDsa.X86_64.Verify.huChk, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨_, c2⟩, c3⟩, _⟩ := hc'
  sig_pub [hintBitUnpackContract, hintBitUnpackSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h1.r2, h1.r3, h1.r4, h2.r0, h2.r1, h2.r2, h2.r3, h2.r4, h1.1.2, h2.1.2, h1.rsp, h2.rsp]
  simp only [Arg.val]
  rw [VG.Proof.MlDsa.X86_64.Verify.imm64 (show len < 2 ^ 64 by omega), Lx.wbytesAt c2, Ly.wbytesAt c2, eb]
  exact ⟨by rw [e.2], rfl, e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c2), by first | rfl | trivial, by first | rfl | trivial,
    e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS c3), by first | rfl | trivial⟩

/-! ## The norm -/

def nlChk (bs : List (Reg × Nat)) (f : VG.Impl.MlDsa.X86_64.Verify.Ptr) : Bool := VG.Proof.MlDsa.X86_64.Verify.inB bs f 1024

abbrev nlArgs (f : VG.Impl.MlDsa.X86_64.Verify.Ptr) (bound : Nat) : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg) := [(.rdi, .ptr f), (.rsi, .imm bound)]

theorem nl_args {bs : List (Reg × Nat)} (L : VG.Proof.MlDsa.X86_64.Verify.LayOk bs) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {bound : Nat} (hb : bound < 2 ^ 31)
    (hc : VG.Proof.MlDsa.X86_64.Verify.nlChk bs f = true) : ∀ x ∈ VG.Proof.MlDsa.X86_64.Verify.nlArgs f bound, x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok L hc, by decide⟩, ⟨hb, by decide⟩⟩

theorem nl_pre {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {bound : Nat}
    (hc : VG.Proof.MlDsa.X86_64.Verify.nlChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) {s1 : State} (h1 : VG.Proof.MlDsa.X86_64.Verify.Args (VG.Proof.MlDsa.X86_64.Verify.nlArgs f bound) s s1) :
    (normLtContract X86_64.abi 16).pre (s1.callEntry.withRegions [⟨VG.Proof.MlDsa.X86_64.Verify.pa s f, 1024⟩] []) := by
  sig_pre [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.rsp, h1.1.2]
  exact ⟨L.sp16, rfl, L.ret8 hc, L.stk16 hc, L.nwp hc, L.wreduced hc _ hr⟩

theorem normLtAt_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.normLt (normLtContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {bound : Nat} (hb : bound < 2 ^ 31)
    (hc : VG.Proof.MlDsa.X86_64.Verify.nlChk (rbs ++ wbs) f = true) (hr : Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)) :
    WP isa (normLtAt P f bound) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [] ∧ s'.gpr .r15 = s.gpr .r15 ∧
      VG.Proof.MlDsa.X86_64.Verify.res s' = if normRq [polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s f)] < bound then 1 else 0 := by
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.callAt_ok C.correct C.nosp C.depth (VG.Proof.MlDsa.X86_64.Verify.nl_args L.ok hb hc)
    (by simp only [List.map_cons, List.map_nil]; decide)
    (fun s1 h1 => VG.Proof.MlDsa.X86_64.Verify.nl_pre L hc hr h1) (Covers.append_left (L.cR hc) Covers.nil) Covers.nil)
    fun s' ⟨hP, s1, h1, s₂, hm, hg, hq⟩ => ⟨hP.b, hP.cs .r15 (by decide), ?_⟩
  sig_post [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs] at hq
  rw [h1.r0, h1.r1, h1.rsp, h1.1.2, hg _ (by decide)] at hq
  simp only [Arg.val, VG.Proof.MlDsa.X86_64.Verify.imm32 (show bound < 2 ^ 32 by omega), L.wpolyAt hc] at hq
  exact hq

theorem normLtAt_tr {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.normLt (normLtContract X86_64.abi 16))
    {rbs wbs : List (Reg × Nat)} (hS : VG.Proof.MlDsa.X86_64.Verify.LayOk (rbs ++ wbs)) {f : VG.Impl.MlDsa.X86_64.Verify.Ptr} {bound : Nat} (hb : bound < 2 ^ 31)
    (hc : VG.Proof.MlDsa.X86_64.Verify.nlChk (rbs ++ wbs) f = true) {Q : State → State → Prop}
    (hQ : ∀ x y, Q x y → VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs x ∧ VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs y ∧ Reduced x.mem (VG.Proof.MlDsa.X86_64.Verify.pa x f) ∧ Reduced y.mem (VG.Proof.MlDsa.X86_64.Verify.pa y f) ∧ VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa Q (normLtAt P f bound) fun _ _ => True := by
  refine VG.Proof.MlDsa.X86_64.Verify.callAt_tr C.correct C.ct (VG.Proof.MlDsa.X86_64.Verify.nl_args hS hb hc) (by simp only [List.map_cons, List.map_nil]; decide) ?_
  intro x y x1 y1 hp h1 h2
  obtain ⟨Lx, Ly, rx, ry, e⟩ := hQ x y hp
  refine ⟨_, _, _, _, VG.Proof.MlDsa.X86_64.Verify.nl_pre Lx hc rx h1, VG.Proof.MlDsa.X86_64.Verify.nl_pre Ly hc ry h2, ?_, Covers.append_left (Lx.cR hc) Covers.nil, Covers.nil,
    Covers.append_left (Ly.cR hc) Covers.nil, Covers.nil, e.2⟩
  sig_pub [normLtContract, normLtSig, X86_64.abi, VG.X86_64.argRegs]
  rw [h1.r0, h1.r1, h2.r0, h2.r1, h1.rsp, h2.rsp]
  simp only [Arg.val]
  exact ⟨by rw [e.2], e.pa (VG.Proof.MlDsa.X86_64.Verify.ptr_bs hS hc), by first | rfl | trivial⟩

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Flag`. -/
section

/-!
# ML-DSA verification on x86-64: the result in `r15`, and the samplers

The result so far is kept in `r15` as 1 or 0 (`flag`); `and15` and `mov32 r15,
eax` update it from a callee's result. A sampler's call, its result ANDed into
`r15` and its output masked with it (`sampled`) leaves a reduced polynomial
either way, the sampled one if the sampler succeeded (`sampled_ok`, and
`sampled4_ok` for four polynomials).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- 1 if `p`, 0 otherwise. -/
def flag (p : Prop) [Decidable p] : BitVec 64 := if p then 1 else 0

theorem flag_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) : VG.Proof.MlDsa.X86_64.Verify.flag p = VG.Proof.MlDsa.X86_64.Verify.flag q := by
  unfold VG.Proof.MlDsa.X86_64.Verify.flag; by_cases hp : p
  · rw [VG.Proof.MlKem.X86_64.ifp hp, VG.Proof.MlKem.X86_64.ifp (h.mp hp)]
  · rw [VG.Proof.MlKem.X86_64.ifn hp, VG.Proof.MlKem.X86_64.ifn (fun hq => hp (h.mpr hq))]

theorem and15_ok (s : State) :
    WP isa (.block and15) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&& (s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧
        Keep [.r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold and15
  xrun

theorem mov15_ok (s : State) :
    WP isa (.block [.mov32 .r15 (.reg .rax)]) s fun s' =>
      (s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .rax).setWidth 32) ∧ s'.mem = s.mem) ∧ Keep [.r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  xrun

/-- `r15 ∧ eax` of a flag and a result 0 or 1. -/
theorem and_flag {p : Prop} [Decidable p] {r : BitVec 32} (hr : r = 1 ∨ r = 0) :
    BitVec.setWidth 64 ((VG.Proof.MlDsa.X86_64.Verify.flag p).setWidth 32 &&& r) = VG.Proof.MlDsa.X86_64.Verify.flag (p ∧ r = 1) := by
  unfold VG.Proof.MlDsa.X86_64.Verify.flag
  rcases hr with rfl | rfl <;> by_cases hp : p <;> simp [hp]

theorem mov_flag {r : BitVec 32} (hr : r = 1 ∨ r = 0) : BitVec.setWidth 64 r = VG.Proof.MlDsa.X86_64.Verify.flag (r = 1) := by
  unfold VG.Proof.MlDsa.X86_64.Verify.flag
  rcases hr with rfl | rfl <;> simp

/-! ## The mask -/

theorem mask_one {m : Mem} {p : Addr} (x : BitVec 32) (h : x = 1) :
    ∀ i < n, coeffAt m p i &&& (0 - x) = coeffAt m p i := by
  intro i _; subst h
  rw [show (0 : BitVec 32) - 1 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

theorem mask_zero {m : Mem} {p : Addr} (x : BitVec 32) (h : x = 0) :
    ∀ i < n, coeffAt m p i &&& (0 - x) = 0 := by
  intro i _; subst h; simp

theorem polyAt_eq_of_coeffAt {m m' : Mem} {p : Addr} (h : ∀ i < n, coeffAt m' p i = coeffAt m p i) :
    polyAt m' p = polyAt m p := by
  apply Vector.ext
  intro i hi
  simp only [polyAt, Vector.getElem_ofFn, h i hi]

theorem reduced_of_coeffAt {m m' : Mem} {p : Addr} (h : ∀ i < n, coeffAt m' p i = coeffAt m p i) (hr : Reduced m p) :
    Reduced m' p := fun i hi => by rw [h i hi]; exact hr i hi


/-- A sampler's call, its result ANDed into `r15`, and its output masked. -/
theorem sampled_ok {call : Prog isa} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr}
    (hi : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) a 1024 = true) (hw : VG.Proof.MlDsa.X86_64.Verify.inB wbs a 1024 = true) {p : Prop} [Decidable p]
    (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag p) {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (haw : (a, 1024) ∈ ws)
    {F : Bounds → Option Poly}
    (hcall : WP isa call s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (VG.Proof.MlDsa.X86_64.Verify.res s' = 1 → Reduced s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a)) ∧ Outcome F (VG.Proof.MlDsa.X86_64.Verify.res s') (polyAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a))) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.sampled call a) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws ∧ Reduced s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) ∧
      ∃ r : BitVec 32, (r = 1 ∨ r = 0) ∧ s'.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (p ∧ r = 1) ∧
        (r = 1 → ∃ b, F b = some (polyAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a))) ∧ (r = 0 → F minBounds = none) := by
  unfold VG.Impl.MlDsa.X86_64.Verify.sampled
  refine WP.seq (WP.mono hcall fun s₁ ⟨hP₁, h15₁, hr₁, ho₁⟩ => ?_)
  have L₁ := L.post hP₁
  have hab := VG.Proof.MlDsa.X86_64.Verify.ptr_bs L.ok hi
  have e₁ : VG.Proof.MlDsa.X86_64.Verify.pa s₁ a = VG.Proof.MlDsa.X86_64.Verify.pa s a := hP₁.pa hab
  have hr : VG.Proof.MlDsa.X86_64.Verify.res s₁ = 1 ∨ VG.Proof.MlDsa.X86_64.Verify.res s₁ = 0 := by rcases ho₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact .inl h; exact .inr h]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.and15_ok s₁) fun s₂ ⟨⟨h15₂, hm₂⟩, k₂⟩ => ?_)
  have hP₂ : VG.Proof.MlDsa.X86_64.Verify.PPostB s₁ s₂ [] := VG.Proof.MlDsa.X86_64.Verify.postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  have L₂ := L₁.post hP₂
  have e₂ : VG.Proof.MlDsa.X86_64.Verify.pa s₂ a = VG.Proof.MlDsa.X86_64.Verify.pa s₁ a := hP₂.pa hab
  have hax : (s₂.gpr .rax).setWidth 32 = VG.Proof.MlDsa.X86_64.Verify.res s₁ := by rw [k₂.gpr (by decide)]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.mask_ok L₂ hi hw) fun s₃ ⟨hP₃, h15₃, hc₃⟩ => ?_
  have hsub : ∀ w ∈ [(a, 1024)], w ∈ ws := by simp only [List.mem_singleton, forall_eq]; exact haw
  have hcs : ∀ w ∈ [(a, 1024)], w.1.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases := by simp only [List.mem_singleton, forall_eq]; exact hab
  have hP₁₂ : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₂ ws := PPostB.trans hP₁ hP₂ (fun _ h => absurd h List.not_mem_nil) (fun w hw => hw)
    (fun _ h => absurd h List.not_mem_nil)
  have hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₃ ws := PPostB.trans hP₁₂ hP₃ hcs (fun w hw => hw) hsub
  rw [e₂, e₁, hax, hm₂] at hc₃
  refine ⟨hP, ?_, VG.Proof.MlDsa.X86_64.Verify.res s₁, hr, by rw [h15₃, h15₂, h15₁, h15, VG.Proof.MlDsa.X86_64.Verify.and_flag hr], fun h1 => ?_, fun h0 => ?_⟩
  · rcases hr with h1 | h0
    · exact VG.Proof.MlDsa.X86_64.Verify.reduced_of_coeffAt (fun i hi => by rw [hc₃ i hi, VG.Proof.MlDsa.X86_64.Verify.mask_one _ h1 i hi]) (hr₁ h1)
    · exact (Proof.MlDsa.Verify.polyIs_zero fun i hi => by rw [hc₃ i hi, VG.Proof.MlDsa.X86_64.Verify.mask_zero _ h0 i hi]).1
  · rcases ho₁ with ⟨_, b, hb⟩ | ⟨h0, _⟩
    · refine ⟨b, ?_⟩
      rw [hb, VG.Proof.MlDsa.X86_64.Verify.polyAt_eq_of_coeffAt fun i hi => by rw [hc₃ i hi, VG.Proof.MlDsa.X86_64.Verify.mask_one _ h1 i hi]]
    · rw [h1] at h0; cases h0
  · rcases ho₁ with ⟨h1, _⟩ | ⟨_, hn⟩
    · rw [h1] at h0; cases h0
    · exact hn

theorem coeffAt_poly4 (m : Mem) (p : Addr) (k j : Nat) : coeffAt m (VG.Spec.MlDsa.poly4 p k) j = coeffAt m p (256 * k + j) := by
  unfold coeffAt VG.Spec.MlDsa.poly4
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1024 * k + 4 * j = 4 * (256 * k + j) by omega]

/-- `sampled_ok` for a call that samples the four polynomials from `a`, each
from `F k`. -/
theorem sampled4_ok {call : Prog isa} {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a : VG.Impl.MlDsa.X86_64.Verify.Ptr}
    (hi : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) a 4096 = true) (hw : VG.Proof.MlDsa.X86_64.Verify.inB wbs a 4096 = true) {p : Prop} [Decidable p]
    (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag p) {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (haw : (a, 4096) ∈ ws)
    {F : Nat → Bounds → Option Poly}
    (hcall : WP isa call s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws ∧ s'.gpr .r15 = s.gpr .r15 ∧
      (VG.Proof.MlDsa.X86_64.Verify.res s' = 1 → ∀ k < 4, Reduced s'.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k)) ∧
      ((VG.Proof.MlDsa.X86_64.Verify.res s' = 1 ∧ ∀ k < 4, ∃ b, F k b = some (polyAt s'.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k))) ∨
        (VG.Proof.MlDsa.X86_64.Verify.res s' = 0 ∧ ∃ k < 4, F k minBounds = none))) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.sampled4 call a) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws ∧ (∀ k < 4, Reduced s'.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k)) ∧
      ∃ r : BitVec 32, (r = 1 ∨ r = 0) ∧ s'.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (p ∧ r = 1) ∧
        (r = 1 → ∀ k < 4, ∃ b, F k b = some (polyAt s'.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k))) ∧
        (r = 0 → ∃ k < 4, F k minBounds = none) := by
  unfold VG.Impl.MlDsa.X86_64.Verify.sampled4
  refine WP.seq (WP.mono hcall fun s₁ ⟨hP₁, h15₁, hr₁, ho₁⟩ => ?_)
  have L₁ := L.post hP₁
  have hab := VG.Proof.MlDsa.X86_64.Verify.ptr_bs L.ok hi
  have e₁ : VG.Proof.MlDsa.X86_64.Verify.pa s₁ a = VG.Proof.MlDsa.X86_64.Verify.pa s a := hP₁.pa hab
  have hr : VG.Proof.MlDsa.X86_64.Verify.res s₁ = 1 ∨ VG.Proof.MlDsa.X86_64.Verify.res s₁ = 0 := by rcases ho₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact .inl h; exact .inr h]
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.and15_ok s₁) fun s₂ ⟨⟨h15₂, hm₂⟩, k₂⟩ => ?_)
  have hP₂ : VG.Proof.MlDsa.X86_64.Verify.PPostB s₁ s₂ [] := VG.Proof.MlDsa.X86_64.Verify.postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  have L₂ := L₁.post hP₂
  have e₂ : VG.Proof.MlDsa.X86_64.Verify.pa s₂ a = VG.Proof.MlDsa.X86_64.Verify.pa s₁ a := hP₂.pa hab
  have hax : (s₂.gpr .rax).setWidth 32 = VG.Proof.MlDsa.X86_64.Verify.res s₁ := by rw [k₂.gpr (by decide)]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.maskN_ok L₂ (N := 1024) (by decide) (by decide) hi hw) fun s₃ ⟨hP₃, h15₃, hc₃⟩ => ?_
  have hsub : ∀ w ∈ [(a, 4 * 1024)], w ∈ ws := by simp only [List.mem_singleton, forall_eq]; exact haw
  have hcs : ∀ w ∈ [(a, 4 * 1024)], w.1.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases := by simp only [List.mem_singleton, forall_eq]; exact hab
  have hP₁₂ : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₂ ws := PPostB.trans hP₁ hP₂ (fun _ h => absurd h List.not_mem_nil) (fun w hw => hw)
    (fun _ h => absurd h List.not_mem_nil)
  have hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₃ ws := PPostB.trans hP₁₂ hP₃ hcs (fun w hw => hw) hsub
  rw [e₂, e₁, hax, hm₂] at hc₃
  have hc : ∀ k < 4, ∀ j < n, coeffAt s₃.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k) j =
      coeffAt s₁.mem (VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s a) k) j &&& (0 - VG.Proof.MlDsa.X86_64.Verify.res s₁) := fun k hk j hj => by
    rw [VG.Proof.MlDsa.X86_64.Verify.coeffAt_poly4, VG.Proof.MlDsa.X86_64.Verify.coeffAt_poly4, hc₃ _ (by simp only [n] at hj; omega)]
  refine ⟨hP, fun k hk => ?_, VG.Proof.MlDsa.X86_64.Verify.res s₁, hr, by rw [h15₃, h15₂, h15₁, h15, VG.Proof.MlDsa.X86_64.Verify.and_flag hr], fun h1 k hk => ?_,
    fun h0 => ?_⟩
  · rcases hr with h1 | h0
    · exact VG.Proof.MlDsa.X86_64.Verify.reduced_of_coeffAt (fun i hi => by rw [hc k hk i hi, VG.Proof.MlDsa.X86_64.Verify.mask_one _ h1 i hi]) (hr₁ h1 k hk)
    · exact (Proof.MlDsa.Verify.polyIs_zero fun i hi => by rw [hc k hk i hi, VG.Proof.MlDsa.X86_64.Verify.mask_zero _ h0 i hi]).1
  · rcases ho₁ with ⟨_, hb⟩ | ⟨h0, _⟩
    · obtain ⟨b, hb⟩ := hb k hk
      refine ⟨b, ?_⟩
      rw [hb, VG.Proof.MlDsa.X86_64.Verify.polyAt_eq_of_coeffAt fun i hi => by rw [hc k hk i hi, VG.Proof.MlDsa.X86_64.Verify.mask_one _ h1 i hi]]
    · rw [h1] at h0; cases h0
  · rcases ho₁ with ⟨h1, _⟩ | ⟨_, hn⟩
    · rw [h1] at h0; cases h0
    · exact hn

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top`. -/
section

/-!
# ML-DSA verification on x86-64: the contract, the layout and the invariant

The precondition of the shared contract `verifyContract p X86_64.abi 32`,
spelled out (`VPre`); the layout of the function's buffers (`pk`, `mu`, `sig`
read in `rbp`, `r12`, `r13`; `scratch` written, in `rbx`: `vR p`, `vW p`);
what holds throughout (`T`: the permissions and stack pointer of entry, the
pointers, the caller's callee-saved registers saved in `scratch`, the return
address and the inputs); the prologue and the epilogue.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The parameter sets. -/
def params : List Params := [mlDsa44, mlDsa65, mlDsa87]

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

/-- The precondition of `verifyContract p X86_64.abi 32`. -/
structure VPre (p : Params) (σ : State) : Prop where
  sp : 32 ≤ (σ.gpr .rsp).toNat
  rd : σ.rd = [⟨σ.gpr .rdi, p.pkLen⟩, ⟨σ.gpr .rsi, 64⟩, ⟨σ.gpr .rdx, p.sigLen⟩]
  wr : σ.wr = [⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩]
  d1 : Region.Disjoint ⟨σ.gpr .rdi, p.pkLen⟩ ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩
  d2 : Region.Disjoint ⟨σ.gpr .rsi, 64⟩ ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩
  d3 : Region.Disjoint ⟨σ.gpr .rdx, p.sigLen⟩ ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩
  r1 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdi, p.pkLen⟩
  r2 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rsi, 64⟩
  r3 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rdx, p.sigLen⟩
  r4 : Region.Disjoint ⟨σ.gpr .rsp, 8⟩ ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩
  k1 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rdi, p.pkLen⟩
  k2 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rsi, 64⟩
  k3 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rdx, p.sigLen⟩
  k4 : (below (σ.gpr .rsp) 32).Disjoint ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩
  n1 : (σ.gpr .rdi).toNat + p.pkLen ≤ 2 ^ 64
  n2 : (σ.gpr .rsi).toNat + 64 ≤ 2 ^ 64
  n3 : (σ.gpr .rdx).toNat + p.sigLen ≤ 2 ^ 64
  n4 : (σ.gpr .rcx).toNat + VG.Proof.MlDsa.X86_64.Verify.scrLen p ≤ 2 ^ 64

/-- The inputs of a run from `σ`. -/
abbrev vPk (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) p.pkLen
abbrev vMu (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rsi) 64
abbrev vSig (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdx) p.sigLen

/-- The contract the proof is written against. -/
def verifyK (p : Params) : Contract isa where
  pre := VG.Proof.MlDsa.X86_64.Verify.VPre p
  post σ s := let v := fun b => verifyMu p b (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (VG.Proof.MlDsa.X86_64.Verify.vMu σ) (VG.Proof.MlDsa.X86_64.Verify.vSig p σ)
    (VG.Proof.MlDsa.X86_64.Verify.res s = 1 ∧ ∃ b, v b = some true) ∨ (VG.Proof.MlDsa.X86_64.Verify.res s = 0 ∧ v minBounds ≠ some true)
  pub σ₁ σ₂ := σ₁.gpr .rdi = σ₂.gpr .rdi ∧ σ₁.gpr .rsi = σ₂.gpr .rsi ∧ σ₁.gpr .rdx = σ₂.gpr .rdx ∧
    σ₁.gpr .rcx = σ₂.gpr .rcx ∧ σ₁.gpr .rsp = σ₂.gpr .rsp ∧ VG.Proof.MlDsa.X86_64.Verify.vPk p σ₁ = VG.Proof.MlDsa.X86_64.Verify.vPk p σ₂ ∧ VG.Proof.MlDsa.X86_64.Verify.vMu σ₁ = VG.Proof.MlDsa.X86_64.Verify.vMu σ₂ ∧
    VG.Proof.MlDsa.X86_64.Verify.vSig p σ₁ = VG.Proof.MlDsa.X86_64.Verify.vSig p σ₂

/-! ## The layout -/

/-- `pk`, `mu` and `sig`. -/
abbrev vR (p : Params) : List (Reg × Nat) := [(.rbp, p.pkLen), (.r12, 64), (.r13, p.sigLen)]
/-- `scratch`. -/
abbrev vW (p : Params) : List (Reg × Nat) := [(.rbx, VG.Proof.MlDsa.X86_64.Verify.scrLen p)]
abbrev vB (p : Params) : List (Reg × Nat) := VG.Proof.MlDsa.X86_64.Verify.vR p ++ VG.Proof.MlDsa.X86_64.Verify.vW p

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .rbx

/-- What holds throughout a run from `σ`. -/
structure T (p : Params) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  rsp : s.gpr .rsp = σ.gpr .rsp
  rbx : s.gpr .rbx = σ.gpr .rcx
  rbp : s.gpr .rbp = σ.gpr .rdi
  r12 : s.gpr .r12 = σ.gpr .rsi
  r13 : s.gpr .r13 = σ.gpr .rdx
  saved : ∀ k < 6, s.mem.readW (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSV + 8 * k))) 64 = σ.gpr (VG.Proof.MlDsa.X86_64.Verify.savedReg k)
  ret : s.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64
  pk : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (.rbp, 0)) p.pkLen = VG.Proof.MlDsa.X86_64.Verify.vPk p σ
  mu : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (.r12, 0)) 64 = VG.Proof.MlDsa.X86_64.Verify.vMu σ
  sig : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (.r13, 0)) p.sigLen = VG.Proof.MlDsa.X86_64.Verify.vSig p σ

theorem vB_small {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) : ∀ b ∈ VG.Proof.MlDsa.X86_64.Verify.vB p, b.2 < 2 ^ 31 := by
  revert p; decide

theorem T.lay {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ s : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) (h : VG.Proof.MlDsa.X86_64.Verify.T p σ s) : VG.Proof.MlDsa.X86_64.Verify.Lay (VG.Proof.MlDsa.X86_64.Verify.vR p) (VG.Proof.MlDsa.X86_64.Verify.vW p) s := by
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨VG.Proof.MlDsa.X86_64.Verify.vB_small hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h.rsp]; exact hv.sp⟩
  · intro b hb b' hb' hne hw
    simp only [VG.Proof.MlDsa.X86_64.Verify.vR, VG.Proof.MlDsa.X86_64.Verify.vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl <;>
      simp only [VG.Proof.MlDsa.X86_64.Verify.wRegs, List.mem_singleton, ne_eq, not_true_eq_false, reduceCtorEq, or_self] at hne hw <;> simp only [h.rbx, h.rbp, h.r12, h.r13]
    all_goals first | exact hv.d1 | exact hv.d2 | exact hv.d3 | exact hv.d1.symm | exact hv.d2.symm |
      exact hv.d3.symm
  · intro b hb
    simp only [VG.Proof.MlDsa.X86_64.Verify.vR, VG.Proof.MlDsa.X86_64.Verify.vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13, h.rsp]
    exacts [hv.k1, hv.k2, hv.k3, hv.k4]
  · intro b hb
    simp only [VG.Proof.MlDsa.X86_64.Verify.vR, VG.Proof.MlDsa.X86_64.Verify.vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13]
    exacts [hv.n1, hv.n2, hv.n3, hv.n4]
  · intro b hb
    simp only [VG.Proof.MlDsa.X86_64.Verify.vR, VG.Proof.MlDsa.X86_64.Verify.vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13]
    · exact mem ⟨σ.gpr .rdi, p.pkLen⟩ (by rw [hv.rd]; simp)
    · exact mem ⟨σ.gpr .rsi, 64⟩ (by rw [hv.rd]; simp)
    · exact mem ⟨σ.gpr .rdx, p.sigLen⟩ (by rw [hv.rd]; simp)
    · exact mem ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩ (by rw [hv.wr]; simp)
  · intro b hb
    simp only [VG.Proof.MlDsa.X86_64.Verify.vW, List.mem_singleton] at hb
    subst hb
    exact ⟨_, by rw [h.wr, hv.wr, h.rbx]; simp, Region.contains_self _ _⟩
  · intro b hb
    simp only [VG.Proof.MlDsa.X86_64.Verify.vR, VG.Proof.MlDsa.X86_64.Verify.vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [h.rbx, h.rbp, h.r12, h.r13, h.rsp]
    exacts [hv.r1, hv.r2, hv.r3, hv.r4]
  · intro b hb
    simp only [VG.Proof.MlDsa.X86_64.Verify.vR, VG.Proof.MlDsa.X86_64.Verify.vW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> simp only [VG.Proof.MlDsa.X86_64.Verify.bases, List.mem_cons, true_or, or_true]

/-- A piece that writes `ws` keeps `T`: the saved registers, the inputs, and
the regions written within the layout. -/
def tChk (p : Params) (ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)) : Bool :=
  (List.range 6).all (fun k => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSV + 8 * k)) 8) && ws.all (fun w => VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) w.1 w.2) &&
    VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (.rbp, 0) p.pkLen && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (.r12, 0) 64 && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (.r13, 0) p.sigLen

theorem tChk_nil : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, VG.Proof.MlDsa.X86_64.Verify.tChk p [] = true := by decide

theorem T.step {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ s s' : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) (h : VG.Proof.MlDsa.X86_64.Verify.T p σ s)
    {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws) (hc : VG.Proof.MlDsa.X86_64.Verify.tChk p ws = true) : VG.Proof.MlDsa.X86_64.Verify.T p σ s' := by
  have L := h.lay hp hv
  simp only [VG.Proof.MlDsa.X86_64.Verify.tChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨hsv, hin⟩, hpk⟩, hmu⟩, hsig⟩ := hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.rsp.trans h.rsp, (hP.bs .rbx (by decide)).trans h.rbx,
    (hP.bs .rbp (by decide)).trans h.rbp, (hP.bs .r12 (by decide)).trans h.r12, (hP.bs .r13 (by decide)).trans h.r13,
    fun k hk => ?_, ?_, by rw [L.keepBytes hP hpk]; exact h.pk, by rw [L.keepBytes hP hmu]; exact h.mu,
    by rw [L.keepBytes hP hsig]; exact h.sig⟩
  · rw [L.keepW hP (hsv k hk)]; exact h.saved k hk
  · have := L.keepRet hP hin
    rw [h.rsp] at this
    rw [this, h.ret]


/-! ## Entry and exit -/

theorem readW_writeW_slot (m : Mem) (a : Addr) {x y : Nat} (v : BitVec 64) (hxy : x + 8 ≤ y ∨ y + 8 ≤ x)
    (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    (m.writeW (a + BitVec.ofNat 64 y) v).readW (a + BitVec.ofNat 64 x) 64 = m.readW (a + BitVec.ofNat 64 x) 64 := by
  refine Mem.readW_writeW_sep ?_ (by decide)
  rcases hxy with h | h
  · exact (off_disj (p := a) h (by omega)).sep (Region.contains_self _ _) (Region.contains_self _ _)
  · exact (off_disj (p := a) h (by omega)).symm.sep (Region.contains_self _ _) (Region.contains_self _ _)

/-- The six stores of `pro`: each slot holds its register. -/
theorem stores_read (m : Mem) (a : Addr) (v : Nat → BitVec 64) : ∀ k < 6,
    ((((((m.writeW (a + BitVec.ofNat 64 840) (v 0)).writeW (a + BitVec.ofNat 64 848) (v 1)).writeW
      (a + BitVec.ofNat 64 856) (v 2)).writeW (a + BitVec.ofNat 64 864) (v 3)).writeW (a + BitVec.ofNat 64 872)
      (v 4)).writeW (a + BitVec.ofNat 64 880) (v 5)).readW (a + BitVec.ofNat 64 (VG.Impl.MlDsa.X86_64.Verify.oSV + 8 * k)) 64 = v k := by
  intro k hk
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp (disch := omega) only [VG.Impl.MlDsa.X86_64.Verify.oSV, Nat.reduceMul, Nat.reduceAdd, VG.Proof.MlDsa.X86_64.Verify.readW_writeW_slot, Mem.readW_writeW_self64]

theorem pro_eq : VG.Impl.MlDsa.X86_64.Verify.pro = [.store (VG.Impl.MlKem.X86_64.at_ .rcx 840) .rbx, .store (VG.Impl.MlKem.X86_64.at_ .rcx 848) .rbp, .store (VG.Impl.MlKem.X86_64.at_ .rcx 856) .r12,
    .store (VG.Impl.MlKem.X86_64.at_ .rcx 864) .r13, .store (VG.Impl.MlKem.X86_64.at_ .rcx 872) .r14, .store (VG.Impl.MlKem.X86_64.at_ .rcx 880) .r15, .mov .rbx (.reg .rcx),
    .mov .rbp (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rdx), .mov32 .r15 (.imm 1)] := rfl

theorem scr_big {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) : 888 ≤ VG.Proof.MlDsa.X86_64.Verify.scrLen p := by revert p; decide

theorem pro_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Verify.pro) σ fun s => VG.Proof.MlDsa.X86_64.Verify.T p σ s ∧ s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True := by
  have hb := VG.Proof.MlDsa.X86_64.Verify.scr_big hp
  have hS : ⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩ ∈ σ.wr := by rw [hv.wr]; simp
  have hsl : VG.Proof.MlDsa.X86_64.Verify.scrLen p < 2 ^ 64 := by have := VG.Proof.MlDsa.X86_64.Verify.vB_small hp (.rbx, VG.Proof.MlDsa.X86_64.Verify.scrLen p) (by simp); simp only at this; omega
  have c : ∀ o, o + 8 ≤ VG.Proof.MlDsa.X86_64.Verify.scrLen p → (⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩ : Region).Contains (σ.gpr .rcx + BitVec.ofNat 64 o) 8 :=
    fun o ho => contains_offset' ho hsl
  have w : ∀ o, o + 8 ≤ VG.Proof.MlDsa.X86_64.Verify.scrLen p → InRegions σ.wr (σ.gpr .rcx + BitVec.ofNat 64 o) 8 := fun o ho => ⟨_, hS, c o ho⟩
  have w0 := w 840 (by omega); have w1 := w 848 (by omega); have w2 := w 856 (by omega)
  have w3 := w 864 (by omega); have w4 := w 872 (by omega); have w5 := w 880 (by omega)
  rw [VG.Proof.MlDsa.X86_64.Verify.pro_eq]
  refine WP.mono (WP.keep [.rbx, .rbp, .r12, .r13, .r15] (Q := fun s =>
    s.mem = (((((σ.mem.writeW (σ.gpr .rcx + BitVec.ofNat 64 840) (σ.gpr .rbx)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 848) (σ.gpr .rbp)).writeW (σ.gpr .rcx + BitVec.ofNat 64 856) (σ.gpr .r12)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 864) (σ.gpr .r13)).writeW (σ.gpr .rcx + BitVec.ofNat 64 872) (σ.gpr .r14)).writeW
      (σ.gpr .rcx + BitVec.ofNat 64 880) (σ.gpr .r15) ∧
    s.gpr .rbx = σ.gpr .rcx ∧ s.gpr .rbp = σ.gpr .rdi ∧ s.gpr .r12 = σ.gpr .rsi ∧ s.gpr .r13 = σ.gpr .rdx ∧
    s.gpr .r15 = 1)
    (by xrun [w0, w1, w2, w3, w4, w5]) (by decide)) fun s ⟨⟨hm, hbx, hbp, h12, h13, h15⟩, k⟩ => ⟨?_, h15⟩
  have hf : Frame [⟨σ.gpr .rcx, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩] σ.mem s.mem := by
    rw [hm]
    exact (((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 840 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 848 (by omega))).writeW (List.mem_singleton_self _) _ (c 856 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 864 (by omega))).writeW (List.mem_singleton_self _) _ (c 872 (by omega))).writeW
      (List.mem_singleton_self _) _ (c 880 (by omega)))
  have hsp : s.gpr .rsp = σ.gpr .rsp := k.gpr (by decide)
  have z : ∀ x : Addr, x + BitVec.ofNat 64 0 = x := fun x => BitVec.add_zero x
  refine ⟨k.2.1, k.2.2, hsp, hbx, hbp, h12, h13, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [VG.Proof.MlDsa.X86_64.Verify.pa, hbx, hm]
    exact VG.Proof.MlDsa.X86_64.Verify.stores_read σ.mem (σ.gpr .rcx) (fun j => σ.gpr (VG.Proof.MlDsa.X86_64.Verify.savedReg j)) j hj
  · exact hf.readW (Region.contains_self _ _) (by simpa using hv.r4) (by decide)
  · rw [VG.Proof.MlDsa.X86_64.Verify.pa, hbp, z]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using hv.d1) (by have := hv.n1; omega)
  · rw [VG.Proof.MlDsa.X86_64.Verify.pa, h12, z]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using hv.d2) (by decide)
  · rw [VG.Proof.MlDsa.X86_64.Verify.pa, h13, z]
    exact Proof.MlKem.bytesAt_frame hf (by simpa using hv.d3) (by have := hv.n3; omega)

theorem epi_eq : VG.Impl.MlDsa.X86_64.Verify.epi = [.mov32 .rax (.reg .r15), .mov .r15 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 880)), .mov .r14 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 872)),
    .mov .r13 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 864)), .mov .r12 (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 856)), .mov .rbp (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 848)),
    .mov .rbx (.mem (VG.Impl.MlKem.X86_64.at_ .rbx 840))] := rfl

theorem saved_in {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) : ∀ k < 6, VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSV + 8 * k)) 8 = true := by
  revert p; decide

theorem epi_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ s : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) (h : VG.Proof.MlDsa.X86_64.Verify.T p σ s) :
    WP isa (.block VG.Impl.MlDsa.X86_64.Verify.epi) s fun s' => VG.Proof.MlDsa.X86_64.Verify.res s' = (s.gpr .r15).setWidth 32 ∧ gprPreserved σ s' := by
  have L := h.lay hp hv
  have hin : ∀ k < 6, InRegions (s.rd ++ s.wr) (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSV + 8 * k))) 8 := by
    have hk : ∀ k < 6, VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSV + 8 * k)) 8 = true := VG.Proof.MlDsa.X86_64.Verify.saved_in hp
    exact fun k hkk => L.inR (hk k hkk)
  have e : ∀ k < 6, s.mem.readW (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 64 = σ.gpr (VG.Proof.MlDsa.X86_64.Verify.savedReg k) :=
    fun k hk => h.saved k hk
  have i : ∀ k < 6, InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (840 + 8 * k)) 8 := hin
  have e0 := e 0 (by decide); have e1 := e 1 (by decide); have e2 := e 2 (by decide)
  have e3 := e 3 (by decide); have e4 := e 4 (by decide); have e5 := e 5 (by decide)
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i3 := i 3 (by decide); have i4 := i 4 (by decide); have i5 := i 5 (by decide)
  rw [show VG.Proof.MlDsa.X86_64.Verify.savedReg 0 = .rbx from rfl] at e0; rw [show VG.Proof.MlDsa.X86_64.Verify.savedReg 1 = .rbp from rfl] at e1
  rw [show VG.Proof.MlDsa.X86_64.Verify.savedReg 2 = .r12 from rfl] at e2; rw [show VG.Proof.MlDsa.X86_64.Verify.savedReg 3 = .r13 from rfl] at e3
  rw [show VG.Proof.MlDsa.X86_64.Verify.savedReg 4 = .r14 from rfl] at e4; rw [show VG.Proof.MlDsa.X86_64.Verify.savedReg 5 = .r15 from rfl] at e5
  simp only [Nat.reduceMul, Nat.reduceAdd] at e0 e1 e2 e3 e4 e5 i0 i1 i2 i3 i4 i5
  rw [VG.Proof.MlDsa.X86_64.Verify.epi_eq]
  refine WP.mono (WP.keep [.rax, .r15, .r14, .r13, .r12, .rbp, .rbx] (Q := fun s' =>
    s'.gpr .rax = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) ∧ s'.gpr .r15 = σ.gpr .r15 ∧
    s'.gpr .r14 = σ.gpr .r14 ∧ s'.gpr .r13 = σ.gpr .r13 ∧ s'.gpr .r12 = σ.gpr .r12 ∧ s'.gpr .rbp = σ.gpr .rbp ∧
    s'.gpr .rbx = σ.gpr .rbx ∧ s'.mem = s.mem) (by xrun [i0, i1, i2, i3, i4, i5, e0, e1, e2, e3, e4, e5]) (by decide))
    fun s' ⟨⟨hax, h15, h14, h13, h12, hbp, hbx, hm⟩, k⟩ => ⟨?_, ⟨fun r hr => ?_, ?_⟩⟩
  · simp only [VG.Proof.MlDsa.X86_64.Verify.res, hax]; apply BitVec.eq_of_toNat_eq; simp
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hbx, hbp, by rw [k.gpr (by decide), h.rsp], h12, h13, h14, h15]
  · rw [hm]; exact h.ret

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control`. -/
section

/-!
# ML-DSA verification on x86-64: branches, sequences and the comparison

The branch on the result in `r15` (`ifOk_ok`, `ifOk_tr`), sequences of pieces
indexed by a number (`seqR_ok`, `seqR_tr`), and the comparison of `c̃′` with
`c̃` without a branch (`cmpAnd_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlKem.X86_64 (at_)
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The branch on `r15` -/

theorem test15_ok (s : State) :
    WP isa (.block [.alu32 .test .r15 (.reg .r15)]) s fun s₁ => VG.Proof.MlDsa.X86_64.Verify.PPostB s s₁ [] ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some ((s.gpr .r15).setWidth 32 == 0) :=
  WP.mono (WP.keep [.r15] (Q := fun s₁ => s₁.mem = s.mem ∧ s₁.gpr .r15 = s.gpr .r15 ∧
      s₁.zf = some (((s.gpr .r15).setWidth 32 &&& (s.gpr .r15).setWidth 32) == 0)) (by xrun) (by decide))
    fun _ ⟨⟨hm, h15, hz⟩, k⟩ => ⟨VG.Proof.MlDsa.X86_64.Verify.postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _), h15,
      by rw [hz, BitVec.and_self]⟩

theorem flag_sw (p : Prop) [Decidable p] : ((VG.Proof.MlDsa.X86_64.Verify.flag p).setWidth 32 == 0) = !decide p := by
  unfold VG.Proof.MlDsa.X86_64.Verify.flag; by_cases h : p <;> simp [h]

theorem ifOk_ok {c : Prog isa} {s : State} {Q : State → Prop} {p : Prop} [Decidable p] (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag p)
    (ht : ∀ s₁, VG.Proof.MlDsa.X86_64.Verify.PPostB s s₁ [] → s₁.gpr .r15 = s.gpr .r15 → p → WP isa c s₁ Q)
    (he : ∀ s₁, VG.Proof.MlDsa.X86_64.Verify.PPostB s s₁ [] → s₁.gpr .r15 = s.gpr .r15 → ¬ p → Q s₁) : WP isa (VG.Impl.MlDsa.X86_64.Verify.ifOk c) s Q := by
  unfold VG.Impl.MlDsa.X86_64.Verify.ifOk
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.test15_ok s) fun s₁ ⟨hP, h15', hz⟩ => ?_)
  rw [h15, VG.Proof.MlDsa.X86_64.Verify.flag_sw] at hz
  refine WP.ite (M := isa) (decide p) (show s₁.zf.map (!·) = _ by rw [hz]; simp) (fun hb => ?_) fun hb => ?_
  · exact ht s₁ hP h15' (by simpa using hb)
  · exact WP.block_nil (he s₁ hP h15' (by simpa using hb))

theorem ifOk_tr {c : Prog isa} {P Q : State → State → Prop}
    (he : ∀ x y, P x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (ht : RelCT isa (fun x y => ∃ x₀ y₀, P x₀ y₀ ∧ VG.Proof.MlDsa.X86_64.Verify.PPostB x₀ x [] ∧ VG.Proof.MlDsa.X86_64.Verify.PPostB y₀ y [] ∧
      x.gpr .r15 = x₀.gpr .r15 ∧ y.gpr .r15 = y₀.gpr .r15 ∧ (x₀.gpr .r15).setWidth 32 ≠ 0) c Q)
    (hq : ∀ x y, (∃ x₀ y₀, P x₀ y₀ ∧ VG.Proof.MlDsa.X86_64.Verify.PPostB x₀ x [] ∧ VG.Proof.MlDsa.X86_64.Verify.PPostB y₀ y [] ∧
      x.gpr .r15 = x₀.gpr .r15 ∧ y.gpr .r15 = y₀.gpr .r15 ∧ (x₀.gpr .r15).setWidth 32 = 0) → Q x y) :
    RelCT isa P (VG.Impl.MlDsa.X86_64.Verify.ifOk c) Q := by
  unfold VG.Impl.MlDsa.X86_64.Verify.ifOk
  refine RelCT.seq (RelCT.postDep (VG.Proof.MlDsa.X86_64.Verify.block_nomem_tr fun i hi s => by
      simp only [List.mem_singleton] at hi; subst hi; rfl)
    (F := fun x x₁ => VG.Proof.MlDsa.X86_64.Verify.PPostB x x₁ [] ∧ x₁.gpr .r15 = x.gpr .r15 ∧ x₁.zf = some ((x.gpr .r15).setWidth 32 == 0))
    (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Verify.test15_ok x, VG.Proof.MlDsa.X86_64.Verify.test15_ok y⟩) (Q := fun x₁ y₁ => ∃ x₀ y₀, P x₀ y₀ ∧
      (VG.Proof.MlDsa.X86_64.Verify.PPostB x₀ x₁ [] ∧ x₁.gpr .r15 = x₀.gpr .r15 ∧ x₁.zf = some ((x₀.gpr .r15).setWidth 32 == 0)) ∧
      (VG.Proof.MlDsa.X86_64.Verify.PPostB y₀ y₁ [] ∧ y₁.gpr .r15 = y₀.gpr .r15 ∧ y₁.zf = some ((y₀.gpr .r15).setWidth 32 == 0)))
    fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1, h2⟩) (RelCT.ite ?_ ?_ ?_)
  · rintro x₁ y₁ ⟨x₀, y₀, hp, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩
    show x₁.zf.map (!·) = y₁.zf.map (!·)
    rw [hx, hy, he x₀ y₀ hp]
  · refine RelCT.mono ht (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, e1, hx⟩, ⟨h2, e2, _⟩⟩, hc⟩ =>
      ⟨x₀, y₀, hp, h1, h2, e1, e2, ?_⟩) fun _ _ h => h
    have hc' : x₁.zf.map (!·) = some true := hc
    rw [hx] at hc'
    simpa using hc'
  · refine RelCT.mono VG.Proof.MlDsa.X86_64.Verify.nil_tr (fun x₁ y₁ ⟨⟨x₀, y₀, hp, ⟨h1, e1, hx⟩, ⟨h2, e2, _⟩⟩, hc⟩ =>
      ⟨x₀, y₀, hp, h1, h2, e1, e2, ?_⟩) fun x y h => hq x y h
    have hc' : x₁.zf.map (!·) = some false := hc
    rw [hx] at hc'
    simpa using hc'

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (VG.Impl.MlDsa.X86_64.Verify.seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [VG.Impl.MlDsa.X86_64.Verify.seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact VG.Proof.MlDsa.X86_64.Verify.seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (VG.Impl.MlDsa.X86_64.Verify.seqR f a n) (R (a + n))
  | 0, _, _ => VG.Proof.MlDsa.X86_64.Verify.nil_tr
  | n + 1, a, h => by
    rw [VG.Impl.MlDsa.X86_64.Verify.seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (VG.Proof.MlDsa.X86_64.Verify.seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))


/-! ## The comparison -/

theorem sbb_val (x r : BitVec 64) :
    BitVec.setWidth 64 (BitVec.setWidth 32 r &&&
      BitVec.setWidth 32 (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide (x.toNat < (1 : BitVec 64).toNat))))) =
    if x = 0 then BitVec.setWidth 64 (BitVec.setWidth 32 r) else 0 := by
  by_cases h : x = 0
  · subst h
    rw [VG.Proof.MlKem.X86_64.ifp rfl, show decide ((0 : BitVec 64).toNat < (1 : BitVec 64).toNat) = true by decide,
      show BitVec.setWidth 32 (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 32 by decide,
      BitVec.and_allOnes]
  · rw [VG.Proof.MlKem.X86_64.ifn h, show decide (x.toNat < (1 : BitVec 64).toNat) = false by
      simp only [decide_eq_false_iff_not]; intro h'; exact h (BitVec.eq_of_toNat_eq (by simp at h' ⊢; omega))]
    apply BitVec.eq_of_toNat_eq; simp

theorem cmpEnd_ok (s : State) :
    WP isa (.block (([.alu .sub .rdx (.imm 1), .alu .sbb .rax (.reg .rax)] : List Instr) ++ and15)) s fun s' =>
      (s'.gpr .r15 = (if s.gpr .rdx = 0 then BitVec.setWidth 64 ((s.gpr .r15).setWidth 32) else 0) ∧
        s'.mem = s.mem) ∧ Keep [.rdx, .rax, .r15] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold and15
  xrun [List.cons_append, List.nil_append]
  exact VG.Proof.MlDsa.X86_64.Verify.sbb_val _ _



theorem cmpBody_ok (s : State) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 1)
    (h1 : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 1) :
    WP isa cmpBody s fun s' =>
      (s'.gpr .rdx = s.gpr .rdx ||| (BitVec.setWidth 64 (s.mem (s.gpr .rsi)) ^^^ BitVec.setWidth 64 (s.mem (s.gpr .rdi))) ∧
        s'.gpr .rsi = s.gpr .rsi + 1 ∧ s'.gpr .rdi = s.gpr .rdi + 1 ∧ s'.gpr .rcx = s.gpr .rcx - 1 ∧
        s'.zf = some (s.gpr .rcx - 1 == 0) ∧ s'.mem = s.mem) ∧ Keep [.rax, .r8, .rdx, .rsi, .rdi, .rcx] s s' := by
  refine WP.keep _ ?_ (by decide)
  unfold cmpBody
  xrun [h0, h1]

theorem or_xor_zero {d : BitVec 64} {x y : Byte} :
    (d ||| (BitVec.setWidth 64 x ^^^ BitVec.setWidth 64 y) = 0) ↔ d = 0 ∧ x = y := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  refine and_congr Iff.rfl ⟨fun h => ?_, fun h => h ▸ rfl⟩
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at this
  have hx := x.isLt; have hy := y.isLt
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- `r15 ← 0` unless the `n` bytes at `a` and `b` are equal. -/
theorem cmpAnd_ok {rbs wbs : List (Reg × Nat)} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay rbs wbs s) {a b : VG.Impl.MlDsa.X86_64.Verify.Ptr} {n : Nat} (hn : 0 < n)
    (ha : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) a n = true) (hb : VG.Proof.MlDsa.X86_64.Verify.inB (rbs ++ wbs) b n = true) {P : Prop} [Decidable P]
    (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag P) :
    WP isa (cmpAnd a b n) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [] ∧
      s'.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (P ∧ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) n = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s b) n) := by
  have hS := L.ok
  have hn' : n < 2 ^ 31 := by obtain ⟨m, hm, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec ha; have := (hS _ hm).1; omega
  have hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × VG.Impl.MlDsa.X86_64.Verify.Arg)),
      x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS ha, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hb, by decide⟩, ⟨hn', by decide⟩⟩
  have ra := L.inR ha
  have rb := L.inR hb
  unfold cmpAnd
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s1 h1 => ?_
  refine WP.mono (WP.keep [.rdx] (Q := fun s₂ => s₂.mem = s1.mem ∧ s₂.gpr .rdx = 0) (by xrun) (by decide))
    fun s2 ⟨⟨hm2, hd2⟩, k2⟩ => ?_
  have k12 : Keep VG.Proof.MlDsa.X86_64.Verify.argRegs s s2 := (h1.2.trans k2).mono (by simp)
  have hm12 : s2.mem = s.mem := hm2.trans h1.1.2
  have ea : s2.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s a := by rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_self ..)
  have eb : s2.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s b := by
    rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have ec : s2.gpr .rcx = BitVec.ofNat 64 n := by
    rw [k2.gpr (by decide)]
    exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine WP.seq (WP.mono (wp_countdown (cnt := .rcx) (N := n) (by omega) hn (fun k s' =>
      s'.gpr .rsi = VG.Proof.MlDsa.X86_64.Verify.pa s a + BitVec.ofNat 64 k ∧ s'.gpr .rdi = VG.Proof.MlDsa.X86_64.Verify.pa s b + BitVec.ofNat 64 k ∧ s'.mem = s.mem ∧
      (s'.gpr .rdx = 0 ↔ ∀ j < k, s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a + BitVec.ofNat 64 j) = s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s b + BitVec.ofNat 64 j)) ∧
      Keep VG.Proof.MlDsa.X86_64.Verify.argRegs s s')
    (fun k hk s' ⟨hsi, hdi, hm, hd, kk⟩ _ => ?_) (fun _ h => h)
    ⟨by rw [ea]; simp, by rw [eb]; simp, hm12, by rw [hd2]; simp, k12⟩ ec)
    fun s3 ⟨_, _, hm3, hd3, k3⟩ => ?_)
  · refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.cmpBody_ok s' (by rw [kk.2.1, kk.2.2, hsi]; exact VG.Proof.MlDsa.X86_64.Verify.inRegions_byte ra hk (by omega))
      (by rw [kk.2.1, kk.2.2, hdi]; exact VG.Proof.MlDsa.X86_64.Verify.inRegions_byte rb hk (by omega)))
      fun s'' ⟨⟨hd', hsi', hdi', hcx, hz, hm'⟩, k'⟩ => ⟨⟨?_, ?_, hm'.trans hm, ?_, (kk.trans k').mono (by simp)⟩, hcx, hz⟩
    · rw [hsi', hsi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [hdi', hdi, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.add_assoc, ← BitVec.ofNat_add]
    · rw [hd', VG.Proof.MlDsa.X86_64.Verify.or_xor_zero, hd, hsi, hdi, hm]
      constructor
      · rintro ⟨h, e⟩ j hj
        rcases (by omega : j < k ∨ j = k) with hj | rfl
        · exact h j hj
        · exact e
      · intro h; exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.cmpEnd_ok s3) fun s4 ⟨⟨h15', hm4⟩, k4⟩ => ⟨?_, ?_⟩
    · exact VG.Proof.MlDsa.X86_64.Verify.postB_of_keep (k3.trans k4) (by decide) (by rw [hm4, hm3]; exact Frame.refl _ _)
    · have hr15 : s3.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag P := by rw [k3.gpr (by decide), h15]
      rw [h15', hr15]
      have heq : (s3.gpr .rdx = 0) ↔ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) n = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s b) n := by
        rw [hd3]
        constructor
        · intro h; simp only [bytesAt]; exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)
        · intro h j hj
          have := congrArg (fun l => l.getD j 0) h
          rwa [Proof.MlKem.bytesAt_getD _ _ hj, Proof.MlKem.bytesAt_getD _ _ hj] at this
      by_cases hd : s3.gpr .rdx = 0
      · rw [VG.Proof.MlKem.X86_64.ifp hd]
        have he := heq.mp hd
        by_cases hP : P <;> simp [VG.Proof.MlDsa.X86_64.Verify.flag, hP, he]
      · rw [VG.Proof.MlKem.X86_64.ifn hd]
        have he : ¬ bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s a) n = bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s b) n := fun e => hd (heq.mpr e)
        simp [VG.Proof.MlDsa.X86_64.Verify.flag, he]

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk`. -/
section

/-!
# ML-DSA verification on x86-64: what the proofs need of the primitives

`PrimsOk P`: each primitive of `P` is correct and constant time under its
shared contract with at most 16 bytes of stack (`CalleeOk`, from its
`Verified` proof by `CalleeOk.of_verified`; 24 for `vg_mldsa_rej_ntt_poly4`),
never writes the stack pointer, calls at most three deep and never loads
MXCSR. The proofs of `vg_mldsa*_verify` hold for any such `P`.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Spec.MlDsa

/-- Implementations of the primitives, correct and constant time. -/
structure PrimsOk (P : VG.Impl.MlDsa.X86_64.Verify.Prims) : Prop where
  ntt : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.ntt (nttContract X86_64.abi 16)
  invNtt : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.invNtt (nttInvContract X86_64.abi 16)
  mul : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.mul (mulContract X86_64.abi 16)
  mulAdd : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.mulAdd (mulAddContract X86_64.abi 16)
  sub : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.sub (subContract X86_64.abi 16)
  rejNtt : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.rejNtt (rejNTTContract X86_64.abi 16)
  ball : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.ball (sampleInBallContract X86_64.abi 16)
  useHint : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.useHint (useHintContract X86_64.abi 16)
  simpleBitPack : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.simpleBitPack (simpleBitPackContract X86_64.abi 16)
  bitUnpack : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.bitUnpack (bitUnpackContract X86_64.abi 16)
  unpackT1 : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.unpackT1 (unpackT1Contract X86_64.abi 16)
  hintUnpack : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.hintUnpack (hintBitUnpackContract X86_64.abi 16)
  normLt : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.normLt (normLtContract X86_64.abi 16)
  rej4 : VG.Proof.MlDsa.X86_64.Verify.CalleeOk P.rej4 (rejNTT4Contract X86_64.abi 24)

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageZ`. -/
section

/-!
# ML-DSA verification on x86-64: the hint and `z`

`HintIs` the hint of the signature, and `r15` whether it is well formed
(`hint_ok`); then, if it is, `z[i]` (polynomial `8 + i`) and `r15` whether
each norm so far is small (`zOne_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

/-- The `len` bytes at offset `off` of the signature. -/
theorem T.sigSlice {p : Params} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Verify.T p σ s) {off len : Nat} (hl : off + len ≤ p.sigLen) :
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (.r13, off)) len = ((VG.Proof.MlDsa.X86_64.Verify.vSig p σ).drop off).take len := by
  rw [← h.sig, VG.Proof.MlDsa.X86_64.Verify.pa, VG.Proof.MlDsa.X86_64.Verify.pa, BitVec.add_zero, Proof.MlKem.bytesAt_slice _ _ hl]

theorem T.pkSlice {p : Params} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Verify.T p σ s) {off len : Nat} (hl : off + len ≤ p.pkLen) :
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (.rbp, off)) len = ((VG.Proof.MlDsa.X86_64.Verify.vPk p σ).drop off).take len := by
  rw [← h.pk, VG.Proof.MlDsa.X86_64.Verify.pa, VG.Proof.MlDsa.X86_64.Verify.pa, BitVec.add_zero, Proof.MlKem.bytesAt_slice _ _ hl]

theorem lenZ_eq (p : Params) : VG.Impl.MlDsa.X86_64.Verify.lenZ p = VG.Proof.MlDsa.Verify.lenZ p := rfl

/-! ## The hint -/

/-- After the hint: `r15` whether it is well formed, and the hint. -/
def S1 (p : Params) (σ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.T p σ s ∧ match vHint p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) with
    | some h => s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True ∧ HintIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pH 0)) p.k h
    | none => s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag False

/-- The facts about the parameters the hint needs. -/
def hintChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.huChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (.r13, oHint p) (p.ω + p.k) (pH 0) (256 * p.k) &&
    VG.Proof.MlDsa.X86_64.Verify.tChk p [(pH 0, 256 * p.k * 4)] && decide (VG.Proof.MlDsa.X86_64.Verify.HuPar (p.ω + p.k) p.ω (256 * p.k)) &&
    decide (oHint p + (p.ω + p.k) ≤ p.sigLen)

theorem hintChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, VG.Proof.MlDsa.X86_64.Verify.hintChk p = true := by decide +kernel

theorem hint_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ s : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    (h : VG.Proof.MlDsa.X86_64.Verify.T p σ s) : WP isa (hint P p) s (VG.Proof.MlDsa.X86_64.Verify.S1 p σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.hintChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hc
  have L := h.lay hp hv
  unfold hint
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.hintUnpackAt_ok C.hintUnpack L c3 c1) fun s₁ ⟨hP₁, _, hq₁⟩ => ?_)
  have h₁ := h.step hp hv hP₁ c2
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.mov15_ok s₁) fun s₂ ⟨⟨h15, hm₂⟩, k₂⟩ => ?_
  have hP₂ : VG.Proof.MlDsa.X86_64.Verify.PPostB s₁ s₂ [] := VG.Proof.MlDsa.X86_64.Verify.postB_of_keep k₂ (by decide) (by rw [hm₂]; exact Frame.refl _ _)
  refine ⟨h₁.step hp hv hP₂ (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), ?_⟩
  rw [h.sigSlice c4, show p.ω + p.k - p.ω = p.k by omega] at hq₁
  have e : VG.Proof.MlDsa.X86_64.Verify.pa s₂ (pH 0) = VG.Proof.MlDsa.X86_64.Verify.pa s (pH 0) := by rw [hP₂.pa (by decide), hP₁.pa (by decide)]
  have hv' : vHint p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) = VG.Spec.MlDsa.hintBitUnpack p.ω p.k (((VG.Proof.MlDsa.X86_64.Verify.vSig p σ).drop (oHint p)).take (p.ω + p.k)) := rfl
  rw [hv']
  revert hq₁
  generalize VG.Spec.MlDsa.hintBitUnpack p.ω p.k (((VG.Proof.MlDsa.X86_64.Verify.vSig p σ).drop (oHint p)).take (p.ω + p.k)) = H
  cases H with
  | some hh =>
    intro ⟨hr, hH⟩
    simp only [VG.Proof.MlDsa.X86_64.Verify.res] at hr
    refine ⟨by rw [h15, hr]; rfl, ?_⟩
    rw [e, hm₂]; exact hH
  | none =>
    intro hr
    simp only [VG.Proof.MlDsa.X86_64.Verify.res] at hr
    show s₂.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag False
    rw [h15, hr]; rfl


/-! ## `z` -/

/-- After `z[0], …, z[j - 1]`, with the hint `h`. -/
structure S2 (p : Params) (h : List (Vector Bool n)) (j : Nat) (σ s : State) : Prop where
  t : VG.Proof.MlDsa.X86_64.Verify.T p σ s
  hint : HintIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pH 0)) p.k h
  z : ∀ i < j, PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pZ i)) (toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i))
  r15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (∀ i < j, normRq [toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i)] < p.γ₁ - p.β)

/-- The facts about the parameters `z[i]` needs. -/
def zChk (p : Params) (i : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.buChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (.r13, p.ctildeLen + lenZ p * i) (lenZ p) (pZ i) &&
    decide ((p.γ₁ - 1, p.γ₁) ∈ bitPackParams) && decide (lenZ p = 32 * bitlen (p.γ₁ - 1 + p.γ₁)) &&
    decide (p.ctildeLen + lenZ p * i + lenZ p ≤ p.sigLen) && VG.Proof.MlDsa.X86_64.Verify.tChk p [(pZ i, 1024)] &&
    VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [(pZ i, 1024)] (pH 0) (1024 * p.k) &&
    (List.range i).all (fun i' => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [(pZ i, 1024)] (pZ i') 1024) && VG.Proof.MlDsa.X86_64.Verify.nlChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (pZ i) &&
    decide (p.γ₁ - p.β < 2 ^ 31)

theorem zChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, ∀ i < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.zChk p i = true := by decide +kernel

theorem zOne_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {i : Nat} (hi : i < p.ℓ) {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S2 p h i σ s) :
    WP isa (zOne P p i) s (VG.Proof.MlDsa.X86_64.Verify.S2 p h (i + 1) σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.zChk_all p hp i hi
  simp only [VG.Proof.MlDsa.X86_64.Verify.zChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩ := hc
  have L := hs.t.lay hp hv
  unfold zOne
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.bitUnpackAt_ok C.bitUnpack L c2 c3 c1) fun s₁ ⟨hP₁, h15₁, hq₁⟩ => ?_)
  have t₁ := hs.t.step hp hv hP₁ c5
  have L₁ := t₁.lay hp hv
  rw [hs.t.sigSlice c4] at hq₁
  have e₁ : VG.Proof.MlDsa.X86_64.Verify.pa s₁ (pZ i) = VG.Proof.MlDsa.X86_64.Verify.pa s (pZ i) := hP₁.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide)
  rw [← e₁] at hq₁
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.normLtAt_ok C.normLt L₁ c9 c8 hq₁.1) fun s₂ ⟨hP₂, h15₂, hr₂⟩ => ?_)
  have t₂ := t₁.step hp hv hP₂ (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp)
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.and15_ok s₂) fun s₃ ⟨⟨h15₃, hm₃⟩, k₃⟩ => ?_
  have hP₃ : VG.Proof.MlDsa.X86_64.Verify.PPostB s₂ s₃ [] := VG.Proof.MlDsa.X86_64.Verify.postB_of_keep k₃ (by decide) (by rw [hm₃]; exact Frame.refl _ _)
  have hP₂₃ : VG.Proof.MlDsa.X86_64.Verify.PPostB s₁ s₃ [] := PPostB.trans hP₂ hP₃ (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
  refine ⟨t₂.step hp hv hP₃ (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), ?_, fun i' hi' => ?_, ?_⟩
  · exact L₁.keepHint hP₂₃ (VG.Proof.MlDsa.X86_64.Verify.keepB_nil c6) (L.keepHint hP₁ c6 hs.hint)
  · rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
    · exact L₁.keepPoly hP₂₃ (VG.Proof.MlDsa.X86_64.Verify.keepB_nil (c7 i' hi')) (L.keepPoly hP₁ (c7 i' hi') (hs.z i' hi'))
    · exact L₁.keepPoly hP₂₃ (VG.Proof.MlDsa.X86_64.Verify.keepB_nil_of (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide) c8) hq₁
  · rw [h15₃, h15₂, h15₁, hs.r15]
    have hr : VG.Proof.MlDsa.X86_64.Verify.res s₂ = 1 ∨ VG.Proof.MlDsa.X86_64.Verify.res s₂ = 0 := by
      rw [hr₂]
      by_cases hh : normRq [polyAt s₁.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₁ (pZ i))] < p.γ₁ - p.β
      · left; rw [VG.Proof.MlKem.X86_64.ifp hh]
      · right; rw [VG.Proof.MlKem.X86_64.ifn hh]
    rw [VG.Proof.MlDsa.X86_64.Verify.and_flag hr]
    have hq2 : polyAt s₁.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₁ (pZ i)) = toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i) := hq₁.2
    refine VG.Proof.MlDsa.X86_64.Verify.flag_congr ⟨fun ⟨h1, h2⟩ i' hi' => ?_, fun h1 => ⟨fun i' hi' => h1 i' (by omega), ?_⟩⟩
    · rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
      · exact h1 i' hi'
      · rw [hr₂, hq2] at h2
        by_contra hn; rw [VG.Proof.MlKem.X86_64.ifn hn] at h2; cases h2
    · rw [hr₂, hq2, VG.Proof.MlKem.X86_64.ifp (h1 i (by omega))]

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageA`. -/
section

/-!
# ML-DSA verification on x86-64: the samplers

`ρ` to `SB` and `SB4`; each entry `Â[r, s]` (number `ℓr + s`) sampled from
`ρ ‖ s ‖ r`, four at a time (`aGrp_ok`) and then one at a time (`aOne_ok`),
and `c` (`ballStage_ok`), each reduced, and `r15` 1 only if every sampler
succeeded, with their outputs (`S3`, `S4`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt vRho aSeed)

/-! ## The seed -/

theorem seed_bytes (m : Mem) (A : Addr) (b1 b2 : Byte) :
    bytesAt ((m.writeW (A + BitVec.ofNat 64 32) b1).writeW (A + BitVec.ofNat 64 33) b2) A 34 =
      bytesAt m A 32 ++ [b1] ++ [b2] := by
  refine Proof.MlKem.bytesAt_eq (by simp [Proof.MlKem.bytesAt_length]) fun i hi => ?_
  rw [VG.WriteBytes.writeW8_apply, VG.WriteBytes.writeW8_apply]
  rcases (by omega : i < 32 ∨ i = 32 ∨ i = 33) with h | rfl | rfl
  · have n1 : A + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 33 := by intro e; bv_omega
    have n2 : A + BitVec.ofNat 64 i ≠ A + BitVec.ofNat 64 32 := by intro e; bv_omega
    rw [VG.Proof.MlKem.X86_64.ifn n1, VG.Proof.MlKem.X86_64.ifn n2]
    simp [List.getElem_append_left, Proof.MlKem.bytesAt_getElem, h, Proof.MlKem.bytesAt_length]
  · have n1 : A + BitVec.ofNat 64 32 ≠ A + BitVec.ofNat 64 33 := by intro e; bv_omega
    rw [VG.Proof.MlKem.X86_64.ifn n1, VG.Proof.MlKem.X86_64.ifp rfl]
    simp [Proof.MlKem.bytesAt_length]
  · rw [VG.Proof.MlKem.X86_64.ifp rfl]
    simp [Proof.MlKem.bytesAt_length]

theorem integerToBytes_one (x : Nat) : integerToBytes x 1 = [BitVec.ofNat 8 x] := by
  simp [integerToBytes]


/-! ## `Â` -/

/-- Entry `(r', c')` of `Â`, number `l r' + c'` in rows of `l` entries, is sampled before entry `e`. -/
def Done (l e r' c' : Nat) : Prop := l * r' + c' < e

theorem rc_eq {l r c e : Nat} (hc : c < l) (h : l * r + c = e) : r = e / l ∧ c = e % l := by
  have hl : 0 < l := by omega
  subst h
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hc, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

theorem pA_eq (l r c : Nat) : pA l r c = VG.Impl.MlDsa.X86_64.Verify.pS (20 + (l * r + c)) := by
  show VG.Impl.MlDsa.X86_64.Verify.pS (20 + l * r + c) = _
  rw [Nat.add_assoc]

theorem l_pos : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, 0 < p.ℓ := by decide

/-- Entry `e < kℓ` is `Â[e / ℓ, e mod ℓ]`. -/
theorem entry_lt {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {e : Nat} (he : e < p.k * p.ℓ) : e / p.ℓ < p.k ∧ e % p.ℓ < p.ℓ :=
  ⟨(Nat.div_lt_iff_lt_mul (VG.Proof.MlDsa.X86_64.Verify.l_pos p hp)).mpr he, Nat.mod_lt _ (VG.Proof.MlDsa.X86_64.Verify.l_pos p hp)⟩

theorem done_all {p : Params} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) : VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ (p.k * p.ℓ) r c := by
  unfold VG.Proof.MlDsa.X86_64.Verify.Done
  have := Nat.mul_le_mul_left p.ℓ (show r + 1 ≤ p.k by omega)
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm p.ℓ p.k] at this
  omega

/-- After the first `e` entries of `Â`, with the hint `h`. -/
structure S3 (p : Params) (h : List (Vector Bool n)) (e : Nat) (σ st : State) : Prop where
  t : VG.Proof.MlDsa.X86_64.Verify.T p σ st
  hint : HintIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pZ i)) (toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i))
  rho : bytesAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB)) 32 = vRho (VG.Proof.MlDsa.X86_64.Verify.vPk p σ)
  rho4 : ∀ k < 4, bytesAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k))) 32 = vRho (VG.Proof.MlDsa.X86_64.Verify.vPk p σ)
  red : ∀ r' < p.k, ∀ c' < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ e r' c' → Reduced st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pA p.ℓ r' c'))
  ok : ∃ q : Bool, st.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (q = true) ∧
    (q = true → ∀ r' < p.k, ∀ c' < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ e r' c' →
      ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r' c') = some (polyAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pA p.ℓ r' c')))) ∧
    (q = false → ∃ r' < p.k, ∃ c' < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ e r' c' ∧ rejNTTPoly minBounds.rejNTT (aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r' c') = none)

abbrev wsB : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat) := [(VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 32), 1), (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 33), 1)]
abbrev wsA (e : Nat) : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat) := [(VG.Impl.MlDsa.X86_64.Verify.pS (20 + e), 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 2048)]

/-- A state keeps what `S3` says across a piece that writes `ws`. -/
def keepChk (p : Params) (ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.tChk p ws && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pH 0) (1024 * p.k) && (List.range p.ℓ).all (fun i => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pZ i) 1024)

/-- The facts about the parameters entry `e` needs. -/
def aChk (p : Params) (e : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 32)) 1 && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 33)) 1 && VG.Proof.MlDsa.X86_64.Verify.rejChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e)) &&
    VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e)) 1024 && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e)) 1024 && VG.Proof.MlDsa.X86_64.Verify.keepChk p VG.Proof.MlDsa.X86_64.Verify.wsB && VG.Proof.MlDsa.X86_64.Verify.keepChk p (VG.Proof.MlDsa.X86_64.Verify.wsA e) &&
    VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) VG.Proof.MlDsa.X86_64.Verify.wsB (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 32 && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsA e) (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 32 &&
    (List.range p.k).all (fun r' => (List.range p.ℓ).all fun c' => !decide (p.ℓ * r' + c' < e) ||
      (VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) VG.Proof.MlDsa.X86_64.Verify.wsB (pA p.ℓ r' c') 1024 && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsA e) (pA p.ℓ r' c') 1024)) &&
    (List.range 4).all (fun k => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) VG.Proof.MlDsa.X86_64.Verify.wsB (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k)) 32 &&
      VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsA e) (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k)) 32)

theorem aChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, ∀ e < p.k * p.ℓ, VG.Proof.MlDsa.X86_64.Verify.aChk p e = true := by decide +kernel


theorem keepChk_spec {p : Params} {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (h : VG.Proof.MlDsa.X86_64.Verify.keepChk p ws = true) :
    VG.Proof.MlDsa.X86_64.Verify.tChk p ws = true ∧ VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pH 0) (1024 * p.k) = true ∧ ∀ i < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pZ i) 1024 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.keepChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem setB2At_ok {p : Params} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay (VG.Proof.MlDsa.X86_64.Verify.vR p) (VG.Proof.MlDsa.X86_64.Verify.vW p) s) (B : Nat)
    (h32 : VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (B + 32)) 1 = true)
    (h33 : VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (B + 33)) 1 = true) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    WP isa (.block (VG.Impl.MlDsa.X86_64.Verify.setB (VG.Impl.MlDsa.X86_64.Verify.sc (B + 32)) x ++ VG.Impl.MlDsa.X86_64.Verify.setB (VG.Impl.MlDsa.X86_64.Verify.sc (B + 33)) y)) s fun s' =>
      VG.Proof.MlDsa.X86_64.Verify.PPostB s s' [(VG.Impl.MlDsa.X86_64.Verify.sc (B + 32), 1), (VG.Impl.MlDsa.X86_64.Verify.sc (B + 33), 1)] ∧
      s'.gpr .r15 = s.gpr .r15 ∧
      s'.mem = (s.mem.writeW (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc B) + BitVec.ofNat 64 32) (BitVec.ofNat 8 x)).writeW
        (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc B) + BitVec.ofNat 64 33) (BitVec.ofNat 8 y) := by
  have e32 : VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc (B + 32)) = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc B) + BitVec.ofNat 64 32 := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have e33 : VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc (B + 33)) = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc B) + BitVec.ofNat 64 33 := by
    simp only [VG.Proof.MlDsa.X86_64.Verify.pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.setB_ok _ x (show Reg.rbx ≠ .rax by decide) hx s (L.inW h32)) fun s₁ ⟨hm₁, k₁⟩ => ?_
  have e₁ : VG.Proof.MlDsa.X86_64.Verify.pa s₁ (VG.Impl.MlDsa.X86_64.Verify.sc (B + 33)) = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc (B + 33)) := by simp only [VG.Proof.MlDsa.X86_64.Verify.pa]; rw [k₁.gpr (by decide)]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.setB_ok _ y (show Reg.rbx ≠ .rax by decide) hy s₁ (by rw [k₁.2.2, e₁]; exact L.inW h33)) fun s₂ ⟨hm₂, k₂⟩ =>
    ⟨VG.Proof.MlDsa.X86_64.Verify.postB_of_keep (k₁.trans k₂) (by decide) ?_, by rw [k₂.gpr (by decide), k₁.gpr (by decide)], ?_⟩
  · rw [hm₂, hm₁, e₁]
    have hc : ∀ q : VG.Impl.MlDsa.X86_64.Verify.Ptr, (Region.mk (VG.Proof.MlDsa.X86_64.Verify.pa s q) 1).Contains (VG.Proof.MlDsa.X86_64.Verify.pa s q) 1 := fun q => Region.contains_self _ _
    exact ((Frame.refl _ _).writeW (List.mem_cons_self ..) _ (hc _)).writeW
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (hc _)
  · rw [hm₂, hm₁, e₁, e32, e33]

theorem setB2_ok {p : Params} {s : State} (L : VG.Proof.MlDsa.X86_64.Verify.Lay (VG.Proof.MlDsa.X86_64.Verify.vR p) (VG.Proof.MlDsa.X86_64.Verify.vW p) s) (h32 : VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 32)) 1 = true)
    (h33 : VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 33)) 1 = true) (x y : Nat) (hx : x < 256) (hy : y < 256) :
    WP isa (.block (VG.Impl.MlDsa.X86_64.Verify.setB (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 32)) x ++ VG.Impl.MlDsa.X86_64.Verify.setB (VG.Impl.MlDsa.X86_64.Verify.sc (VG.Impl.MlDsa.X86_64.Verify.oSB + 33)) y)) s fun s' => VG.Proof.MlDsa.X86_64.Verify.PPostB s s' VG.Proof.MlDsa.X86_64.Verify.wsB ∧
      s'.gpr .r15 = s.gpr .r15 ∧
      s'.mem = (s.mem.writeW (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) + BitVec.ofNat 64 32) (BitVec.ofNat 8 x)).writeW
        (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) + BitVec.ofNat 64 33) (BitVec.ofNat 8 y) :=
  VG.Proof.MlDsa.X86_64.Verify.setB2At_ok L VG.Impl.MlDsa.X86_64.Verify.oSB h32 h33 x y hx hy

theorem kl_le : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, p.ℓ ≤ 7 ∧ p.k ≤ 8 := by decide

theorem done_succ {l e r' c' : Nat} : VG.Proof.MlDsa.X86_64.Verify.Done l (e + 1) r' c' ↔ VG.Proof.MlDsa.X86_64.Verify.Done l e r' c' ∨ l * r' + c' = e := by
  unfold VG.Proof.MlDsa.X86_64.Verify.Done; omega

theorem aOne_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {e : Nat} (he : e < p.k * p.ℓ) {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S3 p h e σ s) :
    WP isa (aOne P p e) s (VG.Proof.MlDsa.X86_64.Verify.S3 p h (e + 1) σ) := by
  have hck := VG.Proof.MlDsa.X86_64.Verify.aChk_all p hp e he
  have hkl := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp
  obtain ⟨hr, hc⟩ := VG.Proof.MlDsa.X86_64.Verify.entry_lt hp he
  simp only [VG.Proof.MlDsa.X86_64.Verify.aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h32, h33⟩, hrej⟩, hin⟩, hwa⟩, kB⟩, kA⟩, kSB⟩, kSA⟩, kE⟩, k4⟩ := hck
  obtain ⟨tB, hB, zB⟩ := VG.Proof.MlDsa.X86_64.Verify.keepChk_spec kB
  obtain ⟨tA, hA, zA⟩ := VG.Proof.MlDsa.X86_64.Verify.keepChk_spec kA
  have L := hs.t.lay hp hv
  unfold aOne
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.setB2_ok L h32 h33 (e % p.ℓ) (e / p.ℓ) (by omega) (by omega))
    fun s₁ ⟨hP₁, h15₁, hm₁⟩ => ?_)
  have t₁ := hs.t.step hp hv hP₁ tB
  have L₁ := t₁.lay hp hv
  have hseed : bytesAt s₁.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₁ (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB)) 34 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (e / p.ℓ) (e % p.ℓ) := by
    rw [hP₁.pa (by decide), hm₁, VG.Proof.MlDsa.X86_64.Verify.seed_bytes, hs.rho, aSeed, VG.Proof.MlDsa.X86_64.Verify.integerToBytes_one, VG.Proof.MlDsa.X86_64.Verify.integerToBytes_one]
  obtain ⟨q, h15, hok, hbad⟩ := hs.ok
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.sampled_ok L₁ hin hwa (h15₁.trans h15) (List.mem_cons_self ..)
    (WP.mono (VG.Proof.MlDsa.X86_64.Verify.rejNttAt_ok C.rejNtt L₁ hrej) fun s' ⟨hP, h15', hr', ho⟩ => ⟨hP, h15', hr', ho⟩))
    fun s₂ ⟨hP₂, hred, rr, hrr, h15₂, hs1, hs0⟩ => ?_
  rw [hseed] at hs1 hs0
  have hPA : ∀ r' c', c' < p.ℓ → p.ℓ * r' + c' = e →
      VG.Proof.MlDsa.X86_64.Verify.pa s₂ (pA p.ℓ r' c') = VG.Proof.MlDsa.X86_64.Verify.pa s₁ (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e)) ∧ r' = e / p.ℓ ∧ c' = e % p.ℓ := fun r' c' hc' he' =>
    ⟨by rw [hP₂.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide), VG.Proof.MlDsa.X86_64.Verify.pA_eq, he'], VG.Proof.MlDsa.X86_64.Verify.rc_eq hc' he'⟩
  refine ⟨t₁.step hp hv hP₂ tA, L₁.keepHint hP₂ hA (L.keepHint hP₁ hB hs.hint),
    fun i hi => L₁.keepPoly hP₂ (zA i hi) (L.keepPoly hP₁ (zB i hi) (hs.z i hi)),
    by rw [L₁.keepBytes hP₂ kSA, L.keepBytes hP₁ kSB, hs.rho],
    fun k hk => by rw [L₁.keepBytes hP₂ (k4 k hk).2, L.keepBytes hP₁ (k4 k hk).1, hs.rho4 k hk],
    fun r' hr' c' hc' hd => ?_,
    ⟨q && (rr == 1), ?_, fun hq r' hr' c' hc' hd => ?_, fun hq => ?_⟩⟩
  · rcases done_succ.mp hd with hd | he'
    · have := kE r' hr' c' hc'
      rw [or_iff_right (by unfold VG.Proof.MlDsa.X86_64.Verify.Done at hd; omega)] at this
      exact L₁.keepRed hP₂ this.2 (L.keepRed hP₁ this.1 (hs.red r' hr' c' hc' hd))
    · rw [(hPA r' c' hc' he').1]; exact hred
  · rw [h15₂]
    exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by cases q <;> simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    rcases done_succ.mp hd with hd | he'
    · have := kE r' hr' c' hc'
      rw [or_iff_right (by unfold VG.Proof.MlDsa.X86_64.Verify.Done at hd; omega)] at this
      obtain ⟨b, hb⟩ := hok hq.1 r' hr' c' hc' hd
      exact ⟨b, by rw [hb, L₁.keepPolyAt hP₂ this.2, L.keepPolyAt hP₁ this.1]⟩
    · obtain ⟨e1, e2, e3⟩ := hPA r' c' hc' he'
      obtain ⟨b, hb⟩ := hs1 hq.2
      refine ⟨b, ?_⟩
      rw [e1, e2, e3]
      exact hb
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', hd, hn⟩ := hbad hq'
      exact ⟨r', hr', c', hc', done_succ.mpr (.inl hd), hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      exact ⟨e / p.ℓ, hr, e % p.ℓ, hc, done_succ.mpr (.inr (Nat.div_add_mod e p.ℓ)), hs0 h0⟩

/-! ## Four entries at a time -/

/-- A piece writing `ws` keeps the entries done before `e` but those `ex` says, and `S3`'s other facts. -/
def s3Chk (p : Params) (e : Nat) (ex : Nat → Nat → Bool) (ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.keepChk p ws && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 32 && (List.range 4).all (fun k => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k)) 32) &&
    (List.range p.k).all (fun r' => (List.range p.ℓ).all fun c' =>
      !decide (p.ℓ * r' + c' < e) || ex r' c' || keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pA p.ℓ r' c') 1024)

theorem s3Chk_spec {p : Params} {e : Nat} {ex : Nat → Nat → Bool} {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)}
    (h : VG.Proof.MlDsa.X86_64.Verify.s3Chk p e ex ws = true) :
    VG.Proof.MlDsa.X86_64.Verify.keepChk p ws = true ∧ VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 32 = true ∧
      (∀ k < 4, VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k)) 32 = true) ∧
      ∀ r' < p.k, ∀ c' < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ e r' c' → ex r' c' = false → VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pA p.ℓ r' c') 1024 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.s3Chk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, fun k hk => List.all_eq_true.mp h3 k (List.mem_range.mpr hk), fun r' hr' c' hc' hd hx => ?_⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp h4 r' (List.mem_range.mpr hr')) c' (List.mem_range.mpr hc')
  rw [decide_eq_true (show p.ℓ * r' + c' < e from hd), hx] at this
  simpa using this

/-- `S3` across a piece that writes `ws`, which `s3Chk` says keeps it. -/
theorem S3.keep {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) {h : List (Vector Bool n)} {e : Nat}
    {s s' : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S3 p h e σ s) {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws)
    (h15 : s'.gpr .r15 = s.gpr .r15) (hc : VG.Proof.MlDsa.X86_64.Verify.s3Chk p e (fun _ _ => false) ws = true) : VG.Proof.MlDsa.X86_64.Verify.S3 p h e σ s' := by
  obtain ⟨hk, kSB, k4, kE⟩ := VG.Proof.MlDsa.X86_64.Verify.s3Chk_spec hc
  obtain ⟨tk, hh, zk⟩ := VG.Proof.MlDsa.X86_64.Verify.keepChk_spec hk
  have L := hs.t.lay hp hv
  obtain ⟨q, hq, hok, hbad⟩ := hs.ok
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hh hs.hint, fun i hi => L.keepPoly hP (zk i hi) (hs.z i hi),
    by rw [L.keepBytes hP kSB, hs.rho], fun k hk => by rw [L.keepBytes hP (k4 k hk), hs.rho4 k hk],
    fun r' hr' c' hc' hd => L.keepRed hP (kE r' hr' c' hc' hd rfl) (hs.red r' hr' c' hc' hd),
    q, by rw [h15, hq], fun hq' r' hr' c' hc' hd => ?_, hbad⟩
  obtain ⟨b, hb⟩ := hok hq' r' hr' c' hc' hd
  exact ⟨b, by rw [hb, L.keepPolyAt hP (kE r' hr' c' hc' hd rfl)]⟩

/-- The two bytes of seed `j` of `SB4`. -/
abbrev wsS (j : Nat) : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat) := [(VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j + 32), 1), (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j + 33), 1)]

/-- What setting the bytes of seed `j` needs, after `e` entries. -/
def slotChk (p : Params) (e j : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j + 32)) 1 && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j + 33)) 1 &&
    VG.Proof.MlDsa.X86_64.Verify.s3Chk p e (fun _ _ => false) (VG.Proof.MlDsa.X86_64.Verify.wsS j) &&
    (List.range j).all (fun k => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsS j) (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k)) 34)

/-- After the bytes of the first `j` seeds of `SB4`, for the entries `e + k`. -/
structure GS (p : Params) (h : List (Vector Bool n)) (e j : Nat) (σ st : State) : Prop where
  s3 : VG.Proof.MlDsa.X86_64.Verify.S3 p h e σ st
  done : ∀ k < j, bytesAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k))) 34 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + k) / p.ℓ) ((e + k) % p.ℓ)

theorem slot_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) {h : List (Vector Bool n)}
    {e j : Nat} (hj : j < 4) (he : e + j < p.k * p.ℓ) (hck : VG.Proof.MlDsa.X86_64.Verify.slotChk p e j = true) {s : State}
    (hs : VG.Proof.MlDsa.X86_64.Verify.GS p h e j σ s) : WP isa (.block (setSR p e j)) s (VG.Proof.MlDsa.X86_64.Verify.GS p h e (j + 1) σ) := by
  have hkl := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp
  obtain ⟨hr, hc⟩ := VG.Proof.MlDsa.X86_64.Verify.entry_lt hp he
  simp only [VG.Proof.MlDsa.X86_64.Verify.slotChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hck
  obtain ⟨⟨⟨h32, h33⟩, h3⟩, hk⟩ := hck
  have L := hs.s3.t.lay hp hv
  unfold setSR
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.setB2At_ok L (oSB4 + 34 * j) h32 h33 ((e + j) % p.ℓ) ((e + j) / p.ℓ) (by omega) (by omega))
    fun s₁ ⟨hP₁, h15₁, hm₁⟩ => ⟨hs.s3.keep hp hv hP₁ h15₁ h3, fun k hk' => ?_⟩
  rcases (by omega : k < j ∨ k = j) with hk' | rfl
  · rw [L.keepBytes hP₁ (hk k hk'), hs.done k hk']
  · rw [hP₁.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide), hm₁, VG.Proof.MlDsa.X86_64.Verify.seed_bytes, hs.s3.rho4 k hj, aSeed, VG.Proof.MlDsa.X86_64.Verify.integerToBytes_one,
      VG.Proof.MlDsa.X86_64.Verify.integerToBytes_one]

/-- Whether entry `(r', c')` is one of the four from `e`. -/
abbrev inGrp (l e r' c' : Nat) : Bool := decide (e ≤ l * r' + c') && decide (l * r' + c' < e + 4)

/-- The facts about the parameters the entries `e, …, e + 3` need. -/
def gChk (p : Params) (e : Nat) : Bool :=
  (List.range 4).all (fun j => VG.Proof.MlDsa.X86_64.Verify.slotChk p e j) && VG.Proof.MlDsa.X86_64.Verify.rej4Chk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e)) (VG.Impl.MlDsa.X86_64.Verify.sc (oR4 p)) &&
    VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e)) 4096 && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e)) 4096 &&
    VG.Proof.MlDsa.X86_64.Verify.s3Chk p e (VG.Proof.MlDsa.X86_64.Verify.inGrp p.ℓ e) [(VG.Impl.MlDsa.X86_64.Verify.pS (20 + e), 4096), (VG.Impl.MlDsa.X86_64.Verify.sc (oR4 p), 8192)] && decide (e + 4 ≤ p.k * p.ℓ)

theorem gChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, ∀ g < p.k * p.ℓ / 4, VG.Proof.MlDsa.X86_64.Verify.gChk p (4 * g) = true := by decide +kernel

theorem pa_poly4 (s : State) (e k : Nat) : VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.pS (20 + e))) k = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.pS (20 + (e + k))) := by
  unfold VG.Spec.MlDsa.poly4
  simp only [VG.Proof.MlDsa.X86_64.Verify.pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show VG.Impl.MlDsa.X86_64.Verify.oP (20 + e) + 1024 * k = VG.Impl.MlDsa.X86_64.Verify.oP (20 + (e + k)) by
    simp only [VG.Impl.MlDsa.X86_64.Verify.oP]; omega]

theorem aGrp_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {g : Nat} (hck : VG.Proof.MlDsa.X86_64.Verify.gChk p (4 * g) = true) {s : State}
    (hs : VG.Proof.MlDsa.X86_64.Verify.S3 p h (4 * g) σ s) : WP isa (aGrp P p g) s (VG.Proof.MlDsa.X86_64.Verify.S3 p h (4 * (g + 1)) σ) := by
  have hkl := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.gChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hsl, hrej⟩, hin⟩, hwa⟩, hG⟩, hl⟩ := hck
  obtain ⟨hk, kSB, k4, kE⟩ := VG.Proof.MlDsa.X86_64.Verify.s3Chk_spec hG
  obtain ⟨tk, hh, zk⟩ := VG.Proof.MlDsa.X86_64.Verify.keepChk_spec hk
  unfold aGrp
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.slot_ok hp hv (by decide) (by omega) (hsl 0 (by decide))
    ⟨hs, fun _ h => absurd h (by omega)⟩) fun _ g₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.slot_ok hp hv (by decide) (by omega) (hsl 1 (by decide)) g₁) fun _ g₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.slot_ok hp hv (by decide) (by omega) (hsl 2 (by decide)) g₂) fun _ g₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.slot_ok hp hv (by decide) (by omega) (hsl 3 (by decide)) g₃) fun s₄ g₄ => ?_)
  have L₄ := g₄.s3.t.lay hp hv
  obtain ⟨q, h15, hok, hbad⟩ := g₄.s3.ok
  have hseed : ∀ k < 4, seed4 s₄.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₄ (VG.Impl.MlDsa.X86_64.Verify.sc oSB4)) k =
      aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((4 * g + k) / p.ℓ) ((4 * g + k) % p.ℓ) := fun k hk => by
    unfold seed4
    rw [show VG.Proof.MlDsa.X86_64.Verify.pa s₄ (VG.Impl.MlDsa.X86_64.Verify.sc oSB4) + BitVec.ofNat 64 (34 * k) = VG.Proof.MlDsa.X86_64.Verify.pa s₄ (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k)) by
      simp only [VG.Proof.MlDsa.X86_64.Verify.pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
    exact g₄.done k hk
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.sampled4_ok L₄ hin hwa h15 (List.mem_cons_self ..)
    (F := fun k b => rejNTTPoly b.rejNTT (aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((4 * g + k) / p.ℓ) ((4 * g + k) % p.ℓ)))
    (WP.mono (VG.Proof.MlDsa.X86_64.Verify.rej4At_ok C.rej4 L₄ hrej) fun s' ⟨hP, h15', hred, ho⟩ => ⟨hP, h15', hred, ?_⟩))
    fun s₅ ⟨hP₅, hred₅, rr, hrr, h15₅, hs1, hs0⟩ => ?_
  · rcases ho with ⟨h1, hb⟩ | ⟨h0, k, hk, hn⟩
    · exact .inl ⟨h1, fun k hk => by rw [← hseed k hk]; exact hb k hk⟩
    · exact .inr ⟨h0, k, hk, by rw [← hseed k hk]; exact hn⟩
  have e₅ : ∀ k, VG.Spec.MlDsa.poly4 (VG.Proof.MlDsa.X86_64.Verify.pa s₄ (VG.Impl.MlDsa.X86_64.Verify.pS (20 + 4 * g))) k = VG.Proof.MlDsa.X86_64.Verify.pa s₅ (VG.Impl.MlDsa.X86_64.Verify.pS (20 + (4 * g + k))) := fun k => by
    rw [VG.Proof.MlDsa.X86_64.Verify.pa_poly4, hP₅.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide)]
  have hgrp : ∀ r' c', VG.Proof.MlDsa.X86_64.Verify.inGrp p.ℓ (4 * g) r' c' = true → 4 * g ≤ p.ℓ * r' + c' ∧ p.ℓ * r' + c' < 4 * g + 4 :=
    fun r' c' hg => by simp only [VG.Proof.MlDsa.X86_64.Verify.inGrp, Bool.and_eq_true, decide_eq_true_eq] at hg; exact hg
  have hout : ∀ r' c', VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ (4 * (g + 1)) r' c' → VG.Proof.MlDsa.X86_64.Verify.inGrp p.ℓ (4 * g) r' c' = false → VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ (4 * g) r' c' :=
    fun r' c' hd hx => by
      simp only [VG.Proof.MlDsa.X86_64.Verify.inGrp, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hx
      unfold VG.Proof.MlDsa.X86_64.Verify.Done at hd ⊢
      omega
  refine ⟨g₄.s3.t.step hp hv hP₅ tk, L₄.keepHint hP₅ hh g₄.s3.hint,
    fun i hi => L₄.keepPoly hP₅ (zk i hi) (g₄.s3.z i hi), by rw [L₄.keepBytes hP₅ kSB, g₄.s3.rho],
    fun k hk => by rw [L₄.keepBytes hP₅ (k4 k hk), g₄.s3.rho4 k hk], fun r' hr' c' hc' hd => ?_,
    q && (rr == 1), ?_, fun hq r' hr' c' hc' hd => ?_, fun hq => ?_⟩
  · cases hx : VG.Proof.MlDsa.X86_64.Verify.inGrp p.ℓ (4 * g) r' c'
    · exact L₄.keepRed hP₅ (kE r' hr' c' hc' (hout r' c' hd hx) hx) (g₄.s3.red r' hr' c' hc' (hout r' c' hd hx))
    · obtain ⟨g1, g2⟩ := hgrp r' c' hx
      have := hred₅ (p.ℓ * r' + c' - 4 * g) (by omega)
      rwa [e₅, show 4 * g + (p.ℓ * r' + c' - 4 * g) = p.ℓ * r' + c' by omega, ← VG.Proof.MlDsa.X86_64.Verify.pA_eq] at this
  · rw [h15₅]
    exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by cases q <;> simp)
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    cases hx : VG.Proof.MlDsa.X86_64.Verify.inGrp p.ℓ (4 * g) r' c'
    · obtain ⟨b, hb⟩ := hok hq.1 r' hr' c' hc' (hout r' c' hd hx)
      exact ⟨b, by rw [hb, L₄.keepPolyAt hP₅ (kE r' hr' c' hc' (hout r' c' hd hx) hx)]⟩
    · obtain ⟨g1, g2⟩ := hgrp r' c' hx
      obtain ⟨b, hb⟩ := hs1 hq.2 (p.ℓ * r' + c' - 4 * g) (by omega)
      obtain ⟨er, ec⟩ := VG.Proof.MlDsa.X86_64.Verify.rc_eq hc' (show p.ℓ * r' + c' = 4 * g + (p.ℓ * r' + c' - 4 * g) by omega)
      rw [← er, ← ec, e₅, show 4 * g + (p.ℓ * r' + c' - 4 * g) = p.ℓ * r' + c' by omega, ← VG.Proof.MlDsa.X86_64.Verify.pA_eq] at hb
      exact ⟨b, hb⟩
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', hd, hn⟩ := hbad hq'
      exact ⟨r', hr', c', hc', by unfold VG.Proof.MlDsa.X86_64.Verify.Done at hd ⊢; omega, hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      obtain ⟨k, hk, hn⟩ := hs0 h0
      obtain ⟨hr, hc⟩ := VG.Proof.MlDsa.X86_64.Verify.entry_lt hp (show 4 * g + k < p.k * p.ℓ by omega)
      exact ⟨_, hr, _, hc, by unfold VG.Proof.MlDsa.X86_64.Verify.Done; have := Nat.div_add_mod (4 * g + k) p.ℓ; omega, hn⟩

/-- After the samplers, with the hint `h`. -/
structure S4 (p : Params) (h : List (Vector Bool n)) (σ st : State) : Prop where
  t : VG.Proof.MlDsa.X86_64.Verify.T p σ st
  hint : HintIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pZ i)) (toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i))
  red : ∀ r < p.k, ∀ c < p.ℓ, Reduced st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pA p.ℓ r c))
  redC : Reduced st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st pC)
  ok : ∃ q : Bool, st.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (q = true) ∧
    (q = true → (∀ r < p.k, ∀ c < p.ℓ,
      ∃ b : Bounds, rejNTTPoly b.rejNTT (aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r c) = some (polyAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pA p.ℓ r c)))) ∧
      ∃ b : Bounds, (VG.Spec.MlDsa.sampleInBall p.τ b.ball (vCt p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ))).map toRq = some (polyAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st pC))) ∧
    (q = false → (∃ r < p.k, ∃ c < p.ℓ, rejNTTPoly minBounds.rejNTT (aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r c) = none) ∨
      (VG.Spec.MlDsa.sampleInBall p.τ minBounds.ball (vCt p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ))).map toRq = none)

abbrev wsC : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat) := [(pC, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 2048)]

/-- The facts about the parameters the copy of `ρ` and `c` need. -/
def sChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (.rbp, 0) 32 (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 32 && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 32 && VG.Proof.MlDsa.X86_64.Verify.keepChk p [(VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB, 32)] &&
    decide (32 ≤ p.pkLen) && VG.Proof.MlDsa.X86_64.Verify.ballChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (.r13, 0) p.ctildeLen pC &&
    decide ((p.ctildeLen, p.τ) ∈ ballParams) && decide (p.ctildeLen ≤ p.sigLen) && VG.Proof.MlDsa.X86_64.Verify.keepChk p VG.Proof.MlDsa.X86_64.Verify.wsC &&
    VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) pC 1024 && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) pC 1024 &&
    (List.range p.k).all (fun r => (List.range p.ℓ).all fun c => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) VG.Proof.MlDsa.X86_64.Verify.wsC (pA p.ℓ r c) 1024)

theorem sChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, VG.Proof.MlDsa.X86_64.Verify.sChk p = true := by decide +kernel

/-- After `ρ` is copied to `SB` and the first `j` seeds of `SB4`. -/
structure RhoS (p : Params) (h : List (Vector Bool n)) (j : Nat) (σ st : State) : Prop where
  t : VG.Proof.MlDsa.X86_64.Verify.T p σ st
  hint : HintIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pH 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pZ i)) (toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i))
  rho : bytesAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB)) 32 = vRho (VG.Proof.MlDsa.X86_64.Verify.vPk p σ)
  rho4 : ∀ k < j, bytesAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k))) 32 = vRho (VG.Proof.MlDsa.X86_64.Verify.vPk p σ)
  f15 : st.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True

theorem copyRho_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.copy (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) (.rbp, 0) 32) s (VG.Proof.MlDsa.X86_64.Verify.RhoS p h 0 σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.sChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  obtain ⟨t3, h3, z3⟩ := VG.Proof.MlDsa.X86_64.Verify.keepChk_spec c3
  have L := hs.t.lay hp hv
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.copy_ok L (by decide) c1 c2) fun s₁ ⟨hP₁, h15₁, hcp⟩ => ?_
  have t₁ := hs.t.step hp hv hP₁ t3
  refine ⟨t₁, L.keepHint hP₁ h3 hs.hint, fun i hi => L.keepPoly hP₁ (z3 i hi) (hs.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h15₁, h15]⟩
  rw [hP₁.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide), hcp, hs.t.pkSlice c4, List.drop_zero]
  rfl

/-- What copying `ρ` to seed `j` of `SB4` needs. -/
def rChk (p : Params) (j : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.sepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (.rbp, 0) 32 (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j)) 32 && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vW p) (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j)) 32 &&
    VG.Proof.MlDsa.X86_64.Verify.keepChk p [(VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j), 32)] && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [(VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j), 32)] (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSB) 32 &&
    (List.range j).all (fun k => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [(VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j), 32)] (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * k)) 32)

theorem rChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, ∀ j < 4, VG.Proof.MlDsa.X86_64.Verify.rChk p j = true := by decide +kernel

theorem copyK_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) {h : List (Vector Bool n)} {j : Nat}
    (hj : j < 4) {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.RhoS p h j σ s) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.copy (VG.Impl.MlDsa.X86_64.Verify.sc (oSB4 + 34 * j)) (.rbp, 0) 32) s (VG.Proof.MlDsa.X86_64.Verify.RhoS p h (j + 1) σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.rChk_all p hp j hj
  simp only [VG.Proof.MlDsa.X86_64.Verify.rChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩ := hc
  have hpk : 32 ≤ p.pkLen := by
    have := VG.Proof.MlDsa.X86_64.Verify.sChk_all p hp
    simp only [VG.Proof.MlDsa.X86_64.Verify.sChk, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1.1.1.1.1.2
  obtain ⟨t3, h3, z3⟩ := VG.Proof.MlDsa.X86_64.Verify.keepChk_spec c3
  have L := hs.t.lay hp hv
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.copy_ok L (by decide) c1 c2) fun s₁ ⟨hP₁, h15₁, hcp⟩ => ?_
  refine ⟨hs.t.step hp hv hP₁ t3, L.keepHint hP₁ h3 hs.hint, fun i hi => L.keepPoly hP₁ (z3 i hi) (hs.z i hi),
    by rw [L.keepBytes hP₁ c4, hs.rho], fun k hk => ?_, by rw [h15₁, hs.f15]⟩
  rcases (by omega : k < j ∨ k = j) with hk | rfl
  · rw [L.keepBytes hP₁ (c5 k hk), hs.rho4 k hk]
  · rw [hP₁.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide), hcp, hs.t.pkSlice hpk, List.drop_zero]
    rfl

theorem RhoS.s3 {p : Params} {h : List (Vector Bool n)} {σ s : State} (r : VG.Proof.MlDsa.X86_64.Verify.RhoS p h 4 σ s) : VG.Proof.MlDsa.X86_64.Verify.S3 p h 0 σ s :=
  ⟨r.t, r.hint, r.z, r.rho, r.rho4, fun r' _ c' _ hd => absurd hd (by unfold VG.Proof.MlDsa.X86_64.Verify.Done; omega),
    true, by rw [r.f15]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp), fun _ r' _ c' _ hd => absurd hd (by unfold VG.Proof.MlDsa.X86_64.Verify.Done; omega),
    fun hq => absurd hq (by simp)⟩

theorem rhos_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True) :
    WP isa rhos s (VG.Proof.MlDsa.X86_64.Verify.S3 p h 0 σ) := by
  unfold rhos
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyRho_ok hp hv hs h15) fun s₀ r₀ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyK_ok hp hv (j := 0) (by decide) r₀) fun s₁ r₁ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyK_ok hp hv (j := 1) (by decide) r₁) fun s₂ r₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyK_ok hp hv (j := 2) (by decide) r₂) fun s₃ r₃ => ?_)
  exact WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyK_ok hp hv (j := 3) (by decide) r₃) fun _ r₄ => r₄.s3

theorem ballStage_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {s₂ : State} (hs₂ : VG.Proof.MlDsa.X86_64.Verify.S3 p h (p.k * p.ℓ) σ s₂) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.sampled (VG.Impl.MlDsa.X86_64.Verify.ballAt P (.r13, 0) p.ctildeLen p.τ pC) pC) s₂ (VG.Proof.MlDsa.X86_64.Verify.S4 p h σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.sChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩ := hc
  obtain ⟨t8, h8, z8⟩ := VG.Proof.MlDsa.X86_64.Verify.keepChk_spec c8
  have L₂ := hs₂.t.lay hp hv
  obtain ⟨q, h15₂, hok, hbad⟩ := hs₂.ok
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.sampled_ok L₂ c9 c10 h15₂ (List.mem_cons_self ..)
    (WP.mono (VG.Proof.MlDsa.X86_64.Verify.ballAt_ok C.ball L₂ c6 c5) fun s' ⟨hP, h15', hr', ho⟩ => ⟨hP, h15', hr', ho⟩))
    fun s₃ ⟨hP₃, hred, rr, hrr, h15₃, hs1, hs0⟩ => ?_
  have hct : bytesAt s₂.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₂ (.r13, 0)) p.ctildeLen = vCt p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) := by
    rw [hs₂.t.sigSlice (by omega), List.drop_zero]; rfl
  rw [hct] at hs1 hs0
  have hdone : ∀ r' c', r' < p.k → c' < p.ℓ → VG.Proof.MlDsa.X86_64.Verify.Done p.ℓ (p.k * p.ℓ) r' c' := fun _ _ hr hc => VG.Proof.MlDsa.X86_64.Verify.done_all hr hc
  have ec : VG.Proof.MlDsa.X86_64.Verify.pa s₃ pC = VG.Proof.MlDsa.X86_64.Verify.pa s₂ pC := hP₃.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide)
  refine ⟨hs₂.t.step hp hv hP₃ t8, L₂.keepHint hP₃ h8 hs₂.hint, fun i hi => L₂.keepPoly hP₃ (z8 i hi) (hs₂.z i hi),
    fun r hr c hc => L₂.keepRed hP₃ (c11 r hr c hc) (hs₂.red r hr c hc (hdone r c hr hc)), by rw [ec]; exact hred,
    q && (rr == 1), by rw [h15₃]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by cases q <;> simp), fun hq => ?_, fun hq => ?_⟩
  · simp only [Bool.and_eq_true, beq_iff_eq] at hq
    refine ⟨fun r hr c hc => ?_, ?_⟩
    · obtain ⟨b, hb⟩ := hok hq.1 r hr c hc (hdone r c hr hc)
      exact ⟨b, by rw [hb, L₂.keepPolyAt hP₃ (c11 r hr c hc)]⟩
    · obtain ⟨b, hb⟩ := hs1 hq.2
      exact ⟨b, by rw [hb, ec]⟩
  · cases hq' : q
    · obtain ⟨r', hr', c', hc', _, hn⟩ := hbad hq'
      exact .inl ⟨r', hr', c', hc', hn⟩
    · rw [hq'] at hq
      have h0 : rr = 0 := by
        rcases hrr with h1 | h0
        · rw [h1] at hq; cases hq
        · exact h0
      exact .inr (hs0 h0)

theorem samples_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S2 p h p.ℓ σ s) (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.samples P p) s (VG.Proof.MlDsa.X86_64.Verify.S4 p h σ) := by
  unfold VG.Impl.MlDsa.X86_64.Verify.samples
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.rhos_ok hp hv hs h15) fun s₁ s₁3 => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.seqR_ok (I := fun g => VG.Proof.MlDsa.X86_64.Verify.S3 p h (4 * g) σ) (p.k * p.ℓ / 4) 0
    (fun g _ hg st hst => VG.Proof.MlDsa.X86_64.Verify.aGrp_ok C hp hv (VG.Proof.MlDsa.X86_64.Verify.gChk_all p hp g (by omega)) hst) s₁ s₁3) fun s₂ hs₂ => ?_)
  rw [Nat.zero_add] at hs₂
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.seqR_ok (I := fun e => VG.Proof.MlDsa.X86_64.Verify.S3 p h e σ) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4))
    (fun e _ he st hst => VG.Proof.MlDsa.X86_64.Verify.aOne_ok C hp hv (by omega) hst) s₂ hs₂) fun s₃ hs₃ => ?_)
  rw [Nat.div_add_mod] at hs₃
  exact VG.Proof.MlDsa.X86_64.Verify.ballStage_ok C hp hv hs₃

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.StageC`. -/
section

/-!
# ML-DSA verification on x86-64: `w′₁`, row by row

With the entries `A'` of `Â` and `ĉ = cH` as the samplers left them: `ẑ[i] =
NTT(z[i])` (`nttZ_ok`), `ĉ` (`nttC_ok`), and each row `r` of `w′₁`, packed to
`B + r · 32 bitlen b` (`row_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt vRho aSeed zHat dotAcc t1Hat wRow w1Row vT1 add_zero_left hintAt_row useHint_le)

/-- While computing, with the hint `h`, `Â = A'`, the result so far `Q`:
`ẑ[i]` for `i < j` (`z[i]` after), `ĉ` or `c` at `C` (`cH`), and the rows
of `w′₁` before `r` packed. -/
structure SC (p : Params) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (Q : Prop) [Decidable Q]
    (j : Nat) (cH : Poly) (r : Nat) (σ st : State) : Prop where
  t : VG.Proof.MlDsa.X86_64.Verify.T p σ st
  hint : HintIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pH 0)) p.k h
  a : ∀ r' < p.k, ∀ c < p.ℓ, PolyIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pA p.ℓ r' c)) (A' r' c)
  z : ∀ i < p.ℓ, PolyIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (pZ i)) (if i < j then VG.Proof.MlDsa.Verify.zHat p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i else toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i))
  c : PolyIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st pC) cH
  rows : ∀ r' < r, bytesAt st.mem (VG.Proof.MlDsa.X86_64.Verify.pa st (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r'))) (w1Len p) =
    VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) A' cH h r') (w1Max p)
  r15 : st.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag Q

/-- What a piece writing `ws` keeps of `SC`: `T`, the hint, `Â` and `z[i]`
but `z[ex]`, but for `C` and the rows. -/
def keepC (p : Params) (ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)) (ex : Nat) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.tChk p ws && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pH 0) (1024 * p.k) &&
    (List.range p.ℓ).all (fun i => i == ex || keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pZ i) 1024) &&
    (List.range p.k).all (fun r => (List.range p.ℓ).all fun c => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pA p.ℓ r c) 1024)

theorem keepC_spec {p : Params} {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} {ex : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.keepC p ws ex = true) :
    VG.Proof.MlDsa.X86_64.Verify.tChk p ws = true ∧ VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pH 0) (1024 * p.k) = true ∧
      (∀ i < p.ℓ, i ≠ ex → VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pZ i) 1024 = true) ∧
      ∀ r < p.k, ∀ c < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) ws (pA p.ℓ r c) 1024 = true := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.keepC, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, fun i hi hne => (h.1.2 i hi).resolve_left hne, h.2⟩

/-- The facts about the parameters the NTTs need. -/
def nttChk (p : Params) : Bool :=
  (List.range p.ℓ).all (fun i => VG.Proof.MlDsa.X86_64.Verify.ipChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (pZ i) && VG.Proof.MlDsa.X86_64.Verify.keepC p [(pZ i, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024)] i &&
    VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [(pZ i, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024)] pC 1024) &&
  VG.Proof.MlDsa.X86_64.Verify.ipChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pC && VG.Proof.MlDsa.X86_64.Verify.keepC p [(pC, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024)] 100

theorem nttChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, VG.Proof.MlDsa.X86_64.Verify.nttChk p = true := by decide +kernel

theorem nttZ_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {i : Nat} (hi : i < p.ℓ) {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q i cH 0 σ s) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.nttAt P (pZ i)) s (VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q (i + 1) cH 0 σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.nttChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨c1, c2⟩, c3⟩ := hc.1.1 i hi
  obtain ⟨tk, hH, hZ, hA⟩ := VG.Proof.MlDsa.X86_64.Verify.keepC_spec c2
  have L := hs.t.lay hp hv
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.ipAt_ok C.ntt L c1 (by have := hs.z i hi; rw [VG.Proof.MlKem.X86_64.ifn (Nat.lt_irrefl _)] at this; exact this.1))
    fun s' ⟨hP, h15, hq⟩ => ?_
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hH hs.hint, fun r' hr' c hc' => L.keepPoly hP (hA r' hr' c hc')
    (hs.a r' hr' c hc'), fun i' hi' => ?_, L.keepPoly hP c3 hs.c, fun _ h => absurd h (Nat.not_lt_zero _),
    by rw [h15]; exact hs.r15⟩
  rcases (by omega : i' < i ∨ i' = i ∨ i < i') with hlt | rfl | hgt
  · rw [VG.Proof.MlKem.X86_64.ifp (by omega : i' < i + 1)]
    have := L.keepPoly hP (hZ i' hi' (by omega)) (hs.z i' hi')
    rwa [VG.Proof.MlKem.X86_64.ifp hlt] at this
  · rw [VG.Proof.MlKem.X86_64.ifp (Nat.lt_succ_self _), hP.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide)]
    have := (hs.z i' hi').2
    rw [VG.Proof.MlKem.X86_64.ifn (Nat.lt_irrefl _)] at this
    rw [this] at hq
    exact hq
  · rw [VG.Proof.MlKem.X86_64.ifn (by omega : ¬ i' < i + 1)]
    have := L.keepPoly hP (hZ i' hi' (by omega)) (hs.z i' hi')
    rwa [VG.Proof.MlKem.X86_64.ifn (by omega : ¬ i' < i)] at this

theorem nttC_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ cH 0 σ s) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.nttAt P pC) s (VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ (VG.Spec.MlDsa.ntt cH) 0 σ) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.nttChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨_, c1⟩, c2⟩ := hc
  obtain ⟨tk, hH, hZ, hA⟩ := VG.Proof.MlDsa.X86_64.Verify.keepC_spec c2
  have L := hs.t.lay hp hv
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.ipAt_ok C.ntt L c1 hs.c.1) fun s' ⟨hP, h15, hq⟩ => ?_
  refine ⟨hs.t.step hp hv hP tk, L.keepHint hP hH hs.hint, fun r' hr' c hc' => L.keepPoly hP (hA r' hr' c hc')
    (hs.a r' hr' c hc'), fun i hi => L.keepPoly hP (hZ i hi (by have := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp; omega)) (hs.z i hi), ?_,
    fun _ h => absurd h (Nat.not_lt_zero _), by rw [h15]; exact hs.r15⟩
  rw [hP.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide), ← hs.c.2]
  exact hq


/-! ## A row -/

/-- What row `r` writes. -/
abbrev wsR (p : Params) (r : Nat) : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat) :=
  [(pW, 1024), (pT, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024), (pT2, 1024), (pW1, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r), w1Len p)]

/-- The facts about the parameters row `r` needs. -/
def rowChk (p : Params) (r : Nat) : Bool :=
  (List.range p.ℓ).all (fun c => VG.Proof.MlDsa.X86_64.Verify.mulChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW (pA p.ℓ r c) (pZ c)) &&
    VG.Proof.MlDsa.X86_64.Verify.t1Chk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (.rbp, 32 + 320 * r) pT && decide (32 + 320 * r + 320 ≤ p.pkLen) &&
    VG.Proof.MlDsa.X86_64.Verify.ipChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pT && VG.Proof.MlDsa.X86_64.Verify.ipChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW && VG.Proof.MlDsa.X86_64.Verify.mulChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pT2 pC pT &&
    VG.Proof.MlDsa.X86_64.Verify.subChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW pT2 && VG.Proof.MlDsa.X86_64.Verify.uhChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (pH r) pW pW1 && decide (p.γ₂ ∈ gamma2s) &&
    VG.Proof.MlDsa.X86_64.Verify.sbpChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW1 (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r)) (w1Len p) && decide (w1Max p ∈ simpleBitPackBounds) &&
    decide (w1Len p = 32 * bitlen (w1Max p)) && VG.Proof.MlDsa.X86_64.Verify.keepC p (VG.Proof.MlDsa.X86_64.Verify.wsR p r) 100 && VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsR p r) pC 1024 &&
    (List.range r).all (fun r' => VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsR p r) (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r')) (w1Len p)) &&
    VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [(pT, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024), (pT2, 1024)] pW 1024 && decide (1 ≤ p.ℓ) &&
    decide (w1Max p = (q - 1) / (2 * p.γ₂) - 1)

theorem rowChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, ∀ r < p.k, VG.Proof.MlDsa.X86_64.Verify.rowChk p r = true := by decide +kernel

theorem hintRow_pa (s : State) (r : Nat) : VG.Proof.MlDsa.X86_64.Verify.pa s (pH r) = VG.Proof.MlDsa.X86_64.Verify.pa s (pH 0) + BitVec.ofNat 64 (1024 * r) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.pa, VG.Impl.MlDsa.X86_64.Verify.oP]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_zero, Nat.add_zero]

theorem wsR_bases (p : Params) (r : Nat) : ∀ w ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r, w.1.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases := by
  intro w hw
  simp only [VG.Proof.MlDsa.X86_64.Verify.wsR, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide)

/-- `rowChk`, piece by piece. -/
structure RowC (p : Params) (r : Nat) : Prop where
  mul : ∀ c < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.mulChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW (pA p.ℓ r c) (pZ c) = true
  t1 : VG.Proof.MlDsa.X86_64.Verify.t1Chk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (.rbp, 32 + 320 * r) pT = true
  pk : 32 + 320 * r + 320 ≤ p.pkLen
  ipT : VG.Proof.MlDsa.X86_64.Verify.ipChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pT = true
  ipW : VG.Proof.MlDsa.X86_64.Verify.ipChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW = true
  mulT : VG.Proof.MlDsa.X86_64.Verify.mulChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pT2 pC pT = true
  sub : VG.Proof.MlDsa.X86_64.Verify.subChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW pT2 = true
  uh : VG.Proof.MlDsa.X86_64.Verify.uhChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (pH r) pW pW1 = true
  g2 : p.γ₂ ∈ gamma2s
  sbp : VG.Proof.MlDsa.X86_64.Verify.sbpChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) pW1 (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r)) (w1Len p) = true
  sbpB : w1Max p ∈ simpleBitPackBounds
  len : w1Len p = 32 * bitlen (w1Max p)
  keep : VG.Proof.MlDsa.X86_64.Verify.keepC p (VG.Proof.MlDsa.X86_64.Verify.wsR p r) 100 = true
  keepC' : VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsR p r) pC 1024 = true
  rows : ∀ r' < r, VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.wsR p r) (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r')) (w1Len p) = true
  keepW : VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [(pT, 1024), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024), (pT2, 1024)] pW 1024 = true
  l1 : 1 ≤ p.ℓ
  max : w1Max p = (q - 1) / (2 * p.γ₂) - 1

theorem rowC {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {r : Nat} (hr : r < p.k) : VG.Proof.MlDsa.X86_64.Verify.RowC p r := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.rowChk_all p hp r hr
  simp only [VG.Proof.MlDsa.X86_64.Verify.rowChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, c16⟩,
    c17⟩, c18⟩ := hc
  exact ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩

theorem wsR_mem (p : Params) (r : Nat) :
    (pW, 1024) ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r ∧ (pT, 1024) ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r ∧ (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oSS, 1024) ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r ∧ (pT2, 1024) ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r ∧
      (pW1, 1024) ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r ∧ (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r), w1Len p) ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [VG.Proof.MlDsa.X86_64.Verify.wsR, List.mem_cons, true_or, or_true]

theorem sub1 {α : Type} {x : α} {l : List α} (h : x ∈ l) : ∀ w ∈ [x], w ∈ l := fun _ hw => by
  rw [List.mem_singleton.mp hw]; exact h

theorem sub2 {α : Type} {x y : α} {l : List α} (h : x ∈ l) (h' : y ∈ l) : ∀ w ∈ [x, y], w ∈ l := fun _ hw => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  exacts [h, h']

theorem PPostB.accR {p : Params} {r : Nat} {s s₁ s₂ : State} {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (h₁ : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₁ (VG.Proof.MlDsa.X86_64.Verify.wsR p r))
    (h₂ : VG.Proof.MlDsa.X86_64.Verify.PPostB s₁ s₂ ws) (hw : ∀ w ∈ ws, w ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r) : VG.Proof.MlDsa.X86_64.Verify.PPostB s s₂ (VG.Proof.MlDsa.X86_64.Verify.wsR p r) :=
  h₁.trans h₂ (fun w hw' => VG.Proof.MlDsa.X86_64.Verify.wsR_bases p r w (hw w hw')) (fun _ h => h) hw

theorem pa_rbx {s s' : State} {W : List Region} (hP : VG.Proof.MlDsa.X86_64.Verify.PostB s s' W) (o : Nat) : VG.Proof.MlDsa.X86_64.Verify.pa s' (.rbx, o) = VG.Proof.MlDsa.X86_64.Verify.pa s (.rbx, o) :=
  hP.pa (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide)

/-- After `Σ_{s < j} Â[r, s] ẑ[s]`, from `s₀`. -/
def DI (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r j : Nat) (s₀ st : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.PPostB s₀ st [(pW, 1024)] ∧ st.gpr .r15 = s₀.gpr .r15 ∧ PolyIs st.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₀ pW) (dotAcc p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) A' r j)

theorem SC.zHat {p : Params} {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q]
    {cH : Poly} {r : Nat} {σ s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ cH r σ s) {c : Nat} (hc : c < p.ℓ) :
    PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pZ c)) (VG.Proof.MlDsa.Verify.zHat p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) c) := by
  have := hs.z c hc; rwa [VG.Proof.MlKem.X86_64.ifp hc] at this

section Dot
variable {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
  {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
  {r : Nat} (hr : r < p.k) {s₀ : State} (hs : VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ cH r σ s₀)
include C hp hv hr hs

theorem dotFirst_ok : WP isa (VG.Impl.MlDsa.X86_64.Verify.mulAt P pW (pA p.ℓ r 0) (pZ 0)) s₀ (VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r 1 s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.mulAt_ok C.mul (hs.t.lay hp hv) (R.mul 0 R.l1) (hs.a r hr 0 R.l1).1 (hs.zHat R.l1).1)
    fun s₁ ⟨hP₁, e₁, hq₁⟩ => ⟨hP₁, e₁, ?_⟩
  rw [(hs.a r hr 0 R.l1).2, (hs.zHat R.l1).2] at hq₁
  simp only [dotAcc, VG.Proof.MlDsa.Verify.add_zero_left]
  exact hq₁

theorem dotStep_ok {k : Nat} (hk' : k < p.ℓ) {st : State} (hd : VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r k s₀ st) :
    WP isa (VG.Impl.MlDsa.X86_64.Verify.mulAddAt P pW (pA p.ℓ r k) (pZ k)) st (VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r (k + 1) s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L := hs.t.lay hp hv
  obtain ⟨_, _, hZ, hA⟩ := VG.Proof.MlDsa.X86_64.Verify.keepC_spec R.keep
  obtain ⟨hP, e, hW⟩ := hd
  have H := hP.mono (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).1)
  have ew : VG.Proof.MlDsa.X86_64.Verify.pa st pW = VG.Proof.MlDsa.X86_64.Verify.pa s₀ pW := VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP _
  have hz : k ≠ 100 := by have := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp; omega
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.mulAddAt_ok C.mulAdd (L.post hP) (R.mul k hk') (by rw [ew]; exact hW.1)
    (L.keepRed H (hA r hr k hk') (hs.a r hr k hk').1) (L.keepRed H (hZ k hk' hz) (hs.zHat hk').1))
    fun s' ⟨hP', e', hq'⟩ => ?_
  rw [ew, hW.2, L.keepPolyAt H (hA r hr k hk'), (hs.a r hr k hk').2, L.keepPolyAt H (hZ k hk' hz),
    (hs.zHat hk').2] at hq'
  exact ⟨hP.trans hP' (fun w hw => by rw [List.mem_singleton.mp hw]; decide) (fun _ h => h) (fun _ h => h),
    e'.trans e, hq'⟩

theorem dot_ok : WP isa (dot P p r) s₀ (VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r p.ℓ s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  unfold dot
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.dotFirst_ok C hp hv hr hs) fun s₁ h₁ => ?_)
  have := VG.Proof.MlDsa.X86_64.Verify.seqR_ok (I := fun j => VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r j s₀) (p.ℓ - 1) 1
    (fun k _ hk' st hd => VG.Proof.MlDsa.X86_64.Verify.dotStep_ok C hp hv hr hs (by omega) hd) s₁ h₁
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by have := R.l1; omega] at this

end Dot

theorem keepB_sub {bs : List (Reg × Nat)} {ws ws' : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} {q : VG.Impl.MlDsa.X86_64.Verify.Ptr} {l : Nat} (h : VG.Proof.MlDsa.X86_64.Verify.keepB bs ws q l = true)
    (hw : ∀ w ∈ ws', w ∈ ws) : VG.Proof.MlDsa.X86_64.Verify.keepB bs ws' q l = true := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.keepB, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨h.1, fun w hw' => h.2 w (hw w hw')⟩

section Row
variable {p : Params} {σ : State} {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {cH : Poly} {r : Nat}

/-- `Σₛ Â[r, s] ẑ[s]`. -/
abbrev rDot (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) : Poly := dotAcc p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) A' r p.ℓ
/-- `t₁[r] · 2ᵈ`. -/
abbrev rU (p : Params) (σ : State) (r : Nat) : Poly := (vT1 (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r).map fun c => ofInt (c * 2 ^ d : Nat)
/-- `ĉ t̂₁[r]`. -/
abbrev rCT (p : Params) (σ : State) (cH : Poly) (r : Nat) : Poly := multiplyNTT cH (t1Hat (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r)

/-- Row `r` from `s₀`, what every step keeps: the writes and `r15`. -/
abbrev RB (p : Params) (r : Nat) (s₀ s : State) : Prop := VG.Proof.MlDsa.X86_64.Verify.PPostB s₀ s (VG.Proof.MlDsa.X86_64.Verify.wsR p r) ∧ s.gpr .r15 = s₀.gpr .r15

/-- After `Σₛ Â[r, s] ẑ[s]`, and `t₁[r] · 2ᵈ`, its NTT, and `ĉ t̂₁[r]`. -/
def RF1 (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.RB p r s₀ s ∧ PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW) (VG.Proof.MlDsa.X86_64.Verify.rDot p σ A' r)
def RF2 (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.RF1 p σ A' r s₀ s ∧ PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pT) (VG.Proof.MlDsa.X86_64.Verify.rU p σ r)
def RF3 (p : Params) (σ : State) (A' : Nat → Nat → Poly) (r : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.RF1 p σ A' r s₀ s ∧ PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pT) (VG.Spec.MlDsa.ntt (VG.Proof.MlDsa.X86_64.Verify.rU p σ r))
def RF4 (p : Params) (σ : State) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.RF1 p σ A' r s₀ s ∧ PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pT2) (VG.Proof.MlDsa.X86_64.Verify.rCT p σ cH r)
/-- After `w′ = NTT⁻¹(…)` less `ĉ t̂₁[r]`, `w′`, and `w′₁`. -/
def RF5 (p : Params) (σ : State) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.RB p r s₀ s ∧ PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW) (VG.Spec.MlDsa.sub (VG.Proof.MlDsa.X86_64.Verify.rDot p σ A' r) (VG.Proof.MlDsa.X86_64.Verify.rCT p σ cH r))
def RF6 (p : Params) (σ : State) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat) (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.RB p r s₀ s ∧ PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW) (wRow p (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) A' cH r)
def RF7 (p : Params) (σ : State) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (cH : Poly) (r : Nat)
    (s₀ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.RB p r s₀ s ∧ NatPolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW1) (w1Row p (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) A' cH h r)

theorem RB.acc {s₀ s s' : State} (hb : VG.Proof.MlDsa.X86_64.Verify.RB p r s₀ s) {ws : List (VG.Impl.MlDsa.X86_64.Verify.Ptr × Nat)} (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' ws)
    (e : s'.gpr .r15 = s.gpr .r15) (hw : ∀ w ∈ ws, w ∈ VG.Proof.MlDsa.X86_64.Verify.wsR p r) : VG.Proof.MlDsa.X86_64.Verify.RB p r s₀ s' :=
  ⟨hb.1.accR hP hw, e.trans hb.2⟩

variable {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) {Q : Prop} [Decidable Q] (hr : r < p.k)
  {s₀ : State} (hs : VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ cH r σ s₀)
include C hp hv hr hs

omit C hp hv hr hs in
theorem DI.rf1 {s : State} (hd : VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r p.ℓ s₀ s) : VG.Proof.MlDsa.X86_64.Verify.RF1 p σ A' r s₀ s :=
  let ⟨hP, e, hq⟩ := hd
  ⟨⟨hP.mono (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).1), e⟩, by rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP]; exact hq⟩

theorem row0_ok : WP isa (dot P p r) s₀ (VG.Proof.MlDsa.X86_64.Verify.RF1 p σ A' r s₀) :=
  WP.mono (VG.Proof.MlDsa.X86_64.Verify.dot_ok C hp hv hr hs) fun _ hd => DI.rf1 hd

theorem row1_ok {s : State} (hf : VG.Proof.MlDsa.X86_64.Verify.RF1 p σ A' r s₀ s) :
    WP isa (unpackT1At P (.rbp, 32 + 320 * r) pT) s (VG.Proof.MlDsa.X86_64.Verify.RF2 p σ A' r s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.unpackT1At_ok C.unpackT1 L R.t1) fun s' ⟨hP, e, hq⟩ => ⟨⟨hf.1.acc hP e (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).2.1),
    L.keepPoly hP (VG.Proof.MlDsa.X86_64.Verify.keepB_sub R.keepW (VG.Proof.MlDsa.X86_64.Verify.sub1 (List.mem_cons_self ..))) hf.2⟩, ?_⟩
  rw [(hs.t.step hp hv hf.1.1 (VG.Proof.MlDsa.X86_64.Verify.keepC_spec R.keep).1).pkSlice R.pk] at hq
  rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP]
  exact hq

theorem row2_ok {s : State} (hf : VG.Proof.MlDsa.X86_64.Verify.RF2 p σ A' r s₀ s) : WP isa (VG.Impl.MlDsa.X86_64.Verify.nttAt P pT) s (VG.Proof.MlDsa.X86_64.Verify.RF3 p σ A' r s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1.1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.ipAt_ok C.ntt L R.ipT hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨⟨hf.1.1.acc hP e
    (VG.Proof.MlDsa.X86_64.Verify.sub2 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).2.1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).2.2.1), L.keepPoly hP (VG.Proof.MlDsa.X86_64.Verify.keepB_sub R.keepW (VG.Proof.MlDsa.X86_64.Verify.sub2 (List.mem_cons_self ..)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) hf.1.2⟩, ?_⟩
  rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP, ← hf.2.2]
  exact hq

theorem row3_ok {s : State} (hf : VG.Proof.MlDsa.X86_64.Verify.RF3 p σ A' r s₀ s) : WP isa (VG.Impl.MlDsa.X86_64.Verify.mulAt P pT2 pC pT) s (VG.Proof.MlDsa.X86_64.Verify.RF4 p σ A' cH r s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L₀ := hs.t.lay hp hv
  have L := L₀.post hf.1.1.1
  have hC := L₀.keepPoly hf.1.1.1 R.keepC' hs.c
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.mulAt_ok C.mul L R.mulT hC.1 hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨⟨hf.1.1.acc hP e
    (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).2.2.2.1), L.keepPoly hP (VG.Proof.MlDsa.X86_64.Verify.keepB_sub R.keepW (VG.Proof.MlDsa.X86_64.Verify.sub1 (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))))) hf.1.2⟩, ?_⟩
  rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP, hC.2, hf.2.2] at *
  exact hq

theorem row4_ok {s : State} (hf : VG.Proof.MlDsa.X86_64.Verify.RF4 p σ A' cH r s₀ s) : WP isa (VG.Impl.MlDsa.X86_64.Verify.subAt P pW pT2) s (VG.Proof.MlDsa.X86_64.Verify.RF5 p σ A' cH r s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1.1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.subAt_ok C.sub L R.sub hf.1.2.1 hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨hf.1.1.acc hP e
    (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).1), ?_⟩
  rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP, hf.1.2.2, hf.2.2] at *
  exact hq

theorem row5_ok {s : State} (hf : VG.Proof.MlDsa.X86_64.Verify.RF5 p σ A' cH r s₀ s) : WP isa (VG.Impl.MlDsa.X86_64.Verify.invNttAt P pW) s (VG.Proof.MlDsa.X86_64.Verify.RF6 p σ A' cH r s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L := (hs.t.lay hp hv).post hf.1.1
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.ipAt_ok C.invNtt L R.ipW hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨hf.1.acc hP e
    (VG.Proof.MlDsa.X86_64.Verify.sub2 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).2.2.1), ?_⟩
  rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP, hf.2.2] at *
  exact hq

theorem row6_ok {s : State} (hf : VG.Proof.MlDsa.X86_64.Verify.RF6 p σ A' cH r s₀ s) : WP isa (useHintAt P (pH r) pW p.γ₂ pW1) s (VG.Proof.MlDsa.X86_64.Verify.RF7 p σ h A' cH r s₀) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L₀ := hs.t.lay hp hv
  have L := L₀.post hf.1.1
  have hh := L₀.keepHint hf.1.1 (VG.Proof.MlDsa.X86_64.Verify.keepC_spec R.keep).2.1 hs.hint
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.useHintAt_ok C.useHint L R.g2 R.uh hf.2.1) fun s' ⟨hP, e, hq⟩ => ⟨hf.1.acc hP e
    (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).2.2.2.2.1), ?_⟩
  have hq' : natPolyAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW1) = _ := hq
  rw [VG.Proof.MlDsa.X86_64.Verify.hintRow_pa s r, hintAt_row hh hr, hf.2.2] at hq'
  show natPolyAt s'.mem (VG.Proof.MlDsa.X86_64.Verify.pa s' pW1) = _
  rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP]
  exact hq'

theorem row7_ok {s : State} (hf : VG.Proof.MlDsa.X86_64.Verify.RF7 p σ h A' cH r s₀ s) :
    WP isa (sbpAt P pW1 (w1Max p) (VG.Impl.MlDsa.X86_64.Verify.sc (oB + w1Len p * r)) (w1Len p)) s (VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ cH (r + 1) σ) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have L₀ := hs.t.lay hp hv
  have L := L₀.post hf.1.1
  obtain ⟨tk, hH, hZ, hA⟩ := VG.Proof.MlDsa.X86_64.Verify.keepC_spec R.keep
  have hq₇ : natPolyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW1) = _ := hf.2
  have hb : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW1) i).toNat ≤ w1Max p := fun i hi => by
    have := congrArg (·[i]'hi) hq₇
    simp only [natPolyAt, Vector.getElem_ofFn, w1Row, Vector.getElem_zipWith] at this
    rw [this, R.max]
    exact useHint_le R.g2 _ _
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.sbpAt_ok C.simpleBitPack L R.sbpB R.len R.sbp hb) fun s' ⟨hP, e, hq⟩ => ?_
  rw [hq₇] at hq
  have H := hf.1.1.accR hP (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).2.2.2.2.2)
  refine ⟨hs.t.step hp hv H tk, L₀.keepHint H hH hs.hint,
    fun r' hr' c hc => L₀.keepPoly H (hA r' hr' c hc) (hs.a r' hr' c hc),
    fun i hi => L₀.keepPoly H (hZ i hi (by have := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp; omega)) (hs.z i hi), L₀.keepPoly H R.keepC' hs.c,
    fun r' hr' => ?_, by rw [e, hf.1.2]; exact hs.r15⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hr' with hlt | rfl
  · rw [L₀.keepBytes H (R.rows r' hlt)]; exact hs.rows r' hlt
  · rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP]
    exact hq

theorem row_ok : WP isa (row P p r) s₀ (VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ cH (r + 1) σ) := by
  unfold row
  exact WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.row0_ok C hp hv hr hs) fun _ h1 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.row1_ok C hp hv hr hs h1) fun _ h2 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.row2_ok C hp hv hr hs h2) fun _ h3 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.row3_ok C hp hv hr hs h3) fun _ h4 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.row4_ok C hp hv hr hs h4) fun _ h5 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.row5_ok C hp hv hr hs h5) fun _ h6 =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.row6_ok C hp hv hr hs h6) fun _ h7 => VG.Proof.MlDsa.X86_64.Verify.row7_ok C hp hv hr hs h7)))))))

end Row

/-! ## The rows, the hash and the comparison -/

theorem bytesAt_rows {m : Mem} {a : Addr} {L : Nat} {f : Nat → List Byte} :
    ∀ k, (∀ r < k, bytesAt m (a + BitVec.ofNat 64 (L * r)) L = f r) → bytesAt m a (k * L) = (List.range k).flatMap f
  | 0, _ => by rw [Nat.zero_mul]; rfl
  | k + 1, h => by
    rw [Nat.succ_mul, Proof.MlKem.bytesAt_add, VG.Proof.MlDsa.X86_64.Verify.bytesAt_rows k (fun r hr => h r (by omega)), Nat.mul_comm k L,
      h k (by omega), List.range_succ, List.flatMap_append, List.flatMap_singleton]

theorem row_pa (s : State) (L r : Nat) : VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc (oB + L * r)) = VG.Proof.MlDsa.X86_64.Verify.pa s (VG.Impl.MlDsa.X86_64.Verify.sc oB) + BitVec.ofNat 64 (L * r) := by
  simp only [VG.Proof.MlDsa.X86_64.Verify.pa]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The facts about the parameters the hash and the comparison need. -/
def compChk (p : Params) : Bool :=
  VG.Proof.MlDsa.X86_64.Verify.hashChk (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Proof.MlDsa.X86_64.Verify.vW p) (.r12, 0) 64 (VG.Impl.MlDsa.X86_64.Verify.sc oB) (p.k * w1Len p) (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oCT) p.ctildeLen &&
    VG.Proof.MlDsa.X86_64.Verify.tChk p [(VG.Impl.MlDsa.X86_64.Verify.sc 0, 200), (VG.Impl.MlDsa.X86_64.Verify.sc 200, 640), (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oCT, p.ctildeLen)] && VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oCT) p.ctildeLen &&
    VG.Proof.MlDsa.X86_64.Verify.inB (VG.Proof.MlDsa.X86_64.Verify.vB p) (.r13, 0) p.ctildeLen && decide (0 < p.ctildeLen) && decide (p.ctildeLen ≤ p.sigLen)

theorem compChk_all : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, VG.Proof.MlDsa.X86_64.Verify.compChk p = true := by decide +kernel

/-- `w′₁` of the signature, encoded. -/
abbrev w1Enc (p : Params) (σ : State) (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (cH : Poly) :
    List Byte :=
  (List.range p.k).flatMap fun r => VG.Spec.MlDsa.simpleBitPack (w1Row p (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) A' cH h r) (w1Max p)

theorem tail_ok {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s₃ : State} (hs₃ : VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ cH p.k σ s₃) :
    WP isa (.seq (hash2 (.r12, 0) 64 (VG.Impl.MlDsa.X86_64.Verify.sc oB) (p.k * w1Len p) (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oCT) p.ctildeLen)
      (cmpAnd (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oCT) (.r13, 0) p.ctildeLen)) s₃ fun s' => VG.Proof.MlDsa.X86_64.Verify.T p σ s' ∧
      s'.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (Q ∧ H (VG.Proof.MlDsa.X86_64.Verify.vMu σ ++ VG.Proof.MlDsa.X86_64.Verify.w1Enc p σ h A' cH) p.ctildeLen = vCt p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ)) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.compChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.compChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
  have L₃ := hs₃.t.lay hp hv
  have hB : bytesAt s₃.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₃ (VG.Impl.MlDsa.X86_64.Verify.sc oB)) (p.k * w1Len p) = VG.Proof.MlDsa.X86_64.Verify.w1Enc p σ h A' cH :=
    VG.Proof.MlDsa.X86_64.Verify.bytesAt_rows p.k fun r hr => by rw [← VG.Proof.MlDsa.X86_64.Verify.row_pa]; exact hs₃.rows r hr
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.hash2_ok L₃ c1) fun s₄ ⟨hP₄, f₄, hq₄⟩ => ?_)
  rw [hB, hs₃.t.mu] at hq₄
  have t₄ := hs₃.t.step hp hv hP₄ c2
  have L₄ := t₄.lay hp hv
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.cmpAnd_ok L₄ c5 c3 c4 (P := Q) (by rw [f₄]; exact hs₃.r15)) fun s₅ ⟨hP₅, f₅⟩ => ⟨t₄.step hp hv hP₅
    (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), ?_⟩
  rw [f₅, show VG.Proof.MlDsa.X86_64.Verify.pa s₄ (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oCT) = VG.Proof.MlDsa.X86_64.Verify.pa s₃ (VG.Impl.MlDsa.X86_64.Verify.sc VG.Impl.MlDsa.X86_64.Verify.oCT) from VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP₄ _, hq₄,
    t₄.sigSlice (by omega : 0 + p.ctildeLen ≤ p.sigLen), List.drop_zero]
  exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (and_congr_right fun _ => Iff.rfl)

theorem compute_ok {P : VG.Impl.MlDsa.X86_64.Verify.Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {Q : Prop} [Decidable Q] {cH : Poly}
    {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q 0 cH 0 σ s) :
    WP isa (compute P p) s fun s' => VG.Proof.MlDsa.X86_64.Verify.T p σ s' ∧
      s'.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (Q ∧ H (VG.Proof.MlDsa.X86_64.Verify.vMu σ ++ VG.Proof.MlDsa.X86_64.Verify.w1Enc p σ h A' (VG.Spec.MlDsa.ntt cH)) p.ctildeLen = vCt p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ)) := by
  unfold compute
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q i cH 0 σ) p.ℓ 0
    (fun i _ hi st hst => VG.Proof.MlDsa.X86_64.Verify.nttZ_ok C hp hv (by omega) hst) s hs) fun s₁ hs₁ => ?_)
  rw [Nat.zero_add] at hs₁
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.nttC_ok C hp hv hs₁) fun s₂ hs₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.seqR_ok (I := fun r => VG.Proof.MlDsa.X86_64.Verify.SC p h A' Q p.ℓ (VG.Spec.MlDsa.ntt cH) r σ) p.k 0
    (fun r _ hr st hst => VG.Proof.MlDsa.X86_64.Verify.row_ok C hp hv (by omega) hst) s₂ hs₂) fun s₃ hs₃ => ?_)
  rw [Nat.zero_add] at hs₃
  exact VG.Proof.MlDsa.X86_64.Verify.tail_ok hp hv hs₃

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Instrs`. -/
section

/-!
# ML-DSA verification on x86-64: properties of every instruction

A property `q` of every instruction of `verify P p` (`Code.allInstrs q`) holds
if it holds of every instruction of the primitives `P` and of `verify P0 p`,
the same code with the primitives empty (`verify_q`), which the kernel
evaluates. So it never writes the stack pointer (`verify_spSafe`) if the
primitives do not. Likewise for `ctlC` (`verify_c`): it loads MXCSR only to
restore it (`verify_ctl`) if the primitives do (`ctlOk`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Spec.MlDsa

/-- The primitives, each empty. -/
def P0 : Prims := ⟨.block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [], .block [],
  .block [], .block [], .block [], .block [], .block [], ""⟩

/-- `q` holds of every instruction of the primitives `P`. -/
structure PrimsQ (q : Instr → Bool) (P : Prims) : Prop where
  ntt : P.ntt.allInstrs q = true
  invNtt : P.invNtt.allInstrs q = true
  mul : P.mul.allInstrs q = true
  mulAdd : P.mulAdd.allInstrs q = true
  sub : P.sub.allInstrs q = true
  rejNtt : P.rejNtt.allInstrs q = true
  ball : P.ball.allInstrs q = true
  useHint : P.useHint.allInstrs q = true
  simpleBitPack : P.simpleBitPack.allInstrs q = true
  bitUnpack : P.bitUnpack.allInstrs q = true
  unpackT1 : P.unpackT1.allInstrs q = true
  hintUnpack : P.hintUnpack.allInstrs q = true
  normLt : P.normLt.allInstrs q = true
  rej4 : P.rej4.allInstrs q = true

/-- `q` holds of every instruction of `c` exactly when it does of `c'`. -/
def SameQ (q : Instr → Bool) (c c' : Prog isa) : Prop := c.allInstrs q = c'.allInstrs q

section
variable {q : Instr → Bool}

theorem SameQ.seq {a a' b b' : Prog isa} (ha : VG.Proof.MlDsa.X86_64.Verify.SameQ q a a') (hb : VG.Proof.MlDsa.X86_64.Verify.SameQ q b b') :
    VG.Proof.MlDsa.X86_64.Verify.SameQ q (.seq a b) (.seq a' b') := by
  show (a.allInstrs q && b.allInstrs q) = (a'.allInstrs q && b'.allInstrs q)
  rw [show a.allInstrs q = a'.allInstrs q from ha, show b.allInstrs q = b'.allInstrs q from hb]

theorem SameQ.call {c : Prog isa} (hc : c.allInstrs q = true) {n n' : String} (as : List (Reg × Arg)) :
    VG.Proof.MlDsa.X86_64.Verify.SameQ q (callAt n c as) (callAt n' (.block []) as) := by
  show (_ && c.allInstrs q) = (_ && true)
  rw [hc]

theorem SameQ.seqR {f g : Nat → Prog isa} (h : ∀ k, VG.Proof.MlDsa.X86_64.Verify.SameQ q (f k) (g k)) :
    ∀ a n, VG.Proof.MlDsa.X86_64.Verify.SameQ q (VG.Impl.MlDsa.X86_64.Verify.seqR f a n) (VG.Impl.MlDsa.X86_64.Verify.seqR g a n)
  | _, 0 => rfl
  | a, n + 1 => (h a).seq (SameQ.seqR h (a + 1) n)

theorem SameQ.ifOk {c c' : Prog isa} (h : VG.Proof.MlDsa.X86_64.Verify.SameQ q c c') : VG.Proof.MlDsa.X86_64.Verify.SameQ q (VG.Impl.MlDsa.X86_64.Verify.ifOk c) (VG.Impl.MlDsa.X86_64.Verify.ifOk c') := by
  refine SameQ.seq rfl ?_
  show (c.allInstrs q && _) = (c'.allInstrs q && _)
  rw [show c.allInstrs q = c'.allInstrs q from h]

theorem SameQ.sampled {c c' : Prog isa} (h : VG.Proof.MlDsa.X86_64.Verify.SameQ q c c') (a : Ptr) : VG.Proof.MlDsa.X86_64.Verify.SameQ q (VG.Impl.MlDsa.X86_64.Verify.sampled c a) (VG.Impl.MlDsa.X86_64.Verify.sampled c' a) :=
  h.seq rfl

theorem SameQ.sampled4 {c c' : Prog isa} (h : VG.Proof.MlDsa.X86_64.Verify.SameQ q c c') (a : Ptr) : VG.Proof.MlDsa.X86_64.Verify.SameQ q (VG.Impl.MlDsa.X86_64.Verify.sampled4 c a) (VG.Impl.MlDsa.X86_64.Verify.sampled4 c' a) :=
  h.seq rfl

variable {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Verify.PrimsQ q P) (p : Params)
include hP

theorem hint_q : VG.Proof.MlDsa.X86_64.Verify.SameQ q (hint P p) (hint VG.Proof.MlDsa.X86_64.Verify.P0 p) := (SameQ.call hP.hintUnpack _).seq rfl

theorem zOne_q (i : Nat) : VG.Proof.MlDsa.X86_64.Verify.SameQ q (zOne P p i) (zOne VG.Proof.MlDsa.X86_64.Verify.P0 p i) :=
  (SameQ.call hP.bitUnpack _).seq ((SameQ.call hP.normLt _).seq rfl)

theorem aOne_q (e : Nat) : VG.Proof.MlDsa.X86_64.Verify.SameQ q (aOne P p e) (aOne VG.Proof.MlDsa.X86_64.Verify.P0 p e) :=
  SameQ.seq rfl (SameQ.sampled (SameQ.call hP.rejNtt _) _)

theorem aGrp_q (g : Nat) : VG.Proof.MlDsa.X86_64.Verify.SameQ q (aGrp P p g) (aGrp VG.Proof.MlDsa.X86_64.Verify.P0 p g) :=
  SameQ.seq rfl (SameQ.seq rfl (SameQ.seq rfl (SameQ.seq rfl (SameQ.sampled4 (SameQ.call hP.rej4 _) _))))

theorem samples_q : VG.Proof.MlDsa.X86_64.Verify.SameQ q (VG.Impl.MlDsa.X86_64.Verify.samples P p) (VG.Impl.MlDsa.X86_64.Verify.samples VG.Proof.MlDsa.X86_64.Verify.P0 p) :=
  SameQ.seq rfl ((SameQ.seqR (VG.Proof.MlDsa.X86_64.Verify.aGrp_q hP p) _ _).seq ((SameQ.seqR (VG.Proof.MlDsa.X86_64.Verify.aOne_q hP p) _ _).seq
    (SameQ.sampled (SameQ.call hP.ball _) _)))

theorem dot_q (r : Nat) : VG.Proof.MlDsa.X86_64.Verify.SameQ q (dot P p r) (dot VG.Proof.MlDsa.X86_64.Verify.P0 p r) :=
  (SameQ.call hP.mul _).seq (SameQ.seqR (fun _ => SameQ.call hP.mulAdd _) _ _)

theorem row_q (r : Nat) : VG.Proof.MlDsa.X86_64.Verify.SameQ q (row P p r) (row VG.Proof.MlDsa.X86_64.Verify.P0 p r) :=
  (VG.Proof.MlDsa.X86_64.Verify.dot_q hP p r).seq ((SameQ.call hP.unpackT1 _).seq ((SameQ.call hP.ntt _).seq ((SameQ.call hP.mul _).seq
    ((SameQ.call hP.sub _).seq ((SameQ.call hP.invNtt _).seq ((SameQ.call hP.useHint _).seq
      (SameQ.call hP.simpleBitPack _)))))))

theorem compute_q : VG.Proof.MlDsa.X86_64.Verify.SameQ q (compute P p) (compute VG.Proof.MlDsa.X86_64.Verify.P0 p) :=
  (SameQ.seqR (fun _ => SameQ.call hP.ntt _) _ _).seq ((SameQ.call hP.ntt _).seq
    ((SameQ.seqR (VG.Proof.MlDsa.X86_64.Verify.row_q hP p) _ _).seq rfl))

theorem verify_q : VG.Proof.MlDsa.X86_64.Verify.SameQ q (verify P p) (verify VG.Proof.MlDsa.X86_64.Verify.P0 p) :=
  SameQ.seq rfl (((VG.Proof.MlDsa.X86_64.Verify.hint_q hP p).seq (SameQ.ifOk ((SameQ.seqR (VG.Proof.MlDsa.X86_64.Verify.zOne_q hP p) _ _).seq
    (SameQ.ifOk ((VG.Proof.MlDsa.X86_64.Verify.samples_q hP p).seq (VG.Proof.MlDsa.X86_64.Verify.compute_q hP p)))))).seq rfl)

end

theorem verify0_sp : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, (verify VG.Proof.MlDsa.X86_64.Verify.P0 p).allInstrs (fun i => !isa.writesSp i) = true := by
  decide +kernel

/-! ## MXCSR -/

/-- Every primitive of `P` loads MXCSR only to restore it. -/
structure PrimsC (P : Prims) : Prop where
  ntt : ctlOk P.ntt = true
  invNtt : ctlOk P.invNtt = true
  mul : ctlOk P.mul = true
  mulAdd : ctlOk P.mulAdd = true
  sub : ctlOk P.sub = true
  rejNtt : ctlOk P.rejNtt = true
  ball : ctlOk P.ball = true
  useHint : ctlOk P.useHint = true
  simpleBitPack : ctlOk P.simpleBitPack = true
  bitUnpack : ctlOk P.bitUnpack = true
  unpackT1 : ctlOk P.unpackT1 = true
  hintUnpack : ctlOk P.hintUnpack = true
  normLt : ctlOk P.normLt = true
  rej4 : ctlOk P.rej4 = true

/-- `ctlC` holds of `c` exactly when it does of `c'`. -/
def SameC (c c' : Prog isa) : Prop := ctlC c = ctlC c'

theorem SameC.seq {a a' b b' : Prog isa} (ha : VG.Proof.MlDsa.X86_64.Verify.SameC a a') (hb : VG.Proof.MlDsa.X86_64.Verify.SameC b b') : VG.Proof.MlDsa.X86_64.Verify.SameC (.seq a b) (.seq a' b') := by
  show (ctlC a && ctlC b) = (ctlC a' && ctlC b')
  rw [show ctlC a = ctlC a' from ha, show ctlC b = ctlC b' from hb]

theorem SameC.call {c : Prog isa} (hc : ctlOk c = true) {n n' : String} (as : List (Reg × Arg)) :
    VG.Proof.MlDsa.X86_64.Verify.SameC (callAt n c as) (callAt n' (.block []) as) := by
  show (_ && ctlOk c) = (_ && true)
  rw [hc]

theorem SameC.seqR {f g : Nat → Prog isa} (h : ∀ k, VG.Proof.MlDsa.X86_64.Verify.SameC (f k) (g k)) : ∀ a n, VG.Proof.MlDsa.X86_64.Verify.SameC (VG.Impl.MlDsa.X86_64.Verify.seqR f a n) (VG.Impl.MlDsa.X86_64.Verify.seqR g a n)
  | _, 0 => rfl
  | a, n + 1 => (h a).seq (SameC.seqR h (a + 1) n)

theorem SameC.ifOk {c c' : Prog isa} (h : VG.Proof.MlDsa.X86_64.Verify.SameC c c') : VG.Proof.MlDsa.X86_64.Verify.SameC (VG.Impl.MlDsa.X86_64.Verify.ifOk c) (VG.Impl.MlDsa.X86_64.Verify.ifOk c') := by
  refine SameC.seq rfl ?_
  show (ctlC c && _) = (ctlC c' && _)
  rw [show ctlC c = ctlC c' from h]

theorem SameC.sampled {c c' : Prog isa} (h : VG.Proof.MlDsa.X86_64.Verify.SameC c c') (a : Ptr) : VG.Proof.MlDsa.X86_64.Verify.SameC (VG.Impl.MlDsa.X86_64.Verify.sampled c a) (VG.Impl.MlDsa.X86_64.Verify.sampled c' a) :=
  h.seq rfl

theorem SameC.sampled4 {c c' : Prog isa} (h : VG.Proof.MlDsa.X86_64.Verify.SameC c c') (a : Ptr) : VG.Proof.MlDsa.X86_64.Verify.SameC (VG.Impl.MlDsa.X86_64.Verify.sampled4 c a) (VG.Impl.MlDsa.X86_64.Verify.sampled4 c' a) :=
  h.seq rfl

section
variable {P : Prims} (hP : VG.Proof.MlDsa.X86_64.Verify.PrimsC P) (p : Params)
include hP

theorem verify_c : VG.Proof.MlDsa.X86_64.Verify.SameC (verify P p) (verify VG.Proof.MlDsa.X86_64.Verify.P0 p) := by
  have aOne : ∀ e, VG.Proof.MlDsa.X86_64.Verify.SameC (aOne P p e) (aOne VG.Proof.MlDsa.X86_64.Verify.P0 p e) := fun e =>
    SameC.seq rfl (SameC.sampled (SameC.call hP.rejNtt _) _)
  have dot : ∀ r, VG.Proof.MlDsa.X86_64.Verify.SameC (dot P p r) (dot VG.Proof.MlDsa.X86_64.Verify.P0 p r) := fun r =>
    (SameC.call hP.mul _).seq (SameC.seqR (fun _ => SameC.call hP.mulAdd _) _ _)
  have row : ∀ r, VG.Proof.MlDsa.X86_64.Verify.SameC (row P p r) (row VG.Proof.MlDsa.X86_64.Verify.P0 p r) := fun r =>
    (dot r).seq ((SameC.call hP.unpackT1 _).seq ((SameC.call hP.ntt _).seq ((SameC.call hP.mul _).seq
      ((SameC.call hP.sub _).seq ((SameC.call hP.invNtt _).seq ((SameC.call hP.useHint _).seq
        (SameC.call hP.simpleBitPack _)))))))
  have aGrp : ∀ g, VG.Proof.MlDsa.X86_64.Verify.SameC (aGrp P p g) (aGrp VG.Proof.MlDsa.X86_64.Verify.P0 p g) := fun g =>
    SameC.seq rfl (SameC.seq rfl (SameC.seq rfl (SameC.seq rfl (SameC.sampled4 (SameC.call hP.rej4 _) _))))
  have samples : VG.Proof.MlDsa.X86_64.Verify.SameC (VG.Impl.MlDsa.X86_64.Verify.samples P p) (VG.Impl.MlDsa.X86_64.Verify.samples VG.Proof.MlDsa.X86_64.Verify.P0 p) :=
    SameC.seq rfl ((SameC.seqR aGrp _ _).seq ((SameC.seqR aOne _ _).seq
      (SameC.sampled (SameC.call hP.ball _) _)))
  have compute : VG.Proof.MlDsa.X86_64.Verify.SameC (compute P p) (compute VG.Proof.MlDsa.X86_64.Verify.P0 p) :=
    (SameC.seqR (fun _ => SameC.call hP.ntt _) _ _).seq ((SameC.call hP.ntt _).seq
      ((SameC.seqR row _ _).seq rfl))
  have zOne : ∀ i, VG.Proof.MlDsa.X86_64.Verify.SameC (zOne P p i) (zOne VG.Proof.MlDsa.X86_64.Verify.P0 p i) := fun _ =>
    (SameC.call hP.bitUnpack _).seq ((SameC.call hP.normLt _).seq rfl)
  exact SameC.seq rfl ((((SameC.call hP.hintUnpack _).seq rfl).seq (SameC.ifOk ((SameC.seqR zOne _ _).seq
    (SameC.ifOk (samples.seq compute))))).seq rfl)

end

theorem verify0_ctlC : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, ctlC (verify VG.Proof.MlDsa.X86_64.Verify.P0 p) = true := by
  decide +kernel

variable {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params)
include C hp

theorem verify_ctl : ctlOk (verify P p) = true :=
  ctlOk_of_ctlC ((VG.Proof.MlDsa.X86_64.Verify.verify_c ⟨C.ntt.ctl, C.invNtt.ctl, C.mul.ctl, C.mulAdd.ctl, C.sub.ctl, C.rejNtt.ctl, C.ball.ctl,
    C.useHint.ctl, C.simpleBitPack.ctl, C.bitUnpack.ctl, C.unpackT1.ctl, C.hintUnpack.ctl,
    C.normLt.ctl, C.rej4.ctl⟩ p).trans (VG.Proof.MlDsa.X86_64.Verify.verify0_ctlC p hp))

theorem verify_spSafe : (verify P p).all (fun i => !isa.writesSp i) = true :=
  Code.all_of_allInstrs ((VG.Proof.MlDsa.X86_64.Verify.verify_q ⟨Code.allInstrs_of_all C.ntt.spSafe, Code.allInstrs_of_all C.invNtt.spSafe,
    Code.allInstrs_of_all C.mul.spSafe, Code.allInstrs_of_all C.mulAdd.spSafe, Code.allInstrs_of_all C.sub.spSafe,
    Code.allInstrs_of_all C.rejNtt.spSafe, Code.allInstrs_of_all C.ball.spSafe,
    Code.allInstrs_of_all C.useHint.spSafe, Code.allInstrs_of_all C.simpleBitPack.spSafe,
    Code.allInstrs_of_all C.bitUnpack.spSafe, Code.allInstrs_of_all C.unpackT1.spSafe,
    Code.allInstrs_of_all C.hintUnpack.spSafe, Code.allInstrs_of_all C.normLt.spSafe,
    Code.allInstrs_of_all C.rej4.spSafe⟩ p).trans (VG.Proof.MlDsa.X86_64.Verify.verify0_sp p hp))

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct`. -/
section

/-!
# ML-DSA verification on x86-64: correctness

`vg_mldsa*_verify` returns 1 only if `verifyMu` accepts the signature for some
bounds on the samplers' loops, and 0 only if it does not accept it with the
least bounds (`verify_correct`): a malformed hint returns 0 at once, a `z` too
large after the norms, and otherwise `r15` holds the result of the samplers
(`S4`) and then the comparison of `c̃` (`compute_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (VG.Proof.MlDsa.X86_64.Verify.vMu σ) (VG.Proof.MlDsa.X86_64.Verify.vSig p σ)

/-- At the end, before the epilogue: the result in `r15`. -/
def Fin (p : Params) (σ s : State) : Prop :=
  VG.Proof.MlDsa.X86_64.Verify.T p σ s ∧ ((s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True ∧ ∃ b, VG.Proof.MlDsa.X86_64.Verify.vv p σ b = some true) ∨
    (s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag False ∧ VG.Proof.MlDsa.X86_64.Verify.vv p σ minBounds ≠ some true))

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : VG.Proof.MlDsa.X86_64.Verify.vv p σ b = some false) : VG.Proof.MlDsa.X86_64.Verify.vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := verifyMu_mono (bmax_left b minBounds).rejNTT (bmax_left b minBounds).ball h
    have e₂ := verifyMu_mono (bmax_right b minBounds).rejNTT (bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

/-- The facts about the parameters the proof needs. -/
theorem parChk : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, p.γ₁ ∈ gamma1s ∧ 0 < p.γ₁ - p.β ∧ VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [] (pH 0) (1024 * p.k) = true ∧
    ∀ i < p.ℓ, VG.Proof.MlDsa.X86_64.Verify.keepB (VG.Proof.MlDsa.X86_64.Verify.vB p) [] (pZ i) 1024 = true := by decide

theorem S2.flag {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) {h : List (Vector Bool n)} {j : Nat}
    (hj : j ≤ p.ℓ) {s s' : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S2 p h j σ s) (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s s' []) (e : s'.gpr .r15 = s.gpr .r15) :
    VG.Proof.MlDsa.X86_64.Verify.S2 p h j σ s' := by
  have L := hs.t.lay hp hv
  obtain ⟨_, _, kh, kz⟩ := VG.Proof.MlDsa.X86_64.Verify.parChk p hp
  exact ⟨hs.t.step hp hv hP (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), L.keepHint hP kh hs.hint,
    fun i hi => L.keepPoly hP (kz i (by omega)) (hs.z i hi), by rw [e]; exact hs.r15⟩

theorem S4.toSC {p : Params} {h : List (Vector Bool n)} {σ s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S4 p h σ s) {q : Bool}
    (h15 : s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag (q = true)) :
    VG.Proof.MlDsa.X86_64.Verify.SC p h (fun r c => polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pA p.ℓ r c))) (q = true) 0 (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pC)) 0 σ s :=
  ⟨hs.t, hs.hint, fun r hr c hc => ⟨hs.red r hr c hc, rfl⟩,
    fun i hi => by rw [iteN (Nat.not_lt_zero _)]; exact hs.z i hi, ⟨hs.redC, rfl⟩,
    fun _ h => absurd h (Nat.not_lt_zero _), h15⟩

/-- After the norms: the samplers, the rows, the hash and the comparison. -/
theorem cs_ok {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {h : List (Vector Bool n)} (hh : vHint p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) = some h)
    (hn : ∀ i < p.ℓ, normRq [toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i)] < p.γ₁ - p.β) {s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S4 p h σ s) :
    WP isa (compute P p) s (VG.Proof.MlDsa.X86_64.Verify.Fin p σ) := by
  obtain ⟨q, h15, hok, hbad⟩ := hs.ok
  have hSC := hs.toSC h15
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.compute_ok C hp hv hSC) fun s' ⟨ht, h15'⟩ => ⟨ht, ?_⟩
  cases q with
  | false =>
    refine .inr ⟨by rw [h15']; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp), ?_⟩
    rcases hbad rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_rej_none minBounds _ _ hh hr hc hn']; nofun
    · show verifyMu p minBounds _ _ _ ≠ some true
      rw [verifyMu_ball_none minBounds _ _ hh (Option.map_eq_none_iff.mp hn')]; nofun
  | true =>
    obtain ⟨hA, hB⟩ := hok rfl
    obtain ⟨nA, hnA⟩ := common_bound (P := fun r n => ∀ c < p.ℓ,
        rejNTTPoly n (aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r c) = some (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pA p.ℓ r c))))
      (fun _ _ _ hle h c hc => VG.Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
        common_bound (P := fun c n => rejNTTPoly n (aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r c) = some (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pA p.ℓ r c))))
          (fun _ _ _ hle h => VG.Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc =>
            let ⟨b, hb⟩ := hA r hr c hc; ⟨b.rejNTT, hb⟩
    obtain ⟨bB, hbB⟩ := hB
    obtain ⟨cc, hcc, hcc'⟩ := Option.map_eq_some_iff.mp hbB
    have hl : h.length = p.k := hs.hint.1
    have e := verifyMu_rows p ⟨0, 0, nA, bB.ball⟩ (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) (VG.Proof.MlDsa.X86_64.Verify.vMu σ) (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) hh hl hnA hcc
    obtain ⟨hg, hβ, _, _⟩ := VG.Proof.MlDsa.X86_64.Verify.parChk p hp
    rw [decide_eq_true ((normR_vZ_iff hβ p hg _).mpr hn), hcc', Bool.true_and] at e
    by_cases hE : H (VG.Proof.MlDsa.X86_64.Verify.vMu σ ++ VG.Proof.MlDsa.X86_64.Verify.w1Enc p σ h (fun r c => polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pA p.ℓ r c))) (VG.Spec.MlDsa.ntt (polyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pC))))
        p.ctildeLen = vCt p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ)
    · exact .inl ⟨by rw [h15']; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp [hE]),
        ⟨_, e.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
    · exact .inr ⟨by rw [h15']; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp [hE]),
        VG.Proof.MlDsa.X86_64.Verify.false_ne (e.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

theorem body_ok {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {σ : State} (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ)
    {s : State} (ht : VG.Proof.MlDsa.X86_64.Verify.T p σ s) : WP isa (body P p) s (VG.Proof.MlDsa.X86_64.Verify.Fin p σ) := by
  unfold body
  refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.hint_ok C hp hv ht) fun s₁ ⟨t₁, hm⟩ => ?_)
  split at hm
  · rename_i h hh
    obtain ⟨h15₁, hH⟩ := hm
    refine VG.Proof.MlDsa.X86_64.Verify.ifOk_ok (p := True) h15₁ (fun s₂ hP₂ e₂ _ => ?_) fun _ _ _ h => absurd trivial h
    obtain ⟨_, _, kh, _⟩ := VG.Proof.MlDsa.X86_64.Verify.parChk p hp
    have S : VG.Proof.MlDsa.X86_64.Verify.S2 p h 0 σ s₂ := ⟨t₁.step hp hv hP₂ (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), (t₁.lay hp hv).keepHint hP₂ kh hH,
      fun _ h => absurd h (Nat.not_lt_zero _), by rw [e₂, h15₁]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp)⟩
    refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.seqR_ok (I := fun i => VG.Proof.MlDsa.X86_64.Verify.S2 p h i σ) p.ℓ 0
      (fun i _ hi st hst => VG.Proof.MlDsa.X86_64.Verify.zOne_ok C hp hv (by omega) hst) s₂ S) fun s₃ hs₃ => ?_)
    rw [Nat.zero_add] at hs₃
    refine VG.Proof.MlDsa.X86_64.Verify.ifOk_ok hs₃.r15 (fun s₄ hP₄ e₄ hn => ?_) fun s₄ hP₄ e₄ hn => ?_
    · refine WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.samples_ok C hp hv (hs₃.flag hp hv (Nat.le_refl _) hP₄ e₄)
        (by rw [e₄, hs₃.r15]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (iff_true_intro hn))) fun s₅ hs₅ => VG.Proof.MlDsa.X86_64.Verify.cs_ok C hp hv hh hn hs₅)
    · obtain ⟨hg, hβ, _, _⟩ := VG.Proof.MlDsa.X86_64.Verify.parChk p hp
      exact ⟨hs₃.t.step hp hv hP₄ (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), .inr ⟨by rw [e₄, hs₃.r15]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (iff_false_intro hn),
        verifyMu_norm minBounds _ _ hh (by rw [normR_vZ_iff hβ p hg]; exact hn)⟩⟩
  · rename_i hh
    refine VG.Proof.MlDsa.X86_64.Verify.ifOk_ok (p := False) hm (fun _ _ _ h => h.elim) fun s₂ hP₂ e₂ _ =>
      ⟨t₁.step hp hv hP₂ (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), .inr ⟨by rw [e₂]; exact hm, ?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [verifyMu_hint_none minBounds _ _ hh]
    nofun

theorem verify_correct {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) (σ : State) (hv : VG.Proof.MlDsa.X86_64.Verify.VPre p σ) :
    ∃ t s', Exec isa (verify P p) σ t s' ∧ abiPreserved σ s' ∧ (VG.Proof.MlDsa.X86_64.Verify.verifyK p).post σ s' := by
  obtain ⟨t, s', he, hF⟩ := WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.pro_ok hp hv) fun s₁ ⟨h₁, _⟩ =>
    WP.seq (WP.mono (VG.Proof.MlDsa.X86_64.Verify.body_ok C hp hv h₁) fun s₂ ⟨h₂, hr⟩ =>
      WP.mono (VG.Proof.MlDsa.X86_64.Verify.epi_ok hp hv h₂) fun s₃ ⟨hres, hg⟩ =>
        (⟨hg, by
          rcases hr with ⟨e, hb⟩ | ⟨e, hb⟩
          · exact .inl ⟨by rw [hres, e]; rfl, hb⟩
          · exact .inr ⟨by rw [hres, e]; rfl, hb⟩⟩ : gprPreserved σ s₃ ∧ (VG.Proof.MlDsa.X86_64.Verify.verifyK p).post σ s₃)))
  exact ⟨t, s', he, abiPreserved_of_ctl (VG.Proof.MlDsa.X86_64.Verify.verify_ctl C hp) he hF.1, hF.2⟩

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTBase`. -/
section

/-!
# ML-DSA verification on x86-64: constant time, the pieces without calls

Two runs from inputs with the same public data (`RV`) keep the same pointers
(`T.lrel`). A block that accesses no memory, followed by code that the taint
analysis checks from the registers it sets (`blockLoop_tr`), leaks the same in
both: the copy (`copy_tr`), the mask of a sampler's output (`mask_tr`) and the
comparison (`cmpAnd_tr`). The rest is checked by the taint analysis.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Spec.MlDsa

/-- Two runs from states satisfying `VPre p` with the same public data, each
satisfying `I` from its own initial state. -/
abbrev RV (p : Params) (I : State → State → Prop) : State → State → Prop := Rel2 (VG.Proof.MlDsa.X86_64.Verify.VPre p) (VG.Proof.MlDsa.X86_64.Verify.verifyK p).pub I

theorem T.sameB {p : Params} {σ₁ σ₂ x y : State} (pub : (VG.Proof.MlDsa.X86_64.Verify.verifyK p).pub σ₁ σ₂) (h₁ : VG.Proof.MlDsa.X86_64.Verify.T p σ₁ x) (h₂ : VG.Proof.MlDsa.X86_64.Verify.T p σ₂ y) :
    VG.Proof.MlDsa.X86_64.Verify.SameB x y := by
  refine ⟨fun r hr => ?_, by rw [h₁.rsp, h₂.rsp, pub.2.2.2.2.1]⟩
  simp only [VG.Proof.MlDsa.X86_64.Verify.bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub.2.2.2.1]
  · rw [h₁.rbp, h₂.rbp, pub.1]
  · rw [h₁.r12, h₂.r12, pub.2.1]
  · rw [h₁.r13, h₂.r13, pub.2.2.1]

theorem RV.lrel {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s)
    {x y : State} (h : VG.Proof.MlDsa.X86_64.Verify.RV p I x y) : VG.Proof.MlDsa.X86_64.Verify.LRel (VG.Proof.MlDsa.X86_64.Verify.vR p) (VG.Proof.MlDsa.X86_64.Verify.vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩ := h
  exact ⟨(hI _ _ i₁).lay hp v₁, (hI _ _ i₂).lay hp v₂, T.sameB pub (hI _ _ i₁) (hI _ _ i₂)⟩

/-! ## A block without memory accesses, then code the taint analysis checks -/

theorem blockLoop_tr {B : List Instr} {L : Prog isa} {P : State → State → Prop}
    (hB : ∀ i ∈ B, ∀ s, isa.addrs i s = []) {F : State → State → Prop}
    (hw : ∀ x y, P x y → WP isa (.block B) x (F x) ∧ WP isa (.block B) y (F y)) (rs : List Reg)
    (hQ : ∀ x y x' y', P x y → F x x' → F y y' → ∀ r ∈ rs, x'.gpr r = y'.gpr r)
    {hc : VG.Taint.Hint X86_64.Taint.T} (h : (taint.check (X86_64.Taint.ofRegs rs) L hc).isSome = true) :
    RelCT isa P (.seq (.block B) L) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (VG.Proof.MlDsa.X86_64.Verify.block_nomem_tr hB) hw hQ) (taintRel rs (fun _ _ h => h) h)

theorem SameB.arg {x y : State} (h : VG.Proof.MlDsa.X86_64.Verify.SameB x y) {p : Ptr} (hp : p.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) : (Arg.ptr p).val x = (Arg.ptr p).val y :=
  h.pa hp

theorem copy_tr {dst src : Ptr} {n : Nat} (hok : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.copyArgs dst src n, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs)
    (hd : dst.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) (hs : src.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa P (copy dst src n) fun _ _ => True := by
  have nd : ((VG.Proof.MlDsa.X86_64.Verify.copyArgs dst src n).map (·.1)).Nodup := by simp only [List.map_cons, List.map_nil]; decide
  unfold copy
  refine VG.Proof.MlDsa.X86_64.Verify.blockLoop_tr (VG.Proof.MlDsa.X86_64.Verify.glue_nomem _) (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok nd x, VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok nd y⟩) [.rdi, .rsi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  have e := hP x y hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [hx.1.1 _ (List.mem_cons_self ..), hy.1.1 _ (List.mem_cons_self ..)]; exact e.arg hd
  · rw [hx.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)),
      hy.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))]; exact e.arg hs
  · rw [hx.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      hy.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))]; rfl

theorem maskPre_wp {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) {N : Nat} (hN : N < 2 ^ 31) (s : State) :
    WP isa (.block (([.mov32 .rdx (.imm 0), .alu32 .sub .rdx (.reg .rax)] : List Instr) ++
      glue [(.rdi, .ptr a), (.rcx, .imm N)])) s
      fun s' => s'.gpr .rdi = (Arg.ptr a).val s ∧ s'.gpr .rcx = BitVec.ofNat 64 N := by
  have hok' : ∀ x ∈ ([(.rdi, .ptr a), (.rcx, .imm N)] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨hok, by decide⟩, ⟨hN, by decide⟩⟩
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.maskPre_ok s) fun s₀ ⟨_, k₀⟩ => ?_
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok _ hok' (by simp only [List.map_cons, List.map_nil]; decide) s₀) fun s1 ⟨⟨hv1, _⟩, _⟩ =>
    ⟨?_, hv1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))⟩
  have nb : a.1 ∉ [Reg.rdx] := by
    simp only [List.mem_singleton]; intro h; rw [h] at hb; exact absurd hb (by decide)
  rw [hv1 _ (List.mem_cons_self ..)]
  simp only [Arg.val, VG.Proof.MlDsa.X86_64.Verify.pa]
  rw [k₀.gpr nb]

theorem mask_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) {N : Nat} (hN : N < 2 ^ 31)
    {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.X86_64.Verify.SameB x y) : RelCT isa P (mask a N) fun _ _ => True := by
  unfold mask
  refine VG.Proof.MlDsa.X86_64.Verify.blockLoop_tr (fun i hi s => ?_) (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Verify.maskPre_wp hok hb hN x, VG.Proof.MlDsa.X86_64.Verify.maskPre_wp hok hb hN y⟩)
    [.rdi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  · rcases List.mem_append.mp hi with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> rfl
    · exact VG.Proof.MlDsa.X86_64.Verify.glue_nomem _ i h s
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hx.1, hy.1]; exact (hP x y hp).arg hb
    · rw [hx.2, hy.2]

theorem cmpPre_wp {a b : Ptr} {n : Nat} (hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)),
      x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs) (s : State) :
    WP isa (.block (glue [(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] ++ ([.mov32 .rdx (.imm 0)] : List Instr))) s
      fun s' => s'.gpr .rsi = (Arg.ptr a).val s ∧ s'.gpr .rdi = (Arg.ptr b).val s ∧
        s'.gpr .rcx = (Arg.imm n).val s := by
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.MlDsa.X86_64.Verify.glue_ok' hok (by simp only [List.map_cons, List.map_nil]; decide) s) fun s1 h1 => ?_
  refine WP.mono (WP.keep [.rdx] (Q := fun s₂ => s₂.mem = s1.mem ∧ s₂.gpr .rdx = 0) (by xrun) (by decide)) fun s2 ⟨_, k2⟩ => ⟨?_, ?_, ?_⟩
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_self ..)
  · rw [k2.gpr (by decide)]; exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · rw [k2.gpr (by decide)]
    exact h1.1.1 _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

theorem cmpAnd_tr {a b : Ptr} {n : Nat}
    (hok : ∀ x ∈ ([(.rsi, .ptr a), (.rdi, .ptr b), (.rcx, .imm n)] : List (Reg × Arg)), x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs)
    (ha : a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) (hb : b.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) {P : State → State → Prop} (hP : ∀ x y, P x y → VG.Proof.MlDsa.X86_64.Verify.SameB x y) :
    RelCT isa P (cmpAnd a b n) fun _ _ => True := by
  unfold cmpAnd
  refine VG.Proof.MlDsa.X86_64.Verify.blockLoop_tr (fun i hi s => ?_) (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Verify.cmpPre_wp hok x, VG.Proof.MlDsa.X86_64.Verify.cmpPre_wp hok y⟩) [.rsi, .rdi, .rcx]
    (fun x y x' y' hp hx hy r hr => ?_) (by taint_decide)
  · rcases List.mem_append.mp hi with h | h
    · exact VG.Proof.MlDsa.X86_64.Verify.glue_nomem _ i h s
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [hx.1, hy.1]; exact (hP x y hp).arg ha
    · rw [hx.2.1, hy.2.1]; exact (hP x y hp).arg hb
    · rw [hx.2.2, hy.2.2]; rfl

/-! ## Blocks the taint analysis checks -/

theorem setB2_tr {x y : Nat} {P : State → State → Prop} (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rbx = s₂.gpr .rbx) :
    RelCT isa P (.block (setB (sc (oSB + 32)) x ++ setB (sc (oSB + 33)) y)) fun _ _ => True :=
  taintRel [.rbx] (fun s₁ s₂ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hP s₁ s₂ h)
    (hc := .block []) (by with_unfolding_all rfl)

theorem and15_tr {P : State → State → Prop} : RelCT isa P (.block and15) fun _ _ => True :=
  VG.Proof.MlDsa.X86_64.Verify.block_nomem_tr fun i hi s => by simp only [and15, List.mem_singleton] at hi; subst hi; rfl

theorem pro_tr {p : Params} : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p fun σ s => s = σ) (.block VG.Impl.MlDsa.X86_64.Verify.pro) fun _ _ => True :=
  taintRel [.rcx, .rdi, .rsi, .rdx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    subst h₁ h₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [pub.2.2.2.1, pub.1, pub.2.1, pub.2.2.1]) (by taint_decide)

theorem epi_tr {p : Params} : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.T p)) (.block VG.Impl.MlDsa.X86_64.Verify.epi) fun _ _ => True :=
  taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, pub, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    rw [h₁.rbx, h₂.rbx, pub.2.2.2.1]) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages`. -/
section

/-!
# ML-DSA verification on x86-64: constant time, the hint and `z`

Two runs with the same public data (`RV`) run the same code: each piece's
invariant holds of each run from its own inputs (`relInv`), which gives what
each call's trace needs (the pointers, reduced inputs, and the public bytes it
reads); the branches test results that are functions of the signature alone
(the hint is well formed, `z` is small: `ifOk_rel`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

theorem layOk : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, VG.Proof.MlDsa.X86_64.Verify.LayOk (VG.Proof.MlDsa.X86_64.Verify.vB p) := by unfold VG.Proof.MlDsa.X86_64.Verify.LayOk; decide

/-- Two runs after a piece `F` from states satisfying `I` keep the layout. -/
theorem RV.lrelStep {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {I : State → State → Prop} (hI : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s)
    {F : State → State → Prop} (hF : ∀ s₀ s, F s₀ s → ∃ W, VG.Proof.MlDsa.X86_64.Verify.PostB s₀ s W) {x y : State}
    (h : VG.Proof.MlDsa.X86_64.Verify.RV p (fun σ s => ∃ s₀, I σ s₀ ∧ F s₀ s) x y) : VG.Proof.MlDsa.X86_64.Verify.LRel (VG.Proof.MlDsa.X86_64.Verify.vR p) (VG.Proof.MlDsa.X86_64.Verify.vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, ⟨x₀, i₁, f₁⟩, ⟨y₀, i₂, f₂⟩⟩ := h
  obtain ⟨_, hx⟩ := hF _ _ f₁
  obtain ⟨_, hy⟩ := hF _ _ f₂
  exact (RV.lrel hp hI ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩).post hx hy

/-- A piece that keeps the layout leaves two runs with the same pointers. -/
theorem RelCT.sameB {P : State → State → Prop} {c : Prog isa} (ht : RelCT isa P c fun _ _ => True)
    (hw : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, VG.Proof.MlDsa.X86_64.Verify.PostB x x' W) ∧ WP isa c y (fun y' => ∃ W, VG.Proof.MlDsa.X86_64.Verify.PostB y y' W))
    (hs : ∀ x y, P x y → VG.Proof.MlDsa.X86_64.Verify.SameB x y) : RelCT isa P c fun x y => VG.Proof.MlDsa.X86_64.Verify.SameB x y :=
  RelCT.postDep ht hw fun x y _ _ hp ⟨_, hx⟩ ⟨_, hy⟩ => (hs x y hp).post hx hy

theorem and15_post (x : State) : WP isa (.block and15) x fun x' => ∃ W, VG.Proof.MlDsa.X86_64.Verify.PostB x x' W :=
  WP.mono (VG.Proof.MlDsa.X86_64.Verify.and15_ok x) fun x' ⟨⟨_, hm⟩, k⟩ =>
    ⟨_, (VG.Proof.MlDsa.X86_64.Verify.postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _) : VG.Proof.MlDsa.X86_64.Verify.PPostB x x' [])⟩

theorem sampledTail_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Verify.SameB x y) (.seq (.block and15) (mask a)) fun _ _ => True :=
  RelCT.seq (RelCT.sameB VG.Proof.MlDsa.X86_64.Verify.and15_tr (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Verify.and15_post x, VG.Proof.MlDsa.X86_64.Verify.and15_post y⟩) fun _ _ h => h)
    (VG.Proof.MlDsa.X86_64.Verify.mask_tr hok hb (N := 256) (by decide) fun _ _ h => h)

theorem sampledTail4_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.bases) :
    RelCT isa (fun x y => VG.Proof.MlDsa.X86_64.Verify.SameB x y) (.seq (.block and15) (mask a 1024)) fun _ _ => True :=
  RelCT.seq (RelCT.sameB VG.Proof.MlDsa.X86_64.Verify.and15_tr (fun x y _ => ⟨VG.Proof.MlDsa.X86_64.Verify.and15_post x, VG.Proof.MlDsa.X86_64.Verify.and15_post y⟩) fun _ _ h => h)
    (VG.Proof.MlDsa.X86_64.Verify.mask_tr hok hb (N := 1024) (by decide) fun _ _ h => h)

theorem flag_ne {P : Prop} [Decidable P] (h : (VG.Proof.MlDsa.X86_64.Verify.flag P).setWidth 32 ≠ 0) : P := by
  by_contra hn
  exact h (by unfold VG.Proof.MlDsa.X86_64.Verify.flag; rw [VG.Proof.MlKem.X86_64.ifn hn]; rfl)

/-! ## Branches -/

theorem ifOk_rel {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {I It : State → State → Prop} {c : Prog isa}
    (hT : ∀ σ s, I σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s)
    (he : ∀ x y, VG.Proof.MlDsa.X86_64.Verify.RV p I x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (hk : ∀ σ s₀ s, VG.Proof.MlDsa.X86_64.Verify.VPre p σ → I σ s₀ → VG.Proof.MlDsa.X86_64.Verify.PPostB s₀ s [] → s.gpr .r15 = s₀.gpr .r15 →
      (s₀.gpr .r15).setWidth 32 ≠ 0 → It σ s)
    (ht : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p It) c (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.T p))) : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p I) (VG.Impl.MlDsa.X86_64.Verify.ifOk c) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.T p)) := by
  refine VG.Proof.MlDsa.X86_64.Verify.ifOk_tr he (RelCT.mono ht (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩, hPx, hPy, ex, ey, hne⟩ =>
    ⟨σ₁, σ₂, v₁, v₂, pub, hk σ₁ x₀ x v₁ i₁ hPx ex hne, hk σ₂ y₀ y v₂ i₂ hPy ey
      (by rw [← he x₀ y₀ ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩]; exact hne)⟩) fun _ _ h => h) ?_
  rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩, hPx, hPy, _, _, _⟩
  exact ⟨σ₁, σ₂, v₁, v₂, pub, (hT _ _ i₁).step hp v₁ hPx (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), (hT _ _ i₂).step hp v₂ hPy (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp)⟩

/-! ## The hint -/

theorem S1.r15 {p : Params} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Verify.S1 p σ s) :
    s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag ((vHint p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ)).isSome = true) := by
  unfold VG.Proof.MlDsa.X86_64.Verify.S1 at h
  obtain ⟨_, hm⟩ := h
  split at hm
  · rename_i _ hh; rw [hm.1, hh]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp)
  · rename_i hh; rw [hm, hh]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp)

theorem hint_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p fun σ s => VG.Proof.MlDsa.X86_64.Verify.T p σ s ∧ s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True) (hint P p) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.S1 p)) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.hintChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, _⟩, c3⟩, c4⟩ := hc
  refine relInv (fun σ s hv hs => VG.Proof.MlDsa.X86_64.Verify.hint_ok C hp hv hs.1) ?_
  unfold hint
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.hintUnpackAt_tr C.hintUnpack (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) c3 c1 fun x y h => ?_)
    (VG.Proof.MlDsa.X86_64.Verify.block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
  have L := RV.lrel hp (fun _ _ h => h.1) h
  obtain ⟨σ₁, σ₂, _, _, pub, i₁, i₂⟩ := h
  exact ⟨L.1, L.2.1, L.2.2, by rw [i₁.1.sigSlice c4, i₂.1.sigSlice c4, pub.2.2.2.2.2.2.2]⟩

/-! ## `z` -/

/-- After `z[0], …, z[i - 1]`, with a well-formed hint. -/
def Iz (p : Params) (i : Nat) (σ s : State) : Prop := ∃ h, vHint p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) = some h ∧ VG.Proof.MlDsa.X86_64.Verify.S2 p h i σ s

theorem Iz.t {p : Params} {i : Nat} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Verify.Iz p i σ s) : VG.Proof.MlDsa.X86_64.Verify.T p σ s :=
  let ⟨_, _, hs⟩ := h; hs.t

theorem zOne_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {i : Nat} (hi : i < p.ℓ) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.Iz p i)) (zOne P p i) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.Iz p (i + 1))) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.zChk_all p hp i hi
  simp only [VG.Proof.MlDsa.X86_64.Verify.zChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩, _⟩, _⟩, c8⟩, c9⟩ := hc
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.zOne_ok C hp hv hi hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold zOne
  refine RelCT.seq (relInv (I' := fun σ s => ∃ s₀, VG.Proof.MlDsa.X86_64.Verify.Iz p i σ s₀ ∧
      (VG.Proof.MlDsa.X86_64.Verify.PPostB s₀ s [(pZ i, 1024)] ∧ ∃ f, PolyIs s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s₀ (pZ i)) f))
    (fun σ s hv hs => WP.mono (VG.Proof.MlDsa.X86_64.Verify.bitUnpackAt_ok C.bitUnpack (hs.t.lay hp hv) c2 c3 c1) fun _ ⟨hP, _, hq⟩ =>
      ⟨s, hs, hP, _, hq⟩)
    (VG.Proof.MlDsa.X86_64.Verify.bitUnpackAt_tr C.bitUnpack (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) c2 c3 c1 fun x y h => RV.lrel hp (fun _ _ h => h.t) h)) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.normLtAt_tr C.normLt (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) c9 c8 fun x y h => ?_) VG.Proof.MlDsa.X86_64.Verify.and15_tr
  have L := RV.lrelStep hp (fun _ _ h => Iz.t h) (fun _ _ f => ⟨_, f.1⟩) h
  obtain ⟨_, _, _, _, _, ⟨x₀, _, fx, _, hx⟩, ⟨y₀, _, fy, _, hy⟩⟩ := h
  exact ⟨L.1, L.2.1, by rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx fx]; exact hx.1, by rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx fy]; exact hy.1, L.2.2⟩

theorem zs_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.Iz p 0)) (VG.Impl.MlDsa.X86_64.Verify.seqR (zOne P p) 0 p.ℓ) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.Iz p p.ℓ)) := by
  have := VG.Proof.MlDsa.X86_64.Verify.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.Iz p i)) p.ℓ 0 fun i _ hi => VG.Proof.MlDsa.X86_64.Verify.zOne_tr C hp (by omega)
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample`. -/
section

/-!
# ML-DSA verification on x86-64: constant time, the samplers

The seed of each entry of `Â` (and of each four, `aGrp_tr`) is `ρ ‖ s ‖ r`,
and `c̃` a piece of the signature, public in both runs; each sampler's output
is masked with its result without a branch (`sampledTail_tr`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt aSeed)

/-- A well-formed hint `h`, and `z` small. -/
def HN (p : Params) (σ : State) (h : List (Vector Bool n)) : Prop :=
  vHint p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) = some h ∧ ∀ i < p.ℓ, normRq [toRq (vZ p (VG.Proof.MlDsa.X86_64.Verify.vSig p σ) i)] < p.γ₁ - p.β

/-- Before the samplers, after them and while sampling `Â`. -/
def Is (p : Params) (σ s : State) : Prop := ∃ h, VG.Proof.MlDsa.X86_64.Verify.HN p σ h ∧ VG.Proof.MlDsa.X86_64.Verify.S2 p h p.ℓ σ s ∧ s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True
def I4 (p : Params) (σ s : State) : Prop := ∃ h, VG.Proof.MlDsa.X86_64.Verify.HN p σ h ∧ VG.Proof.MlDsa.X86_64.Verify.S4 p h σ s
def IA (p : Params) (e : Nat) (σ s : State) : Prop := ∃ h, VG.Proof.MlDsa.X86_64.Verify.HN p σ h ∧ VG.Proof.MlDsa.X86_64.Verify.S3 p h e σ s

theorem IA.t {p : Params} {e : Nat} {σ s : State} (h : VG.Proof.MlDsa.X86_64.Verify.IA p e σ s) : VG.Proof.MlDsa.X86_64.Verify.T p σ s := let ⟨_, _, hs⟩ := h; hs.t

theorem seed_of {p : Params} {h : List (Vector Bool n)} {e r c : Nat} {σ s₀ s : State} (hs : VG.Proof.MlDsa.X86_64.Verify.S3 p h e σ s₀)
    (hP : VG.Proof.MlDsa.X86_64.Verify.PPostB s₀ s VG.Proof.MlDsa.X86_64.Verify.wsB) (hm : s.mem = (s₀.mem.writeW (VG.Proof.MlDsa.X86_64.Verify.pa s₀ (sc oSB) + BitVec.ofNat 64 32) (BitVec.ofNat 8 c)).writeW
      (VG.Proof.MlDsa.X86_64.Verify.pa s₀ (sc oSB) + BitVec.ofNat 64 33) (BitVec.ofNat 8 r)) :
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (sc oSB)) 34 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) r c := by
  rw [hP.pa (by decide), hm, VG.Proof.MlDsa.X86_64.Verify.seed_bytes, hs.rho, aSeed, VG.Proof.MlDsa.X86_64.Verify.integerToBytes_one, VG.Proof.MlDsa.X86_64.Verify.integerToBytes_one]

theorem aOne_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {e : Nat} (he : e < p.k * p.ℓ) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p e)) (aOne P p e) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p (e + 1))) := by
  have hck := VG.Proof.MlDsa.X86_64.Verify.aChk_all p hp e he
  have hkl := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp
  obtain ⟨hr, hc⟩ := VG.Proof.MlDsa.X86_64.Verify.entry_lt hp he
  simp only [VG.Proof.MlDsa.X86_64.Verify.aChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Nat.not_lt] at hck
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h32, h33⟩, hrej⟩, hin⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hck
  have hT : ∀ σ s, VG.Proof.MlDsa.X86_64.Verify.IA p e σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s := fun _ _ h => h.t
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.aOne_ok C hp hv he hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold aOne
  refine RelCT.seq (relInv (I' := fun σ s => ∃ s₀, VG.Proof.MlDsa.X86_64.Verify.IA p e σ s₀ ∧ (VG.Proof.MlDsa.X86_64.Verify.PPostB s₀ s VG.Proof.MlDsa.X86_64.Verify.wsB ∧ s.gpr .r15 = s₀.gpr .r15 ∧
      s.mem = (s₀.mem.writeW (VG.Proof.MlDsa.X86_64.Verify.pa s₀ (sc oSB) + BitVec.ofNat 64 32) (BitVec.ofNat 8 (e % p.ℓ))).writeW
        (VG.Proof.MlDsa.X86_64.Verify.pa s₀ (sc oSB) + BitVec.ofNat 64 33) (BitVec.ofNat 8 (e / p.ℓ))))
    (fun σ s hv hs => WP.mono (VG.Proof.MlDsa.X86_64.Verify.setB2_ok ((hT σ s hs).lay hp hv) h32 h33 (e % p.ℓ) (e / p.ℓ) (by omega) (by omega))
      fun _ h' => ⟨s, hs, h'⟩)
    (VG.Proof.MlDsa.X86_64.Verify.setB2_tr fun x y h => (RV.lrel hp hT h).2.2.1 .rbx (by decide))) ?_
  unfold VG.Impl.MlDsa.X86_64.Verify.sampled
  refine RelCT.seq (RelCT.sameB (VG.Proof.MlDsa.X86_64.Verify.rejNttAt_tr C.rejNtt (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) hrej fun x y h => ?_) (fun x y h => ?_)
    (fun x y h => (RV.lrelStep hp hT (fun _ _ f => ⟨_, f.1⟩) h).2.2))
    (VG.Proof.MlDsa.X86_64.Verify.sampledTail_tr (VG.Proof.MlDsa.X86_64.Verify.ptr_ok (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) hin) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide))
  · have L := RV.lrelStep hp hT (fun _ _ f => ⟨_, f.1⟩) h
    obtain ⟨σ₁, σ₂, _, _, pub, ⟨x₀, ⟨_, _, hx⟩, fx⟩, ⟨y₀, ⟨_, _, hy⟩, fy⟩⟩ := h
    exact ⟨L.1, L.2.1, L.2.2, by rw [VG.Proof.MlDsa.X86_64.Verify.seed_of hx fx.1 fx.2.2, VG.Proof.MlDsa.X86_64.Verify.seed_of hy fy.1 fy.2.2, pub.2.2.2.2.2.1]⟩
  · have L := RV.lrelStep hp hT (fun _ _ f => ⟨_, f.1⟩) h
    exact ⟨WP.mono (VG.Proof.MlDsa.X86_64.Verify.rejNttAt_ok C.rejNtt L.1 hrej) fun _ h' => ⟨_, h'.1⟩,
      WP.mono (VG.Proof.MlDsa.X86_64.Verify.rejNttAt_ok C.rejNtt L.2.1 hrej) fun _ h' => ⟨_, h'.1⟩⟩

theorem bytes136 (m : Mem) (P : Addr) : bytesAt m P 136 = bytesAt m P 34 ++ bytesAt m (P + BitVec.ofNat 64 34) 34 ++
    bytesAt m (P + BitVec.ofNat 64 68) 34 ++ bytesAt m (P + BitVec.ofNat 64 102) 34 := by
  rw [show 136 = 34 + 102 from rfl, Proof.MlKem.bytesAt_add, show 102 = 34 + 68 from rfl, Proof.MlKem.bytesAt_add,
    show 68 = 34 + 34 from rfl, Proof.MlKem.bytesAt_add]
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, List.append_assoc, Nat.reduceAdd]

/-- The four seeds of `SB4`, for the entries `e, …, e + 3`. -/
theorem GS.seeds {p : Params} {h : List (Vector Bool n)} {e : Nat} {σ s : State} (g : VG.Proof.MlDsa.X86_64.Verify.GS p h e 4 σ s) :
    bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (sc oSB4)) 136 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) ++
      aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) ++ aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) ++
      aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
  have ek : ∀ k, VG.Proof.MlDsa.X86_64.Verify.pa s (sc (oSB4 + 34 * k)) = VG.Proof.MlDsa.X86_64.Verify.pa s (sc oSB4) + BitVec.ofNat 64 (34 * k) := fun k => by
    simp only [VG.Proof.MlDsa.X86_64.Verify.pa]; rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have b0 : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (sc oSB4)) 34 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 0) / p.ℓ) ((e + 0) % p.ℓ) := g.done 0 (by decide)
  have b1 : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (sc oSB4) + BitVec.ofNat 64 34) 34 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 1) / p.ℓ) ((e + 1) % p.ℓ) := by
    have := g.done 1 (by decide); rw [ek] at this; exact this
  have b2 : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (sc oSB4) + BitVec.ofNat 64 68) 34 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 2) / p.ℓ) ((e + 2) % p.ℓ) := by
    have := g.done 2 (by decide); rw [ek] at this; exact this
  have b3 : bytesAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (sc oSB4) + BitVec.ofNat 64 102) 34 = aSeed (VG.Proof.MlDsa.X86_64.Verify.vPk p σ) ((e + 3) / p.ℓ) ((e + 3) % p.ℓ) := by
    have := g.done 3 (by decide); rw [ek] at this; exact this
  rw [VG.Proof.MlDsa.X86_64.Verify.bytes136, b0, b1, b2, b3]

theorem slotBlock_tr {p : Params} {e j : Nat} {P : State → State → Prop}
    (hP : ∀ s₁ s₂, P s₁ s₂ → s₁.gpr .rbx = s₂.gpr .rbx) :
    RelCT isa P (.block (setSR p e j)) fun _ _ => True :=
  taintRel [.rbx] (fun s₁ s₂ h r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hP s₁ s₂ h)
    (hc := .block []) (by with_unfolding_all rfl)

/-- The bytes of seed `j` of `SB4`, from `GS j` to `GS (j + 1)`. -/
theorem slot_tr {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {e j : Nat} (hj : j < 4) (he : e + j < p.k * p.ℓ)
    (hck : VG.Proof.MlDsa.X86_64.Verify.slotChk p e j = true) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p fun σ s => ∃ h, VG.Proof.MlDsa.X86_64.Verify.HN p σ h ∧ VG.Proof.MlDsa.X86_64.Verify.GS p h e j σ s) (.block (setSR p e j))
      (VG.Proof.MlDsa.X86_64.Verify.RV p fun σ s => ∃ h, VG.Proof.MlDsa.X86_64.Verify.HN p σ h ∧ VG.Proof.MlDsa.X86_64.Verify.GS p h e (j + 1) σ s) :=
  relInv (fun σ s hv ⟨h, hh, g⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.slot_ok hp hv hj he hck g) fun _ g' => ⟨h, hh, g'⟩)
    (VG.Proof.MlDsa.X86_64.Verify.slotBlock_tr fun x y h => (RV.lrel hp (fun _ _ h => let ⟨_, _, g⟩ := h; g.s3.t) h).2.2.1 .rbx (by decide))

theorem aGrp_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {g : Nat}
    (hck : VG.Proof.MlDsa.X86_64.Verify.gChk p (4 * g) = true) : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p (4 * g))) (aGrp P p g) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p (4 * (g + 1)))) := by
  have hck' := hck
  simp only [VG.Proof.MlDsa.X86_64.Verify.gChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hck'
  obtain ⟨⟨⟨⟨⟨hsl, hrej⟩, hin⟩, _⟩, _⟩, hl⟩ := hck'
  have hTG : ∀ σ s, (∃ h, VG.Proof.MlDsa.X86_64.Verify.HN p σ h ∧ VG.Proof.MlDsa.X86_64.Verify.GS p h (4 * g) 4 σ s) → VG.Proof.MlDsa.X86_64.Verify.T p σ s := fun _ _ ⟨_, _, g⟩ => g.s3.t
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.aGrp_ok C hp hv hck hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold aGrp
  refine RelCT.seq (RelCT.mono (VG.Proof.MlDsa.X86_64.Verify.slot_tr hp (by decide) (by omega) (hsl 0 (by decide)))
    (fun x y ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, s₁⟩, ⟨h₂, hh₂, s₂⟩⟩ => ⟨σ₁, σ₂, v₁, v₂, pub,
      ⟨h₁, hh₁, s₁, fun _ h => absurd h (by omega)⟩, ⟨h₂, hh₂, s₂, fun _ h => absurd h (by omega)⟩⟩)
    fun _ _ h => h) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.slot_tr hp (by decide) (by omega) (hsl 1 (by decide))) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.slot_tr hp (by decide) (by omega) (hsl 2 (by decide))) ?_
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.slot_tr hp (by decide) (by omega) (hsl 3 (by decide))) ?_
  unfold VG.Impl.MlDsa.X86_64.Verify.sampled4
  refine RelCT.seq (RelCT.sameB (VG.Proof.MlDsa.X86_64.Verify.rej4At_tr C.rej4 (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) hrej fun x y h => ?_) (fun x y h => ?_)
    (fun x y h => (RV.lrel hp hTG h).2.2))
    (VG.Proof.MlDsa.X86_64.Verify.sampledTail4_tr (VG.Proof.MlDsa.X86_64.Verify.ptr_ok (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) hin) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide))
  · have L := RV.lrel hp hTG h
    obtain ⟨σ₁, σ₂, _, _, pub, ⟨_, _, gx⟩, ⟨_, _, gy⟩⟩ := h
    exact ⟨L.1, L.2.1, L.2.2, by rw [gx.seeds, gy.seeds, pub.2.2.2.2.2.1]⟩
  · have L := RV.lrel hp hTG h
    exact ⟨WP.mono (VG.Proof.MlDsa.X86_64.Verify.rej4At_ok C.rej4 L.1 hrej) fun _ h' => ⟨_, h'.1⟩,
      WP.mono (VG.Proof.MlDsa.X86_64.Verify.rej4At_ok C.rej4 L.2.1 hrej) fun _ h' => ⟨_, h'.1⟩⟩

theorem ballStage_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p (p.k * p.ℓ))) (VG.Impl.MlDsa.X86_64.Verify.sampled (ballAt P (.r13, 0) p.ctildeLen p.τ pC) pC) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.I4 p)) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.sChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, c5⟩, c6⟩, c7⟩, _⟩, c9⟩, _⟩, _⟩ := hc
  have hT : ∀ σ s, VG.Proof.MlDsa.X86_64.Verify.IA p (p.k * p.ℓ) σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s := fun _ _ h => h.t
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.ballStage_ok C hp hv hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold VG.Impl.MlDsa.X86_64.Verify.sampled
  refine RelCT.seq (RelCT.sameB (VG.Proof.MlDsa.X86_64.Verify.ballAt_tr C.ball (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) c6 c5 fun x y h => ?_) (fun x y h => ?_)
    (fun x y h => (RV.lrel hp hT h).2.2)) (VG.Proof.MlDsa.X86_64.Verify.sampledTail_tr (VG.Proof.MlDsa.X86_64.Verify.ptr_ok (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) c9) (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide))
  · have L := RV.lrel hp hT h
    obtain ⟨σ₁, σ₂, _, _, pub, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩ := h
    exact ⟨L.1, L.2.1, L.2.2, by rw [hx.t.sigSlice (by omega : 0 + p.ctildeLen ≤ p.sigLen),
      hy.t.sigSlice (by omega : 0 + p.ctildeLen ≤ p.sigLen), pub.2.2.2.2.2.2.2]⟩
  · have L := RV.lrel hp hT h
    exact ⟨WP.mono (VG.Proof.MlDsa.X86_64.Verify.ballAt_ok C.ball L.1 c6 c5) fun _ h' => ⟨_, h'.1⟩,
      WP.mono (VG.Proof.MlDsa.X86_64.Verify.ballAt_ok C.ball L.2.1 c6 c5) fun _ h' => ⟨_, h'.1⟩⟩

/-- While copying `ρ`. -/
def IRho (p : Params) (j : Nat) (σ s : State) : Prop := ∃ h, VG.Proof.MlDsa.X86_64.Verify.HN p σ h ∧ VG.Proof.MlDsa.X86_64.Verify.RhoS p h j σ s

theorem copyK_tr {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {j : Nat} (hj : j < 4) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRho p j)) (copy (sc (oSB4 + 34 * j)) (.rbp, 0) 32) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRho p (j + 1))) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.rChk_all p hp j hj
  simp only [VG.Proof.MlDsa.X86_64.Verify.rChk, Bool.and_eq_true] at hc
  have hS := VG.Proof.MlDsa.X86_64.Verify.layOk p hp
  have hsd' := VG.Proof.MlDsa.X86_64.Verify.sepB_spec hc.1.1.1.1
  have hok : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.copyArgs (sc (oSB4 + 34 * j)) (.rbp, 0) 32, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hsd'.2.1, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hsd'.1, by decide⟩, ⟨show 32 < 2 ^ 31 by decide, by decide⟩⟩
  exact relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyK_ok hp hv hj hs) fun _ h' => ⟨h, hh, h'⟩)
    (VG.Proof.MlDsa.X86_64.Verify.copy_tr hok (show Reg.rbx ∈ VG.Proof.MlDsa.X86_64.Verify.bases by decide) (by decide) fun x y h =>
      (RV.lrel hp (fun _ _ h => let ⟨_, _, hs⟩ := h; hs.t) h).2.2)

theorem samples_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.Is p)) (VG.Impl.MlDsa.X86_64.Verify.samples P p) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.I4 p)) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.sChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.sChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c1, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hc
  have hS := VG.Proof.MlDsa.X86_64.Verify.layOk p hp
  have hsd' := VG.Proof.MlDsa.X86_64.Verify.sepB_spec c1
  have hok : ∀ a ∈ VG.Proof.MlDsa.X86_64.Verify.copyArgs (sc oSB) (.rbp, 0) 32, a.2.Ok ∧ a.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hsd'.2.1, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS hsd'.1, by decide⟩, ⟨show 32 < 2 ^ 31 by decide, by decide⟩⟩
  unfold VG.Impl.MlDsa.X86_64.Verify.samples rhos
  refine RelCT.seq (RelCT.seq (relInv (I' := VG.Proof.MlDsa.X86_64.Verify.IRho p 0)
    (fun σ s hv ⟨h, hh, hs, h15⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.copyRho_ok hp hv hs h15) fun _ h' => ⟨h, hh, h'⟩)
    (VG.Proof.MlDsa.X86_64.Verify.copy_tr hok (by decide) (by decide) fun x y h =>
      (RV.lrel hp (fun _ _ h => let ⟨_, _, hs, _⟩ := h; hs.t) h).2.2))
    (RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.copyK_tr hp (j := 0) (by decide)) (RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.copyK_tr hp (j := 1) (by decide))
      (RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.copyK_tr hp (j := 2) (by decide)) (RelCT.mono (VG.Proof.MlDsa.X86_64.Verify.copyK_tr hp (j := 3) (by decide)) (fun _ _ h => h)
        (Q' := VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p 0)) fun x y h => ?_))))) (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p (4 * (p.k * p.ℓ / 4)))) ?_
    (RelCT.seq (R := VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p (p.k * p.ℓ))) ?_ (VG.Proof.MlDsa.X86_64.Verify.ballStage_tr C hp)))
  · obtain ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, r₁⟩, ⟨h₂, hh₂, r₂⟩⟩ := h
    exact ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, hh₁, r₁.s3⟩, ⟨h₂, hh₂, r₂.s3⟩⟩
  · have := VG.Proof.MlDsa.X86_64.Verify.seqR_tr (R := fun g => VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p (4 * g))) (p.k * p.ℓ / 4) 0 fun g _ hg =>
      VG.Proof.MlDsa.X86_64.Verify.aGrp_tr C hp (VG.Proof.MlDsa.X86_64.Verify.gChk_all p hp g (by omega))
    rwa [Nat.zero_add] at this
  · have := VG.Proof.MlDsa.X86_64.Verify.seqR_tr (R := fun e => VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IA p e)) (p.k * p.ℓ % 4) (4 * (p.k * p.ℓ / 4)) fun e _ he =>
      VG.Proof.MlDsa.X86_64.Verify.aOne_tr C hp (by omega)
    rwa [Nat.div_add_mod] at this

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute`. -/
section

/-!
# ML-DSA verification on x86-64: constant time, `w′₁`, the hash and the comparison

Each run's invariant is `SC` at the start of a row, with the facts after each
step of it (`IRX`), which give each call's trace the reduced inputs it needs.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt useHint_le w1Row)

/-- Two runs whose states lie within the layout from states satisfying `T`. -/
theorem RV.lrelOf {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {I : State → State → Prop}
    (hI : ∀ σ s, I σ s → ∃ s₀ W, VG.Proof.MlDsa.X86_64.Verify.T p σ s₀ ∧ VG.Proof.MlDsa.X86_64.Verify.PostB s₀ s W) {x y : State} (h : VG.Proof.MlDsa.X86_64.Verify.RV p I x y) :
    VG.Proof.MlDsa.X86_64.Verify.LRel (VG.Proof.MlDsa.X86_64.Verify.vR p) (VG.Proof.MlDsa.X86_64.Verify.vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩ := h
  obtain ⟨x₀, _, t₁, hx⟩ := hI _ _ i₁
  obtain ⟨y₀, _, t₂, hy⟩ := hI _ _ i₂
  exact ⟨(t₁.lay hp v₁).post hx, (t₂.lay hp v₂).post hy, (T.sameB pub t₁ t₂).post hx hy⟩

/-- While computing, before `ẑ` and `ĉ`, and at the start of row `r`. -/
def IC (p : Params) (j : Nat) (σ s : State) : Prop :=
  ∃ (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (q : Bool) (cH : Poly), VG.Proof.MlDsa.X86_64.Verify.SC p h A' (q = true) j cH 0 σ s
def IR (p : Params) (r : Nat) (σ s : State) : Prop :=
  ∃ (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (q : Bool) (cH : Poly), VG.Proof.MlDsa.X86_64.Verify.SC p h A' (q = true) p.ℓ cH r σ s

/-- In row `r`, after a piece: `F` of the state at the start of the row. -/
def IRX (p : Params) (r : Nat)
    (F : List (Vector Bool n) → (Nat → Nat → Poly) → Poly → State → State → State → Prop) (σ s : State) : Prop :=
  ∃ (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (q : Bool) (cH : Poly) (s₀ : State),
    VG.Proof.MlDsa.X86_64.Verify.SC p h A' (q = true) p.ℓ cH r σ s₀ ∧ F h A' cH σ s₀ s

section
variable {p : Params} {r : Nat}
  {F F' : List (Vector Bool n) → (Nat → Nat → Poly) → Poly → State → State → State → Prop}

theorem IRX.lrel (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) (hF : ∀ h A' cH σ s₀ s, F h A' cH σ s₀ s → ∃ W, VG.Proof.MlDsa.X86_64.Verify.PostB s₀ s W) {x y : State}
    (h : VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRX p r F) x y) : VG.Proof.MlDsa.X86_64.Verify.LRel (VG.Proof.MlDsa.X86_64.Verify.vR p) (VG.Proof.MlDsa.X86_64.Verify.vW p) x y :=
  RV.lrelOf hp (fun _ _ ⟨_, _, _, _, s₀, hs, hf⟩ => let ⟨W, hW⟩ := hF _ _ _ _ _ _ hf; ⟨s₀, W, hs.t, hW⟩) h

theorem IRX.step {c : Prog isa}
    (hw : ∀ h A' (q : Bool) cH σ s₀ s, VG.Proof.MlDsa.X86_64.Verify.VPre p σ → VG.Proof.MlDsa.X86_64.Verify.SC p h A' (q = true) p.ℓ cH r σ s₀ → F h A' cH σ s₀ s →
      WP isa c s (F' h A' cH σ s₀))
    (ht : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRX p r F)) c fun _ _ => True) : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRX p r F)) c (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRX p r F')) :=
  relInv (fun σ s hv ⟨h, A', q, cH, s₀, hs, hf⟩ => WP.mono (hw h A' q cH σ s₀ s hv hs hf)
    fun _ h' => ⟨h, A', q, cH, s₀, hs, h'⟩) ht

end

/-! ## `ẑ` and `ĉ` -/

theorem nttZ_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {i : Nat} (hi : i < p.ℓ) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IC p i)) (nttAt P (pZ i)) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IC p (i + 1))) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.nttChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨c1, _⟩, _⟩ := hc.1.1 i hi
  have hT : ∀ σ s, VG.Proof.MlDsa.X86_64.Verify.IC p i σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.nttZ_ok C hp hv hi hs) fun _ h' => ⟨h, A', q, cH, h'⟩)
    (VG.Proof.MlDsa.X86_64.Verify.ipAt_tr C.ntt (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) c1 fun x y hxy => ?_)
  have L := RV.lrel hp hT hxy
  obtain ⟨_, _, _, _, _, ⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := hxy
  exact ⟨L.1, L.2.1, (hx.z i hi).1, (hy.z i hi).1, L.2.2⟩

theorem nttC_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IC p p.ℓ)) (nttAt P pC) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IR p 0)) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.nttChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨_, c1⟩, _⟩ := hc
  have hT : ∀ σ s, VG.Proof.MlDsa.X86_64.Verify.IC p p.ℓ σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.nttC_ok C hp hv hs) fun _ h' => ⟨h, A', q, _, h'⟩)
    (VG.Proof.MlDsa.X86_64.Verify.ipAt_tr C.ntt (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) c1 fun x y hxy => ?_)
  have L := RV.lrel hp hT hxy
  obtain ⟨_, _, _, _, _, ⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := hxy
  exact ⟨L.1, L.2.1, hx.c.1, hy.c.1, L.2.2⟩

/-! ## A row -/

section Row
variable {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) {r : Nat} (hr : r < p.k)
include C hp hr

theorem dot_tr : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IR p r)) (dot P p r)
    (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRX p r fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r p.ℓ s₀ s)) := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  obtain ⟨_, _, hZ, hA⟩ := VG.Proof.MlDsa.X86_64.Verify.keepC_spec R.keep
  have hT : ∀ σ s, VG.Proof.MlDsa.X86_64.Verify.IR p r σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  unfold dot
  refine RelCT.seq (relInv (I' := VG.Proof.MlDsa.X86_64.Verify.IRX p r fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r 1 s₀ s)
    (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.dotFirst_ok C hp hv hr hs) fun _ h' => ⟨h, A', q, cH, s, hs, h'⟩)
    (VG.Proof.MlDsa.X86_64.Verify.mulAt_tr C.mul (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) (R.mul 0 R.l1) fun x y hxy => ?_)) ?_
  · have L := RV.lrel hp hT hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, ⟨(hx.a r hr 0 R.l1).1, (hx.zHat R.l1).1⟩, ⟨(hy.a r hr 0 R.l1).1, (hy.zHat R.l1).1⟩, L.2.2⟩
  have hs := VG.Proof.MlDsa.X86_64.Verify.seqR_tr (R := fun j => VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRX p r fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r j s₀ s)) (p.ℓ - 1) 1
    fun k hk hk' => IRX.step (fun h A' q cH σ s₀ s hv hs hd => VG.Proof.MlDsa.X86_64.Verify.dotStep_ok C hp hv hr hs (by omega) hd)
      (VG.Proof.MlDsa.X86_64.Verify.mulAddAt_tr C.mulAdd (VG.Proof.MlDsa.X86_64.Verify.layOk p hp) (R.mul k (by omega)) fun x y hxy => ?_)
  · rwa [show 1 + (p.ℓ - 1) = p.ℓ by have := R.l1; omega] at hs
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hd => ⟨_, hd.1⟩) hxy
    have hz : k ≠ 100 := by have := VG.Proof.MlDsa.X86_64.Verify.kl_le p hp; omega
    have red : ∀ {σ s}, VG.Proof.MlDsa.X86_64.Verify.VPre p σ → VG.Proof.MlDsa.X86_64.Verify.IRX p r (fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.DI p σ A' r k s₀ s) σ s →
        Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pA p.ℓ r k)) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s (pZ k)) :=
      fun hv ⟨_, _, _, _, s₀, hs, hP, _, hW⟩ => by
        have L₀ := hs.t.lay hp hv
        have H := hP.mono (VG.Proof.MlDsa.X86_64.Verify.sub1 (VG.Proof.MlDsa.X86_64.Verify.wsR_mem p r).1)
        exact ⟨by rw [VG.Proof.MlDsa.X86_64.Verify.pa_rbx hP]; exact hW.1, L₀.keepRed H (hA r hr k (by omega)) (hs.a r hr k (by omega)).1,
          L₀.keepRed H (hZ k (by omega) hz) (hs.zHat (by omega)).1⟩
    obtain ⟨_, _, v₁, v₂, _, i₁, i₂⟩ := hxy
    exact ⟨L.1, L.2.1, red v₁ i₁, red v₂ i₂, L.2.2⟩

omit C in
theorem RF7.bound {σ : State} {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {cH : Poly} {s₀ s : State}
    (hf : VG.Proof.MlDsa.X86_64.Verify.RF7 p σ h A' cH r s₀ s) : ∀ i < n, (coeffAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW1) i).toNat ≤ w1Max p := fun i hi => by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have hq₇ : natPolyAt s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pW1) = _ := hf.2
  have := congrArg (·[i]'hi) hq₇
  simp only [natPolyAt, Vector.getElem_ofFn, w1Row, Vector.getElem_zipWith] at this
  rw [this, R.max]
  exact useHint_le R.g2 _ _

theorem rowRest_tr : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IRX p r fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF1 p σ A' r s₀ s))
    (.seq (unpackT1At P (.rbp, 32 + 320 * r) pT) (.seq (nttAt P pT) (.seq (mulAt P pT2 pC pT)
      (.seq (subAt P pW pT2) (.seq (invNttAt P pW) (.seq (useHintAt P (pH r) pW p.γ₂ pW1)
        (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p))))))))
    fun _ _ => True := by
  have R := VG.Proof.MlDsa.X86_64.Verify.rowC hp hr
  have hS := VG.Proof.MlDsa.X86_64.Verify.layOk p hp
  refine RelCT.seq (IRX.step (F' := fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF2 p σ A' r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => VG.Proof.MlDsa.X86_64.Verify.row1_ok C hp hv hr hs hf)
    (VG.Proof.MlDsa.X86_64.Verify.unpackT1At_tr C.unpackT1 hS R.t1 fun x y hxy => IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy)) ?_
  refine RelCT.seq (IRX.step (F' := fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF3 p σ A' r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => VG.Proof.MlDsa.X86_64.Verify.row2_ok C hp hv hr hs hf)
    (VG.Proof.MlDsa.X86_64.Verify.ipAt_tr C.ntt hS R.ipT fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, hx.2.1, hy.2.1, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun _ A' cH σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF4 p σ A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => VG.Proof.MlDsa.X86_64.Verify.row3_ok C hp hv hr hs hf)
    (VG.Proof.MlDsa.X86_64.Verify.mulAt_tr C.mul hS R.mulT fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1.1⟩) hxy
    have red : ∀ {σ s}, VG.Proof.MlDsa.X86_64.Verify.VPre p σ → VG.Proof.MlDsa.X86_64.Verify.IRX p r (fun _ A' _ σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF3 p σ A' r s₀ s) σ s →
        Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pC) ∧ Reduced s.mem (VG.Proof.MlDsa.X86_64.Verify.pa s pT) := fun hv ⟨_, _, _, _, _, hs, hf⟩ =>
      ⟨(hs.t.lay hp hv).keepRed hf.1.1.1 R.keepC' hs.c.1, hf.2.1⟩
    obtain ⟨_, _, v₁, v₂, _, i₁, i₂⟩ := hxy
    exact ⟨L.1, L.2.1, red v₁ i₁, red v₂ i₂, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun _ A' cH σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF5 p σ A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => VG.Proof.MlDsa.X86_64.Verify.row4_ok C hp hv hr hs hf)
    (VG.Proof.MlDsa.X86_64.Verify.subAt_tr C.sub hS R.sub fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, ⟨hx.1.2.1, hx.2.1⟩, ⟨hy.1.2.1, hy.2.1⟩, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun _ A' cH σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF6 p σ A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => VG.Proof.MlDsa.X86_64.Verify.row5_ok C hp hv hr hs hf)
    (VG.Proof.MlDsa.X86_64.Verify.ipAt_tr C.invNtt hS R.ipW fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, hx.2.1, hy.2.1, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun h A' cH σ s₀ s => VG.Proof.MlDsa.X86_64.Verify.RF7 p σ h A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => VG.Proof.MlDsa.X86_64.Verify.row6_ok C hp hv hr hs hf)
    (VG.Proof.MlDsa.X86_64.Verify.useHintAt_tr C.useHint hS R.g2 R.uh fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, hx.2.1, hy.2.1, L.2.2⟩
  refine VG.Proof.MlDsa.X86_64.Verify.sbpAt_tr C.simpleBitPack hS R.sbpB R.len R.sbp fun x y hxy => ?_
  have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy
  obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
  exact ⟨L.1, L.2.1, RF7.bound hp hr hx, RF7.bound hp hr hy, L.2.2⟩

theorem row_tr : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IR p r)) (row P p r) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IR p (r + 1))) := by
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.row_ok C hp hv hr hs) fun _ h' => ⟨h, A', q, cH, h'⟩) ?_
  unfold row
  exact RelCT.seq (RelCT.mono (VG.Proof.MlDsa.X86_64.Verify.dot_tr C hp hr) (fun _ _ h => h)
    fun _ _ ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, A₁, q₁, c₁, x₀, hx, dx⟩, ⟨h₂, A₂, q₂, c₂, y₀, hy, dy⟩⟩ =>
      ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, A₁, q₁, c₁, x₀, hx, DI.rf1 dx⟩, ⟨h₂, A₂, q₂, c₂, y₀, hy, DI.rf1 dy⟩⟩)
    (VG.Proof.MlDsa.X86_64.Verify.rowRest_tr C hp hr)

end Row

/-! ## The whole computation -/

theorem compute_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IC p 0)) (compute P p) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.T p)) := by
  have hc := VG.Proof.MlDsa.X86_64.Verify.compChk_all p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.compChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨c1, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  unfold compute
  have hz : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IC p 0)) (VG.Impl.MlDsa.X86_64.Verify.seqR (fun i => nttAt P (pZ i)) 0 p.ℓ) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IC p p.ℓ)) := by
    have := VG.Proof.MlDsa.X86_64.Verify.seqR_tr (R := fun i => VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IC p i)) p.ℓ 0 fun i _ hi => VG.Proof.MlDsa.X86_64.Verify.nttZ_tr C hp (by omega)
    rwa [Nat.zero_add] at this
  have hrows : RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IR p 0)) (VG.Impl.MlDsa.X86_64.Verify.seqR (row P p) 0 p.k) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IR p p.k)) := by
    have := VG.Proof.MlDsa.X86_64.Verify.seqR_tr (R := fun r => VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.IR p r)) p.k 0 fun r _ hr => VG.Proof.MlDsa.X86_64.Verify.row_tr C hp (by omega)
    rwa [Nat.zero_add] at this
  refine RelCT.seq hz (RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.nttC_tr C hp) (RelCT.seq hrows ?_))
  have hT : ∀ σ s, VG.Proof.MlDsa.X86_64.Verify.IR p p.k σ s → VG.Proof.MlDsa.X86_64.Verify.T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  have hS := VG.Proof.MlDsa.X86_64.Verify.layOk p hp
  have hok : ∀ x ∈ ([(.rsi, .ptr (sc VG.Impl.MlDsa.X86_64.Verify.oCT)), (.rdi, .ptr (.r13, 0)), (.rcx, .imm p.ctildeLen)] : List (Reg × Arg)),
      x.2.Ok ∧ x.1 ∈ VG.Proof.MlDsa.X86_64.Verify.argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    have hn' : p.ctildeLen < 2 ^ 31 := by obtain ⟨m, hm, hl⟩ := VG.Proof.MlDsa.X86_64.Verify.inB_spec c3; have := (hS _ hm).1; omega
    exact ⟨⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c3, by decide⟩, ⟨VG.Proof.MlDsa.X86_64.Verify.ptr_ok hS c4, by decide⟩, ⟨hn', by decide⟩⟩
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (VG.Proof.MlDsa.X86_64.Verify.tail_ok hp hv hs) fun _ h' => h'.1) ?_
  refine RelCT.seq (RelCT.sameB (RelCT.mono (VG.Proof.MlDsa.X86_64.Verify.hash2_tr hS c1) (fun x y h => RV.lrel hp hT h) fun _ _ h => h)
    (fun x y hxy => ?_) (fun x y h => (RV.lrel hp hT h).2.2))
    (VG.Proof.MlDsa.X86_64.Verify.cmpAnd_tr hok (by decide) (by decide) fun _ _ h => h)
  have L := RV.lrel hp hT hxy
  exact ⟨WP.mono (VG.Proof.MlDsa.X86_64.Verify.hash2_ok L.1 c1) fun _ h' => ⟨_, h'.1⟩, WP.mono (VG.Proof.MlDsa.X86_64.Verify.hash2_ok L.2.1 c1) fun _ h' => ⟨_, h'.1⟩⟩

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified`. -/
section

/-!
# ML-DSA verification on x86-64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

For primitives `P` that meet their contracts (`PrimsOk`), `verify P p` meets
`verifyContract p` (`verify_verified`): it is correct (`verify_correct`) and
leaks only its inputs, which the contract makes public (`verify_ct`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

theorem body_tr {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    RelCT isa (VG.Proof.MlDsa.X86_64.Verify.RV p fun σ s => VG.Proof.MlDsa.X86_64.Verify.T p σ s ∧ s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True) (body P p) (VG.Proof.MlDsa.X86_64.Verify.RV p (VG.Proof.MlDsa.X86_64.Verify.T p)) := by
  unfold body
  refine RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.hint_tr C hp) (VG.Proof.MlDsa.X86_64.Verify.ifOk_rel hp (fun _ _ h => h.1) ?_ ?_ (RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.zs_tr C hp)
    (VG.Proof.MlDsa.X86_64.Verify.ifOk_rel hp (fun _ _ h => Iz.t h) ?_ ?_ (RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.samples_tr C hp)
      (RelCT.mono (VG.Proof.MlDsa.X86_64.Verify.compute_tr C hp) ?_ fun _ _ h => h)))))
  · rintro x y ⟨σ₁, σ₂, _, _, pub, i₁, i₂⟩
    rw [S1.r15 i₁, S1.r15 i₂, pub.2.2.2.2.2.2.2]
  · intro σ s₀ s hv h₀ hP e hne
    have t₀ := h₀.1
    unfold VG.Proof.MlDsa.X86_64.Verify.S1 at h₀
    obtain ⟨_, hm⟩ := h₀
    split at hm
    · rename_i h hh
      obtain ⟨h15, hH⟩ := hm
      obtain ⟨_, _, kh, _⟩ := VG.Proof.MlDsa.X86_64.Verify.parChk p hp
      exact ⟨h, hh, t₀.step hp hv hP (VG.Proof.MlDsa.X86_64.Verify.tChk_nil p hp), (t₀.lay hp hv).keepHint hP kh hH,
        fun _ h => absurd h (Nat.not_lt_zero _), by rw [e, h15]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (by simp)⟩
    · exact absurd (by rw [hm]; rfl) hne
  · rintro x y ⟨σ₁, σ₂, _, _, pub, ⟨_, _, hx⟩, ⟨_, _, hy⟩⟩
    rw [hx.r15, hy.r15, pub.2.2.2.2.2.2.2]
  · rintro σ s₀ s hv ⟨h, hh, hs⟩ hP e hne
    have hn := VG.Proof.MlDsa.X86_64.Verify.flag_ne (by rw [← hs.r15]; exact hne)
    exact ⟨h, ⟨hh, hn⟩, hs.flag hp hv (Nat.le_refl _) hP e, by rw [e, hs.r15]; exact VG.Proof.MlDsa.X86_64.Verify.flag_congr (iff_true_intro hn)⟩
  · rintro x y ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, _, hx⟩, ⟨h₂, _, hy⟩⟩
    obtain ⟨q₁, e₁, _, _⟩ := hx.ok
    obtain ⟨q₂, e₂, _, _⟩ := hy.ok
    exact ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, _, q₁, _, hx.toSC e₁⟩, ⟨h₂, _, q₂, _, hy.toSC e₂⟩⟩

theorem verify_ct {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    ConstantTime isa (VG.Proof.MlDsa.X86_64.Verify.verifyK p).pre (VG.Proof.MlDsa.X86_64.Verify.verifyK p).pub (verify P p) := by
  unfold verify
  exact relStart (RelCT.seq (relInv (I' := fun σ s => VG.Proof.MlDsa.X86_64.Verify.T p σ s ∧ s.gpr .r15 = VG.Proof.MlDsa.X86_64.Verify.flag True)
    (fun σ s hv hs => by subst hs; exact VG.Proof.MlDsa.X86_64.Verify.pro_ok hp hv) VG.Proof.MlDsa.X86_64.Verify.pro_tr) (RelCT.seq (VG.Proof.MlDsa.X86_64.Verify.body_tr C hp) VG.Proof.MlDsa.X86_64.Verify.epi_tr))

theorem map_toNat_inj : ∀ {l₁ l₂ : List Byte}, l₁.map (·.toNat) = l₂.map (·.toNat) → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, VG.Proof.MlDsa.X86_64.Verify.map_toNat_inj h.2]

/-- A state satisfying `verifyContract`'s precondition. -/
def verifySat (p : Params) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 0x40000 | .rsp => 0x200000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x10000, p.pkLen⟩, ⟨0x20000, 64⟩, ⟨0x30000, p.sigLen⟩]
  wr := [⟨0x40000, VG.Proof.MlDsa.X86_64.Verify.scrLen p⟩]

theorem verify_sat : ∀ p ∈ VG.Proof.MlDsa.X86_64.Verify.params, ∃ s, (verifyContract p X86_64.abi 32).pre s := by
  intro p hp
  simp only [VG.Proof.MlDsa.X86_64.Verify.params, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using VG.Proof.MlDsa.X86_64.Verify.verifySat mlDsa44
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using VG.Proof.MlDsa.X86_64.Verify.verifySat mlDsa65
  · sig_implies_sat [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] [verifySat] using VG.Proof.MlDsa.X86_64.Verify.verifySat mlDsa87

theorem verify_implies {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) : (VG.Proof.MlDsa.X86_64.Verify.verifyK p).Implies (verifyContract p X86_64.abi 32) where
  pre s h := by
    sig_pre [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := h
    exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩
  post s s' _ h := by
    sig_post [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs]
    exact h
  pub s₁ s₂ _ _ h := by
    sig_pub [verifyContract, verifySig, X86_64.abi, VG.X86_64.argRegs] at h
    obtain ⟨hsp, hb, hdi, hsi, hdx, hcx⟩ := h
    have e := VG.Proof.MlDsa.X86_64.Verify.map_toNat_inj hb
    obtain ⟨e₁, e₃⟩ := List.append_inj' e (by simp only [Proof.MlKem.bytesAt_length])
    obtain ⟨e₁, e₂⟩ := List.append_inj' e₁ (by simp only [Proof.MlKem.bytesAt_length])
    exact ⟨hdi, hsi, hdx, hcx, hsp, e₁, e₂, e₃⟩
  sat := VG.Proof.MlDsa.X86_64.Verify.verify_sat p hp

/-- `verify P p` meets `verifyContract p` with 32 bytes of stack. -/
theorem verify_verified {P : Prims} (C : VG.Proof.MlDsa.X86_64.Verify.PrimsOk P) {p : Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    Verified X86_64.target (verify P p) (verifyContract p X86_64.abi 32) :=
  Verified.of_correct (VG.Proof.MlDsa.X86_64.Verify.verify_correct C hp) (VG.Proof.MlDsa.X86_64.Verify.verify_ct C hp) (VG.Proof.MlDsa.X86_64.Verify.verify_implies hp)

end VG.Proof.MlDsa.X86_64.Verify

end

/- Proofs formerly in `VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Prims`. -/
section

/-!
# ML-DSA verification on x86-64: the primitives it calls

The x86-64 implementations of the primitives (`prims`) meet their contracts
with at most 16 bytes of stack, never write the stack pointer or load MXCSR,
and call at most two deep, with any implementation `v` of the polynomial
arithmetic (`prims_okWith`), so `verify (primsWith v.code) p` meets
`verifyContract p`.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlDsa.X86_64
open VG.Proof.MlDsa.X86_64 (FnOk ArithImpl)

/-- The x86-64 implementations of the primitives. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  sub := Arith.sub
  rejNtt := Sample.rejNTT
  ball := Sample.sampleInBall
  useHint := Round.useHint
  simpleBitPack := Pack.simpleBitPack
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack
  normLt := Round.normLt
  rej4 := Sample.Rej4.rejNTT4

/-- The primitives, with the polynomial arithmetic of `B`. -/
def primsWith (B : Arith.Backend) : Prims :=
  { VG.Proof.MlDsa.X86_64.Verify.prims with
    ntt := B.ntt
    invNtt := B.invNtt
    mul := B.mul
    mulAdd := B.mulAdd
    sub := B.sub
    normLt := B.normLt
    useHint := B.useHint
    rej4 := B.rej4
    sfx := B.sfx }

/-- A function of the polynomial arithmetic satisfies what the proofs of verification need of it. -/
theorem calleeOf {sig : Sig} {pre : Curry (sig.words X86_64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post X86_64.abi.ptrBits} {wa : Bool} {c : Prog isa}
    (h : FnOk (fun S => sig.contract X86_64.abi pre post wa S none) c) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk c (sig.contract X86_64.abi pre post wa 16 none) :=
  CalleeOk.of_verified h.ver (by decide) h.nosp (Nat.le_succ_of_le h.depth) h.ctl h.sp

theorem prims_okWith (v : ArithImpl) : VG.Proof.MlDsa.X86_64.Verify.PrimsOk (VG.Proof.MlDsa.X86_64.Verify.primsWith v.code) where
  ntt := by
    have h := v.ok.ntt
    unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract at h ⊢
    exact VG.Proof.MlDsa.X86_64.Verify.calleeOf h
  invNtt := by
    have h := v.ok.invNtt
    unfold Spec.MlDsa.nttInvContract Spec.MlDsa.inPlaceContract at h ⊢
    exact VG.Proof.MlDsa.X86_64.Verify.calleeOf h
  mul := VG.Proof.MlDsa.X86_64.Verify.calleeOf v.ok.mul
  mulAdd := VG.Proof.MlDsa.X86_64.Verify.calleeOf v.ok.mulAdd
  sub := VG.Proof.MlDsa.X86_64.Verify.calleeOf v.ok.sub
  rejNtt := (CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.rejNTT_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk prims.rejNtt _)
  ball := (CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.sampleInBall_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk prims.ball _)
  useHint := VG.Proof.MlDsa.X86_64.Verify.calleeOf v.ok.useHint
  simpleBitPack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.simpleBitPack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk prims.simpleBitPack _)
  bitUnpack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.bitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk prims.bitUnpack _)
  unpackT1 := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.unpackT1_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk prims.unpackT1 _)
  hintUnpack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.hintBitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    VG.Proof.MlDsa.X86_64.Verify.CalleeOk prims.hintUnpack _)
  normLt := VG.Proof.MlDsa.X86_64.Verify.calleeOf v.ok.normLt
  rej4 := ⟨v.ok.rej4.ver.1, v.ok.rej4.ver.2.1, v.ok.rej4.nosp, v.ok.rej4.depth, v.ok.rej4.ctl, v.ok.rej4.sp⟩

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the x86-64
primitives, with the polynomial arithmetic of `v`. -/
theorem verify_prims (v : ArithImpl) {p : Spec.MlDsa.Params} (hp : p ∈ VG.Proof.MlDsa.X86_64.Verify.params) :
    Verified X86_64.target (verify (VG.Proof.MlDsa.X86_64.Verify.primsWith v.code) p) (Spec.MlDsa.verifyContract p X86_64.abi 32) :=
  VG.Proof.MlDsa.X86_64.Verify.verify_verified (VG.Proof.MlDsa.X86_64.Verify.prims_okWith v) hp

end VG.Proof.MlDsa.X86_64.Verify

end
