module

public import VerifiedGarbage.Proof.Framework.X86.Taint
import VerifiedGarbage.Proof.X25519.X86.Lit
public import VerifiedGarbage.Impl.X25519.X86.Fn
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.X25519.X86.Lit
meta import VerifiedGarbage.Impl.X25519.X86.Fn
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
public import VerifiedGarbage.Proof.X25519.X86.Field32.Call
import VerifiedGarbage.Proof.X25519.Bytes
import VerifiedGarbage.Proof.X25519.X86.Freeze
import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.X25519.X86.Ops
public import VerifiedGarbage.Proof.X25519.Ladder
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.X25519.Contract
public import VerifiedGarbage.Proof.X25519.X86.Basic
public import VerifiedGarbage.Spec.X25519.Contract
public import VerifiedGarbage.TCB.X86.Target
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Field32.Call
meta import VerifiedGarbage.Proof.X25519.Bytes
meta import VerifiedGarbage.Proof.X25519.X86.Freeze
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.X25519.X86.Ops
meta import VerifiedGarbage.Proof.X25519.Ladder
meta import VerifiedGarbage.Proof.Framework.X86.Spill
meta import VerifiedGarbage.Proof.X25519.Contract
meta import VerifiedGarbage.Proof.X25519.X86.Basic
meta import VerifiedGarbage.Spec.X25519.Contract
meta import VerifiedGarbage.TCB.X86.Target

/-! ### `X25519.X86.Main`, which only this module used -/

section

/-! ### `X25519.X86.Contract`, which this module and modules that import it used -/

section

/-!
# X25519 on x86 (32-bit): the contract the proof is written against

The facts of the shared contract (`Proof.X25519.x25519Contract`) the proof
uses, stated for x86; the shared contract implies it (`sig_implies`, in
`Main.lean`).
-/

@[expose] public section

namespace VG.Proof.X25519

open VG VG.X86 in
/-- `vg_x25519(out, scalar, point, scratch)`, whose arguments are on the
stack (cdecl). -/
def x25519X86 : Contract X86.isa where
  pre s :=
    let out : Region := ⟨(arg s 0).setWidth 64, 32⟩
    let scalar : Region := ⟨(arg s 1).setWidth 64, 32⟩
    let point : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4096⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stk : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩
    s.rd = [scalar, point, args] ∧ s.wr = [out, scratch] ∧ out.Disjoint scratch ∧
      scalar.Disjoint scratch ∧ point.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch ∧ (arg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 1).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 4096 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧ stk.Disjoint out ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧
      8 ≤ (s.gpr .esp).toNat
  post s s' := Spec.X25519.bytesAt s'.mem ((arg s 0).setWidth 64) 32 =
    Spec.X25519.x25519 (Spec.X25519.bytesAt s.mem ((arg s 1).setWidth 64) 32)
      (Spec.X25519.bytesAt s.mem ((arg s 2).setWidth 64) 32)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧
    arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

end VG.Proof.X25519

namespace VG.Proof.X25519.X86

open VG VG.X86

section
variable (s₀ : State)
/-- The arguments and the regions, on entry. -/
abbrev outR : Region := ⟨(arg s₀ 0).setWidth 64, 32⟩
abbrev scalarR : Region := ⟨(arg s₀ 1).setWidth 64, 32⟩
abbrev pointR : Region := ⟨(arg s₀ 2).setWidth 64, 32⟩
abbrev argsR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(s₀.gpr .esp).setWidth 64, 4⟩
abbrev stkR : Region := ⟨(s₀.gpr .esp).setWidth 64 - BitVec.ofNat 64 8, 8⟩
end

/-- The precondition, by name. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [scalarR s₀, pointR s₀, argsR s₀]
  wr : s₀.wr = [outR s₀, scR 4096 (arg s₀ 3)]
  out_sc : (outR s₀).Disjoint (scR 4096 (arg s₀ 3))
  scalar_sc : (scalarR s₀).Disjoint (scR 4096 (arg s₀ 3))
  point_sc : (pointR s₀).Disjoint (scR 4096 (arg s₀ 3))
  args_out : (argsR s₀).Disjoint (outR s₀)
  args_sc : (argsR s₀).Disjoint (scR 4096 (arg s₀ 3))
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_sc : (retR s₀).Disjoint (scR 4096 (arg s₀ 3))
  out_fit : (arg s₀ 0).toNat + 32 ≤ 2 ^ 32
  scalar_fit : (arg s₀ 1).toNat + 32 ≤ 2 ^ 32
  point_fit : (arg s₀ 2).toNat + 32 ≤ 2 ^ 32
  sc_fit : (arg s₀ 3).toNat + 4096 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 20 ≤ 2 ^ 32
  stk_out : (stkR s₀).Disjoint (outR s₀)
  stk_sc : (stkR s₀).Disjoint (scR 4096 (arg s₀ 3))
  stk_args : (stkR s₀).Disjoint (argsR s₀)
  sp_room : 8 ≤ (s₀.gpr .esp).toNat

theorem Pre.of (s₀ : State) (h : Proof.X25519.x25519X86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩

/-- An argument slot's address, in the argument region. -/
theorem arg_contains {s : State} (hfit : (s.gpr .esp).toNat + 20 ≤ 2 ^ 32) {i : Nat}
    (hi : i < 4) : (⟨argAddr s 0, 16⟩ : Region).Contains (addr (s.gpr .esp) (4 + 4 * i)) 4 :=
  sub_contains (x := s.gpr .esp) (a := 4) (k := 16) (by omega_using [hfit]) (by omega_using [])
    (by omega_using [hi]) (by decide)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem argIn {i : Nat} (hi : i < 4) : InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 :=
  ⟨argsR s₀, by rw [hp.rd]; simp, arg_contains hp.sp_fit hi⟩

/-- An argument, in memory the code has written only in the working space. -/
theorem arg_same {m : Mem} (hf : Frame [scR 4096 (arg s₀ 3)] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains hp.sp_fit hi)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.args_sc) (by decide)

theorem sc_in : scR 4096 (arg s₀ 3) ∈ s₀.wr := by rw [hp.wr]; simp

theorem out_in : outR s₀ ∈ s₀.wr := by rw [hp.wr]; simp

end Pre

end VG.Proof.X25519.X86

end

end

/-! ### `X25519.X86.Step`, which only this module used -/

section

/-!
# X25519 on x86 (32-bit): the ladder

What holds from the end of the setup on (`Base`: the working space, the saved
registers, the scalar's bits, and that nothing outside the working space
changes), and the ladder: each iteration takes the ladder's state after the
bits `254, …, n + 1` in the slots `X2, Z2, X3, Z3` and the word `SWAP` (`LInv
(n + 1)`) to that after the bit `n` (`LInv n`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- The callee-saved registers and their slots in the working space, in the
order `save` stores them. -/
def savedSlots : Spill.Slots := [(.ebx, 0), (.esi, 4), (.edi, 8), (.ebp, 12)]

theorem savedSlots_bound : ∀ p ∈ savedSlots, p.2 + 4 ≤ 16 := by decide

/-- What holds from the end of the setup on: the working space at `x` (in
`edi`), the saved registers (of the state on entry `s₀`), the bits of the
scalar `k`, and memory outside the working space as on entry. -/
structure Base (x : BitVec 32) (k : Nat) (s₀ s : State) : Prop where
  ctx : Ctx 4096 x s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR 4096 x] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr x) s₀.gpr savedSlots
  bits : ∀ t < 255, s.mem (addr x (BITS + t)) = BitVec.ofNat 8 (bit k t)

/-- A byte of the working space outside a frame's region. -/
theorem byte_frame1 {m m' : Mem} {x : BitVec 32} {o n d : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 4096 ≤ 2 ^ 32) (ho : o + n ≤ 4096) (hd : d < 4096) (h : d + 1 ≤ o ∨ o + n ≤ d) :
    m' (addr x d) = m (addr x d) :=
  hf _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact sub_disj (x := x) (n := 1) (by omega_using [hx, hd]) (by omega_using [hx, ho]) h _
      (Region.contains_self _ _)

theorem Base.of_frame {x : BitVec 32} {k : Nat} {s₀ s s' : State} (h : Base x k s₀ s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {o n : Nat} (hf : Frame [sub x o n] s.mem s'.mem) (ho : o + n ≤ 4096)
    (hlo : 16 ≤ o) (hgap : o + n ≤ 32 ∨ 288 ≤ o) (hon : o < 4096) : Base x k s₀ s' := by
  have hfit := h.ctx.fit
  refine ⟨h.ctx.keep hedi hwr hesp, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_, fun t ht => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr, scR_eq]
      exact sub_sub hfit (Nat.zero_le _) (by omega_using [ho]) hon⟩)
  · have := savedSlots_bound p hp
    exact wd_frame1 hf hfit ho (by omega_using [this]) (by omega_using [this, hlo])
  · rw [byte_frame1 hf hfit ho (by simp only [BITS]; omega_using [ht]) (by simp only [BITS]; omega_using [ht, hgap])]
    exact h.bits t ht

/-- The operations keep `Base`. -/
theorem Base.ops {x : BitVec 32} {k : Nat} {s₀ s s' : State} (h : Base x k s₀ s) (hk : Keep s s')
    (hf : Frame [sub x 288 640] s.mem s'.mem) : Base x k s₀ s' :=
  h.of_frame hk.edi hk.esp hk.rd hk.wr hf (by decide) (by decide) (.inr (Nat.le_refl _)) (by decide)

/-- The ladder's state after the bits `254` down to `n`, in the slots. -/
structure LInv (x : BitVec 32) (k : Nat) (x1 : Fe) (s₀ : State) (n : Nat) (s : State) : Prop
    extends Base x k s₀ s where
  esi : s.gpr .esi = BitVec.ofNat 32 n
  vx1 : F s.mem x X1 = x1
  vx2 : F s.mem x X2 = (ladderAfter k x1 n).x2
  vz2 : F s.mem x Z2 = (ladderAfter k x1 n).z2
  vx3 : F s.mem x X3 = (ladderAfter k x1 n).x3
  vz3 : F s.mem x Z3 = (ladderAfter k x1 n).z3
  swap : wd s.mem x SWAP = BitVec.ofNat 32 (ladderAfter k x1 n).swap

theorem run_step (V : Nat → Fe) :
    let A := V X2 + V Z2
    let AA := A * A
    let B := V X2 - V Z2
    let BB := B * B
    let Ee := AA - BB
    let C := V X3 + V Z3
    let D := V X3 - V Z3
    let DA := D * A
    let CB := C * B
    run stepOps V X2 = AA * BB ∧ run stepOps V Z2 = Ee * (AA + a24 * Ee) ∧
      run stepOps V X3 = (DA + CB) * (DA + CB) ∧ run stepOps V Z3 = V X1 * ((DA - CB) * (DA - CB)) ∧
      run stepOps V X1 = V X1 := by
  simp only [run, stepOps, opOut, opVal, Function.update_apply, X1, X2, Z2, X3, Z3, A, B, C, D, AA, BB,
    Impl.X25519.X86.E, DA, CB]
  simp only [↓reduceIte, Nat.reduceEqDiff, and_self]

theorem stepOps_valid : ∀ op ∈ stepOps, opValid 288 op = true := by decide

theorem cswap_fst (sw : Nat) (a b : Fe) : (Spec.X25519.cswap sw a b).1 = if sw = 1 then b else a := by
  unfold Spec.X25519.cswap; split <;> rfl

theorem cswap_snd (sw : Nat) (a b : Fe) : (Spec.X25519.cswap sw a b).2 = if sw = 1 then a else b := by
  unfold Spec.X25519.cswap; split <;> rfl

theorem F_ite {m m' : Mem} {x : BitVec 32} {q a b : Nat} (sw : Nat)
    (h : fe m' x q = if sw = 1 then fe m x a else fe m x b) :
    F m' x q = if sw = 1 then F m x a else F m x b := by
  simp only [F, h]; split <;> rfl

theorem ofNat_xor {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) :
    BitVec.ofNat 32 a ^^^ BitVec.ofNat 32 b = BitVec.ofNat 32 (a ^^^ b) := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

theorem byte_ofNat {b : Nat} (h : b ≤ 1) : (BitVec.ofNat 8 b).setWidth 32 = BitVec.ofNat 32 b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> decide

theorem xor_le_one {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl <;> decide

theorem addr_add_ofNat (x : BitVec 32) (n d : Nat) : addr (x + BitVec.ofNat 32 n) d = addr x (d + n) := by
  simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm n d]

/-- `movzx d, BYTE PTR [b + o]` -/
theorem wp_movzx8 {is : List Instr} {s : State} {Q : State → Prop} {d b : Reg} {o : Nat} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', Wp.Upd s s' d ((s.mem a).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d ⟨b, o⟩ :: is)) s Q := by
  refine Wp.cons (s' := s.setReg d ((s.mem a).setWidth 32)) ?_ (k _ (Wp.Upd.setReg _ _ _))
  simp only [exec, State.load8, ea_mk, ha, hin, ↓reduceIte, Option.map_some]

/-- The start of an iteration: the counter decremented to `n`, `swap` updated
and the mask of the swap in `ecx`. -/
theorem stepHead_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} {n : Nat} (hn : n < 255)
    (h : LInv x k x1 s₀ (n + 1) s) :
    WP isa (.block stepHead) s fun s' => Base x k s₀ s' ∧ s'.gpr .esi = BitVec.ofNat 32 n ∧
      s'.gpr .ecx = mask ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n) ∧
      (∀ q, isSlot 288 q = true → F s'.mem x q = F s.mem x q) ∧
      wd s'.mem x SWAP = BitVec.ofNat 32 (bit k n) := by
  have hc := h.ctx
  have hfit := hc.fit
  obtain hsw := ladderAfter_swap_le k x1 (n := n + 1) (by omega_using [hn])
  obtain hb := bit_le k n
  refine Wp.wp_subi fun s₁ u₁ _ _ => Wp.wp_mov fun s₂ u₂ => Wp.wp_add fun s₃ u₃ _ => ?_
  obtain esi₁ : s₁.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₁.gpr, h.esi]; exact Wp.ofNat_pred (by omega_using [])
  obtain esi₃ : s₃.gpr .esi = BitVec.ofNat 32 n := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), esi₁]
  obtain eax₃ : s₃.gpr .eax = x + BitVec.ofNat 32 n := by
    rw [u₃.gpr, u₂.gpr, u₂.other .esi (by decide), esi₁, u₁.other _ (by decide), hc.edi]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain edi₃ : s₃.gpr .edi = x := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hc.edi]
  obtain c₃ : Ctx 4096 x s₃ := hc.keep (by rw [edi₃, hc.edi]) (by rw [u₃.wr, u₂.wr, u₁.wr])
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
  refine wp_movzx8 (a := addr x (BITS + n)) (by rw [eax₃, addr_add_ofNat])
    (c₃.inRW (by simp only [BITS]; omega_using [hn]) (by decide)) fun s₄ u₄ => ?_
  obtain eax₄ : s₄.gpr .eax = BitVec.ofNat 32 (bit k n) := by
    rw [u₄.gpr, m₃, h.bits n (by omega_using [hn]), byte_ofNat hb]
  obtain c₄ := (updKeep u₄).ctx c₃
  refine Wp.wp_ldm c₄.edi (c₄.inRW (by simp only [SWAP]; decide) (by decide)) fun s₅ u₅ => ?_
  refine Wp.wp_xor fun s₆ u₆ => ?_
  obtain edx₆ : s₆.gpr .edx = BitVec.ofNat 32 ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n) := by
    rw [u₆.gpr, u₅.gpr, u₄.mem, m₃, u₅.other .eax (by decide), eax₄]
    exact (congrArg (· ^^^ _) h.swap).trans (ofNat_xor hsw hb)
  obtain c₆ := (updKeep u₆).ctx ((updKeep u₅).ctx c₄)
  refine Wp.wp_stm c₆.edi (c₆.inW (by simp only [SWAP]; decide) (by decide)) fun s₇ u₇ => ?_
  refine Wp.wp_movi fun s₈ u₈ => Wp.wp_sub fun s₉ u₉ _ => WP.block_nil ?_
  obtain m₇ : s₉.mem = s.mem.writeW (addr x SWAP) (BitVec.ofNat 32 (bit k n)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.other .eax (by decide), u₅.other .eax (by decide), eax₄, u₆.mem,
      u₅.mem, u₄.mem, m₃]
  obtain hf : Frame [sub x SWAP 4] s.mem s₉.mem := by
    rw [m₇]; exact frame_write1 (Frame.refl _ _) hfit (by decide) (Nat.le_refl _) (Nat.le_refl _) _
  obtain g : ∀ r, r ≠ .ecx → r ≠ .eax → r ≠ .edx → r ≠ .esi → s₉.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₉.other _ h1, u₈.other _ h1, u₇.gpr, u₆.other _ h3, u₅.other _ h3, u₄.other _ h2, u₃.other _ h2,
      u₂.other _ h2, u₁.other _ h4]
  refine ⟨h.toBase.of_frame (g _ (by decide) (by decide) (by decide) (by decide))
    (g _ (by decide) (by decide) (by decide) (by decide))
    (by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) hf (by decide) (by decide)
    (.inl (by decide)) (by decide), ?_, ?_, fun q hq => ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), esi₃]
  · rw [u₉.gpr, u₈.gpr, u₈.other .edx (by decide), u₇.gpr, edx₆]; rfl
  · have hq' := slot_ge hq; have hqb := slot_below hq; simp only [Below, T] at hqb
    simp only [F]
    exact congrArg toFe (fe_frame fun j hj => wd_frame1 hf hfit (by decide) (by omega_using [hqb, hj])
      (by simp only [SWAP]; omega_using [hq']))
  · rw [m₇, wd_write_self]

/-- A frame of two slots is one of the slots and `T`. -/
theorem frame2_wide {m m' : Mem} {x : BitVec 32} {a b : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x a 32, sub x b 32] m m') (ha : isSlot 288 a = true) (hb : isSlot 288 b = true) :
    Frame [sub x 288 640] m m' := by
  obtain ha1 := slot_ge ha; have ha2 := slot_below ha; have hb1 := slot_ge hb; have hb2 := slot_below hb
  simp only [Below, T] at ha2 hb2
  exact hf.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact sub_sub hx ha1 (by omega_using [ha2]) (by omega_using [ha2])
    · exact sub_sub hx hb1 (by omega_using [hb2]) (by omega_using [hb2])⟩

/-- A slot other than the two a frame's regions are. -/
theorem F_frame2 {m m' : Mem} {x : BitVec 32} {a b q : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x a 32, sub x b 32] m m') (ha : isSlot 288 a = true) (hb : isSlot 288 b = true)
    (hq : isSlot 288 q = true) (hqa : q ≠ a) (hqb : q ≠ b) : F m' x q = F m x q := by
  obtain ha2 := slot_below ha; have hb2 := slot_below hb; have hq2 := slot_below hq
  simp only [Below, T] at ha2 hb2 hq2
  obtain sa := slot_ne ha hq hqa; have sb := slot_ne hb hq hqb
  simp only [F]
  refine congrArg toFe (fe_frame fun j hj => wd_frame hf fun r hr => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj (by omega_using [hx, hq2, hj]) (by omega_using [hx, ha2]) (by omega_using [sa, hj])
  · exact sub_disj (by omega_using [hx, hq2, hj]) (by omega_using [hx, hb2]) (by omega_using [sb, hj])

/-- One iteration of the ladder, for the bit `n`. -/
theorem step_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} {n : Nat} (hn : n < 255)
    (h : LInv x k x1 s₀ (n + 1) s) :
    WP isa (.block step) s fun s' => LInv x k x1 s₀ n s' ∧ s'.zf = some (decide (n = 0)) := by
  have hfit := h.ctx.fit
  obtain hsw := xor_le_one (ladderAfter_swap_le k x1 (n := n + 1) (by omega_using [hn])) (bit_le k n)
  simp only [step, List.append_assoc]
  refine WP.block_append (WP.mono (stepHead_ok hn h) fun s₁ ⟨b₁, esi₁, ecx₁, F₁, sw₁⟩ => ?_)
  refine WP.block_append (WP.mono (cswap_ok b₁.ctx (X := X2) (Y := X3) (by decide) (by decide) (by decide)
    hsw ecx₁) fun s₂ ⟨k₂, ecx₂, f₂, x₂, y₂⟩ => ?_)
  obtain b₂ := b₁.ops k₂ (frame2_wide hfit f₂ (by decide) (by decide))
  refine WP.block_append (WP.mono (cswap_ok b₂.ctx (X := Z2) (Y := Z3) (by decide) (by decide) (by decide)
    hsw (ecx₂.trans ecx₁)) fun s₃ ⟨k₃, _, f₃, x₃, y₃⟩ => ?_)
  obtain b₃ := b₂.ops k₃ (frame2_wide hfit f₃ (by decide) (by decide))
  refine WP.block_append (WP.mono (ops_ok stepOps b₃.ctx stepOps_valid) fun s₄ ⟨k₄, f₄, e₄⟩ => ?_)
  obtain b₄ := b₃.ops k₄ f₄
  refine Wp.wp_test fun s₅ u₅ z₅ => WP.block_nil ?_
  -- The values after the swaps.
  obtain hstep := ladderAfter_step k x1 hn
  have v₁ : ∀ q, isSlot 288 q = true → F s₁.mem x q = F s.mem x q := F₁
  obtain eX2 : F s₃.mem x X2 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).x2 (ladderAfter k x1 (n + 1)).x3).1 := by
    rw [F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide), F_ite _ x₂,
      v₁ _ (by decide), v₁ _ (by decide), h.vx2, h.vx3, cswap_fst]
  obtain eX3 : F s₃.mem x X3 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).x2 (ladderAfter k x1 (n + 1)).x3).2 := by
    rw [F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide), F_ite _ y₂,
      v₁ _ (by decide), v₁ _ (by decide), h.vx2, h.vx3, cswap_snd]
  obtain eZ2 : F s₃.mem x Z2 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).z2 (ladderAfter k x1 (n + 1)).z3).1 := by
    rw [F_ite _ x₃, F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      v₁ _ (by decide), v₁ _ (by decide), h.vz2, h.vz3, cswap_fst]
  obtain eZ3 : F s₃.mem x Z3 = (Spec.X25519.cswap ((ladderAfter k x1 (n + 1)).swap ^^^ bit k n)
      (ladderAfter k x1 (n + 1)).z2 (ladderAfter k x1 (n + 1)).z3).2 := by
    rw [F_ite _ y₃, F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide),
      v₁ _ (by decide), v₁ _ (by decide), h.vz2, h.vz3, cswap_snd]
  obtain eX1 : F s₃.mem x X1 = x1 := by
    rw [F_frame2 hfit f₃ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₂ (by decide) (by decide) (by decide) (by decide) (by decide), v₁ _ (by decide), h.vx1]
  obtain ⟨r2, rz2, r3, rz3, r1⟩ := run_step (F s₃.mem x)
  have m₅ : s₅.mem = s₄.mem := u₅.mem
  refine ⟨⟨b₄.of_frame (o := 288) (n := 640) (by rw [u₅.gpr]) (by rw [u₅.gpr]) u₅.rd u₅.wr
    (by rw [m₅]; exact Frame.refl _ _) (by decide) (by decide) (.inr (by decide)) (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.gpr, k₄.esi, k₃.esi, k₂.esi, esi₁]
  · rw [m₅, e₄ _ (by decide), r1, eX1]
  · rw [m₅, e₄ _ (by decide), r2, hstep, ladderStep_eq, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), rz2, hstep, ladderStep_eq, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), r3, hstep, ladderStep_eq, eX3, eZ3, eX2, eZ2]
  · rw [m₅, e₄ _ (by decide), rz3, hstep, ladderStep_eq, eX3, eZ3, eX2, eZ2, eX1]
  · have hs : ∀ {m m' : Mem}, Frame [sub x 288 640] m m' → wd m' x SWAP = wd m x SWAP := fun hf =>
      wd_frame1 hf hfit (by decide) (by decide) (.inl (by decide))
    rw [m₅, hs f₄, hs (frame2_wide hfit f₃ (by decide) (by decide)),
      hs (frame2_wide hfit f₂ (by decide) (by decide)), sw₁, hstep, ladderStep_eq]
  · rw [z₅, k₄.esi, k₃.esi, k₂.esi, esi₁, BitVec.and_self, Wp.ofNat_beq_zero (by omega_using [hn])]

/-- The 255 iterations. -/
theorem ladderLoop_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} (h : LInv x k x1 s₀ 255 s) :
    WP isa (.loop (.block step) .ne) s (LInv x k x1 s₀ 0) := by
  refine WP.loop (M := isa) (Q := LInv x k x1 s₀ 0) (fun m s => 1 ≤ m ∧ m ≤ 255 ∧ LInv x k x1 s₀ m s)
    (fun m s hm => ?_) 255 s ⟨by decide, Nat.le_refl _, h⟩
  obtain ⟨h1, h2, hL⟩ := hm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (step_ok (by omega_using [h2]) hL) fun s' ⟨hL', hz⟩ => ?_
  by_cases e : n = 0
  · subst e
    exact .inl ⟨by simp only [eval, hz]; rfl, hL'⟩
  · exact .inr ⟨by simp only [eval, hz, e, decide_false]; rfl, n, by omega_using [],
      by omega_using [e], by omega_using [h2], hL'⟩

end VG.Proof.X25519.X86

end

end

/-! ### `X25519.X86.Finish`, which only this module used -/

section

/-!
# X25519 on x86 (32-bit): the end of the ladder, and the result

The swap after the loop, and `finish`: `x2 · z2^(p-2)` (with `z2^(p-2)` in
`E1`), reduced fully, stored to `out`, and the saved registers restored.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

/-- The swap after the loop. -/
theorem lastSwap_ok {x : BitVec 32} {k : Nat} {x1 : Fe} {s₀ s : State} (h : LInv x k x1 s₀ 0 s) :
    WP isa (.block lastSwap) s fun s' => Base x k s₀ s' ∧
      F s'.mem x X2 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).x2
        (ladderAfter k x1 0).x3).1 ∧
      F s'.mem x Z2 = (Spec.X25519.cswap (ladderAfter k x1 0).swap (ladderAfter k x1 0).z2
        (ladderAfter k x1 0).z3).1 := by
  have hfit := h.ctx.fit
  obtain hsw := ladderAfter_swap_le k x1 (n := 0) (by decide)
  simp only [lastSwap, List.cons_append, List.nil_append]
  refine Wp.wp_ldm h.ctx.edi (h.ctx.inRW (by decide) (by decide)) fun s₁ u₁ => ?_
  refine Wp.wp_movi fun s₂ u₂ => Wp.wp_sub fun s₃ u₃ _ => ?_
  obtain k₃ : Keep s s₃ := (updKeep u₁).trans ((updKeep u₂).trans (updKeep u₃))
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain b₃ : Base x k s₀ s₃ := h.toBase.ops k₃ (by rw [m₃]; exact Frame.refl _ _)
  obtain ecx₃ : s₃.gpr .ecx = mask (ladderAfter k x1 0).swap := by
    rw [u₃.gpr, u₂.gpr, u₂.other .edx (by decide), u₁.gpr]
    show 0 - wd s.mem x SWAP = _
    rw [h.swap]; rfl
  refine WP.block_append (WP.mono (cswap_ok b₃.ctx (X := X2) (Y := X3) (by decide) (by decide) (by decide)
    hsw ecx₃) fun s₄ ⟨k₄, ecx₄, f₄, x₄, _⟩ => ?_)
  obtain b₄ := b₃.ops k₄ (frame2_wide hfit f₄ (by decide) (by decide))
  refine WP.mono (cswap_ok b₄.ctx (X := Z2) (Y := Z3) (by decide) (by decide) (by decide)
    hsw (ecx₄.trans ecx₃)) fun s₅ ⟨k₅, _, f₅, x₅, _⟩ => ⟨b₄.ops k₅ (frame2_wide hfit f₅ (by decide) (by decide)), ?_, ?_⟩
  · rw [F_frame2 hfit f₅ (by decide) (by decide) (by decide) (by decide) (by decide), F_ite _ x₄, m₃, h.vx2, h.vx3,
      cswap_fst]
  · rw [F_ite _ x₅, F_frame2 hfit f₄ (by decide) (by decide) (by decide) (by decide) (by decide),
      F_frame2 hfit f₄ (by decide) (by decide) (by decide) (by decide) (by decide), m₃, h.vz2, h.vz3, cswap_fst]

/-! ## The result -/

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- The 8 bytes of stack below `esp` the inversion's call uses. -/
theorem callStk_eq : callStk s₀ = stkR s₀ := by
  simp only [callStk, VG.X86.Taint.sub_setWidth hp.sp_room]

theorem sc_callStk : (scR 4096 (arg s₀ 3)).Disjoint (callStk s₀) := by
  rw [hp.callStk_eq]; exact hp.stk_sc.symm

/-- An argument, in memory the code has written only in the working space and
the stack below `esp`. -/
theorem arg_same' {m : Mem} (hf : Frame [scR 4096 (arg s₀ 3), callStk s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = arg s₀ i :=
  hf.readW (arg_contains hp.sp_fit hi) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.args_sc
    · rw [hp.callStk_eq]; exact hp.stk_args.symm) (by decide)

/-- The return address, apart from the stack below `esp`. -/
theorem ret_stk : (retR s₀).Disjoint (callStk s₀) := by
  rw [hp.callStk_eq]; exact VG.Offset.base_disjoint_below _ (by decide)

end Pre

theorem num_shift (f : Nat → Nat) (n : Nat) : num f (n + 1) = f 0 + 2 ^ 32 * num (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [num]
  | succ n ih =>
    rw [num_succ, ih, num_succ, Nat.mul_add, Nat.pow_succ (2 ^ 32) n, Nat.mul_comm ((2 ^ 32) ^ n) (2 ^ 32),
      Nat.mul_assoc]
    omega_using []

/-- The digits of a number of words. -/
theorem num_digit : ∀ (j : Nat) {f : Nat → Nat} {n : Nat}, (∀ k < n, f k < 2 ^ 32) → j < n →
    num f n / (2 ^ 32) ^ j % 2 ^ 32 = f j
  | 0, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [num_shift, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 hj)]
  | j + 1, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [num_shift, Nat.pow_succ (2 ^ 32) j, Nat.mul_comm ((2 ^ 32) ^ j) (2 ^ 32), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (h 0 (by omega_using [])), Nat.zero_add]
    exact num_digit j (fun k hk => h (k + 1) (by omega_using [hk])) (by omega_using [hj])

/-- The words stored to `out` so far: those of `X2`. -/
structure OInv (s₀ sF : State) (n : Nat) (s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esi : s.gpr .esi = arg s₀ 0
  esp : s.gpr .esp = sF.gpr .esp
  rd : s.rd = sF.rd
  wr : s.wr = sF.wr
  frame : Frame [outR s₀] sF.mem s.mem
  words : ∀ j < n, wd s.mem (arg s₀ 0) (4 * j) = wd sF.mem (arg s₀ 3) (X2 + 4 * j)

theorem out_contains {s₀ : State} (hp : Pre s₀) {j : Nat} (hj : j < 8) :
    (outR s₀).Contains (addr (arg s₀ 0) (4 * j)) 4 := by
  have := sub_contains (x := arg s₀ 0) (a := 0) (k := 32) (d := 4 * j) (n := 4)
    (by have := hp.out_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hj]) (by decide)
  rwa [sub, addr_zero] at this

theorem outWord_ok {s₀ sF s : State} (hp : Pre s₀) (hsF : sF.wr = s₀.wr) {n : Nat} (hn : n < 8)
    (h : OInv s₀ sF n s) :
    WP isa (.block [.mov .eax (.mem (sc (X2 + 4 * n))), .store (at_ .esi (4 * n)) .eax]) s (OInv s₀ sF (n + 1)) := by
  have hfit := hp.sc_fit
  refine Wp.wp_ldm h.edi ⟨_, by rw [h.wr, hsF]; exact List.mem_append_right _ hp.sc_in,
    scR_contains hfit (by simp only [X2]; omega_using [hn]) (by decide)⟩ fun s₁ u₁ => ?_
  refine Wp.wp_stm (by rw [u₁.other _ (by decide), h.esi]) ⟨_, by rw [u₁.wr, h.wr, hsF]; exact hp.out_in,
    out_contains hp hn⟩ fun s₂ u₂ => WP.block_nil ?_
  obtain hsame : wd s.mem (arg s₀ 3) (X2 + 4 * n) = wd sF.mem (arg s₀ 3) (X2 + 4 * n) :=
    wd_frame h.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine Region.Disjoint.symm (hp.out_sc.sub_right ?_)
      rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by simp only [X2]; omega_using [hn])
        (by simp only [X2]; omega_using [hn])
  refine ⟨by rw [u₂.gpr, u₁.other _ (by decide), h.edi], by rw [u₂.gpr, u₁.other _ (by decide), h.esi],
    by rw [u₂.gpr, u₁.other _ (by decide), h.esp], by rw [u₂.rd, u₁.rd, h.rd], by rw [u₂.wr, u₁.wr, h.wr], ?_,
    fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]; exact h.frame.writeW (List.mem_singleton_self _) _ (out_contains hp hn)
  · rw [u₂.mem, u₁.mem, u₁.gpr]
    have hof := hp.out_fit
    by_cases e : j = n
    · subst e; rw [wd_write_self]; exact hsame
    · rw [wd_write_ne _ _ (by omega_using [hof, hj, hn]) (by omega_using [hof, hn]) (by omega_using [hj, e])]
      exact h.words j (by omega_using [hj, e])

theorem outWords_ok {s₀ sF : State} (hp : Pre s₀) (hsF : sF.wr = s₀.wr) : ∀ n ≤ 8, ∀ s, OInv s₀ sF 0 s →
    WP isa (.block ((List.range n).flatMap fun k => [.mov .eax (.mem (sc (X2 + 4 * k))),
      .store (at_ .esi (4 * k)) .eax])) s (OInv s₀ sF n)
  | 0, _, _, h => WP.block_nil h
  | n + 1, hn, s, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (outWords_ok hp hsF n (by omega_using [hn]) s h) fun s₁ h₁ =>
      outWord_ok hp hsF (by omega_using [hn]) h₁)

theorem restore_eq : restore =
    .mov .eax (.reg .edi) :: (Spill.restoreCode .eax [(.ebx, 0), (.esi, 4), (.ebp, 12), (.edi, 8)] ++ []) := rfl

/-- The saved registers restored. -/
theorem restore_ok {x : BitVec 32} {s s₀ : State} (hc : Ctx 4096 x s) (hs : Spill.Saved s.mem (addr x) s₀.gpr savedSlots) :
    WP isa (.block restore) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .esp = s.gpr .esp ∧ ∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = s₀.gpr r := by
  rw [restore_eq]
  refine Wp.wp_mov fun s₁ u₁ => ?_
  obtain ea : s₁.gpr .eax = x := by rw [u₁.gpr, hc.edi]
  refine Spill.restore_ok _ (by decide)
    (fun p h => by
      rw [ea, u₁.rd, u₁.wr]; exact hc.inRW (by have := savedSlots_bound p (by revert p h; decide); omega_using [this])
        (by decide))
    (by rw [ea, u₁.mem]; exact hs.sub (by decide)) fun s' r' => WP.block_nil ⟨by rw [r'.mem, u₁.mem],
      by rw [r'.other _ (by decide), u₁.other _ (by decide)],
      fun r hr hsp => r'.regs r (by revert hsp; revert hr; revert r; decide)⟩

end VG.Proof.X25519.X86

end

end

/-! ### `X25519.X86.Invert`, which only this module used -/

section

/-!
# X25519 on x86 (32-bit): the inversion

`z2` copied to byte 128, the addition chain (`Field32.pow250Call`, through
`pow250Call_ok'`), then five squarings and a product (`Field32`'s `sqnC` and
`mulC`) leave `invert z2` in `E1` (`invert_ok`). The copy overwrites the
scalar's bits and the call the 8 bytes of stack below `esp`: from then on,
what holds is `After`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519
open VG.Proof.X25519 (pw pw_mul sqn_pw pow_pw)
open VG.Proof.X25519.X86.Field32 (Cs CSpec cenv opMul opSqn sqnC mulC pow250Call_ok')

/-- What holds after the inversion: `Base` without the scalar's bits, with
the 8 bytes of stack below `esp` on entry (`callStk s₀`) changed too. -/
structure After (x : BitVec 32) (s₀ s : State) : Prop where
  ctx : Ctx 4096 x s
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR 4096 x, callStk s₀] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr x) s₀.gpr savedSlots

theorem Base.after {x : BitVec 32} {k : Nat} {s₀ s : State} (h : Base x k s₀ s) : After x s₀ s :=
  ⟨h.ctx, h.esp, h.rd, h.wr, h.frame.mono fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_self .., h.saved⟩

/-- A change of the working space past the saved registers keeps `After`. -/
theorem After.of_frame {x : BitVec 32} {s₀ s s' : State} (h : After x s₀ s)
    (hedi : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {o n : Nat} (hf : Frame [sub x o n] s.mem s'.mem) (ho : o + n ≤ 4096)
    (hlo : 16 ≤ o) (hon : o < 4096) : After x s₀ s' := by
  have hfit := h.ctx.fit
  refine ⟨h.ctx.keep hedi hwr hesp, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_cons_self .., by
      rw [List.mem_singleton.mp hr, scR_eq]
      exact sub_sub hfit (Nat.zero_le _) (by omega_using [ho]) hon⟩)
  · have := savedSlots_bound p hp
    exact wd_frame1 hf hfit ho (by omega_using [this]) (.inl (by omega_using [this, hlo]))

/-- The operations keep `After`. -/
theorem After.ops {x : BitVec 32} {s₀ s s' : State} (h : After x s₀ s) (hk : Keep s s')
    (hf : Frame [sub x 288 640] s.mem s'.mem) : After x s₀ s' :=
  h.of_frame hk.edi hk.esp hk.rd hk.wr hf (by decide) (by decide) (by decide)

/-- The chain's tail for the inversion: five squarings, and `z^11`. -/
theorem invert_tail (z : Fe) :
    VG.Proof.X25519.sqn (pw z (2 ^ 250 - 1)) 5 * pw z 11 = VG.Proof.X25519.invert z := by
  rw [VG.Proof.X25519.invert_eq, pow_pw, sqn_pw, pw_mul]
  exact congrArg (pw z) (by decide)

theorem tail_spec (x : BitVec 32) :
    CSpec x (.seq (Field32.sqn Field32.E1 Field32.E1 5) (.block (mul Field32.E1 Field32.E1 Field32.E0)))
      (fun e => opMul 1 1 0 (opSqn 1 1 5 e)) :=
  (sqnC x 1 1 5 (by decide) (by decide)).seq (mulC x 1 1 0)

/-- The inversion, from `Base` with the stack below `esp` apart from the working space. -/
theorem invert_ok {x : BitVec 32} {k : Nat} {s₀ s : State} (h : Base x k s₀ s)
    (hE : 8 ≤ (s₀.gpr .esp).toNat) (hd : (scR 4096 x).Disjoint (callStk s₀)) :
    WP isa Impl.X25519.X86.invert s fun s' => After x s₀ s' ∧
      F s'.mem x Field32.E1 = VG.Proof.X25519.invert (F s.mem x Z2) ∧ F s'.mem x X2 = F s.mem x X2 := by
  have hfit := h.ctx.fit
  -- `z2` to byte 128.
  refine WP.seq (WP.mono (copy_ok h.ctx (o := Impl.X25519.X86.Field32.aAt) (a := Z2) (by decide) (by decide)
    (by decide)) fun s₁ ⟨k₁, f₁, e₁⟩ => ?_)
  obtain a₁ := h.after.of_frame k₁.edi k₁.esp k₁.rd k₁.wr f₁ (by decide) (by decide) (by decide)
  obtain z₁ : F s₁.mem x Impl.X25519.X86.Field32.aAt = F s.mem x Z2 := congrArg toFe e₁
  obtain x₁ : F s₁.mem x X2 = F s.mem x X2 := congrArg toFe (fe_frame1 f₁ hfit (by decide) (by decide) (by decide))
  -- The call.
  obtain cs₁ : callStk s₁ = callStk s₀ := by rw [callStk, callStk, a₁.esp]
  refine WP.seq (WP.mono (pow250Call_ok' a₁.ctx (by rw [a₁.esp]; exact hE) (cs₁ ▸ hd))
    fun s₂ ⟨k₂, f₂, p₁, p₀⟩ => ?_)
  rw [cs₁] at f₂
  obtain w₂ : ∀ d, d + 4 ≤ 512 → wd s₂.mem x d = wd s₁.mem x d := fun d hd' =>
    wd_frame f₂ fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact sub_disj (by omega_using [hfit, hd']) (by omega_using [hfit]) (.inl hd')
      · exact hd.sub_left (by
          rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hd']) (by omega_using [hd']))
  obtain a₂ : After x s₀ s₂ := by
    refine ⟨k₂.ctx a₁.ctx, k₂.esp.trans a₁.esp, k₂.rd.trans a₁.rd, k₂.wr.trans a₁.wr,
      a₁.frame.trans (f₂.sub fun r hr => ?_), a₁.saved.of_readW fun p hp => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self .., by
          rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by decide) (by decide)⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
    · have := savedSlots_bound p hp
      exact w₂ _ (by omega_using [this])
  obtain x₂ : F s₂.mem x X2 = F s₁.mem x X2 :=
    congrArg toFe (fe_frame fun j hj => w₂ _ (by simp only [X2]; omega_using [hj]))
  -- Five squarings and `z^11`.
  refine WP.mono (tail_spec x s₂ a₂.ctx) fun s₃ ⟨k₃, e₃⟩ => ?_
  refine ⟨a₂.of_frame k₃.edi k₃.esp k₃.rd k₃.wr k₃.frame (by decide) (by decide) (by decide), ?_, ?_⟩
  · change cenv s₃.mem x 1 = _
    rw [e₃]
    simp only [opMul, opSqn, Function.update_self, Function.update_of_ne (show (0 : Cs) ≠ 1 by decide)]
    change VG.Proof.X25519.sqn (F s₂.mem x Field32.E1) 5 * F s₂.mem x Field32.E0 = _
    rw [p₁, p₀, z₁, invert_tail]
  · rw [← x₁, ← x₂]
    exact congrArg toFe (fe_frame1 k₃.frame hfit (by decide) (by decide) (by decide))

end VG.Proof.X25519.X86

end

end

/-! ### `X25519.X86.Setup`, which only this module used -/

section

/-!
# X25519 on x86 (32-bit): reading the arguments

`save` stores the callee-saved registers in the working space, `loadPoint` the
u-coordinate (its top bit masked) in `X1`, `loadScalar` the bits of the scalar
in `BITS` (clamped), and `initLadder` the ladder's initial state; so the
ladder starts with `LInv 255`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem save_eq : save = .mov .eax (.mem (at_ .esp 16)) :: (Spill.saveCode .eax savedSlots ++
    ([.mov .edi (.reg .eax)] : List Instr)) := rfl

/-- What `save` leaves. -/
structure Saved (s₀ s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [scR 4096 (arg s₀ 3)] s₀.mem s.mem
  saved : Spill.Saved s.mem (addr (arg s₀ 3)) s₀.gpr savedSlots

theorem save_ok {s₀ : State} (hp : Pre s₀) : WP isa (.block save) s₀ (Saved s₀) := by
  have hfit := hp.sc_fit
  rw [save_eq]
  refine Wp.wp_ldm (B := s₀.gpr .esp) (o := 16) rfl (hp.argIn (i := 3) (by decide)) fun s₁ u₁ => ?_
  have ea : s₁.gpr .eax = arg s₀ 3 := u₁.gpr
  obtain inW : ∀ {s : State} {d : Nat}, s.wr = s₀.wr → d + 4 ≤ 4096 → InRegions s.wr (addr (arg s₀ 3) d) 4 :=
    fun hw hd => ⟨_, hw ▸ hp.sc_in, scR_contains hfit hd (by decide)⟩
  refine Spill.save_ok savedSlots (fun p h => by
    rw [ea]; exact inW u₁.wr (by have := savedSlots_bound p h; omega_using [this])) fun s₅ u₅ => ?_
  refine Wp.wp_mov fun s₆ u₆ => WP.block_nil ?_
  obtain hr : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r := fun r h => u₁.other r h
  obtain hm : s₆.mem = Spill.saveMem s₀.mem (addr (arg s₀ 3)) s₀.gpr savedSlots := by
    rw [u₆.mem, u₅.mem, ea, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => hr _ (by revert p h; decide)
  refine ⟨by rw [u₆.gpr, u₅.gpr, ea], by rw [u₆.other _ (by decide), u₅.gpr, hr _ (by decide)],
    by rw [u₆.rd, u₅.rd, u₁.rd], by rw [u₆.wr, u₅.wr, u₁.wr], ?_, ?_⟩
  · rw [hm]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p h =>
      scR_contains hfit (by have := savedSlots_bound p h; omega_using [this]) (by decide)
  · rw [hm]; exact Spill.saveMem_saved_addr _ _ (n := 16) (by decide) (by omega_using [hfit])

/-- A store to the working space above the saved registers keeps `Saved`. -/
theorem Saved.write {s₀ s s' : State} (hp : Pre s₀) (h : Saved s₀ s) {d : Nat} (hd : 16 ≤ d)
    (hd' : d + 4 ≤ 4096) (hg : s'.gpr .edi = s.gpr .edi) (hesp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) {v : BitVec 32} (hm : s'.mem = s.mem.writeW (addr (arg s₀ 3) d) v) : Saved s₀ s' := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · rw [hm]; exact h.frame.writeW (List.mem_singleton_self _) _ (scR_contains hfit hd' (by decide))
  · have := savedSlots_bound p hp
    rw [hm]
    exact wd_write_ne _ _ (by omega_using [hfit, this]) (by omega_using [hfit, hd']) (.inl (by omega_using [this, hd]))

/-- The words of the u-coordinate, on entry. -/
abbrev pw (s₀ : State) (k : Nat) : BitVec 32 := wd s₀.mem (arg s₀ 2) (4 * k)

/-- The words `X1` receives: those of the u-coordinate, the top bit masked. -/
def pv (s₀ : State) (k : Nat) : BitVec 32 := if k = 7 then pw s₀ 7 &&& low31 else pw s₀ k

/-- A word of the u-coordinate, unchanged. -/
theorem point_contains {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < 8) :
    (pointR s₀).Contains (addr (arg s₀ 2) (4 * k)) 4 := by
  have := sub_contains (x := arg s₀ 2) (a := 0) (k := 32) (d := 4 * k) (n := 4)
    (by have := hp.point_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hk]) (by decide)
  rwa [sub, addr_zero] at this

/-- A word of the u-coordinate, unchanged. -/
theorem Saved.pw {s₀ s : State} (hp : Pre s₀) (h : Saved s₀ s) {k : Nat} (hk : k < 8) :
    wd s.mem (arg s₀ 2) (4 * k) = pw s₀ k :=
  h.frame.readW (point_contains hp hk)
    (by simp only [List.mem_singleton]; rintro r rfl; exact hp.point_sc) (by decide)

theorem loadWord_ok {s₀ s : State} (hp : Pre s₀) {n : Nat} (hn : n < 8)
    (h : Saved s₀ s) (hesi : s.gpr .esi = arg s₀ 2) (hw : ∀ j < n, wd s.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j) :
    WP isa (.block (([.mov .eax (.mem (at_ .esi (4 * n)))] : List Instr) ++
      (if n = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * n)) .eax] : List Instr))) s fun s' =>
      Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
  have hfit := hp.sc_fit
  obtain hin : InRegions (s.rd ++ s.wr) (addr (arg s₀ 2) (4 * n)) 4 :=
    ⟨pointR s₀, by rw [h.rd, hp.rd]; simp, point_contains hp hn⟩
  simp only [List.cons_append, List.nil_append]
  refine Wp.wp_ldm hesi hin fun s₁ u₁ => ?_
  -- The rest, from the value `w` in `eax`.
  obtain fin : ∀ (s₂ : State) (w : BitVec 32), s₂.gpr .eax = w → w = pv s₀ n → s₂.gpr .edi = s.gpr .edi →
      s₂.gpr .esp = s.gpr .esp → s₂.gpr .esi = s.gpr .esi → s₂.rd = s.rd → s₂.wr = s.wr → s₂.mem = s.mem →
      WP isa (.block [.store (sc (X1 + 4 * n)) .eax]) s₂ fun s' =>
        Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n + 1, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
    intro s₂ w ew hw' g1 g2 g3 g4 g5 g6
    refine Wp.wp_stm (by rw [g1]; exact h.edi) ⟨_, by rw [g5, h.wr]; exact hp.sc_in,
      scR_contains hfit (by simp only [X1]; omega_using [hn]) (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    refine ⟨h.write hp (d := X1 + 4 * n) (by simp only [X1]; omega_using []) (by simp only [X1]; omega_using [hn])
      (by rw [u₃.gpr, g1]) (by rw [u₃.gpr, g2]) (by rw [u₃.rd, g4]) (by rw [u₃.wr, g5]) (by rw [u₃.mem, g6]),
      by rw [u₃.gpr, g3, hesi], fun j hj => ?_⟩
    rw [u₃.mem, g6]
    by_cases e : j = n
    · subst e; rw [wd_write_self, ew, hw']
    · rw [wd_write_ne _ _ (by simp only [X1]; omega_using [hfit, hj, hn]) (by simp only [X1]; omega_using [hfit, hn])
        (by omega_using [e])]
      exact hw j (by omega_using [hj, e])
  obtain e₁ : s₁.gpr .eax = pw s₀ n := by rw [u₁.gpr]; exact h.pw hp hn
  by_cases h7 : n = 7
  · subst h7
    simp only [ite_true, List.cons_append, List.nil_append]
    refine Wp.wp_andi fun s₂ u₂ => fin s₂ _ u₂.gpr ?_ (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)])
      (by rw [u₂.other _ (by decide), u₁.other _ (by decide)]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr])
      (by rw [u₂.mem, u₁.mem])
    rw [e₁]; rfl
  · simp only [h7, ite_false, List.nil_append]
    exact fin s₁ _ rfl (by rw [e₁, pv, ite_eq_right h7]) (u₁.other _ (by decide)) (u₁.other _ (by decide))
      (u₁.other _ (by decide)) u₁.rd u₁.wr u₁.mem

theorem loadWords_ok {s₀ : State} (hp : Pre s₀) : ∀ n ≤ 8, ∀ s, Saved s₀ s → s.gpr .esi = arg s₀ 2 →
    WP isa (.block ((List.range n).flatMap fun k => ([.mov .eax (.mem (at_ .esi (4 * k)))] : List Instr) ++
      (if k = 7 then ([.alu .and .eax (.imm low31)] : List Instr) else []) ++
      ([.store (sc (X1 + 4 * k)) .eax] : List Instr))) s fun s' =>
      Saved s₀ s' ∧ s'.gpr .esi = arg s₀ 2 ∧ ∀ j < n, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j
  | 0, _, _, h, he => WP.block_nil ⟨h, he, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  | n + 1, hn, s, h, he => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (loadWords_ok hp n (by omega_using [hn]) s h he) fun s₁ ⟨h₁, e₁, w₁⟩ =>
      loadWord_ok hp (by omega_using [hn]) h₁ e₁ w₁)

theorem loadPoint_ok {s₀ s : State} (hp : Pre s₀) (h : Saved s₀ s) :
    WP isa (.block loadPoint) s fun s' => Saved s₀ s' ∧ ∀ j < 8, wd s'.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j := by
  refine Wp.wp_ldm (B := s.gpr .esp) (o := 12) rfl (by rw [h.esp, h.rd, h.wr]; exact hp.argIn (i := 2) (by decide))
    fun s₁ u₁ => ?_
  obtain h₁ : Saved s₀ s₁ := ⟨by rw [u₁.other _ (by decide)]; exact h.edi, by rw [u₁.other _ (by decide)]; exact h.esp,
    by rw [u₁.rd]; exact h.rd, by rw [u₁.wr]; exact h.wr, by rw [u₁.mem]; exact h.frame,
    by rw [u₁.mem]; exact h.saved⟩
  obtain e₁ : s₁.gpr .esi = arg s₀ 2 := by
    rw [u₁.gpr, h.esp]; exact hp.arg_same h.frame (i := 2) (by decide)
  exact WP.mono (loadWords_ok hp 8 (Nat.le_refl _) s₁ h₁ e₁) fun s' ⟨h', _, w'⟩ => ⟨h', w'⟩

/-! ## The scalar's bits -/

theorem wp_store8 {is : List Instr} {s : State} {Q : State → Prop} {b : Reg} {o : Nat} {r : Reg8} {a : Addr}
    (ha : addr (s.gpr b) o = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', Wp.Mupd s s' (s.mem.writeW a ((s.gpr r.reg).setWidth 8)) → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 ⟨b, o⟩ r :: is)) s Q := by
  refine Wp.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r.reg).setWidth 8) }) ?_
    (k _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  simp only [exec, State.store8, ea_mk, ha, hout, ↓reduceIte]

theorem byte_write_self (m : Mem) (a : Addr) (v : BitVec 8) : (m.writeW a v) a = v := by
  simp only [Mem.writeW, Mem.write, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero]
  apply BitVec.eq_of_toNat_eq
  simp

theorem byte_write_ne (m : Mem) {x : BitVec 32} (v : BitVec 8) {d e : Nat} (hd : x.toNat + d + 1 ≤ 2 ^ 32)
    (he : x.toNat + e + 1 ≤ 2 ^ 32) (h : d ≠ e) : (m.writeW (addr x e) v) (addr x d) = m (addr x d) := by
  obtain hdisj := sub_disj (x := x) (n := 1) (k := 1) hd he (by omega_using [h])
  exact Mem.write_apply fun h' => hdisj _ (Region.contains_self _ _) (by
    simp only [Region.Contains]; omega_using [h'])

theorem Saved.of_frame {s₀ sA s : State} (hp : Pre s₀) (h : Saved s₀ sA) {o n : Nat}
    (hf : Frame [sub (arg s₀ 3) o n] sA.mem s.mem) (ho : 16 ≤ o) (hon : o + n ≤ 4096) (hn : o < 4096)
    (hg : s.gpr .edi = sA.gpr .edi) (hesp : s.gpr .esp = sA.gpr .esp) (hrd : s.rd = sA.rd) (hwr : s.wr = sA.wr) :
    Saved s₀ s := by
  have hfit := hp.sc_fit
  refine ⟨hg.trans h.edi, hesp.trans h.esp, hrd.trans h.rd, hwr.trans h.wr, ?_,
    h.saved.of_readW fun p hp => ?_⟩
  · exact h.frame.trans (hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, by
      rw [List.mem_singleton.mp hr, scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [hon]) hn⟩)
  · have := savedSlots_bound p hp
    exact wd_frame1 hf hfit hon (by omega_using [this]) (.inl (by omega_using [this, ho]))

/-- Byte `i` of the scalar, on entry. -/
abbrev sb (s₀ : State) (i : Nat) : Nat := (s₀.mem (addr (arg s₀ 1) i)).toNat

/-- The bits stored so far. -/
structure BInv (s₀ sA : State) (t : Nat) (s : State) : Prop where
  edi : s.gpr .edi = arg s₀ 3
  esp : s.gpr .esp = sA.gpr .esp
  rd : s.rd = sA.rd
  wr : s.wr = sA.wr
  frame : Frame [sub (arg s₀ 3) BITS 256] sA.mem s.mem
  bits : ∀ u < t, s.mem (addr (arg s₀ 3) (BITS + u)) = BitVec.ofNat 8 ((sb s₀ (u / 8) >>> (u % 8)) &&& 1)

/-- `BInv` through instructions that keep `edi`, `esp` and memory. -/
theorem BInv.upd {s₀ sA s s' : State} {t : Nat} (h : BInv s₀ sA t s) (he : s'.gpr .edi = s.gpr .edi)
    (hs : s'.gpr .esp = s.gpr .esp) (hr : s'.rd = s.rd) (hw : s'.wr = s.wr) (hm : s'.mem = s.mem) :
    BInv s₀ sA t s' :=
  ⟨he.trans h.edi, hs.trans h.esp, hr.trans h.rd, hw.trans h.wr, by rw [hm]; exact h.frame,
    by rw [hm]; exact h.bits⟩

theorem bit_toNat {b : Nat} (hb : b < 256) (j : Nat) :
    ((BitVec.ofNat 32 b >>> j) &&& 1).toNat = (b >>> j) &&& 1 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb])]
  rfl

theorem setWidth8_bit (w : BitVec 32) {b : Nat} (h : w.toNat = b) :
    w.setWidth 8 = BitVec.ofNat 8 b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, h, BitVec.toNat_ofNat]

theorem bitOf_ok {s₀ sA s : State} (hp : Pre s₀) (hsA : sA.wr = s₀.wr) {i j : Nat} (hi : i < 32) (hj : j < 8)
    (h : BInv s₀ sA (8 * i + j) s) (heax : s.gpr .eax = BitVec.ofNat 32 (sb s₀ i))
    (hebx : s.gpr .ebx = arg s₀ 3 + BitVec.ofNat 32 (BITS + 8 * i)) :
    WP isa (.block (bitOf j)) s fun s' => BInv s₀ sA (8 * i + j + 1) s' ∧ ∀ r, r ≠ .edx → s'.gpr r = s.gpr r := by
  have hfit := hp.sc_fit
  obtain hbl : sb s₀ i < 256 := BitVec.isLt _
  -- The last two instructions, from `edx = eax >>> j`.
  obtain fin : ∀ s₁, s₁.gpr .edx = s.gpr .eax >>> j → (∀ r, r ≠ .edx → s₁.gpr r = s.gpr r) → s₁.rd = s.rd →
      s₁.wr = s.wr → s₁.mem = s.mem →
      WP isa (.block [.alu .and .edx (.imm 1), .store8 (at_ .ebx j) .dl]) s₁ fun s' =>
        BInv s₀ sA (8 * i + j + 1) s' ∧ ∀ r, r ≠ .edx → s'.gpr r = s.gpr r := by
    intro s₁ e1 g g4 g5 g6
    refine Wp.wp_andi fun s₂ u₂ => ?_
    refine wp_store8 (a := addr (arg s₀ 3) (BITS + 8 * i + j))
      (by rw [u₂.other _ (by decide), g _ (by decide), hebx]; simp only [addr, BitVec.add_assoc, BitVec.ofNat_add_ofNat])
      ⟨_, by rw [u₂.wr, g5, h.wr, hsA]; exact hp.sc_in, scR_contains hfit (by simp only [BITS]; omega_using [hi, hj])
        (by decide)⟩ fun s₃ u₃ => WP.block_nil ?_
    obtain ev : ((s₂.gpr (Reg8.dl).reg).setWidth 8) = BitVec.ofNat 8 ((sb s₀ i >>> j) &&& 1) := by
      refine setWidth8_bit _ ?_
      show (s₂.gpr .edx).toNat = _
      rw [u₂.gpr, e1, heax, bit_toNat hbl]
    obtain m₃ : s₃.mem = s.mem.writeW (addr (arg s₀ 3) (BITS + 8 * i + j)) (BitVec.ofNat 8 ((sb s₀ i >>> j) &&& 1)) := by
      rw [u₃.mem, ev, u₂.mem, g6]
    refine ⟨⟨by rw [u₃.gpr, u₂.other _ (by decide), g _ (by decide), h.edi],
      by rw [u₃.gpr, u₂.other _ (by decide), g _ (by decide), h.esp], by rw [u₃.rd, u₂.rd, g4, h.rd],
      by rw [u₃.wr, u₂.wr, g5, h.wr], ?_, fun u hu => ?_⟩, fun r hr => by rw [u₃.gpr, u₂.other _ hr, g r hr]⟩
    · rw [m₃]
      exact h.frame.writeW (List.mem_singleton_self _) _
        (sub_contains (by simp only [BITS]; omega_using [hfit]) (by simp only [BITS]; omega_using [])
          (by simp only [BITS]; omega_using [hi, hj])
          (by decide))
    · rw [m₃]
      by_cases e : u = 8 * i + j
      · subst e
        rw [show BITS + (8 * i + j) = BITS + 8 * i + j by omega_using [], byte_write_self,
          show (8 * i + j) / 8 = i by omega_using [hj], show (8 * i + j) % 8 = j by omega_using [hj]]
      · rw [byte_write_ne _ _ (by simp only [BITS]; omega_using [hfit, hu, hi, hj])
          (by simp only [BITS]; omega_using [hfit, hi, hj]) (by omega_using [e])]
        exact h.bits u (by omega_using [hu, e])
  simp only [bitOf]
  by_cases h0 : j = 0
  · subst h0
    simp only [ite_true, List.nil_append, List.cons_append]
    refine Wp.wp_mov fun s₁ u₁ => fin s₁ (by rw [u₁.gpr]; exact (BitVec.ushiftRight_zero _).symm)
      (fun r hr => u₁.other _ hr) u₁.rd u₁.wr u₁.mem
  · simp only [h0, ite_false, List.cons_append, List.nil_append]
    refine Wp.wp_mov fun s₁ u₁ => Wp.wp_shr ⟨by omega_using [h0], by omega_using [hj]⟩ fun s₂ u₂ _ =>
      fin s₂ (by rw [u₂.gpr, u₁.gpr]) (fun r hr => by rw [u₂.other _ hr, u₁.other _ hr]) (by rw [u₂.rd, u₁.rd])
      (by rw [u₂.wr, u₁.wr]) (by rw [u₂.mem, u₁.mem])

theorem bitsOf_ok {s₀ sA : State} (hp : Pre s₀) (hsA : sA.wr = s₀.wr) {i : Nat} (hi : i < 32) :
    ∀ n ≤ 8, ∀ s, BInv s₀ sA (8 * i) s → s.gpr .eax = BitVec.ofNat 32 (sb s₀ i) →
    s.gpr .ebx = arg s₀ 3 + BitVec.ofNat 32 (BITS + 8 * i) →
    WP isa (.block ((List.range n).flatMap bitOf)) s fun s' =>
      BInv s₀ sA (8 * i + n) s' ∧ ∀ r, r ≠ .edx → s'.gpr r = s.gpr r
  | 0, _, _, h, _, _ => WP.block_nil ⟨h, fun _ _ => rfl⟩
  | n + 1, hn, s, h, he, hb => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append (WP.mono (bitsOf_ok hp hsA hi n (by omega_using [hn]) s h he hb) fun s₁ ⟨h₁, e₁⟩ => ?_)
    exact WP.mono (bitOf_ok hp hsA hi (by omega_using [hn]) h₁ (by rw [e₁ _ (by decide), he])
      (by rw [e₁ _ (by decide), hb])) fun s₂ ⟨h₂, e₂⟩ => ⟨h₂, fun r hr => (e₂ r hr).trans (e₁ r hr)⟩

theorem scalar_contains {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    (scalarR s₀).Contains (addr (arg s₀ 1) i) 1 := by
  have := sub_contains (x := arg s₀ 1) (a := 0) (k := 32) (d := i) (n := 1)
    (by have := hp.scalar_fit; omega_using [this]) (Nat.zero_le _) (by omega_using [hi]) (by decide)
  rwa [sub, addr_zero] at this

/-- The loop over the scalar's bytes: `i` of them done. -/
def LInvS (s₀ sA : State) (i : Nat) (s : State) : Prop :=
  BInv s₀ sA (8 * i) s ∧ s.gpr .esi = arg s₀ 1 + BitVec.ofNat 32 i ∧
    s.gpr .ebx = arg s₀ 3 + BitVec.ofNat 32 (BITS + 8 * i) ∧ s.gpr .ecx = BitVec.ofNat 32 (32 - i)

theorem scalarBitsByte_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) {i : Nat} (hi : i < 32) {s : State}
    (h : LInvS s₀ sA i s) :
    WP isa (.block scalarBitsByte) s fun t => LInvS s₀ sA (i + 1) t ∧ t.zf = some (decide (32 - (i + 1) = 0)) := by
  obtain ⟨h₁, si, bi, ci⟩ := h
  have hfit := hp.sc_fit
  -- The byte of the scalar, unchanged.
  obtain hsame : s.mem (addr (arg s₀ 1) i) = s₀.mem (addr (arg s₀ 1) i) := by
    obtain f : Frame [scR 4096 (arg s₀ 3)] s₀.mem s.mem := hA.frame.trans (h₁.frame.sub fun _ hr =>
      ⟨_, List.mem_singleton_self _, by
        rw [List.mem_singleton.mp hr, scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by simp only [BITS]; decide)
          (by simp only [BITS]; decide)⟩)
    exact f _ fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.scalar_sc _ (scalar_contains hp hi)
  unfold scalarBitsByte
  refine wp_movzx8 (a := addr (arg s₀ 1) i) (by rw [si]; simp only [addr, BitVec.add_zero])
    ⟨scalarR s₀, by rw [h₁.rd, hA.rd, hp.rd]; simp, scalar_contains hp hi⟩ fun s₂ u₂ => ?_
  obtain h₂ : BInv s₀ sA (8 * i) s₂ := h₁.upd (u₂.other _ (by decide)) (u₂.other _ (by decide)) u₂.rd u₂.wr u₂.mem
  obtain e₂ : s₂.gpr .eax = BitVec.ofNat 32 (sb s₀ i) := by
    rw [u₂.gpr, hsame]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  refine WP.block_append (WP.mono (bitsOf_ok hp (by rw [hA.wr]) hi 8 (Nat.le_refl _) s₂ h₂ e₂
    (by rw [u₂.other _ (by decide), bi])) fun s₃ ⟨h₃, g₃⟩ => ?_)
  refine Wp.wp_addi fun w₁ y₁ => Wp.wp_addi fun w₂ y₂ => Wp.wp_subi fun w₃ y₃ _ z₃ => WP.block_nil ?_
  obtain g : ∀ r, r ≠ .edx → r ≠ .eax → s₃.gpr r = s.gpr r := fun r hr ha => by
    rw [g₃ r hr, u₂.other _ ha]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [show 8 * (i + 1) = 8 * i + 8 by omega_using []]
    exact h₃.upd (by rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.other _ (by decide)])
      (by rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.other _ (by decide)])
      (by rw [y₃.rd, y₂.rd, y₁.rd]) (by rw [y₃.wr, y₂.wr, y₁.wr]) (by rw [y₃.mem, y₂.mem, y₁.mem])
  · rw [y₃.other _ (by decide), y₂.other _ (by decide), y₁.gpr, g _ (by decide) (by decide), si,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
  · rw [y₃.other _ (by decide), y₂.gpr, y₁.other _ (by decide), g _ (by decide) (by decide), bi,
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
      show BITS + 8 * i + 8 = BITS + 8 * (i + 1) by omega_using []]
  · rw [y₃.gpr, y₂.other _ (by decide), y₁.other _ (by decide), g _ (by decide) (by decide), ci,
      Wp.ofNat_pred (by omega_using [hi])]
    congr 1
  · rw [z₃, y₂.other _ (by decide), y₁.other _ (by decide), g _ (by decide) (by decide), ci,
      Wp.ofNat_pred (by omega_using [hi]), Wp.ofNat_beq_zero (by omega_using [hi])]
    rfl

theorem scalarLoop_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) {s : State} (h : LInvS s₀ sA 0 s) :
    WP isa (.loop (.block scalarBitsByte) .ne) s (LInvS s₀ sA 32) := by
  refine WP.loop (M := isa) (Q := LInvS s₀ sA 32) (fun m t => ∃ i, m = 32 - i ∧ i < 32 ∧ LInvS s₀ sA i t) ?_ 32 s
    ⟨0, rfl, by decide, h⟩
  rintro m t ⟨i, rfl, hi, ht⟩
  refine WP.mono (scalarBitsByte_ok hp hA hi ht) fun u ⟨hu, z⟩ => ?_
  by_cases done : i + 1 = 32
  · refine .inl ⟨?_, done ▸ hu⟩
    simp only [eval, z, show 32 - (i + 1) = 0 by omega_using [done], decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, 32 - (i + 1), by omega_using [hi], i + 1, rfl, by omega_using [hi, done], hu⟩
    simp only [eval, z, show 32 - (i + 1) ≠ 0 by omega_using [hi, done], decide_false, Option.map_some,
      Bool.not_false]

theorem kb_getD {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < 32) :
    (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).getD i 0 = s₀.mem (addr (arg s₀ 1) i) := by
  simp only [Spec.X25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
    Option.map_some, Option.getD_some]
  rw [addr_eq (by have := hp.scalar_fit; omega_using [this, hi])]

theorem length_kb (s₀ : State) : (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32).length = 32 := by
  simp [Spec.X25519.bytesAt]

/-- The scalar's bits, clamped: bit `t` of the decoded scalar at `BITS + t`. -/
theorem loadScalar_ok {s₀ sA : State} (hp : Pre s₀) (hA : Saved s₀ sA) :
    WP isa loadScalar sA fun s' => Saved s₀ s' ∧ Frame [sub (arg s₀ 3) BITS 256] sA.mem s'.mem ∧
      ∀ t < 255, s'.mem (addr (arg s₀ 3) (BITS + t)) = BitVec.ofNat 8
        (bit (decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)) t) := by
  have hfit := hp.sc_fit
  unfold loadScalar
  refine WP.seq (Wp.wp_ldm (B := sA.gpr .esp) (o := 8) rfl
    (by rw [hA.esp, hA.rd, hA.wr]; exact hp.argIn (i := 1) (by decide))
    fun s₁ u₁ => Wp.wp_mov fun v₂ u₂ => Wp.wp_addi fun v₃ u₃ => Wp.wp_movi fun v₄ u₄ => WP.block_nil ?_)
  obtain e₄ : v₄.gpr .edi = sA.gpr .edi := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain h₁ : BInv s₀ sA 0 v₄ := ⟨e₄.trans hA.edi,
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)],
    by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd], by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr],
    by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine WP.seq (WP.mono (scalarLoop_ok hp hA ⟨h₁, ?_, ?_, by rw [u₄.gpr]; rfl⟩) fun s₂ h₂ => ?_)
  · rw [show arg s₀ 1 + BitVec.ofNat 32 0 = arg s₀ 1 from BitVec.add_zero _, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hA.esp]
    exact hp.arg_same hA.frame (i := 1) (by decide)
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hA.edi]; rfl
  replace h₂ := h₂.1
  unfold clampBits
  obtain inb : ∀ {s : State} {d : Nat}, s.wr = sA.wr → d < 256 →
      InRegions s.wr (addr (arg s₀ 3) (BITS + d)) 1 := fun hw hd =>
    ⟨_, by rw [hw, hA.wr]; exact hp.sc_in, scR_contains hfit (by simp only [BITS]; omega_using [hd]) (by decide)⟩
  refine Wp.wp_movi fun s₃ u₃ => ?_
  obtain edi₃ : s₃.gpr .edi = arg s₀ 3 := by rw [u₃.other _ (by decide)]; exact h₂.edi
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 0)) (by rw [edi₃]; rfl) (inb (by rw [u₃.wr, h₂.wr]) (by decide))
    fun s₄ u₄ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 1)) (by rw [u₄.gpr, edi₃])
    (inb (by rw [u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₅ u₅ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 2)) (by rw [u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₆ u₆ => ?_
  refine Wp.wp_movi fun s₇ u₇ => ?_
  refine wp_store8 (a := addr (arg s₀ 3) (BITS + 254)) (by rw [u₇.other _ (by decide), u₆.gpr, u₅.gpr, u₄.gpr, edi₃])
    (inb (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]) (by decide)) fun s₈ u₈ => WP.block_nil ?_
  obtain z3 : ((s₃.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by simp only [Reg8.reg, u₃.gpr]; decide
  obtain z4 : ((s₄.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₄.gpr]; exact z3
  obtain z5 : ((s₅.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 0 := by rw [u₅.gpr]; exact z4
  obtain o : ((s₇.gpr (Reg8.dl).reg).setWidth 8 : BitVec 8) = 1 := by simp only [Reg8.reg, u₇.gpr]; decide
  obtain m₈ : s₈.mem = ((((s₂.mem.writeW (addr (arg s₀ 3) (BITS + 0)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 1)) (0 : BitVec 8)).writeW (addr (arg s₀ 3) (BITS + 2)) (0 : BitVec 8)).writeW
      (addr (arg s₀ 3) (BITS + 254)) (1 : BitVec 8)) := by
    rw [u₈.mem, o, u₇.mem, u₆.mem, z5, u₅.mem, z4, u₄.mem, z3, u₃.mem]
  obtain g : ∀ r, r ≠ .edx → s₈.gpr r = s₂.gpr r := fun r hr => by
    rw [u₈.gpr, u₇.other _ hr, u₆.gpr, u₅.gpr, u₄.gpr, u₃.other _ hr]
  obtain hb : ∀ {m : Mem} {d : Nat} (v : BitVec 8), d < 256 → Frame [sub (arg s₀ 3) BITS 256] sA.mem m →
      Frame [sub (arg s₀ 3) BITS 256] sA.mem (m.writeW (addr (arg s₀ 3) (BITS + d)) v) := fun v hd hf =>
    hf.writeW (List.mem_singleton_self _) _ (sub_contains (by simp only [BITS]; omega_using [hfit])
      (by omega_using []) (by omega_using [hd]) (by decide))
  obtain f₈ : Frame [sub (arg s₀ 3) BITS 256] sA.mem s₈.mem := by
    rw [m₈]; exact hb _ (by decide) (hb _ (by decide) (hb _ (by decide) (hb _ (by decide) h₂.frame)))
  refine ⟨hA.of_frame hp f₈ (by decide) (by decide) (by decide) (by rw [g _ (by decide), h₂.edi, hA.edi])
    (by rw [g _ (by decide), h₂.esp]) (by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, h₂.rd])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, h₂.wr]), f₈, fun t ht => ?_⟩
  rw [scalar_bit (length_kb s₀) ht, m₈]
  obtain ne : ∀ (m : Mem) (v : BitVec 8) (e : Nat), e < 256 → t ≠ e →
      (m.writeW (addr (arg s₀ 3) (BITS + e)) v) (addr (arg s₀ 3) (BITS + t)) = m (addr (arg s₀ 3) (BITS + t)) :=
    fun m v e he h => byte_write_ne m v (by simp only [BITS]; omega_using [hfit, ht])
      (by simp only [BITS]; omega_using [hfit, he]) (by omega_using [h])
  by_cases h3 : t < 3
  · rw [ite_eq_left h3, ne _ _ 254 (by decide) (by omega_using [h3])]
    rcases (by omega_using [h3] : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
    · rw [ne _ _ 2 (by decide) (by decide), ne _ _ 1 (by decide) (by decide), byte_write_self]; rfl
    · rw [ne _ _ 2 (by decide) (by decide), byte_write_self]; rfl
    · rw [byte_write_self]; rfl
  · rw [ite_eq_right h3]
    by_cases h254 : t = 254
    · subst h254; rw [ite_eq_left rfl, byte_write_self]; rfl
    · rw [ite_eq_right h254, ne _ _ 254 (by decide) h254, ne _ _ 2 (by decide) (by omega_using [h3]),
        ne _ _ 1 (by decide) (by omega_using [h3]), ne _ _ 0 (by decide) (by omega_using [h3]),
        h₂.bits t (by omega_using [ht]), kb_getD hp (by omega_using [ht])]

/-! ## The ladder's initial state -/

theorem setSmall_step {x : BitVec 32} {s₀ s : State} (hc : Ctx 4096 x s) {o n : Nat} (ho : Below o) (hn : n < 8)
    (c : BitVec 32) (hk : Keep s₀ s) (hf : Frame [sub x o (4 * n)] s₀.mem s.mem)
    (hw : ∀ j < n, wd s.mem x (o + 4 * j) = if j = 0 then c else 0) :
    WP isa (.block [.mov .eax (.imm (if n = 0 then c else 0)), .store (sc (o + 4 * n)) .eax]) s fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * (n + 1))] s₀.mem s'.mem ∧
        ∀ j < n + 1, wd s'.mem x (o + 4 * j) = if j = 0 then c else 0 := by
  simp only [Below, T] at ho
  have hfit := hc.fit
  refine Wp.wp_movi fun s₁ u₁ => ?_
  obtain c₁ := (updKeep u₁).ctx hc
  refine Wp.wp_stm c₁.edi (c₁.inW (by omega_using [ho, hn]) (by decide)) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨hk.trans ((updKeep u₁).trans ⟨by rw [u₂.gpr], by rw [u₂.gpr], by rw [u₂.gpr], u₂.rd, u₂.wr⟩),
    ?_, fun j hj => ?_⟩
  · rw [u₂.mem, u₁.mem]
    exact frame_write1 (frameWiden hf hfit (Nat.le_refl _) (by omega_using []) (by omega_using [ho, hn]))
      hfit (by omega_using [ho, hn]) (by omega_using []) (by omega_using []) _
  · rw [u₂.mem, u₁.mem]
    by_cases e : j = n
    · subst e; rw [wd_write_self, u₁.gpr]
    · rw [wd_write_ne _ _ (by omega_using [hfit, ho, hj, hn]) (by omega_using [hfit, ho, hn])
        (by omega_using [hj, e])]
      exact hw j (by omega_using [hj, e])

theorem setSmalls_ok {x : BitVec 32} {s₀ : State} (hc₀ : Ctx 4096 x s₀) {o : Nat} (ho : Below o) (c : BitVec 32) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun k =>
      [.mov .eax (.imm (if k = 0 then c else 0)), .store (sc (o + 4 * k)) .eax])) s₀ fun s' =>
      Keep s₀ s' ∧ Frame [sub x o (4 * n)] s₀.mem s'.mem ∧
        ∀ j < n, wd s'.mem x (o + 4 * j) = if j = 0 then c else 0
  | 0, _ => WP.block_nil ⟨Keep.refl _, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (setSmalls_ok hc₀ ho c n (by omega_using [hn])) fun s₁ ⟨k₁, f₁, w₁⟩ =>
      setSmall_step (k₁.ctx hc₀) ho (by omega_using [hn]) c k₁ f₁ w₁)

/-- `[o] = c`. -/
theorem setSmall_ok {x : BitVec 32} {s : State} (hc : Ctx 4096 x s) {o : Nat} (ho : Below o) (c : BitVec 32) :
    WP isa (.block (setSmall o c)) s fun s' => Keep s s' ∧ Frame [sub x o 32] s.mem s'.mem ∧
      fe s'.mem x o = c.toNat :=
  WP.mono (setSmalls_ok hc ho c 8 (Nat.le_refl _)) fun _ ⟨k, f, w⟩ => ⟨k, f, by
    rw [fe]
    rw [num_congr (g := fun j => if j = 0 then c.toNat else 0) fun j hj => by
      show (wd _ x (o + 4 * j)).toNat = _; rw [w j hj]; split <;> rfl]
    simp only [num, Nat.reduceEqDiff, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.one_mul,
      Nat.zero_add]⟩

theorem F_setSmall {x : BitVec 32} {s' : State} {o : Nat} (c : BitVec 32) (h : fe s'.mem x o = c.toNat) :
    F s'.mem x o = toFe c.toNat := by simp only [F, h]

/-- The slots, other than `o`, after a frame of `o`'s. -/
theorem F_frame1 {m m' : Mem} {x : BitVec 32} {o q : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x o 32] m m') (ho : isSlot 288 o = true) (hq : isSlot 288 q = true) (hne : q ≠ o) :
    F m' x q = F m x q := by
  obtain hob := slot_below ho; have hqb := slot_below hq; simp only [Below, T] at hob hqb
  simp only [F]
  exact congrArg toFe (fe_frame1 hf hx (by omega_using [hob]) (by omega_using [hqb]) (slot_ne ho hq hne))

theorem frame_slot {m m' : Mem} {x : BitVec 32} {o : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32)
    (hf : Frame [sub x o 32] m m') (ho : isSlot 288 o = true) : Frame [sub x 288 640] m m' := by
  obtain hob := slot_below ho; have ho' := slot_ge ho; simp only [Below, T] at hob
  exact frameWiden hf hx ho' (by omega_using [hob]) (by omega_using [hob])

/-- The u-coordinate as `X1` holds it: decoded (RFC 7748 §5). -/
theorem fe_X1 {s₀ s : State} (hp : Pre s₀) (hw : ∀ j < 8, wd s.mem (arg s₀ 3) (X1 + 4 * j) = pv s₀ j) :
    fe s.mem (arg s₀ 3) X1 = decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
  have hpf := hp.point_fit
  obtain e1 : fe s.mem (arg s₀ 3) X1 = num (fun k => (pv s₀ k).toNat) 8 :=
    num_congr fun j hj => by show (wd _ _ _).toNat = _; rw [hw j hj]
  obtain e2 : num (fun k => (pv s₀ k).toNat) 8 = num (fun k => (pw s₀ k).toNat) 8 % 2 ^ 255 := by
    rw [(fold_top (f := fun k => (pw s₀ k).toNat) fun _ _ => BitVec.isLt _).1, num_top]
    obtain n7 : num (fun k => (pv s₀ k).toNat) 7 = num (fun k => (pw s₀ k).toNat) 7 :=
      num_congr fun j hj => by
        show (pv s₀ j).toNat = (pw s₀ j).toNat
        rw [pv, ite_eq_right (show j ≠ 7 by omega_using [hj])]
    rw [n7]
    simp only [pv, ite_true, low31_toNat]
  obtain e3 : num (fun k => (pw s₀ k).toNat) 8 = leNum (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32) := by
    rw [leNum_bytesAt_words32]
    obtain r : ∀ k < 8, (pw s₀ k).toNat =
        (s₀.mem.readW ((arg s₀ 2).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32).toNat := fun k hk => by
      simp only [pw, wd]; rw [addr_eq (by omega_using [hpf, hk])]
    simp only [num, r 0 (by decide), r 1 (by decide), r 2 (by decide), r 3 (by decide), r 4 (by decide),
      r 5 (by decide), r 6 (by decide), r 7 (by decide), Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      Nat.reduceMul, Nat.reducePow, Nat.one_mul, Nat.zero_add]
  rw [e1, e2, e3, decodeUCoordinate_eq (length_bytesAt _ _ _)]

/-- The scalar, decoded. -/
abbrev kOf (s₀ : State) : Nat := decodeScalar25519 (Spec.X25519.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 32)

/-- The u-coordinate, decoded. -/
abbrev uOf (s₀ : State) : Fe := toFe (decodeUCoordinate (Spec.X25519.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 32))

theorem initLadder_eq : initLadder = copy X3 X1 ++ (setSmall X2 1 ++
    (setSmall Z2 0 ++ (setSmall Z3 1 ++ ([.mov .eax (.imm 0), .store (sc SWAP) .eax] : List Instr)))) := by
  simp only [initLadder, List.append_assoc]

/-- The arguments read: the ladder's initial state, in `LInv 255` but for the counter. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) :
    WP isa setup s₀ fun s => Base (arg s₀ 3) (kOf s₀) s₀ s ∧ F s.mem (arg s₀ 3) X1 = uOf s₀ ∧
      F s.mem (arg s₀ 3) X2 = 1 ∧ F s.mem (arg s₀ 3) Z2 = 0 ∧ F s.mem (arg s₀ 3) X3 = uOf s₀ ∧
      F s.mem (arg s₀ 3) Z3 = 1 ∧ wd s.mem (arg s₀ 3) SWAP = 0 := by
  have hfit := hp.sc_fit
  unfold setup
  refine WP.seq (WP.block_append (WP.mono (save_ok hp) fun s₁ h₁ => ?_))
  refine WP.mono (loadPoint_ok hp h₁) fun s₂ ⟨h₂, w₂⟩ => ?_
  refine WP.seq (WP.mono (loadScalar_ok hp h₂) fun s₃ ⟨h₃, f₃, b₃⟩ => ?_)
  rw [initLadder_eq]
  obtain B₃ : Base (arg s₀ 3) (kOf s₀) s₀ s₃ :=
    ⟨⟨h₃.edi, hfit, by rw [h₃.wr]; exact hp.sc_in, by decide, fun _ hW => absurd hW (by decide)⟩, h₃.esp, h₃.rd, h₃.wr, h₃.frame, h₃.saved, b₃⟩
  obtain x1₃ : F s₃.mem (arg s₀ 3) X1 = uOf s₀ := by
    simp only [F, uOf]
    rw [← fe_X1 hp w₂]
    exact congrArg toFe (fe_frame1 f₃ hfit (by decide) (by decide) (.inr (by decide)))
  obtain sl : ∀ q, isSlot 288 q = true → Below q := fun q hq => slot_below hq
  refine WP.block_append (WP.mono (copy_ok B₃.ctx (o := X3) (a := X1) (by decide) (by decide) (by decide))
    fun s₄ ⟨k₄, f₄, e₄⟩ => ?_)
  obtain B₄ := B₃.ops k₄ (frame_slot hfit f₄ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₄.ctx (o := X2) (by decide) 1) fun s₅ ⟨k₅, f₅, e₅⟩ => ?_)
  obtain B₅ := B₄.ops k₅ (frame_slot hfit f₅ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₅.ctx (o := Z2) (by decide) 0) fun s₆ ⟨k₆, f₆, e₆⟩ => ?_)
  obtain B₆ := B₅.ops k₆ (frame_slot hfit f₆ (by decide))
  refine WP.block_append (WP.mono (setSmall_ok B₆.ctx (o := Z3) (by decide) 1) fun s₇ ⟨k₇, f₇, e₇⟩ => ?_)
  obtain B₇ := B₆.ops k₇ (frame_slot hfit f₇ (by decide))
  refine Wp.wp_movi fun s₈ u₈ => ?_
  obtain c₈ := (updKeep u₈).ctx B₇.ctx
  refine Wp.wp_stm c₈.edi (c₈.inW (by decide) (by decide)) fun s₉ u₉ => WP.block_nil ?_
  obtain m₉ : s₉.mem = s₇.mem.writeW (addr (arg s₀ 3) SWAP) (0 : BitVec 32) := by rw [u₉.mem, u₈.gpr, u₈.mem]
  obtain f₉ : Frame [sub (arg s₀ 3) SWAP 4] s₇.mem s₉.mem := by
    rw [m₉]; exact frame_write1 (Frame.refl _ _) hfit (by decide) (Nat.le_refl _) (Nat.le_refl _) _
  obtain F₉ : ∀ q, isSlot 288 q = true → F s₉.mem (arg s₀ 3) q = F s₇.mem (arg s₀ 3) q := fun q hq => by
    obtain hq' := slot_ge hq; have hqb := slot_below hq; simp only [Below, T] at hqb
    simp only [F]
    exact congrArg toFe (fe_frame1 f₉ hfit (by decide) (by omega_using [hqb]) (.inr (by simp only [SWAP]; omega_using [hq'])))
  refine ⟨B₇.of_frame (by rw [u₉.gpr, u₈.other _ (by decide)]) (by rw [u₉.gpr, u₈.other _ (by decide)])
    (by rw [u₉.rd, u₈.rd]) (by rw [u₉.wr, u₈.wr]) f₉ (by decide) (by decide) (.inl (by decide)) (by decide),
    ?_, ?_, ?_, ?_, ?_, by rw [m₉, wd_write_self]⟩
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_frame1 hfit f₅ (by decide) (by decide) (by decide),
      F_frame1 hfit f₄ (by decide) (by decide) (by decide), x1₃]
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_setSmall _ e₅]; rfl
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide), F_setSmall _ e₆]; rfl
  · rw [F₉ _ (by decide), F_frame1 hfit f₇ (by decide) (by decide) (by decide),
      F_frame1 hfit f₆ (by decide) (by decide) (by decide), F_frame1 hfit f₅ (by decide) (by decide) (by decide)]
    simp only [F] at x1₃ ⊢
    rw [e₄]; exact x1₃
  · rw [F₉ _ (by decide), F_setSmall _ e₇]; rfl

end VG.Proof.X25519.X86

end

end


/-!
# X25519 on x86 (32-bit): the whole function

The setup, the ladder, the last swap, the inversion and the result, composed:
`vg_x25519` writes `X25519(k, u)` to `out` (`x25519_eq`), and restores the
callee-saved registers.
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86 VG.Spec.X25519

theorem x25519_code : Impl.X25519.X86.x25519 =
    .seq setup (.seq (.seq (.block [.mov .esi (.imm 255)]) (.loop (.block step) .ne))
      (.seq (.block lastSwap) (.seq Impl.X25519.X86.invert (.block finish)))) := rfl

theorem finish_eq : finish = ops ([.mul X2 X2 Field32.E1] : List Op) ++ (freeze X2 ++ (.mov .esi (.mem (at_ .esp 4)) ::
    (((List.range 8).flatMap fun k => ([.mov .eax (.mem (sc (X2 + 4 * k))), .store (at_ .esi (4 * k)) .eax] :
      List Instr)) ++ restore))) := by
  simp only [finish, ops, List.flatMap_cons, List.flatMap_nil, Op.code, List.append_nil, List.append_assoc,
    List.cons_append]

/-- The result `r`, as the words of its value at `[x + X2]`, to `out`, and the registers restored. -/
theorem finish_ok {s₀ s : State} (hp : Pre s₀) (hb : After (arg s₀ 3) s₀ s) :
    WP isa (.block finish) s fun s' => abiPreserved s₀ s' ∧
      Spec.X25519.bytesAt s'.mem ((arg s₀ 0).setWidth 64) 32 =
        encodeUCoordinate (F s.mem (arg s₀ 3) X2 * F s.mem (arg s₀ 3) Field32.E1) := by
  have hfit := hp.sc_fit
  rw [finish_eq]
  refine WP.block_append (WP.mono (ops_ok (lo := 288) [.mul X2 X2 Field32.E1] hb.ctx (by decide)) fun s₁ ⟨k₁, f₁, e₁⟩ => ?_)
  obtain b₁ := hb.ops k₁ f₁
  refine WP.block_append (WP.mono (freeze_ok b₁.ctx (lo := 288) (o := X2) (by decide)) fun s₂ ⟨k₂, f₂, e₂⟩ => ?_)
  obtain b₂ := b₁.ops k₂ (frame_wide hfit (lo := 288) (by decide) (by decide) f₂)
  -- The value: fully reduced.
  obtain hv : fe s₂.mem (arg s₀ 3) X2 = (F s.mem (arg s₀ 3) X2 * F s.mem (arg s₀ 3) Field32.E1).val := by
    rw [e₂, ← toFe_val]
    have := e₁ X2 (by decide)
    simp only [X86.run, opOut, opVal, Function.update_self] at this
    exact congrArg Fin.val this
  refine Wp.wp_ldm (B := s₂.gpr .esp) (o := 4) rfl (by rw [b₂.esp, b₂.rd, b₂.wr]; exact hp.argIn (i := 0) (by decide))
    fun s₃ u₃ => ?_
  obtain o₃ : OInv s₀ s₃ 0 s₃ := ⟨by rw [u₃.other _ (by decide)]; exact b₂.ctx.edi,
    by rw [u₃.gpr, b₂.esp]; exact hp.arg_same' b₂.frame (i := 0) (by decide), rfl, rfl, rfl, Frame.refl _ _,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain w₃ : s₃.wr = s₀.wr := by rw [u₃.wr, b₂.wr]
  refine WP.block_append (WP.mono (outWords_ok hp w₃ 8 (Nat.le_refl _) s₃ o₃) fun s₄ o₄ => ?_)
  obtain c₄ : Ctx 4096 (arg s₀ 3) s₄ :=
    ⟨o₄.edi, hfit, by rw [o₄.wr, w₃]; exact hp.sc_in, by decide, fun _ hW => absurd hW (by decide)⟩
  -- The saved words, unchanged by the stores to `out`.
  obtain sv : Spill.Saved s₄.mem (addr (arg s₀ 3)) s₀.gpr savedSlots := b₂.saved.of_readW fun p hq => by
    have := savedSlots_bound p hq
    show wd s₄.mem (arg s₀ 3) p.2 = wd s₂.mem (arg s₀ 3) p.2
    rw [wd_frame o₄.frame fun r hr => by
      rw [List.mem_singleton.mp hr]
      refine Region.Disjoint.symm (hp.out_sc.sub_right ?_)
      rw [scR_eq]; exact sub_sub hfit (Nat.zero_le _) (by omega_using [this]) (by omega_using [this]),
      u₃.mem]
  refine WP.mono (restore_ok c₄ sv) fun s₅ ⟨m₅, esp₅, g₅⟩ => ⟨?_, ?_⟩
  · refine ⟨fun r hr => ?_, ?_⟩
    · by_cases h : r = .esp
      · subst h; rw [esp₅, o₄.esp, u₃.other _ (by decide), b₂.esp]
      · exact g₅ r hr h
    · rw [m₅]
      obtain r₄ : s₄.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₃.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
        o₄.frame.readW (Region.contains_self _ _) (by simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_out)
          (by decide)
      rw [r₄, u₃.mem]
      exact b₂.frame.readW (Region.contains_self _ _) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro r (rfl | rfl)
        · exact hp.ret_sc
        · exact hp.ret_stk) (by decide)
  · rw [m₅, encodeUCoordinate_eq]
    refine bytesAt_leBytes_words32 _ _ _ fun j hj => ?_
    have hof := hp.out_fit
    rw [← addr_eq (by omega_using [hof, hj]), ← wd, o₄.words j hj, u₃.mem, ← hv, Nat.pow_mul]
    exact (num_digit j (f := fun k => wv s₂.mem (arg s₀ 3) (X2 + 4 * k)) (fun _ _ => wv_lt _ _ _) hj).symm

theorem ladderAfter_255_eq (k : Nat) (x1 : Fe) :
    ladderAfter k x1 255 = { x2 := 1, z2 := 0, x3 := x1, z3 := 1, swap := 0 } := rfl

/-- The function's correctness. -/
theorem x25519_correct {s₀ : State} (hp : Pre s₀) :
    WP isa Impl.X25519.X86.x25519 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.X25519.x25519X86.post s₀ s' := by
  rw [x25519_code]
  refine WP.seq (WP.mono (setup_ok hp) fun s₁ ⟨b₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  refine WP.seq (WP.seq (Wp.wp_movi fun s₂ u₂ => WP.block_nil ?_))
  obtain b₂ : Base (arg s₀ 3) (kOf s₀) s₀ s₂ := b₁.of_frame (o := 288) (n := 640) (u₂.other _ (by decide))
    (u₂.other _ (by decide)) u₂.rd u₂.wr (by rw [u₂.mem]; exact Frame.refl _ _) (by decide) (by decide)
    (.inr (Nat.le_refl _)) (by decide)
  obtain L₂ : LInv (arg s₀ 3) (kOf s₀) (uOf s₀) s₀ 255 s₂ :=
    ⟨b₂, u₂.gpr, by rw [u₂.mem]; exact x1₁, by rw [u₂.mem, ladderAfter_255_eq]; exact x2₁,
      by rw [u₂.mem, ladderAfter_255_eq]; exact z2₁, by rw [u₂.mem, ladderAfter_255_eq]; exact x3₁,
      by rw [u₂.mem, ladderAfter_255_eq]; exact z3₁, by rw [u₂.mem, ladderAfter_255_eq]; exact sw₁⟩
  refine WP.mono (ladderLoop_ok L₂) fun s₃ L₃ => ?_
  refine WP.seq (WP.mono (lastSwap_ok L₃) fun s₄ ⟨b₄, x2₄, z2₄⟩ => ?_)
  refine WP.seq (WP.mono (invert_ok b₄ hp.sp_room hp.sc_callStk) fun s₅ ⟨b₅, t1₅, x2₅⟩ => ?_)
  refine WP.mono (finish_ok hp b₅) fun s₆ ⟨abi, out⟩ => ⟨abi, ?_⟩
  show Spec.X25519.bytesAt s₆.mem ((arg s₀ 0).setWidth 64) 32 = _
  rw [out, t1₅, x2₅, x2₄, z2₄, x25519_eq]

end VG.Proof.X25519.X86

end

end

/-!
# X25519 on x86 (32-bit): correct and constant time

Correctness (`x25519_ok`) and constant time (`x25519_ct`, by taint tracking:
the only branches are on the loop counters, and every address is a pointer
plus a constant or the counter, through the inversion's calls of
`vg_gf25519_r32_mul` and `vg_gf25519_r32_sqn`) against the target's contract `x25519X86`, which
`vg_x25519_exchange`'s proof (`Exchange.lean`) composes, with a state
satisfying it (`satState`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86

/-- The taint analysis starts with the stack arguments public, and the words
holding `out` and `scratch` known to be the base addresses of the writable
regions, and the 8 bytes below `esp`, where the inversion's call pushes, apart
from them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [32, 4096], argLen := 20, argBases := [(4, 0), (16, 1)],
    room := 8 }

theorem wf₀ {s : State} (hp : Pre s) : VG.X86.Taint.Wf τ₀ s := by
  have hsc := hp.sc_fit; have ho := hp.out_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τ₀], by simpa [hp.wr] using hp.out_sc, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hp.sp_room, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_using [hsc, ho]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_out hp.args_out
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by omega_using [hs]) hp.ret_sc hp.args_sc
  · intro p hp'
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.stk_out
    · exact hp.stk_sc

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.X25519.x25519X86.pre s₁) (h₂ : Proof.X25519.x25519X86.pre s₂)
    (hpub : Proof.X25519.x25519X86.pub s₁ s₂) : VG.X86.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := Pre.of _ h₁; have hp₂ := Pre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, wf₀ hp₁, wf₀ hp₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [outR, a0, a3]
  · simp only [τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by omega_using [hk]
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem x25519_ct : ConstantTime isa Proof.X25519.x25519X86.pre Proof.X25519.x25519X86.pub
    Impl.X25519.X86.x25519 :=
  VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp) (by taint_decide)

/-- Memory holding the arguments `0x1000, 0x2000, 0x3000, 0x4000` at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x8009 then 0x20 else if a = 0x800d then 0x30 else
  if a = 0x8011 then 0x40 else 0

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x8004, 16⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x4000, 4096⟩]

theorem x25519_ok (s : State) (hs : Proof.X25519.x25519X86.pre s) :
    ∃ t s', Exec isa Impl.X25519.X86.x25519 s t s' ∧ abiPreserved s s' ∧ Proof.X25519.x25519X86.post s s' :=
  x25519_correct (Pre.of s hs)

end VG.Proof.X25519.X86
