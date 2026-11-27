module

public import VerifiedGarbage.Proof.Ed448.X86.CombBase
meta import VerifiedGarbage.Proof.Ed448.X86.CombBase
import VerifiedGarbage.Proof.Ed448.X86.BaseLit
meta import VerifiedGarbage.Proof.Ed448.X86.BaseLit
public import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
meta import VerifiedGarbage.Proof.Ed448.X86.BaseEncode
import VerifiedGarbage.Proof.X448.X86.Counters
meta import VerifiedGarbage.Proof.X448.X86.Counters
import VerifiedGarbage.Proof.X448.X86.Iter
meta import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.Ed448.ScalarWords
import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.Syms
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.X25519.X86.Basic
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.X448.X86.Columns
import VerifiedGarbage.Proof.X448.X86.Copy
import VerifiedGarbage.Proof.X448.X86.FnVerified
import VerifiedGarbage.Proof.X448.X86.Frame
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Select
import VerifiedGarbage.Proof.X448.X86.Small
import VerifiedGarbage.Proof.X448.X86.Step
meta import VerifiedGarbage.Proof.Ed448.ScalarWords
meta import VerifiedGarbage.Proof.Ed448.X86.ScalarMulAdd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Mmx
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.X25519.X86.Basic
meta import VerifiedGarbage.Proof.X448.Bytes
meta import VerifiedGarbage.Proof.X448.X86.Columns
meta import VerifiedGarbage.Proof.X448.X86.Copy
meta import VerifiedGarbage.Proof.X448.X86.FnVerified
meta import VerifiedGarbage.Proof.X448.X86.Frame
meta import VerifiedGarbage.Proof.X448.X86.Freeze
meta import VerifiedGarbage.Proof.X448.X86.Restore
meta import VerifiedGarbage.Proof.X448.X86.Select
meta import VerifiedGarbage.Proof.X448.X86.Small
meta import VerifiedGarbage.Proof.X448.X86.Step

/-! ### `Ed448.X86.BaseWhole`, which this module and modules that import it used -/

section

/-!
# Ed448 base-point multiplication on x86 (32-bit): the whole function

`vg_ed448_scalar_base(out = [esp + 4], scalar = [esp + 8], scratch = [esp + 12])`
against a local contract (`scalarBaseLocal`, `BaseLocal.lean`: the arguments
only read): it computes the encoding of the comb over the scalar's bits
(`scalarBase_comb`): the entry, the scalar's bits, the comb (`combBase_ok`),
the inversion of `Z` and the encoding. Every write is in the working space but
the result's, so the arguments and the scalar are read unchanged; the
callee-saved registers are restored from the working space, and the return
address is kept.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86
open VG.Proof.Ed448 (signedComb pt)
open VG.Impl.Ed448.X86 (scalarBase initSlots baseBits baseEntry combVal combSym combBase)
open VG.Impl.X448.X86 (slot BITS ACC at_)
open VG.Spec.Ed448 (bytesAt decodeLE)

/-- The precondition, by name. -/
structure BasePre (s : State) : Prop where
  rd : s.rd = [⟨(arg s 1).setWidth 64, 57⟩, ⟨argAddr s 0, 12⟩, TblR ((s.syms combSym).setWidth 64)]
  wr : s.wr = [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2)]
  out_sc : (⟨(arg s 0).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  scalar_sc : (⟨(arg s 1).setWidth 64, 57⟩ : Region).Disjoint (scR (arg s 2))
  args_out : (⟨argAddr s 0, 12⟩ : Region).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  args_sc : (⟨argAddr s 0, 12⟩ : Region).Disjoint (scR (arg s 2))
  ret_out : (retR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  ret_sc : (retR s).Disjoint (scR (arg s 2))
  out_fit : (arg s 0).toNat + 57 ≤ 2 ^ 32
  scalar_fit : (arg s 1).toNat + 57 ≤ 2 ^ 32
  sc_fit : (arg s 2).toNat + 8192 ≤ 2 ^ 32
  sp_fit : (s.gpr .esp).toNat + 16 ≤ 2 ^ 32
  sp_room : 20 ≤ (s.gpr .esp).toNat
  stk_out : (stkR s).Disjoint ⟨(arg s 0).setWidth 64, 57⟩
  stk_sc : (stkR s).Disjoint (scR (arg s 2))
  held : CombHeld s [⟨(arg s 0).setWidth 64, 57⟩, scR (arg s 2), stkR s]

theorem BasePre.of {s : State} (h : scalarBaseLocal.pre s) : BasePre s := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem BasePre.stk_args {s : State} (h : BasePre s) : (stkR s).Disjoint ⟨argAddr s 0, 12⟩ := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> simp only [argAddr] <;> bv_omega

theorem BasePre.stk_ret {s : State} (h : BasePre s) : (stkR s).Disjoint (retR s) := by
  have h1 := h.sp_room
  have h2 := h.sp_fit
  refine Region.disjoint_of_le (Or.inl ?_) ?_ ?_ <;> bv_omega

theorem BasePre.args {s : State} (h : BasePre s) : Args s 3 2 :=
  ⟨by rw [h.rd]; simp, by have := h.sp_fit; omega_using [this], by decide, by rw [h.wr]; simp, h.sc_fit,
    h.args_sc, h.ret_sc⟩

theorem combVal_lt (i : Nat) : combVal i < Spec.X448.P := by
  unfold combVal
  repeat (first | exact Fin.isLt _ | (split; exact Fin.isLt _) | (split; decide +kernel) | split)
  decide +kernel

section
variable (σ : State)
/-- The working space and the scalar, from the entry state `σ`. -/
abbrev bsB : Addr := (arg σ 2).setWidth 64
abbrev kB : Nat := decodeLE (bytesAt σ.mem ((arg σ 1).setWidth 64) 57)
end

/-- After the entry block, from the entry state `σ`. -/
structure BMid (σ s : State) : Prop where
  pre : BasePre σ
  fe : FE bsB σ s
  rd : s.rd = σ.rd
  syms : s.syms = σ.syms
  saved : Saved (bsB σ) σ.gpr s.mem
  bits : BitsAtB (bsB σ) (kB σ) s.mem
  init : CombInit (E s.mem (bsB σ))

/-- The comb's tables, from the entry state's. -/
theorem BasePre.tblMem {σ s : State} (h : BasePre σ) (fe : FE bsB σ s) (hr : s.rd = σ.rd) :
    TblMem (σ.syms combSym) s := by
  obtain ⟨w, fit, far⟩ := h.held
  have far' : ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20], (TblR ((σ.syms combSym).setWidth 64)).Disjoint r := by
    rw [h.wr, ← stkR_below h.sp_room]
    simpa using far
  exact ⟨fit, by rw [hr, h.rd]; simp, w.frame (by rw [combWords_length]; decide) fe.frame far', by rw [fe.sp, fe.wr]; exact far'⟩

theorem entry_stage {s₀ : State} (h : BasePre s₀) :
    WP isa baseEntry s₀ (BMid s₀) := by
  refine WP.of_syms ?_
  have hA := h.args
  have hin : Input s₀ (bsB s₀) (arg s₀ 1) 57 :=
    Input.of_region h.scalar_fit (by rw [h.rd]; simp) h.scalar_sc
  refine WP.seq (WP.mono (save_ok hA) fun s₁ ⟨hs₁, sv₁, o₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (initSlots_ok hs₁ combVal) fun s₂ ⟨l₂, o₂, k₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have k02 : Keeps [.eax, .ebx, .ebp, .edi] s₀ s₂ := (k₁.mono (by decide)).trans (k₂.mono (by decide))
  have o02 : Outside (bsB s₀) 0 8192 s₀.mem s₂.mem :=
    (o₁.mono (by omega_using []) (by omega_using [])).trans (o₂.mono (by omega_using []) (by omega_using []))
  unfold baseBits
  refine WP.seq (hA.load (i := 1) (k02.1 _ (by decide)) k02.2.1 k02.2.2 o02 (by decide)
    fun s₃ u₃ => WP.block_nil ?_)
  have hs₃ := hs₂.of_upd u₃ (by decide)
  refine WP.mono (baseBytes_ok (k := (arg s₀ 1).setWidth 64) hs₃ (by rw [u₃.gpr]) (by rw [u₃.gpr]; exact hin.fit)
    (by rw [u₃.rd, u₃.wr, k02.2.1, k02.2.2]; exact hin.read) hin.far) fun s₄ ⟨k₄, o₄, bits₄⟩ sy => ?_
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  have mem34 : bytesAt s₃.mem ((arg s₀ 1).setWidth 64) 57 = bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57 := by
    rw [u₃.mem]; exact hin.bytes o02
  rw [mem34] at bits₄
  have e₄ : ∀ i : Index, E s₄.mem (bsB s₀) i = Proof.X448.toFe (combVal i.val) := by
    intro i
    rw [← initSlots_E combVal_lt l₂ i]
    simp only [E, F]
    rw [o₄.fe (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega_using []))
      (by have := i.isLt; simp only [slot]; omega_using []), u₃.mem]
  have k04 : Keeps [.eax, .ebx, .ebp, .edi, .esi, .edx, .ecx] s₀ s₄ :=
    (k02.mono (by decide)).trans ((u₃.rest (by decide)).trans (k₄.mono (by decide)))
  have sp₄ : s₄.gpr .esp = s₀.gpr .esp := k04.1 _ (by decide)
  have hc₄ : CallCtx s₄ (bsB s₀) := ⟨by rw [sp₄]; exact h.sp_room, by
    simp only [callStk, sp₄]; rw [← stkR_below h.sp_room]; exact h.stk_sc.symm⟩
  have o4w : Outside (bsB s₀) 0 8192 s₃.mem s₄.mem := o₄.mono (by omega_using []) (by simp only [BITS]; omega_using [])
  rw [u₃.mem] at o4w
  have ws : (⟨bsB s₀, 8192⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) 20] := by
    rw [h.wr]; simp
  refine ⟨h, ⟨⟨hs₄, hc₄⟩, sp₄, k04.2.2, (Outside.frame (o02.trans o4w)).mono fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ws⟩, k04.2.1, sy,
    (sv₁.outside o₂ (by decide)).outside (u₃.mem ▸ o₄) (by decide), bits₄, combInit _ e₄⟩

/-- After the comb, from the entry state `σ`. -/
structure BL (σ s : State) : Prop where
  pre : BasePre σ
  fe : FE bsB σ s
  rd : s.rd = σ.rd
  saved : Saved (bsB σ) σ.gpr s.mem
  r : pt (E s.mem (bsB σ)) 0 1 2 = signedComb (kB σ)

theorem comb_stage {σ s : State} (h : BMid σ s) : WP isa combBase s (BL σ) :=
  WP.mono (h.fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => CombKeep (bsB σ) s t ∧ pt (E t.mem (bsB σ)) 0 1 2 = signedComb (kB σ))
    (WP.mono (combBase_ok h.fe.fin.scr h.fe.fin.ctx (congrFun h.syms _) (h.pre.tblMem h.fe h.rd) h.bits h.init)
      fun t ⟨k, r⟩ => ⟨⟨h.fe.fin.scr.of_keeps k.regs (by decide), h.fe.fin.ctx.keep (k.regs.1 _ (by decide))⟩,
        k.regs.1 _ (by decide), k.regs.2.2, k, r⟩))
    fun t ⟨fe, k, r⟩ => ⟨h.pre, fe, k.regs.2.1.trans h.rd, h.saved.wsout2 k.mem (by decide) (by decide), r⟩

theorem encode_stage {σ s : State} (h : BL σ s) :
    WP isa Impl.Ed448.X86.baseEncode s fun t => abiPreserved σ t ∧
      bytesAt t.mem ((arg σ 0).setWidth 64) 57 = Spec.Ed448.encodePoint (signedComb (kB σ)) := by
  have hp := h.pre
  have fe := h.fe
  have hawr : ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20], (⟨argAddr σ 0, 4 * 3⟩ : Region).Disjoint r := by
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.args_out
    · exact hp.args_sc
    · exact hp.stk_args.symm
  refine WP.mono (baseEncode_ok hp.args (by decide) fe.sp h.rd fe.wr fe.frame hawr
    fe.fin.scr fe.fin.ctx (by rw [hp.wr]; simp) hp.out_fit hp.out_sc
    h.saved) fun t ⟨bt, rt, kt, ft⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact rt (.ebx, 0) (by decide)
    · exact rt (.esi, 4) (by decide)
    · exact rt (.edi, 8) (by decide)
    · exact rt (.ebp, 12) (by decide)
    · rw [kt.1 _ (by decide), fe.sp]
  · have ret : (retR σ).Contains ((σ.gpr .esp).setWidth 64) 4 := by
      simpa only [BitVec.add_zero] using
        Offset.contains_base ((σ.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide)
          (by decide)
    refine (fe.frame.trans ft).readW ret ?_ (by decide)
    rw [hp.wr, ← stkR_below hp.sp_room]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.ret_out
    · exact hp.ret_sc
    · exact hp.stk_ret.symm
  · rw [bt]
    exact congrArg Spec.Ed448.encodePoint h.r

theorem scalarBase_comb {s₀ : State} (h : BasePre s₀) :
    WP isa scalarBase s₀ fun t => abiPreserved s₀ t ∧
      bytesAt t.mem ((arg s₀ 0).setWidth 64) 57 =
        Spec.Ed448.encodePoint (signedComb (decodeLE (bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 57))) := by
  unfold scalarBase
  exact WP.seq (WP.mono (entry_stage h) fun _ m => WP.seq (WP.mono (comb_stage m) fun _ l => encode_stage l))

end VG.Proof.Ed448.X86

end

end

/-!
# Ed448 base-point multiplication on x86 (32-bit): constant time

The calls of the field functions are related run by run (`RelCT`,
`Proof/X448/X86/Runs.lean`), and so is the whole function: the entry block
from the arguments (`scalarTaint`), the field programs by the field
functions' constant time, the selection of the comb's entry (a scan of every
entry under masks), the counter and the encoding's last block by the taint
analysis from what each run's correctness says of its own state
(the stages above), and the loop and the inversion's runs of
squarings by `RelCT.loop`. The comb is related for any function that runs it
(`combBaseG_tr`), `vg_x448_base` too.
-/

@[expose] public section

namespace VG.Proof.Ed448.X86

open VG VG.X86 VG.Proof.X448.X86 VG.Proof.X448.Radix16
open VG.Proof.X448 (nib nib_lt mag mag_lt)
open VG.Impl.Ed448.X86 (scalarBase baseEncode toOp field baseEntry combSym TPTR tblSetup digitAdd combStep combLoop
  double4 combFinish combBase)
open VG.Impl.Ed448 (doubleOps addOps)
open VG.Impl.X448.X86 (BITS ACC ops)

/-- Two entry states the constant-time statement relates. -/
def BP₀ (σ₁ σ₂ : State) : Prop :=
  scalarBaseLocal.pre σ₁ ∧ scalarBaseLocal.pre σ₂ ∧ scalarBaseLocal.pub σ₁ σ₂

theorem BP₀.hp {σ₁ σ₂ : State} (h : BP₀ σ₁ σ₂) : bsB σ₁ = bsB σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp :=
  ⟨by simp only [bsB, h.2.2.2.2.2.1], h.2.2.1⟩

/-! ## The entry -/

theorem scalarBase_wf {s : State} (h : scalarBaseLocal.pre s) :
    VG.X86.Taint.Wf (scalarTaint 2 3) s := by
  have hp := BasePre.of h
  exact scalarTaint_wf hp.args hp.wr hp.out_sc hp.out_fit hp.ret_out hp.args_out

theorem scalarBase_agree {s t : State} (hs : scalarBaseLocal.pre s) (ht : scalarBaseLocal.pre t)
    (hp : scalarBaseLocal.pub s t) : VG.X86.Taint.Agree (scalarTaint 2 3) s t := by
  obtain ⟨sp, a0, a1, a2, _⟩ := hp
  have ps := BasePre.of hs
  have pt := BasePre.of ht
  refine scalarTaint_agree (scalarBase_wf hs) (scalarBase_wf ht) sp ?_ (by decide)
    ps.wr pt.wr ps.args.sp_fit pt.args.sp_fit
  intro i hi
  rcases (by omega_using [hi] : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  exacts [a0, a1, a2]

/-! ## The comb

The comb leaves the same trace in two runs whatever function runs it (`combBaseG_tr`, for
`vg_x448_base` too): from the field arithmetic's invariant (`FE bs`), the scalar's bits in the
working space and the tables, for the working space `bs` and the scalar `k` of a run, at the same
address of the static. -/

section
variable {P₀ : State → State → Prop} {bs : State → Addr} {k : State → Nat}

/-- What the comb's code needs of a run. -/
structure CombG (bs : State → Addr) (k : State → Nat) (σ t : State) : Prop where
  fe : FE bs σ t
  rd : t.rd = σ.rd
  bits : BitsAtB (bs σ) (k σ) t.mem
  tm : ∀ u, FE bs σ u → u.rd = σ.rd → TblMem (σ.syms combSym) u

/-- In the loop, after `n` steps. -/
structure RowG (bs : State → Addr) (k : State → Nat) (n : Nat) (σ t : State) : Prop extends CombG bs k σ t where
  esi : t.gpr .esi = BitVec.ofNat 32 n
  lt : n < 57
  ptr : word t.mem (bs σ) TPTR = σ.syms combSym

theorem RowG.tbl {n : Nat} {σ t : State} (h : RowG bs k n σ t) : TblAt (bs σ) (σ.syms combSym) t :=
  ⟨h.tm t h.fe h.rd, h.ptr⟩

theorem RowG.keep {n : Nat} {σ s t : State} (h : RowG bs k n σ s) (fe : FE bs σ t) (kp : Keep (bs σ) s t) :
    RowG bs k n σ t :=
  ⟨⟨fe, kp.regs.2.1.trans h.rd, h.bits.keep kp.mem, h.tm⟩, (kp.regs.1 _ (by decide)).trans h.esi, h.lt,
    (kp.mem.word (Or.inr (by decide)) (Or.inr (by decide)) (by decide)).trans h.ptr⟩

/-- A step's piece. -/
theorem RowG.wp {n : Nat} {σ s : State} (h : RowG bs k n σ s) {c : Prog isa} (hc : NoSp c) (hu : stackUse c ≤ 20)
    {Q : State → Prop} (hw : WP isa c s fun t => Keep (bs σ) s t ∧ Q t) :
    WP isa c s fun t => RowG bs k n σ t ∧ Q t :=
  WP.mono (h.fe.wp hc hu (Q := fun t => Keep (bs σ) s t ∧ Q t) (WP.mono hw fun t ⟨kp, q⟩ =>
    ⟨⟨kp.scr h.fe.fin.scr, kp.ctx h.fe.fin.ctx⟩, kp.regs.1 _ (by decide), kp.regs.2.2, kp, q⟩))
    fun t ⟨fe, kp, q⟩ => ⟨h.keep fe kp, q⟩

/-- Two entry states the comb's runs start from. -/
def CombP (P₀ : State → State → Prop) (bs : State → Addr) : Prop :=
  ∀ σ₁ σ₂, P₀ σ₁ σ₂ → bs σ₁ = bs σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp ∧ σ₁.syms combSym = σ₂.syms combSym

theorem CombP.hp (h : CombP P₀ bs) : ∀ σ₁ σ₂, P₀ σ₁ σ₂ → bs σ₁ = bs σ₂ ∧ σ₁.gpr .esp = σ₂.gpr .esp :=
  fun _ _ hp => ⟨(h _ _ hp).1, (h _ _ hp).2.1⟩

theorem agreeG (hP : CombP P₀ bs) {n : Nat} {s₁ s₂ : State} (h : Runs P₀ (RowG bs k n) s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .esi, .edi]) s₁ s₂ := by
  obtain ⟨σ₁, σ₂, hp, f₁, f₂⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact f₁.fe.sp.trans ((hP _ _ hp).2.1.trans f₂.fe.sp.symm)
  · exact f₁.esi.trans f₂.esi.symm
  · exact edi_eq f₁.fe.fin.scr ((hP _ _ hp).1 ▸ f₂.fe.fin.scr)

/-- After a digit's load: its table's address. -/
def LoadG (bs : State → Addr) (k : State → Nat) (n i : Nat) (σ t : State) : Prop :=
  RowG bs k n σ t ∧ t.gpr .ecx = BitVec.ofNat 32 (mag (nib (k σ) i)) ∧
    t.gpr .ebp = σ.syms combSym + BitVec.ofNat 32 (896 * n) ∧ RowAt (bs σ) n t

theorem agreeL (hP : CombP P₀ bs) {n i : Nat} {s₁ s₂ : State} (h : Runs P₀ (LoadG bs k n i) s₁ s₂) :
    VG.X86.Taint.Agree (τr [.esp, .esi, .edi, .ebp]) s₁ s₂ := by
  obtain ⟨σ₁, σ₂, hp, ⟨f₁, _, b₁, _⟩, ⟨f₂, _, b₂, _⟩⟩ := h
  refine agree_regs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact f₁.fe.sp.trans ((hP _ _ hp).2.1.trans f₂.fe.sp.symm)
  · exact f₁.esi.trans f₂.esi.symm
  · exact edi_eq f₁.fe.fin.scr ((hP _ _ hp).1 ▸ f₂.fe.fin.scr)
  · rw [b₁, b₂, (hP _ _ hp).2.2]

theorem fieldG_rel (hP : CombP P₀ bs) (n : Nat)
    (l : List Impl.X448.X86.Op) (xs : List FieldOp) (hl : l = xs.map FieldOp.impl) :
    RelCT isa (Runs P₀ (RowG bs k n)) (ops l) (Runs P₀ (RowG bs k n)) := by
  rw [hl]
  exact Runs.step (ops_tr hP.hp (fun _ _ h => h.fe.fs) xs) fun σ s h =>
    WP.mono (ops_FE h.fe xs) fun t ⟨fe, kp, _⟩ => h.keep fe kp

/-- A digit's trace, and what it leaves. -/
theorem digitG_rel (hP : CombP P₀ bs) (n : Nat) {o i : Nat} {x y z : Index} (ha : Acc x y z)
    (hoi : (o = 4 ∧ i = 2 * n + 1) ∨ (o = 0 ∧ i = 2 * n)) :
    RelCT isa (Runs P₀ (RowG bs k n)) (digitAdd o x.val y.val z.val) (Runs P₀ (RowG bs k n)) := by
  have ho : 8 * n + o = 4 * i := by omega_using [hoi]
  obtain ⟨_, tl⟩ : ∃ R, RelCT isa (Runs P₀ (RowG bs k n)) (.block (Impl.Ed448.X86.digitLoad o)) R := by
    rcases hoi with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨_, RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => agreeG hP h) (by taint_decide)⟩
    · exact ⟨_, RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => agreeG hP h) (by taint_decide)⟩
  obtain ⟨_, tn⟩ : ∃ R, RelCT isa (Runs P₀ (RowG bs k n)) (.block (Impl.Ed448.X86.negSel o)) R := by
    rcases hoi with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨_, RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => agreeG hP h) (by taint_decide)⟩
    · exact ⟨_, RelCT.taint (A := taint) (τr [.esp, .esi, .edi]) (fun _ _ h => agreeG hP h) (by taint_decide)⟩
  unfold digitAdd
  refine RelCT.seq (Runs.step (G := LoadG bs k n i) tl ?_)
    (RelCT.seq (Runs.step (G := RowG bs k n) (RelCT.taint (A := taint) (τr [.esp, .esi, .edi, .ebp])
      (fun _ _ h => agreeL hP h) (by taint_decide)) ?_)
    (RelCT.seq (fieldG_rel hP n _ _ neg_impl)
      (RelCT.seq (Runs.step (G := RowG bs k n) tn ?_)
      (fieldG_rel hP n _ _ (affFields_impl ha)))))
  · intro σ s h
    have hi : i < 114 := by have := h.lt; omega_using [hoi, this]
    refine WP.mono (h.wp (Q := fun t => t.gpr .ecx = BitVec.ofNat 32 (mag (nib (k σ) i)) ∧
      t.gpr .ebp = σ.syms combSym + BitVec.ofNat 32 (896 * n) ∧ RowAt (bs σ) n t)
      (NoSp.of_all (by rcases hoi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> lit_decide))
      (by rcases hoi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> lit_decide)
      (WP.mono (digitLoad_ok h.fe.fin.scr h.tbl h.lt ho hi h.esi h.bits) fun t ⟨kt, mt, nt, pt, rt⟩ =>
        ⟨⟨kt, by rw [mt]; exact WsOut2.refl _ _ _ _ _ _⟩, nt, pt, rt⟩)) fun t ht => ht
  · rintro σ s ⟨h, nt, _, rt⟩
    refine WP.mono (h.wp (Q := fun _ => True) (NoSp.of_all (by lit_decide)) (by lit_decide)
      (WP.mono (selectT_ok h.fe.fin.scr (mag_lt (nib_lt (k σ) i)) nt rt) fun t ⟨kt, _⟩ => ⟨kt, trivial⟩))
      fun t ht => ht.1
  · intro σ s h
    have hi : i < 114 := by have := h.lt; omega_using [hoi, this]
    refine WP.mono (h.wp (Q := fun _ => True)
      (NoSp.of_all (by rcases hoi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> lit_decide))
      (by rcases hoi with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> lit_decide)
      (WP.mono (negSel_ok h.fe.fin.scr ho hi h.esi h.bits) fun t ⟨kt, _⟩ => ⟨kt, trivial⟩)) fun t ht => ht.1

/-- A step's trace, and what it leaves. -/
theorem combStepG_rel (hP : CombP P₀ bs) (n : Nat) :
    RelCT isa (Runs P₀ (RowG bs k n)) combStep
      (Runs P₀ fun σ t => (n + 1 < 57 → RowG bs k (n + 1) σ t) ∧ CombG bs k σ t ∧ t.zf = some (decide (n + 1 = 57))) := by
  unfold combStep
  refine RelCT.seq (digitG_rel hP n (o := 4) (x := 0) (y := 1) (z := 2) (Or.inl ⟨rfl, rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩))
    (RelCT.seq (digitG_rel hP n (o := 0) (x := 3) (y := 4) (z := 5) (Or.inr ⟨rfl, rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩))
      (Runs.step (RelCT.taint (A := taint) (τr []) (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim)
        (by taint_decide)) ?_))
  intro σ s h
  have e57 : ∀ n < 57, (BitVec.ofNat 32 (n + 1) - (57 : BitVec 32) == 0) = decide (n + 1 = 57) := by decide
  refine WP.mono (h.fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
    (Q := fun t => t.gpr .esi = BitVec.ofNat 32 (n + 1) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.zf = some (decide (n + 1 = 57))) ?_)
    fun t ⟨fe, b, m, rd, z⟩ => ?_
  · refine wp_alu (Or.inl rfl) rfl fun s3 h3 _ => wp_cmp rfl fun t vt hz => WP.block_nil ?_
    have b3 : s3.gpr .esi = BitVec.ofNat 32 (n + 1) := by
      rw [h3.gpr]; change s.gpr .esi + BitVec.ofNat 32 1 = _
      rw [h.esi, add_ofNat]
    have k3 : Keeps [.esi] s t := (h3.rest (by decide)).trans (vt.rest _)
    exact ⟨⟨h.fe.fin.scr.of_keeps k3 (by decide), h.fe.fin.ctx.keep (k3.1 _ (by decide))⟩, k3.1 _ (by decide), k3.2.2,
      by rw [congrFun vt.gpr, b3], by rw [vt.mem, h3.mem], k3.2.1, by rw [hz, b3]; exact congrArg some (e57 n h.lt)⟩
  · have g : CombG bs k σ t := ⟨fe, rd.trans h.rd, by rw [m]; exact h.bits, h.tm⟩
    exact ⟨fun hn => ⟨g, b, hn, by rw [m]; exact h.ptr⟩, g, z⟩

/-- The address of the tables: the frame's word below `esp`, and the store. -/
theorem tblSetupG_rel (hP : CombP P₀ bs) : RelCT isa
    (Runs P₀ fun σ s => CombG bs k σ s ∧ s.syms combSym = σ.syms combSym) tblSetup
    (Runs P₀ fun σ t => CombG bs k σ t ∧ word t.mem (bs σ) TPTR = σ.syms combSym) := by
  have h4 : ∀ {σ s : State}, CombG bs k σ s → 4 ≤ (s.gpr .esp).toNat := fun h => Nat.le_trans (by decide) h.fe.fin.ctx.sp
  refine Runs.step (R := fun _ _ => True) ?_ fun σ s ⟨h, sy⟩ => ?_
  · unfold tblSetup
    have fr : RelCT isa (Runs P₀ fun σ s => CombG bs k σ s ∧ s.syms combSym = σ.syms combSym) (.frame (.symPush .eax combSym) (.block []) (.pop .ecx 1))
        (fun _ _ => True) := by
      rintro s t tr₁ tr₂ s' t' ⟨σ₁, σ₂, hp, ⟨f₁, -⟩, ⟨f₂, -⟩⟩ e₁ e₂
      exact ⟨by rw [symFrame_trace (h4 f₁) e₁, symFrame_trace (h4 f₂) e₂, f₁.fe.sp, f₂.fe.sp, (hP _ _ hp).2.1], trivial⟩
    refine RelCT.seq (Runs.step (G := fun σ t => (t.gpr .edi).setWidth 64 = bs σ) fr fun σ s ⟨h, _⟩ => ?_)
      (RelCT.taint (A := taint) (τr [.edi]) ?_ (by taint_decide))
    · exact WP.mono (symFrame_ok combSym s (h4 h)) fun t ht => by rw [ht.gpr _ (by decide)]; exact h.fe.fin.scr.edi
    · rintro s₁ s₂ ⟨σ₁, σ₂, hp, f₁, f₂⟩
      refine agree_regs fun r hr => ?_
      rw [List.mem_singleton.mp hr]
      exact BitVec.eq_of_toNat_eq (by
        have := congrArg BitVec.toNat (f₁.trans ((hP _ _ hp).1.trans f₂.symm))
        simpa only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide : 2 ^ 32 ≤ 2 ^ 64))] using this)
  · refine WP.mono (h.fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide)
      (Q := fun t => Keeps [.eax, .ecx] s t ∧ word t.mem (bs σ) TPTR = s.syms combSym ∧
        ∀ i < 456, t.mem (off (bs σ) (BITS + i)) = s.mem (off (bs σ) (BITS + i)))
      (WP.mono (tblSetup_ok h.fe.fin.scr h.fe.fin.ctx) fun t ⟨kt, pt, _, _, bt⟩ =>
        ⟨⟨h.fe.fin.scr.of_keeps kt (by decide), h.fe.fin.ctx.keep (kt.1 _ (by decide))⟩, kt.1 _ (by decide), kt.2.2, kt, pt, bt⟩))
      fun t ⟨fe, kt, pt, bt⟩ => ?_
    exact ⟨⟨fe, kt.2.1.trans h.rd, fun i hi => (bt i hi).trans (h.bits i hi), h.tm⟩, pt.trans sy⟩

/-- The trace of the comb's 57 steps. -/
theorem combLoopG_rel (hP : CombP P₀ bs) :
    RelCT isa (Runs P₀ fun σ t => CombG bs k σ t ∧ word t.mem (bs σ) TPTR = σ.syms combSym) combLoop
      (Runs P₀ (CombG bs k)) := by
  unfold combLoop
  refine RelCT.seq (Runs.step (G := RowG bs k 0) (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    (RelCT.loop (M := isa) (fun m => Runs P₀ fun σ s => m < 57 ∧ RowG bs k (56 - m) σ s) (fun m => ?_) 56 |>.mono
      (fun _ _ ⟨σ₁, σ₂, hp, f₁, f₂⟩ => ⟨σ₁, σ₂, hp, ⟨by decide, (Nat.sub_self 56).symm ▸ f₁⟩, ⟨by decide, (Nat.sub_self 56).symm ▸ f₂⟩⟩) fun _ _ h => h)
  · rintro σ s ⟨h, hp⟩
    exact WP.mono (setCounter_ok s 0 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨⟨⟨FInv.of_counter h.fe.fin h2 h3 h4 h5, (h2 _ (by decide)).trans h.fe.sp, h5.trans h.fe.wr,
        by rw [h3]; exact h.fe.frame⟩, h4.trans h.rd, by rw [h3]; exact h.bits, h.tm⟩, h1, by decide, by rw [h3]; exact hp⟩
  · by_cases hm : m < 57
    case neg => exact fun _ _ _ _ _ _ ⟨_, _, _, f, _⟩ => absurd f.1 hm
    refine (combStepG_rel (bs := bs) (k := k) hP (56 - m)).mono
      (fun _ _ ⟨σ₁, σ₂, hp, f₁, f₂⟩ => ⟨σ₁, σ₂, hp, f₁.2, f₂.2⟩) ?_
    rintro t₁ t₂ ⟨σ₁, σ₂, hp, ⟨r₁, g₁, z₁⟩, ⟨r₂, g₂, z₂⟩⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun _ => ⟨σ₁, σ₂, hp, g₁, g₂⟩, fun hz => ?_⟩
    have hn : ¬(56 - m + 1 = 57) := by simpa using hz
    have e : 56 - (m - 1) = 56 - m + 1 := by omega_using [hn, hm]
    exact ⟨m - 1, by omega_using [hn, hm], σ₁, σ₂, hp, ⟨by omega_using [hn, hm], by rw [e]; exact r₁ (by omega_using [hn, hm])⟩,
      ⟨by omega_using [hn, hm], by rw [e]; exact r₂ (by omega_using [hn, hm])⟩⟩

/-- In `double4`, `m + 1` doublings left. -/
def D4 (bs : State → Addr) (m : Nat) (σ s : State) : Prop :=
  FS bs σ s ∧ s.gpr .esi = BitVec.ofNat 32 (m + 1) ∧ m + 1 < 2 ^ 16

theorem double4G_rel (hP : CombP P₀ bs) :
    RelCT isa (Runs P₀ (CombG bs k)) double4 (Runs P₀ (FS bs)) := by
  unfold double4
  refine RelCT.seq (Runs.step (G := D4 bs 3) (RelCT.taint (A := taint) (τr [])
    (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide)) ?_)
    (RelCT.loop (M := isa) (fun m => Runs P₀ (D4 bs m)) (fun m => ?_) 3)
  · intro σ s h
    exact WP.mono (setCounter_ok s 4 (by decide)) fun t ⟨h1, h2, h3, h4, h5⟩ =>
      ⟨⟨FInv.of_counter h.fe.fin h2 h3 h4 h5, (h2 _ (by decide)).trans h.fe.sp⟩, h1, by decide⟩
  refine Runs.then (G := fun σ t => FS bs σ t ∧ t.gpr .esi = BitVec.ofNat 32 m ∧ t.zf = some (decide (m = 0)) ∧
      m < 2 ^ 16) (fun _ _ h => h) (RelCT.seq (R := fun _ _ => True) ?_ (RelCT.taint (A := taint) (τr [])
      (fun _ _ _ => agree_regs fun _ h => (List.not_mem_nil h).elim) (by taint_decide))) ?_ ?_
  · rw [field, doubleFields_impl]
    exact ops_tr hP.hp (fun _ _ h => h.1) doubleFields
  · rintro σ s ⟨f, e, hm⟩
    exact WP.mono (double4Step_ok f.1.scr f.1.ctx (k := m) (by omega_using [hm]) e)
      fun t ⟨et, zt, kt, _⟩ => ⟨⟨⟨f.1.scr.of_keeps kt (by decide), f.1.ctx.keep (kt.1 _ (by decide))⟩,
        (kt.1 _ (by decide)).trans f.2⟩, et, zt, by omega_using [hm]⟩
  · rintro σ₁ σ₂ t₁ t₂ hp - ⟨f₁, e₁, z₁, b₁⟩ ⟨f₂, e₂, z₂, b₂⟩
    rw [eval_ne z₁, eval_ne z₂]
    refine ⟨rfl, fun _ => ⟨σ₁, σ₂, hp, f₁, f₂⟩, fun hz => ?_⟩
    have hk0 : m ≠ 0 := fun h0 => by simp [h0] at hz
    have e : m - 1 + 1 = m := by omega_using [hk0]
    exact ⟨m - 1, by omega_using [hk0], σ₁, σ₂, hp, ⟨f₁, e ▸ e₁, by omega_using [b₁]⟩, ⟨f₂, e ▸ e₂, by omega_using [b₁]⟩⟩

/-- The comb's trace. -/
theorem combBaseG_tr (hP : CombP P₀ bs) :
    RelCT isa (Runs P₀ fun σ s => CombG bs k σ s ∧ s.syms combSym = σ.syms combSym) combBase fun _ _ => True := by
  unfold combBase combFinish
  refine RelCT.seq (tblSetupG_rel hP) (RelCT.seq (combLoopG_rel hP) (RelCT.seq (double4G_rel hP) ?_))
  rw [copyC_impl, addTake_impl]
  refine RelCT.seq (Runs.step (G := FS bs) (ops_tr hP.hp (fun _ _ h => h) copyFields) fun σ s h =>
    WP.mono (ops_ok h.1.scr h.1.ctx copyFields) fun t ⟨kt, _⟩ =>
      ⟨⟨kt.scr h.1.scr, kt.ctx h.1.ctx⟩, (kt.regs.1 _ (by decide)).trans h.2⟩)
    (ops_tr hP.hp (fun _ _ h => h) (addFields ++ takeFields))

end

/-! ## The whole function -/

theorem baseEntry_rel :
    RelCT isa (Runs BP₀ fun σ s => s = σ ∧ BasePre σ)
      baseEntry (Runs BP₀ BMid) := by
  refine Runs.step (RelCT.taint (A := taint) (scalarTaint 2 3) ?_ (by taint_decide))
    fun σ s ⟨e, h⟩ => by subst e; exact entry_stage h
  rintro s₁ s₂ ⟨σ₁, σ₂, hP, ⟨rfl, -⟩, ⟨rfl, -⟩⟩
  exact scalarBase_agree hP.1 hP.2.1 hP.2.2

theorem BP₀.combP : CombP BP₀ bsB := fun _ _ h => ⟨h.hp.1, h.hp.2, h.2.2.2.2.2.2⟩

theorem BMid.combG {σ s : State} (h : BMid σ s) : CombG bsB kB σ s ∧ s.syms combSym = σ.syms combSym :=
  ⟨⟨h.fe, h.rd, h.bits, fun _ fe hr => h.pre.tblMem fe hr⟩, congrFun h.syms _⟩

theorem comb_rel : RelCT isa (Runs BP₀ BMid) combBase (Runs BP₀ BL) :=
  Runs.step ((combBaseG_tr (bs := bsB) (k := kB) BP₀.combP).mono
      (fun _ _ ⟨σ₁, σ₂, hP, m₁, m₂⟩ => ⟨σ₁, σ₂, hP, m₁.combG, m₂.combG⟩) fun _ _ h => h)
    fun _ _ m => comb_stage m

theorem baseEncode_tr : RelCT isa (Runs BP₀ BL) baseEncode fun _ _ => True := by
  unfold baseEncode
  refine RelCT.seq (Runs.step (G := FE bsB)
    (rf_tr (fun _ _ h => h.hp) (fun _ _ h => h.fe.fs) invert_rel) ?_)
    (RelCT.seq (R := Runs BP₀ (FE bsB)) ?_ ?_)
  · intro σ s h
    exact WP.mono (h.fe.wp (NoSp.of_all (by lit_decide)) (by lit_decide) (Q := fun _ => True)
      (WP.mono (invert_ok h.fe.fin.scr h.fe.fin.ctx) fun t ⟨k, _⟩ =>
        ⟨⟨k.scr h.fe.fin.scr, k.ctx h.fe.fin.ctx⟩, k.regs.1 _ (by decide), k.regs.2.2, trivial⟩))
      fun t ⟨fe, _⟩ => fe
  · rw [encodeFields_impl]
    exact Runs.step (ops_tr (fun _ _ h => h.hp) (fun _ _ h => h.fs) encodeFields) fun σ s h =>
      WP.mono (ops_FE h encodeFields) fun t ⟨fe, _⟩ => fe
  · refine RelCT.taint (A := taint) (τa 16) ?_ (by taint_decide)
    rintro s₁ s₂ ⟨σ₁, σ₂, hP, f₁, f₂⟩
    have p₁ := BasePre.of hP.1
    have p₂ := BasePre.of hP.2.1
    have a := scalarBase_agree hP.1 hP.2.1 hP.2.2
    have wr : ∀ {σ : State}, BasePre σ → ∀ r ∈ σ.wr, Region.Disjoint ⟨(σ.gpr .esp).setWidth 64, 16⟩ r := by
      intro σ p r hr
      have := p.sp_fit
      rw [p.wr] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [this]) p.ret_out p.args_out
      · exact VG.X86.Taint.frame_disjoint (n := 12) (by omega_using [this]) p.ret_sc p.args_sc
    have ad : ∀ {σ : State}, BasePre σ → ∀ r ∈ σ.wr ++ [below (σ.gpr .esp) 20],
        (⟨argAddr σ 0, 16 - 4⟩ : Region).Disjoint r := by
      intro σ p r hr
      rw [p.wr, ← stkR_below p.sp_room] at hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact p.args_out
      · exact p.args_sc
      · exact p.stk_args.symm
    exact f₁.agreeA f₂ hP.hp.1 hP.hp.2 (by have := p₁.sp_fit; omega_using [this]) (by have := p₂.sp_fit; omega_using [this])
      (wr p₁) (wr p₂) (ad p₁) (ad p₂) fun k h4 hk => by
        have := a.argMem k h4 hk
        simpa only [scalarTaint, VG.X86.Taint.depth, Nat.zero_add] using this

theorem scalarBase_ct : ConstantTime isa scalarBaseLocal.pre scalarBaseLocal.pub scalarBase := by
  refine RelCT.constantTime (Q := fun _ _ => True)
    ((?_ : RelCT isa (Runs BP₀ fun σ s => s = σ ∧ BasePre σ) scalarBase fun _ _ => True).mono
      (fun s₁ s₂ h => ⟨s₁, s₂, h, ⟨rfl, BasePre.of h.1⟩, ⟨rfl, BasePre.of h.2.1⟩⟩) fun _ _ h => h)
  unfold scalarBase
  exact baseEntry_rel.seq (comb_rel.seq baseEncode_tr)

end VG.Proof.Ed448.X86
