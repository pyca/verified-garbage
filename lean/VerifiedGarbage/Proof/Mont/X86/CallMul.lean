module

public import VerifiedGarbage.Proof.Mont.X86.MulAtVerified
public import VerifiedGarbage.Proof.Mont.X86.OutsZ
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Omega

/-! # Multiplication in the context by a call

`callMul_ok`: `callMul n o a b` (`Impl/Mont/X86/MulAt.lean`) does what
`context_mul_ok` says of the inline multiplication, from a context with 40
bytes of stack below `esp` apart from it (`CallRoom`): it changes only
`eax`, `ecx` and `edx`, the number at `o`, slots 1 and 2, and the 20 bytes
below `esp` (`CallKeep`). -/

@[expose] public section

namespace VG.Proof.Mont.X86.Dynamic

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Mont VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Spec.Rsa.MontMulAt

theorem contextBytes_div' (n : Nat) : 8 * (contextBytes n / 8) = contextBytes n := by
  rw [Nat.mul_comm]; exact contextBytes_div n

theorem mulPre_of {n : Nat} {s : State} (A : MulABI n s) : (mulContract (ctxLayout n) abi 20).pre s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := A
  sig_pre [mulContract, sig, ctxLayout, abi, argSlots, argVal, argBytes, stackBelow]
  sig_and_intros
  all_goals with_reducible assumption

/-- The working space lies below the 40 bytes under `sp`, or at or above `sp`. -/
theorem _root_.VG.Proof.Mont.X86.CallRoom.cases {sp : BitVec 32} {base : Addr} {size : Nat} (R : CallRoom sp base size)
    (hn : base.toNat + size ≤ 2 ^ 32) (hs : 0 < size) :
    base.toNat + size ≤ sp.toNat - 40 ∨ sp.toNat ≤ base.toNat := by
  have h40 := R.low
  have hsp := sp.isLt
  have e40 : ((sp - BitVec.ofNat 32 40).setWidth 64).toNat = sp.toNat - 40 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  by_contra hc
  simp only [not_or, Nat.not_le] at hc
  generalize hz : (sp - BitVec.ofNat 32 40).setWidth 64 = z at e40
  have ap := R.apart
  simp only [below, hz] at ap
  by_cases hb : base.toNat ≤ sp.toNat - 40
  · refine ap z ?_ ?_
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    · simp only [Region.Contains]; bv_omega
  · refine ap base ?_ ?_
    · simp only [Region.Contains]; bv_omega
    · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

/-- What a call writing `[o]` keeps: the registers but `eax`, `ecx` and `edx`,
the regions, and the memory but `[o]`, slots 1 and 2 and the 20 bytes below
`esp`. -/
structure CallKeep (n : Nat) (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : OutsZ base (s.gpr .esp) [(o, 8 * n), (slot n 1, 2 * stride n)] s.mem s'.mem

theorem CallKeep.keeps {n : Nat} {base : Addr} {o : Nat} {s s' : State} (K : CallKeep n base o s s') :
    Keeps [.eax, .ecx, .edx] s s' := ⟨K.gpr, K.rd, K.wr⟩

theorem CallKeep.esp {n : Nat} {base : Addr} {o : Nat} {s s' : State} (K : CallKeep n base o s s') :
    s'.gpr .esp = s.gpr .esp := K.gpr _ (by decide)

/-- The slots but `o` and the multiplication's keep their numbers. -/
theorem CallKeep.slot_val {n m size o i : Nat} {base : Addr} {s t : State} (h : Context n m base size s)
    (R : CallRoom (s.gpr .esp) base size) (K : CallKeep n base (slot n o) s t) (hi : i < 9) (hio : i ≠ o)
    (hi1 : i ≠ 1) (hi2 : i ≠ 2) : wordsVal t.mem base (slot n i) n = wordsVal s.mem base (slot n i) n := by
  have := slot_sep (n := n) hio; have := slot_sep (n := n) hi1; have := slot_sep (n := n) hi2
  have bi := slot_bound (n := n) hi
  have s12 : slot n 2 = slot n 1 + stride n := by unfold slot stride; omega
  have eS : stride n = 16 * n + 8 := rfl
  have sz := h.size_le
  refine K.mem.wordsVal R h.scr.nowrap (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> dsimp only <;> omega

theorem mulAtBody_noSp (n : Nat) : NoSp (mulAtBody n) := by
  apply NoSp.of_all
  rw [Code.allInstrs_eq]
  simp only [mulAtBody, mulAt, instrs, List.all_append]
  rfl

theorem mulAtBody_stackUse (n : Nat) : stackUse (mulAtBody n) = 0 := rfl

/-- The callee's state: the frame of the arguments pushed from `s`, the
return address pushed, and the regions narrowed to the arguments and the
context. -/
abbrev calleeState (n : Nat) (base : Addr) (s : State) : State :=
  ((pushed [Reg.eax, .ecx, .edx, .edi] s).callEntry).withRegions [below (s.gpr .esp) 16]
    [⟨base, contextBytes n⟩]

/-- What a call writing slot `o` from slots `a` and `b` needs: a context
with room for the call below `esp`, slots it may take, and `[b]` reduced. -/
structure MulReady (n m : Nat) (base : Addr) (size o a b : Nat) (s : State) : Prop where
  ctx : Context n m base size s
  room : CallRoom (s.gpr .esp) base size
  ho : o < 9
  ha : a < 9
  hb : b < 9
  ho0 : o ≠ 0
  ho1 : o ≠ 1
  ho2 : o ≠ 2
  ha1 : a ≠ 1
  ha2 : a ≠ 2
  hb1 : b ≠ 1
  hb2 : b ≠ 2
  bLt : wordsVal s.mem base (slot n b) n < m

/-- What the call's frame needs: `MulReady`, with the offsets of slots `o`,
`a` and `b` in `edx`, `ecx` and `eax`. -/
structure CallReady (n m : Nat) (base : Addr) (size o a b : Nat) (s : State) : Prop
    extends MulReady n m base size o a b s where
  eax : s.gpr .eax = BitVec.ofNat 32 (slot n b)
  ecx : s.gpr .ecx = BitVec.ofNat 32 (slot n a)
  edx : s.gpr .edx = BitVec.ofNat 32 (slot n o)

section
variable {n m size o a b : Nat} {base : Addr} {s : State} (C : CallReady n m base size o a b s)
include C

theorem CallReady.fit : 4 * [Reg.eax, .ecx, .edx, .edi].length + 4 ≤ (s.gpr .esp).toNat := by
  have := C.room.low; simp only [List.length_cons, List.length_nil]; omega

/-- The callee's arguments and precondition, and the stack the call writes. -/
theorem CallReady.callee :
    MulABI n (calleeState n base s) ∧ wsOf (calleeState n base s) = base ∧
      (arg (calleeState n base s) 1).toNat = slot n o ∧ (arg (calleeState n base s) 2).toNat = slot n a ∧
      (arg (calleeState n base s) 3).toNat = slot n b ∧
      Frame [below (s.gpr .esp) 20] s.mem (calleeState n base s).mem := by
  have h := C.ctx
  have R := C.room
  have sz := h.size_le
  have nw := h.scr.nowrap
  have h40 := R.low
  have hspN := (s.gpr .esp).isLt
  have eS : stride n = 16 * n + 8 := rfl
  have s12 : slot n 2 = slot n 1 + stride n := by unfold slot stride; omega
  have s0 : slot n 0 = 64 := by unfold slot; omega
  have bo := slot_bound (n := n) C.ho; have ba := slot_bound (n := n) C.ha
  have bb := slot_bound (n := n) C.hb
  have ho' := slot_header n o
  have so1 := slot_sep (n := n) C.ho1; have so2 := slot_sep (n := n) C.ho2
  have so0 := slot_sep (n := n) C.ho0
  have sa1 := slot_sep (n := n) C.ha1; have sa2 := slot_sep (n := n) C.ha2
  have sb1 := slot_sep (n := n) C.hb1; have sb2 := slot_sep (n := n) C.hb2
  have cases := R.cases nw (by omega)
  have bN := h.scr.edi_toNat
  have hfit := C.fit
  generalize ht : calleeState n base s = t
  have targ : ∀ i (hi : i < 4), arg t i = s.gpr ([Reg.eax, .ecx, .edx, .edi][3 - i]'(by simp; omega)) :=
    fun i hi => by rw [← ht]; exact callEntry_arg hfit (by decide) (by simpa using hi)
  have hlt : ∀ i, i < 9 → (BitVec.ofNat 32 (slot n i)).toNat = slot n i := fun i hi => by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; have := slot_bound (n := n) hi; omega
  have a0 : arg t 0 = s.gpr .edi := targ 0 (by decide)
  have a1 : (arg t 1).toNat = slot n o := by
    rw [targ 1 (by decide)]; show (s.gpr .edx).toNat = _; rw [C.edx, hlt o C.ho]
  have a2 : (arg t 2).toNat = slot n a := by
    rw [targ 2 (by decide)]; show (s.gpr .ecx).toNat = _; rw [C.ecx, hlt a C.ha]
  have a3 : (arg t 3).toNat = slot n b := by
    rw [targ 3 (by decide)]; show (s.gpr .eax).toNat = _; rw [C.eax, hlt b C.hb]
  have hws : wsOf t = base := by show (arg t 0).setWidth 64 = base; rw [a0]; exact h.scr.edi
  have hwsN : (arg t 0).toNat = base.toNat := by rw [a0]; exact bN
  have espT : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 20 := by
    rw [← ht]; show ((pushed _ s).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat hfit]; rfl
  have argA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [← ht]; exact callEntry_argAddr0 _ _
  have argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 16 := by
    rw [argA, BitVec.toNat_setWidth, sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
    rw [BitVec.toNat_setWidth, espT]; exact Nat.mod_eq_of_lt (by omega)
  have lowN : ((t.gpr .esp).setWidth 64 - 20#64).toNat = (s.gpr .esp).toNat - 40 := by
    rw [BitVec.toNat_sub, retN]; simp only [BitVec.toNat_ofNat]; omega
  have fr : Frame [below (s.gpr .esp) 20] s.mem t.mem := by
    rw [← ht]; exact callEntry_frame hfit (rs := [Reg.eax, .ecx, .edx, .edi]) (by decide)
  have Z : OutsZ base (s.gpr .esp) [] s.mem t.mem :=
    fun x _ hz => fr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hz
  have vt : ∀ d, d + 8 * n ≤ size → wordsVal t.mem base d n = wordsVal s.mem base d n :=
    fun d hd => Z.wordsVal R nw (fun r hr => absurd hr List.not_mem_nil) hd
  have trd : t.rd = [below (s.gpr .esp) 16] := by rw [← ht]; rfl
  have twr : t.wr = [⟨base, contextBytes n⟩] := by rw [← ht]; rfl
  refine ⟨⟨by rw [espT]; omega, by rw [espT]; omega,
      by rw [trd, argA],
      by rw [twr, hws, contextBytes_div],
      Region.disjoint_of_le (by simp only; rw [argN, hws, contextBytes_div]; omega)
        (by simp only; rw [hws, contextBytes_div]; omega) (by simp only; rw [argN]; omega),
      Region.disjoint_of_le (by simp only; rw [retN, hws, contextBytes_div]; omega)
        (by simp only; rw [retN]; omega) (by simp only; rw [hws, contextBytes_div]; omega),
      Region.disjoint_of_le (by simp only; rw [retN, argN]; omega) (by simp only; rw [retN]; omega)
        (by simp only; rw [argN]; omega),
      Region.disjoint_of_le (by simp only; rw [lowN, hws, contextBytes_div]; omega)
        (by simp only; rw [lowN]; omega) (by simp only; rw [hws, contextBytes_div]; omega),
      Region.disjoint_of_le (by simp only; rw [lowN, argN]; omega) (by simp only; rw [lowN]; omega)
        (by simp only; rw [argN]; omega),
      by rw [hwsN, contextBytes_div]; omega,
      by rw [a1, contextBytes_div']; omega,
      by rw [a2, contextBytes_div']; omega,
      by rw [a3, contextBytes_div']; omega,
      by rw [a1]; unfold Apart; dsimp only; omega,
      by rw [a2]; unfold Apart; dsimp only; omega,
      by rw [a3]; unfold Apart; dsimp only; omega,
      by rw [a1]; unfold Apart; dsimp only; omega,
      by rw [a1]; unfold Apart; dsimp only; omega, ?_, ?_⟩, hws, a1, a2, a3, fr⟩
  · rw [numAt_eq8, numAt_eq4, hws, vt _ (by omega)]
    have := h.inverse
    rw [← h.modulus.val] at this
    rwa [show w32 t.mem base 0 = w32 s.mem base 0 from Z.w32 R nw (fun r hr => absurd hr List.not_mem_nil)
      (by omega)]
  · rw [numAt_eq8, numAt_eq8, hws, a3, vt _ (by omega), vt _ (by omega)]
    have := h.modulus.val
    change wordsVal s.mem base (slot n 0) n = m at this
    rw [this]; exact C.bLt

theorem CallReady.wsCov : Covers [(⟨base, contextBytes n⟩ : Region)] s.wr :=
  Covers.of_sub fun r hr => ⟨_, C.ctx.scr.wr, 0, by rw [List.mem_singleton.mp hr, BitVec.add_zero],
    by rw [List.mem_singleton.mp hr]; dsimp only; have := C.ctx.size_le; omega⟩

/-- The callee's precondition, with its regions narrowed and covered. -/
theorem CallReady.pre :
    CallPre (mulContract (ctxLayout n) abi 20) [.eax, .ecx, .edx, .edi] [below (s.gpr .esp) 16]
      [⟨base, contextBytes n⟩] s := by
  refine ⟨mulPre_of C.callee.1, ?_, ?_⟩
  · refine Covers.append_left (Covers.of_mem fun r hr => ?_) ?_
    · rw [List.mem_singleton.mp hr]; simp
    · exact (C.wsCov.trans (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)).right
  · exact C.wsCov.trans (Covers.of_mem fun r hr => List.mem_cons_of_mem _ hr)

end

/-- The call in its frame of arguments. -/
theorem callFrame_ok {n m size o a b : Nat} {base : Addr} {s : State} (hn : 2 ≤ n)
    (C : CallReady n m base size o a b s) :
    WP isa (.frame (.push [.eax, .ecx, .edx, .edi]) (.call (mulAtName n) (mulAtBody n)) (.pop .eax 4)) s
      fun t => Context n m base size t ∧ CallKeep n base (slot n o) s t ∧
        wordsVal t.mem base (slot n o) n < m ∧
        wordsVal t.mem base (slot n o) n * 2 ^ (64 * n) % m =
          wordsVal s.mem base (slot n a) n * wordsVal s.mem base (slot n b) n % m := by
  have h := C.ctx
  have R := C.room
  have sz := h.size_le
  have nw := h.scr.nowrap
  have bo := slot_bound (n := n) C.ho; have ba := slot_bound (n := n) C.ha
  have bb := slot_bound (n := n) C.hb
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have eS : stride n = 16 * n + 8 := rfl
  have s12 : slot n 2 = slot n 1 + stride n := by unfold slot stride; omega
  have ho' := slot_header n o
  obtain ⟨_, hws, a1, a2, a3, fr⟩ := C.callee
  have Z : OutsZ base (s.gpr .esp) [] s.mem (calleeState n base s).mem :=
    fun x _ hz => fr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hz
  have vt : ∀ d, d + 8 * n ≤ size → wordsVal (calleeState n base s).mem base d n = wordsVal s.mem base d n :=
    fun d hd => Z.wordsVal R nw (fun r hr => absurd hr List.not_mem_nil) hd
  refine WP.callWith (k := mulContract (ctxLayout n) abi 20) (fun u hu => mulAt_correct hn u hu)
    (mulAtBody_noSp n) (by decide) (by decide) (by rw [mulAtBody_stackUse]; exact C.fit) C.pre ?_
  intro s' rd' wr' cs' F ⟨s₂, m₂, post⟩
  change (mulContract (ctxLayout n) abi 20).post (calleeState n base s) s₂ at post
  generalize ht : calleeState n base s = t at hws a1 a2 a3 vt post
  sig_post [mulContract, sig, ctxLayout, abi, argSlots, argVal, argBytes] at post
  obtain ⟨L₂, C₂, K₂⟩ := post
  rw [m₂] at L₂ C₂ K₂
  have hws' : (arg t 0).setWidth 64 = base := hws
  simp only [numAt_eq8, hws', a1, a2, a3] at L₂ C₂ K₂
  have mv : wordsVal t.mem base (slot n 0) n = m := by rw [vt _ (by omega)]; exact h.modulus.val
  rw [mv, vt _ (by omega), vt _ (by omega)] at C₂
  rw [mv] at L₂
  have gK : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s'.gpr r = s.gpr r := fun r hr => by
    refine cs' r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    revert h1 h2 h3; cases r <;> decide
  have O : OutsZ base (s.gpr .esp) [(slot n o, 8 * n), (slot n 1, 2 * stride n)] s.mem s'.mem := by
    intro x hx hz
    by_cases hin : ofs base x < contextBytes n
    · have ex : x = base + BitVec.ofNat 64 (ofs base x) := by
        simp only [ofs, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rw [BitVec.add_comm, BitVec.sub_add_cancel]
      rw [ex]
      rw [K₂ _ (by rw [contextBytes_div']; exact hin) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hx _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
        · exact hx _ (List.mem_cons_self ..)), ← ex, ← ht]
      exact fr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hz
    · rw [F x fun r hr => ?_]
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | rfl
      · simp only [Region.Contains, ofs] at hin ⊢; omega
      · rw [mulAtBody_stackUse]; exact hz
  have K : CallKeep n base (slot n o) s s' := ⟨gK, rd', wr', O⟩
  have hsep : ∀ i, i < 9 → i ≠ o → i ≠ 1 → i ≠ 2 → ∀ r ∈ [(slot n o, 8 * n), (slot n 1, 2 * stride n)],
      slot n i + 8 * n ≤ r.1 ∨ r.1 + r.2 ≤ slot n i := by
    intro i hi hio hi1 hi2 r hr
    have := slot_sep (n := n) hio; have := slot_sep (n := n) hi1; have := slot_sep (n := n) hi2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega
  refine ⟨⟨h.scr.of_eq (gK _ (by decide)) (gK _ (by decide)) wr', sz,
    ⟨h.modulus.n0, h.modulus.mo, h.modulus.tmp, h.modulus.sep, ?_⟩, h.gt_one, ?_⟩, K, L₂, C₂⟩
  · change wordsVal s'.mem base (slot n 0) n = m
    rw [O.wordsVal R nw (hsep 0 (by decide) (Ne.symm C.ho0) (by decide) (by decide)) (by omega)]
    exact h.modulus.val
  · have h1 := slot_header n 1
    rw [O.w32 R nw (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only <;> omega) (by omega)]
    exact h.inverse

/-- The three offsets into `edx`, `ecx` and `eax`. -/
theorem callArgs_ok {n : Nat} (o a b : Nat) {s : State} :
    WP isa (.block [.mov .eax (.imm (BitVec.ofNat 32 (slot n b))), .mov .ecx (.imm (BitVec.ofNat 32 (slot n a))),
      .mov .edx (.imm (BitVec.ofNat 32 (slot n o)))]) s fun t =>
      Keeps [.eax, .ecx, .edx] s t ∧ t.mem = s.mem ∧ t.gpr .eax = BitVec.ofNat 32 (slot n b) ∧
        t.gpr .ecx = BitVec.ofNat 32 (slot n a) ∧ t.gpr .edx = BitVec.ofNat 32 (slot n o) := by
  refine wp_movS rfl fun s₁ u₁ _ => wp_movS rfl fun s₂ u₂ _ => wp_movS rfl fun s₃ u₃ _ =>
    WP.block_nil ⟨?_, by rw [u₃.mem, u₂.mem, u₁.mem], by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr],
      by rw [u₃.other _ (by decide), u₂.gpr], u₃.gpr⟩
  refine ⟨fun r hr => ?_, by rw [u₃.rd, u₂.rd, u₁.rd], by rw [u₃.wr, u₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]

/-- `MulReady` once the offsets are in registers. -/
theorem MulReady.args {n m size o a b : Nat} {base : Addr} {s u : State} (M : MulReady n m base size o a b s)
    (K : Keeps [.eax, .ecx, .edx] s u) (hm : u.mem = s.mem) (eax : u.gpr .eax = BitVec.ofNat 32 (slot n b))
    (ecx : u.gpr .ecx = BitVec.ofNat 32 (slot n a)) (edx : u.gpr .edx = BitVec.ofNat 32 (slot n o)) :
    CallReady n m base size o a b u :=
  { ctx := M.ctx.outside_keep K (by decide) (by decide) (by rw [hm]; exact Outside.refl _ 4 0 _)
      (.inr (by have := slot_header n 0; omega)) (Nat.le_refl _)
    room := (K.1 _ (by decide) : u.gpr .esp = s.gpr .esp) ▸ M.room
    ho := M.ho, ha := M.ha, hb := M.hb, ho0 := M.ho0, ho1 := M.ho1, ho2 := M.ho2, ha1 := M.ha1,
    ha2 := M.ha2, hb1 := M.hb1, hb2 := M.hb2, bLt := by rw [hm]; exact M.bLt, eax, ecx, edx }

/-- `[o] = [a] [b] R⁻¹ mod m` by a call. -/
theorem callMul_ok {n size m o a b : Nat} {base : Addr} {s : State} (hn : 2 ≤ n)
    (h : Context n m base size s) (R : CallRoom (s.gpr .esp) base size)
    (ho : o < 9) (ha : a < 9) (hb : b < 9) (ho0 : o ≠ 0) (ho1 : o ≠ 1) (ho2 : o ≠ 2)
    (hB : wordsVal s.mem base (slot n b) n < m)
    (ha1 : a ≠ 1 := by decide) (ha2 : a ≠ 2 := by decide) (hb1 : b ≠ 1 := by decide)
    (hb2 : b ≠ 2 := by decide) :
    WP isa (callMul n (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base size t ∧ CallKeep n base (slot n o) s t ∧
      wordsVal t.mem base (slot n o) n < m ∧
      wordsVal t.mem base (slot n o) n * 2 ^ (64 * n) % m =
        wordsVal s.mem base (slot n a) n * wordsVal s.mem base (slot n b) n % m := by
  unfold callMul
  refine WP.seq (WP.mono (callArgs_ok (n := n) o a b) fun s₃ ⟨K₃, m₃, eax, ecx, edx⟩ => ?_)
  have esp₃ : s₃.gpr .esp = s.gpr .esp := K₃.1 _ (by decide)
  have C : CallReady n m base size o a b s₃ :=
    MulReady.args ⟨h, R, ho, ha, hb, ho0, ho1, ho2, ha1, ha2, hb1, hb2, hB⟩ K₃ m₃ eax ecx edx
  refine WP.mono (callFrame_ok hn C) fun t ⟨Ct, Kt, Lt, Vt⟩ => ⟨Ct, ?_, Lt, by rw [Vt, m₃]⟩
  refine ⟨fun r hr => (Kt.gpr r hr).trans (K₃.1 r hr), Kt.rd.trans K₃.2.1, Kt.wr.trans K₃.2.2, ?_⟩
  rw [← m₃, ← esp₃]
  exact Kt.mem

end VG.Proof.Mont.X86.Dynamic
