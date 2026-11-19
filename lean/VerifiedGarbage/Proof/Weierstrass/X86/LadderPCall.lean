module

public import VerifiedGarbage.Proof.Weierstrass.Point0Contract
public import VerifiedGarbage.Proof.Weierstrass.Env
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
public import VerifiedGarbage.Impl.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Mont.X86.Chain
public import VerifiedGarbage.Proof.Weierstrass.X86.MontCall
public import VerifiedGarbage.Impl.Weierstrass.X86.Point
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! ### `Weierstrass.X86.PointCall`, which this module and modules that import it used -/

section

/-!
# Calls of the Montgomery functions from a point function, on x86 (32-bit)

`callB enc f body o a b` (`Impl/Weierstrass/X86/Point.lean`) is `callOp`:
it pushes the working space at `edi` and the offsets `enc o`, `enc a` and
`enc b` as the arguments of the function `f`, whose code is `body`, and calls
it (`callB_ok`). As `callOp_ok` (`MontCall.lean`), from the point function's
view of its state (`ScrP`: `edi` and its argument the working space's base,
the working space writable, the stack the call uses apart from it), the call
changes only `eax`, `ecx` and `edx`, the number at `o`, the functions' own working space and memory
outside the working space, but none of it outside the working space and the
20 bytes below `esp` (`CallKeepB`), and does what `body` does.
`mulCallB_ok`, `addCallB_ok` and `subCallB_ok` are the calls of `mulFn`,
`addFn` and `subFn`.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Impl.Weierstrass.X86.Point
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass.X86.Mont

/-- The point function's argument is the working space's base `base`,
readable; the working space is writable, below `2³²`; and the stack a call
uses is apart from it. -/
structure ArgP (s : State) (base : Addr) : Prop where
  ws : (arg s 0).setWidth 64 = base
  rd : (⟨argAddr s 0, 4⟩ : Region) ∈ s.rd
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 32
  stk : StkOk (s.gpr .esp) base 8192
  sp_fit : (s.gpr .esp).toNat + 8 ≤ 2 ^ 32
  args_ws : Region.Disjoint ⟨argAddr s 0, 4⟩ ⟨base, 8192⟩

/-- The point function's view of the state after its entry: also `edi` is
the working space's base. -/
structure ScrP (s : State) (base : Addr) : Prop extends ArgP s base where
  edi : (s.gpr .edi).setWidth 64 = base

theorem ArgP.arg_toNat {s : State} {base : Addr} (hs : ArgP s base) : (arg s 0).toNat = base.toNat := by
  rw [← hs.ws, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (arg s 0).isLt
    (Nat.pow_le_pow_right (by decide) (by decide)))]

/-- The argument's address. -/
theorem argAddr0_eq (s : State) : addr (s.gpr .esp) 4 = argAddr s 0 := rfl

/-- What a call writing `[o]` keeps: the registers but `eax`, `ecx` and
`edx`, the regions, the memory but `callW`, and the memory outside the
working space and the 20 bytes below `esp`. -/
structure CallKeepB (k : Nat) (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outs base (callW k o) s.mem s'.mem
  fr : Frame [⟨base, 8192⟩, below (s.gpr .esp) 20] s.mem s'.mem

theorem argAddr0_toNat (s : State) (h : (s.gpr .esp).toNat + 8 ≤ 2 ^ 32) :
    (argAddr s 0).toNat = (s.gpr .esp).toNat + 4 := by
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega_arith

theorem below_toNat (sp : BitVec 32) {n : Nat} (h : n ≤ sp.toNat) : (below sp n).base.toNat = sp.toNat - n := by
  show ((sp - BitVec.ofNat 32 n).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, sub_toNat h]; omega_arith

/-- The argument is apart from the 20 bytes below `esp`. -/
theorem args_below {s : State} (h20 : 20 ≤ (s.gpr .esp).toNat) (h : (s.gpr .esp).toNat + 8 ≤ 2 ^ 32) :
    Region.Disjoint ⟨argAddr s 0, 4⟩ (below (s.gpr .esp) 20) :=
  Region.disjoint_of_le (.inr (by
    show (below (s.gpr .esp) 20).base.toNat + 20 ≤ (argAddr s 0).toNat
    rw [below_toNat _ h20, argAddr0_toNat s h]; omega_arith))
    (by show (argAddr s 0).toNat + 4 ≤ _; rw [argAddr0_toNat s h]; omega_arith)
    (by show (below (s.gpr .esp) 20).base.toNat + 20 ≤ _; rw [below_toNat _ h20]; omega_arith)

/-- The argument survives a change of memory within the working space and
the stack below `esp`. -/
theorem ScrP.keep {s s' : State} {base : Addr} (hs : ScrP s base) (hsp : s'.gpr .esp = s.gpr .esp)
    (hedi : s'.gpr .edi = s.gpr .edi)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨base, 8192⟩, below (s.gpr .esp) 20] s.mem s'.mem) : ScrP s' base := by
  obtain e : argAddr s' 0 = argAddr s 0 := by simp only [argAddr, hsp]
  obtain harg : arg s' 0 = arg s 0 := by
    simp only [arg, e]
    refine hf.readW (r := ⟨argAddr s 0, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.args_ws
    · exact args_below hs.stk.1 hs.sp_fit
  exact ⟨⟨by rw [harg]; exact hs.ws, by rw [hrd, e]; exact hs.rd, by rw [hwr]; exact hs.wr, hs.nowrap,
    by rw [hsp]; exact hs.stk, by rw [hsp]; exact hs.sp_fit, by rw [e]; exact hs.args_ws⟩, by rw [hedi]; exact hs.edi⟩

/-- A call of `body`, which from the working space `ws` and the offsets
`enc o`, `enc a` and `enc b` as its arguments changes only `[enc o]` and its
own working space, preserves the callee-saved registers, and relates the
memory before and after by `V`. -/
theorem callB_ok {enc : Nat → Nat} {f : String} {body : Prog isa} (hsp : NoSp body) (hst : stackUse body = 0)
    {k : Nat} (hk0 : 0 < k) (hk9 : k ≤ 9) {s : State} {base : Addr} (hs : ScrP s base) {o a b : Nat}
    (ho : enc o + 8 * k ≤ own k) (ha : enc a + 8 * k ≤ own k) (hb : enc b + 8 * k ≤ own k)
    {V : Mem → Mem → Prop}
    (hbody : ∀ t, Pre k t → wsOf t = base → (arg t 1).toNat = enc o → (arg t 2).toNat = enc a →
      (arg t 3).toNat = enc b → Frame [below (s.gpr .esp) 20] s.mem t.mem →
      WP isa body t fun t' => abiPreserved t t' ∧ Outs base (outs k t) t.mem t'.mem ∧ V t.mem t'.mem) :
    WP isa (callB enc f body o a b) s fun s' => CallKeepB k base (enc o) s s' ∧
      ∃ m m', Frame [below (s.gpr .esp) 20] s.mem m ∧ V m m' ∧ Frame [below (s.gpr .esp) 20] m' s'.mem := by
  obtain hown := (saveAt_le hk0 hk9).2
  have hn := hs.nowrap
  obtain ⟨h20, hz⟩ := hs.stk
  obtain hspN := (s.gpr .esp).isLt
  rw [callB, callOp]
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_movS rfl fun s₂ u₂ _ => wp_movS rfl fun s₃ u₃ _ =>
    WP.block_nil ?_)
  obtain g : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
  obtain m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  obtain rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  obtain esp₃ : s₃.gpr .esp = s.gpr .esp := g _ (by decide)
  obtain edi₃ : s₃.gpr .edi = s.gpr .edi := g _ (by decide)
  obtain eax₃ : s₃.gpr .eax = BitVec.ofNat 32 (enc b) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  obtain ecx₃ : s₃.gpr .ecx = BitVec.ofNat 32 (enc a) := by rw [u₃.other _ (by decide), u₂.gpr]
  have edx₃ : s₃.gpr .edx = BitVec.ofNat 32 (enc o) := u₃.gpr
  obtain hfit : 4 * [Reg.eax, .ecx, .edx, .edi].length + 4 ≤ (s₃.gpr .esp).toNat := by
    rw [esp₃]; simp only [List.length_cons, List.length_nil]; omega_arith
  -- The callee's view.
  let t := ((pushed [Reg.eax, .ecx, .edx, .edi] s₃).callEntry).withRegions
    [below (s₃.gpr .esp) 16] [⟨base, 8192⟩]
  obtain targ : ∀ i (hi : i < 4), arg t i = s₃.gpr ([Reg.eax, .ecx, .edx, .edi][3 - i]'(by simp; omega_arith)) :=
    fun i hi => callEntry_arg hfit (by decide) (by simpa using hi)
  obtain a0 : arg t 0 = s.gpr .edi := by rw [targ 0 (by decide)]; exact edi₃
  obtain hlt : ∀ x, x < 4096 → (BitVec.ofNat 32 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; omega_arith
  obtain a1 : (arg t 1).toNat = enc o := by
    rw [targ 1 (by decide)]; show (s₃.gpr .edx).toNat = enc o; rw [edx₃, hlt _ (by omega_arith)]
  obtain a2 : (arg t 2).toNat = enc a := by
    rw [targ 2 (by decide)]; show (s₃.gpr .ecx).toNat = enc a; rw [ecx₃, hlt _ (by omega_arith)]
  obtain a3 : (arg t 3).toNat = enc b := by
    rw [targ 3 (by decide)]; show (s₃.gpr .eax).toNat = enc b; rw [eax₃, hlt _ (by omega_arith)]
  obtain hws : wsOf t = base := by show (arg t 0).setWidth 64 = base; rw [a0]; exact hs.edi
  obtain hwsN : (arg t 0).toNat = base.toNat := by
    rw [a0, ← hs.edi, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .edi).isLt
      (Nat.pow_le_pow_right (by decide) (by decide)))]
  obtain espT : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 20 := by
    show ((pushed _ s₃).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat hfit, esp₃]; rfl
  obtain argA : argAddr t 0 = (s₃.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := callEntry_argAddr0 _ _
  obtain argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 16 := by
    rw [argA, esp₃, BitVec.toNat_setWidth, sub_toNat (by omega_arith)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  obtain retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
    rw [BitVec.toNat_setWidth, espT]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain fr : Frame [below (s.gpr .esp) 20] s.mem t.mem := by
    have := callEntry_frame hfit (rs := [Reg.eax, .ecx, .edx, .edi]) (by decide)
    rw [m₃, esp₃] at this
    exact this
  obtain hpre : Pre k t := by
    obtain hwsT : (wsOf t).toNat = base.toNat := by rw [hws]
    refine ⟨by show [below (s₃.gpr .esp) 16] = [(⟨argAddr t 0, 16⟩ : Region)]; rw [argA],
      by show [(⟨base, 8192⟩ : Region)] = _; rw [hws], by rw [hwsN]; exact hn, by rw [espT]; omega_arith,
      Region.disjoint_of_le (by simp only; rw [argN, hwsT]; omega_arith) (by simp only; rw [argN]; omega_arith)
        (by simp only; rw [hwsT]; omega_arith),
      Region.disjoint_of_le (by simp only; rw [retN, hwsT]; omega_arith) (by simp only; rw [retN]; omega_arith)
        (by simp only; rw [hwsT]; omega_arith),
      hk0, hk9, by rw [a1]; exact ho, by rw [a2]; exact ha, by rw [a3]; exact hb⟩
  let K : Contract isa :=
    { pre := fun u => Pre k u ∧ wsOf u = base ∧ (arg u 1).toNat = enc o ∧ (arg u 2).toNat = enc a ∧
        (arg u 3).toNat = enc b ∧ Frame [below (s.gpr .esp) 20] s.mem u.mem
      post := fun u u' => Outs base (outs k u) u.mem u'.mem ∧ V u.mem u'.mem
      pub := fun _ _ => True }
  refine WP.callWith (k := K) (fun u ⟨h1, h2, h3, h4, h5, h6⟩ => by
      obtain ⟨tr, u', he, A, O, W⟩ := hbody u h1 h2 h3 h4 h5 h6
      exact ⟨tr, u', he, A, O, W⟩) hsp (by decide) (by decide)
    (by rw [hst]; exact hfit) (rd := [below (s₃.gpr .esp) 16]) (wr := [⟨base, 8192⟩])
    ⟨⟨hpre, hws, a1, a2, a3, fr⟩, ?_, ?_⟩ ?_
  · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; simp
    · rw [List.mem_singleton.mp hr, wr₃]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr, wr₃]; exact List.mem_cons_of_mem _ hs.wr
  intro s' rd' wr' cs' F' ⟨s₂, m₂, O₂, V₂⟩
  rw [hst, esp₃] at F'
  obtain m₂ : Frame [below (s.gpr .esp) 20] s₂.mem s'.mem := by
    rw [esp₃] at m₂; exact Frame.below_mono (wr := []) m₂ (by decide) h20
  refine ⟨⟨fun r hr => ?_, by rw [rd', rd₃], by rw [wr', wr₃], fun x hx => ?_, ?_⟩, t.mem, s₂.mem, fr, V₂, m₂⟩
  · rw [← g r hr]
    refine cs' r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
    revert h1 h2 h3; cases r <;> decide
  · by_cases hzx : (below (s.gpr .esp) 20).Contains x 1
    · have h1 : 8192 ≤ ofs base x := by
        have hn' := hs.nowrap
        simp only [Region.Contains] at hzx
        simp only [ofs]
        obtain e : ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
          rw [BitVec.toNat_setWidth, sub_toNat h20]
          exact Nat.mod_eq_of_lt (by omega_arith)
        generalize ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64) = z at hzx e
        bv_omega_arith
      obtain h2 := hx outW (by simp)
      obtain h3 : ofs base x < 2 ^ 64 := (x - base).isLt
      simp only at h2
      omega_arith
    · rw [m₂ x (fun r hr => by rw [List.mem_singleton.mp hr]; exact hzx), O₂ x fun r hr => ?_]
      · exact fr x fun r hr => by rw [List.mem_singleton.mp hr]; exact hzx
      simp only [outs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [a1]; exact hx _ (List.mem_cons_self ..)
      · exact hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · rw [← m₃]
    refine F'.mono fun r hr => ?_
    simp only [List.mem_append, List.mem_singleton] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with rfl | rfl
    · exact .inl rfl
    · exact .inr rfl

/-- The stack a call uses is past the working space. -/
theorem zone_ofsP {s : State} {base : Addr} (hs : ScrP s base) {x : Addr}
    (hx : (below (s.gpr .esp) 20).Contains x 1) : 8192 ≤ ofs base x := by
  obtain ⟨h20, hz⟩ := hs.stk
  have hn := hs.nowrap
  obtain hsp := (s.gpr .esp).isLt
  simp only [Region.Contains] at hx
  simp only [ofs]
  obtain e : ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
    rw [BitVec.toNat_setWidth, sub_toNat h20]
    exact Nat.mod_eq_of_lt (by omega_arith)
  generalize ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64) = z at hx e
  bv_omega_arith

/-- Memory that changed only in the stack a call uses keeps the working space. -/
theorem frame_val32P {s : State} {base : Addr} (hs : ScrP s base) {m m' : Mem}
    (hF : Frame [below (s.gpr .esp) 20] m m') {d n : Nat} (h : d + 4 * n ≤ 8192) :
    val32 m' base d n = val32 m base d n := by
  have hn := hs.nowrap
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => hF _ fun r hr hc => ?_)
  rw [List.mem_singleton.mp hr] at hc
  have := zone_ofsP hs hc
  rw [ofs_off base (by omega_arith)] at this
  omega_arith

section
variable {enc : Nat → Nat} {S : Impl.Weierstrass.Mont.Modulus} (hF : FnOk S) {s : State} {base : Addr}
  (hs : ScrP s base) {o a b : Nat}
  (ho : enc o + 8 * S.k ≤ own S.k) (ha : enc a + 8 * S.k ≤ own S.k) (hb : enc b + 8 * S.k ≤ own S.k)
include hF hs ho ha hb

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulCallB_ok (hB : wordsVal s.mem base (enc b) S.k < S.m) :
    WP isa (callB enc (S.fn "mul") (mulFn S.k S.m) o a b) s fun s' => CallKeepB S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k < S.m ∧
      wordsVal s'.mem base (enc o) S.k * 2 ^ (64 * S.k) % S.m =
        wordsVal s.mem base (enc a) S.k * wordsVal s.mem base (enc b) S.k % S.m := by
  obtain hown := (saveAt_le hF.mul.k0 hF.k9).2
  refine WP.mono (callB_ok hF.nsMul (by
    unfold mulFn mulBody
    split <;> [rfl; (split <;> rfl)]) hF.mul.k0 hF.k9 hs ho ha hb
    (V := fun m m' => val32 m' base (enc o) (2 * S.k) < S.m ∧
      val32 m' base (enc o) (2 * S.k) * 2 ^ (64 * S.k) % S.m =
        val32 m base (enc a) (2 * S.k) * val32 m base (enc b) (2 * S.k) % S.m)
    fun t hp hws h1 h2 h3 hfr => ?_) fun s' ⟨K, m, m', hm, ⟨V₁, V₂⟩, hm'⟩ => ?_
  · refine WP.mono (mulFn_ok hF.mul hp (by
      rw [hws, h3, frame_val32P hs hfr (by omega_arith), ← wordsVal_eq_val32]; exact hB))
      fun t' ⟨A, O, L, C⟩ => ⟨A, hws ▸ O, ?_⟩
    rw [hws, h1] at L
    rw [hws, h1, h2, h3] at C
    exact ⟨L, C⟩
  · rw [frame_val32P hs hm (by omega_arith), frame_val32P hs hm (by omega_arith),
      ← frame_val32P hs hm' (by omega_arith)] at V₂
    rw [← frame_val32P hs hm' (by omega_arith)] at V₁
    refine ⟨K, ?_, ?_⟩
    · rw [wordsVal_eq_val32]; exact V₁
    · rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32]; exact V₂

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
theorem addCallB_ok (hAB : wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k < 2 * S.m) :
    WP isa (callB enc (S.fn "add") (addFn S.k S.m) o a b) s fun s' => CallKeepB S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k =
        (wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k) % S.m := by
  obtain hown := (saveAt_le hF.mul.k0 hF.k9).2
  refine WP.mono (callB_ok hF.nsAdd rfl hF.mul.k0 hF.k9 hs ho ha hb
    (V := fun m m' => val32 m' base (enc o) (2 * S.k) =
      (val32 m base (enc a) (2 * S.k) + val32 m base (enc b) (2 * S.k)) % S.m)
    fun t hp hws h1 h2 h3 hfr => ?_) fun s' ⟨K, m, m', hm, V, hm'⟩ => ?_
  · refine WP.mono (addFn_ok hF.mul hp (by
      rw [hws, h2, h3, frame_val32P hs hfr (by omega_arith), frame_val32P hs hfr (by omega_arith), ← wordsVal_eq_val32,
        ← wordsVal_eq_val32]; exact hAB))
      fun t' ⟨A, O, L⟩ => ⟨A, hws ▸ O, ?_⟩
    rw [hws, h1, h2, h3] at L
    exact L
  · rw [frame_val32P hs hm (by omega_arith), frame_val32P hs hm (by omega_arith),
      ← frame_val32P hs hm' (by omega_arith)] at V
    refine ⟨K, ?_⟩
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32]; exact V

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
theorem subCallB_ok (hA : wordsVal s.mem base (enc a) S.k < S.m) (hB : wordsVal s.mem base (enc b) S.k < S.m) :
    WP isa (callB enc (S.fn "sub") (subFn S.k S.m) o a b) s fun s' => CallKeepB S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k =
        (wordsVal s.mem base (enc a) S.k + S.m - wordsVal s.mem base (enc b) S.k) % S.m := by
  obtain hown := (saveAt_le hF.mul.k0 hF.k9).2
  refine WP.mono (callB_ok hF.nsSub rfl hF.mul.k0 hF.k9 hs ho ha hb
    (V := fun m m' => val32 m' base (enc o) (2 * S.k) =
      (val32 m base (enc a) (2 * S.k) + S.m - val32 m base (enc b) (2 * S.k)) % S.m)
    fun t hp hws h1 h2 h3 hfr => ?_) fun s' ⟨K, m, m', hm, V, hm'⟩ => ?_
  · refine WP.mono (subFn_ok hF.mul hp
      (by rw [hws, h2, frame_val32P hs hfr (by omega_arith), ← wordsVal_eq_val32]; exact hA)
      (by rw [hws, h3, frame_val32P hs hfr (by omega_arith), ← wordsVal_eq_val32]; exact hB))
      fun t' ⟨A, O, L⟩ => ⟨A, hws ▸ O, ?_⟩
    rw [hws, h1, h2, h3] at L
    exact L
  · rw [frame_val32P hs hm (by omega_arith), frame_val32P hs hm (by omega_arith),
      ← frame_val32P hs hm' (by omega_arith)] at V
    refine ⟨K, ?_⟩
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32]; exact V

end

end VG.Proof.Weierstrass.X86.Point

end

end

/-! ### `Weierstrass.X86.PointFn`, which only this module used -/

section

/-! ### `Weierstrass.X86.PointFprog`, which only this module used -/

section

/-!
# Field programs on slots at offsets known at run time, on x86 (32-bit)

`fprogB σ S ops` (`Impl/Weierstrass/X86/Point.lean`) runs the field
operations `ops`, on slots named by number, each slot `x` at the offset
`σ x`, by calls of the functions of the modulus `S`. As on 32-bit ARM
(`Proof/Weierstrass/Arm/PointFprog.lean`), what the slots stand for (`toM`)
follows `runOps ops` (`fprogB_ok`), and only the slots the program writes
(`W`) must be apart from every other (`LayR`). `opsB_ok` runs a formula on
the function's slots (`OpsOk`), such as the complete addition
(`rcbIds_opsOk`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Point
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Mont

/-- The slots `x < N` at offsets `σ x` of numbers of `k` words: below the
functions' own working space, and each of `W` apart from every other. -/
structure LayR (k N : Nat) (W : List Nat) (σ : Nat → Nat) : Prop where
  le : ∀ x < N, σ x + 8 * k ≤ own k
  apart : ∀ w ∈ W, ∀ x < N, x ≠ w → σ x + 8 * k ≤ σ w ∨ σ w + 8 * k ≤ σ x

/-- The state holds the environment `E` in Montgomery's form in the slots `V`
(below `N`), below `m`, in the point function's view (`ScrP`). -/
structure InvR (k N : Nat) (σ : Nat → Nat) (base : Addr) (m : Nat) [NeZero m]
    (V : List Nat) (E : Nat → Fin m) (s : State) : Prop where
  scr : ScrP s base
  ids : ∀ x ∈ V, x < N
  lt : ∀ x ∈ V, wordsVal s.mem base (σ x) k < m
  val : ∀ x ∈ V, toM m (2 ^ (64 * k)) (wordsVal s.mem base (σ x) k) = E x

/-- What a program writing the slots `W` keeps: the registers but `eax`,
`ecx` and `edx`, the regions, the memory but the slots `W`, the
functions' own working space and memory outside the working space, and
the memory outside the working space and the 20 bytes below `esp`. -/
structure KeepR (k : Nat) (σ : Nat → Nat) (base : Addr) (W : List Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outs base (W.map (fun w => (σ w, 8 * k)) ++ [(own k, 64 * k), outW]) s.mem s'.mem
  fr : Frame [⟨base, 8192⟩, below (s.gpr .esp) 20] s.mem s'.mem

theorem KeepR.refl (k : Nat) (σ : Nat → Nat) (base : Addr) (W : List Nat) (s : State) : KeepR k σ base W s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Outs.refl _ _ _, Frame.refl _ _⟩

theorem KeepR.trans {k : Nat} {σ : Nat → Nat} {base : Addr} {W : List Nat} {s₁ s₂ s₃ : State}
    (h₁ : KeepR k σ base W s₁ s₂) (h₂ : KeepR k σ base W s₂ s₃) : KeepR k σ base W s₁ s₃ :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.mem.trans h₂.mem,
    h₁.fr.trans (by rw [← h₁.gpr .esp (by decide)]; exact h₂.fr)⟩

theorem KeepR.mono {k : Nat} {σ : Nat → Nat} {base : Addr} {W W' : List Nat} {s s' : State}
    (h : KeepR k σ base W s s') (hW : ∀ w ∈ W, w ∈ W') : KeepR k σ base W' s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono fun r hr => by
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with ⟨w, hw, rfl⟩ | hr
    · exact .inl ⟨w, hW w hw, rfl⟩
    · exact .inr hr, h.fr⟩

/-- A call's frame, as a program's. -/
theorem KeepR.of_call {k : Nat} {σ : Nat → Nat} {base : Addr} {o : Nat} {s s' : State}
    (h : CallKeepB k base (σ o) s s') : KeepR k σ base [o] s s' :=
  ⟨h.gpr, h.rd, h.wr, h.mem.mono (by
    intro r hr
    simp only [callW, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rcases hr with rfl | rfl | rfl <;> simp), h.fr⟩

/-- An operation writing `o`, which then holds `v`, keeps the invariant. -/
theorem InvR.update {k N : Nat} {σ : Nat → Nat} {base : Addr} {m : Nat} [NeZero m]
    {W : List Nat} (hL : LayR k N W σ) {V : List Nat} {E : Nat → Fin m} {s s' : State}
    (hI : InvR k N σ base m V E s) {o : Nat} (hoW : o ∈ W) (hoN : o < N) (hk : KeepR k σ base [o] s s')
    (hr : wordsVal s'.mem base (σ o) k < m) {v : Fin m}
    (hv : toM m (2 ^ (64 * k)) (wordsVal s'.mem base (σ o) k) = v) :
    InvR k N σ base m (o :: V) (Function.update E o v) s' := by
  have hn := hI.scr.nowrap
  obtain heq : ∀ x ∈ V, x ≠ o → wordsVal s'.mem base (σ x) k = wordsVal s.mem base (σ x) k := by
    intro x hx hxo
    obtain hxN := hI.ids x hx
    obtain h1 := hL.le x hxN
    obtain h2 := hL.apart o hoW x hxN hxo
    obtain hown : own k ≤ 4096 := Nat.sub_le _ _
    refine Outs.wordsVal hk.mem (fun r hr => ?_) (by omega_using [h1, hown])
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h2
    · exact .inl h1
    · exact .inl (show σ x + 8 * k ≤ 8192 by omega_using [h1, hown])
  refine ⟨hI.scr.keep (hk.gpr .esp (by decide)) (hk.gpr .edi (by decide)) hk.rd hk.wr hk.fr, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hoN
    · exact hI.ids x hx
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; exact hr
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo]; exact hI.lt x hx'
  · intro x hx
    by_cases hxo : x = o
    · subst hxo; rw [Function.update_self]; exact hv
    · have hx' := List.mem_of_ne_of_mem hxo hx
      rw [heq x hx' hxo, Function.update_of_ne hxo]
      exact hI.val x hx'

/-- One operation. -/
theorem fopB_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hF : FnOk S) (hk : S.k = k) {W : List Nat} (hL : LayR k N W σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) {V : List Nat} {E : Nat → Fin S.m} {s : State}
    (hI : InvR k N σ base S.m V E s) {op : FOp} (hW : op.out ∈ W) (hN : ∀ x ∈ op.out :: op.ins, x < N)
    (hR : ∀ x ∈ op.ins, x ∈ V) :
    WP isa (opCodeB σ S op) s fun s' =>
      KeepR k σ base [op.out] s s' ∧ InvR k N σ base S.m (op.out :: V) (op.run E) s' := by
  subst hk
  cases op with
  | mul o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    refine WP.mono (mulCallB_ok (enc := σ) hF hI.scr (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2)
        (hI.lt b hR.2))
      fun s' ⟨K, hlt, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) hlt ?_⟩
    rw [toM_mul hm heq, hI.val a hR.1, hI.val b hR.2]
  | add o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    obtain hA := hI.lt a hR.1
    obtain hB := hI.lt b hR.2
    refine WP.mono (addCallB_ok (enc := σ) hF hI.scr (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2)
        (by omega_using [hA, hB]))
      fun s' ⟨K, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_add, hI.val a hR.1, hI.val b hR.2]
  | sub o a b =>
    simp only [FOp.out, FOp.ins, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hW hN hR
    obtain hA := hI.lt a hR.1
    obtain hB := hI.lt b hR.2
    refine WP.mono (subCallB_ok (enc := σ) hF hI.scr (hL.le o hN.1) (hL.le a hN.2.1) (hL.le b hN.2.2)
        hA hB)
      fun s' ⟨K, heq⟩ => ?_
    refine ⟨.of_call K, hI.update hL hW hN.1 (.of_call K) ?_ ?_⟩
    · rw [heq]; exact Nat.mod_lt _ (by omega_using [hA])
    · rw [heq, toM_sub (by omega_using [hB]), hI.val a hR.1, hI.val b hR.2]

/-- A field program. -/
theorem fprogB_ok {k N : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hF : FnOk S) (hk : S.k = k) {W : List Nat} (hL : LayR k N W σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) :
    ∀ (ops : List FOp) {V : List Nat} {E : Nat → Fin S.m} {s : State},
      InvR k N σ base S.m V E s → (∀ op ∈ ops, op.out ∈ W ∧ ∀ x ∈ op.out :: op.ins, x < N) →
      readsOk ops V = true →
      WP isa (fprogB σ S ops) s fun s' => KeepR k σ base (ops.map FOp.out) s s' ∧
        InvR k N σ base S.m (validAfter ops V) (runOps ops E) s'
  | [], _, _, s, hI, _, _ => WP.block_nil ⟨KeepR.refl _ _ _ _ s, hI⟩
  | op :: ops, V, E, s, hI, hS, hR => by
    simp only [readsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hR
    obtain hop := hS op (List.mem_cons_self ..)
    refine progs_wp _ _ (WP.mono (fopB_ok hF hk hL hm hI hop.1 hop.2 hR.1) fun s₁ ⟨k₁, I₁⟩ => ?_)
    refine WP.mono (fprogB_ok hF hk hL hm ops I₁ (fun op' h => hS op' (List.mem_cons_of_mem _ h)) hR.2)
      fun s₂ ⟨k₂, I₂⟩ => ⟨(k₁.mono fun w hw => ?_).trans (k₂.mono fun w hw => ?_), I₂⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      simp [hw]
    · simp [hw]

/-! ## The complete addition -/

/-- The slots the function's addition writes: the result's and the
temporaries. -/
def wIds : List Nat := [0, 1, 2, 11, 12, 13, 14, 15, 16]

/-- The slots it reads first: `p`, `q`, `a` and `3b`. -/
def rIds : List Nat := [3, 4, 5, 6, 7, 8, 9, 10]

/-- A formula on the function's slots: it writes only `wIds`, names only
slots below 17, reads only `rIds` or what it wrote, and writes the
result's three slots. -/
structure OpsOk (ops : List FOp) : Prop where
  slots : ∀ op ∈ ops, op.out ∈ wIds ∧ ∀ x ∈ op.out :: op.ins, x < 17
  reads : readsOk ops rIds = true
  outs : ∀ j < 3, j ∈ validAfter ops rIds

/-- A formula on the slots numbered as the function numbers them, from a
state holding `E` in the slots it reads. -/
theorem opsB_ok {k : Nat} {σ : Nat → Nat} {base : Addr} {S : Impl.Weierstrass.Mont.Modulus}
    [NeZero S.m] (hF : FnOk S) (hk : S.k = k) (hL : LayR k 17 wIds σ)
    (hm : UnitMod S.m (2 ^ (64 * k))) {ops : List FOp} (hO : OpsOk ops)
    {E : Nat → Fin S.m} {s : State} (hI : InvR k 17 σ base S.m rIds E s) :
    WP isa (fprogB σ S ops) s fun s' => KeepR k σ base wIds s s' ∧
      InvR k 17 σ base S.m (validAfter ops rIds) (runOps ops E) s' := by
  refine WP.mono (fprogB_ok hF hk hL hm _ hI hO.slots hO.reads) fun s' ⟨hk', hI'⟩ =>
    ⟨hk'.mono fun w hw => ?_, hI'⟩
  obtain ⟨op, hop, rfl⟩ := List.mem_map.mp hw
  exact (hO.slots op hop).1

theorem rcbIds_ok : ∀ op ∈ rcb sId pId qId oId, op.out ∈ wIds ∧ ∀ x ∈ op.out :: op.ins, x < 17 := by
  decide

theorem rcbIds_reads : readsOk (rcb sId pId qId oId) rIds = true := by decide

theorem rcbIds_apart : RcbApart sId pId qId oId := ⟨by decide, by decide⟩

/-! ## The formulas for `a = 0` -/

theorem dbl0_opsOk : OpsOk (dbl0 sId pId oId) := ⟨by decide, by decide, by decide⟩

theorem rcb0m_opsOk : OpsOk (rcb0m sId pId qId oId) := ⟨by decide, by decide, by decide⟩

theorem rcbIds_opsOk : OpsOk (rcb sId pId qId oId) := ⟨rcbIds_ok, rcbIds_reads, by decide⟩

theorem ops0_opsOk (dbl : Bool) : OpsOk (ops0 dbl) := by
  cases dbl
  · exact rcb0m_opsOk
  · exact dbl0_opsOk

/-- What the formulas compute on the slots. -/
theorem ops0_run {m : Nat} [NeZero m] (E : Nat → Fin m) (dbl : Bool) :
    (runOps (ops0 dbl) E 0, runOps (ops0 dbl) E 1, runOps (ops0 dbl) E 2) =
      if dbl then Impl.Weierstrass.Point.rcbDbl0 (E 10) (E 3) (E 4) (E 5)
      else Impl.Weierstrass.Point.rcbAdd0m (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) := by
  cases dbl <;> rfl

end VG.Proof.Weierstrass.X86.Point

end

end


/-!
# Complete point addition and doubling as functions, on x86 (32-bit): correctness

`fnOps S dbl ops` (`Impl/Weierstrass/X86/Point.lean`), for field operations
`ops` that write only the result and the temporaries (`OpsOk`), from a
state that its
precondition describes (`PrePt`: the working space the argument, writable,
the arguments, the return address and the stack its calls use apart from
it, and every coordinate it reads below the prime), returns with the
callee-saved registers and the return address kept, the working space
changed only at `O` and in the own working space, and `O`'s coordinates
below the prime, standing for what `ops` computes from what the constants
and the operands stand for (`fnOps_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Point
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86.Mont

/-- The numbers of the layout, for `omega`. -/
theorem lay_nums {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) :
    Impl.Weierstrass.Point.ownAt k + 64 + 6 * Impl.Weierstrass.Point.elemBytes k = own k ∧ own k + 64 * k = 4096 ∧ Impl.Weierstrass.Point.elemBytes k = 8 * k ∧
    Impl.Weierstrass.Point.b3At k + Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.ownAt k ∧ Impl.Weierstrass.Point.aAt k + Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.b3At k ∧
    Impl.Weierstrass.Point.qAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.aAt k ∧ Impl.Weierstrass.Point.pAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.qAt k ∧
    Impl.Weierstrass.Point.oAt k + 3 * Impl.Weierstrass.Point.elemBytes k = Impl.Weierstrass.Point.pAt k ∧ 1000 ≤ Impl.Weierstrass.Point.oAt k := by
  unfold Impl.Weierstrass.Point.oAt Impl.Weierstrass.Point.pAt Impl.Weierstrass.Point.qAt Impl.Weierstrass.Point.aAt Impl.Weierstrass.Point.b3At Impl.Weierstrass.Point.ownAt Impl.Weierstrass.Point.elemBytes own Impl.Weierstrass.Mont.ownAt
    Impl.Weierstrass.Mont.ownBytes
  omega

/-- The slots the function reads first lie below its own working space. -/
theorem enc_rIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ x ∈ rIds, enc k dbl x + 8 * k ≤ Impl.Weierstrass.Point.ownAt k := by
  have := lay_nums hk3 hk6
  intro x hx
  simp only [rIds, List.mem_cons, List.not_mem_nil, or_false] at hx
  cases dbl <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Bool.false_eq_true] <;> omega_using [this]

/-- The outputs of a point function lie in the working space. -/
theorem enc_out {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) {j : Nat} (hj : j < 3) :
    enc k dbl j + 8 * k ≤ 8192 := by
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega_using [hj]
  all_goals obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> decide

/-- The slots `enc` gives are laid out as the program needs, and those it
writes lie apart from the saved `lr` and within `O` or the own working
space. -/
theorem enc_lay {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) : LayR k 17 wIds (enc k dbl) := by
  obtain rfl | rfl | rfl | rfl : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega_using [hk3, hk6]
  all_goals cases dbl <;> exact ⟨by decide, by decide⟩

theorem enc_wIds {k : Nat} (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) :
    ∀ w ∈ wIds, (enc k dbl w + 8 * k ≤ Impl.Weierstrass.Point.ownAt k ∨ Impl.Weierstrass.Point.ownAt k + 4 ≤ enc k dbl w) ∧
      ((Impl.Weierstrass.Point.oAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ Impl.Weierstrass.Point.pAt k) ∨
        (Impl.Weierstrass.Point.ownAt k ≤ enc k dbl w ∧ enc k dbl w + 8 * k ≤ 4096)) := by
  have := lay_nums hk3 hk6
  intro w hw
  simp only [wIds, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [enc, Impl.Weierstrass.X86.Point.tmpAt, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte, Nat.reduceSub, Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega_using [this]

/-- Changes within ranges are within any ranges that contain them. -/
theorem outs_sub {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m')
    (hs : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' :=
  fun x hx => h x fun r hr => by
    obtain ⟨r', hr', h1, h2⟩ := hs r hr
    have := hx r' hr'
    omega_using [h1, h2, this]

/-- A 32-bit word apart from the ranges. -/
theorem outs_readW32 {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (h : Outs base W m m')
    {d : Nat} (hd : ∀ w ∈ W, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  (Mem.readW_congr fun i hi => (h _ fun w hw' => by
    rw [ofs_off base (by omega_using [hd', hi])]; have := hd w hw'; omega_using [hi, this]).symm).symm

/-- The precondition of the function, on the state: the working space its
argument, writable, apart from the argument, the return address and the
stack its calls use, and the numbers it reads below `m`. -/
structure PrePt (k m : Nat) (dbl : Bool) (s : State) : Prop where
  scr : ArgP s (wsOf s)
  ret_ws : Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ ⟨wsOf s, 8192⟩
  k3 : 3 ≤ k
  k6 : k ≤ 6
  lt : ∀ x ∈ rIds, wordsVal s.mem (wsOf s) (enc k dbl x) k < m

/-- `[ws + d]`, through a register holding the argument. -/
theorem addr_ws {s : State} {base : Addr} (hs : ArgP s base) {d : Nat} (hd : d < 8192) :
    addr (arg s 0) d = off base d := by
  rw [addr_eq (by have := hs.arg_toNat; have := hs.nowrap; omega_arith), hs.ws]

/-- The environment of the entry: what the numbers of the slots stand for. -/
def E₀ (k m : Nat) [NeZero m] (dbl : Bool) (s : State) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal s.mem (wsOf s) (enc k dbl x) k)

theorem rIds_lt : ∀ x ∈ rIds, x < 17 := by decide

/-- A function of field operations `ops` reading `rs` (`OpsOk`): the
callee-saved registers and the return address kept, the working space
changed only at `O` and in the own working space, and `O`'s coordinates
below the prime, standing for what `ops` computes from what the slots
stand for. -/
theorem fnOps_ok {S : Impl.Weierstrass.Mont.Modulus} [NeZero S.m] (hF : FnOk S) (hodd : S.m % 2 = 1)
    {dbl : Bool} {ops : List FOp} (hO : OpsOk ops) {s : State} (hp : PrePt S.k S.m dbl s) :
    WP isa (Impl.Weierstrass.X86.Point.fnOps S dbl ops) s fun s' => abiPreserved s s' ∧
      Outs (wsOf s) [(Impl.Weierstrass.Point.oAt S.k, 3 * Impl.Weierstrass.Point.elemBytes S.k),
        (Impl.Weierstrass.Point.ownAt S.k, 4096 - Impl.Weierstrass.Point.ownAt S.k), outW] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem (wsOf s) (enc S.k dbl j) S.k < S.m) ∧
      (toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (wsOf s) (enc S.k dbl 0) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (wsOf s) (enc S.k dbl 1) S.k),
        toM S.m (2 ^ (64 * S.k)) (wordsVal s'.mem (wsOf s) (enc S.k dbl 2) S.k)) =
        (runOps ops (E₀ S.k S.m dbl s) 0, runOps ops (E₀ S.k S.m dbl s) 1,
          runOps ops (E₀ S.k S.m dbl s) 2) := by
  obtain hl := lay_nums hp.k3 hp.k6
  obtain hR := enc_rIds hp.k3 hp.k6 dbl
  obtain hW := enc_wIds hp.k3 hp.k6 dbl
  have hs := hp.scr
  have hn := hs.nowrap
  obtain hsv : Impl.Weierstrass.X86.Point.saveAt S.k + 4 < 8192 := by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith
  rw [Impl.Weierstrass.X86.Point.fnOps]
  -- `edi` saved, and `edi = ws`.
  refine WP.seq (wp_ldm (b := .esp) rfl ⟨_, List.mem_append_left _ hs.rd, by
      rw [argAddr0_eq]; exact Region.contains_self _ _⟩ fun s₀ u₀ => ?_)
  rw [argAddr0_eq] at u₀
  have eax₀ : s₀.gpr .eax = arg s 0 := u₀.gpr
  refine wp_stm (b := .eax) eax₀ ⟨_, by rw [u₀.wr]; exact hs.wr, by
      rw [addr_ws hs (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun s₁ u₁ =>
    wp_mov fun s₂ u₂ => WP.block_nil ?_
  rw [addr_ws hs (by omega_arith)] at u₁
  obtain m₁ : s₂.mem = s.mem.writeW (off (wsOf s) (Impl.Weierstrass.X86.Point.saveAt S.k)) (s.gpr .edi) := by
    rw [u₂.mem, u₁.mem, u₀.mem, u₀.other _ (by decide)]
  obtain g₁ : ∀ r, r ≠ .eax → r ≠ .edi → s₂.gpr r = s.gpr r := fun r h h' => by
    rw [u₂.other _ h', u₁.gpr, u₀.other _ h]
  obtain edi₂ : s₂.gpr .edi = arg s 0 := by rw [u₂.gpr, u₁.gpr, eax₀]
  obtain O₁ : Outside (wsOf s) (Impl.Weierstrass.X86.Point.saveAt S.k) 4 s.mem s₂.mem := by
    rw [m₁]; exact writeW32_outside _ _ _ (by omega_arith)
  obtain F₁ : Frame [⟨wsOf s, 8192⟩, below (s.gpr .esp) 20] s.mem s₂.mem := by
    rw [m₁]
    exact (Frame.refl _ _).writeW (List.mem_cons_self ..) _ (Offset.contains_base _ (by omega_arith) (by omega_arith))
  obtain esp₂ : s₂.gpr .esp = s.gpr .esp := g₁ _ (by decide) (by decide)
  obtain hs₁ : ScrP s₂ (wsOf s) := by
    obtain e : argAddr s₂ 0 = argAddr s 0 := by simp only [argAddr, esp₂]
    obtain harg : arg s₂ 0 = arg s 0 := by
      simp only [arg, e]
      refine F₁.readW (r := ⟨argAddr s 0, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hs.args_ws
      · exact args_below hs.stk.1 hs.sp_fit
    exact ⟨⟨by rw [harg], by rw [u₂.rd, u₁.rd, u₀.rd, e]; exact hs.rd,
      by rw [u₂.wr, u₁.wr, u₀.wr]; exact hs.wr, hs.nowrap, by rw [esp₂]; exact hs.stk,
      by rw [esp₂]; exact hs.sp_fit, by rw [e]; exact hs.args_ws⟩, by rw [edi₂]⟩
  obtain hI : InvR S.k 17 (enc S.k dbl) (wsOf s) S.m rIds (E₀ S.k S.m dbl s) s₂ := by
    obtain heq : ∀ x ∈ rIds, wordsVal s₂.mem (wsOf s) (enc S.k dbl x) S.k =
        wordsVal s.mem (wsOf s) (enc S.k dbl x) S.k := fun x hx =>
      Outs.wordsVal (Outs.of_outside O₁ (List.mem_singleton_self _)) (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr
        exact .inl (by have := hR x hx; simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith))
        (by have := hR x hx; omega_arith)
    exact ⟨hs₁, rIds_lt, fun x hx => by rw [heq x hx]; exact hp.lt x hx,
      fun x hx => by rw [heq x hx]; rfl⟩
  refine WP.seq (WP.mono (opsB_ok hF rfl (enc_lay hp.k3 hp.k6 dbl) (unitMod_pow_two hodd _) hO hI)
    fun s₃ ⟨K, I₂⟩ => ?_)
  -- `edi` restored.
  have hs₂ := I₂.scr
  obtain edi₃ : s₃.gpr .edi = arg s 0 := by
    apply BitVec.eq_of_toNat_eq
    obtain h1 := congrArg BitVec.toNat hs₂.edi
    have h2 := hs.arg_toNat
    obtain b1 := (s₃.gpr .edi).isLt
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)] at h1
    omega_arith
  refine wp_ldm (b := .edi) edi₃ ⟨_, List.mem_append_right _ hs₂.wr, by
      rw [addr_ws hs (by omega_arith)]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)⟩ fun s₄ u₄ =>
    WP.block_nil ?_
  rw [addr_ws hs (by omega_arith)] at u₄
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  -- The saved word survives the program.
  obtain hsaved : s₃.mem.readW (off (wsOf s) (Impl.Weierstrass.X86.Point.saveAt S.k)) 32 = s.gpr .edi := by
    obtain h := outs_readW32 K.mem (d := Impl.Weierstrass.X86.Point.saveAt S.k) (fun r hr => by
      simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl
      · rcases (hW x hx).1 with h | h <;> [exact .inr (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith);
          exact .inl (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith)]
      · exact .inl (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith)
      · exact .inl (by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith)) (by omega_arith)
    rw [h, m₁, Mem.readW_writeW_self32]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, fun j hj => ?_, ?_⟩
  · -- The callee-saved registers.
    by_cases hb : r = .edi
    · subst hb
      rw [u₄.gpr, hsaved]
    · have hr' : r ∉ [Reg.eax, .ecx, .edx] := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₄.other _ hb, K.gpr r hr', g₁ r (by simp_all) hb]
  · -- The return address.
    rw [m₄]
    refine (F₁.trans (by rw [← esp₂]; exact K.fr)).readW (r := ⟨(s.gpr .esp).setWidth 64, 4⟩)
      (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.ret_ws
    · have h20 := hs.stk.1
      have hsp := hs.sp_fit
      exact Region.disjoint_of_le (.inr (by
        show (below (s.gpr .esp) 20).base.toNat + 20 ≤ ((s.gpr .esp).setWidth 64).toNat
        rw [below_toNat _ h20, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]; omega_arith))
        (by show ((s.gpr .esp).setWidth 64).toNat + 4 ≤ _; rw [BitVec.toNat_setWidth]; omega_arith)
        (by show (below (s.gpr .esp) 20).base.toNat + 20 ≤ _; rw [below_toNat _ h20]; omega_arith)
  · -- The memory.
    rw [m₄]
    refine (outs_sub (rs := [(Impl.Weierstrass.X86.Point.saveAt S.k, 4)]) (Outs.of_outside O₁ (List.mem_singleton_self _)) fun r hr => ?_).trans
      (outs_sub K.mem fun r hr => ?_)
    · rw [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith,
        by simp only [Impl.Weierstrass.X86.Point.saveAt]; omega_arith⟩
    · simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with ⟨x, hx, rfl⟩ | rfl | rfl
      · rcases (hW x hx).2 with h | h
        · exact ⟨_, List.mem_cons_self, h.1, by dsimp only; omega_arith⟩
        · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.1, by dsimp only; omega_arith⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by dsimp only; omega_arith, by dsimp only; omega_arith⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), Nat.le_refl _, Nat.le_refl _⟩
  · rw [m₄]; exact I₂.lt j (hO.outs j hj)
  · rw [m₄, I₂.val 0 (hO.outs 0 (by decide)), I₂.val 1 (hO.outs 1 (by decide)),
      I₂.val 2 (hO.outs 2 (by decide))]

end VG.Proof.Weierstrass.X86.Point

end

end


/-!
# The ladder by calls of the point functions, on x86 (32-bit): copies and calls

`copyPt n o a` copies the point at `a` to `o` (`copyPt_ok`), and
`ptCall S dbl arg` calls `vg_<curve>_point_double` or `vg_<curve>_point_add`
on the working space at `edi`, then loads `edi` again from the caller's
argument holding it (`ptCall_ok`): it changes only `eax`, `ecx` and `edx`,
`O`, the point functions' own working space and the 28 bytes of stack below
`esp`, and `O` then holds `rcbAdd` of what `a`, `3b`, `P` and `Q` (or `P`)
stood for (`ptVal`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86.Point

open VG VG.X86 VG.X86.Wp VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86.Mont
open VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass.X86.Point
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86
  VG.Proof.Weierstrass.X86.Mont

theorem copyPt_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n : Nat} {o a : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, a.x, a.y, a.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hoa : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [a.x, a.y, a.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (copyPt n o a)) s fun s' =>
      wordsVal s'.mem base o.x n = wordsVal s.mem base a.x n ∧
      wordsVal s'.mem base o.y n = wordsVal s.mem base a.y n ∧
      wordsVal s'.mem base o.z n = wordsVal s.mem base a.z n ∧
      Keeps [.eax] s s' ∧ Outs base [(o.x, 8 * n), (o.y, 8 * n), (o.z, 8 * n)] s.mem s'.mem := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hoa
  obtain ⟨iox, ioy, ioz, iax, iay, iaz⟩ := hin
  obtain ⟨⟨xax, xay, xaz⟩, ⟨yax, yay, yaz⟩, ⟨zax, zay, zaz⟩⟩ := hoa
  obtain ⟨xy, xz, yz⟩ := hoo
  simp only [wordsVal_eq_val32]
  rw [copyPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (copy_ok (2 * n) hs (by omega_using [iox]) (by omega_using [iax]) (by omega_using [xax]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * n) hs₁ (by omega_using [ioy]) (by omega_using [iay]) (by omega_using [yay]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (copy_ok (2 * n) hs₂ (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [zaz]))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.val32 (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.val32 (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.val32 (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.val32 (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.val32 (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.val32 (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · rw [show 4 * (2 * n) = 8 * n by omega_using []] at O₁ O₂ O₃
    exact ((Outs.of_outside O₁ (by simp)).trans (Outs.of_outside O₂ (by simp))).trans
      (Outs.of_outside O₃ (by simp))

/-! ## The point functions' stack and `esp` -/

theorem mem_instrs_progs : ∀ (ps : List (Prog isa)) {i : Instr}, i ∈ instrs (progs ps) → ∃ p ∈ ps, i ∈ instrs p
  | [], _, h => by simp [progs, instrs] at h
  | [p], _, h => ⟨p, List.mem_singleton_self _, h⟩
  | p :: q :: ps, i, h => by
    simp only [progs, instrs, List.mem_append] at h
    rcases h with h | h
    · exact ⟨p, List.mem_cons_self .., h⟩
    · obtain ⟨r, hr, hi⟩ := mem_instrs_progs (q :: ps) h
      exact ⟨r, List.mem_cons_of_mem _ hr, hi⟩

theorem stackUse_progs_le {n : Nat} : ∀ (ps : List (Prog isa)), (∀ p ∈ ps, stackUse p ≤ n) →
    stackUse (progs ps) ≤ n
  | [], _ => by simp [progs, stackUse]
  | [p], h => h p (List.mem_singleton_self _)
  | p :: q :: ps, h => by
    simp only [progs, stackUse]
    exact Nat.max_le.mpr ⟨h p (List.mem_cons_self ..),
      stackUse_progs_le (q :: ps) fun r hr => h r (List.mem_cons_of_mem _ hr)⟩

theorem mulFn_stackUse (k m : Nat) : stackUse (mulFn k m) = 0 := by
  unfold mulFn mulBody
  split <;> [rfl; (split <;> rfl)]

theorem noSp_callB {enc : Nat → Nat} {f : String} {body : Prog isa} (h : NoSp body) {o a b : Nat} :
    NoSp (callB enc f body o a b) := by
  intro i hi
  simp only [callB, callOp, instrs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with (rfl | rfl | rfl) | (rfl | hi) | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h i hi
  · rfl

theorem stackUse_callB {enc : Nat → Nat} {f : String} {body : Prog isa} (h : stackUse body = 0) {o a b : Nat} :
    stackUse (callB enc f body o a b) = 20 := by
  simp only [callB, callOp, stackUse, frameBytes, h]; rfl

/-- The point functions never write `esp` but by their calls' frames. -/
theorem fnOps_noSp {S : Impl.Weierstrass.Mont.Modulus} (hF : FnOk S) (dbl : Bool) (ops : List FOp) :
    NoSp (fnOps S dbl ops) := by
  intro i hi
  simp only [fnOps, instrs, List.mem_append] at hi
  rcases hi with hi | hi | hi
  · simp only [entry, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl
  · obtain ⟨p, hp, hi⟩ := mem_instrs_progs _ hi
    obtain ⟨op, -, rfl⟩ := List.mem_map.mp hp
    cases op with
    | mul => exact noSp_callB hF.nsMul i hi
    | add => exact noSp_callB hF.nsAdd i hi
    | sub => exact noSp_callB hF.nsSub i hi
  · simp only [restore, List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi]; rfl

/-- A point function's calls use 20 bytes of stack. -/
theorem fnOps_stackUse (S : Impl.Weierstrass.Mont.Modulus) (dbl : Bool) (ops : List FOp) :
    stackUse (fnOps S dbl ops) ≤ 20 := by
  simp only [fnOps, stackUse, Nat.zero_max, Nat.max_zero]
  refine stackUse_progs_le _ fun p hp => ?_
  obtain ⟨op, -, rfl⟩ := List.mem_map.mp hp
  cases op with
  | mul => exact Nat.le_of_eq (stackUse_callB (mulFn_stackUse _ _))
  | add => exact Nat.le_of_eq (stackUse_callB rfl)
  | sub => exact Nat.le_of_eq (stackUse_callB rfl)

/-- The 8 bytes below `esp` (a push and a return address) are past the
working space, given 28 bytes below `esp` apart from it. -/
theorem zone8 {s : State} {base : Addr} (hs : Scr s base 8192) (h28 : 28 ≤ (s.gpr .esp).toNat)
    (hz : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ (s.gpr .esp).toNat) {x : Addr}
    (hx : (below (s.gpr .esp) 8).Contains x 1) : 8192 ≤ ofs base x := by
  have hn := hs.nowrap
  obtain hsp := (s.gpr .esp).isLt
  simp only [Region.Contains] at hx
  simp only [ofs]
  obtain e : ((s.gpr .esp - BitVec.ofNat 32 8).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega_using [])
  generalize ((s.gpr .esp - BitVec.ofNat 32 8).setWidth 64) = z at hx e
  bv_omega

/-- Memory that changed only in the 8 bytes below `esp` keeps the working space. -/
theorem frame_val32P' {s : State} {base : Addr} (hs : Scr s base 8192) {m m' : Mem}
    (hF : Frame [below (s.gpr .esp) 8] m m') (h28 : 28 ≤ (s.gpr .esp).toNat := by omega)
    (hz : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ (s.gpr .esp).toNat := by omega)
    {d n : Nat} (h : d + 4 * n ≤ 8192) : val32 m' base d n = val32 m base d n := by
  have hn := hs.nowrap
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => hF _ fun r hr hc => ?_)
  rw [List.mem_singleton.mp hr] at hc
  have := zone8 hs h28 hz hc
  rw [ofs_off base (by omega_using [h, hj, hi])] at this
  omega_using [h, hj, hi, this]

/-- What the slot of number `x` stands for, in the working space at `base`. -/
def Eb (k m : Nat) [NeZero m] (dbl : Bool) (mem : Mem) (base : Addr) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal mem base (enc k dbl x) k)

/-- What the point function `ptName S a0 dbl` computes from the values of
the slots: Algorithm 9 or 8 for `a0`, else Algorithm 1. -/
def ptVal {m : Nat} [NeZero m] (a0 dbl : Bool) (E : Nat → Fin m) : Fin m × Fin m × Fin m :=
  if a0 then
    (if dbl then Impl.Weierstrass.Point.rcbDbl0 (E 10) (E 3) (E 4) (E 5)
    else Impl.Weierstrass.Point.rcbAdd0m (E 10) (E 3) (E 4) (E 5) (E 6) (E 7))
  else VG.Proof.Weierstrass.rcbAdd (E 9) (E 10) (E 3) (E 4) (E 5) (E 6) (E 7) (E 8)

theorem ptOps_opsOk (a0 dbl : Bool) : OpsOk (ptOps a0 dbl) := by
  cases a0
  · exact rcbIds_opsOk
  · exact ops0_opsOk dbl

theorem ptOps_run {m : Nat} [NeZero m] (E : Nat → Fin m) (a0 dbl : Bool) :
    (runOps (ptOps a0 dbl) E 0, runOps (ptOps a0 dbl) E 1, runOps (ptOps a0 dbl) E 2) =
      ptVal a0 dbl E := by
  cases a0
  · exact rcb_run rcbIds_apart E
  · exact ops0_run E dbl

theorem ptVal_congr {m : Nat} [NeZero m] {E E' : Nat → Fin m} (h : ∀ x ∈ rIds, E x = E' x) (a0 dbl : Bool) :
    ptVal a0 dbl E = ptVal a0 dbl E' := by
  simp only [ptVal, h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
    h 8 (by decide), h 9 (by decide), h 10 (by decide)]

/-- A call of a point function, from the working space at `edi`, whose base
is also the caller's argument at `[esp + arg]`, with 28 bytes of stack below
`esp` apart from the working space: only `eax`, `ecx`, `edx`, `O`, the own
working space and the stack below `esp` change, and `O` holds `rcbAdd` of
what the constants and the operands stood for. -/
theorem ptCall_ok {S : Impl.Weierstrass.Mont.Modulus} {m k : Nat} [NeZero m] (hF : FnOk S) (hm : S.m = m)
    (hk : S.k = k) (hodd : m % 2 = 1) (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) {a0 : Bool} {ao : Nat} {s : State}
    {base : Addr} (hs : Scr s base 8192) (h28 : 28 ≤ (s.gpr .esp).toNat)
    (hz : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ (s.gpr .esp).toNat)
    (hrd : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) ao) 4)
    (hav : s.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi)
    (haw : Region.Disjoint ⟨addr (s.gpr .esp) ao, 4⟩ ⟨base, 8192⟩)
    (has : Region.Disjoint ⟨addr (s.gpr .esp) ao, 4⟩ (below (s.gpr .esp) 28))
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc k dbl x) k < m) :
    WP isa (ptCall S dbl ao a0) s fun s' => Keeps [.eax, .ecx, .edx] s s' ∧
      Outs base [(Impl.Weierstrass.Point.oAt k, 3 * Impl.Weierstrass.Point.elemBytes k),
        (Impl.Weierstrass.Point.ownAt k, 4096 - Impl.Weierstrass.Point.ownAt k), outW] s.mem s'.mem ∧
      Frame [⟨base, 8192⟩, below (s.gpr .esp) 28] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc k dbl j) k < m) ∧
      (Eb k m dbl s'.mem base 0, Eb k m dbl s'.mem base 1, Eb k m dbl s'.mem base 2) =
        ptVal a0 dbl (Eb k m dbl s.mem base) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hm hk
  subst hm hk
  have hn := hs.nowrap
  obtain hspN := (s.gpr .esp).isLt
  have hedi := hs.edi_toNat
  obtain hl := lay_nums hk3 hk6
  obtain hst := fnOps_stackUse ⟨c, w, m', k', d⟩ dbl (ptOps a0 dbl)
  obtain hfit : 4 * [Reg.edi].length + 4 ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega_arith
  -- The callee's view.
  let t := ((pushed [Reg.edi] s).callEntry).withRegions [below (s.gpr .esp) 4] [⟨base, 8192⟩]
  obtain arg0 : arg t 0 = s.gpr .edi := callEntry_arg hfit (by decide) (by decide)
  obtain hws : wsOf t = base := by show (arg t 0).setWidth 64 = base; rw [arg0]; exact hs.edi
  obtain hwsN : (wsOf t).toNat = base.toNat := by rw [hws]
  obtain espT : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 8 := by
    show ((pushed _ s).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat hfit]; rfl
  obtain argA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 := callEntry_argAddr0 _ _
  obtain argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 4 := by
    rw [argA, BitVec.toNat_setWidth, sub_toNat (by omega_arith)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  obtain retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, espT]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain fr : Frame [below (s.gpr .esp) 8] s.mem t.mem := callEntry_frame hfit (rs := [Reg.edi]) (by decide)
  obtain hpre : PrePt k' m' dbl t := by
    refine ⟨⟨rfl, by show _ ∈ [below (s.gpr .esp) 4]; rw [argA]; exact List.mem_singleton_self _,
      by show _ ∈ [(⟨base, 8192⟩ : Region)]; rw [hws]; exact List.mem_singleton_self _,
      by rw [hwsN]; exact hn, ⟨by rw [espT]; omega_arith, by rw [espT, hwsN]; omega_arith⟩, by rw [espT]; omega_arith,
      Region.disjoint_of_le (by simp only; rw [argN, hwsN]; omega_arith) (by simp only; rw [argN]; omega_arith)
        (by simp only; rw [hwsN]; omega_arith)⟩,
      Region.disjoint_of_le (by simp only; rw [retN, hwsN]; omega_arith) (by simp only; rw [retN]; omega_arith)
        (by simp only; rw [hwsN]; omega_arith), hk3, hk6, fun x hx => ?_⟩
    rw [hws, wordsVal_eq_val32, frame_val32P' hs fr h28 hz (h := by have := enc_rIds hk3 hk6 dbl x hx; omega_arith),
      ← wordsVal_eq_val32]
    exact hlt x hx
  let K : Contract isa :=
    { pre := fun u => PrePt k' m' dbl u ∧ wsOf u = base ∧ Frame [below (s.gpr .esp) 8] s.mem u.mem
      post := fun u u' =>
        Outs (wsOf u) [(Impl.Weierstrass.Point.oAt k', 3 * Impl.Weierstrass.Point.elemBytes k'),
          (Impl.Weierstrass.Point.ownAt k', 4096 - Impl.Weierstrass.Point.ownAt k'), outW] u.mem u'.mem ∧
        (∀ j < 3, wordsVal u'.mem (wsOf u) (enc k' dbl j) k' < m') ∧
        (toM m' (2 ^ (64 * k')) (wordsVal u'.mem (wsOf u) (enc k' dbl 0) k'),
          toM m' (2 ^ (64 * k')) (wordsVal u'.mem (wsOf u) (enc k' dbl 1) k'),
          toM m' (2 ^ (64 * k')) (wordsVal u'.mem (wsOf u) (enc k' dbl 2) k')) =
          ptVal a0 dbl (E₀ k' m' dbl u)
      pub := fun _ _ => True }
  rw [ptCall]
  refine WP.seq (WP.callWith (k := K) (fun u ⟨h1, _, _⟩ => by
      obtain ⟨tr, u', he, A, O, L, E⟩ := fnOps_ok (S := ⟨c, w, m', k', d⟩) hF hodd (ptOps_opsOk a0 dbl) h1
      exact ⟨tr, u', he, A, O, L, E.trans (ptOps_run _ a0 dbl)⟩) (fnOps_noSp hF dbl _) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega_arith) (rd := [below (s.gpr .esp) 4])
    (wr := [⟨base, 8192⟩]) ⟨⟨hpre, hws, fr⟩, ?_, ?_⟩ ?_)
  · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; simp
    · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ hs.wr
  intro s' rd' wr' cs' F' ⟨s₂, m₂, P₂⟩
  have P₂' : K.post t s₂ := P₂
  obtain ⟨O₂, L₂, E₂⟩ := P₂'
  obtain F₂ : Frame [⟨base, 8192⟩, below (s.gpr .esp) 28] s.mem s'.mem := by
    have := Frame.below_mono F' (b := 28) (by simp only [List.length_cons, List.length_nil]; omega_arith) h28
    exact this.mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  obtain esp' : s'.gpr .esp = s.gpr .esp := cs' .esp (by decide)
  obtain edi' : s'.gpr .edi = s.gpr .edi := cs' .edi (by decide)
  obtain m₂ : Frame [below (s.gpr .esp) 8] s₂.mem s'.mem := Frame.below_mono (wr := []) m₂ (by decide) (by omega_arith)
  obtain v₂ : ∀ x, x + 8 * k' ≤ 8192 → wordsVal s'.mem base x k' = wordsVal s₂.mem base x k' := fun x hx => by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, frame_val32P' hs m₂ h28 hz (h := by omega_arith)]
  rw [hws] at O₂ L₂
  simp only [hws] at E₂
  rw [← v₂ _ (enc_out hk3 hk6 dbl (j := 0) (by decide)), ← v₂ _ (enc_out hk3 hk6 dbl (j := 1) (by decide)),
    ← v₂ _ (enc_out hk3 hk6 dbl (j := 2) (by decide))] at E₂
  refine wp_ldm (b := .esp) esp' (by rw [rd', wr']; exact hrd) fun s₃ u₃ => WP.block_nil ?_
  obtain hv : s'.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi := by
    rw [F₂.readW (r := ⟨addr (s.gpr .esp) ao, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact haw
      · exact has) (by decide), hav]
  have m₃ : s₃.mem = s'.mem := u₃.mem
  -- The callee's view of memory: the push and the return address, then the call.
  have mt : (pushed [Reg.edi] s).callEntry.mem = t.mem := rfl
  obtain vt : ∀ x, x + 8 * k' ≤ 8192 → wordsVal t.mem base x k' = wordsVal s.mem base x k' := fun x hx => by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, frame_val32P' hs fr h28 hz (h := by omega_arith)]
  refine ⟨⟨fun r hr => ?_, by rw [u₃.rd, rd'], by rw [u₃.wr, wr']⟩, ?_, ?_, fun j hj => ?_, ?_⟩
  · by_cases h : r = .edi
    · subst h; rw [u₃.gpr, hv]
    · rw [u₃.other _ h]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact cs' r (by revert hr; cases r <;> decide)
  · rw [m₃]
    refine fun x hx => ?_
    by_cases hzx : ofs base x < 8192
    · have nz : ∀ r ∈ [below (s.gpr .esp) 8], ¬ r.Contains x 1 := fun r hr hc => by
        rw [List.mem_singleton.mp hr] at hc
        have := zone8 hs h28 hz hc
        omega_arith
      exact (m₂ x nz).trans ((O₂ x hx).trans (fr x nz))
    · have h2 := hx outW (by simp)
      obtain h3 : ofs base x < 2 ^ 64 := (x - base).isLt
      simp only at h2
      omega_arith
  · rw [m₃]; exact F₂
  · rw [m₃, v₂ _ (enc_out hk3 hk6 dbl hj)]; exact L₂ j hj
  · simp only [Eb]
    rw [m₃]
    obtain e : ∀ x, x ∈ rIds →
        toM m' (2 ^ (64 * k')) (wordsVal t.mem base (enc k' dbl x) k') =
          toM m' (2 ^ (64 * k')) (wordsVal s.mem base (enc k' dbl x) k') := fun x hx => by
      have := enc_rIds hk3 hk6 dbl x hx
      obtain hl := lay_nums hk3 hk6
      rw [vt _ (by omega_arith)]
    exact E₂.trans (ptVal_congr (fun x hx => by
      show toM _ _ (wordsVal t.mem (wsOf t) _ _) = _
      rw [hws]; exact e x hx) a0 dbl)

end VG.Proof.Weierstrass.X86.Point
