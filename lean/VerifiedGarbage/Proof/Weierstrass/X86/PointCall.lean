import VerifiedGarbage.Proof.Weierstrass.X86.MontCall
import VerifiedGarbage.Impl.Weierstrass.X86.Point

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
  simp only [argAddr, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem below_toNat (sp : BitVec 32) {n : Nat} (h : n ≤ sp.toNat) : (below sp n).base.toNat = sp.toNat - n := by
  show ((sp - BitVec.ofNat 32 n).setWidth 64).toNat = _
  rw [BitVec.toNat_setWidth, sub_toNat h]; omega

/-- The argument is apart from the 20 bytes below `esp`. -/
theorem args_below {s : State} (h20 : 20 ≤ (s.gpr .esp).toNat) (h : (s.gpr .esp).toNat + 8 ≤ 2 ^ 32) :
    Region.Disjoint ⟨argAddr s 0, 4⟩ (below (s.gpr .esp) 20) :=
  Region.disjoint_of_le (.inr (by
    show (below (s.gpr .esp) 20).base.toNat + 20 ≤ (argAddr s 0).toNat
    rw [below_toNat _ h20, argAddr0_toNat s h]; omega))
    (by show (argAddr s 0).toNat + 4 ≤ _; rw [argAddr0_toNat s h]; omega)
    (by show (below (s.gpr .esp) 20).base.toNat + 20 ≤ _; rw [below_toNat _ h20]; omega)

/-- The argument survives a change of memory within the working space and
the stack below `esp`. -/
theorem ScrP.keep {s s' : State} {base : Addr} (hs : ScrP s base) (hsp : s'.gpr .esp = s.gpr .esp)
    (hedi : s'.gpr .edi = s.gpr .edi)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hf : Frame [⟨base, 8192⟩, below (s.gpr .esp) 20] s.mem s'.mem) : ScrP s' base := by
  have e : argAddr s' 0 = argAddr s 0 := by simp only [argAddr, hsp]
  have harg : arg s' 0 = arg s 0 := by
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
      ∃ m, Frame [below (s.gpr .esp) 20] s.mem m ∧ V m s'.mem := by
  have hown := (saveAt_le hk0 hk9).2
  have hn := hs.nowrap
  obtain ⟨h20, hz⟩ := hs.stk
  have hspN := (s.gpr .esp).isLt
  rw [callB, callOp]
  refine WP.seq (wp_movS rfl fun s₁ u₁ _ => wp_movS rfl fun s₂ u₂ _ => wp_movS rfl fun s₃ u₃ _ =>
    WP.block_nil ?_)
  have g : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₃.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₃.other _ hr.2.2, u₂.other _ hr.2.1, u₁.other _ hr.1]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have rd₃ : s₃.rd = s.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have esp₃ : s₃.gpr .esp = s.gpr .esp := g _ (by decide)
  have edi₃ : s₃.gpr .edi = s.gpr .edi := g _ (by decide)
  have eax₃ : s₃.gpr .eax = BitVec.ofNat 32 (enc b) := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ecx₃ : s₃.gpr .ecx = BitVec.ofNat 32 (enc a) := by rw [u₃.other _ (by decide), u₂.gpr]
  have edx₃ : s₃.gpr .edx = BitVec.ofNat 32 (enc o) := u₃.gpr
  have hfit : 4 * [Reg.eax, .ecx, .edx, .edi].length + 4 ≤ (s₃.gpr .esp).toNat := by
    rw [esp₃]; simp only [List.length_cons, List.length_nil]; omega
  -- The callee's view.
  let t := ((pushed [Reg.eax, .ecx, .edx, .edi] s₃).callEntry).withRegions
    [below (s₃.gpr .esp) 16] [⟨base, 8192⟩]
  have targ : ∀ i (hi : i < 4), arg t i = s₃.gpr ([Reg.eax, .ecx, .edx, .edi][3 - i]'(by simp; omega)) :=
    fun i hi => callEntry_arg hfit (by decide) (by simpa using hi)
  have a0 : arg t 0 = s.gpr .edi := by rw [targ 0 (by decide)]; exact edi₃
  have hlt : ∀ x, x < 4096 → (BitVec.ofNat 32 x).toNat = x := fun x hx => by
    rw [BitVec.toNat_ofNat]; omega
  have a1 : (arg t 1).toNat = enc o := by
    rw [targ 1 (by decide)]; show (s₃.gpr .edx).toNat = enc o; rw [edx₃, hlt _ (by omega)]
  have a2 : (arg t 2).toNat = enc a := by
    rw [targ 2 (by decide)]; show (s₃.gpr .ecx).toNat = enc a; rw [ecx₃, hlt _ (by omega)]
  have a3 : (arg t 3).toNat = enc b := by
    rw [targ 3 (by decide)]; show (s₃.gpr .eax).toNat = enc b; rw [eax₃, hlt _ (by omega)]
  have hws : wsOf t = base := by show (arg t 0).setWidth 64 = base; rw [a0]; exact hs.edi
  have hwsN : (arg t 0).toNat = base.toNat := by
    rw [a0, ← hs.edi, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (s.gpr .edi).isLt
      (Nat.pow_le_pow_right (by decide) (by decide)))]
  have espT : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 20 := by
    show ((pushed _ s₃).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat hfit, esp₃]; rfl
  have argA : argAddr t 0 = (s₃.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := callEntry_argAddr0 _ _
  have argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 16 := by
    rw [argA, esp₃, BitVec.toNat_setWidth, sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
    rw [BitVec.toNat_setWidth, espT]; exact Nat.mod_eq_of_lt (by omega)
  have fr : Frame [below (s.gpr .esp) 20] s.mem t.mem := by
    have := callEntry_frame hfit (rs := [Reg.eax, .ecx, .edx, .edi]) (by decide)
    rw [m₃, esp₃] at this
    exact this
  have hpre : Pre k t := by
    have hwsT : (wsOf t).toNat = base.toNat := by rw [hws]
    refine ⟨by show [below (s₃.gpr .esp) 16] = [(⟨argAddr t 0, 16⟩ : Region)]; rw [argA],
      by show [(⟨base, 8192⟩ : Region)] = _; rw [hws], by rw [hwsN]; exact hn, by rw [espT]; omega,
      Region.disjoint_of_le (by simp only; rw [argN, hwsT]; omega) (by simp only; rw [argN]; omega)
        (by simp only; rw [hwsT]; omega),
      Region.disjoint_of_le (by simp only; rw [retN, hwsT]; omega) (by simp only; rw [retN]; omega)
        (by simp only; rw [hwsT]; omega),
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
  refine ⟨⟨fun r hr => ?_, by rw [rd', rd₃], by rw [wr', wr₃], fun x hx => ?_, ?_⟩, t.mem, fr,
    by rw [← m₂]; exact V₂⟩
  · rw [← g r hr]
    refine cs' r ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
    cases r <;> simp_all
  · by_cases hzx : (below (s.gpr .esp) 20).Contains x 1
    · have h1 : 8192 ≤ ofs base x := by
        have hn' := hs.nowrap
        simp only [Region.Contains] at hzx
        simp only [ofs]
        have e : ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
          rw [BitVec.toNat_setWidth, sub_toNat h20]
          exact Nat.mod_eq_of_lt (by omega)
        generalize ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64) = z at hzx e
        bv_omega
      have h2 := hx outW (by simp)
      have h3 : ofs base x < 2 ^ 64 := (x - base).isLt
      simp only at h2
      omega
    · rw [← m₂, O₂ x fun r hr => ?_]
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
  have hsp := (s.gpr .esp).isLt
  simp only [Region.Contains] at hx
  simp only [ofs]
  have e : ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64).toNat = (s.gpr .esp).toNat - 20 := by
    rw [BitVec.toNat_setWidth, sub_toNat h20]
    exact Nat.mod_eq_of_lt (by omega)
  generalize ((s.gpr .esp - BitVec.ofNat 32 20).setWidth 64) = z at hx e
  bv_omega

/-- Memory that changed only in the stack a call uses keeps the working space. -/
theorem frame_val32P {s : State} {base : Addr} (hs : ScrP s base) {m m' : Mem}
    (hF : Frame [below (s.gpr .esp) 20] m m') {d n : Nat} (h : d + 4 * n ≤ 8192) :
    val32 m' base d n = val32 m base d n := by
  have hn := hs.nowrap
  refine val32_congr fun j hj => congrArg BitVec.toNat (Mem.readW_congr fun i hi => hF _ fun r hr hc => ?_)
  rw [List.mem_singleton.mp hr] at hc
  have := zone_ofsP hs hc
  rw [ofs_off base (by omega)] at this
  omega

section
variable {enc : Nat → Nat} {S : Spec.Weierstrass.Mont.Modulus} (hF : FnOk S) {s : State} {base : Addr}
  (hs : ScrP s base) {o a b : Nat}
  (ho : enc o + 8 * S.k ≤ own S.k) (ha : enc a + 8 * S.k ≤ own S.k) (hb : enc b + 8 * S.k ≤ own S.k)
include hF hs ho ha hb

/-- `[o] = [a] [b] R⁻¹ mod m` by a call of `vg_<curve>_mul_mod_<p|n>`. -/
theorem mulCallB_ok (hB : wordsVal s.mem base (enc b) S.k < S.m) :
    WP isa (callB enc (S.fn "mul") (mulFn S.k S.m) o a b) s fun s' => CallKeepB S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k < S.m ∧
      wordsVal s'.mem base (enc o) S.k * 2 ^ (64 * S.k) % S.m =
        wordsVal s.mem base (enc a) S.k * wordsVal s.mem base (enc b) S.k % S.m := by
  have hown := (saveAt_le hF.mul.k0 hF.k9).2
  refine WP.mono (callB_ok hF.nsMul (by
    unfold mulFn mulBody
    split <;> rfl) hF.mul.k0 hF.k9 hs ho ha hb
    (V := fun m m' => val32 m' base (enc o) (2 * S.k) < S.m ∧
      val32 m' base (enc o) (2 * S.k) * 2 ^ (64 * S.k) % S.m =
        val32 m base (enc a) (2 * S.k) * val32 m base (enc b) (2 * S.k) % S.m)
    fun t hp hws h1 h2 h3 hfr => ?_) fun s' ⟨K, m, hm, V₁, V₂⟩ => ?_
  · refine WP.mono (mulFn_ok hF.mul hp (by
      rw [hws, h3, frame_val32P hs hfr (by omega), ← wordsVal_eq_val32]; exact hB))
      fun t' ⟨A, O, L, C⟩ => ⟨A, hws ▸ O, ?_⟩
    rw [hws, h1] at L
    rw [hws, h1, h2, h3] at C
    exact ⟨L, C⟩
  · rw [frame_val32P hs hm (by omega), frame_val32P hs hm (by omega)] at V₂
    refine ⟨K, ?_, ?_⟩
    · rw [wordsVal_eq_val32]; exact V₁
    · rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32]; exact V₂

/-- `[o] = [a] + [b] mod m` by a call of `vg_<curve>_add_mod_<p|n>`. -/
theorem addCallB_ok (hAB : wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k < 2 * S.m) :
    WP isa (callB enc (S.fn "add") (addFn S.k S.m) o a b) s fun s' => CallKeepB S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k =
        (wordsVal s.mem base (enc a) S.k + wordsVal s.mem base (enc b) S.k) % S.m := by
  have hown := (saveAt_le hF.mul.k0 hF.k9).2
  refine WP.mono (callB_ok hF.nsAdd rfl hF.mul.k0 hF.k9 hs ho ha hb
    (V := fun m m' => val32 m' base (enc o) (2 * S.k) =
      (val32 m base (enc a) (2 * S.k) + val32 m base (enc b) (2 * S.k)) % S.m)
    fun t hp hws h1 h2 h3 hfr => ?_) fun s' ⟨K, m, hm, V⟩ => ?_
  · refine WP.mono (addFn_ok hF.mul hp (by
      rw [hws, h2, h3, frame_val32P hs hfr (by omega), frame_val32P hs hfr (by omega), ← wordsVal_eq_val32,
        ← wordsVal_eq_val32]; exact hAB))
      fun t' ⟨A, O, L⟩ => ⟨A, hws ▸ O, ?_⟩
    rw [hws, h1, h2, h3] at L
    exact L
  · rw [frame_val32P hs hm (by omega), frame_val32P hs hm (by omega)] at V
    refine ⟨K, ?_⟩
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32]; exact V

/-- `[o] = [a] - [b] mod m` by a call of `vg_<curve>_sub_mod_<p|n>`. -/
theorem subCallB_ok (hA : wordsVal s.mem base (enc a) S.k < S.m) (hB : wordsVal s.mem base (enc b) S.k < S.m) :
    WP isa (callB enc (S.fn "sub") (subFn S.k S.m) o a b) s fun s' => CallKeepB S.k base (enc o) s s' ∧
      wordsVal s'.mem base (enc o) S.k =
        (wordsVal s.mem base (enc a) S.k + S.m - wordsVal s.mem base (enc b) S.k) % S.m := by
  have hown := (saveAt_le hF.mul.k0 hF.k9).2
  refine WP.mono (callB_ok hF.nsSub rfl hF.mul.k0 hF.k9 hs ho ha hb
    (V := fun m m' => val32 m' base (enc o) (2 * S.k) =
      (val32 m base (enc a) (2 * S.k) + S.m - val32 m base (enc b) (2 * S.k)) % S.m)
    fun t hp hws h1 h2 h3 hfr => ?_) fun s' ⟨K, m, hm, V⟩ => ?_
  · refine WP.mono (subFn_ok hF.mul hp
      (by rw [hws, h2, frame_val32P hs hfr (by omega), ← wordsVal_eq_val32]; exact hA)
      (by rw [hws, h3, frame_val32P hs hfr (by omega), ← wordsVal_eq_val32]; exact hB))
      fun t' ⟨A, O, L⟩ => ⟨A, hws ▸ O, ?_⟩
    rw [hws, h1, h2, h3] at L
    exact L
  · rw [frame_val32P hs hm (by omega), frame_val32P hs hm (by omega)] at V
    refine ⟨K, ?_⟩
    rw [wordsVal_eq_val32, wordsVal_eq_val32, wordsVal_eq_val32]; exact V

end

end VG.Proof.Weierstrass.X86.Point
