import VerifiedGarbage.Proof.Weierstrass.X86.PointFn
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Impl.Weierstrass.X86.LadderP

/-!
# The ladder by calls of the point functions, on x86 (32-bit): copies and calls

`copyPt n o a` copies the point at `a` to `o` (`copyPt_ok`), and
`ptCall S dbl arg` calls `vg_<curve>_point_double` or `vg_<curve>_point_add`
on the working space at `edi`, then loads `edi` again from the caller's
argument holding it (`ptCall_ok`): it changes only `eax`, `ecx` and `edx`,
`O`, the point functions' own working space and the 28 bytes of stack below
`esp`, and `O` then holds `rcbAdd` of what `a`, `3b`, `P` and `Q` (or `P`)
stood for (`fn_ok`).
-/

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
  have hs₁ := hs.of_keeps k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (copy_ok (2 * n) hs₁ (by omega_using [ioy]) (by omega_using [iay]) (by omega_using [yay]))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.mono (copy_ok (2 * n) hs₂ (by omega_using [ioz]) (by omega_using [iaz]) (by omega_using [zaz]))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, ?_⟩
  · rw [O₃.val32 (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.val32 (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.val32 (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.val32 (d := a.y) (by omega_using [xay]) (by omega_using [iay, hn])]
  · rw [e₃, O₂.val32 (d := a.z) (by omega_using [yaz]) (by omega_using [iaz, hn]),
      O₁.val32 (d := a.z) (by omega_using [xaz]) (by omega_using [iaz, hn])]
  · rw [show 4 * (2 * n) = 8 * n by omega] at O₁ O₂ O₃
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
  split <;> rfl

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
theorem fn_noSp {S : Spec.Weierstrass.Mont.Modulus} (hF : FnOk S) (dbl : Bool) : NoSp (fn S dbl) := by
  intro i hi
  simp only [fn, instrs, List.mem_append] at hi
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
theorem fn_stackUse (S : Spec.Weierstrass.Mont.Modulus) (dbl : Bool) : stackUse (fn S dbl) ≤ 20 := by
  simp only [fn, stackUse, Nat.zero_max, Nat.max_zero]
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
  have hsp := (s.gpr .esp).isLt
  simp only [Region.Contains] at hx
  simp only [ofs]
  have e : ((s.gpr .esp - BitVec.ofNat 32 8).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
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
  rw [ofs_off base (by omega)] at this
  omega

/-- What the slot of number `x` stands for, in the working space at `base`. -/
def Eb (k m : Nat) [NeZero m] (dbl : Bool) (mem : Mem) (base : Addr) (x : Nat) : Fin m :=
  toM m (2 ^ (64 * k)) (wordsVal mem base (enc k dbl x) k)

/-- A call of a point function, from the working space at `edi`, whose base
is also the caller's argument at `[esp + arg]`, with 28 bytes of stack below
`esp` apart from the working space: only `eax`, `ecx`, `edx`, `O`, the own
working space and the stack below `esp` change, and `O` holds `rcbAdd` of
what the constants and the operands stood for. -/
theorem ptCall_ok {S : Spec.Weierstrass.Mont.Modulus} {m k : Nat} [NeZero m] (hF : FnOk S) (hm : S.m = m)
    (hk : S.k = k) (hodd : m % 2 = 1) (hk3 : 3 ≤ k) (hk6 : k ≤ 6) (dbl : Bool) {ao : Nat} {s : State}
    {base : Addr} (hs : Scr s base 8192) (h28 : 28 ≤ (s.gpr .esp).toNat)
    (hz : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ (s.gpr .esp).toNat)
    (hrd : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) ao) 4)
    (hav : s.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi)
    (haw : Region.Disjoint ⟨addr (s.gpr .esp) ao, 4⟩ ⟨base, 8192⟩)
    (has : Region.Disjoint ⟨addr (s.gpr .esp) ao, 4⟩ (below (s.gpr .esp) 28))
    (hlt : ∀ x ∈ rIds, wordsVal s.mem base (enc k dbl x) k < m) :
    WP isa (ptCall S dbl ao) s fun s' => Keeps [.eax, .ecx, .edx] s s' ∧
      Outs base [(Spec.Weierstrass.Point.oAt k, 3 * Spec.Weierstrass.Point.elemBytes k),
        (Spec.Weierstrass.Point.ownAt k, 4096 - Spec.Weierstrass.Point.ownAt k), outW] s.mem s'.mem ∧
      Frame [⟨base, 8192⟩, below (s.gpr .esp) 28] s.mem s'.mem ∧
      (∀ j < 3, wordsVal s'.mem base (enc k dbl j) k < m) ∧
      (Eb k m dbl s'.mem base 0, Eb k m dbl s'.mem base 1, Eb k m dbl s'.mem base 2) =
        VG.Proof.Weierstrass.rcbAdd (Eb k m dbl s.mem base 9) (Eb k m dbl s.mem base 10)
          (Eb k m dbl s.mem base 3) (Eb k m dbl s.mem base 4) (Eb k m dbl s.mem base 5)
          (Eb k m dbl s.mem base 6) (Eb k m dbl s.mem base 7) (Eb k m dbl s.mem base 8) := by
  obtain ⟨c, w, m', k', d⟩ := S
  dsimp only at hm hk
  subst hm hk
  have hn := hs.nowrap
  have hspN := (s.gpr .esp).isLt
  have hedi := hs.edi_toNat
  have hl := lay_nums hk3 hk6
  have hst := fn_stackUse ⟨c, w, m', k', d⟩ dbl
  have hfit : 4 * [Reg.edi].length + 4 ≤ (s.gpr .esp).toNat := by simp only [List.length_cons, List.length_nil]; omega
  -- The callee's view.
  let t := ((pushed [Reg.edi] s).callEntry).withRegions [below (s.gpr .esp) 4] [⟨base, 8192⟩]
  have a0 : arg t 0 = s.gpr .edi := callEntry_arg hfit (by decide) (by decide)
  have hws : wsOf t = base := by show (arg t 0).setWidth 64 = base; rw [a0]; exact hs.edi
  have hwsN : (wsOf t).toNat = base.toNat := by rw [hws]
  have espT : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 8 := by
    show ((pushed _ s).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat hfit]; rfl
  have argA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 := callEntry_argAddr0 _ _
  have argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 4 := by
    rw [argA, BitVec.toNat_setWidth, sub_toNat (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, espT]; exact Nat.mod_eq_of_lt (by omega)
  have fr : Frame [below (s.gpr .esp) 8] s.mem t.mem := callEntry_frame hfit (rs := [Reg.edi]) (by decide)
  have hpre : PrePt k' m' dbl t := by
    refine ⟨⟨rfl, by show _ ∈ [below (s.gpr .esp) 4]; rw [argA]; exact List.mem_singleton_self _,
      by show _ ∈ [(⟨base, 8192⟩ : Region)]; rw [hws]; exact List.mem_singleton_self _,
      by rw [hwsN]; exact hn, ⟨by rw [espT]; omega, by rw [espT, hwsN]; omega⟩, by rw [espT]; omega,
      Region.disjoint_of_le (by simp only; rw [argN, hwsN]; omega) (by simp only; rw [argN]; omega)
        (by simp only; rw [hwsN]; omega)⟩,
      Region.disjoint_of_le (by simp only; rw [retN, hwsN]; omega) (by simp only; rw [retN]; omega)
        (by simp only; rw [hwsN]; omega), hk3, hk6, fun x hx => ?_⟩
    rw [hws, wordsVal_eq_val32, frame_val32P' hs fr h28 hz (h := by have := enc_rIds hk3 hk6 dbl x hx; omega),
      ← wordsVal_eq_val32]
    exact hlt x hx
  let K : Contract isa :=
    { pre := fun u => PrePt k' m' dbl u ∧ wsOf u = base ∧ Frame [below (s.gpr .esp) 8] s.mem u.mem
      post := fun u u' =>
        Outs (wsOf u) [(Spec.Weierstrass.Point.oAt k', 3 * Spec.Weierstrass.Point.elemBytes k'),
          (Spec.Weierstrass.Point.ownAt k', 4096 - Spec.Weierstrass.Point.ownAt k'), outW] u.mem u'.mem ∧
        (∀ j < 3, wordsVal u'.mem (wsOf u) (enc k' dbl j) k' < m') ∧
        (toM m' (2 ^ (64 * k')) (wordsVal u'.mem (wsOf u) (enc k' dbl 0) k'),
          toM m' (2 ^ (64 * k')) (wordsVal u'.mem (wsOf u) (enc k' dbl 1) k'),
          toM m' (2 ^ (64 * k')) (wordsVal u'.mem (wsOf u) (enc k' dbl 2) k')) =
          VG.Proof.Weierstrass.rcbAdd (E₀ k' m' dbl u 9) (E₀ k' m' dbl u 10) (E₀ k' m' dbl u 3)
            (E₀ k' m' dbl u 4) (E₀ k' m' dbl u 5) (E₀ k' m' dbl u 6) (E₀ k' m' dbl u 7) (E₀ k' m' dbl u 8)
      pub := fun _ _ => True }
  rw [ptCall]
  refine WP.seq (WP.callWith (k := K) (fun u ⟨h1, _, _⟩ => by
      obtain ⟨tr, u', he, A, O, L, E⟩ := fn_ok (S := ⟨c, w, m', k', d⟩) hF hodd h1
      exact ⟨tr, u', he, A, O, L, E⟩) (fn_noSp hF dbl) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega) (rd := [below (s.gpr .esp) 4])
    (wr := [⟨base, 8192⟩]) ⟨⟨hpre, hws, fr⟩, ?_, ?_⟩ ?_)
  · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_)
    · rw [List.mem_singleton.mp hr]; simp
    · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
  · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ hs.wr
  intro s' rd' wr' cs' F' ⟨s₂, m₂, P₂⟩
  have P₂' : K.post t s₂ := P₂
  obtain ⟨O₂, L₂, E₂⟩ := P₂'
  have F₂ : Frame [⟨base, 8192⟩, below (s.gpr .esp) 28] s.mem s'.mem := by
    have := Frame.below_mono F' (b := 28) (by simp only [List.length_cons, List.length_nil]; omega) h28
    exact this.mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  have esp' : s'.gpr .esp = s.gpr .esp := cs' .esp (by decide)
  have edi' : s'.gpr .edi = s.gpr .edi := cs' .edi (by decide)
  rw [hws, m₂] at O₂ L₂
  simp only [E₀, hws, m₂] at E₂
  refine wp_ldm (b := .esp) esp' (by rw [rd', wr']; exact hrd) fun s₃ u₃ => WP.block_nil ?_
  have hv : s'.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi := by
    rw [F₂.readW (r := ⟨addr (s.gpr .esp) ao, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact haw
      · exact has) (by decide), hav]
  have m₃ : s₃.mem = s'.mem := u₃.mem
  -- The callee's view of memory: the push and the return address, then the call.
  have mt : (pushed [Reg.edi] s).callEntry.mem = t.mem := rfl
  have vt : ∀ x, x + 8 * k' ≤ 8192 → wordsVal t.mem base x k' = wordsVal s.mem base x k' := fun x hx => by
    rw [wordsVal_eq_val32, wordsVal_eq_val32, frame_val32P' hs fr h28 hz (h := by omega)]
  refine ⟨⟨fun r hr => ?_, by rw [u₃.rd, rd'], by rw [u₃.wr, wr']⟩, ?_, ?_, fun j hj => ?_, ?_⟩
  · by_cases h : r = .edi
    · subst h; rw [u₃.gpr, hv]
    · rw [u₃.other _ h]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact cs' r (by cases r <;> simp_all [calleeSaved])
  · rw [m₃]
    refine fun x hx => (O₂ x hx).trans ?_
    by_cases hzx : ofs base x < 8192
    · exact fr x fun r hr hc => by
        rw [List.mem_singleton.mp hr] at hc
        have := zone8 hs h28 hz hc
        omega
    · have h2 := hx outW (by simp)
      have h3 : ofs base x < 2 ^ 64 := (x - base).isLt
      simp only at h2
      omega
  · rw [m₃]; exact F₂
  · rw [m₃]; exact L₂ j hj
  · simp only [Eb]
    rw [m₃]
    have e : ∀ x, x ∈ rIds →
        toM m' (2 ^ (64 * k')) (wordsVal t.mem base (enc k' dbl x) k') =
          toM m' (2 ^ (64 * k')) (wordsVal s.mem base (enc k' dbl x) k') := fun x hx => by
      have := enc_rIds hk3 hk6 dbl x hx
      have hl := lay_nums hk3 hk6
      rw [vt _ (by omega)]
    rw [e 9 (by decide), e 10 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide), e 6 (by decide),
      e 7 (by decide), e 8 (by decide)] at E₂
    exact E₂

end VG.Proof.Weierstrass.X86.Point
