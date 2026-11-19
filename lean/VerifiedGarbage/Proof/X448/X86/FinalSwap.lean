module

public import VerifiedGarbage.Proof.X448.X86.Env
public import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.X448.X86.Frame
public import VerifiedGarbage.Proof.X448.X86.Save
import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Output
import VerifiedGarbage.Proof.X448.X86.Freeze
import VerifiedGarbage.Proof.X448.Bytes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X448.X86.Counters
public import VerifiedGarbage.Proof.X448.X86.Bits
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.X448.X86.Initial
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.Radix16Bytes
public import VerifiedGarbage.Proof.X448.X86.Mem
import VerifiedGarbage.Proof.X448.X86.Decode
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.X448.X86.Swap
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! ### `X448.X86.Ladder`, which the modules that import this one used -/

section

/-! ### `X448.X86.BitsInput`, which the modules that import this one used -/

section

/-! ### `X448.X86.Setup`, which the modules that import this one used -/

section

/-! ### `X448.X86.DecodeAll`, which only this module used -/

section

/-!
# X448 on x86 (32-bit): decoding the whole coordinate

The 28 limb loads fill two slots while preserving input bytes outside the
working space.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem decoded_congr {m m' : Mem} {p : Addr} {i : Nat} (hi : i < 28)
    (h : ∀ j < 56, m' (off p j) = m (off p j)) : decoded m' p i = decoded m p i := by
  simp only [decoded, byteN]
  rw [h (2 * i) (by omega_using [hi]), h (2 * i + 1) (by omega_using [hi])]

theorem decodeAll_ok {s : State} {base p : Addr} (hs : Scr s base)
    (hp : (s.gpr .esi).setWidth 64 = p) (hfit : (s.gpr .esi).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block ((List.range 28).flatMap decodeLimb)) s fun t =>
      (∀ j < 28, limbs t.mem base X1 j = decoded s.mem p j) ∧
      (∀ j < 28, limbs t.mem base X3 j = decoded s.mem p j) ∧
      Outside2 base X1 112 X3 112 s.mem t.mem ∧ Keeps [.eax, .edx] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, limbs t.mem base X1 j = decoded s.mem p j) ∧
    (∀ j < n, limbs t.mem base X3 j = decoded s.mem p j) ∧
    Outside2 base X1 (4 * n) X3 (4 * n) s.mem t.mem ∧ Keeps [.eax, .edx] s t
  have step : ∀ n t, n < 28 → inv n t → WP isa (.block (decodeLimb n)) t (inv (n + 1)) := by
    intro n t hn ⟨tx, ty, tm, tk⟩
    have tp : (t.gpr .esi).setWidth 64 = p := by rw [tk.1 _ (by decide)]; exact hp
    have tfit : (t.gpr .esi).toNat + 56 ≤ 2 ^ 32 := by rw [tk.1 _ (by decide)]; exact hfit
    have tr : ∀ j < 56, InRegions (t.rd ++ t.wr) (off p j) 1 := by
      intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj
    have byte : ∀ j < 56, t.mem (off p j) = s.mem (off p j) := by
      intro j hj
      have h := hd j hj
      exact tm _ (Or.inr (by simp only [X1, slot]; omega_using [hn, h])) (Or.inr (by simp only [X3, slot]; omega_using [hn, h]))
    have eq := decoded_congr hn byte
    refine WP.mono (decodeLimb_ok (hs.of_keeps tk (by decide)) hn tp tfit tr) fun u ⟨um, uk⟩ => ?_
    rw [eq] at um
    let v := BitVec.ofNat 32 (decoded s.mem p n)
    have vn : v.toNat = decoded s.mem p n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (decoded_lt s.mem p n) (by decide))]
    have pair := fun j (hj : j < 28) => pair_write (m := t.mem) (base := base)
      (x := X1) (y := X3) (by decide) (by decide) (by decide) hn hj v v
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · intro j hj
      rw [um, (pair j (by omega_using [hn, hj])).1]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact tx j (by omega_using [hj, h])
    · intro j hj
      rw [um, (pair j (by omega_using [hn, hj])).2]
      by_cases h : j = n
      · rw [ite_eq_left h, vn, h]
      · rw [ite_eq_right h]; exact ty j (by omega_using [hj, h])
    · rw [um]
      exact (tm.mono (by omega_using []) (by omega_using [])).trans (decodeLimb_outside _ _ hn _)
  exact wp_range_flatMap (M := isa) (N := 28) inv step 28 (by decide) s
    ⟨fun _ hj => by omega, fun _ hj => by omega, Outside2.refl _ _ _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): reading the arguments

Setup saves the callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def setupRegs : List Reg := [.eax, .edx, .edi, .esi]

theorem setup_ok {s : State} (hp : Pre s) {base p : Addr}
    (hc : (arg s 3).setWidth 64 = base) (hpoint : (arg s 2).setWidth 64 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ Keeps setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧
      E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E t.mem base 1 = 1 ∧ E t.mem base 2 = 0 ∧
      E t.mem base 3 = E t.mem base 0 ∧ E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun t ⟨ts, tv, tm, tk⟩ => ?_
  refine loadArg_ok hp (tk.1 _ (by decide)) tk.2.1 tk.2.2
    (XFrame.of_outside (tm.mono (by decide) (by decide))) (by decide : 2 < 4) fun t' ht => ?_
  rw [hc] at ts tv tm
  have ts' := ts.of_upd ht (by decide)
  have tm' : Outside base 0 16 s.mem t'.mem := by rw [ht.mem]; exact tm
  have tk' : Keeps setupRegs s t' := (tk.mono (by simp [setupRegs])).trans (ht.rest (by decide))
  change WP isa (.block ((List.range 28).flatMap decodeLimb ++ initSlots)) t' _
  rw [WP.block_append_iff]
  refine WP.mono (decodeAll_ok ts' (by rw [ht.gpr]; exact hpoint)
    (by rw [ht.gpr]; exact hp.point_fit)
    (by intro j hj; rw [tk'.2.1, tk'.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_lt _ _ _
  have ub3 : Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_lt _ _ _
  have uv0 : E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t'.mem p 56)) := by
    apply congrArg toFe
    exact (valN_congr ux).trans (decoded_val t'.mem p 28).symm
  have uv3 : E u.mem base 3 = E u.mem base 0 := congrArg toFe ((valN_congr uy).trans (valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t'.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm' _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (initSlots_ok (ts'.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts'.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    tk'.trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm'.mono (by decide) (by decide)).trans ?_,
    ((show Saved base s.gpr t'.mem from ht.mem ▸ tv).outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show Outside base 0 8192 t'.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega_using [h]) (by simp only [X3, slot]; omega_using [h])).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): loading the scalar argument

Scratch-only setup leaves the scalar pointer and input bytes available for
expansion.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

theorem bits_ok {s₀ s : State} (pre : Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hm : Outside base 0 8192 s₀.mem s.mem) (hs : Scr s base)
    (hkd : ∀ i < 56, 8192 ≤ ofs base (off ((arg s₀ 1).setWidth 64) i)) :
    WP isa bits s fun t =>
      Keeps bitRegs s t ∧ Outside base BITS 448 s.mem t.mem ∧
      ∀ j < 448, t.mem (off base (BITS + j)) =
        BitVec.ofNat 8 (bit (Spec.X448.decodeScalar448
          (Spec.X448.bytesAt s.mem ((arg s₀ 1).setWidth 64) 56)) j) := by
  unfold bits
  refine WP.seq (loadArg_ok pre hsp hr hw (XFrame.of_outside (hbase ▸ hm)) (by decide : 1 < 4)
    fun u hu => WP.block_nil ?_)
  refine WP.mono (bitsData_ok (hs.of_upd hu (by decide)) (by rw [hu.gpr])
    (by rw [hu.gpr]; exact pre.scalar_fit)
    (by intro i hi; rw [hu.rd, hu.wr, hr, hw]; exact ⟨scalarR s₀,
      by rw [pre.rd]; simp, Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])⟩)
    hkd) fun t ⟨tk, tm, tb⟩ => ?_
  rw [hu.mem] at tm tb
  exact ⟨(hu.rest (by decide)).trans tk, tm, tb⟩

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): all 448 ladder iterations

A decreasing public counter connects the loop to the specification's
descending fold over scalar bits.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

/-- The ladder's loop, from the counter `n ≥ 1` down to 0. -/
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → LInv base k u s₀ s n →
      WP isa (.loop step .ne) s fun s' => LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := step) (c := .ne)
    (Q := fun s' => LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega_using [h1]⟩
  refine WP.mono (step_ok (by omega_using [h2]) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, hz, Option.map_some]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega_using [hm] : ¬m = 0), Bool.not_false], m, by omega_using [],
      by omega_using [hm], by omega_using [h2], hi'⟩

/-- The ladder: the counter set to 448, then the loop. -/
theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : ∀ s', s'.gpr .esi = BitVec.ofNat 32 448 → (∀ r, r ≠ .esi → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → LInv base k u s₀ s' 448) :
    WP isa ladder s fun s' => LInv base k u s₀ s' 0 := by
  refine WP.seq (WP.mono (setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => loop_ok hbits 448 s' (by omega_using []) (by omega_using []) (hi s' h1 h2 h3 h4 h5))

end VG.Proof.X448.X86

end

end

/-! ### `X448.X86.Finish`, which the modules that import this one used -/

section

/-!
# X448 on x86 (32-bit): the result and restored registers

The final multiplication, canonical reduction and encoding produce the affine
coordinate. The four callee-saved registers are then restored from the
disjoint working space.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def finishRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem finish_ok {s₀ s : State} (pre : Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hm : XFrame s₀ s.mem)
    (hs : Scr s base) (hc : CallCtx s base) (hb : BoundedEnv s.mem base)
    (hfar : ∀ j < 8192, 56 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j))
    (sv : Saved base s₀.gpr s.mem) :
    WP isa finish s fun t =>
      (∀ p ∈ savedSlots, t.gpr p.1 = s₀.gpr p.1) ∧ Keeps finishRegs s t ∧
      Frame [⟨base, 8192⟩, outR s₀, callStk s] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem ((arg s₀ 0).setWidth 64) 56 =
        Spec.X448.encodeUCoordinate (E s.mem base 1 * E s.mem base 21) := by
  refine WP.seq (WP.mono (mulCall_ok hs hc (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.keeps (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  have frames : Frame [⟨base, 8192⟩, outR s₀, callStk s] s.mem v.mem :=
    (uk.ext.mono (by simp)).trans ((vm.whole (by decide)).frame.mono (by simp))
  have stk : callStk s = stkR s₀ := by
    simp only [callStk, below, hsp]
    rw [VG.X86.Taint.sub_setWidth pre.sp_room]
  have frame0 : XFrame s₀ v.mem := hm.trans (frames.mono (by rw [stk, ← hbase]; simp))
  have ksv := uk.keeps.then vk
  have hvsp : v.gpr .esp = s₀.gpr .esp := (ksv.1 _ (by decide)).trans hsp
  have hvrd : v.rd = s₀.rd := ksv.2.1.trans hr
  have hvwr : v.wr = s₀.wr := ksv.2.2.trans hwr
  refine loadArg_ok pre hvsp hvrd hvwr frame0 (by decide : 0 < 4) fun v' hv => ?_
  have vs' := vs.of_upd hv (by decide)
  change WP isa (.block ((List.range 28).flatMap packLimb ++ restore)) v' _
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs' (hv.mem ▸ vb) (by rw [hv.gpr])
    (by rw [hv.gpr]; exact pre.out_fit)
    (by intro j hj; rw [hv.wr, hvwr]; exact ⟨outR s₀, pre.out_in,
      Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])⟩) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs'.of_keeps wk (by decide)
  have svv := (sv.wsfield uk.mem (by decide)).field vm (by decide)
  have svw : Saved base s₀.gpr w.mem := svv.of_readW fun p hp => by
    have := savedSlots_bound p hp
    rw [← hv.mem]; exact output_word wm (by decide) (by omega_using [this]) hfar
  refine WP.mono (restore_ok ws svw) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, (uk.keeps.mono ?_).trans ((vk.mono ?_).trans ((hv.rest (by decide)).trans ((wk.mono ?_).trans (tk.mono ?_)))), ?_, ?_⟩
  · decide
  · intro r hr; simp only [workRegs, clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [restoreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [tm]
    rw [hv.mem] at wm
    exact frames.trans (wm.frame.mono (by simp [outR]))
  · rw [tm, wv, hv.mem, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.X86

end

end

/-!
# X448 on x86 (32-bit): the final ladder swap

The last swap bit selects the coordinates that are converted back to affine
form.
-/

@[expose] public section

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem mask_of : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block [ld .ecx SWAP, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)]) s
      fun t => t.gpr .ebx = mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ Keeps [.ecx, .ebx] s t := by
  refine load_ok hs (by decide) fun s1 h1 => ?_
  refine wp_mov rfl fun s2 h2 => ?_
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun s3 h3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .ebx - s2.gpr .ecx = _
    rw [h2.gpr, h2.other .ecx (by decide), h1.gpr, hw]
    exact mask_of sw hsw
  · rw [h3.mem, h2.mem, h1.mem]
  · exact (h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide)))

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block lastSwap) s fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = opSwap 2 4 (decide (sw = 1)) (opSwap 1 3 (decide (sw = 1)) (E s.mem base)) := by
  rw [lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ WsOut2.refl _ _ _ _ _ _⟩
  refine WP.mono (swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.X86
