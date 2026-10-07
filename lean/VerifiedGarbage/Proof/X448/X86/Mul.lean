import VerifiedGarbage.Proof.X448.X86.MulLoop
import VerifiedGarbage.Proof.X448.X86.Reduce
import VerifiedGarbage.Proof.X448.X86.FnCtx

/-!
# X448 on x86 (32-bit): field multiplication

`vg_gf448_r16_mul`'s product (`Impl/X448/X86.lean`, `mulFn`): `esi` points
at `b`, and the row loop (`mulLoopWith_ok`) reads `a_i` at `ws + a + 4 i`,
from the offset `a` on the stack and the row pointer (`mulCode`), producing
the 56 limbs of the product, which are folded and normalized modulo the
prime into the element at `o` (`mulTail_ok`).
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

/-- The row loop's code reads `a_i` from the offset `a` and the row pointer,
and `b_j` through `esi`. -/
theorem mulCode {s0 : State} {base : Addr} {o a b : Nat} (hc : FnCtx s0 base 4 o a)
    (hb : Slot b) (hp : s0.gpr .esi = s0.gpr .edi + BitVec.ofNat 32 b) {i : Nat} (hi : i < 28) :
    RowCode base a b s0 i mulA (fun j => at_ .esi (4 * j)) := by
  have ha' : a + 112 ≤ 3584 := hc.slotA
  have hb' : b + 112 ≤ 3584 := hb
  refine ⟨fun s h => ?_, fun j hj s hs hk => ?_⟩
  · have sc : FnCtx s base 4 o a := hc.keep h.regs (by decide) (by decide)
      (h.mem.mono (by decide) (by decide))
    unfold mulA
    refine sc.args.load (by decide) fun u hu => wp_alu (Or.inl rfl) rfl fun v hv _ => ?_
    have us := sc.scr.of_upd hu (by decide)
    have vs := us.of_upd hv (by decide)
    have vp : v.gpr .ecx = v.gpr .edi + BitVec.ofNat 32 (4 * i + a) := by
      rw [hv.gpr, hv.other .edi (by decide)]
      change u.gpr .ecx + u.gpr .ebp = _
      rw [hu.gpr, sc.argA, hu.other .ebp (by decide), hu.other .edi (by decide)]
      exact ofNat_add_edi h.ptr
    refine wp_load (vs.ea_ptr vp (by omega)) (vs.read (by omega)) fun w hw => WP.block_nil ⟨?_, ?_, ?_⟩
    · rw [hw.gpr, hv.mem, hu.mem, Nat.add_zero, Nat.add_comm]
    · exact (hu.rest (by decide)).trans ((hv.rest (by decide)).trans (hw.rest (by decide)))
    · rw [hw.mem, hv.mem, hu.mem]
  · have e : s.gpr .esi = s.gpr .edi + BitVec.ofNat 32 b := by
      rw [hk.1 _ (by decide), hk.1 _ (by decide)]; exact hp
    exact hs.ea_ptr e (by omega)

/-- `esi = ws + b`, the accumulator zeroed and the row pointer at `ws`. -/
theorem mulSetup_ok {s : State} {base : Addr} {o a b : Nat} (hc : FnCtx s base 4 o a)
    (hvb : arg s 3 = BitVec.ofNat 32 b) :
    WP isa (.block (argPtr .esi 3 ++ mulPre)) s fun t =>
      ∃ s0, RowInv base a b s0 0 t ∧ s0.gpr .esi = s0.gpr .edi + BitVec.ofNat 32 b ∧
        Keeps [.esi] s s0 ∧ s0.mem = s.mem := by
  rw [WP.block_append_iff]
  refine WP.mono (argPtr_ok hc.args (by decide) (by decide) hvb) fun s0 ⟨p0, m0, k0⟩ => ?_
  exact WP.mono (mulPre_ok (hc.scr.of_keeps k0 (by decide)) a b) fun t ht => ⟨s0, ht, p0, k0, m0⟩

/-- The rows, from `RowInv base a b s0 0`. -/
theorem mulRows_ok {s0 t : State} {base : Addr} {o a b : Nat} (hc : FnCtx s0 base 4 o a)
    (hb : Slot b) (hp : s0.gpr .esi = s0.gpr .edi + BitVec.ofNat 32 b)
    (ab : Bounded s0.mem base a) (bb : Bounded s0.mem base b) (ht : RowInv base a b s0 0 t) :
    WP isa (.loop (.block mulRow) .ne) t (RowInv base a b s0 28) :=
  mulLoopWith_ok hc.slotA hb ab bb (fun _ hi => mulCode hc hb hp hi) ht

/-- The product folded and normalized into the element at `o`. -/
theorem mulTail_ok {s0 u : State} {base : Addr} {o a b : Nat} (hc : FnCtx s0 base 4 o a)
    (hu : RowInv base a b s0 28 u) :
    WP isa (.block ((List.range 28).flatMap reduceCol ++ normalize)) u fun w =>
      FieldMem base o u.mem w.mem WORK ∧ Bounded w.mem base o ∧
      F w.mem base o = F s0.mem base a * F s0.mem base b ∧ Keeps [.eax, .ebx, .edx, .ebp] u w := by
  have uk := hu.regs
  have us := hu.scr
  let f := limbs u.mem base ACC
  have fb : ∀ i < 56, f i < radix := hu.lt
  have fv : valN f 56 = fe s0.mem base a * fe s0.mem base b := hu.val
  have uc : FnCtx u base 4 o a := hc.keep uk (by decide) (by decide) (hu.mem.mono (by decide) (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok us (fun _ _ => rfl) fb) fun v ⟨vf, vm, vk⟩ => ?_
  have vc : FnCtx v base 4 o a := uc.keep vk (by decide) (by decide) (vm.mono (by decide) (by decide))
  refine WP.mono (normalize_ok vc.scr vc.args (by decide) vc.slotO vc.argO vf (reduced_bound fb))
    fun w ⟨wf, wm, wk⟩ => ?_
  have value : fe w.mem base o % Spec.X448.P = (fe s0.mem base a * fe s0.mem base b) % Spec.X448.P := by
    rw [show fe w.mem base o = valN (normalized (reduced f)) 28 from valN_congr wf,
      normalized_mod (reduced_bound fb), reduced_mod, fv]
  refine ⟨(FieldMem.work vm (by decide) (by decide)).trans wm, ?_, toFe_mul value,
    (vk.mono (by decide)).trans wk⟩
  intro i hi
  rw [wf i hi]
  exact digit_lt _ _

end VG.Proof.X448.X86
