module

public import VerifiedGarbage.Proof.Rc4.RISCV64.Lookup
public import VerifiedGarbage.Spec.Rc4
import VerifiedGarbage.Proof.Framework.RISCV64.Wp
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Rc4.Memory
import VerifiedGarbage.Proof.Rc4.Table

/-! # RC4 on RISC-V: the table in the frame

The table is kept in a frame on the stack, copied there from the context
(`table_copy`), and the frame is zeroed before returning (`wipe_ok`). -/

@[expose] public section

namespace VG.Proof.Rc4.RISCV64
open VG VG.RISCV64 VG.Impl.Rc4.RISCV64 VG.Spec.Rc4 VG.Proof.Rc4

/-- A table copied byte for byte. -/
theorem table_copy {m m' : Mem} {p q : Addr}
    (h : ∀ k < 256, m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) :
    (contextAt m' q).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  exact h k hk

/-- The context, from its table and its two indices. -/
theorem context_of {m : Mem} {p : Addr} {c : Context} (ht : (contextAt m p).table = c.table)
    (hi : m (p + 256#64) = c.i) (hj : m (p + 257#64) = c.j) : contextAt m p = c :=
  context_ext ht hi hj

/-- The bytes of the context at `p` lie outside a region separate from it. -/
theorem ctx_byte {p : Addr} {R : Region} (hs : Mem.Sep R.base R.len p 258) {k : Nat} (hk : k < 258) :
    ∀ r ∈ [R], ¬ r.Contains (p + BitVec.ofNat 64 k) 1 := by
  intro r hr hc
  simp only [List.mem_singleton] at hr
  subst hr
  exact hs (p + BitVec.ofNat 64 k) (by simp only [Region.Contains] at hc; omega)
    (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hk)

/-- The doublewords of the frame zeroed. -/
theorem wipe_ok (s : State) (hal : (s.gpr .a7).toNat % 8 = 0)
    (hw : InRegions s.wr (s.gpr .a7) 256) :
    WP isa (.block wipe) s fun t => Frame [⟨s.gpr .a7, 256⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hw' : wipe = (List.range 32).flatMap fun k => [.store .d .t6 .a7 (8 * k)] := by
    rfl
  rw [hw']
  refine wp_range_flatMap (M := isa) (fun _ t => Frame [⟨s.gpr .a7, 256⟩] s.mem t.mem ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp) (fun k t hk h => ?_) 32
    (Nat.le_refl _) s ⟨Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  obtain ⟨hf, hg, hrd, hwr, hsp⟩ := h
  refine Wp.wp_sd (a := s.gpr .a7 + BitVec.ofNat 64 (8 * k)) (by omega) (by rw [hg])
    (al_add hal (by omega) (by omega))
    (by rw [hwr]; exact region_offset _ _ _ _ _ (by omega) (by omega) hw) fun u hu =>
    WP.block_nil ⟨?_, hu.gpr.trans hg, hu.rd.trans hrd, hu.wr.trans hwr, hu.sp.trans hsp⟩
  rw [hu.mem]
  exact hf.writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))

end VG.Proof.Rc4.RISCV64
