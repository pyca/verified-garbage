import VerifiedGarbage.Proof.X448.AArch64.Init
import VerifiedGarbage.Proof.X448.AArch64.BitWrite
import VerifiedGarbage.Impl.Ed448.AArch64.VerifyWindow

/-!
# Ed448 verification on AArch64: the challenge copied

Untrusted: everything here is checked by Lean. The entry copies the
challenge's 57 bytes (at `x2`) to `KB` in the working space, byte by byte
(`copyK_ok`), so that the windows read them at addresses from public
registers.
-/

namespace VG.Proof.Ed448.AArch64.Window

open VG VG.AArch64 VG.Impl.Ed448.AArch64
open VG.Proof.X448.AArch64 (Scr Keeps off word Outside ofs write1_eq writeW8_apply read1_eq)

private theorem byte_rt : ∀ b : BitVec 8,
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by decide +kernel

theorem ofs_off0' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d := by
  have := VG.Proof.X448.AArch64.ofs_off base (d := d) (i := 0) (by omega)
  simpa only [BitVec.add_zero, Nat.add_zero] using this

theorem copyByte_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p) {i : Nat} (hi : i < 57)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1) :
    WP isa (.block [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)]) s fun t =>
      t.mem = s.mem.writeW (off base (KB + i)) (s.mem (p + BitVec.ofNat 64 i)) ∧ Keeps [.x4] s t := by
  have w := hs.write (d := KB + i) (n := 1) (by simp only [KB]; omega)
  have e1 : i % 1 = 0 ∧ i < 4096 := ⟨Nat.mod_one _, by omega⟩
  have e2 : (KB + i) % 1 = 0 ∧ KB + i < 4096 := ⟨Nat.mod_one _, by simp only [KB]; omega⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits, addr, e1, e2, and_self,
    hp, hs.x3, State.load, hr, read1_eq, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    off, State.store, w, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    write1_eq, byte_rt, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- **The challenge copied** to `KB`: only those 57 bytes change. -/
theorem copyK_ok {s : State} {base p : Addr} (hs : Scr s base) (hp : s.gpr .x2 = p)
    (hr : ∀ i < 57, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hfar : ∀ i < 57, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    WP isa (.block ((List.range 57).flatMap fun i => [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)])) s fun t =>
      (∀ i < 57, t.mem (off base (KB + i)) = s.mem (p + BitVec.ofNat 64 i)) ∧
      Outside base KB 57 s.mem t.mem ∧ Keeps [.x4] s t := by
  suffices h : ∀ k ≤ 57, WP isa (.block ((List.range k).flatMap fun i =>
      [.ldrb .x4 .x2 i, .strb .x4 .x3 (KB + i)])) s fun t =>
      (∀ i < k, t.mem (off base (KB + i)) = s.mem (p + BitVec.ofNat 64 i)) ∧
      Outside base KB 57 s.mem t.mem ∧ Keeps [.x4] s t from h 57 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact WP.block_nil ⟨fun i hi => absurd hi (Nat.not_lt_zero _), Outside.refl _ _ _ _, Keeps.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun t ⟨t1, t2, kt⟩ => ?_
    have ht : Scr t base := hs.of_keeps kt (by decide)
    have hn := hs.nowrap
    refine WP.mono (copyByte_ok ht ((kt.1 _ (by decide)).trans hp) (i := k) (by omega)
      (by rw [kt.2.1, kt.2.2]; exact hr k (by omega))) fun u ⟨mu, ku⟩ => ⟨fun i hi => ?_, ?_, kt.trans ku⟩
    · have hsrc : t.mem (p + BitVec.ofNat 64 k) = s.mem (p + BitVec.ofNat 64 k) :=
        t2 _ (Or.inr (by have := hfar k (by omega); simp only [KB]; omega))
      rw [mu, writeW8_apply]
      by_cases hik : i = k
      · subst hik; rw [ite_eq_left rfl, hsrc]
      · rw [ite_eq_right ?_]
        · exact t1 i (by omega)
        · intro h
          have := congrArg (ofs base) h
          rw [ofs_off0' base (by simp only [KB]; omega),
            ofs_off0' base (by simp only [KB]; omega)] at this
          omega
    · rw [mu]
      refine t2.trans fun x hx => ?_
      rw [writeW8_apply, ite_eq_right_iff.mpr]
      intro h; subst h
      rw [ofs_off0' base (by simp only [KB]; omega)] at hx
      omega

end VG.Proof.Ed448.AArch64.Window
