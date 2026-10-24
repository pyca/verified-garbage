module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.Whole.Hash
public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.Frame
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Ed448's whole functions on PPC64LE: the setup

As Ed25519's on this target (`Proof/Ed25519/PPC64LE/Whole/Frame.lean`,
whose invariant `Inv` they share): the registers `rs` and the link register
saved at `o(F)`, then the arguments moved into `rs` (`setup_ok`, by
`movs_ok`); a hash, or any step that keeps the callee-saved registers and
writes within the body's regions, apart from the slots, keeps `Inv`
(`Inv.kept`).
-/

@[expose] public section

namespace VG.Proof.Ed448.PPC64LE.Whole

open VG VG.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Impl.Ed25519.PPC64LE.Whole (mov saveRegs restoreRegs slots)
open VG.Proof.Ed25519.PPC64LE.Whole (Inv slotArea save_ok saveG)

/-- `mov`s from registers that none of them writes, to distinct registers. -/
theorem movs_ok : ∀ (ms : List (Reg × Reg)) {s : State} {rest : List Instr} {Q : State → Prop},
    (∀ p ∈ ms, p.2 ≠ .r0 ∧ p.2 ∉ ms.map Prod.fst) → (ms.map Prod.fst).Nodup →
    (∀ u, u.mem = s.mem → u.rd = s.rd → u.wr = s.wr → u.sp = s.sp →
      (∀ p ∈ ms, u.gpr p.1 = s.gpr p.2) → (∀ r, r ∉ ms.map Prod.fst → u.gpr r = s.gpr r) →
      WP isa (.block rest) u Q) →
    WP isa (.block (ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  intro ms
  induction ms with
  | nil => exact fun _ _ k => k _ rfl rfl rfl rfl (fun _ h => absurd h List.not_mem_nil) fun _ _ => rfl
  | cons p ms ih =>
    intro s rest Q hs hn k
    obtain ⟨d, n⟩ := p
    have hn' := List.nodup_cons.mp hn
    have h0 := hs (d, n) List.mem_cons_self
    simp only [List.map_cons, List.cons_append]
    refine wp_addi h0.1 (by decide) fun u hu => ih (fun q hq => ⟨(hs q (List.mem_cons_of_mem _ hq)).1,
      fun h => (hs q (List.mem_cons_of_mem _ hq)).2 (List.mem_cons_of_mem _ h)⟩) hn'.2
      fun u' m' rd' wr' sp' hm ho => k u' (m'.trans hu.mem) (rd'.trans hu.rd) (wr'.trans hu.wr) (sp'.trans hu.sp)
        (fun q hq => ?_) fun r hr => ?_
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hn'.1, hu.gpr, BitVec.add_zero]
      · have hq2 : q.2 ≠ d := fun e => (hs q (List.mem_cons_of_mem _ hq)).2 (e ▸ List.mem_cons_self)
        rw [hm q hq, hu.other _ hq2]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, hu.other r hr.1]

/-- The saves at `o(F)` (`F` in `f`), then the moves `ms` into the registers `rs`, which hold `v`: the
invariant holds after them. -/
theorem setup_ok {s : State} {f : Reg} {o : Nat} {rs : List Reg} {ms : List (Reg × Reg)} {v : Reg → BitVec 64}
    {W : List Region} {rest : List Instr} {Q : State → Prop} (hf0 : f ≠ .r0)
    (hfits : Spill.Fits (slots o rs)) (hlo : o + 8 * (rs.length + 1) < 2 ^ 64)
    (hin : ∀ p ∈ slots o rs, InRegions s.wr (s.gpr f + BitVec.ofNat 64 p.2) 8)
    (hW : ∃ R ∈ W, Region.Sub (slotArea (s.gpr f) o rs) R) (hms : ms.map Prod.fst = rs)
    (hsrc : ∀ p ∈ ms, p.2 ≠ .r0 ∧ p.2 ∉ rs) (hnd : rs.Nodup) (hv : ∀ p ∈ ms, v p.1 = s.gpr p.2)
    (k : ∀ u, Inv s (s.gpr f) o rs v W u → WP isa (.block rest) u Q) :
    WP isa (.block (saveRegs f o rs ++ ms.map (fun p => mov p.1 p.2) ++ rest)) s Q := by
  rw [List.append_assoc]
  refine save_ok hf0 hfits hlo hin fun u hu _ hsv hfr => ?_
  refine movs_ok ms (fun p hp => ⟨(hsrc p hp).1, hms ▸ (hsrc p hp).2⟩) (hms ▸ hnd)
    fun u' m' rd' wr' sp' hm ho => k u' ⟨rd'.trans hu.rd, wr'.trans hu.wr, sp'.trans hu.sp, fun r hr => ?_,
      fun r hr hn => ?_, m' ▸ hsv, m' ▸ hfr.sub fun x hx => by
        rw [List.mem_singleton.mp hx]; exact hW⟩
  · rw [← hms] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    rw [hm p hp, hv p hp, hu.gpr _ (by simpa using (hsrc p hp).1)]
  · rw [ho r (hms ▸ hn), hu.gpr _ (by simpa using fun e => (by revert hr; rw [e]; decide : False))]

/-- A step that keeps the callee-saved registers, writing within `W` and apart from the slots. -/
theorem Inv.kept {s t t' : State} {F : Addr} {o : Nat} {rs : List Reg} {v : Reg → BitVec 64} {W Wc : List Region}
    (h : Inv s F o rs v W t) (hrs : ∀ r ∈ rs, r ∈ preserved) (hk : Kept Wc t t')
    (hsub : ∀ r ∈ Wc, ∃ R ∈ W, Region.Sub r R) (hd : ∀ r ∈ Wc, Region.Disjoint (slotArea F o rs) r) :
    Inv s F o rs v W t' :=
  h.step hrs hk.rd hk.wr hk.sp hk.cs hk.frame hsub hd

end VG.Proof.Ed448.PPC64LE.Whole
