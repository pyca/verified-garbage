module
-- separate module: the argument copies, rebuilt only when they change

public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Body
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # `vg_rsa_private_precompute` on x86: its callees' arguments

`copyArgument i j` copies argument `i` to the callee's argument `j`, at
`slot s (4 j)` (`wp_copyArg`); `copies l` does so for the pairs of `l`,
whose callee's arguments are distinct (`wp_copies`).
-/

@[expose] public section
namespace VG.Proof.Bignum.X86.PrivPre
open VG VG.X86 VG.X86.Wp VG.Proof.Mont.X86
open VG.Impl.Bignum.X86.PrivPre (copyArgument copies)

section
variable {s t : State} {is : List Instr} {Q : State → Prop}

/-- The callee's argument `j`'s region. -/
abbrev argR (s : State) (j : Nat) : Region := ⟨slot s (4 * j), 4⟩

theorem argR_apart {j j' : Nat} (h : j ≠ j') (hj : 4 * j + 4 ≤ 96) (hj' : 4 * j' + 4 ≤ 96) :
    (argR s j).Disjoint (argR s j') :=
  Offset.disjoint _ (by omega) (by omega) (by omega)

theorem wp_copyArg (A : PPABI s) (B : Body s t) {i j : Nat} (hi : i < 10) (hj : 4 * j + 4 ≤ 96)
    (k : ∀ u, Body s u → Keeps [.eax] t u → Frame [argR s j] t.mem u.mem →
      u.mem.readW (slot s (4 * j)) 32 = arg s i → WP isa (.block is) u Q) :
    WP isa (.block (copyArgument i j ++ is)) t Q := by
  simp only [copyArgument, List.cons_append, List.nil_append]
  refine wp_movS (B.readArg A hi) fun u₁ U₁ _ => ?_
  have B₁ : Body s u₁ :=
    B.next (U₁.other _ (by decide)) U₁.rd U₁.wr (by rw [U₁.mem]; exact Frame.refl _ _)
  refine wp_slot A B₁ hj fun u₂ B₂ M => k u₂ B₂ ⟨fun r hr => ?_, by rw [M.rd, U₁.rd], by rw [M.wr, U₁.wr]⟩ ?_ ?_
  · rw [M.gpr, U₁.other _ (by simpa using hr)]
  · rw [M.mem, U₁.mem]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  · rw [M.mem, Mem.readW_writeW_self32, U₁.gpr]

theorem wp_copies (A : PPABI s) : ∀ (l : List (Nat × Nat)) {t : State}, Body s t →
    (∀ p ∈ l, p.1 < 10 ∧ 4 * p.2 + 4 ≤ 96) → (l.map (·.2)).Nodup →
    (∀ u, Body s u → Keeps [.eax] t u → Frame (l.map fun p => argR s p.2) t.mem u.mem →
      (∀ p ∈ l, u.mem.readW (slot s (4 * p.2)) 32 = arg s p.1) → WP isa (.block is) u Q) →
    WP isa (.block (copies l ++ is)) t Q
  | [], t, B, _, _, k => by
    simpa [copies] using k t B (Keeps.refl _ _) (Frame.refl _ _) (by simp)
  | p :: l, t, B, hl, hn, k => by
    rw [copies, List.flatMap_cons, List.append_assoc]
    have hp := hl p (List.mem_cons_self ..)
    have hn' := List.nodup_cons.mp hn
    refine wp_copyArg A B hp.1 hp.2 fun u₁ B₁ K₁ F₁ V₁ => ?_
    refine wp_copies A l B₁ (fun q hq => hl q (List.mem_cons_of_mem _ hq)) hn'.2
      fun u B' K F V => k u B' (K₁.trans K) ?_ fun q hq => ?_
    · exact (F₁.mono fun r hr => by simp only [List.mem_singleton] at hr; simp [hr]).trans
        (F.mono fun r hr => List.mem_cons_of_mem _ hr)
    · rcases List.mem_cons.mp hq with rfl | hq
      · refine (F.readW (r := argR s q.2) (Region.contains_self _ _) (fun r hr => ?_) (by decide)).trans V₁
        obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
        have hql := hl q' (List.mem_cons_of_mem _ hq')
        refine argR_apart (fun e => hn'.1 ?_) hp.2 hql.2
        exact List.mem_map.mpr ⟨q', hq', e.symm⟩
      · exact V q hq

end
end VG.Proof.Bignum.X86.PrivPre
