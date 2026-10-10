import VerifiedGarbage.Proof.X448.X86_64.Pow223
import VerifiedGarbage.Proof.X448.X86_64.Lit
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.X448.Field64

/-!
# X448 on x86-64: `vg_gf448_r64_pow223`, verified

The facts of `Spec.X448.Field64.pow223Contract` on x86-64 (`pow64`: `ws` in
`rdi`), which `pow223Fn` meets (`pow223Fn_ok`): the callee-saved registers
are restored, and every byte it writes is in `[960, 1648)` of `ws`, which the
return address is apart from; the slots' values are `c222` and `c223` of slot
12's, the powers `2^222 - 1` and `2^223 - 1` (`c222_eq`, `c223_eq`).
Constant time by taint tracking (only `rsp` and `ws` are public), and a state
satisfying the precondition.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448
open VG.Spec.X448.Field64 (valAt aAt eAt oAt)

/-- `vg_gf448_r64_pow223(ws = rdi)`. -/
def pow64 : Contract isa where
  pre s := s.rd = [] ∧ s.wr = [⟨s.gpr .rdi, 8192⟩] ∧
    (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 8192⟩ ∧ (s.gpr .rdi).toNat + 8192 ≤ 2 ^ 64
  post s s' :=
    valAt s'.mem (s.gpr .rdi) oAt % Spec.X448.P =
        valAt s.mem (s.gpr .rdi) aAt ^ (2 ^ 223 - 1) % Spec.X448.P ∧
      valAt s'.mem (s.gpr .rdi) eAt % Spec.X448.P =
        valAt s.mem (s.gpr .rdi) aAt ^ (2 ^ 222 - 1) % Spec.X448.P ∧
      Spec.X448.Field64.Keeps (s.gpr .rdi) s.mem s'.mem
  pub s₁ s₂ := s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi

theorem mv_eq_wordsVal (m : Mem) (base : Addr) : ∀ d k, mv m base d k = Mont.wordsVal m base d k
  | _, 0 => rfl
  | d, k + 1 => by rw [mv, Mont.wordsVal, mv_eq_wordsVal m base (d + 8) k]

/-- The spec's element at `o` is the slot's seven words. -/
theorem valAt_eq (m : Mem) (base : Addr) (o : Nat) : valAt m base o = fe m base o := by
  show valAt m base o = mv m base o 7
  rw [mv_eq_wordsVal, ← Mont.read_eq_wordsVal]
  rfl

/-- A slot's residue, from its field element. -/
theorem valAt_mod (m : Mem) (base : Addr) (i : Index) :
    valAt m base (slot i.val) % Spec.X448.P = (E m base i).val := by
  rw [valAt_eq]; rfl

theorem pw_val (z : Spec.X448.Fe) (e : Nat) (x : Nat) (hz : z.val = x % Spec.X448.P) :
    (pw z e).val = x ^ e % Spec.X448.P := by
  rw [pw, Fin.val_ofNat, hz, ← Nat.pow_mod]

theorem pow223_x64 (s : State) (hs : pow64.pre s) :
    ∃ t s', Exec isa pow223Fn s t s' ∧ abiPreserved s s' ∧ pow64.post s s' := by
  obtain ⟨hrd, hwr, hret, hnw⟩ := hs
  have hscr : Scr s (s.gpr .rdi) := ⟨rfl, by rw [hwr]; simp, hnw⟩
  suffices hwp : WP isa pow223Fn s fun s' => gprPreserved s s' ∧ pow64.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he hg, hp⟩
  refine WP.mono (pow223Fn_ok hscr) fun s' ⟨hg, _, _, hm, he⟩ => ?_
  have ha := (valAt_mod s.mem (s.gpr .rdi) 12).symm
  refine ⟨⟨fun r hr => hg r (by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide), ?_⟩, ?_, ?_, ?_⟩
  · refine Mem.readW_congr fun i hi => hm _ (Or.inr ?_)
    have hx := hret (s.gpr .rsp + BitVec.ofNat 64 i) (by
      simp only [Region.Contains]; rw [Mem.sub_ofNat_toNat _ (by omega)]; omega)
    simp only [Region.Contains, Nat.not_le] at hx
    simp only [ofs]; omega
  · rw [show oAt = slot (21 : Index).val from rfl, show aAt = slot (12 : Index).val from rfl, valAt_mod,
      he, chainEnv_21, c223_eq, pw_val _ _ _ ha]
  · rw [show eAt = slot (20 : Index).val from rfl, show aAt = slot (12 : Index).val from rfl, valAt_mod,
      he, chainEnv_20, c222_eq, pw_val _ _ _ ha]
  · intro i hi hown
    simp only [Spec.X448.Field64.wsBytes, Spec.X448.Field64.ownAt, Spec.X448.Field64.ownEnd,
      Spec.X448.Field64.slotAt] at hi hown
    exact hm _ (by rw [ofs_off' _ (by omega)]; omega)

theorem pow223_ct : ConstantTime isa pow64.pre pow64.pub pow223Fn := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h0, h1⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h1
  · exact h0

/-- A state satisfying the precondition. -/
def powSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 8192⟩]

theorem pow223_verified :
    Verified X86_64.target pow223Fn (Spec.X448.Field64.pow223Contract X86_64.abi) :=
  Verified.of_correct pow223_x64 pow223_ct (by
    sig_implies [Spec.X448.Field64.pow223Contract, Spec.X448.Field64.sig, X86_64.abi, X86_64.argRegs,
      pow64] [powSat] using powSat)

end VG.Proof.X448.X86_64
