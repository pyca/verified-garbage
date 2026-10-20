module
public import VerifiedGarbage.Proof.Rsa.X86.RvMontGeometry


/-! # Memory and register frames of recovery's Montgomery products -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

abbrev montWrites (o : Nat) : List Nat := [o, mTmp, mAcc, mAcc + 1]

theorem mont_frame {g : Geo} {m m' : Mem} {o : Nat}
    (k : Outs g.B [(arr g.w o, 8 * g.n), (arr g.w mTmp, 8 * g.n),
      (arr g.w mAcc, accLen (montMod g.n))] m m') :
    Keep g.B g.w (montWrites o) [] m m' := by
  intro x hx
  apply k x
  have outside (j : Nat) (hj : j ∈ montWrites o) :=
    hx (arr g.w j, S g.w) (by simp only [ranges, List.mem_append, List.mem_map]; exact .inl ⟨j, hj, rfl⟩)
  have outO := outside o (by simp [montWrites])
  have outT := outside mTmp (by simp [montWrites])
  have outA := outside mAcc (by simp [montWrites])
  have outA1 := outside (mAcc + 1) (by simp [montWrites])
  rw [arr_succ] at outA1
  have acc : accLen (montMod g.n) ≤ 2 * S g.w := by
    simp only [accLen, montMod, VG.Impl.Mont.X86.words, S, Geo.w, width]; omega
  have wordSize : 8 * g.n ≤ S g.w := by change 8 * g.n ≤ 4 * (2 * g.n + 2 + 2); omega
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> dsimp only at * <;> omega

theorem mont_keep {g : Geo} {s t : State} {o : Nat}
    (k : OpKeep (montMod g.n) g.B (arr g.w mAcc) (arr g.w o) s t) :
    Keep g.B g.w (montWrites o) [] s.mem t.mem := mont_frame k.mem

theorem mont_rest {g : Geo} {s t : State} {o : Nat}
    (k : OpKeep (montMod g.n) g.B (arr g.w mAcc) (arr g.w o) s t) : Keeps opRegs s t :=
  (show Keeps clob s t from ⟨k.gpr, k.rd, k.wr⟩).mono (by decide)

theorem MR.keep {g : Geo} {m : Nat} {s t : State} (h : MR g m s)
    {js : List Nat} (k : Keep g.B g.w js [] s.mem t.mem)
    (hj : ∀ j ∈ js, j ≠ mBase) (r : Keeps opRegs s t) : MR g m t := by
  refine ⟨h.ws.rest r, h.positive, ?_, h.bound, ?_⟩
  · rw [k.num hj (by simp) (h.ws.fit64 (by decide)), h.modulus]
  · change (m * slot t.mem g.B sInv + 1) % 2 ^ 32 = 0
    rw [k.slot (e := sInv) (by decide) (by simp)]; exact h.inverse

end VG.Proof.Rsa.X86.Recover
