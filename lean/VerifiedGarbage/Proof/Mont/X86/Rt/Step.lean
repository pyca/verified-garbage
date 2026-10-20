module

public import VerifiedGarbage.Proof.Mont.X86.Rt.Base
public import VerifiedGarbage.Proof.Mont.X86.Step
import VerifiedGarbage.Proof.Mont.X86.Mac
import VerifiedGarbage.Proof.Framework.Omega

/-! # One step of a row of the run-time width multiplication

`mulStepAt`: `[ebp] += [edi + mo] · [ecx]` with the carry in `ebx`, both
pointers up a word and the count `esi` down by 4, ZF when it reaches zero.
`macAt` and `pairCtl_ok`: the same for a word at an offset, and the end of a
two-word step.
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Rt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont.X86.Rt VG.Proof.Mont VG.Proof.Mont.X86

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `sub d, src`, and ZF. -/
theorem wp_subZ {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ t, Upd s t d (s.gpr d - v) → t.zf = some (s.gpr d - v == 0) → WP isa (.block is) t Q) :
    WP isa (.block (.alu .sub d src :: is)) s Q :=
  cons (by simp only [exec, execAlu, h, Option.bind_some]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

end

/-- The count down by 4: ZF when it reaches zero. -/
theorem count_zf {x : BitVec 32} {N j : Nat} (hx : x.toNat = 4 * (N - j)) (hj : j < N) :
    (x - 4).toNat = 4 * (N - (j + 1)) ∧ (x - 4 == 0) = decide (j + 1 = N) := by
  have h4 : (x - 4).toNat = 4 * (N - (j + 1)) := by
    rw [BitVec.toNat_sub, hx]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]
    omega
  refine ⟨h4, ?_⟩
  by_cases h : j + 1 = N
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h4]; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hz
    have := congrArg BitVec.toNat hz
    rw [h4] at this
    simp at this
    omega

/-- One step of a row, the multiplier at `[edi + mo]`. -/
theorem mulStepAt_ok {mo : Nat} {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {S bx w j N : Nat}
    (hedi : PtrAt t W .edi S) (hecx : PtrAt t W .ecx (bx + 4 * j)) (hebp : PtrAt t W .ebp (w + 4 * j))
    (hesi : (t.gpr .esi).toNat = 4 * (N - j)) (hj : j < N)
    (hm : S + mo + 4 ≤ L) (hb : bx + 4 * j + 4 ≤ L) (ht : w + 4 * j + 4 ≤ L) :
    WP isa (.block (Rt.mulStepAt mo)) t fun u =>
      u.mem = t.mem.writeW (off W (w + 4 * j)) (BitVec.ofNat 32
        (w32 t.mem W (S + mo) * w32 t.mem W (bx + 4 * j) + (t.gpr .ebx).toNat + w32 t.mem W (w + 4 * j))) ∧
      (u.gpr .ebx).toNat = (w32 t.mem W (S + mo) * w32 t.mem W (bx + 4 * j) + (t.gpr .ebx).toNat +
          w32 t.mem W (w + 4 * j)) / 2 ^ 32 ∧
      PtrAt u W .ecx (bx + 4 * (j + 1)) ∧ PtrAt u W .ebp (w + 4 * (j + 1)) ∧
      (u.gpr .esi).toNat = 4 * (N - (j + 1)) ∧
      u.zf = some (decide (j + 1 = N)) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t u := by
  unfold Rt.mulStepAt
  refine WP.block_append (WP.mono (macWord_ok (output := 0) (input := 0) hw hedi hecx hebp
    hm (by omega) (by omega)) fun v ⟨mv, bv, Kv⟩ => ?_)
  simp only [Nat.add_zero] at mv bv
  refine wp_addS rfl fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_subZ rfl fun u uu zu => WP.block_nil ?_
  have K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t u :=
    (((Kv.mono (by decide)).widen u₁.keeps).widen u₂.keeps).widen uu.keeps
  have cu : s₂.gpr .ecx = t.gpr .ecx + 4 := by
    rw [u₂.other _ (by decide), u₁.gpr, Kv.1 _ (by decide)]
  have pu : s₂.gpr .ebp = t.gpr .ebp + 4 := by
    rw [u₂.gpr, u₁.other _ (by decide), Kv.1 _ (by decide)]
  have su : s₂.gpr .esi = t.gpr .esi := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), Kv.1 _ (by decide)]
  obtain ⟨c₁, c₂⟩ := count_zf hesi hj
  refine ⟨by rw [uu.mem, u₂.mem, u₁.mem, mv], ?_, ?_, ?_,
    by rw [uu.gpr, su]; exact c₁, by rw [zu, su, c₂], K⟩
  · rw [uu.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), bv]
  · rw [PtrAt, uu.other _ (by decide), cu, ptr_add hecx 4]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega
  · rw [PtrAt, uu.other _ (by decide), pu, ptr_add hebp 4]
    rw [show (4 : BitVec 32).toNat = 4 from rfl]; omega

/-- The count down by 8: ZF when it reaches zero. -/
theorem count2_zf {x : BitVec 32} {N j : Nat} (hx : x.toNat = 4 * (N - j)) (hj : j + 2 ≤ N) :
    (x - 8).toNat = 4 * (N - (j + 2)) ∧ (x - 8 == 0) = decide (j + 2 = N) := by
  have h8 : (x - 8).toNat = 4 * (N - (j + 2)) := by
    rw [BitVec.toNat_sub, hx]
    rw [show (8 : BitVec 32).toNat = 8 from rfl]
    omega
  refine ⟨h8, ?_⟩
  by_cases h : j + 2 = N
  · simp only [h, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h8]; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hz
    have := congrArg BitVec.toNat hz
    rw [h8] at this
    simp at this
    omega

/-- `[ebp + d] += [edi + mo] · [ecx + d]` with the carry `ebx`, `ecx` at `c` and `ebp` at `p`. -/
theorem macAt_ok {mo d : Nat} {t : State} {W : Addr} {L : Nat} (hw : Ws t W L) {S c p : Nat}
    (hedi : PtrAt t W .edi S) (hecx : PtrAt t W .ecx c) (hebp : PtrAt t W .ebp p)
    (hm : S + mo + 4 ≤ L) (hb : c + d + 4 ≤ L) (ht : p + d + 4 ≤ L) :
    WP isa (.block (Rt.macAt mo d)) t fun u =>
      u.mem = t.mem.writeW (off W (p + d)) (BitVec.ofNat 32
        (w32 t.mem W (S + mo) * w32 t.mem W (c + d) + (t.gpr .ebx).toNat + w32 t.mem W (p + d))) ∧
      (u.gpr .ebx).toNat = (w32 t.mem W (S + mo) * w32 t.mem W (c + d) + (t.gpr .ebx).toNat +
          w32 t.mem W (p + d)) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] t u := by
  exact macWord_ok hw hedi hecx hebp hm hb ht

/-- The end of a two-word step: both pointers up two words, the count down by 8, ZF when it reaches zero. -/
theorem pairCtl_ok {t : State} {W : Addr} {c p j N : Nat}
    (hecx : PtrAt t W .ecx c) (hebp : PtrAt t W .ebp p)
    (hesi : (t.gpr .esi).toNat = 4 * (N - j)) (hj : j + 2 ≤ N) :
    WP isa (.block [.alu .add .ecx (.imm 8), .alu .add .ebp (.imm 8), .alu .sub .esi (.imm 8)]) t fun u =>
      u.mem = t.mem ∧ PtrAt u W .ecx (c + 8) ∧ PtrAt u W .ebp (p + 8) ∧
      (u.gpr .esi).toNat = 4 * (N - (j + 2)) ∧ u.zf = some (decide (j + 2 = N)) ∧
      Keeps [.ecx, .ebp, .esi] t u := by
  refine wp_addS rfl fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_subZ rfl fun u u₃ z₃ => WP.block_nil ?_
  have esi₂ : s₂.gpr .esi = t.gpr .esi := by rw [u₂.other _ (by decide), u₁.other _ (by decide)]
  obtain ⟨c₁, c₂⟩ := count2_zf hesi hj
  refine ⟨by rw [u₃.mem, u₂.mem, u₁.mem], ?_, ?_, by rw [u₃.gpr, esi₂]; exact c₁, by rw [z₃, esi₂, c₂],
    ((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps⟩
  · rw [PtrAt, u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, ptr_add hecx 8]
    rw [show (8 : BitVec 32).toNat = 8 from rfl]
  · rw [PtrAt, u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), ptr_add hebp 8]
    rw [show (8 : BitVec 32).toNat = 8 from rfl]

end VG.Proof.Mont.X86.Rt
