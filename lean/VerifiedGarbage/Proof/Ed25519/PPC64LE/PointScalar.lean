module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.PointMul
import VerifiedGarbage.Proof.X25519.PPC64LE.Mul
public import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Field
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Layout
public import VerifiedGarbage.Proof.X25519.PPC64LE.Field

/-!
# Ed25519 on PPC64LE: the field area cleared, `[S] P` from a scalar's pointer, and `lr`

`initFields_ok`: the slots cleared. `pointFromScalar_ok`: `d` into slot 16 and the product of
the point of slots 0–3 by the `2 count` bytes at `r14`. The link register through `mflr`,
`addi` and `mtlr`, and kept by a block that writes no link register (`WP.keep_lr`); and what
the multiplication writes misses the saved registers' slots (`mulW_saves`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.PPC64LE

open VG VG.PPC64LE VG.Impl.Ed25519.PPC64LE VG.Proof.X25519.PPC64LE
open VG.Spec.Ed25519 (decodeLE bytesAt)

section
variable {b : Addr}

theorem initFields_ok {s : State} (hc : Ctx b s) :
    WP isa (.block initFields) s fun t => Rest [.r7] s t ∧ Frame [FA b] s.mem t.mem := by
  unfold initFields
  refine wp_li (by decide) fun s1 u1 => ?_
  refine WP.mono (stores_ok (r := .r7) (o := 64) (n := 176) (by omega_arith)
    (hc.of_rest (u1.rest (ws := [.r7]) (by decide)) (by decide))) fun t ⟨_, h2, _, h4⟩ =>
      ⟨(u1.rest (by decide)).trans (h4.mono (by decide)), ?_⟩
  rw [← u1.mem]
  exact h2.sub fun r hr => ⟨_, List.mem_singleton_self _, by
    rw [List.mem_singleton.mp hr]; exact Region.sub_prefix (by omega_arith)⟩

theorem env_const16 (e : Env) : point (evalOps [.const 16 Spec.Ed25519.d] e) 0 1 2 3 = point e 0 1 2 3 ∧
    evalOps [.const 16 Spec.Ed25519.d] e 16 = Spec.Ed25519.d := ⟨rfl, rfl⟩

/-- **`[S] P`** for the `2 count` bytes at `r14`. -/
theorem pointFromScalar_ok {s : State} (hc : Ctx8 b s) {count : Nat} (hc1 : 1 ≤ count) (hc32 : count ≤ 32)
    {p : Addr} (h14 : s.gpr .r14 = p) (hin : ∀ i < 2 * count, InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 i) 1)
    (hpd : (⟨p, 2 * count⟩ : Region).Disjoint ⟨b, 8192⟩) :
    WP isa (pointFromScalar count) s fun t =>
      Rest (.r19 :: .r7 :: batchR) s t ∧ Frame (mulW b) s.mem t.mem ∧
      point (env t.mem b) 0 1 2 3 =
        Spec.Ed25519.pointMul (decodeLE (bytesAt s.mem p (2 * count))) (point (env s.mem b) 0 1 2 3) ∧
      env t.mem b 16 = Spec.Ed25519.d := by
  unfold pointFromScalar
  refine WP.seq (wp_addi (by decide) (by decide) fun s1 u1 => WP.block_nil ?_)
  have hc1' : Ctx8 b s1 := hc.of_rest (u1.rest (ws := [.r19]) (by decide)) (by decide)
  refine WP.seq (WP.mono (fieldCode_ok _ hc1'.ctx) fun s2 ⟨k2, e2⟩ => ?_)
  obtain ⟨p2, d2⟩ := env_const16 (env s1.mem b)
  rw [← e2] at p2 d2
  have hc2 : Ctx8 b s2 := hc1'.of_keep k2
  have hb2 : bytesAt s2.mem p (2 * count) = bytesAt s.mem p (2 * count) := by
    simp only [Spec.Ed25519.bytesAt, List.map_inj_left]
    intro i hi
    rw [← u1.mem]
    exact bytes_ws k2.frame (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.sub_base _ (by omega_arith)) hpd
      (by omega_arith) (List.mem_range.mp hi)
  refine WP.mono (pointMultiply_ok hc2 d2 (p := p) hc1 hc32
    (by rw [k2.rest.gpr _ (by decide), u1.gpr, h14, BitVec.add_zero])
    (fun i hi => by rw [k2.rest.rd, k2.rest.wr, u1.rd, u1.wr]; exact hin i hi) hpd) fun t ⟨rt, ft, pt, dt⟩ =>
      ⟨?_, ?_, ?_, dt⟩
  · exact (u1.rest (by decide)).trans ((k2.rest.mono (by decide)).trans (rt.mono (by decide)))
  · rw [← u1.mem]
    exact (k2.frame.mono (by simp)).trans ft
  · rw [pt, hb2, p2, u1.mem]

/-- A block that writes no link register keeps it. -/
theorem WP.keep_lr {is : List Instr} {s : State} {Q : State → Prop} (h : WP isa (.block is) s Q)
    (hl : (instrs (.block is : Prog isa)).all (fun i => !i.writesLr) = true) :
    WP isa (.block is) s fun t => Q t ∧ t.lr = s.lr := by
  obtain ⟨tr, t, he, hq⟩ := h
  exact ⟨tr, t, he, hq, Exec.lr he rfl hl⟩

theorem wp_mflr {d : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', Upd s s' d s.lr → s'.lr = s.lr → WP isa (.block is) s' Q) : WP isa (.block (.mflr d :: is)) s Q :=
  WP.cons exec_mflr (k _ (Upd.write _ _ _) rfl)

/-- `addi`, keeping the link register. -/
theorem wp_addiL {d n : Reg} {imm : Nat} (hn : n ≠ .r0) (h : imm < 2 ^ 15) {is : List Instr} {s : State}
    {Q : State → Prop} (k : ∀ s', Upd s s' d (s.gpr n + BitVec.ofNat 64 imm) → s'.lr = s.lr → WP isa (.block is) s' Q) :
    WP isa (.block (.addi d n imm :: is)) s Q :=
  WP.cons (exec_addi hn h) (k _ (Upd.write _ _ _) rfl)

theorem wp_mtlr {r : Reg} {is : List Instr} {s : State} {Q : State → Prop}
    (k : WP isa (.block is) { s with lr := s.gpr r } Q) : WP isa (.block (.mtlr r :: is)) s Q :=
  WP.cons exec_mtlr k

theorem LRS_eq : LRS = 1120 := rfl

theorem mulW_saves {B : Addr} (lo n : Nat) (h1 : 1024 ≤ lo) (h2 : lo + n ≤ 1632) :
    ∀ r ∈ mulW B, Region.Disjoint ⟨B + BitVec.ofNat 64 lo, n⟩ r := by
  intro r hr
  have hB : BITSB = 32 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inl (by omega_arith)) (by omega_arith) (by omega_arith)
  · exact Offset.disjoint _ (.inr (by omega_arith)) (by omega_arith) (by omega_arith)

end

end VG.Proof.Ed25519.PPC64LE
