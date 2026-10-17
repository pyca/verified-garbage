module

public import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.CT
public import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
meta import VerifiedGarbage.Proof.Gcm.X86_64.Prepared.Context
import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
meta import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Bcast
import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pair
meta import VerifiedGarbage.Proof.Gcm.X86_64.StitchZ.Pair

/-!
# AES-GCM's short path on x86-64: the table of powers from a prepared context

Untrusted: everything here is checked by Lean. A prepared key context
(`VG.Spec.Gcm.PreparedPowersRepr`) holds `H'¹`–`H'⁴⁸` in pairs, the 64 bytes
at `ctx + 256 + 64 j` being `H'⁴ʲ⁺²`, `H'⁴ʲ⁺¹`, `H'⁴ʲ⁺⁴`, `H'⁴ʲ⁺³`. `powersP`
copies the first eight groups to the table, each swapped by halves
(`vshufi32x4` with `0x4E`, `grpP_ok`, `grpsP_ok`), into the table's order
`H'⁴ʲ⁺⁴`–`H'⁴ʲ⁺¹`: what `powers` computes (`powOk_powersP`). It addresses
memory only from the key context's and `W`'s registers (`powersP_ct`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesGcm.X86_64.Short

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.Impl.AesGcm.X86_64.Short
open VG.Proof.AesGcm.X86_64
open VG.Proof.Gcm.X86_64 (revMask)
open VG.Proof.Gcm.X86_64.Pclmul (Only const_ok)
open VG.Proof.Gcm.X86_64.Stitch (CtxMode)
open VG.Impl.Gcm.X86_64.Pclmul (poly)
open VG.Spec.Gcm (ctxH)

/-- Group `j` of `powersP`. -/
abbrev grpP (j : Nat) : List Instr :=
  [.vmovdqu32Load .xmm8 (at_ .r13 (256 + 64 * j)), .zop (.vshufi32x4 .xmm8 .xmm8 .xmm8 0x4E),
    .vmovdqu32Store (at_ .r11 (64 * j)) .xmm8]

/-- `vshufi32x4` with `0x4E`: the two halves swapped. -/
theorem shuf4E (a : Nat → BitVec 128) {l : Nat} (hl : l < 4) : shuf4Lanes a a 0x4E l = a ((l + 2) % 4) := by
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- One group: the 64 bytes at `ctx + 256 + 64 j`, swapped by halves, at
`T + 64 j`. -/
theorem grpP_ok (j : Nat) (s : State) {Ctx T : Addr} (h13 : s.gpr .r13 = Ctx) (h11 : s.gpr .r11 = T)
    (hin : InRegions (s.rd ++ s.wr) (Ctx + BitVec.ofNat 64 (256 + 64 * j)) 64)
    (hout : InRegions s.wr (T + BitVec.ofNat 64 (64 * j)) 64) :
    WP isa (.block (grpP j)) s fun s' =>
      (∃ v : BitVec 512, s'.mem = s.mem.writeW (T + BitVec.ofNat 64 (64 * j)) v ∧
        ∀ l < 4, v.extractLsb' (128 * l) 128 =
          s.mem.readW (Ctx + BitVec.ofNat 64 (256 + 64 * j) + BitVec.ofNat 64 (16 * ((l + 2) % 4))) 128) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .xmm8 → ∀ l < 4, s'.zlane r l = s.zlane r l) := by
  have ea₁ : s.gpr .r13 + BitVec.ofInt 64 ((256 + 64 * j : Nat) : Int) = Ctx + BitVec.ofNat 64 (256 + 64 * j) := by
    rw [h13, BitVec.ofInt_natCast]
  have ea₂ : s.gpr .r11 + BitVec.ofInt 64 ((64 * j : Nat) : Int) = T + BitVec.ofNat 64 (64 * j) := by
    rw [h11, BitVec.ofInt_natCast]
  let a := Ctx + BitVec.ofNat 64 (256 + 64 * j)
  let v := s.mem.readW a 512
  let s₁ := s.setZ .xmm8 (v.extractLsb' 0 128) (v.extractLsb' 128 128) (v.extractLsb' 256 128)
    (v.extractLsb' 384 128)
  let s₂ := (ZOp.vshufi32x4 .xmm8 .xmm8 .xmm8 0x4E).exec s₁
  have l₁ : ∀ l < 4, s₁.zlane .xmm8 l = s.mem.readW (a + BitVec.ofNat 64 (16 * l)) 128 := fun l hl =>
    VG.Proof.Gcm.X86_64.StitchZ.zlane_load s .xmm8 a hl
  rw [WP.block_cons_iff]
  refine ⟨s₁, by simp only [isa, exec, State.load512, State.ea, at_, ea₁, hin, ite_true, Option.map_some]; rfl, ?_⟩
  rw [WP.block_cons_iff]; refine ⟨s₂, rfl, ?_⟩
  rw [WP.block_cons_iff]
  have hst : isa.exec (.vmovdqu32Store (at_ .r11 (64 * j)) .xmm8) s₂ =
      some (s₂.setMem (s.mem.writeW (T + BitVec.ofNat 64 (64 * j)) (s₂.zmm .xmm8))) := by
    simp only [isa, exec, State.store512_eq, State.ea, at_, s₂, s₁, ZOp.exec_gpr, State.setZ_gpr, ZOp.exec_wr,
      State.setZ_wr, ZOp.exec_mem, State.setZ_mem, ea₂, hout, ite_true]
  refine ⟨_, hst, WP.block_nil ⟨⟨s₂.zmm .xmm8, by simp, fun l hl => ?_⟩, by simp [s₂, s₁], by simp [s₂, s₁],
    by simp [s₂, s₁], fun r hr l hl => ?_⟩⟩
  · rw [VG.Proof.Aes.X86_64.VaesZ.zmm_lane _ _ hl]
    simp only [s₂, zlane_vshufi32x4 _ _ _ _ _ _ hl, ite_true, shuf4E _ hl]
    exact l₁ _ (by omega)
  · simp [s₂, s₁, zlane_vshufi32x4 _ _ _ _ _ _ hl, State.zlane_setZ _ _ _ _ _ _ _ hl, hr]

/-- After `k` groups: the table's first `k` groups, nothing else written. -/
def InvP (s : State) (Ctx T : Addr) (k : Nat) (t : State) : Prop :=
  (∀ j < k, ∀ l < 4, t.mem.readW (T + BitVec.ofNat 64 (64 * j + 16 * l)) 128 =
      s.mem.readW (Ctx + BitVec.ofNat 64 (256 + 64 * j + 16 * ((l + 2) % 4))) 128) ∧
    Frame [⟨T, 512⟩] s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
    (∀ r, r ≠ .xmm8 → ∀ l < 4, t.zlane r l = s.zlane r l)

/-- The first `k ≤ 8` groups. -/
theorem grpsP_ok (s : State) {Ctx T : Addr} (h13 : s.gpr .r13 = Ctx) (h11 : s.gpr .r11 = T)
    (hcov : Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr)) (hw : Covers [⟨T, 512⟩] s.wr)
    (hd : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨T, 512⟩) :
    ∀ k ≤ 8, WP isa (.block ((List.range k).flatMap grpP)) s (InvP s Ctx T k)
  | 0, _ => WP.block_nil ⟨fun j hj => absurd hj (by omega), Frame.refl _ _, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (grpsP_ok s h13 h11 hcov hw hd k (by omega)) fun t ⟨tab, f, gt, rdt, wrt, zt⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (grpP_ok k t (Ctx := Ctx) (T := T) (by rw [gt]; exact h13) (by rw [gt]; exact h11)
      (by rw [rdt, wrt]; exact in_off hcov (by omega) (by decide))
      (by rw [wrt]; exact in_off hw (by omega) (by decide)))
      fun t' ⟨⟨v, mv, hv⟩, g', rd', wr', z'⟩ => ⟨fun j hj l hl => ?_, ?_, by rw [g', gt], by rw [rd', rdt],
        by rw [wr', wrt], fun r hr l hl => by rw [z' r hr l hl, zt r hr l hl]⟩
    · have ctxKeep : ∀ {o : Nat}, o + 16 ≤ 1024 →
          t.mem.readW (Ctx + BitVec.ofNat 64 o) 128 = s.mem.readW (Ctx + BitVec.ofNat 64 o) 128 := fun ho =>
        f.readW (r := ⟨Ctx + BitVec.ofNat 64 _, 16⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact hd.sub_left (Offset.sub_base Ctx ho)) (by decide)
      by_cases hjk : j = k
      · subst hjk
        have e := readW_writeW_inside t.mem (T + BitVec.ofNat 64 (64 * j)) v (k := 16 * l) (n := 16)
          (by omega) (by decide)
        rw [show 8 * 16 = 128 from rfl, show 8 * (16 * l) = 128 * l by omega] at e
        rw [mv, ← add_ofNat_ofNat, e, hv l hl, add_ofNat_ofNat, ctxKeep (by omega)]
      · rw [mv, (Frame.refl _ _ |>.writeW (List.mem_singleton_self _) v (Region.contains_self _ _)).readW
          (r := ⟨T + BitVec.ofNat 64 (64 * j + 16 * l), 16⟩) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr
            exact Offset.disjoint T (by omega) (by omega) (by omega)) (by decide)]
        exact tab j (by omega) l hl
    · rw [mv]
      exact f.trans (((Frame.refl _ _).writeW (List.mem_singleton_self _) v (Region.contains_self _ _)).sub
        fun r hr => ⟨_, List.mem_singleton_self _, by
          simp only [List.mem_singleton] at hr; subst hr; exact Offset.sub_base T (by omega)⟩)

/-- `powersP`: the constants in every lane of `zmm0` and `zmm1`, and the
table's eight groups from the key context. -/
theorem powersP_run {Ctx W SP : Addr} (s : State) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s)
    (hcov : Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr)) (hcw : (⟨Ctx, 1024⟩ : Region).Disjoint ⟨W, 2560⟩) :
    WP isa powersP s fun t =>
      (∀ j < 8, ∀ l < 4, t.mem.readW (W + BitVec.ofNat 64 1536 + BitVec.ofNat 64 (64 * j + 16 * l)) 128 =
        s.mem.readW (Ctx + BitVec.ofNat 64 (256 + 64 * j + 16 * ((l + 2) % 4))) 128) ∧
      Frame [⟨W + BitVec.ofNat 64 1536, 512⟩] s.mem t.mem ∧
      (∀ l < 4, t.zlane .xmm0 l = revMask) ∧ (∀ l < 4, t.zlane .xmm1 l = poly) ∧
      (∀ r, r ≠ .rax → r ≠ .r11 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  rw [powersP, show Impl.Gcm.X86_64.Pclmul.const .xmm0 Impl.Gcm.X86_64.Pclmul.revMask ++ Impl.Gcm.X86_64.Pclmul.const .xmm1 poly ++
      ([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44),
        .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr) ++
      ptr .r11 .r15 tbO ++ (List.range 8).flatMap grpP =
    Impl.Gcm.X86_64.Pclmul.const .xmm0 Impl.Gcm.X86_64.Pclmul.revMask ++ (Impl.Gcm.X86_64.Pclmul.const .xmm1 poly ++
      ((([.vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .zop (.vshufi32x4 .xmm0 .xmm0 .xmm0 0x44)] : List Instr) ++
        ([.vop (.vinserti128 .xmm1 .xmm1 .xmm1 1), .zop (.vshufi32x4 .xmm1 .xmm1 .xmm1 0x44)] : List Instr)) ++
      (ptr .r11 .r15 tbO ++ (List.range 8).flatMap grpP))) by simp only [List.append_assoc]; rfl]
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm0 _ s (by decide)) fun s₁ ⟨c₁, o₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (const_ok .xmm1 _ s₁ (by decide)) fun s₂ ⟨c₂, o₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pow4c_ok s₂) fun s₃ ⟨b0, b1, f₃⟩ => ?_
  rw [WP.block_append_iff]
  have O₂ := o₁.trans o₂
  obtain ⟨s₄, run₄, r11₄, g₄, m₄, rd₄, wr₄, z₄⟩ : ∃ s₄, runBlock isa (ptr .r11 .r15 tbO) s₃ = some s₄ ∧
      s₄.gpr .r11 = W + BitVec.ofNat 64 1536 ∧ (∀ r, r ≠ .r11 → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr ∧ ∀ r l, s₄.zlane r l = s₃.zlane r l := by
    refine ⟨_, by xrun [tbO], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, gpr_arithFlags, f₃.gpr, O₂.gpr _ (by decide : Reg.r15 ≠ .rax), he.r15]
    · intro r hr; simp [gpr_setReg, gpr_arithFlags, hr]
    all_goals first | rfl | exact fun _ _ => rfl
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  have m₄s : s₄.mem = s.mem := by rw [m₄, f₃.mem, O₂.mem]
  have rd₄s : s₄.rd = s.rd := by rw [rd₄, f₃.rd, O₂.rd]
  have wr₄s : s₄.wr = s.wr := by rw [wr₄, f₃.wr, O₂.wr]
  refine WP.mono (grpsP_ok s₄ (by rw [g₄ _ (by decide), f₃.gpr, O₂.gpr _ (by decide), he.r13]) r11₄
    (by rw [rd₄s, wr₄s]; exact hcov) (by rw [wr₄s]; exact he.perm.wC (by decide))
    (hcw.sub_right (Lay.wSub (by decide))) 8 (Nat.le_refl _)) fun t ⟨tab, f, gt, rdt, wrt, zt⟩ =>
      ⟨fun j hj l hl => by rw [tab j hj l hl, m₄s], by rw [← m₄s]; exact f, fun l hl => ?_, fun l hl => ?_,
        fun r ha hb => by rw [gt, g₄ r hb, f₃.gpr, O₂.gpr r ha], by rw [rdt, rd₄s], by rw [wrt, wr₄s]⟩
  · rw [zt _ (by decide) l hl, z₄, b0 l hl, o₂.xmm _ (by decide), c₁, VG.Proof.Gcm.X86_64.Pclmul.rev_eq]
  · rw [zt _ (by decide) l hl, z₄, b1 l hl, c₂]

/-- With a prepared key context, `powersP` leaves what `powers` does. -/
theorem powOk_powersP : PowOk CtxMode.prepared powersP := by
  intro s₀ Ctx W SP D n X g s he _ hg1 hg8 f rd wr
  have hok : Spec.Gcm.PreparedPowersRepr s.mem Ctx :=
    CtxMode.prepared.frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact X.cw
      · exact X.cd
      · exact X.ct.symm) X.w X.ok
  have hcov : Covers [⟨Ctx, 1024⟩] (s.rd ++ s.wr) := by rw [rd, wr]; exact X.cov
  refine WP.mono (powersP_run s he hcov X.cw) fun t ⟨tab, fT, z0, z1, gt, rdt, wrt⟩ =>
    ⟨fun j hj l hl => ?_, fT, z0, z1, gt, rdt, wrt⟩
  rw [tab j (by omega) l hl]
  have h2 := hok (2 * j) (by omega)
  have h3 := hok (2 * j + 1) (by omega)
  rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl | rfl
  · rw [show 256 + 64 * j + 16 * ((0 + 2) % 4) = 256 + 32 * (2 * j + 1) by omega, h3.1,
      show 2 * (2 * j + 1) + 2 = 4 * j + 4 - 0 by omega]; rfl
  · rw [show 256 + 64 * j + 16 * ((1 + 2) % 4) = 272 + 32 * (2 * j + 1) by omega, h3.2,
      show 2 * (2 * j + 1) + 1 = 4 * j + 4 - 1 by omega]; rfl
  · rw [show 256 + 64 * j + 16 * ((2 + 2) % 4) = 256 + 32 * (2 * j) by omega, h2.1,
      show 2 * (2 * j) + 2 = 4 * j + 4 - 2 by omega]; rfl
  · rw [show 256 + 64 * j + 16 * ((3 + 2) % 4) = 272 + 32 * (2 * j) by omega, h2.2,
      show 2 * (2 * j) + 1 = 4 * j + 4 - 3 by omega]; rfl

/-- `powersP` in two runs: its addresses are the key context's and `W`'s. -/
theorem powersP_ct : PowCT powersP := by
  intro s₀ s₀' Ctx W SP A D R al n J J' tl tl'
  exact rel_env_regs [] (fun _ h => h.env) (fun _ h => h.env) (fun _ _ _ _ _ hr => by cases hr) ⟨_, by taint_decide⟩

end VG.Proof.AesGcm.X86_64.Short
