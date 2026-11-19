module

import VerifiedGarbage.Proof.Sm4Gcm.Arm.StreamFinish
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Args
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Fn
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.SigEval
public import VerifiedGarbage.Proof.Gcm.Arm.Ghash
public import VerifiedGarbage.Impl.Sm4Gcm.Arm
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Flush
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Run
public import VerifiedGarbage.Proof.Cmac.Mem32
import VerifiedGarbage.Proof.Rsa.ZeroTest32
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sm4.CtrCipher
import VerifiedGarbage.Proof.Sm4.Scratch

/-! ### `Sm4Gcm.Arm.Init`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_init`

Untrusted: everything here is checked by Lean. `init` saves our caller's
registers in `scratch` (`W`), expands the key into the context with
`vg_sm4_expand_key`, and computes the hash subkey `CIPH_K(0¹²⁸)` into its
bytes 240–255 with `vg_sm4_ctr32` on a zero block, from a zero counter block
at `W + 96` (`init_wp`). The layout lemmas of `Lay` apply with the state
taken to be `W + 16` (which `init` never touches).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt blocksAt)
open VG.Spec.Sm4.Gcm (KeyRepr)
open VG.Proof.Cmac (store4)

/-- The layout, with the state taken to be `W + 16`. -/
theorem initLay {c w sp : BitVec 32} (cw : c.toNat + 256 ≤ 2 ^ 32) (ww : w.toNat + 768 ≤ 2 ^ 32)
    (sp8 : 1520 ≤ sp.toNat) (cW : (⟨State.addr c, 256⟩ : Region).Disjoint ⟨State.addr w, 768⟩)
    (kc : (below sp).Disjoint ⟨State.addr c, 256⟩) (kw : (below sp).Disjoint ⟨State.addr w, 768⟩) :
    Lay c (w + BitVec.ofNat 32 16) w sp := by
  have e : State.addr (w + BitVec.ofNat 32 16) = State.addr w + BitVec.ofNat 64 16 := addr_add (by omega_using [ww])
  have hs : Region.Sub ⟨State.addr w + BitVec.ofNat 64 16, 80⟩ ⟨State.addr w, 768⟩ := Lay.wSub (by decide)
  refine ⟨cw, ?_, ww, sp8, ?_, cW, ?_, ?_, kc, ?_, kw⟩
  · rw [show (w + BitVec.ofNat 32 16).toNat = w.toNat + 16 by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 16) (by decide), Nat.mod_eq_of_lt (by omega_using [ww])]]
    omega_using [ww]
  · rw [e]; exact cW.sub_right hs
  · rw [e]; simpa using Lay.w_w (w := w) (a := 16) (n := 80) (d := 0) (k := 16) (.inr (by decide)) (by decide)
      (by decide)
  · rw [e]; exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · rw [e]; exact kw.sub_right hs

/-- The entry: our caller's registers saved, `W` in `r11` and the context in
`r9`; the key and the context stay in `r0` and `r1` for the key expansion. -/
theorem initPre_ok {s₀ : State} (hfit : (s₀.gpr .r2).toNat + 768 ≤ 2 ^ 32)
    (hw : Covers [⟨State.addr (s₀.gpr .r2), 768⟩] s₀.wr) {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr .r11 = s₀.gpr .r2 → s₁.gpr .r9 = s₀.gpr .r1 →
      s₁.gpr .r0 = s₀.gpr .r0 → s₁.gpr .r1 = s₀.gpr .r1 →
      s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.sp = s₀.sp → SavedAt s₁.mem (s₀.gpr .r2) s₀ →
      Frame [savedR (s₀.gpr .r2)] s₀.mem s₁.mem → Q s₁) :
    WP isa (.block initPre) s₀ Q := by
  unfold initPre
  refine save_ok rfl hfit hw fun s' g rd wr sp sv fr => WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ?_ ?_ ?_ ?_ rd wr sp sv fr
  all_goals simp [gpr_setReg, g]

/-- The hash subkey's block and `T` zeroed, and the arguments of
`vg_sm4_ctr32` on them. -/
theorem initArgs_ok {c w sp : BitVec 32} (L : Lay c (w + BitVec.ofNat 32 16) w sp) {s : State}
    (h9 : s.gpr .r9 = c) (h11 : s.gpr .r11 = w) (hc : Covers [⟨State.addr c, 256⟩] s.wr)
    (hw : Covers [⟨State.addr w, 768⟩] s.wr) :
    ∃ s', runBlock isa initArgs s = some s' ∧
      s'.mem = store4 (store4 s.mem (State.addr c + BitVec.ofNat 64 240) 0 0 0 0)
        (State.addr w + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s'.gpr .r0 = c ∧ s'.gpr .r2 = w + BitVec.ofNat 32 96 ∧
      s'.gpr .r3 = c + BitVec.ofNat 32 240 ∧ s'.gpr .r12 = BitVec.ofNat 32 1 ∧
      (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have c₀ := in_off hc (show 240 + 4 ≤ 256 by decide) (by decide)
  have c₁ := in_off hc (show 244 + 4 ≤ 256 by decide) (by decide)
  have c₂ := in_off hc (show 248 + 4 ≤ 256 by decide) (by decide)
  have c₃ := in_off hc (show 252 + 4 ≤ 256 by decide) (by decide)
  have w₀ := in_off hw (show 96 + 4 ≤ 768 by decide) (by decide)
  have w₁ := in_off hw (show 100 + 4 ≤ 768 by decide) (by decide)
  have w₂ := in_off hw (show 104 + 4 ≤ 768 by decide) (by decide)
  have w₃ := in_off hw (show 108 + 4 ≤ 768 by decide) (by decide)
  refine ⟨_, by simp only [initArgs, hO]; arun [h9, h11, L.cA, L.wA, c₀, c₁, c₂, c₃, w₀, w₁, w₂, w₃], ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg, h11]
  · simp [gpr_setReg, h9]
  · simp [gpr_setReg]
  · intro r a b d e; simp [gpr_setReg, a, b, d, e]
  all_goals rfl

theorem zero_block (m : Mem) (p : Addr) : blockAt (store4 m p 0 0 0 0) p = 0 := by
  rw [blockAt, Cmac.bytesAt_store4, Cmac.le4_zero]; decide

/-- After the entry, from `s₀`. -/
structure IS1 (s₀ s₁ : State) : Prop where
  r11 : s₁.gpr .r11 = s₀.gpr .r2
  r9 : s₁.gpr .r9 = s₀.gpr .r1
  r0 : s₁.gpr .r0 = s₀.gpr .r0
  r1 : s₁.gpr .r1 = s₀.gpr .r1
  rd : s₁.rd = s₀.rd
  wr : s₁.wr = s₀.wr
  sp : s₁.sp = s₀.sp
  saved : SavedAt s₁.mem (s₀.gpr .r2) s₀
  frame : Frame [savedR (s₀.gpr .r2)] s₀.mem s₁.mem

theorem is1_wp {s₀ : State} (h : initArm.pre s₀) : WP isa (.block initPre) s₀ (IS1 s₀) := by
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, fs, -⟩ := h
  exact initPre_ok fs (by rw [hwr]; exact covers_of_mem (by simp))
    fun s₁ a b c d e f g h i => ⟨a, b, c, d, e, f, g, h, i⟩

theorem init_kc {s₀ s₁ : State} (h : initArm.pre s₀) (h1 : IS1 s₀ s₁) :
    KeyCall s₁ (s₀.gpr .r0) (s₀.gpr .r1) := by
  obtain ⟨hrd, hwr, dkc, -, dcs, bk, bc, bs, fk, fc, fs, sp8⟩ := h
  have hC : Covers [⟨State.addr (s₀.gpr .r1), 256⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  refine ⟨h1.r0, h1.r1, by rw [h1.sp]; exact sp8, fk, by omega_using [fc], dkc.sub_right (Region.sub_prefix (by decide)),
    by rw [h1.sp]; exact bk, by rw [h1.sp]; exact bc.sub_right (Region.sub_prefix (show 128 ≤ 256 by decide)), ?_, ?_⟩
  · rw [h1.rd, h1.wr, hrd]; exact covers_of_mem (List.mem_append_left _ (List.mem_singleton_self _))
  · rw [h1.wr]; exact covers_prefix hC (by decide)

/-- After the key expansion. -/
def IS2 (s₀ s₂ : State) : Prop :=
  ∃ s₁, IS1 s₀ s₁ ∧ KeyPost s₁ (s₀.gpr .r0) (s₀.gpr .r1) s₂

/-- After `initArgs`. -/
def IS3 (s₀ s₃ : State) : Prop := ∃ s₂, IS2 s₀ s₂ ∧ runBlock isa initArgs s₂ = some s₃

theorem IS2.g {s₀ s₂ : State} (h : IS2 s₀ s₂) : s₂.gpr .r9 = s₀.gpr .r1 ∧ s₂.gpr .r11 = s₀.gpr .r2 ∧
    s₂.rd = s₀.rd ∧ s₂.wr = s₀.wr ∧ s₂.sp = s₀.sp := by
  obtain ⟨s₁, h1, kp⟩ := h
  exact ⟨by rw [kp.saved .r9 (by decide) (by decide), h1.r9], by rw [kp.saved .r11 (by decide) (by decide), h1.r11],
    kp.rd.trans h1.rd, kp.wr.trans h1.wr, kp.sp.trans h1.sp⟩

/-- What `initArgs` leaves. -/
theorem IS3.facts {s₀ s₃ : State} (h : initArm.pre s₀) (h3 : IS3 s₀ s₃) :
    ∃ s₂, IS2 s₀ s₂ ∧
      s₃.mem = store4 (store4 s₂.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 240) 0 0 0 0)
        (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 96) 0 0 0 0 ∧
      s₃.gpr .r0 = s₀.gpr .r1 ∧ s₃.gpr .r2 = s₀.gpr .r2 + BitVec.ofNat 32 96 ∧
      s₃.gpr .r3 = s₀.gpr .r1 + BitVec.ofNat 32 240 ∧ s₃.gpr .r12 = BitVec.ofNat 32 1 ∧
      s₃.gpr .r11 = s₀.gpr .r2 ∧ s₃.rd = s₀.rd ∧ s₃.wr = s₀.wr ∧ s₃.sp = s₀.sp := by
  obtain ⟨s₂, h2, run⟩ := h3
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8⟩ := h
  have L := initLay fc fs sp8 dcs bc bs
  obtain ⟨g9, g11, grd, gwr, gsp⟩ := h2.g
  obtain ⟨s₃', run', hm, g0, g2, g3, g12, gg, rd, wr, sp⟩ := initArgs_ok L (s := s₂) g9 g11
    (by rw [gwr, hwr]; exact covers_of_mem (by simp)) (by rw [gwr, hwr]; exact covers_of_mem (by simp))
  obtain rfl : s₃' = s₃ := Option.some.inj (run'.symm.trans run)
  exact ⟨s₂, h2, hm, g0, g2, g3, g12, by rw [gg _ (by decide) (by decide) (by decide) (by decide), g11],
    rd.trans grd, wr.trans gwr, sp.trans gsp⟩

theorem init_cc {s₀ s₃ : State} (h : initArm.pre s₀) (h3 : IS3 s₀ s₃) :
    CtrCall s₃ (s₀.gpr .r1) (s₀.gpr .r2 + BitVec.ofNat 32 96) (s₀.gpr .r1 + BitVec.ofNat 32 240) 1 := by
  obtain ⟨s₂, -, -, g0, g2, g3, g12, -, -, wr₃, hk3⟩ := h3.facts h
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8⟩ := h
  have L := initLay fc fs sp8 dcs bc bs
  have hW : Covers [⟨State.addr (s₀.gpr .r2), 768⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have hC : Covers [⟨State.addr (s₀.gpr .r1), 256⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eT := L.wA (d := 96) (by decide)
  have eH := L.cA (d := 240) (by decide)
  refine ⟨g0, g2, g3, g12, by rw [hk3]; exact sp8,
    by omega_using [fc], by rw [L.wN (by decide)]; omega_using [fs], by rw [L.cN (by decide)]; omega_using [fc],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [eT, eH, hk3, Nat.mul_one]
  · exact (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
  · simpa using Lay.ctx_ctx (c := s₀.gpr .r1) (a := 0) (n := 128) (d := 240) (k := 16) (.inl (by decide))
      (by decide) (by decide)
  · exact (L.ctx_w (a := 240) (n := 16) (d := 96) (k := 16) (by decide) (by decide)).symm
  · exact L.kc.sub_right (Region.sub_prefix (by decide))
  · exact L.stk_w (by decide)
  · exact L.stk_ctx (by decide)
  · rw [wr₃]; exact covers_left (covers_prefix hC (by decide))
  · rw [wr₃]
    exact covers_cons (covers_off hW (by decide) (by decide)) (covers_off hC (by decide) (by decide))

/-- After the call of `vg_sm4_ctr32`. -/
def IS4 (s₀ s₄ : State) : Prop :=
  ∃ s₃, IS3 s₀ s₃ ∧ CtrPost s₃ (s₀.gpr .r1) (s₀.gpr .r2 + BitVec.ofNat 32 96) (s₀.gpr .r1 + BitVec.ofNat 32 240) 1 s₄

theorem init_fin {s₀ s₄ : State} (h : initArm.pre s₀) (h4 : IS4 s₀ s₄) :
    WP isa (.block restore) s₄ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' := by
  obtain ⟨s₃, h3, cp⟩ := h4
  obtain ⟨s₂, h2, hm₃, -, -, -, -, g11, -, wr₃, hk3⟩ := h3.facts h
  obtain ⟨s₁, h1, kp⟩ := h2
  obtain ⟨-, hwr, -, dks, dcs, -, bc, bs, -, fc, fs, sp8⟩ := h
  have L := initLay fc fs sp8 dcs bc bs
  have hW : Covers [⟨State.addr (s₀.gpr .r2), 768⟩] s₀.wr := by rw [hwr]; exact covers_of_mem (by simp)
  have eT := L.wA (d := 96) (by decide)
  have eH := L.cA (d := 240) (by decide)
  have dSv : ∀ {d k : Nat}, d + k ≤ 768 → (128 + 36 ≤ d ∨ d + k ≤ 128) →
      (savedR (s₀.gpr .r2)).Disjoint ⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega_using [h₂]) (by decide) h₁
  have dSc : ∀ {d k : Nat}, d + k ≤ 256 →
      (savedR (s₀.gpr .r2)).Disjoint ⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ => (L.ctx_w h₁ (show 128 + 36 ≤ 768 by decide)).symm
  have cframe := cp.frame
  have cout := cp.out
  simp only [eT, eH, hk3, Nat.mul_one] at cframe cout
  have f₃ : Frame [⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 240, 16⟩, ⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 96, 16⟩]
      s₂.mem s₃.mem := by
    rw [hm₃]
    exact ((Cmac.frame_store4 _ 0 0 0 0).mono (by simp)).trans ((Cmac.frame_store4 _ 0 0 0 0).mono (by simp))
  have kframe := kp.frame
  have sv₄ : SavedAt s₄.mem (s₀.gpr .r2) s₀ := by
    refine ((h1.saved.frame kframe ?_).frame f₃ ?_).frame cframe ?_
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using dSc (d := 0) (k := 128) (by decide)
      · rw [h1.sp]; exact (L.stk_w (show 128 + 36 ≤ 768 by decide)).symm
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dSc (by decide)
      · exact dSv (by decide) (.inr (by decide))
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact dSv (by decide) (.inr (by decide))
      · exact dSc (by decide)
      · exact (L.stk_w (show 128 + 36 ≤ 768 by decide)).symm
  refine WP.mono (restore_ok (s₀ := s₀) (by rw [cp.saved _ (by decide) (by decide), g11]) fs
      (by rw [cp.wr, wr₃]; exact covers_left hW) sv₄ (by rw [cp.sp, hk3])) fun s' hh => ⟨hh.1, ?_⟩
  have hm := hh.2.1
  have dP : ∀ {d k : Nat}, 128 ≤ d → d + k ≤ 256 →
      (⟨State.addr (s₀.gpr .r1), 128⟩ : Region).Disjoint ⟨State.addr (s₀.gpr .r1) + BitVec.ofNat 64 d, k⟩ :=
    fun {d k} h₁ h₂ => by
      simpa using Lay.ctx_ctx (c := s₀.gpr .r1) (a := 0) (n := 128) (d := d) (k := k) (.inl (by omega_using [h₁])) (by decide) h₂
  have dPw : ∀ {d k : Nat}, d + k ≤ 768 →
      (⟨State.addr (s₀.gpr .r1), 128⟩ : Region).Disjoint ⟨State.addr (s₀.gpr .r2) + BitVec.ofNat 64 d, k⟩ := fun h₁ =>
    (L.cw'.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub h₁)
  have key₁ : Spec.Sm4.blockAt s₁.mem (State.addr (s₀.gpr .r0)) =
      Vector.ofFn fun i => (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) 16).getD i.val 0 := by
    rw [← Proof.Sm4.ofFn_toList (Spec.Sm4.blockAt s₁.mem _), ← Proof.Sm4.bytesAt_eq_blockAt,
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact dks.sub_right (Lay.wSub (by decide))) (by decide)]
  have ks₃ : Spec.Sm4.scheduleAt s₃.mem (State.addr (s₀.gpr .r1)) =
      Spec.Sm4.expandKey (Vector.ofFn fun i => (bytesAt s₀.mem (State.addr (s₀.gpr .r0)) 16).getD i.val 0) := by
    rw [Proof.Sm4.scheduleAt_frame f₃ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact dP (by decide) (by decide)
        · exact dPw (by decide)), kp.out, key₁]
  simp only [initArm, KeyRepr, hm]
  refine ⟨?_, ?_⟩
  · rw [Proof.Sm4.scheduleAt_frame cframe (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact dPw (by decide)
        · exact dP (by decide) (by decide)
        · exact (L.kc.sub_right (Region.sub_prefix (by decide))).symm), ks₃]
  · rw [blocksAt_one, blocksAt_one, ctr32_single, List.cons.injEq] at cout
    have z₁ : blockAt s₃.mem (State.addr (s₀.gpr .r2) + BitVec.ofNat 64 96) = 0 := by rw [hm₃, zero_block]
    have z₂ : blockAt s₃.mem (State.addr (s₀.gpr .r1) + BitVec.ofNat 64 240) = 0 := by
      rw [hm₃, blockAt_frame (Cmac.frame_store4 _ 0 0 0 0) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact L.ctx_w (by decide) (by decide)), zero_block]
    rw [ctxH_eq, cout.1, z₁, z₂]
    refine BitVec.zero_xor.trans ?_
    simp only [Spec.Sm4.Gcm.ctxCiph, Spec.Sm4.gcmCipherOfKey, ks₃]

theorem is3_run {s₀ s₂ : State} (h : initArm.pre s₀) (h2 : IS2 s₀ s₂) : ∃ s₃, runBlock isa initArgs s₂ = some s₃ := by
  obtain ⟨-, hwr, -, -, dcs, -, bc, bs, -, fc, fs, sp8⟩ := h
  obtain ⟨g9, g11, -, gwr, -⟩ := h2.g
  obtain ⟨s₃, run, -⟩ := initArgs_ok (initLay fc fs sp8 dcs bc bs) (s := s₂) g9 g11
    (by rw [gwr, hwr]; exact covers_of_mem (by simp)) (by rw [gwr, hwr]; exact covers_of_mem (by simp))
  exact ⟨s₃, run⟩

theorem init_wp {s₀ : State} (h : initArm.pre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ initArm.post s₀ s' :=
  WP.seq (WP.mono (is1_wp h) fun s₁ h1 => WP.seq (WP.mono (key_call (init_kc h h1)) fun s₂ kp =>
    WP.seq (by
      obtain ⟨s₃, run⟩ := is3_run h ⟨s₁, h1, kp⟩
      exact WP.of_runBlock ⟨s₃, run, WP.seq (WP.mono (ctr_call (init_cc h ⟨s₂, ⟨s₁, h1, kp⟩, run⟩)) fun s₄ cp =>
        init_fin h ⟨s₃, ⟨s₂, ⟨s₁, h1, kp⟩, run⟩, cp⟩)⟩)))

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.StreamVerify`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.Arm.Compare`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: checking a received tag

Untrusted: everything here is checked by Lean. `tagLenOk` sets `Z` iff the
tag length in `r6` is not one `tagLenOk` allows (`tagLenOk_ok`); `recv` and
`cmp o` copy the received tag (at `tag`) and the computed one (at `W + o`),
`r6` bytes of each, padded with zeros, to `W + 256` and `W + 240` (`recv_ok`,
`cmp_ok`), and `cmpTail` sets `r0` to 1 if they are equal and 0 if not,
without a branch (`cmpTail_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (zeros)
open VG.Proof.Cmac (le4 store4)

theorem msb_or_neg (x : BitVec 32) : (x ||| (0 - x)) >>> 31 = if x = 0 then 0 else 1 :=
  VG.Proof.Rsa.msb_or_neg x

theorem le4_inj {x y : BitVec 32} (h : le4 x = le4 y) : x = y := by
  have e : ∀ k < 4, x.extractLsb' (8 * k) 8 = y.extractLsb' (8 * k) 8 := fun k hk => by
    have := congrArg (fun l => l.getD k 0) h
    simpa only [Cmac.getD_le4 _ hk] using this
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have := congrArg (fun v => v.getLsbD (j % 8)) (e (j / 8) (by omega_arith))
  simp only [BitVec.getLsbD_extractLsb', show j % 8 < 8 from Nat.mod_lt _ (by decide), decide_true,
    Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega_arith] at this

/-- Subtracting 4 and comparing unsigned with 13 rejects both ends. -/
theorem tagLenOk_carry {tl : Nat} (htl : tl < 2 ^ 32) :
    decide (13 ≤ (BitVec.ofNat 32 tl - 4#32).toNat) = !Spec.Gcm.tagLenOk tl := by
  apply Bool.eq_iff_iff.mpr
  simp [Spec.Gcm.tagLenOk, BitVec.toNat_sub, Nat.mod_eq_of_lt htl]
  omega_arith

/-- `tagLenOk`: `Z` clear iff the tag length is allowed. -/
theorem tagLenOk_ok {s : State} {tl : Nat} (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (htl : tl < 2 ^ 32) :
    WP isa tagLenOk s fun s' => s'.z = !Spec.Gcm.tagLenOk tl ∧ (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  refine WP.of_runBlock ⟨_, by arun [], ?_, ?_, ?_⟩
  · simp only [z_subFlags, c_subFlags, gpr_setReg, z_setReg, c_setReg,
      ite_true, ite_false, reduceCtorEq, h6]
    simp only [show (13#32).toNat = 13 from rfl]
    rw [tagLenOk_carry htl]
    cases Spec.Gcm.tagLenOk tl <;> rfl
  · intro r hr; simp [gpr_setReg, gpr_subFlags, hr]
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem store4_zero_tail (m : Mem) (p : Addr) {k : Nat} (hk : k ≤ 16) :
    bytesAt (store4 m p 0 0 0 0) (p + BitVec.ofNat 64 k) (16 - k) = zeros (16 - k) := by
  have h := store4_zero_bytes m p
  rw [show (16 : Nat) = k + (16 - k) by omega_arith, bytesAt_add,
    show zeros (k + (16 - k)) = zeros k ++ zeros (16 - k) by rw [zeros, zeros, zeros, List.replicate_append_replicate]] at h
  exact (List.append_inj h (by simp [length_bytesAt, Proof.Gcm.length_zeros])).2

section
variable {c st w sp k7 k8 : BitVec 32} (L : Lay c st w sp)
include L

/-- A copy of `tl` bytes from `S` to `W + d`, which holds 16 zero bytes. -/
theorem padCopy_ok {s : State} (he : Env c st w sp k7 k8 s) {S : BitVec 32} {d tl : Nat}
    (hd : d + 16 ≤ 768) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) (hSr : Covers [⟨State.addr S, tl⟩] (s.rd ++ s.wr))
    (hSf : S.toNat + tl ≤ 2 ^ 32) (hSd : (⟨State.addr S, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 d, 16⟩)
    {m₀ : Mem} (hm : s.mem = store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (hr1 : s.gpr .r1 = S)
    (hr2 : s.gpr .r2 = w + BitVec.ofNat 32 d) (hr3 : s.gpr .r3 = BitVec.ofNat 32 tl) :
    WP isa copyLoop s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 d) 16 =
        bytesAt m₀ (State.addr S) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ s'.mem ∧ LoopOut s S (w + BitVec.ofNat 32 d) tl s' := by
  have eD := L.wA (d := d) (by omega_arith)
  have ww := L.ww
  have lp : LoopPre s S (w + BitVec.ofNat 32 d) tl := by
    refine ⟨hr1, hr2, hr3, h1, by omega_arith, hSf, by rw [L.wN (by omega_arith)]; omega_arith, hSr, ?_, ?_⟩
    · rw [eD]; exact he.perm.wC (by omega_arith)
    · rw [eD]; exact hSd.sub_right (Region.sub_prefix h16)
  refine WP.mono (copyLoop_ok s lp) fun s' ⟨hm', lo⟩ => ?_
  rw [hm, eD] at hm'
  have fz : Frame [⟨State.addr w + BitVec.ofNat 64 d, 16⟩] m₀ (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) :=
    Cmac.frame_store4 _ _ _ _ _
  have hx : bytesAt (store4 m₀ (State.addr w + BitVec.ofNat 64 d) 0 0 0 0) (State.addr S) tl =
      bytesAt m₀ (State.addr S) tl :=
    bytesAt_frame fz (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hSd) (by omega_arith)
  rw [hx] at hm'
  have hlen := length_bytesAt m₀ (State.addr S) tl
  refine ⟨?_, ?_, lo⟩
  · rw [hm', bytesAt_writeBytes_prefix _ _ _ (by rw [hlen]; omega_arith) (by omega_arith), hlen, store4_zero_tail _ _ h16]
  · rw [hm']
    exact fz.trans ((writeBytes_frame' _ hlen).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega_arith)⟩)

/-- `zero16 d`: the 16 bytes at `W + d` zeroed. -/
theorem zero16_ok {s : State} (he : Env c st w sp k7 k8 s) {d : Nat} (hd : d + 16 ≤ 768) (ed₁ : d + 12 < 4096) :
    ∃ s', runBlock isa (zero16 d) s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 d) 0 0 0 0 ∧
      (∀ r, r ≠ .r0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have w₀ := he.perm.wW (show d + 4 ≤ 768 by omega_arith)
  have w₁ := he.perm.wW (show d + 4 + 4 ≤ 768 by omega_arith)
  have w₂ := he.perm.wW (show d + 8 + 4 ≤ 768 by omega_arith)
  have w₃ := he.perm.wW (show d + 12 + 4 ≤ 768 by omega_arith)
  have e₀ := L.wA (d := d) (by omega_arith)
  have e₁ := L.wA (d := d + 4) (by omega_arith)
  have e₂ := L.wA (d := d + 8) (by omega_arith)
  have e₃ := L.wA (d := d + 12) (by omega_arith)
  have o₀ : d < 4096 := by omega_arith
  have o₁ : d + 4 < 4096 := by omega_arith
  have o₂ : d + 8 < 4096 := by omega_arith
  refine ⟨_, by simp only [zero16]; arun [h11, e₀, e₁, e₂, e₃, w₀, w₁, w₂, w₃, o₀, o₁, o₂, ed₁], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]; rfl
  · intro r a; simp [gpr_setReg, a]
  · rfl
  · rfl
  · rfl

omit L in
/-- The four words at `p`, as bytes. -/
theorem bytes_words (m : Mem) (p : Addr) : bytesAt m p 16 = le4 (m.readW p 32) ++ le4 (m.readW (p + BitVec.ofNat 64 4) 32) ++
    le4 (m.readW (p + BitVec.ofNat 64 8) 32) ++ le4 (m.readW (p + BitVec.ofNat 64 12) 32) := by
  rw [Cmac.bytesAt_split4, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW, Cmac.le4_readW]

omit L in
theorem words_eq_iff (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    le4 a₀ ++ le4 a₁ ++ le4 a₂ ++ le4 a₃ = le4 b₀ ++ le4 b₁ ++ le4 b₂ ++ le4 b₃ ↔
      a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  constructor
  · intro h
    have l := Cmac.length_le4
    obtain ⟨h₁, h₂⟩ := List.append_inj h (by simp [l])
    obtain ⟨h₁, h₃⟩ := List.append_inj h₁ (by simp [l])
    obtain ⟨h₁, h₄⟩ := List.append_inj h₁ (by simp [l])
    exact ⟨le4_inj h₁, le4_inj h₄, le4_inj h₃, le4_inj h₂⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

omit L in
theorem cmp_value (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : BitVec 32) :
    BitVec.ofNat 32 1 - ((((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃) |||
      (BitVec.ofNat 32 0 - (((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃))) >>> 31 =
    if a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ then 1 else 0 := by
  rw [show BitVec.ofNat 32 0 = 0 from rfl, msb_or_neg]
  by_cases h : a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    simp
  · have : ¬(((a₀ ^^^ b₀ ||| a₁ ^^^ b₁) ||| a₂ ^^^ b₂) ||| a₃ ^^^ b₃) = 0 := by
      intro e
      simp only [show (0 : BitVec 32) = 0#32 from rfl, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff] at e
      exact h ⟨e.1.1.1, e.1.1.2, e.1.2, e.2⟩
    simp only [this, h, ite_false]; rfl

omit L in
theorem runBlock_app (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
    show (isa.exec i s).bind _ = ((isa.exec i s).bind _).bind _
    cases isa.exec i s with
    | none => rfl
    | some s' => exact ih s'

omit L in
theorem runBlock_app_of {a b : List Instr} {s s₁ s₂ : State} (h₁ : runBlock isa a s = some s₁)
    (h₂ : runBlock isa b s₁ = some s₂) : runBlock isa (a ++ b) s = some s₂ := by
  rw [runBlock_app, h₁]; exact h₂

/-- `cmpTail`: `r0` is 1 iff the 16 bytes at `W + 240` and `W + 256` are equal. -/
theorem cmpTail_ok {s : State} (he : Env c st w sp k7 k8 s) :
    ∃ s', runBlock isa cmpTail s = some s' ∧
      s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 240) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  have h11 := he.r11
  have r₀ := he.perm.wR (show 240 + 4 ≤ 768 by decide)
  have r₁ := he.perm.wR (show 244 + 4 ≤ 768 by decide)
  have r₂ := he.perm.wR (show 248 + 4 ≤ 768 by decide)
  have r₃ := he.perm.wR (show 252 + 4 ≤ 768 by decide)
  have q₀ := he.perm.wR (show 256 + 4 ≤ 768 by decide)
  have q₁ := he.perm.wR (show 260 + 4 ≤ 768 by decide)
  have q₂ := he.perm.wR (show 264 + 4 ≤ 768 by decide)
  have q₃ := he.perm.wR (show 268 + 4 ≤ 768 by decide)
  let m := s.mem
  let a := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (240 + 4 * k)) 32
  let b := fun k : Nat => m.readW (State.addr w + BitVec.ofNat 64 (256 + 4 * k)) 32
  obtain ⟨s₁, run₁, g₁, h0₁, k₁⟩ : ∃ s₁, runBlock isa (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) s =
      some s₁ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₁.gpr r = s.gpr r) ∧
      s₁.gpr .r0 = (a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ∧ Keeps s s₁ := by
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11, L.wA, r₀, r₁, q₀, q₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have h11₁ : s₁.gpr .r11 = w := by rw [g₁ _ (by decide) (by decide) (by decide), h11]
  have hm₁ := k₁.mem
  obtain ⟨s₂, run₂, g₂, h0₂, k₂⟩ : ∃ s₂, runBlock isa (xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
      [.dp .orr .r0 .r0 (.reg .r1)]) s₁ = some s₂ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → s₂.gpr r = s₁.gpr r) ∧
      s₂.gpr .r0 = ((a 0 ^^^ b 0 ||| a 1 ^^^ b 1) ||| a 2 ^^^ b 2) ||| a 3 ^^^ b 3 ∧ Keeps s₁ s₂ := by
    rw [← k₁.rd, ← k₁.wr] at r₂ r₃ q₂ q₃
    refine ⟨_, by simp only [xorW, vO, rO]; arun [h11₁, L.wA, r₂, r₃, q₂, q₃, hm₁], ?_, ?_, ?_⟩
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · simp [gpr_setReg, a, b, m, h0₁, hm₁]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨s₃, run₃, g₃, h0₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
      .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)] s₂ =
      some s₃ ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s₃.gpr r = s₂.gpr r) ∧
      s₃.gpr .r0 = BitVec.ofNat 32 1 - ((s₂.gpr .r0 ||| (BitVec.ofNat 32 0 - s₂.gpr .r0)) >>> 31) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [], ?_, ?_, ?_⟩
    · intro r x y; simp [gpr_setReg, x, y]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, Op2.eval]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨s₃, ?_, ?_, ?_, k₁.trans (k₂.trans k₃)⟩
  · rw [show cmpTail = (xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      ((xorW .r1 2 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++ [.dp .orr .r0 .r0 (.reg .r1)]) ++
      [.mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31),
        .mov .r1 (imm 1), .dp .sub .r0 .r1 (.reg .r0)]) from rfl]
    exact runBlock_app_of run₁ (runBlock_app_of run₂ run₃)
  · rw [h0₃, h0₂, cmp_value, bytes_words, bytes_words]
    simp only [add_ofNat_assoc]
    congr 1
    simp only [a, b, m]
    exact propext (words_eq_iff _ _ _ _ _ _ _ _).symm
  · intro r x y z; rw [g₃ r x y, g₂ r x y z, g₁ r x y z]

/-- `recv`: the received tag (`r6` bytes at `T`, the stack argument at `[sp + ta]`), padded
with zeros at `W + 256`. -/
theorem recv_ok {s : State} (he : Env c st w sp k7 k8 s) {ta : Nat} (hta : ta = 8 ∨ ta = 12) {T : BitVec 32} {tl : Nat}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 ta)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 ta)) 32 = T)
    (hTr : Covers [⟨State.addr T, tl⟩] (s.rd ++ s.wr)) (hTf : T.toNat + tl ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 256, 16⟩)
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa (recv ta) s fun s' => bytesAt s'.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr T) tl ++ zeros (16 - tl) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 256, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₀, run₀, h1₀, g₀, k₀⟩ : ∃ s₀, runBlock isa [.ldrSp .r1 ta] s = some s₀ ∧ s₀.gpr .r1 = T ∧
      (∀ r, r ≠ .r1 → s₀.gpr r = s.gpr r) ∧ Keeps s s₀ := by
    refine ⟨_, by rcases hta with rfl | rfl <;> arun [hTi, hTv], ?_, ?_, ?_⟩
    · simp [gpr_setReg, hTv]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have he₀ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₀ _ (by decide)) k₀.sp k₀.rd k₀.wr
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁⟩ := zero16_ok L he₀ (d := rO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he₀.r11]
  obtain ⟨s₂, run₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r2 .r11 rO, .mov .r3 (.reg .r6)] s₁ = some s₂ ∧
      s₂.gpr .r2 = w + BitVec.ofNat 32 256 ∧ s₂.gpr .r3 = BitVec.ofNat 32 tl ∧
      (∀ r, r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [rO]; arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), g₀ .r6 (by decide), h6]
    · intro r x y; simp [gpr_setReg, x, y]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  have run : runBlock isa (.ldrSp .r1 ta :: zero16 rO ++ [addI .r2 .r11 rO, .mov .r3 (.reg .r6)]) s = some s₂ :=
    runBlock_app_of (a := [.ldrSp .r1 ta]) run₀ (runBlock_app_of run₁ run₂)
  refine WP.seq (WP.of_runBlock ⟨s₂, run, ?_⟩)
  have he₂ := he₀.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have h1₂ : s₂.gpr .r1 = T := by rw [g₂ _ (by decide) (by decide), g₁ _ (by decide), h1₀]
  have hTr₂ : Covers [⟨State.addr T, tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [k₂.rd, k₂.wr, rd₁, wr₁, k₀.rd, k₀.wr]; exact hTr
  refine WP.mono (padCopy_ok L he₂ (d := 256) (by decide) h1 h16 hTr₂ hTf hTd (m₀ := s.mem)
    (by rw [k₂.mem, hm₁, k₀.mem]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_
  refine ⟨hb, hf, fun r a b d e f => ?_, lo.rd.trans (k₂.rd.trans (rd₁.trans k₀.rd)),
    lo.wr.trans (k₂.wr.trans (wr₁.trans k₀.wr)), lo.sp.trans (k₂.sp.trans (sp₁.trans k₀.sp))⟩
  rw [lo.other r a b d e f, g₂ r d e, g₁ r a, g₀ r b]

/-- `cmp o`: the first `r6` bytes of the tag at `W + o`, padded with zeros at
`W + 240`, compared with the received tag at `W + 256`. -/
theorem cmp_ok {s : State} (he : Env c st w sp k7 k8 s) {o : Nat} (ho : o = 0 ∨ o = 112) {tl : Nat}
    (h6 : s.gpr .r6 = BitVec.ofNat 32 tl) (h1 : 1 ≤ tl) (h16 : tl ≤ 16) :
    WP isa (cmp o) s fun s' => s'.gpr .r0 = (if bytesAt s.mem (State.addr w + BitVec.ofNat 64 o) tl ++ zeros (16 - tl) =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 then 1 else 0) ∧
      Frame [⟨State.addr w + BitVec.ofNat 64 240, 16⟩] s.mem s'.mem ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  obtain ⟨s₁, run₁, hm₁, g₁, rd₁, wr₁, sp₁⟩ := zero16_ok L he (d := vO) (by decide) (by decide)
  have h11 : s₁.gpr .r11 = w := by rw [g₁ _ (by decide), he.r11]
  have eo : encodable (BitVec.ofNat 32 o) = true := by rcases ho with rfl | rfl <;> decide
  obtain ⟨s₂, run₂, h1₂, h2₂, h3₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [addI .r1 .r11 o, addI .r2 .r11 vO,
      .mov .r3 (.reg .r6)] s₁ = some s₂ ∧ s₂.gpr .r1 = w + BitVec.ofNat 32 o ∧ s₂.gpr .r2 = w + BitVec.ofNat 32 240 ∧
      s₂.gpr .r3 = BitVec.ofNat 32 tl ∧ (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by simp only [vO]; arun [eo], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, h11]
    · simp [gpr_setReg, g₁ .r6 (by decide), h6]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₂, runBlock_app_of run₁ run₂, ?_⟩)
  have he₂ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide)]) (k₂.sp.trans sp₁) (k₂.rd.trans rd₁)
      (k₂.wr.trans wr₁)
  have hSr : Covers [⟨State.addr (w + BitVec.ofNat 32 o), tl⟩] (s₂.rd ++ s₂.wr) := by
    rw [L.wA (by omega_arith)]; exact covers_left (he₂.perm.wC (by omega_arith))
  have hSd : (⟨State.addr (w + BitVec.ofNat 32 o), tl⟩ : Region).Disjoint ⟨State.addr w + BitVec.ofNat 64 240, 16⟩ := by
    rw [L.wA (by omega_arith)]; exact Lay.w_w (by omega_arith) (by omega_arith) (by decide)
  refine WP.seq (WP.mono (padCopy_ok L he₂ (d := 240) (by decide) h1 h16 hSr (by rw [L.wN (by omega_arith)]; have := L.ww; omega_arith) hSd
    (m₀ := s.mem) (by rw [k₂.mem, hm₁]; rfl) h1₂ h2₂ h3₂) fun s₃ ⟨hb, hf, lo⟩ => ?_)
  rw [L.wA (by omega_arith)] at hb
  have he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact lo.other _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) lo.sp lo.rd lo.wr
  obtain ⟨s₄, run₄, h0₄, g₄, k₄⟩ := cmpTail_ok L he₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_, ?_, fun r a b d e f => ?_, k₄.rd.trans (lo.rd.trans (k₂.rd.trans rd₁)),
    k₄.wr.trans (lo.wr.trans (k₂.wr.trans wr₁)), k₄.sp.trans (lo.sp.trans (k₂.sp.trans sp₁))⟩
  · have h256 : bytesAt s₃.mem (State.addr w + BitVec.ofNat 64 256) 16 =
        bytesAt s.mem (State.addr w + BitVec.ofNat 64 256) 16 :=
      bytesAt_frame hf (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by decide)) (by decide) (by decide))
        (by decide)
    rw [h0₄, hb, h256]
  · rw [k₄.mem]; exact hf
  · rw [g₄ r a b d, lo.other r a b d e f, g₂ r b d e, g₁ r a]

end

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_stream_verify`

Untrusted: everything here is checked by Lean. `stream_verify` saves our
caller's registers in `work` (`W`), checks the tag length, and, if it is
allowed, copies the received tag (at `tag`) to `W + 256`, writes the tag to
`W` and compares the first `tag_len` bytes of each; if the length is not
allowed the result is 0 (`streamVerify_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt StreamRepr ghashInput fullTag zeros)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Cmac (store4)

theorem bytesAt_take (m : Mem) (p : Addr) {k n : Nat} (h : k ≤ n) : bytesAt m p k = (bytesAt m p n).take k := by
  rw [show n = k + (n - k) by omega_using [h], bytesAt_add, List.take_left' (length_bytesAt _ _ _)]

theorem tagLenOk_bounds {tl : Nat} (h : Spec.Gcm.tagLenOk tl = true) : 1 ≤ tl ∧ tl ≤ 16 := by
  simp only [Spec.Gcm.tagLenOk, Bool.and_eq_true, decide_eq_true_eq] at h
  omega_using [h]

/-- What `verify` promises, for the additional data `a` and the text `ct`. -/
def VerPost (s₀ : State) (a ct : List Byte) (s : State) : Prop :=
  ∀ iv, StreamRepr s₀.mem (State.addr (s₀.gpr .r1)) (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct → (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 a.length →
    let t := fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct
    if Spec.Gcm.tagLenOk (arg s₀ 3).toNat ∧ t.take (arg s₀ 3).toNat = bytesAt s₀.mem (State.addr (arg s₀ 2))
        (arg s₀ 3).toNat then s.gpr .r0 = 1
    else s.gpr .r0 = 0

theorem ver_run [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamVerifyPreArm s₀) {a ct : List Byte} (ha : a.length % 16 = (s₀.gpr .r2).toNat % 16)
    (hP : (arg s₀ 1 ++ arg s₀ 0).toNat = ct.length) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ VerPost s₀ a ct s' := by
  obtain h' : finPre 5 4 s₀ := streamVerifyPreArm.fin h
  obtain L := finLay h'
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hin : args s₀ 5 ∈ s₀.rd := h'.1.2
  obtain ⟨hrd, -, -, -, -, -, -, tW, -, -, -, -, -, -, -, fT, -⟩ := h
  obtain hTr : Covers [⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))
  obtain dT : ∀ {d k : Nat}, d + k ≤ 768 → (⟨State.addr (arg s₀ 2), (arg s₀ 3).toNat⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  obtain dW : ∀ {d k : Nat}, d + k ≤ 768 → (164 ≤ d ∨ d + k ≤ 128) →
      (savedR (arg s₀ 4)).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega_using [h₂]) (by decide) h₁
  refine WP.seq (WP.block_append (fin1_wp (wi := 4) h' (by decide) (by decide) fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 12] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (arg s₀ 3).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain he₂ := h1.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₂ _ (by decide)) k₂.sp k₂.rd k₂.wr
  refine WP.seq (WP.mono (tagLenOk_ok h6₂ (arg s₀ 3).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  obtain k₁₃ := k₂.trans k₃
  obtain he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  obtain hk₃ := h1.args.of_eq k₁₃.mem k₁₃.sp k₁₃.rd k₁₃.wr
  obtain sv₃ : SavedAt s₃.mem (arg s₀ 4) s₀ := k₁₃.mem ▸ h1.saved
  obtain mid : WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) (.seq (recv 8) (.seq (finTag 0) (.seq (.block [.ldrSp .r6 12])
      (cmp 0))))) s₃ fun s' => (∃ k7, Env (s₀.gpr .r0) (s₀.gpr .r1) (arg s₀ 4) s₀.sp k7
        (s₀.gpr .r2) s') ∧ SavedAt s'.mem (arg s₀ 4) s₀ ∧ VerPost s₀ a ct s' := by
    refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => ?_)
    · have hbad : Spec.Gcm.tagLenOk (arg s₀ 3).toNat = false := by simpa using ht
      refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₃, fun iv _ _ => ?_⟩
      simp only [hbad, Bool.false_eq_true, false_and, ite_false]
      simp [gpr_setReg]
    · have hok : Spec.Gcm.tagLenOk (arg s₀ 3).toNat = true := by simpa using hf
      obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
      obtain h6₃ : s₃.gpr .r6 = BitVec.ofNat 32 (arg s₀ 3).toNat := by rw [g₃ _ (by decide), h6₂]
      obtain ⟨i4, v4⟩ := hk₃.at spf hin 2 (by decide) (show 4 * 2 = 8 from rfl)
      refine WP.seq (WP.mono (recv_ok L he₃ (.inl rfl) i4 v4 (by rw [hk₃.rd, hk₃.wr]; exact hTr) fT (dT (by decide)) h6₃ t1 t16)
        fun s₄ hh => ?_)
      obtain ⟨hb₄, hf₄, g₄, rd₄, wr₄, sp₄⟩ := hh
      obtain he₄ := he₃.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₄ rd₄ wr₄
      obtain dA : ∀ {d k : Nat}, d + k ≤ 768 → (args s₀ 5).Disjoint ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ :=
        fun hd => (h'.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
      obtain hk₄ := hk₃.frame spf hf₄ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact dA (by decide)) sp₄ rd₄ wr₄
      obtain f₀₄ : Frame [savedR (arg s₀ 4), ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩] s₀.mem s₄.mem :=
        (h1.frame.mono (by simp)).trans ((k₁₃.mem ▸ hf₄ : Frame _ s₁.mem s₄.mem).mono (by simp))
      obtain dc₀₄ : ∀ r ∈ [savedR (arg s₀ 4), ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact L.cw'.sub_right (Lay.wSub (by decide))
        · exact L.cw'.sub_right (Lay.wSub (by decide))
      obtain ds₀₄ : ∀ r ∈ [savedR (arg s₀ 4), ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 256, 16⟩],
          (⟨State.addr (s₀.gpr .r1), 80⟩ : Region).Disjoint r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · simpa using L.st_w (a := 0) (n := 80) (d := 128) (k := 36) (by decide) (.inr ⟨by decide, by decide⟩)
        · simpa using L.st_w (a := 0) (n := 80) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
      refine WP.seq (WP.mono (WP.with_rdwr (finTag_ok L (na := 5) (by decide) (o := 0) (.inl rfl) he₄ hk₄ spf hin
        (fin_argsTag h' (.inl rfl))
        (ctxH_keep f₀₄ dc₀₄) ha hP)) fun s₅ hh => ?_)
      obtain ⟨fo, rd₅, wr₅, sp₅⟩ := hh
      obtain ⟨k7₅, he₅⟩ := fo.env
      obtain ⟨j5, w5⟩ := fo.args.at spf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
      obtain ⟨s₆, run₆, h6₆, g₆, k₆⟩ : ∃ s₆, runBlock isa [.ldrSp .r6 12] s₅ = some s₆ ∧
          s₆.gpr .r6 = BitVec.ofNat 32 (arg s₀ 3).toNat ∧ (∀ r, r ≠ .r6 → s₆.gpr r = s₅.gpr r) ∧ Keeps s₅ s₆ := by
        refine ⟨_, by arun [j5, w5], ?_, ?_, ?_⟩
        · simp [gpr_setReg, w5]
        · intro r hr; simp [gpr_setReg, hr]
        · exact ⟨rfl, rfl, rfl, rfl⟩
      refine WP.seq (WP.of_runBlock ⟨s₆, run₆, ?_⟩)
      obtain he₆ := he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide)) k₆.sp k₆.rd k₆.wr
      refine WP.mono (cmp_ok L he₆ (o := 0) (.inl rfl) h6₆ t1 t16) fun s₇ hh => ?_
      obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
      refine ⟨⟨k7₅, he₆.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
          (by decide)) sp₇ rd₇ wr₇⟩, ?_, fun iv hs hl => ?_⟩
      · have sv₅ := (sv₃.frame hf₄ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact dW (by decide) (.inl (by decide)))).frame fo.frame
          (saved_tagFrame L (.inl rfl))
        obtain sv₆ : SavedAt s₆.mem (arg s₀ 4) s₀ := k₆.mem ▸ sv₅
        refine sv₆.frame hf₇ ?_
        intro r hr; simp only [List.mem_singleton] at hr; subst hr
        exact dW (by decide) (.inl (by decide))
      · have ht' : bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 0) 16 =
            fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct := by
          rw [k₆.mem]; exact fin_out (n := 5) (wi := 4) f₀₄ dc₀₄ ds₀₄ fo hs hl
        obtain hrc : bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 256) 16 =
            bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat ++ zeros (16 - (arg s₀ 3).toNat) := by
          rw [k₆.mem, bytesAt_frame fo.frame (fun r hr => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
              rcases hr with rfl | rfl | rfl | rfl | rfl
              · have := L.st_w (a := 0) (n := 32) (d := 256) (k := 16) (by decide) (.inr ⟨by decide, by decide⟩)
                simp only [add_ofNat_zero] at this
                exact this.symm
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
              · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
              · exact (L.stk_w (by decide)).symm) (by decide), hb₄, k₁₃.mem,
            bytesAt_frame h1.frame (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr
              exact dT (d := 128) (k := 36) (by decide)) (by omega_using [])]
        obtain hX : (bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 0) (arg s₀ 3).toNat ++
              zeros (16 - (arg s₀ 3).toNat) = bytesAt s₆.mem (State.addr (arg s₀ 4) + BitVec.ofNat 64 256) 16) ↔
            (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (arg s₀ 3).toNat =
              bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat := by
          rw [bytesAt_take _ _ t16, ht', hrc, List.append_cancel_right_eq]
        simp only [hok, true_and]
        by_cases e : (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
              (ctxH s₀.mem (State.addr (s₀.gpr .r0))) iv a ct).take (arg s₀ 3).toNat =
              bytesAt s₀.mem (State.addr (arg s₀ 2)) (arg s₀ 3).toNat
        · simp only [e, ite_true]
          rw [h0₇]; simp only [hX.mpr e, ite_true]
        · simp only [e, ite_false]
          rw [h0₇]; simp only [show ¬ _ from fun x => e (hX.mp x), ite_false]
  refine WP.seq (WP.mono mid fun s₄ hh => ?_)
  obtain ⟨⟨k7, he⟩, sv, vp⟩ := hh
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, fun iv hs hl => ?_⟩
  have := vp iv hs hl
  rw [hh.2.2.1]; exact this

theorem streamVerify_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : streamVerifyArm.pre s₀) :
    WP isa streamVerify s₀ fun s' => abiPreserved s₀ s' ∧ streamVerifyArm.post s₀ s' := by
  obtain h₀ := ver_run h (a := List.replicate ((s₀.gpr .r2).toNat % 16) 0)
    (ct := List.replicate (arg s₀ 1 ++ arg s₀ 0).toNat 0) (by simp) (by simp)
  refine WP.mono (WP.forall_det (WP.mono h₀ fun _ hh => hh.1)
    (P := fun i : List Byte × List Byte =>
      (s₀.gpr .r3 ++ s₀.gpr .r2) = BitVec.ofNat 64 i.1.length ∧ (arg64 s₀ 0).toNat = i.2.length)
    fun i hi => WP.mono (ver_run h (a := i.1) (ct := i.2) (low_mod16 hi.1).symm hi.2) fun _ hh => hh.2)
    fun s' hh => ⟨hh.1, fun iv a c hs hl hp => hh.2 ⟨a, c⟩ ⟨hl, hp⟩ iv hs hl⟩

end VG.Proof.Sm4Gcm.Arm

end

end

/-! ### `Sm4Gcm.Arm.Seal`, which this module and modules that import it used -/

section

/-! ### `Sm4Gcm.Arm.OneShot`, which this module and modules that import it used -/

section

/-!
# SM4-GCM on ARMv7: the pieces of `vg_sm4_gcm_seal` and `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. Both keep a streaming state at
`W + 16`: the entry saves our caller's registers (`one1_wp`), `oneAad` writes
`J₀` and absorbs the additional data, padded (`oneAad_ok`), `oneCrypt` runs
counter mode over the data from the first counter block (`oneCrypt_ok`), and
`oneTag o` absorbs the data as ciphertext, padded, then the lengths block,
and writes the tag to `W + o` (`oneTag_ok`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput fullTag zeros padLen j0 inc32 gctr ghash ghashFrom blocks toBytes ofBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed Ctr xorKs lensBlock padded)

section
variable {n wi : Nat}

/-- The state, at `W + 16`. -/
abbrev oSt (s₀ : State) (wi : Nat) : BitVec 32 := arg s₀ wi + BitVec.ofNat 32 16

theorem oneLay {s₀ : State} (h : onePre n wi s₀) : Lay (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp := by
  obtain ⟨-, -, -, dcW, -, -, -, -, -, -, -, bc, -, -, -, bW, fc, -, -, -, fW, sp8, -⟩ := h
  exact initLay fc fW sp8 dcW bc bW

theorem oSt_addr {s₀ : State} (h : onePre n wi s₀) :
    State.addr (oSt s₀ wi) = State.addr (arg s₀ wi) + BitVec.ofNat 64 16 :=
  addr_add (by have := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega_arith)

/-- A buffer apart from `W` is apart from the state. -/
theorem oSt_disj {s₀ : State} (h : onePre n wi s₀) {R : Region} (hR : R.Disjoint ⟨State.addr (arg s₀ wi), 768⟩) :
    R.Disjoint ⟨State.addr (oSt s₀ wi), 80⟩ := by
  rw [oSt_addr h]; exact hR.sub_right (Lay.wSub (by decide))

/-- After the entry, from `s₀`. -/
structure SO1 (n wi : Nat) (s₀ s₁ : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r3) s₁
  r4 : s₁.gpr .r4 = s₀.gpr .r1
  r5 : s₁.gpr .r5 = s₀.gpr .r2
  args : ArgsKeep n s₀ s₁
  saved : SavedAt s₁.mem (arg s₀ wi) s₀
  frame : Frame [savedR (arg s₀ wi)] s₀.mem s₁.mem

theorem one1_wp {s₀ : State} (h : onePre n wi s₀) (hn : wi < n) (hwi : 4 * wi < 4096) {Q : State → Prop}
    (k : ∀ s₁, SO1 n wi s₀ s₁ → Q s₁) : WP isa (.block (oneEntry (4 * wi))) s₀ Q := by
  obtain hst := oSt_addr h
  have ww := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨⟨hc, -, -, hin⟩, ⟨-, hw, -⟩, -, -, -, -, -, -, -, -, dWA, -, -, -, -, -, -, -, -, -, fW, -, spf⟩ := h
  obtain hA : ∀ r ∈ [savedR (arg s₀ wi)], (args s₀ n).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  obtain hC : Covers [⟨State.addr (s₀.gpr .r0), 256⟩] (s₀.rd ++ s₀.wr) :=
    covers_of_mem (List.mem_append_left _ hc)
  obtain hW : Covers [⟨State.addr (arg s₀ wi), 768⟩] s₀.wr := covers_of_mem hw
  obtain hS : Covers [⟨State.addr (oSt s₀ wi), 80⟩] s₀.wr := by rw [hst]; exact covers_off hW (by decide) (by decide)
  obtain ha : InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.sp + BitVec.ofNat 32 (4 * wi))) 4 := arg_in hn spf hin
  refine entry_ok (off := 4 * wi) hwi ha fW hW fun s₁ g12 g rd wr sp sv fr => ?_
  obtain hk : ArgsKeep n s₀ s₁ := (ArgsKeep.refl n s₀).frame spf fr hA sp rd wr
  refine WP.of_runBlock ⟨_, by arun [], ?_⟩
  refine k _ ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_, ?_⟩⟩, ?_, ?_, ?_, sv, fr⟩
  any_goals (simp [gpr_setReg, g, g12]; done)
  · simp [gpr_setReg, g, g12]; rfl
  · simp [gpr_setReg, g, g12]; rfl
  · exact sp
  · change Covers _ (s₁.rd ++ s₁.wr); rw [rd, wr]; exact hC
  · change Covers _ s₁.wr; rw [wr]; exact hS
  · change Covers _ s₁.wr; rw [wr]; exact hW
  · exact hk.of_eq rfl rfl rfl rfl

end

theorem abs16_sub {st w sp : BitVec 32} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t16_sub {st w sp : BitVec 32} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ j0Frame st w sp, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Lay.stSub (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem abs16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (absFrame st w sp 16) m m') :
    Frame (j0Frame st w sp) m m' := h.sub abs16_sub

theorem t16_j0Frame {st w sp : BitVec 32} {m m' : Mem} (h : Frame (tFrame st w sp 16) m m') :
    Frame (j0Frame st w sp) m m' := h.sub t16_sub

section
variable {n wi : Nat}

/-- The stack arguments are apart from what `j0` (and the other pieces) write. -/
theorem one_argsJ0 {s₀ : State} (h : onePre n wi s₀) :
    ∀ r ∈ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp, (args s₀ n).Disjoint r := by
  obtain hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

/-- A buffer apart from `W` and the stack below `sp` is apart from what `j0` writes. -/
theorem one_dataJ0 {s₀ : State} (h : onePre n wi s₀) {R : Region} (hW : R.Disjoint ⟨State.addr (arg s₀ wi), 768⟩)
    (hb : (below s₀.sp).Disjoint R) : ∀ r ∈ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp, R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact oSt_disj h hW
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hW.sub_right (Lay.wSub (by decide))
  · exact hb.symm

/-- After `oneAad`, from `m₁`. -/
structure OA (n wi : Nat) (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) s
  args : ArgsKeep n s₀ s
  j : blockAt s.mem (State.addr (oSt s₀ wi)) =
    j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat)
  cb : blockAt s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat))
  abs : Absorbed s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (oSt s₀ wi) + BitVec.ofNat 64 32)
    (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    (bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat ++
      zeros (padLen (bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat).length))
  hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0))
  frame : Frame (j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp) m₁ s.mem

theorem oneAad_ok [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₁ : State} (h : onePre n wi s₀) (hn : 5 ≤ n) (h1 : SO1 n wi s₀ s₁) :
    WP isa oneAad s₁ (OA n wi s₀ s₁.mem) := by
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ n ∈ s₀.rd := h.1.2.2.2
  obtain ⟨hrd, -, -, -, -, dnW, -, daW, -, -, -, -, bn, ba, -, -, -, fn, fa, -, -, -, -⟩ := id h
  obtain hH₁ := ctxH_keep h1.frame (ctx_saved L)
  obtain ji : J0In (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp (s₀.gpr .r7) (s₀.gpr .r3)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (s₀.gpr .r1) (s₀.gpr .r2).toNat s₁ :=
    ⟨h1.env, hH₁, h1.r4, by rw [h1.r5]; simp, ⟨by
      rw [h1.args.rd, h1.args.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.1),
      (s₀.gpr .r2).isLt, fn, oSt_disj h dnW, dnW, bn⟩⟩
  refine WP.seq (WP.mono (WP.with_rdwr (j0_ok L ji)) fun s₂ hh => ?_)
  obtain ⟨jo, rd₂, wr₂, sp₂⟩ := hh
  obtain ⟨k7, he₂⟩ := jo.env
  obtain hiv : bytesAt s₁.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat :=
    bytesAt_frame h1.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dnW.sub_right (Lay.wSub (by decide))) (by omega_arith)
  rw [hiv] at jo
  obtain hk₂ := h1.args.frame spf jo.frame (one_argsJ0 h) sp₂ rd₂ wr₂
  obtain ⟨a0, v0⟩ := hk₂.at spf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  have h8₂ := he₂.r8
  obtain ⟨s₃, run₃, h4₃, h5₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.mov .r4 (.reg .r8), .ldrSp .r5 0, .mov .r6 (imm 0)] s₂ =
      some s₃ ∧ s₃.gpr .r4 = s₀.gpr .r3 ∧ s₃.gpr .r5 = arg s₀ 0 ∧ s₃.gpr .r6 = BitVec.ofNat 32 0 ∧
      (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [a0, v0], ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h8₂]
    · simp [gpr_setReg, v0]
    · simp [gpr_setReg]
    · intro r x y z; simp [gpr_setReg, x, y, z]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ := he₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide) (by decide) (by decide)) k₃.sp k₃.rd k₃.wr
  obtain hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  obtain hda : DataOk (oSt s₀ wi) (arg s₀ wi) s₀.sp s₃ (s₀.gpr .r3) (arg s₀ 0).toNat :=
    ⟨by rw [hk₃.rd, hk₃.wr]; exact covers_of_mem (List.mem_append_left _ hrd.2.2.1), (arg s₀ 0).isLt, fa,
      oSt_disj h daW, daW, ba⟩
  obtain haad : bytesAt s₃.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat =
      bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat := by
    rw [k₃.mem, bytesAt_frame jo.frame (one_dataJ0 h daW ba) (by omega_arith),
      bytesAt_frame h1.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact daW.sub_right (Lay.wSub (by decide))) (by omega_arith)]
  obtain ai : AbsIn (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) []
      (s₀.gpr .r3) (arg s₀ 0).toNat s₃ :=
    ⟨he₃, h4₃, by rw [h5₃]; simp, by rw [h6₃]; rfl, hda, by rw [k₃.mem]; exact jo.hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₄ hh => ?_)
  obtain ⟨ab, rd₄, wr₄, sp₄⟩ := hh
  rw [haad, List.nil_append] at ab
  obtain hk₄ := hk₃.frame spf ab.frame (disj_sub (one_argsJ0 h) abs16_sub) sp₄ rd₄ wr₄
  obtain ⟨b1, w1⟩ := hk₄.at spf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 0, .dp .and .r6 .r6 (imm 15)] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 0).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [b1, w1], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w1, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  obtain hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  obtain hH₄ : blockAt s₄.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl)), k₃.mem]; exact jo.hH
  refine WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₅, by rw [k₅.mem]; exact hH₄⟩ (by rw [h6₅, length_bytesAt]))) fun s₆ hh => ?_
  obtain ⟨fl, rd₆, wr₆, sp₆⟩ := hh
  rw [k₅.mem] at fl
  obtain keepA : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ absFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16,
      (⟨State.addr (oSt s₀ wi) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
    · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega_arith)).symm
  obtain keepT : ∀ {d : Nat}, (d = 0 ∨ d = 48) → ∀ r ∈ tFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16,
      (⟨State.addr (oSt s₀ wi) + BitVec.ofNat 64 d, 16⟩ : Region).Disjoint r := fun hd r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Lay.st_st (by omega_arith) (by omega_arith) (by decide)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
    · exact L.st_w (by omega_arith) (.inr ⟨by decide, by decide⟩)
    · exact (L.stk_st (by omega_arith)).symm
  obtain blk : ∀ {d : Nat}, (d = 0 ∨ d = 48) → blockAt s₆.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 d) =
      blockAt s₂.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 d) := fun hd => by
    rw [blockAt_frame fl.frame (keepT hd), blockAt_frame ab.frame (keepA hd), k₃.mem]
  refine ⟨⟨k7, fl.env⟩, hk₄.frame spf fl.frame (disj_sub (one_argsJ0 h) t16_sub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_, ?_, fl.hH, ?_⟩
  · have := blk (d := 0) (.inl rfl); rw [add_ofNat_zero] at this; rw [this]; exact jo.j0
  · rw [blk (.inr rfl)]; exact jo.cb
  · exact fl.abs (ab.abs (by rw [k₃.mem]; exact Proof.Gcm.absorbed_nil _ jo.y))
  · rw [k₃.mem] at ab
    exact (jo.frame.trans (abs16_j0Frame ab.frame)).trans (t16_j0Frame fl.frame)

/-- The data, for `crypt` and `absorb`. -/
theorem one_dataOk {s₀ s : State} (h : onePre n wi s₀) (hk : ArgsKeep n s₀ s) :
    DataOk (oSt s₀ wi) (arg s₀ wi) s₀.sp s (arg s₀ 1) (arg s₀ 2).toNat := by
  obtain ⟨-, hwr, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -, -, -, -, fD, -, -, -⟩ := id h
  exact ⟨by rw [hk.rd, hk.wr]; exact covers_left (covers_of_mem hwr.1), (arg s₀ 2).isLt, fD,
    oSt_disj h dDW, dDW, bD⟩

theorem dataArgs_run {s₀ s : State} (hk : ArgsKeep n s₀ s) (hf : s₀.sp.toNat + 4 * n ≤ 2 ^ 32)
    (hin : args s₀ n ∈ s₀.rd) (hn : 5 ≤ n) :
    ∃ s', runBlock isa dataArgs s = some s' ∧ s'.gpr .r4 = arg s₀ 1 ∧ s'.gpr .r5 = arg s₀ 2 ∧
      s'.gpr .r6 = BitVec.ofNat 32 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → s'.gpr r = s.gpr r) ∧ Keeps s s' := by
  obtain ⟨a2, v2⟩ := hk.at hf hin 1 (by omega_arith) (show 4 * 1 = 4 from rfl)
  obtain ⟨a3, v3⟩ := hk.at hf hin 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
  refine ⟨_, by simp only [dataArgs]; arun [a2, v2, a3, v3], ?_, ?_, ?_, ?_, ?_⟩
  · simp [gpr_setReg, v2]
  · simp [gpr_setReg, v3]
  · simp [gpr_setReg]
  · intro r x y z; simp [gpr_setReg, x, y, z]
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- After `oneCrypt`, from `m₀`. -/
structure OC (n wi : Nat) (s₀ : State) (k7 : BitVec 32) (icb : Block) (m₀ : Mem) (s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) s
  args : ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat =
    gctr (ciphOf m₀ (State.addr (s₀.gpr .r0))) icb (bytesAt m₀ (State.addr (arg s₀ 1)) (arg s₀ 2).toNat)
  frame : Frame (crFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp (arg s₀ 1) (arg s₀ 2).toNat) m₀ s.mem

theorem oneCrypt_ok {s₀ s : State} (h : onePre n wi s₀) (hn : 5 ≤ n) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) s) (hk : ArgsKeep n s₀ s) {icb : Block}
    (hcb : blockAt s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 48) = icb) :
    WP isa oneCrypt s (OC n wi s₀ k7 icb s.mem) := by
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ n ∈ s₀.rd := h.1.2.2.2
  have dcD := h.2.2.1
  have hwr := h.2.1
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  obtain hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  obtain ci : CrIn (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) icb 0 (arg s₀ 1)
      (arg s₀ 2).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6],
      ⟨one_dataOk h hk₁, by rw [hk₁.wr]; exact covers_of_mem hwr.1, dcD⟩⟩
  refine WP.mono (WP.with_rdwr (crypt_ok L ci)) fun s₂ hh => ?_
  obtain ⟨co, rd₂, wr₂, sp₂⟩ := hh
  obtain hA : ∀ r ∈ crFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp (arg s₀ 1) (arg s₀ 2).toNat, (args s₀ n).Disjoint r := by
    obtain hst := oSt_addr h
    obtain ⟨-, -, -, -, -, -, -, -, -, dDA, dWA, -⟩ := h
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact dDA.symm
    · rw [hst, add_ofNat_assoc]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (dWA.sub_left (Lay.wSub (by decide))).symm
    · exact (below_args s₀ spf).symm
  rw [k₁.mem] at co
  obtain c0 := Proof.Gcm.ctr_zero s.mem _ (State.addr (oSt s₀ wi) + BitVec.ofNat 64 64)
    (ciphOf s.mem (State.addr (s₀.gpr .r0))) hcb
  exact ⟨co.env, hk₁.frame spf (k₁.mem ▸ co.frame) hA sp₂ rd₂ wr₂, by rw [co.out c0, Proof.Gcm.gctr_eq],
    co.frame⟩

end

theorem padded_eq (a c : List Byte) :
    (a ++ zeros (padLen a.length) ++ c) ++ zeros (padLen (a ++ zeros (padLen a.length) ++ c).length) = padded a c := by
  by_cases hc : c = []
  · subst hc
    obtain h0 : padLen (a ++ zeros (padLen a.length) ++ []).length = 0 := by
      apply Proof.Gcm.padLen_of_mod
      simp only [List.append_nil, List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
    rw [h0]; simp [padded, Proof.Gcm.ghashInput_nil, zeros]
  · simp only [padded, Proof.Gcm.ghashInput_of_ne hc]

/-- The regions `oneTag o` writes. -/
abbrev otFrame (st w sp : BitVec 32) (o : Nat) : List Region :=
  [⟨State.addr st, 48⟩, ⟨State.addr w + BitVec.ofNat 64 96, 16⟩, ⟨State.addr w + BitVec.ofNat 64 o, 16⟩,
    ⟨State.addr w + BitVec.ofNat 64 512, 256⟩, below sp]

theorem abs_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ absFrame st w sp 16, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 256⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem t_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ tFrame st w sp 16, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 512, 256⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩

theorem tag_otSub {st w sp : BitVec 32} {o : Nat} : ∀ r ∈ tagFrame st w sp o, ∃ r' ∈ otFrame st w sp o, Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨_, by simp, fun _ h => h⟩

section
variable {n wi : Nat}

/-- After `oneTag o`, from `m₀`, for the tag of `a` and the bytes at `data`. -/
structure OT (n wi : Nat) (s₀ : State) (o : Nat) (a : List Byte) (J : Block) (m₀ : Mem) (s : State) : Prop where
  env : ∃ k7, Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) s
  args : ArgsKeep n s₀ s
  out : bytesAt s.mem (State.addr (arg s₀ wi) + BitVec.ofNat 64 o) 16 =
    toBytes (ghashFrom (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (ghash (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (blocks (padded a (bytesAt m₀ (State.addr (arg s₀ 1)) (arg s₀ 2).toNat))))
      [ofBytes (lensBlock a.length (bytesAt m₀ (State.addr (arg s₀ 1)) (arg s₀ 2).toNat).length)] ^^^
      ciphOf m₀ (State.addr (s₀.gpr .r0)) J)
  frame : Frame (otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o) m₀ s.mem

theorem one_argsOt {s₀ : State} (h : onePre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o, (args s₀ n).Disjoint r := by
  obtain hst := oSt_addr h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, dWA, -⟩ := h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (dWA.sub_left (Lay.wSub (by omega_arith))).symm
  · exact (dWA.sub_left (Lay.wSub (by decide))).symm
  · exact (below_args s₀ spf).symm

theorem oneTag_ok [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s : State} (h : onePre n wi s₀) (hn : 5 ≤ n) {o : Nat} (ho : o = 0 ∨ o = 112) {k7 : BitVec 32}
    (he : Env (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) s) (hk : ArgsKeep n s₀ s)
    (hH : blockAt s.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    {a : List Byte} (hl : (arg s₀ 0).toNat = a.length)
    (hab : Absorbed s.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (oSt s₀ wi) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (a ++ zeros (padLen a.length))) :
    WP isa (oneTag o) s (OT n wi s₀ o a (blockAt s.mem (State.addr (oSt s₀ wi))) s.mem) := by
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ n ∈ s₀.rd := h.1.2.2.2
  obtain hA := one_argsOt h ho
  obtain dC : ∀ r ∈ otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.cs.sub_right (Region.sub_prefix (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.cw'.sub_right (Lay.wSub (by omega_arith))
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · exact L.kc.symm
  obtain dJ : ∀ r ∈ absFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16 ++ tFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16,
      (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain e1 : ∀ {d k : Nat}, 16 ≤ d → d + k ≤ 80 →
        (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint ⟨State.addr (oSt s₀ wi) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := Lay.st_st (st := oSt s₀ wi) (a := 0) (n := 16) (.inl h1) (by decide) h2
      rwa [add_ofNat_zero] at this
    obtain e2 : ∀ {d k : Nat}, 96 ≤ d → d + k ≤ 768 →
        (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint ⟨State.addr (arg s₀ wi) + BitVec.ofNat 64 d, k⟩ := fun h1 h2 => by
      have := L.st_w (a := 0) (n := 16) (by decide) (.inr ⟨h1, h2⟩)
      rwa [add_ofNat_zero] at this
    obtain e3 : (⟨State.addr (oSt s₀ wi), 16⟩ : Region).Disjoint (below s₀.sp) := by
      have := (L.stk_st (a := 0) (n := 16) (by decide)).symm
      rwa [add_ofNat_zero] at this
    rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
    · exact e1 (by decide) (by decide)
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
    · exact e1 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e2 (by decide) (by decide)
    · exact e3
  obtain hx : (a ++ zeros (padLen a.length)).length % 16 = 0 := by
    simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _
  obtain ⟨s₁, run₁, h4, h5, h6, g₁, k₁⟩ := dataArgs_run hk spf hin hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain he₁ := he.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₁ _ (by decide) (by decide) (by decide)) k₁.sp k₁.rd k₁.wr
  obtain hk₁ := hk.of_eq k₁.mem k₁.sp k₁.rd k₁.wr
  obtain ai : AbsIn (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 (s₀.gpr .r3) 16 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (a ++ zeros (padLen a.length)) (arg s₀ 1) (arg s₀ 2).toNat s₁ :=
    ⟨he₁, h4, by rw [h5]; simp, by rw [h6, hx], one_dataOk h hk₁, by rw [k₁.mem]; exact hH⟩
  refine WP.seq (WP.mono (WP.with_rdwr (absorb_ok L (.inr rfl) ai)) fun s₂ hh => ?_)
  obtain ⟨ab, rd₂, wr₂, sp₂⟩ := hh
  rw [k₁.mem] at ab
  obtain hk₂ := hk₁.frame spf (k₁.mem ▸ ab.frame) (disj_sub hA abs_otSub) sp₂ rd₂ wr₂
  obtain ⟨b3, w3⟩ := hk₂.at spf hin 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
  obtain ⟨s₃, run₃, h6₃, g₃, k₃⟩ : ∃ s₃, runBlock isa [.ldrSp .r6 8, .dp .and .r6 .r6 (imm 15)] s₂ = some s₃ ∧
      s₃.gpr .r6 = BitVec.ofNat 32 ((arg s₀ 2).toNat % 16) ∧ (∀ r, r ≠ .r6 → s₃.gpr r = s₂.gpr r) ∧ Keeps s₂ s₃ := by
    refine ⟨_, by arun [b3, w3], ?_, ?_, ?_⟩
    · simp only [gpr_setReg, ite_true, w3, and15]
    · intro r x; simp [gpr_setReg, x]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain he₃ := ab.env.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₃ _ (by decide)) k₃.sp k₃.rd k₃.wr
  obtain hk₃ := hk₂.of_eq k₃.mem k₃.sp k₃.rd k₃.wr
  obtain hH₂ : blockAt s₂.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) := by
    rw [blockAt_frame ab.frame (ctx_absFrame L (.inr rfl))]; exact hH
  let ct := bytesAt s.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat
  obtain hlx : ((a ++ zeros (padLen a.length)) ++ ct).length % 16 = (arg s₀ 2).toNat % 16 := by
    simp only [List.length_append, Proof.Gcm.length_zeros, ct, length_bytesAt] at hx ⊢; omega_arith
  refine WP.seq (WP.mono (WP.with_rdwr (flush_ok L (yo := 16) (.inr rfl)
    (x := (a ++ zeros (padLen a.length)) ++ ct) (H := ctxH s₀.mem (State.addr (s₀.gpr .r0)))
    ⟨he₃, by rw [k₃.mem]; exact hH₂⟩ (by rw [h6₃, hlx]))) fun s₄ hh => ?_)
  obtain ⟨fl, rd₄, wr₄, sp₄⟩ := hh
  rw [k₃.mem] at fl
  obtain hk₄ := hk₂.frame spf fl.frame (disj_sub hA t_otSub) (sp₄.trans k₃.sp) (rd₄.trans k₃.rd) (wr₄.trans k₃.wr)
  obtain ⟨c1, x1⟩ := hk₄.at spf hin 0 (by omega_arith) (show 4 * 0 = 0 from rfl)
  obtain ⟨c3, x3⟩ := hk₄.at spf hin 2 (by omega_arith) (show 4 * 2 = 8 from rfl)
  obtain ⟨s₅, run₅, h4₅, h5₅, h6₅, h7₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r4 0, .mov .r5 (imm 0), .ldrSp .r6 8,
      .mov .r7 (imm 0)] s₄ = some s₅ ∧ s₅.gpr .r4 = arg s₀ 0 ∧ s₅.gpr .r5 = 0 ∧ s₅.gpr .r6 = arg s₀ 2 ∧
      s₅.gpr .r7 = 0 ∧ (∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [c1, x1, c3, x3], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, x1]
    · simp [gpr_setReg]
    · simp [gpr_setReg, x3]
    · simp [gpr_setReg]
    · intro r x y z q; simp [gpr_setReg, x, y, z, q]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ := fl.env.set7 h7₅ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide) (by decide) (by decide))
    k₅.sp k₅.rd k₅.wr
  obtain hk₅ := hk₄.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  refine WP.mono (WP.with_rdwr (tag_ok L ho he₅
    (H := ctxH s₀.mem (State.addr (s₀.gpr .r0))) (by rw [k₅.mem]; exact fl.hH) rfl)) fun s₆ hh => ?_
  obtain ⟨tg, rd₆, wr₆, sp₆⟩ := hh
  rw [h4₅, h5₅, h6₅, h7₅, k₅.mem] at tg
  obtain f₄ : Frame (absFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16 ++ tFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp 16) s.mem s₄.mem :=
    (ab.frame.mono (fun r hr => List.mem_append_left _ hr)).trans
      ((k₃.mem ▸ fl.frame : Frame _ s₂.mem s₄.mem).mono (fun r hr => List.mem_append_right _ hr))
  refine ⟨⟨_, tg.env⟩, hk₄.frame spf tg.frame (disj_sub hA tag_otSub) (sp₆.trans k₅.sp) (rd₆.trans k₅.rd)
    (wr₆.trans k₅.wr), ?_, ?_⟩
  · rw [tg.out]
    obtain hw := (fl.abs (ab.abs hab)).whole_eq (by
      simp only [List.length_append, Proof.Gcm.length_zeros]; exact Proof.Gcm.length_pad_mod _)
    rw [padded_eq] at hw
    rw [hw, ciph_frame f₄ (disj_sub dC (fun r hr => by
        simp only [List.mem_append] at hr
        rcases hr with hr | hr
        · exact abs_otSub r hr
        · exact t_otSub r hr)),
      blockAt_frame f₄ dJ]
    have z0 : (0 : BitVec 32).toNat = 0 := rfl
    obtain l1 : ((0 : BitVec 32) ++ arg s₀ 0).toNat = a.length := by
      rw [Proof.Gcm.toNat_append, ← hl, z0, Nat.zero_mul, Nat.zero_add]
    obtain l3 : ((0 : BitVec 32) ++ arg s₀ 2).toNat = ct.length := by
      rw [Proof.Gcm.toNat_append, length_bytesAt, z0, Nat.zero_mul, Nat.zero_add]
    rw [l1, l3]
  · refine (f₄.sub fun r hr => ?_).trans (tg.frame.sub tag_otSub)
    simp only [List.mem_append] at hr
    rcases hr with hr | hr
    · exact abs_otSub r hr
    · exact t_otSub r hr

end

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_seal`

Untrusted: everything here is checked by Lean. `seal` keeps a streaming
state at `W + 16`: `J₀` and the additional data (`oneAad`), the data
encrypted in place (`oneCrypt`), and the tag of the ciphertext into `W`
(`oneTag 0`), copied to `tag` (`tagOut`) (`seal_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput fullTag zeros padLen j0 inc32 gctr encryptWith toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed)

section
variable {n wi : Nat}

theorem one_dataW {s₀ s : State} (h : onePre n wi s₀) (hk : ArgsKeep n s₀ s) (k7 k8 : BitVec 32) :
    DataW (s₀.gpr .r0) (oSt s₀ wi) (arg s₀ wi) s₀.sp k7 k8 s (arg s₀ 1) (arg s₀ 2).toNat :=
  ⟨one_dataOk h hk, by rw [hk.wr]; exact covers_of_mem h.2.1.1, h.2.2.1⟩

theorem saved_otFrame {s₀ : State} (h : onePre n wi s₀) {o : Nat} (ho : o = 0 ∨ o = 112) :
    ∀ r ∈ otFrame (oSt s₀ wi) (arg s₀ wi) s₀.sp o, (savedR (arg s₀ wi)).Disjoint r := by
  have L := oneLay h
  have hst := oSt_addr h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [hst]; exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
  · exact Lay.w_w (.inr (by omega_using [ho])) (by decide) (by omega_using [ho])
  · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w (by decide)).symm

/-- What `seal`'s pieces leave, from the entry on. -/
theorem seal_mid {s₀ s₁ s₂ s₃ : State} (h : onePre n wi s₀) (h1 : SO1 n wi s₀ s₁) (oa : OA n wi s₀ s₁.mem s₂)
    {k7 : BitVec 32} (oc : OC n wi s₀ k7 (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat))) s₂.mem s₃) :
    blockAt s₃.mem (State.addr (s₀.gpr .r0) + BitVec.ofNat 64 240) = ctxH s₀.mem (State.addr (s₀.gpr .r0)) ∧
    Absorbed s₃.mem (State.addr (oSt s₀ wi) + BitVec.ofNat 64 16) (State.addr (oSt s₀ wi) + BitVec.ofNat 64 32)
      (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat ++
        zeros (padLen (bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat).length)) ∧
    blockAt s₃.mem (State.addr (oSt s₀ wi)) =
      j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat) ∧
    ciphOf s₃.mem (State.addr (s₀.gpr .r0)) =
      ctxCiph s₀.mem (State.addr (s₀.gpr .r0)) ∧
    bytesAt s₃.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat =
      gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
          (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat)))
        (bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat) ∧
    SavedAt s₃.mem (arg s₀ wi) s₀ := by
  have L := oneLay h
  have hd := one_dataW h oa.args 0 0
  have dCr := ctx_crFrame L hd
  have dc₂ : ∀ r ∈ [savedR (arg s₀ wi)] ++ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp,
      (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with rfl | hr
    · exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
  have f₂ : Frame ([savedR (arg s₀ wi)] ++ j0Frame (oSt s₀ wi) (arg s₀ wi) s₀.sp) s₀.mem s₂.mem :=
    (h1.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  have hc₂ := ciph_keep f₂ dc₂
  have hD₂ : bytesAt s₂.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat =
      bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat := by
    have hp := h
    obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hp
    exact bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with rfl | hr
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact one_dataJ0 h dDW bD r hr) (by have := hd.ok.lt; omega_using [])
  have hb := Nat.mod_lt (bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat ++
    zeros (padLen (bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat).length)).length (show 16 > 0 by decide)
  refine ⟨?_, (oa.abs.congr (blockAt_frame oc.frame (stp_crFrame L hd (by decide)))
      (bytesAt_frame oc.frame (stp_crFrame L hd (by omega_using [])) (by omega_using []))), ?_,
    by rw [ciph_frame oc.frame dCr, hc₂], by rw [oc.out, hc₂, hD₂],
    (h1.saved.frame oa.frame (saved_j0Frame L)).frame oc.frame (saved_crFrame L hd)⟩
  · rw [blockAt_frame oc.frame (fun r hr => (dCr r hr).sub_left (Lay.ctxSub (by decide)))]; exact oa.hH
  · rw [blockAt_frame oc.frame (by simpa using stp_crFrame L hd (d := 0) (k := 16) (by decide))]; exact oa.j

end

theorem seal_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : sealArm.pre s₀) :
    WP isa «seal» s₀ fun s' => abiPreserved s₀ s' ∧ sealArm.post s₀ s' := by
  have h' : onePre 5 4 s₀ := sealPreArm.one h
  have L := oneLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ 5 ∈ s₀.rd := h'.1.2.2.2
  obtain ⟨-, hwr, -, -, -, -, -, -, -, -, -, dT, -, -, tW, -, -, -, -, -, -, -, -, -, -, -, -, fT, -⟩ := h
  have dTW : ∀ {d k : Nat}, d + k ≤ 768 → (⟨State.addr (arg s₀ 3), 16⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 4) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  refine WP.seq (one1_wp (wi := 4) h' (by decide) (by decide) fun s₁ h1 =>
    WP.seq (WP.mono (oneAad_ok h' (by decide) h1) fun s₂ oa => ?_))
  obtain ⟨k7, he₂⟩ := oa.env
  refine WP.seq (WP.mono (oneCrypt_ok h' (by decide) he₂ oa.args oa.cb) fun s₃ oc => ?_)
  have he₃ := oc.env
  obtain ⟨hH₃, hab₃, hj₃, hc₃, hD₃, sv₃⟩ := seal_mid h' h1 oa oc
  refine WP.seq (WP.mono (oneTag_ok h' (by decide) (o := 0) (.inl rfl) he₃ oc.args hH₃ (length_bytesAt _ _ _).symm hab₃)
    fun s₄ ot => ?_)
  obtain ⟨k7'', he₄⟩ := ot.env
  obtain ⟨i4, v4⟩ := ot.args.at spf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  obtain ⟨s₅, run₅, hb₅, hf₅, g₅, rd₅, wr₅, sp₅⟩ := tagOut_ok L he₄ (.inr rfl) i4 v4
    (by rw [ot.args.wr, hwr]; exact covers_of_mem (by simp)) fT (by simpa using dTW (d := 0) (k := 16) (by decide))
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  have he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)) sp₅ rd₅ wr₅
  have sv₅ := (sv₃.frame ot.frame (saved_otFrame h' (.inl rfl))).frame hf₅ (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (dTW (by decide)).symm)
  refine WP.mono (restore_ok he₅.r11 fW (covers_left he₅.perm.w) sv₅ he₅.sp) fun s' hh => ⟨hh.1, ?_⟩
  have hm := hh.2.1
  have hpre := h'
  obtain ⟨-, -, -, -, -, -, -, -, dDW, -, -, -, -, -, bD, -⟩ := hpre
  have hD₄ : bytesAt s₄.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat =
      bytesAt s₃.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat := by
    refine bytesAt_frame ot.frame (fun r hr => ?_) (by omega_using [])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [oSt_addr h']; exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact dDW.sub_right (Lay.wSub (by decide))
    · exact bD.symm
  have hD₅ : bytesAt s₅.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat =
      bytesAt s₄.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat :=
    bytesAt_frame hf₅ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dT) (by omega_using [])
  have ho := ot.out
  rw [hc₃, hj₃, add_ofNat_zero, ← Proof.Gcm.fullTag_eq] at ho
  simp only [sealArm, encryptWith, hm, hD₅, hD₄, hD₃, hb₅, ho]
  refine Prod.ext rfl ?_
  exact List.take_of_length_le (by
    rw [Spec.Gcm.fullTag, Proof.Gcm.length_gctr, Cmac.toBytes_length])

end VG.Proof.Sm4Gcm.Arm

end

end

/-!
# SM4-GCM on ARMv7: `vg_sm4_gcm_open`

Untrusted: everything here is checked by Lean. `open` checks the tag length;
if it is allowed, it computes the tag of the ciphertext into `W + 112`
(`oneAad`, `oneTag 112`), copies the received tag (at `tag`) to `W + 256`, compares
the first `tag_len` bytes of each, and decrypts the data in place only if
they are equal; `r0` is the result (`open_wp`).
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.Sm4Gcm.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Sm4Gcm.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (Block blockAt ghashInput fullTag zeros padLen j0 inc32 gctr decryptWith openResult toBytes)
open VG.Spec.Sm4.Gcm (ctxCiph)
open VG.Spec.Gcm (ctxH)
open VG.Proof.Gcm (Absorbed)

theorem SO1.keep {n wi : Nat} {s₀ s₁ s₂ : State} (h1 : SO1 n wi s₀ s₁)
    (hg : ∀ r, r ≠ .r0 → r ≠ .r6 → s₂.gpr r = s₁.gpr r) (hk : Keeps s₁ s₂) : SO1 n wi s₀ s₂ :=
  ⟨h1.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide)) hk.sp hk.rd hk.wr,
    by rw [hg _ (by decide) (by decide)]; exact h1.r4, by rw [hg _ (by decide) (by decide)]; exact h1.r5,
    h1.args.of_eq hk.mem hk.sp hk.rd hk.wr, hk.mem ▸ h1.saved, hk.mem ▸ h1.frame⟩

/-- What `open` promises, given the result `r0` and the data. -/
def OpenPost (s₀ s : State) : Prop :=
  match openRes s₀ with
  | some pt => s.gpr .r0 = 1 ∧ bytesAt s.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat = pt
  | none => s.gpr .r0 = 0 ∧
      bytesAt s.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat = bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat

theorem openPost_none {s₀ s : State} (h : openRes s₀ = none) (h0 : s.gpr .r0 = 0)
    (hd : bytesAt s.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat = bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat) :
    OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

theorem openPost_some {s₀ s : State} {pt : List Byte} (h : openRes s₀ = some pt) (h0 : s.gpr .r0 = 1)
    (hd : bytesAt s.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat = pt) : OpenPost s₀ s := by
  unfold OpenPost; rw [h]; exact ⟨h0, hd⟩

/-- The code of `open` once the tag length is known to be allowed. -/
abbrev openGood : Prog isa :=
  .seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 16]) (.seq (recv 12) (.seq (cmp uO)
    (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) (.seq (.ite .eq (.block []) oneCrypt)
      (.block [.mov .r0 (.reg .r7)])))))))

/-- Whether the computed tag, cut to the tag length, is the received one. -/
abbrev openTagOk (s₀ : State) : Prop :=
  (fullTag (ctxCiph s₀.mem (State.addr (s₀.gpr .r0))) (ctxH s₀.mem (State.addr (s₀.gpr .r0)))
      (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat)
      (bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat)
      (bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat)).take (arg s₀ 4).toNat =
    bytesAt s₀.mem (State.addr (arg s₀ 3)) (arg s₀ 4).toNat

/-- After the tags are compared, with the result in `r7` and `Z`. -/
structure OpenMid (s₀ s : State) : Prop where
  env : Env (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s.gpr .r7) (s₀.gpr .r3) s
  args : ArgsKeep 6 s₀ s
  saved : SavedAt s.mem (arg s₀ 5) s₀
  dat : bytesAt s.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat = bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat
  ciph : ciphOf s.mem (State.addr (s₀.gpr .r0)) =
    ctxCiph s₀.mem (State.addr (s₀.gpr .r0))
  cb : blockAt s.mem (State.addr (oSt s₀ 5) + BitVec.ofNat 64 48) =
    inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat))
  r7 : s.gpr .r7 = if openTagOk s₀ then 1 else 0
  z : s.z = decide (¬ openTagOk s₀)

/-- `open` up to the comparison of the tags, followed by any `T`. -/
theorem open_head [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₂ : State} (ho : openPreArm s₀) (h2 : SO1 6 5 s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ 4).toNat = true) {T : Prog isa} {Q : State → Prop}
    (k : ∀ s₈, OpenMid s₀ s₈ → WP isa T s₈ Q) :
    WP isa (.seq oneAad (.seq (oneTag uO) (.seq (.block [.ldrSp .r6 16]) (.seq (recv 12) (.seq (cmp uO)
      (.seq (.block [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)]) T)))))) s₂ Q := by
  obtain h : onePre 6 5 s₀ := openPreArm.one ho
  obtain ⟨hrd, -, -, -, -, -, -, -, -, -, -, tW, -, -, -, -, -, bT, -, -, -, -, -, fT, -⟩ := ho
  obtain dTW : ∀ {d k : Nat}, d + k ≤ 768 → (⟨State.addr (arg s₀ 3), (arg s₀ 4).toNat⟩ : Region).Disjoint
      ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ := fun hd => tW.sub_right (Lay.wSub hd)
  obtain L := oneLay h
  have spf := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ 6 ∈ s₀.rd := h.1.2.2.2
  obtain ⟨t1, t16⟩ := tagLenOk_bounds hok
  obtain dW : ∀ {d k : Nat}, d + k ≤ 768 → (164 ≤ d ∨ d + k ≤ 128) →
      (savedR (arg s₀ 5)).Disjoint ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ :=
    fun h₁ h₂ => Lay.w_w (by omega_using [h₂]) (by decide) h₁
  refine WP.seq (WP.mono (oneAad_ok h (by decide) h2) fun s₃ oa => ?_)
  obtain ⟨k7, he₃⟩ := oa.env
  refine WP.seq (WP.mono (oneTag_ok h (by decide) (o := 112) (.inr rfl) he₃ oa.args oa.hH (length_bytesAt _ _ _).symm
    oa.abs) fun s₄ ot => ?_)
  obtain ⟨k7₄, he₄⟩ := ot.env
  obtain ⟨j5, w5⟩ := ot.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨s₅, run₅, h6₅, g₅, k₅⟩ : ∃ s₅, runBlock isa [.ldrSp .r6 16] s₄ = some s₅ ∧
      s₅.gpr .r6 = BitVec.ofNat 32 (arg s₀ 4).toNat ∧ (∀ r, r ≠ .r6 → s₅.gpr r = s₄.gpr r) ∧ Keeps s₄ s₅ := by
    refine ⟨_, by arun [j5, w5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, w5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  obtain he₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₅ _ (by decide)) k₅.sp k₅.rd k₅.wr
  obtain hk₅ := ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr
  obtain ⟨i4, v4⟩ := hk₅.at spf hin 3 (by decide) (show 4 * 3 = 12 from rfl)
  refine WP.seq (WP.mono (recv_ok L he₅ (.inr rfl) i4 v4
    (by rw [hk₅.rd, hk₅.wr]; exact covers_of_mem (List.mem_append_left _ (by rw [hrd]; simp))) fT
    (dTW (by decide)) h6₅ t1 t16) fun s₆ hh => ?_)
  obtain ⟨hb₆, hf₆, g₆, rd₆, wr₆, sp₆⟩ := hh
  obtain he₆ := he₅.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₆ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₆ rd₆ wr₆
  obtain h6₆ : s₆.gpr .r6 = BitVec.ofNat 32 (arg s₀ 4).toNat := by
    rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide), h6₅]
  refine WP.seq (WP.mono (cmp_ok L he₆ (o := 112) (.inr rfl) h6₆ t1 t16) fun s₇ hh => ?_)
  obtain ⟨h0₇, hf₇, g₇, rd₇, wr₇, sp₇⟩ := hh
  obtain he₇ := he₆.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact g₇ _ (by decide) (by decide) (by decide) (by decide)
      (by decide)) sp₇ rd₇ wr₇
  -- what the pieces leave
  let rs : List Region := [savedR (arg s₀ 5)] ++ j0Frame (oSt s₀ 5) (arg s₀ 5) s₀.sp ++
    otFrame (oSt s₀ 5) (arg s₀ 5) s₀.sp 112 ++
    [⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 240, 16⟩]
  obtain F₇ : Frame rs s₀.mem s₇.mem := by
    have e₂ : Frame [savedR (arg s₀ 5)] s₀.mem s₂.mem := h2.frame
    refine ((((e₂.mono ?_).trans (oa.frame.mono ?_)).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [rs, List.mem_append]
    · exact .inl (.inl (.inl hr))
    · exact .inl (.inl (.inr hr))
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  have hp := h
  obtain ⟨-, -, dcD, dcW, -, -, -, -, dDW, -, -, bc, -, -, bD, bW, -⟩ := hp
  obtain dC : ∀ r ∈ rs, (⟨State.addr (s₀.gpr .r0), 256⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact L.cw'.sub_right (Lay.wSub (by decide))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact L.cs
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact L.cs.sub_right (Region.sub_prefix (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.kc.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.cw'.sub_right (Lay.wSub (by decide))
      · exact L.cw'.sub_right (Lay.wSub (by decide))
  obtain dD : ∀ r ∈ rs, (⟨State.addr (arg s₀ 1), (arg s₀ 2).toNat⟩ : Region).Disjoint r := by
    intro r hr
    simp only [rs, List.mem_append] at hr
    rcases hr with ((hr | hr) | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact dDW.sub_right (Lay.wSub (by decide))
    · exact one_dataJ0 h dDW bD r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [oSt_addr h]; exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact bD.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dDW.sub_right (Lay.wSub (by decide))
      · exact dDW.sub_right (Lay.wSub (by decide))
  let ciph := ctxCiph s₀.mem (State.addr (s₀.gpr .r0))
  let H := ctxH s₀.mem (State.addr (s₀.gpr .r0))
  let iv := bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat
  let aad := bytesAt s₀.mem (State.addr (s₀.gpr .r3)) (arg s₀ 0).toNat
  let dat := bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat
  let tl := (arg s₀ 4).toNat
  let tag₀ := bytesAt s₀.mem (State.addr (arg s₀ 3)) tl
  obtain F₃ : Frame ([savedR (arg s₀ 5)] ++ j0Frame (oSt s₀ 5) (arg s₀ 5) s₀.sp) s₀.mem s₃.mem :=
    (h2.frame.mono fun r hr => List.mem_append_left _ hr).trans (oa.frame.mono fun r hr => List.mem_append_right _ hr)
  obtain sub₃ : ∀ r ∈ [savedR (arg s₀ 5)] ++ j0Frame (oSt s₀ 5) (arg s₀ 5) s₀.sp, r ∈ rs := fun r hr => by
    simp only [rs, List.mem_append] at hr ⊢; exact .inl (.inl hr)
  obtain hD₃ : bytesAt s₃.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat = dat :=
    bytesAt_frame F₃ (fun r hr => dD r (sub₃ r hr)) (by omega_using [])
  obtain hT₄ : bytesAt s₄.mem (State.addr (arg s₀ 5) + BitVec.ofNat 64 112) 16 = fullTag ciph H iv aad dat := by
    rw [ot.out, hD₃, ciph_keep F₃ (fun r hr => dC r (sub₃ r hr)), oa.j, ← Proof.Gcm.fullTag_eq]
  obtain F₄ : Frame ([savedR (arg s₀ 5)] ++ j0Frame (oSt s₀ 5) (arg s₀ 5) s₀.sp ++ otFrame (oSt s₀ 5) (arg s₀ 5) s₀.sp 112)
      s₀.mem s₄.mem :=
    (F₃.mono fun r hr => List.mem_append_left _ hr).trans (ot.frame.mono fun r hr => List.mem_append_right _ hr)
  obtain hR₀ : bytesAt s₄.mem (State.addr (arg s₀ 3)) tl = tag₀ := by
    refine bytesAt_frame F₄ (fun r hr => ?_) (by omega_using [])
    obtain hst := oSt_addr h
    obtain z : ∀ {d k : Nat}, d + k ≤ 768 → 16 ≤ d →
        (⟨State.addr (arg s₀ 3), tl⟩ : Region).Disjoint ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, k⟩ :=
      fun h₁ _ => dTW h₁
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · simp only [List.mem_singleton] at hr; subst hr; exact z (by decide) (by decide)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [hst]; exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact z (by decide) (by decide)
      · exact bT.symm
  obtain hX : (bytesAt s₆.mem (State.addr (arg s₀ 5) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ 5) + BitVec.ofNat 64 256) 16) ↔ (fullTag ciph H iv aad dat).take tl = tag₀ := by
    rw [hb₆, k₅.mem, hR₀, bytesAt_frame hf₆ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega)) (by omega) (by decide))
        (by omega_using []), k₅.mem, bytesAt_take _ _ t16, hT₄, List.append_cancel_right_eq]
  let X : Prop := bytesAt s₆.mem (State.addr (arg s₀ 5) + BitVec.ofNat 64 112) tl ++ zeros (16 - tl) =
      bytesAt s₆.mem (State.addr (arg s₀ 5) + BitVec.ofNat 64 256) 16
  obtain ⟨s₈, run₈, h7₈, hz₈, g₈, k₈⟩ : ∃ s₈, runBlock isa [.mov .r7 (.reg .r0), .cmp .r0 (imm 0)] s₇ = some s₈ ∧
      s₈.gpr .r7 = s₇.gpr .r0 ∧ s₈.z = decide ((s₇.gpr .r0).toNat = 0) ∧ (∀ r, r ≠ .r7 → s₈.gpr r = s₇.gpr r) ∧
      Keeps s₇ s₈ := by
    refine ⟨_, by arun [], ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg]
    · simp only [z_subFlags, gpr_setReg, reduceCtorEq, ite_false]; exact z_sub0 _
    · intro r hr; simp only [gpr_subFlags, gpr_setReg, hr, ite_false]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.seq (WP.of_runBlock ⟨s₈, run₈, ?_⟩)
  obtain he₈ := he₇.set7 h7₈ (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact g₈ _ (by decide)) k₈.sp k₈.rd k₈.wr
  obtain dA6 : ∀ {d : Nat}, d + 16 ≤ 768 → ∀ r ∈ [(⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 d, 16⟩ : Region)],
      (args s₀ 6).Disjoint r := fun hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.2.2.2.2.2.2.2.2.2.2.1.sub_left (Lay.wSub hd)).symm
  obtain hk₈ : ArgsKeep 6 s₀ s₈ :=
    ((((ot.args.of_eq k₅.mem k₅.sp k₅.rd k₅.wr).frame spf hf₆ (dA6 (by decide)) sp₆ rd₆ wr₆).frame spf hf₇
      (dA6 (by decide)) sp₇ rd₇ wr₇).of_eq k₈.mem k₈.sp k₈.rd k₈.wr)
  obtain F₈ : Frame rs s₀.mem s₈.mem := by rw [k₈.mem]; exact F₇
  obtain hdat₈ : bytesAt s₈.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat = dat := bytesAt_frame F₈ dD (by omega_using [])
  obtain hc₈ : ciphOf s₈.mem (State.addr (s₀.gpr .r0)) = ciph := ciph_keep F₈ dC
  obtain hcb₈ : blockAt s₈.mem (State.addr (oSt s₀ 5) + BitVec.ofNat 64 48) = inc32 (j0 H iv) := by
    obtain F₃₈ : Frame (otFrame (oSt s₀ 5) (arg s₀ 5) s₀.sp 112 ++
        [⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 240, 16⟩])
        s₃.mem s₈.mem := by
      rw [k₈.mem]
      refine ((ot.frame.mono fun r hr => List.mem_append_left _ hr).trans
        ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono fun r hr => ?_)).trans (hf₇.mono fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; simp [hr]
      · simp only [List.mem_singleton] at hr; simp [hr]
    rw [blockAt_frame F₃₈ (fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
      · have := Lay.st_st (st := oSt s₀ 5) (a := 48) (n := 16) (d := 0) (k := 48) (.inr (by decide)) (by decide)
          (by decide)
        rwa [add_ofNat_zero] at this
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact (L.stk_st (by decide)).symm
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩)
      · exact L.st_w (by decide) (.inr ⟨by decide, by decide⟩))]
    exact oa.cb
  obtain F₂₈ : Frame (j0Frame (oSt s₀ 5) (arg s₀ 5) s₀.sp ++ otFrame (oSt s₀ 5) (arg s₀ 5) s₀.sp 112 ++
      [⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 256, 16⟩, ⟨State.addr (arg s₀ 5) + BitVec.ofNat 64 240, 16⟩])
      s₂.mem s₈.mem := by
    rw [k₈.mem]
    refine (((oa.frame.mono ?_).trans (ot.frame.mono ?_)).trans
      ((k₅.mem ▸ hf₆ : Frame _ s₄.mem s₆.mem).mono ?_)).trans (hf₇.mono ?_)
    all_goals intro r hr; simp only [List.mem_append]
    · exact .inl (.inl hr)
    · exact .inl (.inr hr)
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
    · simp only [List.mem_singleton] at hr; exact .inr (by simp [hr])
  obtain sv₈ : SavedAt s₈.mem (arg s₀ 5) s₀ := by
    refine h2.saved.frame F₂₈ fun r hr => ?_
    simp only [List.mem_append] at hr
    rcases hr with (hr | hr) | hr
    · exact saved_j0Frame L r hr
    · exact saved_otFrame h (.inr rfl) r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dW (by decide) (.inl (by decide))
      · exact dW (by decide) (.inl (by decide))
  obtain hX0 : (s₇.gpr .r0).toNat = 0 ↔ ¬X := by
    rw [h0₇]
    split
    · next hx => exact ⟨fun e => absurd e (by decide), fun e => absurd hx e⟩
    · next hx => exact ⟨fun _ => hx, fun _ => rfl⟩
  refine k s₈ ⟨by rw [h7₈]; exact he₈, hk₈, sv₈, hdat₈, hc₈, hcb₈, ?_, ?_⟩
  · rw [h7₈, h0₇]; exact ite_congr (propext hX) (fun _ => rfl) (fun _ => rfl)
  · rw [hz₈]; exact decide_eq_decide.mpr (hX0.trans (not_congr hX))

theorem open_good [VG.Proof.Gcm.Arm.GhashLaw] {s₀ s₂ : State} (ho : openPreArm s₀) (h2 : SO1 6 5 s₀ s₂)
    (hok : Spec.Gcm.tagLenOk (arg s₀ 4).toNat = true) :
    WP isa openGood s₂ fun s => (∃ k7, Env (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp k7 (s₀.gpr .r3) s) ∧
      SavedAt s.mem (arg s₀ 5) s₀ ∧ OpenPost s₀ s := by
  obtain h : onePre 6 5 s₀ := openPreArm.one ho
  obtain L := oneLay h
  refine open_head ho h2 hok fun s₈ om => ?_
  -- the data decrypted only if the tags are equal
  obtain mid : WP isa (.ite .eq (.block []) oneCrypt) s₈ fun s₉ =>
      Env (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp (s₈.gpr .r7) (s₀.gpr .r3) s₉ ∧ SavedAt s₉.mem (arg s₀ 5) s₀ ∧
      (openTagOk s₀ → bytesAt s₉.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat =
        gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
          (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat)))
          (bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat)) ∧
      (¬openTagOk s₀ → bytesAt s₉.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat =
        bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat) := by
    refine WP.ite _ (eval_eq' om.z) (fun ht => ?_) (fun hf => ?_)
    · have hx : ¬openTagOk s₀ := of_decide_eq_true ht
      exact WP.block_nil ⟨om.env, om.saved, fun x => absurd x hx, fun _ => om.dat⟩
    · have hx : openTagOk s₀ := Classical.not_not.mp (of_decide_eq_false hf)
      refine WP.mono (oneCrypt_ok h (by decide) om.env om.args om.cb) fun s₉ oc => ?_
      exact ⟨oc.env, om.saved.frame oc.frame (saved_crFrame L (one_dataW h om.args 0 0)),
        fun _ => by rw [oc.out, om.ciph, om.dat], fun x => absurd hx x⟩
  refine WP.seq (WP.mono mid fun s₉ hh => ?_)
  obtain ⟨he₉, sv₉, hd₁, hd₂⟩ := hh
  refine WP.of_runBlock ⟨s₉.setReg .r0 (s₉.gpr .r7), by arun [], ⟨_, he₉.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, sv₉, ?_⟩
  obtain hres : openRes s₀ = if openTagOk s₀ then
      some (gctr (ctxCiph s₀.mem (State.addr (s₀.gpr .r0)))
        (inc32 (j0 (ctxH s₀.mem (State.addr (s₀.gpr .r0))) (bytesAt s₀.mem (State.addr (s₀.gpr .r1)) (s₀.gpr .r2).toNat)))
        (bytesAt s₀.mem (State.addr (arg s₀ 1)) (arg s₀ 2).toNat)) else none := by
    simp only [openRes, openResult, hok, ite_true, decryptWith]
  obtain r0 : (s₉.setReg .r0 (s₉.gpr .r7)).gpr .r0 = if openTagOk s₀ then 1 else 0 := by
    rw [gpr_setReg_self, he₉.r7, om.r7]
  by_cases e : openTagOk s₀
  · exact openPost_some (hres.trans (ite_eq_left_of_eq_true _ _ (eq_true e)))
      (r0.trans (ite_eq_left_of_eq_true _ _ (eq_true e))) (hd₁ e)
  · exact openPost_none (hres.trans (ite_eq_right_of_eq_false _ _ (eq_false e)))
      (r0.trans (ite_eq_right_of_eq_false _ _ (eq_false e))) (hd₂ e)

theorem open_wp [VG.Proof.Gcm.Arm.GhashLaw] {s₀ : State} (h : openArm.pre s₀) :
    WP isa «open» s₀ fun s' => abiPreserved s₀ s' ∧ openArm.post s₀ s' := by
  obtain h' : onePre 6 5 s₀ := openPreArm.one h
  obtain L := oneLay h'
  have fW := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spf := h'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hin : args s₀ 6 ∈ s₀.rd := h'.1.2.2.2
  refine WP.seq (WP.block_append (one1_wp (wi := 5) h' (by decide) (by decide) fun s₁ h1 => ?_))
  obtain ⟨i5, v5⟩ := h1.args.at spf hin 4 (by decide) (show 4 * 4 = 16 from rfl)
  obtain ⟨s₂, run₂, h6₂, g₂, k₂⟩ : ∃ s₂, runBlock isa [.ldrSp .r6 16] s₁ = some s₂ ∧
      s₂.gpr .r6 = BitVec.ofNat 32 (arg s₀ 4).toNat ∧ (∀ r, r ≠ .r6 → s₂.gpr r = s₁.gpr r) ∧ Keeps s₁ s₂ := by
    refine ⟨_, by arun [i5, v5], ?_, ?_, ?_⟩
    · simp [gpr_setReg, v5]
    · intro r hr; simp [gpr_setReg, hr]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine WP.seq (WP.mono (tagLenOk_ok h6₂ (arg s₀ 4).isLt) fun s₃ ⟨hz₃, g₃, k₃⟩ => ?_)
  obtain h3 : SO1 6 5 s₀ s₃ := (h1.keep (fun r a b => g₂ r b) k₂).keep (fun r a b => g₃ r a) k₃
  obtain mid : WP isa (.ite .eq (.block [.mov .r0 (imm 0)]) openGood) s₃ fun s =>
      (∃ k7, Env (s₀.gpr .r0) (oSt s₀ 5) (arg s₀ 5) s₀.sp k7 (s₀.gpr .r3) s) ∧
      SavedAt s.mem (arg s₀ 5) s₀ ∧ OpenPost s₀ s := by
    refine WP.ite _ (eval_eq' hz₃) (fun ht => ?_) (fun hf => open_good h h3 (by simpa using hf))
    obtain hbad : Spec.Gcm.tagLenOk (arg s₀ 4).toNat = false := by simpa using ht
    refine WP.of_runBlock ⟨s₃.setReg .r0 (BitVec.ofNat 32 0), by arun [], ⟨_, h3.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl) rfl rfl rfl⟩, h3.saved, ?_⟩
    refine openPost_none (by simp only [openRes, openResult, hbad]; rfl) (by simp [gpr_setReg]) ?_
    show bytesAt s₃.mem _ _ = _
    exact bytesAt_frame h3.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact h'.2.2.2.2.2.2.2.2.1.sub_right (Lay.wSub (by decide))) (by omega_using [])
  refine WP.seq (WP.mono mid fun s₄ hh => ?_)
  obtain ⟨⟨k7, he⟩, sv, op⟩ := hh
  refine WP.mono (restore_ok he.r11 fW (covers_left he.perm.w) sv he.sp) fun s' hh => ⟨hh.1, ?_⟩
  obtain e : OpenPost s₀ s' := by
    unfold OpenPost at op ⊢; rw [hh.2.1, hh.2.2.1]; exact op
  exact e

end VG.Proof.Sm4Gcm.Arm
