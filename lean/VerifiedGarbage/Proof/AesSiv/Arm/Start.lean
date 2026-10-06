import VerifiedGarbage.Proof.AesSiv.Arm.Ctr
import VerifiedGarbage.Proof.AesGcm.Arm.Fn

/-!
# AES-SIV on ARMv7: the entry, and S2V's first state

Untrusted: everything here is checked by Lean. `encrypt` and `decrypt` take
the key context in `r0`, the rounds in `r1`, the descriptors in `r2` and
their number in `r3`, and the data, its length, `siv` and `W` on the stack
(`EPre`). They save our caller's registers in `W` where AES-GCM does
(`Proof.AesGcm.Arm.save_ok`), keep their arguments in registers, zero the
block at `W + 16` and `D`, and finalize the zero block into `D`:
`D = AES-CMAC(K1, <zero>)` (`start_ok`), S2V's first state.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Impl.AesGcm.Arm (imm addI save)
open VG.Impl.CmacAes.Arm (mov)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR save_ok covers_left covers_prefix in_off)
open VG.Proof.MdStream.Arm (wp_ldrSp)

/-- What `encrypt` and `decrypt` need of their arguments: the key context
`c`, the rounds `R`, the `N` descriptors at `a`, the data (`n` bytes at `D`),
`siv` (16 bytes at `T`, which they may at least read) and `W`, the last four
on the stack at `sp`. -/
structure EPre (c w sp a D T : BitVec 32) (R N n : Nat) (s : State) : Prop where
  lay : Lay c w sp
  perm : Perm c w s
  r0 : s.gpr .r0 = c
  r1 : s.gpr .r1 = BitVec.ofNat 32 R
  r2 : s.gpr .r2 = a
  r3 : s.gpr .r3 = BitVec.ofNat 32 N
  hsp : s.sp = sp
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  afit : sp.toNat + 16 ≤ 2 ^ 32
  args : Covers [⟨State.addr sp, 16⟩] (s.rd ++ s.wr)
  args_w : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  args_d : (⟨State.addr sp, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩
  a0 : s.mem.readW (State.addr sp) 32 = D
  a1 : s.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n
  a2 : s.mem.readW (State.addr sp + BitVec.ofNat 64 8) 32 = T
  a3 : s.mem.readW (State.addr sp + BitVec.ofNat 64 12) 32 = w
  ads : Ads w sp a N s.mem s
  data : Dat c w sp s D n
  n32 : n < 2 ^ 32
  tfit : T.toNat + 16 ≤ 2 ^ 32
  t_rd : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)
  t_w : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 2576⟩
  t_stk : (blw sp).Disjoint ⟨State.addr T, 16⟩

/-- The descriptors as they were, after writes apart from them. -/
theorem Ads.of_frame {w sp a : BitVec 32} {N : Nat} {m m' : Mem} {s : State} (h : Ads w sp a N m s)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r) :
    Ads w sp a N m' s := by
  have e : ∀ i < N, ∀ j < 2, descW m' a i j = descW m a i j := fun i hi j hj =>
    hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)
  exact { h with comp := fun i hi => by rw [e i hi 0 (by decide), e i hi 1 (by decide)]; exact h.comp i hi }

/-- The components as they were, after writes apart from them. -/
theorem components_frame {a : BitVec 32} {N : Nat} {m m' : Mem}
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨State.addr a, 8 * N⟩ : Region).Disjoint r)
    (hc : ∀ i < N, ∀ r ∈ rs, (⟨State.addr (descW m a i 0), (descW m a i 1).toNat⟩ : Region).Disjoint r) :
    Spec.Siv.components 32 m' (State.addr a) N = Spec.Siv.components 32 m (State.addr a) N := by
  have e : ∀ i < N, ∀ j < 2, descW m' a i j = descW m a i j := fun i hi j hj =>
    hf.readW (r := ⟨State.addr a + BitVec.ofNat 64 (8 * i + 4 * j), 4⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (Offset.sub_base _ (by omega))) (by decide)
  apply List.ext_getElem (by rw [length_components, length_components])
  intro i h₁ h₂
  rw [length_components] at h₂
  rw [components_getElem m' a h₂, components_getElem m a h₂, e i h₂ 0 (by decide), e i h₂ 1 (by decide)]
  exact bytesAt_frame hf (hc i h₂) (by have := (descW m a i 1).isLt; omega)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

theorem saved_wR : ∀ r ∈ wR w sp, (savedR w).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact L.w_w (a := 128) (n := 36) (d := 16) (m := 112) (.inr (by decide)) (by decide) (by decide)
  · exact L.w_w (.inl (by decide)) (by decide) (by decide)
  · exact (L.stk_w' (by decide)).symm

omit L in
/-- What the entry leaves, before the call of `vg_cmac_aes_finalize` that
computes S2V's first state: the registers saved in the memory `mₛ`, the
zero block at `W + 16` and `D` zeroed, and the arguments of the call. -/
structure Started (c w sp a : BitVec 32) (R N : Nat) (s : State) (mₛ : Mem) (s' : State) : Prop where
  fs : Frame [savedR w] s.mem mₛ
  sv : SavedAt mₛ w s
  env : Env c w sp R s'
  r8 : s'.gpr .r8 = a
  r7 : s'.gpr .r7 = BitVec.ofNat 32 N
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  frame : Frame (wR w sp) mₛ s'.mem
  zD : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 = Spec.Cmac.zeros 16
  zZ : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 zOff) 16 = Spec.Cmac.zeros 16
  args : FArgs s' c (w + BitVec.ofNat 32 dOff) (w + BitVec.ofNat 32 zOff) (w + BitVec.ofNat 32 256) 16 R

/-- The entry, up to the call. -/
theorem startBlock_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa (.block (encPre ++ startPre)) s fun s' => ∃ mₛ, Started c w sp a R N s mₛ s' := by
  have ww := L.ww
  have hR := h.rounds
  rw [encPre, List.cons_append]
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 12) (by decide)
    (by rw [h.hsp]; exact addr_add (by have := h.afit; omega)) (in_off h.args (by decide) (by decide))
    fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = w := by rw [u₁.gpr, h.a3]
  simp only [List.append_eq, List.append_assoc]
  refine save_ok h12 (by omega) (by rw [u₁.wr]; exact covers_prefix h.perm.w (by decide))
    fun s₂ g₂ rd₂ wr₂ sp₂ sv₂ f₂ => ?_
  have hrd₂ : s₂.rd = s.rd := by rw [rd₂, u₁.rd]
  have hwr₂ : s₂.wr = s.wr := by rw [wr₂, u₁.wr]
  have hsp₂ : s₂.sp = sp := by rw [sp₂, u₁.sp, h.hsp]
  have gg : ∀ r, r ≠ .r12 → s₂.gpr r = s.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  obtain ⟨s₃, run₃, he₃, h8₃, h7₃, k₃⟩ : ∃ s₃, runBlock isa [mov .r11 .r12, mov .r10 .r0, mov .r9 .r1,
      mov .r8 .r2, mov .r7 .r3] s₂ = some s₃ ∧ Env c w sp R s₃ ∧ s₃.gpr .r8 = a ∧ s₃.gpr .r7 = BitVec.ofNat 32 N ∧
      Proof.AesGcm.Arm.Keeps s₂ s₃ := by
    have e0 : s₂.gpr .r0 = c := by rw [gg _ (by decide), h.r0]
    have e1 : s₂.gpr .r1 = BitVec.ofNat 32 R := by rw [gg _ (by decide), h.r1]
    have e2 : s₂.gpr .r2 = a := by rw [gg _ (by decide), h.r2]
    have e3 : s₂.gpr .r3 = BitVec.ofNat 32 N := by rw [gg _ (by decide), h.r3]
    have e12 : s₂.gpr .r12 = w := by rw [g₂, h12]
    refine ⟨_, by simp only [mov]; arun [], ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · simp [gpr_setReg, e1]
    · simp [gpr_setReg, e0]
    · simp [gpr_setReg, e12]
    · simp [sp_setReg, hsp₂]
    · exact h.perm.of_eq (by simp [rd_setReg, hrd₂]) (by simp [wr_setReg, hwr₂])
    · simp [gpr_setReg, e2]
    · simp [gpr_setReg, e3]
    · exact ⟨rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  simp only [startPre, List.append_assoc]
  refine zero16_ok L he₃ (d := zOff) (by decide) fun s₄ g₄ m₄ rd₄ wr₄ sp₄ => ?_
  have he₄ : Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide)) sp₄ rd₄ wr₄
  refine zero16_ok L he₄ (d := dOff) (by decide) fun s₅ g₅ m₅ rd₅ wr₅ sp₅ => ?_
  have he₅ : Env c w sp R s₅ := he₄.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide)) sp₅ rd₅ wr₅
  have eZ := L.wA (d := zOff) (by decide)
  have eD := L.wA (d := dOff) (by decide)
  obtain ⟨s₆, run₆, he₆, g₆, k₆, F⟩ : ∃ s₆, runBlock isa (macArgs dOff ++ [addI .r3 .r11 zOff, .mov .r12 (imm 16)])
      s₅ = some s₆ ∧ Env c w sp R s₆ ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s₅.gpr r) ∧
      Proof.AesGcm.Arm.Keeps s₅ s₆ ∧
      FArgs s₆ c (w + BitVec.ofNat 32 dOff) (w + BitVec.ofNat 32 zOff) (w + BitVec.ofNat 32 256) 16 R := by
    refine ⟨_, by simp only [macArgs, csOff, zOff, dOff]; arun [he₅.r9, he₅.r10, he₅.r11], ?_⟩
    refine ⟨he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl,
      fun r a b c' d e f => by simp [gpr_setReg, a, b, c', d, e, f], ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
    refine fargs_of L ?_ hR (st := dOff) (.inr ⟨by decide, by decide⟩) (n := 16) (by decide)
      (by rw [L.wN (by decide)]; simp only [zOff]; omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact he₅.keep (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [gpr_setReg]) rfl rfl rfl
    · rw [eZ]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eZ]; exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [eZ]; exact L.stk_w' (by decide)
    · rw [eZ]; exact covers_left (he₅.perm.wC (by decide))
    · simp [gpr_setReg, he₅.r10]
    · simp [gpr_setReg, he₅.r9]
    · simp [gpr_setReg, he₅.r11]
    · simp [gpr_setReg, he₅.r11]
    · simp [gpr_setReg]
    · simp [gpr_setReg, he₅.r11]
  -- What was written after the save.
  have fZ : Frame (wR w sp) s₂.mem s₆.mem := by
    rw [k₆.mem, m₅, m₄, k₃.mem]
    refine ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 16, 112⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
  have hgg : ∀ r ∈ [Reg.r7, .r8], s₆.gpr r = s₃.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;>
      rw [g₆ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide),
        g₄ _ (by decide)]
  have f₂' : Frame [savedR w] s.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  refine WP.of_runBlock ⟨s₆, run₆, s₂.mem, f₂', fun p hp => ?_, he₆, by rw [hgg _ (by simp), h8₃],
    by rw [hgg _ (by simp), h7₃], by rw [k₆.rd, rd₅, rd₄, k₃.rd, hrd₂], by rw [k₆.wr, wr₅, wr₄, k₃.wr, hwr₂], fZ,
    ?_, ?_, F⟩
  · have hp' : p.1 ≠ .r12 := by
      simp only [Impl.AesGcm.Arm.saved, List.mem_cons, List.not_mem_nil,
        or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [sv₂ p hp, u₁.other _ hp']
  · rw [k₆.mem, m₅, Proof.Cmac.zero4_bytes]
  · rw [k₆.mem, m₅, Proof.Cmac.zero4, bytesAt_frame (Proof.Cmac.frame_store4 _ _ _ _ _)
      (p := State.addr w + BitVec.ofNat 64 zOff)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inl (by decide)) (by decide) (by decide))
      (by decide), m₄, Proof.Cmac.zero4_bytes]

/-- The entry and S2V's first state: from the memory `mₛ` after the save,
`D = AES-CMAC(K1, <zero>)`, before the first component. -/
theorem start_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa (.seq (.block (encPre ++ startPre)) finFrame) s fun s' =>
      ∃ mₛ : Mem, Frame [savedR w] s.mem mₛ ∧ SavedAt mₛ w s ∧ AInv c w sp a R N mₛ s 0 s' := by
  have hR := h.rounds
  refine WP.seq (WP.mono (startBlock_ok L h) fun s₆ ⟨mₛ, St⟩ => ?_)
  have he₆ := St.env
  have eD := L.wA (d := dOff) (by decide)
  have eZ := L.wA (d := zOff) (by decide)
  refine WP.mono (fin_call St.args) fun s₇ h₇ => ?_
  have hb₆ := blw16_eq (s := s₆) he₆.sp
  have f₇ := h₇.frame
  rw [eD, L.wA (d := 256) (by decide), hb₆] at f₇
  have f₆₇ : Frame (wR w sp) s₆.mem s₇.mem := f₇.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨⟨State.addr w + BitVec.ofNat 64 176, 2400⟩, by simp, Offset.sub _ (by decide) (by decide)⟩
    · exact ⟨blw sp, by simp, fun _ h => h⟩
  have rd₇ : s₇.rd = s.rd := by rw [h₇.rd, St.rd]
  have wr₇ : s₇.wr = s.wr := by rw [h₇.wr, St.wr]
  refine ⟨mₛ, St.fs, St.sv, ⟨he₆.of_saved h₇.saved h₇.sp h₇.rd h₇.wr, ?_, ?_, ?_, rd₇, wr₇,
    St.frame.trans f₆₇, ?_⟩⟩
  · refine (h.ads.of_frame St.fs (fun r hr => ?_)).of_eq (by rw [rd₇]) (by rw [wr₇])
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.ads.dw.sub_right (Lay.wSub (by decide)))
  · rw [h₇.saved _ (by decide) (by decide), St.r8]; simp
  · rw [h₇.saved _ (by decide) (by decide), St.r7, Nat.sub_zero]
  · have hRb := rounds_le hR
    have dcw : ∀ r ∈ wR w sp, (⟨State.addr c, 512⟩ : Region).Disjoint r := dis_wR L.c_w L.stk_c
    have cK {d k : Nat} (hd : d + k ≤ 512) :
        bytesAt s₆.mem (State.addr c + BitVec.ofNat 64 d) k = bytesAt mₛ (State.addr c + BitVec.ofNat 64 d) k :=
      bytesAt_frame St.frame (fun r hr => (dcw r hr).sub_left (Lay.cSub hd)) (by omega)
    have sch := cK (d := 0) (k := 16 * (R + 1)) (by omega)
    rw [BitVec.add_zero] at sch
    have o₇ := h₇.out
    rw [eD, eZ, sch, cK (d := 240) (k := 16) (by decide), cK (d := 256) (k := 16) (by decide), St.zZ, St.zD] at o₇
    rw [o₇, List.take_zero, Spec.Siv.s2vAcc, List.foldl_nil, Spec.Siv.s2vStart, Spec.Siv.ctxMac,
      Spec.Siv.schedCiph, cmacWith_one _ _ _ _ (by rfl)]
    rfl

end

end VG.Proof.AesSiv.Arm
