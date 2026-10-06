import VerifiedGarbage.Proof.AesSiv.Arm.Start

/-!
# AES-SIV on ARMv7: `vg_aes_siv_encrypt`

Untrusted: everything here is checked by Lean. `encS2v` saves the
registers, sets S2V's first state (`start_ok`), absorbs the components of
associated data (`s2vAds_ok`) and loads the data's address and length
(`s2v_ok`); `encrypt` then finishes S2V with the plaintext into the IV at
`W` (`finish_ok`), encrypts the plaintext with CTR from it (`ctr_ok`), copies
the IV to `siv` (`sivOut_ok`) and restores the registers (`encrypt_wp`):
`encryptWith` of the context's PRF and cipher (`Spec.Siv.encryptWith_eq`).
`decrypt` copies the received IV from `siv` to `W` the same way
(`sivIn_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesSiv.Arm

open VG VG.Arm VG.Arm.RegUpd VG.Impl.AesSiv.Arm
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.Arm (blw)
open VG.Proof.AesGcm.Arm (bytesAt_frame SavedAt savedR restore_ok covers_left covers_prefix in_off sepW
  bytesAt_copy4 store4_eq mem_store add_ofNat_assoc add_ofNat_zero)
open VG.Proof.Cmac (store4)
open VG.Proof.MdStream.Arm (wp_ldrSp)

section
variable {c w sp : BitVec 32} {R : Nat} (L : Lay c w sp)
include L

/-- What `encS2v` leaves: `D` is S2V's state of the components, from the
memory `mₛ` after the save, and the data's address and length in `r6` and
`r5`. -/
structure S2vOut (c w sp a D : BitVec 32) (R N n : Nat) (s : State) (mₛ : Mem) (s' : State) : Prop where
  fs : Frame [savedR w] s.mem mₛ
  sv : SavedAt mₛ w s
  env : Env c w sp R s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  r6 : s'.gpr .r6 = D
  r5 : s'.gpr .r5 = BitVec.ofNat 32 n
  frame : Frame (wR w sp) mₛ s'.mem
  acc : bytesAt s'.mem (State.addr w + BitVec.ofNat 64 dOff) 16 =
    Spec.Siv.s2vAcc (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.components 32 s.mem (State.addr a) N)

theorem s2v_ok {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s) :
    WP isa encS2v s fun s' => ∃ mₛ, S2vOut c w sp a D R N n s mₛ s' := by
  have hR := h.rounds
  have hRb := rounds_le hR
  have hN : N < 2 ^ 32 := by have := h.ads.fit; omega
  have st := WP.seq_iff.mp (start_ok L h)
  refine WP.seq (WP.mono st fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono h₁ fun s₂ ⟨mₛ, fs, sv, I₀⟩ => ?_)
  refine WP.seq (WP.mono (s2vAds_ok L hR I₀ hN) fun s₃ I => ?_)
  -- The data's address and length.
  have dA : ∀ r ∈ savedR w :: wR w sp, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  have fT : Frame (savedR w :: wR w sp) s.mem s₃.mem :=
    (fs.mono (by simp)).trans (I.frame.mono fun r hr => List.mem_cons_of_mem _ hr)
  have v0 : s₃.mem.readW (State.addr sp + BitVec.ofNat 64 0) 32 = D := by
    rw [fT.readW (r := ⟨State.addr sp + BitVec.ofNat 64 0, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), BitVec.add_zero, h.a0]
  have v4 : s₃.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [fT.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  have hsp₃ : s₃.sp = sp := I.env.sp
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 0) (by decide)
    (by rw [hsp₃]; exact addr_add (by have := h.afit; omega))
    (by rw [I.rd, I.wr]; exact in_off h.args (by decide) (by decide)) fun s₄ u₄ => ?_
  refine wp_ldrSp (a := State.addr sp + BitVec.ofNat 64 4) (by decide)
    (by rw [u₄.sp, hsp₃]; exact addr_add (by have := h.afit; omega))
    (by rw [u₄.rd, u₄.wr, I.rd, I.wr]; exact in_off h.args (by decide) (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have dc : ∀ r ∈ [savedR w], (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact L.c0_w' (by decide) (by decide)
  refine ⟨mₛ, fs, sv, I.env.keep (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> rw [u₅.other _ (by decide), u₄.other _ (by decide)])
      (by rw [u₅.sp, u₄.sp]) (by rw [u₅.rd, u₄.rd]) (by rw [u₅.wr, u₄.wr]),
    by rw [u₅.rd, u₄.rd, I.rd], by rw [u₅.wr, u₄.wr, I.wr], by rw [u₅.other _ (by decide), u₄.gpr, v0],
    by rw [u₅.gpr, u₄.mem, v4], by rw [u₅.mem, u₄.mem]; exact I.frame, ?_⟩
  rw [u₅.mem, u₄.mem, I.acc, List.take_of_length_le (by rw [length_components]), ctxMac_frame fs dc hRb,
    components_frame fs (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact h.ads.dw.sub_right (Lay.wSub (by decide)))
      (fun i hi r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (h.ads.comp i hi).w.sub_right (Lay.wSub (by decide)))]

/-- `sivOut`: the IV at `W` copied to `T`, the stack argument at `[sp + 8]`. -/
theorem sivOut_ok {s : State} (he : Env c w sp R s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 = T)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa sivOut s = some s' ∧ bytesAt s'.mem (State.addr T) 16 = bytesAt s.mem (State.addr w) 16 ∧
      Frame [⟨State.addr T, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 2576 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₀ := he.perm.wR (show 0 + 4 ≤ 2576 by decide)
  have r₁ := he.perm.wR (show 4 + 4 ≤ 2576 by decide)
  have r₂ := he.perm.wR (show 8 + 4 ≤ 2576 by decide)
  have r₃ := he.perm.wR (show 12 + 4 ≤ 2576 by decide)
  have w₀ := in_off hTw (show 0 + 4 ≤ 16 by decide) (by decide)
  have w₁ := in_off hTw (show 4 + 4 ≤ 16 by decide) (by decide)
  have w₂ := in_off hTw (show 8 + 4 ≤ 16 by decide) (by decide)
  have w₃ := in_off hTw (show 12 + 4 ≤ 16 by decide) (by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr T + BitVec.ofNat 64 b) v).readW (State.addr w + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr w + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.symm.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa sivOut s = some s' ∧
      s'.mem = store4 s.mem (State.addr T + BitVec.ofNat 64 0) (s.mem.readW (State.addr w + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr w + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr w + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [sivOut]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Proof.Cmac.frame_store4 _ _ _ _ _, hg,
    hk.1, hk.2.1, hk.2.2⟩

/-- `sivIn`: the IV at `T`, the stack argument at `[sp + 8]`, copied to `W`. -/
theorem sivIn_ok {s : State} (he : Env c w sp R s) {T : BitVec 32}
    (hTi : InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 8)) 4)
    (hTv : s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 8)) 32 = T)
    (hTr : Covers [⟨State.addr T, 16⟩] (s.rd ++ s.wr)) (hTf : T.toNat + 16 ≤ 2 ^ 32)
    (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr w, 16⟩) :
    ∃ s', runBlock isa sivIn s = some s' ∧ bytesAt s'.mem (State.addr w) 16 = bytesAt s.mem (State.addr T) 16 ∧
      Frame [⟨State.addr w, 16⟩] s.mem s'.mem ∧ (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  have h11 := he.r11
  have eW : ∀ d, d < 2576 → State.addr (w + BitVec.ofNat 32 d) = State.addr w + BitVec.ofNat 64 d :=
    fun d hd => L.wA hd
  have eT : ∀ d, d < 16 → State.addr (T + BitVec.ofNat 32 d) = State.addr T + BitVec.ofNat 64 d :=
    fun d hd => addr_add (by omega)
  have r₀ := in_off hTr (show 0 + 4 ≤ 16 by decide) (by decide)
  have r₁ := in_off hTr (show 4 + 4 ≤ 16 by decide) (by decide)
  have r₂ := in_off hTr (show 8 + 4 ≤ 16 by decide) (by decide)
  have r₃ := in_off hTr (show 12 + 4 ≤ 16 by decide) (by decide)
  have w₀ := he.perm.wW (show 0 + 4 ≤ 2576 by decide)
  have w₁ := he.perm.wW (show 4 + 4 ≤ 2576 by decide)
  have w₂ := he.perm.wW (show 8 + 4 ≤ 2576 by decide)
  have w₃ := he.perm.wW (show 12 + 4 ≤ 2576 by decide)
  have q : ∀ (m : Mem) (a b : Nat) (v : BitVec 32), a + 4 ≤ 16 → b + 4 ≤ 16 →
      (m.writeW (State.addr w + BitVec.ofNat 64 b) v).readW (State.addr T + BitVec.ofNat 64 a) 32 =
        m.readW (State.addr T + BitVec.ofNat 64 a) 32 := fun m a b v ha hb =>
    sepW (m := m) ((hTd.sub_left (Offset.sub_base _ ha)).sub_right (Offset.sub_base _ hb))
  have p₁ := fun m v => q m 4 0 v (by decide) (by decide)
  have p₂ := fun m v => q m 8 0 v (by decide) (by decide)
  have p₃ := fun m v => q m 8 4 v (by decide) (by decide)
  have p₄ := fun m v => q m 12 0 v (by decide) (by decide)
  have p₅ := fun m v => q m 12 4 v (by decide) (by decide)
  have p₆ := fun m v => q m 12 8 v (by decide) (by decide)
  obtain ⟨s', run, hm, hg, hk⟩ : ∃ s', runBlock isa sivIn s = some s' ∧
      s'.mem = store4 s.mem (State.addr w + BitVec.ofNat 64 0) (s.mem.readW (State.addr T + BitVec.ofNat 64 0) 32)
        (s.mem.readW (State.addr T + BitVec.ofNat 64 4) 32) (s.mem.readW (State.addr T + BitVec.ofNat 64 8) 32)
        (s.mem.readW (State.addr T + BitVec.ofNat 64 12) 32) ∧
      (∀ r, r ≠ .r0 → r ≠ .r1 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
    refine ⟨_, by simp only [sivIn]; arun [hTi, hTv, h11, eW, eT, r₀, r₁, r₂, r₃, w₀, w₁, w₂, w₃, p₁, p₂, p₃, p₄,
      p₅, p₆], ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_store, store4_eq, add_ofNat_assoc]
    · intro r a b; simp [gpr_setReg, a, b]
    · exact ⟨rfl, rfl, rfl⟩
  simp only [add_ofNat_zero] at hm
  refine ⟨s', run, by rw [hm]; exact bytesAt_copy4 _ _ _, by rw [hm]; exact Proof.Cmac.frame_store4 _ _ _ _ _, hg,
    hk.1, hk.2.1, hk.2.2⟩

/-- `vg_aes_siv_encrypt`: the synthetic IV at `T` and the ciphertext in place. -/
theorem encrypt_wp {a D T : BitVec 32} {N n : Nat} {s : State} (h : EPre c w sp a D T R N n s)
    (hTw : Covers [⟨State.addr T, 16⟩] s.wr) (hTd : (⟨State.addr T, 16⟩ : Region).Disjoint ⟨State.addr D, n⟩) :
    WP isa encrypt s fun s' => abiPreserved s s' ∧
      Spec.Siv.encryptWith (Spec.Siv.ctxMac s.mem (State.addr c) R) (Spec.Siv.ctxCiph s.mem (State.addr c) R)
          (Spec.Siv.components 32 s.mem (State.addr a) N) (bytesAt s.mem (State.addr D) n) =
        (bytesAt s'.mem (State.addr T) 16, bytesAt s'.mem (State.addr D) n) := by
  have hR := h.rounds
  have hRb := rounds_le hR
  have ww := L.ww
  refine WP.seq (WP.mono (s2v_ok L h) fun s₁ ⟨mₛ, O⟩ => ?_)
  have hD₁ : Dat c w sp s₁ D n := h.data.of_eq O.rd O.wr
  refine WP.seq (WP.mono (finish_ok L O.env hR hD₁.buf h.n32 O.r6 O.r5 (out := 0) (.inl rfl))
    fun s₂ ⟨he₂, rd₂, wr₂, g₂, f₂, o₂⟩ => ?_)
  -- The memory before CTR.
  have f₀₁ : Frame (savedR w :: oR w sp 0) s.mem s₁.mem :=
    (O.fs.mono (by simp)).trans ((frame_oR 0 O.frame).mono fun r hr => List.mem_cons_of_mem _ hr)
  have f₀₂ : Frame (savedR w :: oR w sp 0) s.mem s₂.mem :=
    (O.fs.mono (by simp)).trans (((frame_oR 0 O.frame).trans f₂).mono fun r hr => List.mem_cons_of_mem _ hr)
  have dA : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
  have dD : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr D, n⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.w.sub_right (Lay.wSub (by decide))
    · exact h.data.buf.stk.symm
  have dc : ∀ r ∈ savedR w :: oR w sp 0, (⟨State.addr c, 512⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.c0_w' (by decide) (by decide)
    · exact L.stk_c.symm
  have hm0 : s₂.mem.readW (State.addr sp) 32 = D := by
    rw [f₀₂.readW (r := ⟨State.addr sp, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Region.sub_prefix (by decide))) (by decide), h.a0]
  have hm1 : s₂.mem.readW (State.addr sp + BitVec.ofNat 64 4) 32 = BitVec.ofNat 32 n := by
    rw [f₀₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 4, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a1]
  have hD₂ : Dat c w sp s₂ D n := hD₁.of_eq rd₂ wr₂
  refine WP.seq (WP.mono (ctr_ok L he₂ hR hD₂ h.n32 h.afit (by rw [rd₂, wr₂, O.rd, O.wr]; exact h.args) h.args_w
    hm0 hm1) fun s₃ ⟨he₃, rd₃, wr₃, g₃, h6₃, h5₃, f₃, d₃⟩ => ?_)
  -- The saved registers are where the save put them.
  have dS : ∀ r ∈ ctrR w sp D n, (savedR w).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w' (by decide)).symm
    · exact (h.data.buf.w.sub_right (Lay.wSub (by decide))).symm
  have sv₃ : SavedAt s₃.mem w s := (O.sv.frame ((frame_oR 0 O.frame).trans f₂) fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact saved_wR L r hr).frame f₃ dS
  -- The IV copied to `siv`.
  have eA : ∀ r ∈ ctrR w sp D n, (⟨State.addr sp, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact h.args_w.sub_right (Lay.wSub (by decide))
    · exact Offset.base_disjoint_below (State.addr sp) (n := 16) (k := 16) (by decide)
    · exact h.args_d
  have a8 : State.addr (s₃.sp + BitVec.ofNat 32 8) = State.addr sp + BitVec.ofNat 64 8 := by
    rw [he₃.sp]; exact addr_add (by have := h.afit; omega)
  have v8 : s₃.mem.readW (State.addr (s₃.sp + BitVec.ofNat 32 8)) 32 = T := by
    rw [a8, f₃.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (eA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide),
      f₀₂.readW (r := ⟨State.addr sp + BitVec.ofNat 64 8, 4⟩) (Region.contains_self _ _)
      (fun r hr => (dA r hr).sub_left (Offset.sub_base _ (by decide))) (by decide), h.a2]
  have i8 : InRegions (s₃.rd ++ s₃.wr) (State.addr (s₃.sp + BitVec.ofNat 32 8)) 4 := by
    rw [a8, rd₃, wr₃, rd₂, wr₂, O.rd, O.wr]
    exact in_off h.args (by decide) (by decide)
  obtain ⟨s₄, run₄, iv₄, fo₄, g₄, rd₄, wr₄, sp₄⟩ := sivOut_ok L he₃ i8 v8
    (by rw [wr₃, wr₂, O.wr]; exact hTw) h.tfit (h.t_w.sub_right (Region.sub_prefix (by decide)))
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  have he₄ : Env c w sp R s₄ := he₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₄ _ (by decide) (by decide)) sp₄ rd₄ wr₄
  have sv₄ : SavedAt s₄.mem w s := sv₃.frame fo₄ fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact (h.t_w.sub_right (Lay.wSub (by decide))).symm
  refine WP.mono (restore_ok (s₀ := s) he₄.r11 (by omega)
    (by rw [rd₄, wr₄, rd₃, wr₃, rd₂, wr₂, O.rd, O.wr]; exact covers_left (covers_prefix h.perm.w (by decide)))
    sv₄ (by rw [he₄.sp, h.hsp])) fun s₅ ⟨ab, m₅, _, _, _⟩ => ⟨ab, ?_⟩
  have pD : bytesAt s₄.mem (State.addr D) n = bytesAt s₃.mem (State.addr D) n :=
    bytesAt_frame fo₄ (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hTd.symm)
      (by have := h.data.buf.lt; omega)
  -- The values.
  have dW : ∀ r ∈ ctrR w sp D n, (⟨State.addr w, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · simpa using L.w_w (a := 0) (n := 16) (.inl (by decide)) (by decide) (by decide)
    · exact (L.stk_w.sub_right (Region.sub_prefix (by decide))).symm
    · exact (h.data.buf.w.sub_right (Region.sub_prefix (by decide))).symm
  have iv : bytesAt s₃.mem (State.addr w) 16 = bytesAt s₂.mem (State.addr w) 16 :=
    bytesAt_frame f₃ dW (by decide)
  have mac₁ : Spec.Siv.ctxMac s₁.mem (State.addr c) R = Spec.Siv.ctxMac s.mem (State.addr c) R :=
    ctxMac_frame f₀₁ dc hRb
  have ciph₂ : Spec.Siv.ctxCiph s₂.mem (State.addr c) R = Spec.Siv.ctxCiph s.mem (State.addr c) R :=
    ctxCiph_frame f₀₂ dc hRb
  have p₁ : bytesAt s₁.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₁ dD
      (by have := h.data.buf.lt; omega)
  have p₂ : bytesAt s₂.mem (State.addr D) n = bytesAt s.mem (State.addr D) n :=
    bytesAt_frame f₀₂ dD (by have := h.data.buf.lt; omega)
  rw [BitVec.add_zero] at o₂
  rw [m₅, iv₄, pD, Spec.Siv.encryptWith_eq, Spec.Siv.sealWith, d₃, iv, o₂, mac₁, O.acc, p₁, ciph₂, p₂]

end

end VG.Proof.AesSiv.Arm
