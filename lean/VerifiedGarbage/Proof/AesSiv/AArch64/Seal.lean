import VerifiedGarbage.Proof.AesSiv.AArch64.Ctr
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-SIV on AArch64: the counter, and the end of `vg_aes_siv_encrypt`

`encrypt` and `decrypt` set the counter `Q` at `W + 64` from an IV at `W`
(`counter_ok`): the IV's second word with bits 7 and 39 cleared
(`counter_words`). From S2V's state of the associated data on, `encrypt`
finishes S2V with the plaintext into the first 16 bytes of the working space
(`finish_wp`), sets the counter from that IV, encrypts the data in place with
CTR (`ctr_wp`) and restores the registers: the working space then starts
with the IV and the data is the ciphertext (`sealTail_wp`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Proof.AesSiv (qmask counter_words)
open VG.Proof.CmacAes.AArch64 (k0 le8_rev)
open VG.Proof.Gcm.AArch64 (rev64_rev64)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

theorem counter_ok (h : Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa (counter 0) s = some s' ∧
      s'.mem = (s.mem.writeW (W + BitVec.ofNat 64 cntOff) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (W + BitVec.ofNat 64 (cntOff + 8)) (s.mem.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  have r₈ := h.inRW hrd hwr (d := 0 + 8) (n := 8) (by decide)
  have w₀ := h.inW hwr (d := cntOff) (n := 8) (by decide)
  have w₈ := h.inW hwr (d := cntOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, counter, cntOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
      Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀, r₈, w₀, w₈]
    rfl, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], by rfl, by rfl, by rfl⟩
  have hq : ~~~((BitVec.setWidth 64 (128 : BitVec 16) <<< (16 * 0) &&& ~~~((65535 : BitVec 64) <<< (16 * 2)) |||
      BitVec.setWidth 64 (128 : BitVec 16) <<< (16 * 2)).rotateRight 0) = qmask := by decide
  rw [Mem.read_write_sep (Offset.sep W (d := 0 + 8) (n := 8) (e := cntOff) (k := 8) (by decide) (by decide)
    (by decide)) (by decide), hq]
  simp only [Mem.writeW, Mem.readW, BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

/-- The counter `Q` of the IV, as `ctr` takes it. -/
theorem counter_cnt (m : Mem) (W : Addr) :
    ∃ hi lo : BitVec 64,
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      ((m.writeW (W + BitVec.ofNat 64 cntOff) (m.readW (W + BitVec.ofNat 64 0) 64)).writeW
          (W + BitVec.ofNat 64 (cntOff + 8)) (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask)).readW
          (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt m W 16)) := by
  refine ⟨rev64 (m.readW (W + BitVec.ofNat 64 0) 64), rev64 (m.readW (W + BitVec.ofNat 64 (0 + 8)) 64 &&& qmask),
    ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (Offset.sep W (d := cntOff) (n := 8) (e := cntOff + 8) (k := 8) (by decide) (by decide)
      (by decide)) (by decide), Mem.readW_writeW_self64, rev64_rev64]
  · rw [Mem.readW_writeW_self64, rev64_rev64]
  · rw [← Proof.Cmac.ofBytes_toBytes (rev64 _ ++ rev64 _), ← le8_rev, rev64_rev64, rev64_rev64, counter_words,
      Proof.Cmac.le8_readW, Proof.Cmac.le8_readW, k0, ← Proof.Cmac.bytesAt_split]

/-! ## What each step writes -/

/-- The regions the counter's two words are written to. -/
abbrev cntRegions (W : Addr) : List Region :=
  [⟨W + BitVec.ofNat 64 cntOff, 8⟩, ⟨W + BitVec.ofNat 64 (cntOff + 8), 8⟩]

theorem counter_frame (m : Mem) (W : Addr) (a b : BitVec 64) :
    Frame (cntRegions W) m ((m.writeW (W + BitVec.ofNat 64 cntOff) a).writeW (W + BitVec.ofNat 64 (cntOff + 8)) b) :=
  ((Frame.refl _ _).writeW List.mem_cons_self a (Region.contains_self (W + BitVec.ofNat 64 cntOff) 8)).writeW
    (List.mem_cons_of_mem _ List.mem_cons_self) b (Region.contains_self (W + BitVec.ofNat 64 (cntOff + 8)) 8)

/-- A range of the working space outside what `finish` writes. -/
theorem fin_dis (_h : Env s₀ C D P W R L) {out d n : Nat} (hout : out + 16 ≤ 256) (_hd : d + n ≤ 2560)
    (h1 : out + 16 ≤ d ∨ d + n ≤ out) (h2 : d + n ≤ 32 ∨ 64 ≤ d) (h3 : d + n ≤ 144 ∨ 160 ≤ d)
    (h5 : d + n ≤ 256) :
    ∀ r ∈ finRegions W out, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the working space, outside what `finish` writes. -/
theorem fin_out {X : Region} {out : Nat} (hout : out + 16 ≤ 256) (hw : X.Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ finRegions W out, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by omega))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

/-- A range of the working space outside what CTR writes. -/
theorem ctr_dis (h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 256) (h1 : d + n ≤ 64 ∨ 112 ≤ d) :
    ∀ r ∈ ctrRegions W P L, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega))
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the data and the working space, outside what CTR writes. -/
theorem ctr_out {X : Region} (hp : X.Disjoint ⟨P, L⟩) (hw : X.Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ ctrRegions W P L, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

/-- A range of the working space outside the counter. -/
theorem cnt_dis {d n : Nat} (hd : d + n ≤ 2560) (h1 : d + n ≤ 64 ∨ 80 ≤ d) :
    ∀ r ∈ cntRegions W, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [cntOff, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Offset.disjoint W (by omega) (by omega) (by omega)
  · exact Offset.disjoint W (by omega) (by omega) (by omega)

/-- A region outside the working space, outside the counter. -/
theorem cnt_out {X : Region} (hw : X.Disjoint ⟨W, 2560⟩) : ∀ r ∈ cntRegions W, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

theorem one_out {X Y : Region} (hw : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact hw

/-- What `encrypt`'s and `decrypt`'s ends write: the data and the working space. -/
abbrev endRegions (W P : Addr) (L : Nat) : List Region := [⟨P, L⟩, ⟨W, 2560⟩]

theorem fin_sub (h : Env s₀ C D P W R L) {out : Nat} (hout : out + 16 ≤ 256) :
    ∀ r ∈ finRegions W out, ∃ r' ∈ endRegions W P L, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by omega)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

theorem cnt_sub (h : Env s₀ C D P W R L) : ∀ r ∈ cntRegions W, ∃ r' ∈ endRegions W P L, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

theorem ctr_sub (h : Env s₀ C D P W R L) : ∀ r ∈ ctrRegions W P L, ∃ r' ∈ endRegions W P L, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by decide)⟩

/-! ## From S2V's end to the restore -/

/-- The registers, and the data and its length in `x26` and `x27`. -/
structure SPre (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop where
  regs : Regs s₀ C D P W R L s
  x26 : s.gpr .x26 = P
  x27 : s.gpr .x27 = BitVec.ofNat 64 L

theorem saved_fits : Spill.Fits saved := by decide

theorem saved_bound : ∀ p ∈ saved, 160 ≤ p.2 ∧ p.2 + 8 ≤ 248 := by decide

theorem restored_sub : ∀ p ∈ restored, p ∈ saved := by decide

theorem restored_restorable : Spill.Restorable .x19 restored := by decide

theorem restored_all : ∀ r ∈ preserved, r ∈ restored.map Prod.fst := by decide

/-- The restore, from the slots the save wrote (`Saved`), with the working
space in `x19`. -/
theorem restore_wp (h : Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) :
    WP isa (.block restore) s fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧
      (∀ r, r ∉ restored.map Prod.fst → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem :=
  WP.mono (Spill.restore_wp h19 (fun p hp => saved_fits.1 p (restored_sub p hp)) restored_restorable
      (fun p hp => by have := saved_bound p (restored_sub p hp); exact h.inRW hrd hwr (by omega))
      (fun p hp => hsv p (restored_sub p hp)))
    fun _ h₇ => ⟨fun r hr => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (restored_all r hr); exact h₇.gpr p hp, h₇.other, h₇.sp, h₇.mem⟩

theorem sealTail_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State}
    (hs : SPre s₀ C D P W R L s) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) :
    WP isa (.seq (finish v.callee v.ctr.callee v.ctr.suffix 0)
        (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.block restore)))) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧ s'.sp = s₀.sp ∧
        Frame (endRegions W P L) s.mem s'.mem ∧
        Spec.Siv.sealWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
          (Spec.Aes.bytesAt s.mem P L) = (Spec.Aes.bytesAt s'.mem W 16, Spec.Aes.bytesAt s'.mem P L) := by
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have hL : L ≤ 2 ^ 64 := by have := h.lt; omega
  refine WP.seq (WP.mono (finish_wp v h hs.regs (Or.inl rfl)) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := counter_ok h h₂.regs.x19 h₂.regs.rd h₂.regs.wr
  have f₃ : Frame (cntRegions W) s₂.mem s₃.mem := m₃ ▸ counter_frame _ _ _ _
  have hr₃ : Regs s₀ C D P W R L s₃ := h₂.regs.keep' (fun r hr => g₃ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₃ rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  have hcnt : ∃ hi lo : BitVec 64, s₃.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s₃.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₂.mem W 16)) := by
    rw [m₃]; exact counter_cnt s₂.mem W
  refine WP.seq (WP.mono (ctr_wp v.ctr h hcp hPw hr₃ hcnt (by rw [g₃ _ (by decide) (by decide), h₂.hold.1, hs.x26])
    (by rw [g₃ _ (by decide) (by decide), h₂.hold.2, hs.x27])) fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hsv₄ : Spill.Saved W g saved s₄.mem := by
    have hb := saved_bound
    refine (((hsv.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp; exact cnt_dis (by omega) (by omega)
    · have := hb p hp; exact ctr_dis h (by omega) (by omega)
  refine WP.mono (restore_wp h h₄.regs.x19 h₄.regs.rd h₄.regs.wr hsv₄) fun s₅ ⟨h₅a, _, sp₅, m₅⟩ => ?_
  have c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
  have d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
  rw [k0] at c₀ d₀
  -- The IV: S2V's end.
  have hv : Spec.Aes.bytesAt s₅.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    rw [m₅, Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide), o₂]
  -- The ciphertext: CTR of the data from the IV's counter.
  have hc : Spec.Aes.bytesAt s₅.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₅.mem W 16))
        (Spec.Aes.bytesAt s.mem P L) := by
    rw [m₅, h₄.data, Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide),
      ctxCiph_frame f₃ (cnt_out h.c_w) hRb, ctxCiph_frame f₂ (fin_out (by decide) h.c_w) hRb,
      Proof.Cmac.bytesAt_frame f₃ (cnt_out h.p_w) hL, Proof.Cmac.bytesAt_frame f₂ (fin_out (by decide) h.p_w) hL]
  refine ⟨h₅a, by rw [sp₅, h₄.regs.sp], ?_, by rw [hc, hv]; rfl⟩
  rw [m₅]
  exact ((f₂.sub (fin_sub h (by decide))).trans (f₃.sub (cnt_sub h))).trans (f₄.sub (ctr_sub h))

end VG.Proof.AesSiv.AArch64
