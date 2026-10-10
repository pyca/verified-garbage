import VerifiedGarbage.Proof.AesSiv.AArch64.Ctr
import VerifiedGarbage.Proof.Cmac.Dbl32

/-!
# AES-SIV on AArch64: the counter, and the end of `vg_aes_siv_encrypt`

`encrypt` and `decrypt` set the counter `Q` at `W + 64` from an IV at `W`
(`counter_ok`): the IV's second word with bits 7 and 39 cleared
(`counter_words`). From S2V's state of the associated data on, `encrypt`
finishes S2V with the plaintext into the first 16 bytes of the working space
(`finish_wp`), sets the counter from that IV, encrypts the data in place with
CTR (`ctr_wp`), copies the IV to `siv`, whose address the save left at
`W + 248` (`sivOut_ok`), and restores the registers: `siv` then holds the IV
and the data is the ciphertext (`sealTail_wp`).
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

theorem saved_bound : ∀ p ∈ saved, 160 ≤ p.2 ∧ p.2 + 8 ≤ 256 := by decide

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

/-- The copy of the IV at `W` to `T`, whose address is at `W + 248`. -/
theorem sivOut_ok {s : State} {W T : Addr} (h19 : s.gpr .x19 = W)
    (aT : s.mem.readW (W + BitVec.ofNat 64 248) 64 = T)
    (r₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 248) 8)
    (r₀ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 0) 8) (r₈ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 8) 8)
    (w₀ : InRegions s.wr (T + BitVec.ofNat 64 0) 8) (w₈ : InRegions s.wr (T + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa sivOut s = some s' ∧
      s'.mem = (s.mem.writeW (T + BitVec.ofNat 64 0) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).writeW
        (T + BitVec.ofNat 64 8)
        ((s.mem.writeW (T + BitVec.ofNat 64 0) (s.mem.readW (W + BitVec.ofNat 64 0) 64)).readW
          (W + BitVec.ofNat 64 8) 64) ∧
      (∀ r, r ≠ .x9 → r ≠ .x10 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [Mem.readW, BitVec.setWidth_eq] at aT
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, and_self,
      sivOut, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      h19, r₂, aT, r₀, r₈, w₀, w₈]
    rfl, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], by rfl, by rfl, by rfl⟩
  simp only [Mem.writeW, Mem.readW, BitVec.setWidth_eq, Nat.reduceDiv, Nat.reduceMul]

/-- Disjoint ranges are separate. -/
theorem sep_of_disjoint {a b : Addr} {n k n' k' : Nat} (h : (⟨a, n'⟩ : Region).Disjoint ⟨b, k'⟩)
    (hn : n ≤ n') (hk : k ≤ k') : Mem.Sep a n b k :=
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega) (by simp only [Region.Contains]; omega)

theorem sealTail_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State}
    (hs : SPre s₀ C D P W R L s) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) {T : Addr}
    (hgT : g .x6 = T) (hTw : (⟨T, 16⟩ : Region) ∈ s₀.wr) (tW : (⟨T, 16⟩ : Region).Disjoint ⟨W, 2560⟩)
    (tP : (⟨T, 16⟩ : Region).Disjoint ⟨P, L⟩) (wT : T.toNat + 16 ≤ 2 ^ 64) :
    WP isa (.seq (finish v.callee v.ctr.callee v.ctr.suffix 0)
        (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (.block sivOut) (.block restore))))) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧ s'.sp = s₀.sp ∧
        Frame (⟨T, 16⟩ :: endRegions W P L) s.mem s'.mem ∧
        Spec.Siv.sealWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
          (Spec.Aes.bytesAt s.mem P L) = (Spec.Aes.bytesAt s'.mem T 16, Spec.Aes.bytesAt s'.mem P L) := by
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
  refine WP.seq (WP.mono (ctr_wp v.ctr h hcp hPw hr₃ (length_counter _) (counter_low _) hcnt (by rw [g₃ _ (by decide) (by decide), h₂.hold.1, hs.x26])
    (by rw [g₃ _ (by decide) (by decide), h₂.hold.2, hs.x27])) fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hb := saved_bound
  have hsv₄ : Spill.Saved W g saved s₄.mem := by
    refine (((hsv.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    · have := hb p hp; exact cnt_dis (by omega) (by omega)
    · have := hb p hp; exact ctr_dis h (by omega) (by omega)
  -- The copy of the IV to `T`.
  have a₂ : s₄.mem.readW (W + BitVec.ofNat 64 248) 64 = T := by
    rw [hsv₄ (.x6, 248) (by decide), hgT]
  have inT (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₄.wr (T + BitVec.ofNat 64 d) 8 := by
    rw [h₄.regs.wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := wT; omega)⟩
  obtain ⟨s₅, run₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := sivOut_ok h₄.regs.x19 a₂
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 248) (n := 8) (by decide))
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 0) (n := 8) (by decide))
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 8) (n := 8) (by decide)) (inT 0 (by decide)) (inT 8 (by decide))
  have fT : Frame [⟨T, 16⟩] s₄.mem s₅.mem := by rw [m₅, k0]; exact Proof.Cmac.frame_store2 _ _ _
  have hsv₅ : Spill.Saved W g saved s₅.mem := hsv₄.frame fT fun p hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := hb p hp
    exact (tW.sub_right (h.sW (d := p.2) (n := 8) (by omega))).symm
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.mono (restore_wp h (by rw [g₅ _ (by decide) (by decide), h₄.regs.x19]) (by rw [rd₅, h₄.regs.rd])
    (by rw [wr₅, h₄.regs.wr]) hsv₅) fun s₆ ⟨h₆a, _, sp₆, m₆⟩ => ?_
  have c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
  have d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
  rw [k0] at c₀ d₀
  -- The IV: S2V's end.
  have hv : Spec.Aes.bytesAt s₄.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    rw [Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide), o₂]
  -- The ciphertext: CTR of the data from the IV's counter.
  have hc : Spec.Aes.bytesAt s₄.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₄.mem W 16))
        (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₄.data, Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide),
      ctxCiph_frame f₃ (cnt_out h.c_w) hRb, ctxCiph_frame f₂ (fin_out (by decide) h.c_w) hRb,
      Proof.Cmac.bytesAt_frame f₃ (cnt_out h.p_w) hL, Proof.Cmac.bytesAt_frame f₂ (fin_out (by decide) h.p_w) hL]
  -- The copy.
  have hT : Spec.Aes.bytesAt s₆.mem T 16 = Spec.Aes.bytesAt s₄.mem W 16 := by
    have sp8 : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
      sep_of_disjoint (tW.sub_right (h.sW (d := 8) (n := 8) (by decide))).symm (by decide) (by decide)
    rw [m₆, m₅, k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  have hP : Spec.Aes.bytesAt s₆.mem P L = Spec.Aes.bytesAt s₄.mem P L := by
    rw [m₆]
    exact Proof.Cmac.bytesAt_frame fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact tP.symm) hL
  refine ⟨h₆a, by rw [sp₆, sp₅, h₄.regs.sp], ?_, by rw [hT, hP, hc, hv]; rfl⟩
  rw [m₆]
  refine (((f₂.sub (fin_sub h (by decide))).trans (f₃.sub (cnt_sub h))).trans (f₄.sub (ctr_sub h))).mono
    (fun r hr => List.mem_cons_of_mem _ hr) |>.trans (fT.mono fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self

end VG.Proof.AesSiv.AArch64
