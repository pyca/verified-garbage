module

import VerifiedGarbage.Proof.AesSiv.Mask
public import VerifiedGarbage.Proof.AesSiv.AArch64.Finish
import VerifiedGarbage.Proof.AesSiv.Ctr32
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.AesSiv.AArch64.FinishLong
public import VerifiedGarbage.Proof.AesSiv.Words
import VerifiedGarbage.Proof.Cmac.Dbl32

/-! ### `AesSiv.AArch64.Seal`, which this module and modules that import it used -/

section

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

@[expose] public section

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
  obtain r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  obtain r₈ := h.inRW hrd hwr (d := 0 + 8) (n := 8) (by decide)
  obtain w₀ := h.inW hwr (d := cntOff) (n := 8) (by decide)
  obtain w₈ := h.inW hwr (d := cntOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, counter, cntOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      addr, State.load, State.store, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write, wr_write,
      Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀, r₈, w₀, w₈]
    rfl, ?_, fun r h₁ h₂ => by simp [gpr_write, h₁, h₂], by rfl, by rfl, by rfl⟩
  obtain hq : ~~~((BitVec.setWidth 64 (128 : BitVec 16) <<< (16 * 0) &&& ~~~((65535 : BitVec 64) <<< (16 * 2)) |||
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
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [_hd]) (by omega_using [hout])
  · exact Offset.disjoint W (by omega_using [h2]) (by omega_using [_hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h3]) (by omega_using [_hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h5]) (by omega_using [_hd]) (by omega_using [])

/-- A region outside the working space, outside what `finish` writes. -/
theorem fin_out {X : Region} {out : Nat} (hout : out + 16 ≤ 256) (hw : X.Disjoint ⟨W, 2560⟩) :
    ∀ r ∈ finRegions W out, X.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hw.sub_right (Offset.sub_base W (by omega_using [hout]))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))
  · exact hw.sub_right (Offset.sub_base W (by decide))

/-- A range of the working space outside what CTR writes. -/
theorem ctr_dis (h : Env s₀ C D P W R L) {d n : Nat} (hd : d + n ≤ 256) (h1 : d + n ≤ 64 ∨ 112 ≤ d) :
    ∀ r ∈ ctrRegions W P L, Region.Disjoint ⟨W + BitVec.ofNat 64 d, n⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.p_w.symm.sub_left (h.sW (by omega_using [hd]))
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [hd]) (by omega_using [hd]) (by omega_using [])

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
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])
  · exact Offset.disjoint W (by omega_using [h1]) (by omega_using [hd]) (by omega_using [])

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
  · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, h.sW (by omega_using [hout])⟩
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
      (fun p hp => by have := saved_bound p (restored_sub p hp); exact h.inRW hrd hwr (by omega_using [this]))
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
  fun x h₁ h₂ => h x (by simp only [Region.Contains]; omega_using [hn, h₁]) (by simp only [Region.Contains]; omega_using [hk, h₂])

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
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_using [h]
  obtain hL : L ≤ 2 ^ 64 := by have := h.lt; omega_using [this]
  refine WP.seq (WP.mono (finish_wp v h hs.regs (Or.inl rfl)) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := counter_ok h h₂.regs.x19 h₂.regs.rd h₂.regs.wr
  obtain f₃ : Frame (cntRegions W) s₂.mem s₃.mem := m₃ ▸ counter_frame _ _ _ _
  obtain hr₃ : Regs s₀ C D P W R L s₃ := h₂.regs.keep' (fun r hr => g₃ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₃ rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  obtain hcnt : ∃ hi lo : BitVec 64, s₃.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s₃.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s₂.mem W 16)) := by
    rw [m₃]; exact counter_cnt s₂.mem W
  refine WP.seq (WP.mono (ctr_wp v.ctr h hcp hPw hr₃ (length_counter _) (counter_low _) hcnt (by rw [g₃ _ (by decide) (by decide), h₂.hold.1, hs.x26])
    (by rw [g₃ _ (by decide) (by decide), h₂.hold.2, hs.x27])) fun s₄ h₄ => ?_)
  have f₄ := h₄.frame
  -- The saved registers.
  have hb := saved_bound
  obtain hsv₄ : Spill.Saved W g saved s₄.mem := by
    refine (((hsv.frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame f₄ fun p hp => ?_)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this]) (by omega_using [this])
    · have := hb p hp; exact cnt_dis (by omega_using [this]) (by omega_using [this])
    · have := hb p hp; exact ctr_dis h (by omega_using [this]) (by omega_using [this])
  -- The copy of the IV to `T`.
  obtain a₂ : s₄.mem.readW (W + BitVec.ofNat 64 248) 64 = T := by
    rw [hsv₄ (.x6, 248) (by decide), hgT]
  have inT (d : Nat) (hd : d + 8 ≤ 16) : InRegions s₄.wr (T + BitVec.ofNat 64 d) 8 := by
    rw [h₄.regs.wr]; exact ⟨_, hTw, Offset.contains_base T hd (by have := wT; omega_using [hd])⟩
  obtain ⟨s₅, run₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := sivOut_ok h₄.regs.x19 a₂
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 248) (n := 8) (by decide))
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 0) (n := 8) (by decide))
    (h.inRW h₄.regs.rd h₄.regs.wr (d := 8) (n := 8) (by decide)) (inT 0 (by decide)) (inT 8 (by decide))
  obtain fT : Frame [⟨T, 16⟩] s₄.mem s₅.mem := by rw [m₅, k0]; exact Proof.Cmac.frame_store2 _ _ _
  obtain hsv₅ : Spill.Saved W g saved s₅.mem := hsv₄.frame fT fun p hp r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    have := hb p hp
    exact (tW.sub_right (h.sW (d := p.2) (n := 8) (by omega_using [this]))).symm
  refine WP.seq (WP.of_runBlock ⟨s₅, run₅, ?_⟩)
  refine WP.mono (restore_wp h (by rw [g₅ _ (by decide) (by decide), h₄.regs.x19]) (by rw [rd₅, h₄.regs.rd])
    (by rw [wr₅, h₄.regs.wr]) hsv₅) fun s₆ ⟨h₆a, _, sp₆, m₆⟩ => ?_
  obtain c₀ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
  obtain d₀ := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
  rw [k0] at c₀ d₀
  -- The IV: S2V's end.
  obtain hv : Spec.Aes.bytesAt s₄.mem W 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L) := by
    have o₂ := h₂.out
    rw [k0] at o₂
    rw [Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide), o₂]
  -- The ciphertext: CTR of the data from the IV's counter.
  obtain hc : Spec.Aes.bytesAt s₄.mem P L =
      Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s₄.mem W 16))
        (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₄.data, Proof.Cmac.bytesAt_frame f₄ c₀ (by decide), Proof.Cmac.bytesAt_frame f₃ d₀ (by decide),
      ctxCiph_frame f₃ (cnt_out h.c_w) hRb, ctxCiph_frame f₂ (fin_out (by decide) h.c_w) hRb,
      Proof.Cmac.bytesAt_frame f₃ (cnt_out h.p_w) hL, Proof.Cmac.bytesAt_frame f₂ (fin_out (by decide) h.p_w) hL]
  -- The copy.
  obtain hT : Spec.Aes.bytesAt s₆.mem T 16 = Spec.Aes.bytesAt s₄.mem W 16 := by
    obtain sp8 : Mem.Sep (W + BitVec.ofNat 64 8) (64 / 8) T (64 / 8) :=
      sep_of_disjoint (tW.sub_right (h.sW (d := 8) (n := 8) (by decide))).symm (by decide) (by decide)
    rw [m₆, m₅, k0, k0, Mem.readW_writeW_sep sp8 (by decide), Proof.Cmac.bytesAt_store2, Proof.Cmac.le8_readW,
      Proof.Cmac.le8_readW, ← Proof.Cmac.bytesAt_split]
  obtain hP : Spec.Aes.bytesAt s₆.mem P L = Spec.Aes.bytesAt s₄.mem P L := by
    rw [m₆]
    exact Proof.Cmac.bytesAt_frame fT (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact tP.symm) hL
  refine ⟨h₆a, by rw [sp₆, sp₅, h₄.regs.sp], ?_, by rw [hT, hP, hc, hv]; rfl⟩
  rw [m₆]
  refine (((f₂.sub (fin_sub h (by decide))).trans (f₃.sub (cnt_sub h))).trans (f₄.sub (ctr_sub h))).mono
    (fun r hr => List.mem_cons_of_mem _ hr) |>.trans (fT.mono fun r hr => ?_)
  simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self

end VG.Proof.AesSiv.AArch64

end

end

/-!
# AES-SIV on AArch64: the end of `vg_aes_siv_decrypt`

From S2V's state of the associated data on, `decrypt` sets the counter from
the IV it is given (`counter_ok`), decrypts the data in place with CTR
(`ctr_wp`), finishes S2V with the plaintext into `W + 112` (`finish_wp`),
compares the two IVs without a branch (`compare_ok`), ANDs the data with the
mask of the result, a word at a time and then its last bytes one at a time
(`maskData_wp`) and restores the registers
(`openTail_wp`).
-/

@[expose] public section

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.AesSiv (or_xor_eq_zero le8_append_eq eqz)
open VG.Proof.CmacAes.AArch64 (k0 succ_ofNat read_one)
open VG.Proof.CmacAes.Stream.AArch64 (toNat_ofNat eval_zero eval_nonzero mz0 bytesAt_writeBytes_self)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The OR of the XORs of the halves of the IVs at `W` and `W + 112` is 0
exactly if they are equal. -/
theorem ivs_eq (m : Mem) (W : Addr) :
    ((m.readW (W + BitVec.ofNat 64 0) 64 ^^^ m.readW (W + BitVec.ofNat 64 tOff) 64) |||
        (m.readW (W + BitVec.ofNat 64 8) 64 ^^^ m.readW (W + BitVec.ofNat 64 (tOff + 8)) 64)) = 0 ↔
      Spec.Aes.bytesAt m W 16 = Spec.Aes.bytesAt m (W + BitVec.ofNat 64 tOff) 16 := by
  rw [or_xor_eq_zero, Proof.Cmac.bytesAt_split, Proof.Cmac.bytesAt_split, ← Proof.Cmac.le8_readW,
    ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, ← Proof.Cmac.le8_readW, le8_append_eq, Offset.add_add, k0]

theorem rot0 (x : BitVec 64) : x.rotateRight 0 = x := by
  simp [BitVec.rotateRight, BitVec.rotateRightAux]

theorem sw64 (x : BitVec (8 * 8)) : BitVec.setWidth 64 x = x := BitVec.setWidth_eq x

theorem compare_ok (h : Env s₀ C D P W R L) {s : State} (h19 : s.gpr .x19 = W) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) :
    ∃ s', runBlock isa compare s = some s' ∧
      s'.gpr .x0 = (if Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
        then 1 else 0) ∧
      s'.gpr .x11 = 0 - s'.gpr .x0 ∧
      (∀ r, r ≠ .x0 → r ≠ .x9 → r ≠ .x10 → r ≠ .x11 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain r₀ := h.inRW hrd hwr (d := 0) (n := 8) (by decide)
  obtain r₁ := h.inRW hrd hwr (d := tOff) (n := 8) (by decide)
  obtain r₂ := h.inRW hrd hwr (d := 8) (n := 8) (by decide)
  obtain r₃ := h.inRW hrd hwr (d := tOff + 8) (n := 8) (by decide)
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, and_self, Impl.AesSiv.AArch64.compare, tOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, addr, State.load, Size.bytes, Size.bits, State.read, gpr_write, mem_write, rd_write,
      wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, h19, r₀, r₁, r₂, r₃]
    rfl, ?_, ?_, ?_, by rfl, by rfl, by rfl, by rfl⟩
  · have e := ivs_eq s.mem W
    have rd8 (a : Addr) : s.mem.read a 8 = s.mem.readW a 64 := (sw64 _).symm
    simp only [gpr_write, reduceCtorEq, ite_true, ite_false, rot0]
    rw [sw64]
    simp only [rd8]
    refine (eqz _).trans ?_
    by_cases hb : Spec.Aes.bytesAt s.mem W 16 = Spec.Aes.bytesAt s.mem (W + BitVec.ofNat 64 tOff) 16
    · exact (ite_eq_left (e.mpr hb)).trans (ite_eq_left hb).symm
    · exact (ite_eq_right (mt e.mp hb)).trans (ite_eq_right hb).symm
  · simp [gpr_write]
  · intro r h₁ h₂ h₃ h₄; simp [gpr_write, h₁, h₂, h₃, h₄]

/-! ## Masking the data -/

/-- A byte ANDed with the mask `0 − r` of a result `r` of 0 or 1. -/
theorem mask_byte (b : BitVec (8 * 1)) (c : Bool) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b) &&&
      ((0 : BitVec 64) - (if c then 1 else 0)))) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    simp [hj]

/-- The loop body of `maskData`. -/
abbrev maskBody : List Instr :=
  [.ldrb .x9 .x6 0, .logic .and .x .x9 .x9 .x11, .strb .x9 .x6 0, .addImm .x .x6 .x6 1, .subImm .x .x8 .x8 1]

theorem maskStep_ok (s : State) {A : Addr} {c : Bool} (ha : s.gpr .x6 + BitVec.ofNat 64 0 = A)
    (h11 : s.gpr .x11 = 0 - (if c then 1 else 0)) (rq : InRegions (s.rd ++ s.wr) A 1) (wq : InRegions s.wr A 1) :
    ∃ s', runBlock isa maskBody s = some s' ∧
      s'.mem = s.mem.writeW A ((if c then s.mem A else 0 : Byte)) ∧
      s'.gpr .x6 = s.gpr .x6 + 1 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bits, State.read,
      gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq, ha, rq, wq]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃],
    rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, h11, mask_byte, read_one, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

/-- What `maskData` leaves: the data, or zeros. -/
structure Masked (s : State) (P : Addr) (L : Nat) (c : Bool) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P L else Spec.Siv.zeros L)
  other : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The loop body of `maskData`'s words. -/
abbrev maskWordBody : List Instr :=
  [.ldr .x .x9 .x6 0, .logic .and .x .x9 .x9 .x11, .str .x .x9 .x6 0, .addImm .x .x6 .x6 8, .subImm .x .x8 .x8 1]

theorem maskWord_ok (s : State) {A : Addr} {c : Bool} (ha : s.gpr .x6 + BitVec.ofNat 64 0 = A)
    (h11 : s.gpr .x11 = 0 - (if c then 1 else 0)) (rq : InRegions (s.rd ++ s.wr) A 8) (wq : InRegions s.wr A 8) :
    ∃ s', runBlock isa maskWordBody s = some s' ∧
      s'.mem = s.mem.writeW A (s.mem.readW A 64 &&& (0 - if c then 1 else 0)) ∧
      s'.gpr .x6 = s.gpr .x6 + 8 ∧ s'.gpr .x8 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, Nat.reduceMod, and_self, maskWordBody,
      runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store, Size.bytes, Size.bits,
      State.read, gpr_write, mem_write, rd_write, wr_write, Option.bind_some, Option.map_some, BitVec.setWidth_eq,
      ha, rq, wq]
    rfl, ?_⟩
  refine ⟨?_, by simp [gpr_write], by simp [gpr_write], fun r h₁ h₂ h₃ => by simp [gpr_write, h₁, h₂, h₃],
    rfl, rfl, rfl⟩
  simp only [mem_write, Mem.writeW, Mem.readW, h11, BitVec.setWidth_eq]

theorem shr3 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 3 = BitVec.ofNat 64 (c / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega_arith), Nat.shiftRight_eq_div_pow]

theorem low3 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c <<< 61 >>> 61 = BitVec.ofNat 64 (c % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hc, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show (2 : Nat) ^ 64 = 2 ^ 3 * 2 ^ 61 from rfl, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (by decide),
    Nat.mod_eq_of_lt (a := c % 2 ^ 3) (by omega_arith)]

/-- The data from `P + j` on, where the bytes before are done. -/
structure MaskInv (s : State) (P : Addr) (c : Bool) (j : Nat) (t : State) : Prop where
  x6 : t.gpr .x6 = P + BitVec.ofNat 64 j
  mem : t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j)
  other : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem maskData_wp (s : State) {P : Addr} {L : Nat} {c : Bool} (hL : L < 2 ^ 64) (hwP : P.toNat + L ≤ 2 ^ 64)
    (h26 : s.gpr .x26 = P) (h27 : s.gpr .x27 = BitVec.ofNat 64 L) (h11 : s.gpr .x11 = 0 - (if c then 1 else 0))
    (hr : ∀ i n, i + n ≤ L → InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) n)
    (hw : ∀ i n, i + n ≤ L → InRegions s.wr (P + BitVec.ofNat 64 i) n) :
    WP isa maskData s (Masked s P L c) := by
  have g27 {t : State} (ht : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) :
      t.gpr .x27 = BitVec.ofNat 64 L := by
    rw [ht _ (by decide) (by decide) (by decide), h27]
  have g11 {t : State} (ht : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) :
      t.gpr .x11 = 0 - (if c then 1 else 0) := by
    rw [ht _ (by decide) (by decide) (by decide), h11]
  -- What the data before `P + j` is written to.
  have fP {t : State} {j : Nat}
      (hm : t.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P j else Spec.Siv.zeros j)) :
      Frame [⟨P, j⟩] s.mem t.mem := by
    rw [hm]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  rw [maskData]
  obtain ⟨s₁, run₁, x6₁, x8₁, g₁, sp₁, m₁, rd₁, wr₁⟩ : ∃ s₁, runBlock isa [mov .x6 .x26, .lsr .x .x8 .x27 3] s =
      some s₁ ∧ s₁.gpr .x6 = P ∧ s₁.gpr .x8 = BitVec.ofNat 64 (L / 8) ∧
      (∀ r, r ≠ .x6 → r ≠ .x8 → s₁.gpr r = s.gpr r) ∧ s₁.sp = s.sp ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by
      simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, runBlock_cons, runStep_some, runBlock_nil, exec,
        Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
      rfl, ?_, ?_, fun r a b => ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_write, h26]
    · simp [gpr_write, h27, shr3 hL]
    · simp [gpr_write, a, b]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain inv₁ : MaskInv s P c 0 s₁ :=
    ⟨by rw [x6₁]; simp, by rw [m₁]; cases c <;> simp [Spec.Aes.bytesAt, Spec.Siv.zeros, writeBytes_nil],
      fun r a b _ => g₁ r a b, sp₁, rd₁, wr₁⟩
  -- The words.
  obtain words : WP isa (.ite (.zero .x .x8) (.block [])
      (.loop (.block maskWordBody) (.nonzero .x .x8))) s₁ (MaskInv s P c (8 * (L / 8))) := by
    refine WP.ite (decide (L / 8 = 0)) (eval_zero (by omega_arith) x8₁) (fun hb => WP.block_nil ?_) (fun hb => ?_)
    · rw [of_decide_eq_true hb]; exact inv₁
    obtain hn0 : L / 8 ≠ 0 := of_decide_eq_false hb
    refine WP.loop (M := isa) (c := .nonzero .x .x8)
      (fun (k : Nat) (t : State) => ∃ j, k = L / 8 - j ∧ j < L / 8 ∧ t.gpr .x8 = BitVec.ofNat 64 (L / 8 - j) ∧
        MaskInv s P c (8 * j) t) ?_ (L / 8 - 0) _ ⟨0, rfl, by omega_arith, x8₁, inv₁⟩
    rintro k t ⟨j, rfl, hj, x8, it⟩
    obtain ⟨t', run', mem', x6', x8', g', sp', rd', wr'⟩ := maskWord_ok t (A := P + BitVec.ofNat 64 (8 * j)) (c := c)
      (by rw [it.x6, BitVec.add_zero]) (g11 it.other) (by rw [it.rd, it.wr]; exact hr _ _ (by omega_arith))
      (by rw [it.wr]; exact hw _ _ (by omega_arith))
    refine WP.of_runBlock ⟨t', run', ?_⟩
    obtain hlen := length_mask s.mem P c (8 * j)
    obtain hmem : t'.mem = writeBytes s.mem P
        (if c then Spec.Aes.bytesAt s.mem P (8 * (j + 1)) else Spec.Siv.zeros (8 * (j + 1))) := by
      obtain hv : t.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 = s.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 :=
        (fP it.mem).readW (w := 64) (Region.contains_self _ _) (fun r hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'
          exact (Offset.base_disjoint P (e := 8 * j) (n := 8) (k := 8 * j) (by omega_arith) (by omega_arith)).symm) (by decide)
      obtain hwa := writeBytes_append s.mem P (if c then Spec.Aes.bytesAt s.mem P (8 * j) else Spec.Siv.zeros (8 * j))
        (Proof.Cmac.le8 (s.mem.readW (P + BitVec.ofNat 64 (8 * j)) 64 &&& (0 - if c then 1 else 0)))
        (by rw [Proof.Cmac.length_le8, hlen]; omega_arith)
      rw [hlen] at hwa
      rw [mem', hv, it.mem, writeW_le8, hwa, ← mask_word, show 8 * (j + 1) = 8 * j + 8 by omega_arith]
    obtain x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L / 8 - (j + 1)) := by
      rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
    obtain ev' := eval_nonzero (s := t') (x := L / 8 - (j + 1)) (by omega_arith) x8''
    obtain gg : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
      rw [g' r h₁ h₂ h₃, it.other r h₁ h₂ h₃]
    obtain x6'' : t'.gpr .x6 = P + BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [x6', it.x6, BitVec.add_assoc, show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add,
        show 8 * j + 8 = 8 * (j + 1) by omega_arith]
    by_cases he : j + 1 = L / 8
    · left
      refine ⟨by rw [ev']; simp [he], ⟨by rw [x6'', he], ?_, gg, by rw [sp', it.sp], by rw [rd', it.rd],
        by rw [wr', it.wr]⟩⟩
      rw [hmem, he]
    · right
      refine ⟨by rw [ev']; simp; omega_arith, L / 8 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, x8'',
        ⟨x6'', hmem, gg, by rw [sp', it.sp], by rw [rd', it.rd], by rw [wr', it.wr]⟩⟩
  refine WP.seq (WP.mono words fun t it => ?_)
  -- The bytes.
  obtain hj₀ : 8 * (L / 8) ≤ L := by omega_arith
  obtain ⟨t₁, run₁', x8₁', g₁', sp₁', m₁', rd₁', wr₁'⟩ : ∃ t₁, runBlock isa [.lsl .x .x8 .x27 61, .lsr .x .x8 .x8 61] t =
      some t₁ ∧ t₁.gpr .x8 = BitVec.ofNat 64 (L - 8 * (L / 8)) ∧ (∀ r, r ≠ .x8 → t₁.gpr r = t.gpr r) ∧
      t₁.sp = t.sp ∧ t₁.mem = t.mem ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by
      simp only [↓reduceIte, Nat.reduceLT, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits]
      rfl, ?_, fun r a => ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_write, State.read, BitVec.setWidth_eq, ↓reduceIte, g27 it.other, low3 hL]
      rw [show L % 8 = L - 8 * (L / 8) by omega_arith]
    · simp [gpr_write, a]
    all_goals rfl
  obtain it₁ : MaskInv s P c (8 * (L / 8)) t₁ :=
    ⟨by rw [g₁' _ (by decide), it.x6], by rw [m₁', it.mem],
      fun r h₁ h₂ h₃ => by rw [g₁' r h₂, it.other r h₁ h₂ h₃], by rw [sp₁', it.sp], by rw [rd₁', it.rd],
      by rw [wr₁', it.wr]⟩
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁', ?_⟩)
  refine WP.ite (decide (L - 8 * (L / 8) = 0)) (eval_zero (by omega_arith) x8₁') (fun hb => WP.block_nil ?_)
    (fun hb => ?_)
  · have he : 8 * (L / 8) = L := by have := of_decide_eq_true hb; omega_arith
    rw [he] at it₁
    exact ⟨it₁.mem, it₁.other, it₁.sp, it₁.rd, it₁.wr⟩
  obtain hlt₀ : 8 * (L / 8) < L := by have := of_decide_eq_false hb; omega_arith
  refine WP.loop (M := isa) (body := .block maskBody) (c := .nonzero .x .x8)
    (fun (k : Nat) (t : State) => ∃ j, k = L - j ∧ j < L ∧ t.gpr .x8 = BitVec.ofNat 64 (L - j) ∧
      MaskInv s P c j t) ?_ (L - 8 * (L / 8)) _ ⟨8 * (L / 8), rfl, hlt₀, x8₁', it₁⟩
  rintro k t ⟨j, rfl, hj, x8, it⟩
  obtain ⟨t', run', mem', x6', x8', g', sp', rd', wr'⟩ := maskStep_ok t (A := P + BitVec.ofNat 64 j) (c := c)
    (by rw [it.x6, BitVec.add_zero]) (g11 it.other) (by rw [it.rd, it.wr]; exact hr j 1 (by omega_arith))
    (by rw [it.wr]; exact hw j 1 (by omega_arith))
  refine WP.of_runBlock ⟨t', run', ?_⟩
  obtain hq : t.mem (P + BitVec.ofNat 64 j) = s.mem (P + BitVec.ofNat 64 j) :=
    fP it.mem _ fun r hr' hcon => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp only [Region.Contains, Mem.sub_ofNat_toNat P (show j < 2 ^ 64 by omega_arith)] at hcon; omega_arith
  obtain hmem : t'.mem = writeBytes s.mem P (if c then Spec.Aes.bytesAt s.mem P (j + 1) else Spec.Siv.zeros (j + 1)) := by
    rw [mem', hq, it.mem, mask_succ, writeBytes_snoc _ _ _ _ (by rw [length_mask]; omega_arith), length_mask]
  obtain x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (j + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith)]; rfl
  obtain ev' := eval_nonzero (s := t') (x := L - (j + 1)) (by omega_arith) x8''
  obtain gg : ∀ r, r ≠ .x6 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ => by
    rw [g' r h₁ h₂ h₃, it.other r h₁ h₂ h₃]
  by_cases he : j + 1 = L
  · left
    exact ⟨by rw [ev']; simp [he], by rw [hmem, he], gg, by rw [sp', it.sp], by rw [rd', it.rd],
      by rw [wr', it.wr]⟩
  · right
    refine ⟨by rw [ev']; simp; omega_arith, L - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, x8'',
      ⟨by rw [x6', it.x6, BitVec.add_assoc, succ_ofNat], hmem, gg, by rw [sp', it.sp], by rw [rd', it.rd],
        by rw [wr', it.wr]⟩⟩

/-! ## From S2V's state on -/

theorem openTail_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L)
    (hcp : (⟨C, 512⟩ : Region).Disjoint ⟨P, L⟩) (hPw : (⟨P, L⟩ : Region) ∈ s₀.wr) {s : State}
    (hs : SPre s₀ C D P W R L s) {g : Reg → BitVec 64} (hsv : Spill.Saved W g saved s.mem) :
    WP isa (.seq (.block (counter 0)) (.seq (ctr v.ctr.callee) (.seq (finish v.callee v.ctr.callee v.ctr.suffix tOff)
        (.seq (.block Impl.AesSiv.AArch64.compare) (.seq maskData (.block restore)))))) s
      fun s' => (∀ r ∈ preserved, s'.gpr r = g r) ∧ s'.sp = s₀.sp ∧
        Frame (endRegions W P L) s.mem s'.mem ∧
        match Spec.Siv.openWith (Spec.Siv.ctxMac s.mem C R) (Spec.Siv.ctxCiph s.mem C R)
            (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem W 16) (Spec.Aes.bytesAt s.mem P L) with
        | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem P L = pt
        | none => (s'.gpr .x0).setWidth 32 = 0 ∧ Spec.Aes.bytesAt s'.mem P L = Spec.Siv.zeros L := by
  obtain hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega_arith
  obtain hL : L ≤ 2 ^ 64 := by have := h.lt; omega_arith
  -- The counter.
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := counter_ok h hs.regs.x19 hs.regs.rd hs.regs.wr
  obtain hr₁ : Regs s₀ C D P W R L s₁ := hs.regs.keep' (fun r hr => g₁ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide)) sp₁ rd₁ wr₁
  obtain fc : Frame (cntRegions W) s.mem s₁.mem := m₁ ▸ counter_frame _ _ _ _
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  obtain hcnt : ∃ hi lo : BitVec 64, s₁.mem.readW (W + BitVec.ofNat 64 cntOff) 64 = rev64 hi ∧
      s₁.mem.readW (W + BitVec.ofNat 64 (cntOff + 8)) 64 = rev64 lo ∧
      (hi ++ lo : BitVec 128) = Spec.Gcm.ofBytes (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) := by
    rw [m₁]; exact counter_cnt s.mem W
  -- CTR.
  refine WP.seq (WP.mono (ctr_wp v.ctr h hcp hPw hr₁ (length_counter _) (counter_low _) hcnt (by rw [g₁ _ (by decide) (by decide), hs.x26])
    (by rw [g₁ _ (by decide) (by decide), hs.x27])) fun s₂ h₂ => ?_)
  have f₂ := h₂.frame
  -- S2V into `W + 112`.
  refine WP.seq (WP.mono (finish_wp v h h₂.regs (out := tOff) (Or.inr rfl)) fun s₃ h₃ => ?_)
  have f₃ := h₃.frame
  -- The comparison.
  obtain ⟨s₄, run₄, x0₄, x11₄, g₄, sp₄, m₄, rd₄, wr₄⟩ := compare_ok h h₃.regs.x19 h₃.regs.rd h₃.regs.wr
  obtain hr₄ : Regs s₀ C D P W R L s₄ := h₃.regs.keep' (fun r hr => g₄ r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide))
    sp₄ rd₄ wr₄
  refine WP.seq (WP.of_runBlock ⟨s₄, run₄, ?_⟩)
  -- The mask.
  refine WP.seq (WP.mono (maskData_wp s₄ (c := decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) h.lt h.wP
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.hold.1, h₂.x26])
    (by rw [g₄ _ (by decide) (by decide) (by decide) (by decide), h₃.hold.2, h₂.x27])
    (by rw [x11₄, x0₄]; simp only [decide_eq_true_eq]) (fun _ _ hin => h.inRP hr₄.rd hr₄.wr hin)
    (fun _ _ hin => h.inWP hPw hr₄.wr hin)) fun s₅ h₅ => ?_)
  obtain f₅ : Frame [⟨P, L⟩] s₄.mem s₅.mem := by
    rw [h₅.mem]; exact writeBytes_frame _ _ _ (by rw [length_mask]; exact Region.contains_self _ _)
  obtain hr₅ : Regs s₀ C D P W R L s₅ := hr₄.keep' (fun r hr => h₅.other r (by rintro rfl; revert hr; decide)
    (by rintro rfl; revert hr; decide) (by rintro rfl; revert hr; decide)) h₅.sp h₅.rd h₅.wr
  obtain hsv₅ : Spill.Saved W g saved s₅.mem := by
    have hb := saved_bound
    refine (((hsv.frame fc fun p hp => ?_).frame f₂ fun p hp => ?_).frame f₃ fun p hp => ?_).frame
      (m' := s₅.mem) (by rw [← m₄]; exact f₅) fun p hp => ?_
    · have := hb p hp; exact cnt_dis (by omega_arith) (by omega_arith)
    · have := hb p hp; exact ctr_dis h (by omega_arith) (by omega_arith)
    · have := hb p hp
      exact fin_dis h (by decide) (by omega_arith) (by simp only [tOff]; omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    · have := hb p hp
      exact one_out (h.p_w.sub_right (h.sW (d := p.2) (n := 8) (by omega_arith))).symm
  refine WP.mono (restore_wp h hr₅.x19 hr₅.rd hr₅.wr hsv₅) fun s₇ ⟨h₇a, h₇b, sp₇, m₇⟩ => ?_
  obtain x0₇ : s₇.gpr .x0 = s₄.gpr .x0 := by
    rw [h₇b _ (by decide), h₅.other _ (by decide) (by decide) (by decide)]
  -- The IV, the plaintext and S2V's end.
  obtain hV : Spec.Aes.bytesAt s₃.mem W 16 = Spec.Aes.bytesAt s.mem W 16 := by
    obtain d₃ := fin_dis h (out := tOff) (d := 0) (n := 16) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    obtain d₂ := ctr_dis h (d := 0) (n := 16) (by decide) (by decide)
    obtain dc := cnt_dis (W := W) (d := 0) (n := 16) (by decide) (by decide)
    rw [k0] at d₃ d₂ dc
    rw [Proof.Cmac.bytesAt_frame f₃ d₃ (by decide), Proof.Cmac.bytesAt_frame f₂ d₂ (by decide),
      Proof.Cmac.bytesAt_frame fc dc (by decide)]
  obtain hp : Spec.Aes.bytesAt s₂.mem P L = Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R)
      (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16)) (Spec.Aes.bytesAt s.mem P L) := by
    rw [h₂.data, ctxCiph_frame fc (cnt_out h.c_w) hRb, Proof.Cmac.bytesAt_frame fc (cnt_out h.p_w) hL]
  obtain hT : Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 =
      Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) := by
    rw [h₃.out, hp, ctxMac_frame f₂ (ctr_out hcp h.c_w) hRb, ctxMac_frame fc (cnt_out h.c_w) hRb,
      Proof.Cmac.bytesAt_frame f₂ (ctr_out h.d_p h.d_w) (by decide),
      Proof.Cmac.bytesAt_frame fc (cnt_out h.d_w) (by decide)]
  obtain hd : Spec.Aes.bytesAt s₇.mem P L = if Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16 then
        Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L) else Spec.Siv.zeros L := by
    obtain hl := length_mask s₄.mem P (decide (Spec.Aes.bytesAt s₃.mem W 16 =
      Spec.Aes.bytesAt s₃.mem (W + BitVec.ofNat 64 tOff) 16)) L
    obtain hw := bytesAt_writeBytes_self s₄.mem P (by rw [hl]; exact h.lt)
    rw [hl] at hw
    rw [m₇, h₅.mem, hw, m₄, Proof.Cmac.bytesAt_frame f₃ (fin_out (by decide) h.p_w) hL, hp]
    simp only [decide_eq_true_eq]
  obtain f₅' : Frame (endRegions W P L) s₄.mem s₅.mem :=
    f₅.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  refine ⟨h₇a, by rw [sp₇, hr₅.sp], ?_, ?_⟩
  · rw [m₇]
    rw [m₄] at f₅'
    exact (((fc.sub (cnt_sub h)).trans (f₂.sub (ctr_sub h))).trans (f₃.sub (fin_sub h (by decide)))).trans f₅'
  · rw [x0₇, x0₄, hd, hV, hT]
    simp only [Spec.Siv.openWith]
    by_cases hc : Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16)
        (Spec.Siv.ctr (Spec.Siv.ctxCiph s.mem C R) (Spec.Siv.counter (Spec.Aes.bytesAt s.mem W 16))
          (Spec.Aes.bytesAt s.mem P L)) = Spec.Aes.bytesAt s.mem W 16
    · rw [ite_eq_left hc, ite_eq_left hc.symm, ite_eq_left hc.symm]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right hc, ite_eq_right (Ne.symm hc), ite_eq_right (Ne.symm hc)]
      exact ⟨rfl, rfl⟩

end VG.Proof.AesSiv.AArch64
