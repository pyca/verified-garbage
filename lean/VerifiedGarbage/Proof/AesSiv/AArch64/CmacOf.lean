import VerifiedGarbage.Proof.AesSiv.AArch64.Call
import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.AbsorbBlocks
import VerifiedGarbage.Proof.AesSiv.CtrPart

/-!
# AES-SIV on AArch64: the CMAC of a string (`cmacOf`)

`cmacOf` computes the CMAC of the string with the context's PRF into the
state at `W + 128`: the code zeroes the state, computes `16 nb`, the bytes of
the whole blocks before the last 1 to 16 (`Spec.Cmac.chainedLen`), into
`x28`, chains the `nb` blocks with `vg_cmac_aes_update` and finalizes the
rest with `vg_cmac_aes_finalize` (`Siv.cmacWith_chained`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 mn agree_of)
open VG.Proof.CmacAes.Stream.AArch64 (UArgs UPost FArgs upd_call upd_rel fin_rel toNat_ofNat eval_zero mz0 mz15
  nb16_bv)
open VG.Proof.Aes.AArch64 (Ctr32Impl)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-! ## The length of the whole blocks -/

theorem chainedLen_le (L : Nat) : Spec.Cmac.chainedLen 16 L ≤ L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_rest (L : Nat) : L - Spec.Cmac.chainedLen 16 L ≤ 16 := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_div (L : Nat) : 16 * (Spec.Cmac.chainedLen 16 L / 16) = Spec.Cmac.chainedLen 16 L := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem chainedLen_pos {L : Nat} (h : 0 < L) : Spec.Cmac.chainedLen 16 L = 16 * ((L - 1) / 16) := by
  simp only [Spec.Cmac.chainedLen]; omega

theorem lsr4 {c : Nat} (hc : c < 2 ^ 64) : BitVec.ofNat 64 c >>> 4 = BitVec.ofNat 64 (c / 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]

theorem ofNat_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

/-- The other registers `encrypt` and `decrypt` keep: the descriptors, the
number left, and the data and its length. -/
def Hold (s s' : State) : Prop := ∀ r ∈ [Reg.x24, .x25, .x26, .x27], s'.gpr r = s.gpr r

theorem Hold.refl (s : State) : Hold s s := fun _ _ => rfl

theorem Hold.trans {a b c : State} (h₁ : Hold a b) (h₂ : Hold b c) : Hold a c :=
  fun r hr => by rw [h₂ r hr, h₁ r hr]

theorem Hold.of {s s' : State} (h : ∀ r ∈ preserved, r ≠ .x28 → r ≠ .x30 → s'.gpr r = s.gpr r) : Hold s s' :=
  fun r hr => h r (dec_mem (by decide) hr) (dec_ne (by decide) hr) (dec_ne (by decide) hr)

/-! ## Before the update -/

theorem cmacArgs_ok {s : State} (hr : Regs s₀ C D P W R L s) {c : Nat} (hc : c < 2 ^ 64)
    (h28 : s.gpr .x28 = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa [.lsr .x .x4 .x28 4, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 stOff, mov .x3 .x22,
        .addImm .x .x5 .x19 csOff] s = some s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.gpr .x0 = C ∧ s'.gpr .x1 = BitVec.ofNat 64 R ∧ s'.gpr .x2 = W + BitVec.ofNat 64 128 ∧
      s'.gpr .x3 = P ∧ s'.gpr .x4 = BitVec.ofNat 64 (c / 16) ∧ s'.gpr .x5 = W + BitVec.ofNat 64 256 ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, stOff, csOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, by simp [gpr_write, hr.x20], by simp [gpr_write, hr.x21],
    by simp [gpr_write, hr.x19], by simp [gpr_write, hr.x22], by simp [gpr_write, h28, lsr4 hc],
    by simp [gpr_write, hr.x19], rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

theorem sub_and15 (x : BitVec 64) : x - (x &&& 15) = BitVec.ofNat 64 (16 * (x.toNat / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have h : (x &&& 15).toNat = x.toNat % 16 := by
    rw [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have := x.isLt
  rw [BitVec.toNat_sub, h, BitVec.toNat_ofNat]
  omega

theorem cmacPre_wp (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) :
    WP isa (cmacPre stOff) s fun s' => Regs s₀ C D P W R L s' ∧ Hold s s' ∧
      UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
      s'.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) ∧
      s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 128) := by
  have hcl := chainedLen_le L
  have hlt := h.lt
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := stOff) (by decide) (by decide)
  rw [cmacPre, show zero16 stOff ++ [.movz .x .x28 0 0] = zero16 stOff ++ ([.movz .x .x28 0 0] : List Instr)
    from rfl]
  refine WP.seq (WP.block_append_iff.mpr (WP.of_runBlock ⟨s₁, run₁, WP.of_runBlock ⟨s₁.write .x .x28 0, by
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, ite_true,
      mz0], ?_⟩⟩))
  -- The state after the first block.
  have hr₁ : Regs s₀ C D P W R L (s₁.write .x .x28 0) :=
    hr.keep' (fun r hr' => by
      rw [gpr_write_of_ne _ _ _ (by rintro rfl; revert hr'; decide), g₁ r (by rintro rfl; revert hr'; decide)])
      (by rw [sp_write, sp₁]) (by rw [rd_write, rd₁]) (by rw [wr_write, wr₁])
  have k₁ : ∀ r ∈ preserved, r ≠ .x28 → (s₁.write .x .x28 0).gpr r = s.gpr r := fun r hr' h28 => by
    rw [gpr_write_of_ne _ _ _ h28, g₁ r (by rintro rfl; revert hr'; decide)]
  have last (s₂ : State) (hr₂ : Regs s₀ C D P W R L s₂)
      (k₂ : ∀ r ∈ preserved, r ≠ .x28 → s₂.gpr r = s.gpr r)
      (x28₂ : s₂.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (m₂ : s₂.mem = s₁.mem) :
      WP isa (.block [.lsr .x .x4 .x28 4, mov .x0 .x20, mov .x1 .x21, .addImm .x .x2 .x19 stOff, mov .x3 .x22,
        .addImm .x .x5 .x19 csOff]) s₂ fun s' => Regs s₀ C D P W R L s' ∧ Hold s s' ∧
        UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) ∧
        s'.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) ∧
        s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 128) := by
    obtain ⟨s', run, g, x0, x1, x2, x3, x4, x5, sp, m, rd, wr⟩ := cmacArgs_ok hr₂ (by omega) x28₂
    have hr' := hr₂.keep' (fun r hr => g r (dec_mem (by decide) hr)) sp rd wr
    refine WP.of_runBlock ⟨s', run, hr', Hold.of fun r hr'' h28 _ => by rw [g r hr'', k₂ r hr'' h28],
      h.uargs hr'.rd hr'.wr (by decide) (by rw [chainedLen_div]; exact h.srcData₀ (by decide) hcl)
        (by rw [chainedLen_div]; omega) x0 x1 x2 x3 x4 x5, by rw [g _ (by decide), x28₂], by rw [m, m₂, m₁]⟩
  have ev := eval_zero (s := s₁.write .x .x28 0) hlt hr₁.x23
  by_cases hL0 : L = 0
  · refine WP.seq (WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h))
    exact last _ hr₁ k₁ (by rw [gpr_write_self, hL0]; rfl) (mem_write _ _ _ _)
  · refine WP.seq (WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_)
    refine WP.of_runBlock ⟨_, by
      simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
        State.read, gpr_write, ite_true, ite_false, BitVec.setWidth_eq]
      rfl, ?_⟩
    refine last _ (hr₁.keep' (fun r hr' => ?_) rfl rfl rfl) (fun r hr' h28 => ?_) ?_ (by simp [mem_write])
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
    · rw [← k₁ r hr' h28]
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [gpr_write]
    · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq, mz15]
      rw [chainedLen_pos (by omega), g₁ _ (by decide), hr.x23, sub_and15]
      have : (BitVec.ofNat 64 L - 1#64).toNat = L - 1 := by
        rw [BitVec.toNat_sub, toNat_ofNat hlt]; simp; omega
      rw [this]

/-! ## Between the calls -/

theorem cmacMid_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {c : Nat}
    (hc : c ≤ L) (h28 : s.gpr .x28 = BitVec.ofNat 64 c) :
    ∃ s', runBlock isa (cmacMid stOff) s = some s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      s'.gpr .x0 = C ∧ s'.gpr .x1 = BitVec.ofNat 64 R ∧ s'.gpr .x2 = W + BitVec.ofNat 64 128 ∧
      s'.gpr .x3 = P + BitVec.ofNat 64 c ∧ s'.gpr .x4 = BitVec.ofNat 64 (L - c) ∧
      s'.gpr .x5 = W + BitVec.ofNat 64 256 ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hlt := h.lt
  refine ⟨_, by
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, cmacMid, mov, stOff, csOff, runBlock_cons, runStep_some,
      runBlock_nil, exec, Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨fun r hr => ?_, by simp [gpr_write, hr.x20], by simp [gpr_write, hr.x21],
    by simp [gpr_write, hr.x19], by simp [gpr_write, hr.x22, h28],
    by simp [gpr_write, hr.x23, h28, ofNat_sub hc hlt], by simp [gpr_write, hr.x19], rfl, rfl, rfl, rfl⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]

/-! ## The whole -/

/-- What `cmacOf` leaves: the CMAC of the string with the context's PRF in the
state at `W + 128`. -/
structure CPost (s₀ : State) (C D P W : Addr) (R L : Nat) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  hold : Hold s s'
  frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 128) 16 =
    Spec.Siv.ctxMac s.mem C R (Spec.Aes.bytesAt s.mem P L)

theorem cmacOf_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L) {s : State}
    (hr : Regs s₀ C D P W R L s) :
    WP isa (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff) s (CPost s₀ C D P W R L s) := by
  have hcl := chainedLen_le L
  have hrest := chainedLen_rest L
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (cmacPre_wp h hr) fun s₁ ⟨hr₁, k₁, hu₁, x28₁, m₁⟩ => ?_)
  refine WP.seq (WP.mono (upd_call v _ hu₁) fun s₂ h₂ => ?_)
  have hr₂ := hr₁.keep h₂.saved h₂.sp h₂.rd h₂.wr
  have x28₂ : s₂.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L) := by
    rw [h₂.saved _ (by decide) (by decide), x28₁]
  obtain ⟨s₃, run₃, g₃, x0₃, x1₃, x2₃, x3₃, x4₃, x5₃, sp₃, m₃, rd₃, wr₃⟩ := cmacMid_ok h hr₂ hcl x28₂
  have hr₃ := hr₂.keep' (fun r hr => g₃ r (dec_mem (by decide) hr)) sp₃ rd₃ wr₃
  refine WP.seq (WP.of_runBlock ⟨s₃, run₃, ?_⟩)
  refine WP.mono (finr_call v.ctr _ (h.fargs hr₃.rd hr₃.wr (by decide)
    (h.srcData (o := 128) (by decide) (show Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) ≤ L by
      omega)) hrest x0₃ x1₃ x2₃ x3₃ x4₃ x5₃)) fun s₄ h₄ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s₁.mem s₂.mem := h₂.frame
  have f₄ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s₃.mem s₄.mem := h₄.frame
  have f₁ : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Proof.Cmac.frame_store2 _ _ _).mono (by simp)
  have frame : Frame [⟨W + BitVec.ofNat 64 128, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s.mem s₄.mem :=
    (f₁.trans f₂).trans (by rw [← m₃]; exact f₄)
  refine ⟨hr₃.keep h₄.saved h₄.sp h₄.rd h₄.wr,
    k₁.trans (Hold.of fun r hr h28 h30 => by rw [h₄.saved r hr h30, g₃ r hr, h₂.saved r hr h30]), frame, ?_⟩
  -- The bytes the calls read are those at the start.
  have dRead {Q : Addr} {n : Nat} (hd : ∀ r ∈ [(⟨W + BitVec.ofNat 64 128, 16⟩ : Region),
      ⟨W + BitVec.ofNat 64 256, 2176⟩], (⟨Q, n⟩ : Region).Disjoint r) (hn : n ≤ 2 ^ 64) :
      Spec.Aes.bytesAt s₁.mem Q n = Spec.Aes.bytesAt s.mem Q n ∧
        Spec.Aes.bytesAt s₃.mem Q n = Spec.Aes.bytesAt s.mem Q n := by
    have e₁ := Proof.Cmac.bytesAt_frame f₁ hd hn
    refine ⟨e₁, ?_⟩
    rw [m₃, Proof.Cmac.bytesAt_frame f₂ hd hn, e₁]
  have hlt := h.lt
  have dC {d n : Nat} (hd : d + n ≤ 512) := dRead (Q := C + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))
    · exact (h.c_w.sub_left (h.sC hd)).sub_right (h.sW (by decide))) (by omega)
  have dP {d n : Nat} (hd : d + n ≤ L) := dRead (Q := P + BitVec.ofNat 64 d) (n := n) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (h.sW (by decide))
    · exact (h.p_w.sub_left (h.sP hd)).sub_right (h.sW (by decide))) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := (dC (d := 240) (n := 16) (by decide)).2
  have k2 := (dC (d := 256) (n := 16) (by decide)).2
  have pre := (dP (d := 0) (n := Spec.Cmac.chainedLen 16 L) (by omega)).1
  have rest := (dP (d := Spec.Cmac.chainedLen 16 L) (n := L - Spec.Cmac.chainedLen 16 L) (by omega)).2
  rw [k0] at sch pre
  have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 128) 16 = Spec.Cmac.zeros 16 := by
    rw [m₁, Proof.Cmac.zero2_bytes]
  have hS : (Spec.Aes.bytesAt s.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
  have hsplit : L = Spec.Cmac.chainedLen 16 L + (L - Spec.Cmac.chainedLen 16 L) := by omega
  rw [h₄.out, mn, sch.2, k1, k2, rest, m₃, h₂.out, Proof.Cmac.Stream.blocksAt_eq, chainedLen_div, sch.1, hz, pre,
    Spec.Siv.ctxMac, Spec.Siv.schedCiph, Siv.cmacWith_chained, hS]
  have tk : (Spec.Aes.bytesAt s.mem P L).take (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem P (Spec.Cmac.chainedLen 16 L) := by
    have := Proof.AesSiv.take_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L)
      (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  have dr : (Spec.Aes.bytesAt s.mem P L).drop (Spec.Cmac.chainedLen 16 L) =
      Spec.Aes.bytesAt s.mem (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)) (L - Spec.Cmac.chainedLen 16 L) := by
    have := Proof.AesSiv.drop_bytesAt s.mem P (a := Spec.Cmac.chainedLen 16 L)
      (b := L - Spec.Cmac.chainedLen 16 L)
    rwa [← hsplit] at this
  rw [tk, dr]
  rw [Proof.Cmac.xor_comm]
  rfl

/-! ## Constant time -/

/-- The registers before and after the update, with `16 nb` in `x28`. -/
abbrev RX (s₀ : State) (C D P W : Addr) (R L : Nat) (s : State) : Prop :=
  Regs s₀ C D P W R L s ∧ s.gpr .x28 = BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L)

theorem regs_agree28 {s₀ s₀' a b : State} {C D P W : Addr} {R L : Nat} (hq : s₀.sp = s₀'.sp)
    (ha : RX s₀ C D P W R L a) (hb : RX s₀' C D P W R L b) :
    taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x28]) a b := by
  refine agree_of (by rw [ha.1.sp, hb.1.sp, hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [ha.1.x19, hb.1.x19]
  · rw [ha.1.x20, hb.1.x20]
  · rw [ha.1.x21, hb.1.x21]
  · rw [ha.1.x22, hb.1.x22]
  · rw [ha.1.x23, hb.1.x23]
  · rw [ha.2, hb.2]

theorem cmacOf_rel (v : Proof.CmacAes.AArch64.UpdateImpl) {s₀' : State} (h : Env s₀ C D P W R L)
    (h' : Env s₀' C D P W R L) (hq : s₀.sp = s₀'.sp) :
    RelCT isa (fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b)
      (cmacOf v.callee v.ctr.callee v.ctr.suffix stOff)
      fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b := by
  have hcl := chainedLen_le L
  obtain ⟨_, hA⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23]) (cmacPre stOff)
      hc).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ hc, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x28])
      (.block (cmacMid stOff)) hc).isSome = true := ⟨_, by taint_decide⟩
  have pre_wp {σ s : State} (hσ : Env σ C D P W R L) (hr : Regs σ C D P W R L s) :
      WP isa (cmacPre stOff) s fun s' => RX σ C D P W R L s' ∧
        UArgs s' C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16) :=
    WP.mono (cmacPre_wp hσ hr) fun _ ⟨a, _, b, c, _⟩ => ⟨⟨a, c⟩, b⟩
  have a := (RelCT.taint (A := taint) (P := fun a b => Regs s₀ C D P W R L a ∧ Regs s₀' C D P W R L b) _
    (fun a b hab => regs_agree hq hab.1 hab.2) hA).wp
    (F₁ := fun (s : State) => RX s₀ C D P W R L s ∧
      UArgs s C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16))
    (F₂ := fun (s : State) => RX s₀' C D P W R L s ∧
      UArgs s C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16))
    fun a b hab => ⟨pre_wp h hab.1, pre_wp h' hab.2⟩
  have u := (upd_rel v v.callee.name
    (P := fun a b => (RX s₀ C D P W R L a ∧
      UArgs a C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16)) ∧
      RX s₀' C D P W R L b ∧
      UArgs b C (W + BitVec.ofNat 64 128) P (W + BitVec.ofNat 64 256) R (Spec.Cmac.chainedLen 16 L / 16))
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.1.sp, hab.2.1.1.sp, hq]⟩).wp
    (F₁ := RX s₀ C D P W R L) (F₂ := RX s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (upd_call v _ hab.1.2) fun _ h₂ =>
        ⟨hab.1.1.1.keep h₂.saved h₂.sp h₂.rd h₂.wr, by rw [h₂.saved _ (by decide) (by decide), hab.1.1.2]⟩,
      WP.mono (upd_call v _ hab.2.2) fun _ h₂ =>
        ⟨hab.2.1.1.keep h₂.saved h₂.sp h₂.rd h₂.wr, by rw [h₂.saved _ (by decide) (by decide), hab.2.1.2]⟩⟩
  have mid_wp {σ s : State} (hσ : Env σ C D P W R L) (hr : RX σ C D P W R L s) :
      WP isa (.block (cmacMid stOff)) s fun s' => Regs σ C D P W R L s' ∧
        FArgs s' C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
          (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R := by
    obtain ⟨s', run, g, x0, x1, x2, x3, x4, x5, sp, _, rd, wr⟩ := cmacMid_ok hσ hr.1 hcl hr.2
    have hr' := hr.1.keep' (fun r hr => g r (dec_mem (by decide) hr)) sp rd wr
    exact WP.of_runBlock ⟨s', run, hr', hσ.fargs hr'.rd hr'.wr (by decide)
      (hσ.srcData (o := 128) (by decide) (by omega)) (chainedLen_rest L) x0 x1 x2 x3 x4 x5⟩
  have m := (RelCT.taint (A := taint) (P := fun a b => RX s₀ C D P W R L a ∧ RX s₀' C D P W R L b) _
    (fun a b hab => regs_agree28 hq hab.1 hab.2) hB).wp
    (F₁ := fun (s : State) => Regs s₀ C D P W R L s ∧
      FArgs s C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    (F₂ := fun (s : State) => Regs s₀' C D P W R L s ∧
      FArgs s C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    fun a b hab => ⟨mid_wp h hab.1, mid_wp h' hab.2⟩
  have f := (fin_rel v.ctr ("vg_cmac_aes_finalize" ++ v.ctr.suffix)
    (P := fun a b => (Regs s₀ C D P W R L a ∧
      FArgs a C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R) ∧
      Regs s₀' C D P W R L b ∧
      FArgs b C (W + BitVec.ofNat 64 128) (P + BitVec.ofNat 64 (Spec.Cmac.chainedLen 16 L))
        (W + BitVec.ofNat 64 256) (L - Spec.Cmac.chainedLen 16 L) R)
    fun a b hab => ⟨hab.1.2, hab.2.2, by rw [hab.1.1.sp, hab.2.1.sp, hq]⟩).wp
    (F₁ := Regs s₀ C D P W R L) (F₂ := Regs s₀' C D P W R L)
    fun a b hab => ⟨WP.mono (finr_call v.ctr _ hab.1.2) fun _ h₂ => hab.1.1.keep h₂.saved h₂.sp h₂.rd h₂.wr,
      WP.mono (finr_call v.ctr _ hab.2.2) fun _ h₂ => hab.2.1.keep h₂.saved h₂.sp h₂.rd h₂.wr⟩
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq ((u.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((m.mono (fun _ _ h => h) fun _ _ h => h.2).seq (f.mono (fun _ _ h => h) fun _ _ h => h.2)))

end VG.Proof.AesSiv.AArch64
