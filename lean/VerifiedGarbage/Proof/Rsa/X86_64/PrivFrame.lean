import VerifiedGarbage.Proof.Rsa.X86_64.PrivCtx
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch

/-!
# `vg_rsa_private_checked` on x86-64: the frame

The frame of `frameBytes` bytes at `S = rsp - frameBytes`, and the blocks
that store to its slots and read the function's stack arguments, at
`S + frameBytes + 8 + 8 j` (`stackArgAddr`).
-/

namespace VG.Proof.Rsa.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Rsa.X86_64.PrivChecked
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-! ## Addresses in the frame -/

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  simp only [State.ea, sp, BitVec.ofInt_natCast]

theorem ea_sp_off {t : State} {S : Addr} (h : t.gpr .rsp = S) (d : Nat) : t.ea (sp d) = off S d := by
  rw [ea_sp, h]

/-- The function's stack argument `j`, from the frame at `S = rsp - frameBytes`. -/
theorem ea_arg {t : State} {s : State} (h : t.gpr .rsp = s.gpr .rsp - BitVec.ofNat 64 frameBytes) (j : Nat) :
    t.ea (arg j) = stackArgAddr s j := by
  rw [arg, ea_sp, h, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

/-! ## The precondition, by name -/

/-- `chkContract.pre`, by name. -/
structure PreF (s : State) : Prop where
  sp1 : stackBytes ≤ (s.gpr .rsp).toNat
  sp2 : (s.gpr .rsp).toNat + 120 ≤ 2 ^ 64
  hrd : s.rd = [⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩, ⟨s.gpr .r8, (s.gpr .r9).toNat⟩,
    ⟨stackArg s 0, (stackArg s 1).toNat⟩, ⟨stackArg s 2, (stackArg s 3).toNat⟩,
    ⟨stackArg s 4, (stackArg s 5).toNat⟩, ⟨stackArg s 6, (stackArg s 7).toNat⟩,
    ⟨stackArg s 8, (stackArg s 9).toNat⟩, ⟨stackArg s 10, (stackArg s 11).toNat⟩, ⟨stackArgAddr s 0, 112⟩]
  hwr : s.wr = [⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩, ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩]
  dOn : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dOe : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dOi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dOp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dOq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dOdp : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dOdq : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dOqi : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dOs : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dOa : (⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  dns : (⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  des : (⟨s.gpr .r8, (s.gpr .r9).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dis : (⟨stackArg s 0, (stackArg s 1).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dps : (⟨stackArg s 2, (stackArg s 3).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dqs : (⟨stackArg s 4, (stackArg s 5).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  ddps : (⟨stackArg s 6, (stackArg s 7).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  ddqs : (⟨stackArg s 8, (stackArg s 9).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dqis : (⟨stackArg s 10, (stackArg s 11).toNat⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dsa : (⟨stackArg s 12, (stackArg s 13).toNat * 8⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  dRo : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dRs : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dKo : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
  dKn : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  dKe : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  dKi : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 0, (stackArg s 1).toNat⟩
  dKp : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 2, (stackArg s 3).toNat⟩
  dKq : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 4, (stackArg s 5).toNat⟩
  dKdp : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 6, (stackArg s 7).toNat⟩
  dKdq : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 8, (stackArg s 9).toNat⟩
  dKqi : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 10, (stackArg s 11).toNat⟩
  dKs : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint
    ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩
  dKa : (⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩ : Region).Disjoint ⟨stackArgAddr s 0, 112⟩
  wO : (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64
  wN : (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64
  wE : (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64
  wI : (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64
  wP : (stackArg s 2).toNat + (stackArg s 3).toNat ≤ 2 ^ 64
  wQ : (stackArg s 4).toNat + (stackArg s 5).toNat ≤ 2 ^ 64
  wDp : (stackArg s 6).toNat + (stackArg s 7).toNat ≤ 2 ^ 64
  wDq : (stackArg s 8).toNat + (stackArg s 9).toNat ≤ 2 ^ 64
  wQi : (stackArg s 10).toNat + (stackArg s 11).toNat ≤ 2 ^ 64
  wS : (stackArg s 12).toNat + (stackArg s 13).toNat * 8 ≤ 2 ^ 64
  k1 : 64 ≤ (s.gpr .rcx).toNat
  k2 : (s.gpr .rcx).toNat ≤ 1024
  hsi : (s.gpr .rsi).toNat = (s.gpr .rcx).toNat
  hil : (stackArg s 1).toNat = (s.gpr .rcx).toNat
  L1 : 1 ≤ (s.gpr .r9).toNat
  L2 : (s.gpr .r9).toNat ≤ (s.gpr .rcx).toNat
  pl1 : 1 ≤ (stackArg s 3).toNat
  pl2 : (stackArg s 3).toNat < (s.gpr .rcx).toNat
  ql1 : 1 ≤ (stackArg s 5).toNat
  ql2 : (stackArg s 5).toNat < (s.gpr .rcx).toNat
  hdpl : (stackArg s 7).toNat = (stackArg s 3).toNat
  hqil : (stackArg s 11).toNat = (stackArg s 3).toNat
  hdql : (stackArg s 9).toNat = (stackArg s 5).toNat
  hsl : 16 * (s.gpr .rcx).toNat ≤ (stackArg s 13).toNat

theorem preF_of {s : State} (h : chkContract.pre s) : PreF s := by
  simp only [chkContract] at h
  obtain ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOi, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, des, dis, dps, dqs, ddps,
    ddqs, dqis, dsa, dRo, -, -, -, -, -, -, -, -, dRs, -, dKo, dKn, dKe, dKi, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa,
    wO, wN, wE, wI, wP, wQ, wDp, wDq, wQi, wS, ⟨k1, k2⟩, hsi, hil, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql,
    hsl⟩ := h
  exact ⟨sp1, sp2, hrd, hwr, dOn, dOe, dOi, dOp, dOq, dOdp, dOdq, dOqi, dOs, dOa, dns, des, dis, dps, dqs, ddps,
    ddqs, dqis, dsa, dRo, dRs, dKo, dKn, dKe, dKi, dKp, dKq, dKdp, dKdq, dKqi, dKs, dKa, wO, wN, wE, wI, wP, wQ, wDp,
    wDq, wQi, wS, k1, k2, hsi, hil, L1, L2, pl1, pl2, ql1, ql2, hdpl, hqil, hdql, hsl⟩

/-! ## The frame -/

/-- The frame's base: `rsp` in the frame. -/
abbrev fb (s : State) : Addr := s.gpr .rsp - BitVec.ofNat 64 frameBytes

/-- The stack the function uses, the caller's `out` and the working space:
all the function and its calls may write. -/
def stkR (s : State) : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, stackBytes⟩
def outR (s : State) : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
def scrR (s : State) : Region := ⟨stackArg s 12, (stackArg s 13).toNat * 8⟩

theorem fb_eq (s : State) : fb s = off (s.gpr .rsp - BitVec.ofNat 64 stackBytes) 8 :=
  Offset.sub_ofNat_eq _ (by decide)

/-- Bytes of the frame are in the stack the function uses. -/
theorem frame_sub (s : State) {d n : Nat} (h : d + n ≤ frameBytes) : Region.Sub ⟨off (fb s) d, n⟩ (stkR s) := by
  rw [fb_eq, off_off]
  exact Offset.sub_base _ (by unfold frameBytes at h; unfold stackBytes; omega)

/-- The return address of a call from the frame. -/
theorem ret_sub (s : State) : Region.Sub (below (fb s) 8) (stkR s) := by
  rw [show below (fb s) 8 = ⟨s.gpr .rsp - BitVec.ofNat 64 stackBytes, 8⟩ by
    simp only [below, fb, BitVec.sub_sub, ← BitVec.ofNat_add]; rfl]
  exact Region.sub_prefix (by decide)

/-- A byte outside the stack the function uses is outside the frame. -/
theorem outside_frame (s : State) {x : Addr} (hx : ¬ (stkR s).Contains x 1) :
    frameBytes ≤ ofs (fb s) x := by
  by_contra hlt
  apply hx
  have hc : (⟨fb s, frameBytes⟩ : Region).Contains x 1 := by
    simp only [Region.Contains, ofs] at hlt ⊢; omega
  have := frame_sub s (d := 0) (n := frameBytes) (by decide)
  simp only [off, BitVec.add_zero] at this
  exact this x hc

/-- Between the calls, from the entry state `s`: in the frame, with `out`,
`n`, `n_len`, `e` and `e_len` in their slots, memory changed only where the
function may write. -/
structure Env (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  mem : Frame [stkR s, outR s, scrR s] s.mem t.mem
  sOut : word t.mem (fb s) oOut = s.gpr .rdi
  sN : word t.mem (fb s) oN = s.gpr .rdx
  sK : word t.mem (fb s) oK = s.gpr .rcx
  sE : word t.mem (fb s) oE = s.gpr .r8
  sEl : word t.mem (fb s) oEl = s.gpr .r9

theorem Env.scr {s t : State} (h : Env s t) (hp : PreF s) : Scr t (fb s) frameBytes :=
  Scr.of_mem (by rw [h.wr]; exact List.mem_cons_self ..) (by
    have := hp.sp1; simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes stackBytes at *
    omega)

/-- A buffer of the caller that the function does not write. -/
theorem Env.bytes {s t : State} (h : Env s t) {p : Addr} {len : Nat} (hk : (stkR s).Disjoint ⟨p, len⟩)
    (ho : (outR s).Disjoint ⟨p, len⟩) (hs : (scrR s).Disjoint ⟨p, len⟩) (hl : len ≤ 2 ^ 64) :
    Spec.Rsa.bytesAt t.mem p len = Spec.Rsa.bytesAt s.mem p len := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h.mem.bytes (R := ⟨p, len⟩) (fun r hr => ?_) hl (List.mem_range.mp hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hk.symm
  · exact ho.symm
  · exact hs.symm

theorem Env.arg {s t : State} (h : Env s t) (hp : PreF s) {j : Nat} (hj : j < 14) :
    t.mem.readW (stackArgAddr s j) 64 = stackArg s j := by
  refine h.mem.readW (r := ⟨stackArgAddr s 0, 112⟩) ?_ (fun r hr => ?_) (by decide)
  · rw [stackArgAddr_eq s j]; exact Offset.contains_base _ (by omega) (by omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.dKa.symm
    · exact hp.dOa.symm
    · exact hp.dsa.symm

theorem stackArgAddr_fb (s : State) (j : Nat) : stackArgAddr s j = off (fb s) (frameBytes + 8 + 8 * j) := by
  rw [off, show frameBytes + 8 + 8 * j = frameBytes + 8 * (j + 1) by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc, BitVec.sub_add_cancel]
  rfl

theorem fb_toNat {s : State} (hp : PreF s) : (fb s).toNat + frameBytes + 8 + 112 ≤ 2 ^ 64 := by
  have := hp.sp1; have := hp.sp2
  simp only [fb, BitVec.toNat_sub, BitVec.toNat_ofNat]; unfold frameBytes stackBytes at *; omega

/-- Memory changed only in the frame turns into `Env`'s. -/
theorem frame_of_outside {s : State} {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) :
    Frame [stkR s, outR s, scrR s] s.mem m :=
  fun x hx => h x (.inr (outside_frame s (hx _ (List.mem_cons_self ..))))

/-- A stack argument, past stores to the frame. -/
theorem arg_outside {s : State} (hp : PreF s) {m : Mem} (h : Outside (fb s) 0 frameBytes s.mem m) {j : Nat}
    (hj : j < 14) : m.readW (stackArgAddr s j) 64 = stackArg s j := by
  have := fb_toNat hp
  show m.readW _ 64 = s.mem.readW _ 64
  rw [stackArgAddr_fb]
  exact h.word (.inr (by unfold frameBytes; omega)) (by unfold frameBytes at *; omega)

/-! ## The CRT's arguments -/

def slotStores : List Instr :=
  [.store (sp oOut) .rdi, .store (sp oN) .rdx, .store (sp oK) .rcx, .store (sp oE) .r8, .store (sp oEl) .r9]

def copyArg (j : Nat) : List Instr := [.mov .rax (.mem (arg (j + 2))), .store (sp (8 * j)) .rax]

def crtRegs : List Instr :=
  lea .rdi oM ++ [.mov .rsi (.reg .rcx), .mov .r8 (.mem (arg 0)), .mov .r9 (.reg .rcx)]

theorem crtArgs_eq : crtArgs = slotStores ++ ((List.range 12).flatMap copyArg ++ crtRegs) := rfl

theorem slotStores_ok {s t : State} (hsp : t.gpr .rsp = fb s) (hs : Scr t (fb s) frameBytes) :
    WP isa (.block slotStores) t fun t' => t'.mem =
      ((((t.mem.writeW (off (fb s) oOut) (t.gpr .rdi)).writeW (off (fb s) oN) (t.gpr .rdx)).writeW
        (off (fb s) oK) (t.gpr .rcx)).writeW (off (fb s) oE) (t.gpr .r8)).writeW (off (fb s) oEl) (t.gpr .r9) ∧
      Keep [] t t' :=
  WP.keep [] (by
    xrun [slotStores, ea_sp, hsp, hs.st (d := oOut) (by decide), hs.st (d := oN) (by decide),
      hs.st (d := oK) (by decide), hs.st (d := oE) (by decide), hs.st (d := oEl) (by decide)]) rfl

/-- Stack argument `j + 2` to the frame's word `j`. -/
theorem copyArg_ok {s t : State} (hp : PreF s) (hsp : t.gpr .rsp = fb s) (hs : Scr t (fb s) frameBytes)
    (hrd : t.rd = s.rd) (ho : Outside (fb s) 0 frameBytes s.mem t.mem) {j : Nat} (hj : j < 12) :
    WP isa (.block (copyArg j)) t fun t' => t'.mem = t.mem.writeW (off (fb s) (8 * j)) (stackArg s (j + 2)) ∧
      Keep [.rax] t t' := by
  have ha : InRegions (t.rd ++ t.wr) (stackArgAddr s (j + 2)) 8 :=
    ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by rw [hrd, hp.hrd]; simp),
      by rw [stackArgAddr_eq s (j + 2)]; exact Offset.contains_base _ (by omega) (by omega)⟩
  exact WP.keep [.rax] (by
    xrun [copyArg, ea_arg hsp, ea_sp, hsp, ha, arg_outside hp ho (show j + 2 < 14 by omega),
      hs.st (d := 8 * j) (by unfold frameBytes; omega)]) rfl

/-- The first `n` copies. -/
theorem copies_ok {s : State} (hp : PreF s) : ∀ (n : Nat), n ≤ 12 → ∀ (t : State), t.gpr .rsp = fb s →
    Scr t (fb s) frameBytes → t.rd = s.rd → Outside (fb s) 0 frameBytes s.mem t.mem →
    WP isa (.block ((List.range n).flatMap copyArg)) t fun t' => Outside (fb s) 0 frameBytes s.mem t'.mem ∧
      (∀ i < n, word t'.mem (fb s) (8 * i) = stackArg s (i + 2)) ∧
      (∀ d, 8 * n ≤ d → d + 8 ≤ frameBytes → word t'.mem (fb s) d = word t.mem (fb s) d) ∧ Keep [.rax] t t'
  | 0, _, t, _, _, _, ho => WP.block_nil ⟨ho, fun _ h => absurd h (by omega), fun _ _ _ => rfl, Keep.refl _ _⟩
  | n + 1, hn, t, hsp, hs, hrd, ho => by
    have hF := fb_toNat hp
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (copies_ok hp n (by omega) t hsp hs hrd ho) fun t₁ ⟨ho₁, hw₁, hk₁, k₁⟩ => ?_
    refine WP.mono (copyArg_ok hp ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) (k₁.2.1.trans hrd) ho₁
      (show n < 12 by omega)) fun t' ⟨hm, k'⟩ => ⟨?_, fun i hi => ?_, fun d hd hd' => ?_,
        (k₁.trans k').mono (by decide)⟩
    · rw [hm]
      exact fun x hx => (writeW_outside _ _ _ (by unfold frameBytes at *; omega) x (by unfold frameBytes at hx; omega)).trans
        (ho₁ x hx)
    · rw [hm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [(writeW_outside t₁.mem (fb s) (stackArg s (n + 2)) (d := 8 * n) (by unfold frameBytes at *; omega)).word
          (.inl (by omega)) (by unfold frameBytes at *; omega)]
        exact hw₁ i hi
      · exact word_writeW_self _ _ _ _
    · rw [hm, (writeW_outside t₁.mem (fb s) (stackArg s (n + 2)) (d := 8 * n) (by unfold frameBytes at *; omega)).word
        (.inr (by omega)) (by unfold frameBytes at *; omega)]
      exact hk₁ d (by omega) hd'

/-- A word past a store to another word of the frame. -/
theorem word_wo (m : Mem) (base : Addr) {d d' : Nat} (v : BitVec 64) (h : d + 8 ≤ d' ∨ d' + 8 ≤ d)
    (hd : d + 8 ≤ 4096) (hd' : d' + 8 ≤ 4096) : word (m.writeW (off base d) v) base d' = word m base d' :=
  (writeW_outside m base v (by omega)).word (by omega) (by omega)

theorem allocState_gpr (s : State) (r : Reg) :
    (allocState frameBytes s).gpr r = if r = .rsp then fb s else s.gpr r := rfl

/-- The frame's push, and the CRT's arguments: `Env`, the CRT's stack
arguments in the frame, and its arguments in registers. -/
theorem crtArgs_ok {s : State} (hp : PreF s) :
    WP isa (.block crtArgs) (allocState frameBytes s) fun t => Env s t ∧
      Outside (fb s) 0 frameBytes s.mem t.mem ∧ (∀ i < 12, word t.mem (fb s) (8 * i) = stackArg s (i + 2)) ∧
      t.gpr .rdi = off (fb s) oM ∧ t.gpr .rsi = s.gpr .rcx ∧ t.gpr .rdx = s.gpr .rdx ∧
      t.gpr .rcx = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧ t.gpr .r9 = s.gpr .rcx := by
  have hF := fb_toNat hp
  set A := allocState frameBytes s with hA
  have hsp : A.gpr .rsp = fb s := rfl
  have hs : Scr A (fb s) frameBytes := Scr.of_mem (List.mem_cons_self ..) (by unfold frameBytes at *; omega)
  rw [crtArgs_eq, WP.block_append_iff]
  refine WP.mono (slotStores_ok hsp hs) fun t₁ ⟨hm₁, k₁⟩ => ?_
  have ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := by
    rw [hm₁]
    intro x hx
    have hx' : frameBytes ≤ ofs (fb s) x := by unfold frameBytes at hx ⊢; omega
    unfold frameBytes at hx hx'
    simp only [oOut, oN, oK, oE, oEl] at *
    rw [writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega), writeW_outside _ _ _ (by omega) x (by omega),
      writeW_outside _ _ _ (by omega) x (by omega)]
    rfl
  have hslots : word t₁.mem (fb s) oOut = s.gpr .rdi ∧ word t₁.mem (fb s) oN = s.gpr .rdx ∧
      word t₁.mem (fb s) oK = s.gpr .rcx ∧ word t₁.mem (fb s) oE = s.gpr .r8 ∧ word t₁.mem (fb s) oEl = s.gpr .r9 := by
    rw [hm₁]
    simp (disch := decide) only [word_wo, word_writeW_self, oOut, oN, oK, oE, oEl]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (copies_ok hp 12 (le_refl _) t₁ ((k₁.gpr (by decide)).trans hsp) (hs.congr k₁.2.2) k₁.2.1 ho₁)
    fun t₂ ⟨ho₂, hw₂, hk₂, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  have hrd₂ : InRegions (t₂.rd ++ t₂.wr) (stackArgAddr s 0) 8 :=
    ⟨⟨stackArgAddr s 0, 112⟩, List.mem_append_left _ (by
      rw [k12.2.1, show A.rd = s.rd from rfl, hp.hrd]
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl trivial))))))))),
      by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩
  refine WP.mono (WP.keep [.rdi, .rsi, .r8, .r9] (Q := fun t => t.gpr .rdi = off (fb s) oM ∧
      t.gpr .rsi = s.gpr .rcx ∧ t.gpr .r8 = stackArg s 0 ∧ t.gpr .r9 = s.gpr .rcx ∧ t.mem = t₂.mem) (by
    xrun [crtRegs, lea, List.cons_append, List.nil_append, sx_ofNat (show oM < 2 ^ 31 by decide), arg, ea_sp, hsp,
      show fb s + BitVec.ofNat 64 (frameBytes + 8 + 8 * 0) = stackArgAddr s 0 from (stackArgAddr_fb s 0).symm, k12.gpr (show Reg.rsp ∉ [] ++ [Reg.rax] by decide),
      k12.gpr (show Reg.rcx ∉ [] ++ [Reg.rax] by decide), hrd₂, arg_outside hp ho₂ (show 0 < 14 by decide)]
    exact ⟨rfl, rfl⟩) rfl) fun t ⟨⟨hdi, hsi, h8, h9, hm⟩, k⟩ => ?_
  have k' := k12.trans k
  have hw : ∀ d, 96 ≤ d → d + 8 ≤ frameBytes → word t.mem (fb s) d = word t₁.mem (fb s) d := fun d hd hd' => by
    rw [hm]; exact hk₂ d (by omega) hd'
  obtain ⟨h1, h2, h3, h4, h5⟩ := hslots
  refine ⟨⟨(k'.gpr (by decide)).trans hsp, k'.2.1, k'.2.2, frame_of_outside (hm ▸ ho₂),
      (hw _ (by decide) (by decide)).trans h1, (hw _ (by decide) (by decide)).trans h2,
      (hw _ (by decide) (by decide)).trans h3, (hw _ (by decide) (by decide)).trans h4,
      (hw _ (by decide) (by decide)).trans h5⟩, hm ▸ ho₂, fun i hi => hm ▸ hw₂ i hi, hdi, hsi,
    (k'.gpr (by decide)).trans rfl, (k'.gpr (by decide)).trans rfl, h8, h9⟩

end VG.Proof.Rsa.X86_64
