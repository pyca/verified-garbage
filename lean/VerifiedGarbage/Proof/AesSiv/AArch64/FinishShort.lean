import VerifiedGarbage.Proof.AesSiv.AArch64.S2vAd

/-!
# AES-SIV on AArch64: finishing S2V with a string shorter than a block

For a last string `P` of `L < 16` bytes, `shortTail` builds
`pad(P) ⊕ dbl(D)` at `W + 32`: it zeroes the block, copies `P` into it,
appends `0x80`, copies `D` to `W + 144`, doubles it there and XORs it into
the block. `shortMac` finalizes that one complete block from a zero state at
`W + out`, which is then the CMAC of `dbl(D) xor pad(P)`
(`Siv.s2vFinish_short`).
-/

namespace VG.Proof.AesSiv.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesSiv.AArch64 VG.WriteBytes
open VG.Impl.CmacAes.AArch64 (mov)
open VG.Proof.CmacAes.AArch64 (k0 mn dblMem dbl_ok dblMem_bytes dblMem_frame xor2_ok pad_ok)
open VG.Proof.CmacAes.Stream.AArch64 (FArgs Copied copy_ok copyMem copyMem_frame copyMem_bytes toNat_ofNat mz16)

variable {s₀ : State} {C D P W : Addr} {R L : Nat}

/-- The data and its length, which `finish` keeps. -/
def Hold2 (s s' : State) : Prop := s'.gpr .x26 = s.gpr .x26 ∧ s'.gpr .x27 = s.gpr .x27

theorem Hold2.trans {a b c : State} (h₁ : Hold2 a b) (h₂ : Hold2 b c) : Hold2 a c :=
  ⟨by rw [h₂.1, h₁.1], by rw [h₂.2, h₁.2]⟩

theorem Hold2.of {s s' : State} (h : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x28 → r ≠ .x30 → s'.gpr r = s.gpr r) :
    Hold2 s s' :=
  ⟨h _ (by decide) (by decide) (by decide) (by decide), h _ (by decide) (by decide) (by decide) (by decide)⟩

theorem Hold.hold2 {s s' : State} (h : Hold s s') : Hold2 s s' := ⟨h _ (by decide), h _ (by decide)⟩

/-! ## The tail -/

theorem shortB1_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) :
    ∃ s₁, runBlock isa (zero16 tailOff ++ ([.addImm .x .x6 .x19 tailOff, mov .x7 .x22, mov .x8 .x23] : List Instr))
      s = some s₁ ∧ Regs s₀ C D P W R L s₁ ∧ (∀ r ∈ preserved, s₁.gpr r = s.gpr r) ∧
      s₁.gpr .x6 = W + BitVec.ofNat 64 32 ∧ s₁.gpr .x7 = P ∧ s₁.gpr .x8 = BitVec.ofNat 64 L ∧
      s₁.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 32) := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := tailOff) (by decide) (by decide)
  have x19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), hr.x19]
  refine ⟨_, by
    rw [runBlock_append, run₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, mov, tailOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : (((s₁.write .x .x6 (s₁.gpr .x19 + BitVec.ofNat 64 32)).write .x .x7
      (s₁.gpr .x22 + BitVec.ofNat 64 0)).write .x .x8 (s₁.gpr .x23 + BitVec.ofNat 64 0)).gpr r = s.gpr r := by
    rw [← g₁ r (by rintro rfl; revert hr'; decide)]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  refine ⟨hr.keep' (fun r hr' => g r (dec_mem (by decide) hr')) sp₁ rd₁ wr₁, g, by simp [gpr_write, x19₁],
    by simp [gpr_write, g₁ _ (by decide : Reg.x22 ≠ .x9), hr.x22],
    by simp [gpr_write, g₁ _ (by decide : Reg.x23 ≠ .x9), hr.x23], by simp [mem_write, m₁]⟩

/-- The regions `shortTail` writes. -/
abbrev tailRegions (W : Addr) : List Region := [⟨W + BitVec.ofNat 64 32, 16⟩, ⟨W + BitVec.ofNat 64 144, 16⟩]

theorem shortTail_wp (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) (hL : L < 16) :
    WP isa shortTail s fun s' => Regs s₀ C D P W R L s' ∧ (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      Frame (tailRegions W) s.mem s'.mem ∧
      Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Siv.xor (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) := by
  have hwW := h.wW
  have hwD := h.wD
  have hD := h.hD
  obtain ⟨s₁, run₁, hr₁, g₁, x6₁, x7₁, x8₁, m₁⟩ := shortB1_ok h hr
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have dPT : (⟨P, L⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 32, L⟩ := h.p_w.sub_right (h.sW (by omega))
  refine WP.seq (WP.mono (copy_ok s₁ (by omega) x7₁ x6₁ x8₁
    (fun i hi => h.inRP hr₁.rd hr₁.wr (by omega))
    (fun i hi => by rw [hr₁.wr, Offset.add_add]; exact h.inW rfl (by omega)) dPT) fun s₂ h₂ => ?_)
  have g₂ (r : Reg) (hr' : r ∈ preserved) : s₂.gpr r = s₁.gpr r :=
    h₂.other r (by rintro rfl; revert hr'; decide) (by rintro rfl; revert hr'; decide)
      (by rintro rfl; revert hr'; decide) (by rintro rfl; revert hr'; decide)
  have hr₂ : Regs s₀ C D P W R L s₂ := hr₁.keep' (fun r hr' => g₂ r (dec_mem (by decide) hr')) h₂.sp h₂.rd h₂.wr
  rw [show ([.add .x .x6 .x19 .x23, .addImm .x .x6 .x6 tailOff, .movz .x .x9 0x80 0, .strb .x9 .x6 0] ++
      copy16 dOff dbOff ++ Impl.CmacAes.AArch64.dbl dbOff dbOff ++ xor2 .x19 .x19 .x19 tailOff dbOff tailOff :
        List Instr) = ([.add .x .x6 .x19 .x23, .addImm .x .x6 .x6 tailOff] : List Instr) ++
      (([.movz .x .x9 0x80 0, .strb .x9 .x6 0] : List Instr) ++ (copy16 dOff dbOff ++
        (Impl.CmacAes.AArch64.dbl dbOff dbOff ++ xor2 .x19 .x19 .x19 tailOff dbOff tailOff))) by simp,
    WP.block_append_iff]
  have x19₂ : s₂.gpr .x19 = W := hr₂.x19
  -- The address of the byte after the string.
  refine WP.of_runBlock ⟨_, by
    simp only [↓reduceIte, Nat.reduceLT, tailOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq]
    rfl, ?_⟩
  generalize hs₃ : ((s₂.write .x .x6 (s₂.gpr .x19 + s₂.gpr .x23)).write .x .x6
    (s₂.gpr .x19 + s₂.gpr .x23 + BitVec.ofNat 64 32)) = s₃
  have g₃ (r : Reg) (hr' : r ≠ .x6) : s₃.gpr r = s₂.gpr r := by rw [← hs₃]; simp [gpr_write, hr']
  have x6₃ : s₃.gpr .x6 + BitVec.ofNat 64 0 = W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L := by
    rw [← hs₃]
    simp only [gpr_write, ite_true, BitVec.setWidth_eq, x19₂, hr₂.x23, BitVec.add_zero]
    rw [BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 L), ← BitVec.add_assoc]
  have m₃ : s₃.mem = s₂.mem := by rw [← hs₃]; rfl
  have sp₃ : s₃.sp = s₂.sp := by rw [← hs₃]; rfl
  have rd₃ : s₃.rd = s₂.rd := by rw [← hs₃]; rfl
  have wr₃ : s₃.wr = s₂.wr := by rw [← hs₃]; rfl
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, m₄, g₄, sp₄, rd₄, wr₄⟩ := pad_ok s₃ x6₃
    (by rw [wr₃, hr₂.wr, Offset.add_add]; exact h.inW rfl (by omega))
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  rw [WP.block_append_iff]
  have x19₄ : s₄.gpr .x19 = W := by rw [g₄ _ (by decide), g₃ _ (by decide), x19₂]
  have rd₄' : s₄.rd = s₀.rd := by rw [rd₄, rd₃, hr₂.rd]
  have wr₄' : s₄.wr = s₀.wr := by rw [wr₄, wr₃, hr₂.wr]
  have inD (d : Nat) (hd : d + 8 ≤ 16) : InRegions (s₄.rd ++ s₄.wr) (W + BitVec.ofNat 64 (dOff + d)) 8 := by
    rw [← Offset.add_add, ← hD]; exact h.inRD rd₄' wr₄' hd
  obtain ⟨s₅, run₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := copy16_ok x19₄ (src := dOff) (dst := dbOff) (by decide) (by decide)
    (by simpa using inD 0 (by decide)) (inD 8 (by decide)) (h.inW wr₄' (by decide)) (h.inW wr₄' (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  rw [WP.block_append_iff]
  have x19₅ : s₅.gpr .x19 = W := by rw [g₅ _ (by decide), x19₄]
  have rd₅' : s₅.rd = s₀.rd := by rw [rd₅, rd₄']
  have wr₅' : s₅.wr = s₀.wr := by rw [wr₅, wr₄']
  obtain ⟨s₆, run₆, m₆, g₆, sp₆, rd₆, wr₆⟩ := dbl_ok s₅ x19₅ (src := dbOff) (dst := dbOff) (by decide) (by decide)
    (h.inRW rd₅' wr₅' (by decide)) (h.inRW rd₅' wr₅' (by decide)) (h.inW wr₅' (by decide))
    (h.inW wr₅' (by decide))
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  have x19₆ : s₆.gpr .x19 = W := by rw [g₆ _ (by decide) (by decide) (by decide) (by decide), x19₅]
  have rd₆' : s₆.rd = s₀.rd := by rw [rd₆, rd₅']
  have wr₆' : s₆.wr = s₀.wr := by rw [wr₆, wr₅']
  obtain ⟨s₇, run₇, m₇, g₇, sp₇, rd₇, wr₇⟩ := xor2_ok s₆ .x19 .x19 .x19 tailOff dbOff tailOff
    (P := W + BitVec.ofNat 64 32) (Q := W + BitVec.ofNat 64 144) (C := W + BitVec.ofNat 64 32)
    (by decide) (by decide) (by decide) (by rw [x19₆]) (by rw [x19₆, Offset.add_add])
    (by rw [x19₆]) (by rw [x19₆, Offset.add_add]) (by rw [x19₆]) (by rw [x19₆, Offset.add_add])
    ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    (h.inRW rd₆' wr₆' (by decide)) (by rw [Offset.add_add]; exact h.inRW rd₆' wr₆' (by decide))
    (h.inRW rd₆' wr₆' (by decide)) (by rw [Offset.add_add]; exact h.inRW rd₆' wr₆' (by decide))
    (h.inW wr₆' (by decide)) (by rw [Offset.add_add]; exact h.inW wr₆' (by decide))
  refine WP.of_runBlock ⟨s₇, by rw [xor2_eq]; exact run₇, ?_⟩
  -- The registers.
  have g (r : Reg) (hr' : r ∈ preserved) : s₇.gpr r = s.gpr r := by
    have n6 : r ≠ .x6 := by rintro rfl; revert hr'; decide
    have n9 : r ≠ .x9 := by rintro rfl; revert hr'; decide
    have n10 : r ≠ .x10 := by rintro rfl; revert hr'; decide
    have n11 : r ≠ .x11 := by rintro rfl; revert hr'; decide
    have n12 : r ≠ .x12 := by rintro rfl; revert hr'; decide
    rw [g₇ r n9 n10, g₆ r n9 n10 n11 n12, g₅ r n9, g₄ r n9, g₃ r n6, g₂ r hr', g₁ r hr']
  refine ⟨hr.keep' (fun r hr' => g r (dec_mem (by decide) hr')) (by rw [sp₇, sp₆, sp₅, sp₄, sp₃, h₂.sp, hr₁.sp, hr.sp])
    (by rw [rd₇, rd₆', hr.rd]) (by rw [wr₇, wr₆', hr.wr]), g, ?_, ?_⟩
  -- The memory, step by step.
  · have hlen : (Spec.Aes.bytesAt s₁.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have c32 (d n : Nat) (hd : d + n ≤ 16) :
        (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 d) n :=
      Offset.contains_base _ hd (by omega)
    have f₁ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s.mem s₁.mem := by rw [m₁]; exact Proof.Cmac.frame_store2 _ _ _
    have f₂ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₁.mem s₂.mem := by
      rw [h₂.mem]; exact writeBytes_frame _ _ _ (by rw [hlen]; simpa using c32 0 L (by omega))
    have f₄ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₃.mem s₄.mem := by
      rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c32 L 1 (by omega))
    have f₅ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₄.mem s₅.mem := by rw [m₅]; exact copyMem_frame _ _ _
    have f₆ : Frame [⟨W + BitVec.ofNat 64 144, 16⟩] s₅.mem s₆.mem := by rw [m₆]; exact dblMem_frame _ _ _ _
    have f₇ : Frame [⟨W + BitVec.ofNat 64 32, 16⟩] s₆.mem s₇.mem := by
      rw [m₇]; exact Proof.Cmac.xor2Mem_frame _ _ _ _
    have sub (rs : List Region) (hs : ∀ r ∈ rs, r ∈ tailRegions W) :
        ∀ r ∈ rs, ∃ r' ∈ tailRegions W, Region.Sub r r' :=
      fun r hr => ⟨r, hs r hr, fun _ h => h⟩
    rw [m₃] at f₄
    exact ((((((f₁.sub (sub _ (by simp))).trans (f₂.sub (sub _ (by simp)))).trans (f₄.sub (sub _ (by simp)))).trans
      (f₅.sub (sub _ (by simp)))).trans (f₆.sub (sub _ (by simp)))).trans (f₇.sub (sub _ (by simp))))
  · have hlen : (Spec.Aes.bytesAt s₁.mem P L).length = L := Proof.Cmac.bytesAt_length _ _ _
    have dWW (d n e k : Nat) (hs : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 2560) (he : e + k ≤ 2560) :
        (⟨W + BitVec.ofNat 64 d, n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 e, k⟩ :=
      Offset.disjoint W hs (by omega) (by omega)
    have e8 (d : Nat) : W + BitVec.ofNat 64 d + BitVec.ofNat 64 8 = W + BitVec.ofNat 64 (d + 8) :=
      Offset.add_add _ _ _
    have one (X Y : Region) (hd : X.Disjoint Y) : ∀ r ∈ [Y], X.Disjoint r := fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd
    rw [m₇, Proof.Cmac.xor2Mem_bytes _ (by rw [e8]; exact dWW 32 8 40 8 (by omega) (by omega) (by omega))
      (by rw [e8]; exact dWW 32 8 152 8 (by omega) (by omega) (by omega))]
    have t₆ : Spec.Aes.bytesAt s₆.mem (W + BitVec.ofNat 64 32) 16 =
        Spec.Aes.bytesAt s₄.mem (W + BitVec.ofNat 64 32) 16 := by
      rw [m₆, Proof.Cmac.bytesAt_frame (dblMem_frame _ _ _ _) (one _ _ (dWW 32 16 144 16 (by omega) (by omega)
        (by omega))) (by decide), m₅, Proof.Cmac.bytesAt_frame (copyMem_frame _ _ _)
        (one _ _ (dWW 32 16 144 16 (by omega) (by omega) (by omega))) (by decide)]
    have hz : Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 = Spec.Cmac.zeros 16 := by
      rw [m₁]; exact Proof.Cmac.zero2_bytes _ _
    have pad := Proof.Cmac.padded_bytes s₁.mem (W + BitVec.ofNat 64 32) (Spec.Aes.bytesAt s₁.mem P L)
      (by rw [hlen]; exact hL) hz
    rw [hlen] at pad
    have hP : Spec.Aes.bytesAt s₁.mem P L = Spec.Aes.bytesAt s.mem P L := by
      rw [m₁]; exact Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _)
        (one _ _ (h.p_w.sub_right (h.sW (by decide)))) (by have := h.lt; omega)
    have dD : (⟨D, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 32, 16⟩ := h.d_w.sub_right (h.sW (by decide))
    have c₄ : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32 + BitVec.ofNat 64 L) 1 :=
      Offset.contains_base (W + BitVec.ofNat 64 32) (d := L) (n := 1) (k := 16) (by omega) (by omega)
    have c₂ : (⟨W + BitVec.ofNat 64 32, 16⟩ : Region).Contains (W + BitVec.ofNat 64 32)
        (Spec.Aes.bytesAt s₁.mem P L).length := by
      rw [hlen]
      have := Offset.contains_base (W + BitVec.ofNat 64 32) (d := 0) (n := L) (k := 16) (by omega) (by omega)
      simpa using this
    have q₆ : Spec.Aes.bytesAt s₆.mem (W + BitVec.ofNat 64 144) 16 =
        Spec.Cmac.dbl 16 (Spec.Aes.bytesAt s.mem D 16) := by
      rw [m₆, dblMem_bytes, m₅, copyMem_bytes _ (by rw [← hD]; exact (h.d_w.sub_right (h.sW (by decide))).symm),
        ← hD, m₄, Proof.Cmac.bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₄)
          (one _ _ dD) (by decide), m₃, h₂.mem,
        Proof.Cmac.bytesAt_frame (writeBytes_frame _ _ _ c₂) (one _ _ dD) (by decide),
        m₁, Proof.Cmac.zero2, Proof.Cmac.bytesAt_frame (Proof.Cmac.frame_store2 _ _ _) (one _ _ dD) (by decide)]
    rw [t₆, m₄, m₃, h₂.mem, pad, hP, q₆, Spec.Siv.pad, Proof.Cmac.bytesAt_length,
      show 16 - L - 1 = 15 - L by omega]
    rfl

/-! ## The whole short case -/

/-- The regions `finish` writes: the output, the tail, `dbl(D)` and the
working space of the functions called. -/
abbrev finRegions (W : Addr) (out : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 32, 32⟩, ⟨W + BitVec.ofNat 64 144, 16⟩,
    ⟨W + BitVec.ofNat 64 256, 2176⟩]

/-- What `finish` leaves: S2V's end, from `D` and the data, at `W + out`. -/
structure FinPost (s₀ : State) (C D P W : Addr) (R L out : Nat) (s s' : State) : Prop where
  regs : Regs s₀ C D P W R L s'
  hold : Hold2 s s'
  frame : Frame (finRegions W out) s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W + BitVec.ofNat 64 out) 16 =
    Spec.Siv.s2vFinish (Spec.Siv.ctxMac s.mem C R) (Spec.Aes.bytesAt s.mem D 16) (Spec.Aes.bytesAt s.mem P L)

theorem macPre_ok (h : Env s₀ C D P W R L) {s : State} (hr : Regs s₀ C D P W R L s) {out : Nat}
    (hout : out = 0 ∨ out = 112) :
    ∃ s', runBlock isa (shortArgs out) s = some s' ∧ Regs s₀ C D P W R L s' ∧
      (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧
      FArgs s' C (W + BitVec.ofNat 64 out) (W + BitVec.ofNat 64 32) (W + BitVec.ofNat 64 256) 16 R ∧
      s'.mem = Proof.Cmac.zero2 s.mem (W + BitVec.ofNat 64 out) := by
  obtain ⟨s₁, run₁, m₁, g₁, sp₁, rd₁, wr₁⟩ := h.zero16_ok hr.x19 hr.wr (d := out) (by omega) (by omega)
  have x19₁ : s₁.gpr .x19 = W := by rw [g₁ _ (by decide), hr.x19]
  have hout' : out < 4096 := by omega
  refine ⟨_, by
    rw [shortArgs, runBlock_append, run₁, Option.bind_some]
    simp only [reduceCtorEq, ↓reduceIte, Nat.reduceLT, Nat.reduceMul, mov, tailOff, csOff, runBlock_cons, runStep_some, runBlock_nil, exec,
      Size.bits, State.read, gpr_write, BitVec.setWidth_eq, hout']
    rfl, ?_⟩
  have g (r : Reg) (hr' : r ∈ preserved) : ((((((s₁.write .x .x0 (s₁.gpr .x20 + BitVec.ofNat 64 0)).write .x .x1
      (s₁.gpr .x21 + BitVec.ofNat 64 0)).write .x .x2 (s₁.gpr .x19 + BitVec.ofNat 64 out)).write .x .x3
      (s₁.gpr .x19 + BitVec.ofNat 64 32)).write .x .x4 (BitVec.setWidth 64 (16 : BitVec 16) <<< (16 * 0))).write
      .x .x5 (s₁.gpr .x19 + BitVec.ofNat 64 256)).gpr r = s.gpr r := by
    rw [← g₁ r (by rintro rfl; revert hr'; decide)]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [gpr_write]
  have hr' := hr.keep' (fun r hr' => g r (dec_mem (by decide) hr')) sp₁ rd₁ wr₁
  refine ⟨hr', g, h.fargs hr'.rd hr'.wr (by omega) (h.srcWork (by omega) (by decide) (by omega)) (by decide)
    (by simp [gpr_write, g₁ _ (by decide : Reg.x20 ≠ .x9), hr.x20])
    (by simp [gpr_write, g₁ _ (by decide : Reg.x21 ≠ .x9), hr.x21])
    (by simp [gpr_write, x19₁]) (by simp [gpr_write, x19₁]) (by simp [gpr_write])
    (by simp [gpr_write, x19₁]), by simp [mem_write, m₁]⟩

theorem finishShort_wp (v : Proof.CmacAes.AArch64.UpdateImpl) (h : Env s₀ C D P W R L) {s : State}
    (hr : Regs s₀ C D P W R L s) (hL : L < 16) {out : Nat} (hout : out = 0 ∨ out = 112) :
    WP isa (.seq shortTail (shortMac v.ctr.callee v.ctr.suffix out)) s (FinPost s₀ C D P W R L out s) := by
  have hwW := h.wW
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  refine WP.seq (WP.mono (shortTail_wp h hr hL) fun s₁ ⟨hr₁, g₁, f₁, t₁⟩ => ?_)
  obtain ⟨s₂, run₂, hr₂, g₂, fa₂, m₂⟩ := macPre_ok h hr₁ hout
  refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
  refine WP.mono (finr_call v.ctr _ fa₂) fun s₃ h₃ => ?_
  have f₂ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩] s₁.mem s₂.mem := by
    rw [m₂]; exact Proof.Cmac.frame_store2 _ _ _
  have f₃ : Frame [⟨W + BitVec.ofNat 64 out, 16⟩, ⟨W + BitVec.ofNat 64 256, 2176⟩] s₂.mem s₃.mem := h₃.frame
  have f₁' : Frame (finRegions W out) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 32, 32⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
  have f₂₃ : Frame (finRegions W out) s₁.mem s₃.mem :=
    (f₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩).trans (f₃.sub fun r hr => ⟨r, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl <;> simp,
      fun _ h => h⟩)
  refine ⟨hr₂.keep h₃.saved h₃.sp h₃.rd h₃.wr,
    Hold2.of fun r hr _ _ h30 => by rw [h₃.saved r hr h30, g₂ r hr, g₁ r hr], f₁'.trans f₂₃, ?_⟩
  -- What the call reads, from the start.
  have fs : Frame (finRegions W out) s.mem s₂.mem :=
    f₁'.trans (f₂.sub fun r hr => ⟨r, by simp_all, fun _ h => h⟩)
  have dC {d n : Nat} (hd : d + n ≤ 512) :
      Spec.Aes.bytesAt s₂.mem (C + BitVec.ofNat 64 d) n = Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 d) n :=
    Proof.Cmac.bytesAt_frame fs (fun r hr => by
      have hc := h.c_w.sub_left (h.sC hd)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hc.sub_right (h.sW (by omega))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))
      · exact hc.sub_right (h.sW (by decide))) (by omega)
  have sch := dC (d := 0) (n := 16 * (R + 1)) (by omega)
  have k1 := dC (d := 240) (n := 16) (by decide)
  have k2 := dC (d := 256) (n := 16) (by decide)
  rw [k0] at sch
  have tl : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 32) 16 = Spec.Aes.bytesAt s₁.mem (W + BitVec.ofNat 64 32) 16 :=
    Proof.Cmac.bytesAt_frame f₂ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Offset.disjoint W (by omega) (by omega) (by omega))
      (by decide)
  have hz : Spec.Aes.bytesAt s₂.mem (W + BitVec.ofNat 64 out) 16 = Spec.Cmac.zeros 16 := by
    rw [m₂]; exact Proof.Cmac.zero2_bytes _ _
  have hlen : (Spec.Aes.bytesAt s.mem P L).length < 16 := by rw [Proof.Cmac.bytesAt_length]; exact hL
  have lk1 : (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 240) 16).length = 16 := Proof.Cmac.bytesAt_length _ _ _
  have lk2 : (Spec.Aes.bytesAt s.mem (C + BitVec.ofNat 64 256) 16).length = 16 := Proof.Cmac.bytesAt_length _ _ _
  have lm : (Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16))
      (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L))).length = 16 := by
    rw [Siv.length_xor, Siv.length_pad hlen, Spec.Siv.dbl, Proof.Cmac.dbl_length (Proof.Cmac.bytesAt_length _ _ _)]
    rfl
  have split := Siv.cmacWith_split (Spec.Siv.schedCiph s.mem C R) (Spec.Aes.bytesAt s.mem (C + 240) 16)
    (Spec.Aes.bytesAt s.mem (C + 256) 16) (msg := [])
    (last := Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)))
    rfl (by omega) (Or.inl rfl)
  rw [List.nil_append] at split
  have ht : Spec.Siv.xor (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) =
      Spec.Siv.xor (Spec.Siv.dbl (Spec.Aes.bytesAt s.mem D 16)) (Spec.Siv.pad (Spec.Aes.bytesAt s.mem P L)) := by
    rw [Siv.xor_eq, Siv.xor_eq, Proof.Cmac.xor_comm]
  rw [h₃.out, mn, sch, k1, k2, tl, t₁, hz, Siv.s2vFinish_short _ _ hlen, Spec.Siv.ctxMac, split,
    Proof.AesSiv.chain_blocks_nil, Proof.AesSiv.xor_zeros (Proof.AesSiv.length_lastBlock lk1 lk2 (by rw [ht]; omega)),
    Proof.Cmac.xor_comm (Spec.Cmac.zeros 16),
    Proof.AesSiv.xor_zeros (Proof.AesSiv.length_lastBlock (Proof.Cmac.bytesAt_length _ _ _)
      (Proof.Cmac.bytesAt_length _ _ _) (by omega)), ht]
  rfl

end VG.Proof.AesSiv.AArch64
