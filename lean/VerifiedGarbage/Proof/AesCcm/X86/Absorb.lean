import VerifiedGarbage.Proof.AesCcm.X86.Blocks

/-!
# AES-CCM on x86: a buffer padded, chained (`absorbPad y`)

Untrusted: everything here is checked by Lean. `absorbPad y` chains the
`len` bytes at `P` (kept at `W + dO`, `len` at `W + nO`), padded with zeros
to whole blocks, into the MAC state at `W + y`: its whole blocks in one call
of `vg_cmac_aes_update` (`absorbWhole_ok`), then its last `len mod 16` bytes
copied into the zeroed block `B` (`absorbTail_ok`); together, the blocks of
the padded string (`absorbPad_ok`, `Proof.AesCcm.blocks_pad16`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86 VG.WriteBytes
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86 (Ctr32Impl)
open VG.Impl.AesGcm.X86 (at_ imm slot copyLoop zero4 splitWhole dO nO)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 slotv zero4_fold length_bytesAt WEnv padLoop_ok shr4 and15
  ofNat_sub32 and_self_beq32)

/-! ## What the pieces write -/

/-- What chaining into `W + y` writes: the state, `B`, `[240, 2560)` (the
arguments of the piece running and the working space of the functions
called) and the stack below `SP`. -/
abbrev macR (W SP : BitVec 32) (y : Nat) : List Region :=
  [⟨w64 W + BitVec.ofNat 64 y, 16⟩, ⟨w64 W + BitVec.ofNat 64 32, 16⟩, wC W, below SP 56]

theorem sub_mac {W SP : BitVec 32} {y : Nat} {r : Region} (hr : r ∈ macR W SP y) :
    ∃ r' ∈ macR W SP y, Region.Sub r r' := ⟨r, hr, fun _ h => h⟩

/-- `[o, o + 4)` of `W`, for `112 ≤ o` and `o + 4 ≤ 240`, is kept. -/
theorem slot_kept {K W SP : BitVec 32} (L : Lay K W SP) {y : Nat} (hy : y = 0 ∨ y = 96) {m m' : Mem}
    (hf : Frame (macR W SP y) m m') {o : Nat} (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) : slotv m' W o = slotv m W o :=
  hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rcases hy with rfl | rfl
      · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
      · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide)
    · exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
    · exact (L.stk_w' (by omega_arith)).symm) (by decide)

/-- A buffer missing `W` and the stack below `SP` keeps its bytes. -/
theorem buf_kept {W SP : BitVec 32} {s : State} {P : BitVec 32} {len : Nat} (hP : Buf W SP s P len) {y : Nat}
    (hy : y + 16 ≤ 2560) {m m' : Mem} (hf : Frame (macR W SP y) m m') :
    bytesAt m' (w64 P) len = bytesAt m (w64 P) len :=
  Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hP.w.sub_right (Lay.wSub hy)
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.w.sub_right (Lay.wSub (by decide))
    · exact hP.stk.symm) (by have := hP.lt; omega_arith)

theorem k_macR {K W SP : BitVec 32} (L : Lay K W SP) {y : Nat} (hy : y + 16 ≤ 2560) :
    ∀ r ∈ macR W SP y, (⟨w64 K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact L.k_w.sub_right (Lay.wSub hy)
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.k_w.sub_right (Lay.wSub (by decide))
  · exact L.stk_k.symm

/-- The cipher of a key schedule outside a frame's regions. -/
theorem ctxCiph_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {K : BitVec 32}
    (hd : ∀ r ∈ rs, (⟨w64 K, 240⟩ : Region).Disjoint r) {R : Nat} (hR : 16 * (R + 1) ≤ 240) :
    Spec.Ccm.ctxCiph m' (w64 K) R = Spec.Ccm.ctxCiph m (w64 K) R := by
  unfold Spec.Ccm.ctxCiph
  rw [Proof.AesGcm.X86.bytesAt_frame hf (fun r hr => (hd r hr).sub_left (Region.sub_prefix hR)) (by omega_arith)]

/-- What `absorbPad`'s pieces keep: the environment, and what they write. -/
structure Absorbed (K W SP : BitVec 32) (s : State) (y : Nat) (Y : List Byte) (s' : State) : Prop where
  env : Env K W SP s'
  frame : Frame (macR W SP y) s.mem s'.mem
  out : bytesAt s'.mem (w64 W + BitVec.ofNat 64 y) 16 = Y
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-! ## Splitting off the whole blocks -/

/-- `splitWhole`, from the slots `dO = P` and `nO = r`: `ebx = P`,
`edi = r / 16` whole blocks, and the slots the rest; ZF is set if there are
none. -/
theorem split_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {P : BitVec 32} {r : Nat}
    (hd : slotv s.mem W dO = P) (hn : slotv s.mem W nO = BitVec.ofNat 32 r) (hr : r < 2 ^ 32) :
    ∃ s', runBlock isa splitWhole s = some s' ∧ s'.gpr .ebx = P ∧ s'.gpr .edi = BitVec.ofNat 32 (r / 16) ∧
      s'.zf = some (decide (r / 16 = 0)) ∧ s'.gpr .ebp = W ∧ s'.gpr .esp = SP ∧
      s'.mem = (s.mem.writeW (w64 W + BitVec.ofNat 64 nO) (BitVec.ofNat 32 (r % 16))).writeW
        (w64 W + BitVec.ofNat 64 dO) (P + BitVec.ofNat 32 (16 * (r / 16))) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hsh := shr4 hr
  have hand := and15 (BitVec.ofNat 32 r)
  rw [toNat_ofNat32 hr] at hand
  have h16 : BitVec.ofNat 32 r - BitVec.ofNat 32 (r % 16) = BitVec.ofNat 32 (16 * (r / 16)) := by
    rw [ofNat_sub32 (Nat.mod_le _ _) hr]; congr 1; omega_arith
  refine ⟨_, by crun [splitWhole, E.ebp, L.aW, E.perm.wW, E.perm.wR, hd, hn], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cregs [hd]
  · cregs [hn, hsh]
  · cmems [hn, hsh]; rw [and_self_beq32 (by omega_arith)]
  · cregs [E.ebp]
  · cregs [E.esp]
  · cmems [hn, hd, hsh, hand, h16]
    rw [BitVec.add_comm (BitVec.ofNat 32 (16 * (r / 16)))]
  all_goals cmems []

/-- The arguments of the call chaining the whole blocks. -/
theorem wholeArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : Lay K W SP) (E₁ : Env K W SP s₁) {R : Nat}
    (hK₁ : slotv s₁.mem W ctxO = K) (hR₁ : slotv s₁.mem W roundsO = BitVec.ofNat 32 R) {P : BitVec 32} {b : Nat}
    (hbx : s₁.gpr .ebx = P) (hdi : s₁.gpr .edi = BitVec.ofNat 32 b) (y : Nat) :
    ∃ s₂, runBlock isa (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr) s₁ = some s₂ ∧
      s₂.mem = s₁.mem ∧ s₂.gpr .eax = K ∧ s₂.gpr .ecx = BitVec.ofNat 32 R ∧ s₂.gpr .edx = W + BitVec.ofNat 32 y ∧
      s₂.gpr .ebx = P ∧ s₂.gpr .esi = BitVec.ofNat 32 b ∧
      s₂.gpr .edi = W + BitVec.ofNat 32 384 ∧ s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
  have hbp := E₁.ebp
  refine ⟨_, by crun [keyArgs, updScr, hbp, L.aW, E₁.perm.wR, hK₁, hR₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cregs [hK₁]
  · cregs [hR₁]
  · cregs [hbp]
  · cregs [hbx]
  · cregs [hdi]
  · cregs [hbp]
  · cregs [hbp]
  · cregs [E₁.esp]
  all_goals rfl

/-- The slots `splitWhole` does not write are kept. -/
theorem split_kept {W : BitVec 32} {m m' : Mem} {a b : BitVec 32}
    (hm : m' = (m.writeW (w64 W + BitVec.ofNat 64 nO) a).writeW (w64 W + BitVec.ofNat 64 dO) b) {o : Nat}
    (h₁ : 112 ≤ o) (h₂ : o + 4 ≤ 240) : slotv m' W o = slotv m W o := by
  have f₁ : Frame [wC W] m m' := by
    rw [hm]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  exact f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide))
    (by decide)

/-! ## The whole blocks -/

/-- The whole blocks of the string at `P` (kept at `W + dO`, its length at
`W + nO`), chained into `W + y`; `dO` and `nO` then the rest. -/
theorem absorbWhole_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hP : 0 < len → Buf W SP s P len)
    (hl : len < 2 ^ 32) (hd : slotv s.mem W dO = P) (hn : slotv s.mem W nO = BitVec.ofNat 32 len) :
    WP isa (.seq (.block splitWhole)
        (.ite .e (.block []) (.seq (.block (keyArgs y ++ ([.mov .esi (.reg .edi)] : List Instr) ++ updScr)) (updCall v.callee v.suffix))))
      s fun s' => Absorbed K W SP s y
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          (Spec.Cmac.blocks 16 ((bytesAt s.mem (w64 P) len).take (16 * (len / 16))))) s' ∧
        slotv s'.mem W dO = P + BitVec.ofNat 32 (16 * (len / 16)) ∧
        slotv s'.mem W nO = BitVec.ofNat 32 (len % 16) := by
  obtain ⟨s₁, run₁, hbx, hdi, hzf, hbp, hsp, hm₁, hrd₁, hwr₁⟩ := split_ok L E hd hn hl
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  have f₁ : Frame [wC W] s.mem s₁.mem := by
    rw [hm₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 276) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains (w64 W) (d := 272) (n := 4) (e := 240) (k := 2320) (by decide) (by decide) (by decide))
  have k₁ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₁.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
    f₁.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide))
      (by decide)
  have hd₁ : slotv s₁.mem W dO = P + BitVec.ofNat 32 (16 * (len / 16)) := by
    rw [hm₁]; exact Mem.readW_writeW_self32 _ _ _
  have hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 (len % 16) := by
    rw [hm₁, slotv, Proof.AesGcm.X86.readW_writeW_off _ _ _ (by decide) (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have hY₁ : bytesAt s₁.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 :=
    Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rcases hy with rfl | rfl <;> exact Lay.w_w (.inl (by decide)) (by decide) (by decide)) (by decide)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hc₁ : Spec.Ccm.ctxCiph s₁.mem (w64 K) R = Spec.Ccm.ctxCiph s.mem (w64 K) R :=
    ctxCiph_frame f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb
  have fm : Frame (macR W SP y) s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
  refine WP.ite (decide (len / 16 = 0)) (eval_e hzf) (fun ht => ?_) (fun hf => ?_)
  · have h0 : len / 16 = 0 := of_decide_eq_true ht
    refine WP.of_runBlock ⟨s₁, rfl, ⟨E₁, fm, ?_, hrd₁, hwr₁⟩, hd₁, hn₁⟩
    rw [hY₁, h0, Nat.mul_zero, List.take_zero]; rfl
  · have h0 : len / 16 ≠ 0 := of_decide_eq_false hf
    have hP := hP (by omega_arith)
    have hP₁ : bytesAt s₁.mem (w64 P) len = bytesAt s.mem (w64 P) len :=
      Proof.AesGcm.X86.bytesAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hP.w.sub_right (Lay.wSub (by decide)))
        (by have := hP.lt; omega_arith)
    obtain ⟨s₂, run₂, hm₂, hax, hcx, hdx, hbx₂, hsi, hdi₂, hbp₂, hsp₂, hrd₂, hwr₂⟩ :=
      wholeArgs_ok L E₁ (by rw [k₁ _ (by decide) (by decide)]; exact hK) (by rw [k₁ _ (by decide) (by decide)]; exact hRo)
        hbx hdi y
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have E₂ : Env K W SP s₂ := E₁.keep (by rw [hbp₂, hbp]) (by rw [hsp₂, hsp]) hrd₂ hwr₂
    have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
    have hq := srcBuf ((hP.take hb).of_eq (s' := s₂) (by rw [hrd₂, hrd₁]) (by rw [hwr₂, hwr₁]))
    have hqy : (⟨w64 P, 16 * (len / 16)⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 y, 16⟩ :=
      (hP.w.sub_left (Region.sub_prefix hb)).sub_right (Lay.wSub (by omega_arith))
    refine WP.mono (updCall_ok v L E₂ hR (by omega_arith) hq hqy (by omega_arith) hax hcx hdx hbx₂ hsi hdi₂)
      fun s₃ ⟨E₃, rd₃, wr₃, _, f₃, o₃⟩ => ⟨⟨E₃, fm.trans ?_, ?_, by rw [rd₃, hrd₂, hrd₁], by rw [wr₃, hwr₂, hwr₁]⟩, ?_, ?_⟩
    · rw [← hm₂]
      exact f₃.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_mac (by simp)
        · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact sub_mac (by simp)
    · rw [o₃, Proof.Cmac.Stream.blocksAt_eq, hm₂, hY₁, hc₁, Proof.AesCcm.bytesAt_prefix _ _ hb, hP₁]
    · have k : slotv s₃.mem W dO = slotv s₂.mem W dO :=
        f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 dO, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w' (by decide)).symm) (by decide)
      rw [k, hm₂, hd₁]
    · have k : slotv s₃.mem W nO = slotv s₂.mem W nO :=
        f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 nO, 4⟩) (Region.contains_self _ _) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · rcases hy with rfl | rfl <;> exact Lay.w_w (.inr (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact (L.stk_w' (by decide)).symm) (by decide)
      rw [k, hm₂, hn₁]

/-- `[mov ecx [nO], test ecx ecx]`: ZF is whether `nO` holds 0. -/
theorem testN_ok {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {r : Nat} (hr : r < 2 ^ 32)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 r) :
    ∃ s₁, runBlock isa [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)] s = some s₁ ∧ s₁.mem = s.mem ∧
      s₁.zf = some (decide (r = 0)) ∧ s₁.gpr .ebp = W ∧ s₁.gpr .esp = SP ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
  refine ⟨_, by crun [E.ebp, L.aW, E.perm.wR, hn], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · cmems [hn]; rw [and_self_beq32 hr]
  · cregs [E.ebp]
  · cregs [E.esp]
  all_goals cmems []

/-- The arguments of the copy of the last bytes into the zeroed `B`. -/
theorem tailArgs_ok {K W SP : BitVec 32} {s₁ : State} (L : Lay K W SP) (E₁ : Env K W SP s₁) {Q : BitVec 32} {t : Nat}
    (hd₁ : slotv s₁.mem W dO = Q) (hn₁ : slotv s₁.mem W nO = BitVec.ofNat 32 t) :
    ∃ s₂, runBlock isa
        (zero4 blkO ++ ([.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO), .mov .ecx (slot nO)] : List Instr))
          s₁ = some s₂ ∧ s₂.mem = Cmac.zero4 s₁.mem (w64 W + BitVec.ofNat 64 32) ∧
        s₂.gpr .edi = Q ∧ s₂.gpr .edx = W + BitVec.ofNat 32 32 ∧ s₂.gpr .ecx = BitVec.ofNat 32 t ∧
        s₂.gpr .ebp = W ∧ s₂.gpr .esp = SP ∧ s₂.rd = s₁.rd ∧ s₂.wr = s₁.wr := by
  have hbp := E₁.ebp
  have hz := zero4_fold s₁.mem W 32
  simp only [Nat.reduceAdd] at hz
  refine ⟨_, by crun [zero4, hbp, L.aW, E₁.perm.wW, E₁.perm.wR, hd₁, hn₁], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cmems [hz]
  · cregs [hd₁]
  · cregs [hbp]
  · cregs [hn₁]
  · cregs [hbp]
  · cregs [E₁.esp]
  all_goals cmems []

/-! ## The last bytes -/

/-- The last `t < 16` bytes, at `Q` (kept at `W + dO`, `t` at `W + nO`),
padded with zeros in `B` and chained into `W + y`, if there are any. -/
theorem absorbTail_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {Q : BitVec 32} {t : Nat} (ht : t < 16) (hd : slotv s.mem W dO = Q)
    (hn : slotv s.mem W nO = BitVec.ofNat 32 t) (hQ : 0 < t → Buf W SP s Q t) :
    WP isa (.seq (.block [.mov .ecx (slot nO), .alu .test .ecx (.reg .ecx)])
        (.ite .e (.block [])
          (.seq (.block (zero4 blkO ++ ([.mov .edi (slot dO), .mov .edx (.reg .ebp), .alu .add .edx (imm blkO),
              .mov .ecx (slot nO)] : List Instr)))
            (.seq copyLoop (updBlock v.callee v.suffix y)))))
      s (Absorbed K W SP s y
        (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
          (if t = 0 then [] else [bytesAt s.mem (w64 Q) t ++ Spec.Ccm.zeros (16 - t)]))) := by
  obtain ⟨s₁, run₁, hm₁, hzf, hbp, hsp, hrd₁, hwr₁⟩ := testN_ok L E (r := t) (by omega_arith) hn
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  have E₁ : Env K W SP s₁ := E.keep (by rw [hbp, E.ebp]) (by rw [hsp, E.esp]) hrd₁ hwr₁
  refine WP.ite (decide (t = 0)) (eval_e hzf) (fun h => ?_) (fun h => ?_)
  · have h0 : t = 0 := of_decide_eq_true h
    refine WP.of_runBlock ⟨s₁, rfl, E₁, by rw [hm₁]; exact Frame.refl _ _, ?_, hrd₁, hwr₁⟩
    simp only [hm₁, h0, ↓reduceIte]; rfl
  · have h0 : t ≠ 0 := of_decide_eq_false h
    have hB := hQ (by omega_arith)
    obtain ⟨s₂, run₂, hm₂, hdi, hdx, hcx, hbp₂, hsp₂, hrd₂, hwr₂⟩ :=
      tailArgs_ok L E₁ (Q := Q) (t := t) (by rw [hm₁]; exact hd) (by rw [hm₁]; exact hn)
    rw [hm₁] at hm₂
    refine WP.seq (WP.of_runBlock ⟨s₂, run₂, ?_⟩)
    have he : WEnv W s₂ := ⟨hbp₂, by rw [hwr₂, hwr₁]; exact E.perm.w, L.fw⟩
    have sd : (⟨w64 Q, t⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 32, 16⟩ := hB.w.sub_right (Lay.wSub (by decide))
    refine WP.seq (WP.mono (padLoop_ok (S := Q) (d := 32) (t := t) (m := s.mem) he hm₂ hdi hdx hcx (by omega_arith)
      (by omega_arith) (by rw [hrd₂, hwr₂, hrd₁, hwr₁]; exact hB.rd) hB.wrap sd (by decide))
      fun s₃ ⟨b₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
    have E₃ : Env K W SP s₃ := ⟨by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hbp₂],
      by rw [g₃ _ (by decide) (by decide) (by decide) (by decide), hsp₂],
      E.perm.of_eq (by rw [rd₃, hrd₂, hrd₁]) (by rw [wr₃, hwr₂, hwr₁])⟩
    have k₃ : ∀ o, 112 ≤ o → o + 4 ≤ 240 → slotv s₃.mem W o = slotv s.mem W o := fun o h₁ h₂ =>
      f₃.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact Lay.w_w (.inr (by omega_arith)) (by omega_arith) (by decide))
        (by decide)
    have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
    refine WP.mono (updBlock_ok v L E₃ hR (by rw [k₃ _ (by decide) (by decide)]; exact hK)
      (by rw [k₃ _ (by decide) (by decide)]; exact hRo) hy)
      fun s₄ ⟨E₄, rd₄, wr₄, f₄, o₄⟩ => ⟨E₄, ?_, ?_, by rw [rd₄, rd₃, hrd₂, hrd₁], by rw [wr₄, wr₃, hwr₂, hwr₁]⟩
    · refine (f₃.sub fun r hr => ?_).trans (f₄.sub fun r hr => ?_)
      · simp only [List.mem_singleton] at hr; subst hr; exact sub_mac (by simp)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact sub_mac (by simp)
        · exact ⟨wC W, by simp, Offset.sub _ (by decide) (by decide)⟩
        · exact sub_mac (by simp)
    · have hY₃ : bytesAt s₃.mem (w64 W + BitVec.ofNat 64 y) 16 = bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16 :=
        Proof.AesGcm.X86.bytesAt_frame f₃ (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          rcases hy with rfl | rfl
          · exact Lay.w_w (.inl (by decide)) (by decide) (by decide)
          · exact Lay.w_w (.inr (by decide)) (by decide) (by decide)) (by decide)
      rw [o₄, hY₃, b₃, ctxCiph_frame f₃ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.k_w.sub_right (Lay.wSub (by decide))) hRb]
      simp only [h0, ↓reduceIte]
      rfl

/-! ## The padded string -/

/-- The `len` bytes at `P` (kept at `W + dO`, `len` at `W + nO`), padded with
zeros to whole blocks, chained into the MAC state at `W + y`. -/
theorem absorbPad_ok (v : Ctr32Impl) {K W SP : BitVec 32} {s : State} (L : Lay K W SP) (E : Env K W SP s) {R : Nat}
    (hR : R = 10 ∨ R = 12 ∨ R = 14) (hK : slotv s.mem W ctxO = K) (hRo : slotv s.mem W roundsO = BitVec.ofNat 32 R)
    {y : Nat} (hy : y = 0 ∨ y = 96) {P : BitVec 32} {len : Nat} (hP : 0 < len → Buf W SP s P len)
    (hl : len < 2 ^ 32) (hd : slotv s.mem W dO = P) (hn : slotv s.mem W nO = BitVec.ofNat 32 len) :
    WP isa (absorbPad v.callee v.suffix y) s (Absorbed K W SP s y
      (Spec.Cmac.chain (Spec.Ccm.ctxCiph s.mem (w64 K) R) (bytesAt s.mem (w64 W + BitVec.ofNat 64 y) 16)
        (Spec.Cmac.blocks 16 (Spec.Ccm.pad16 (bytesAt s.mem (w64 P) len))))) := by
  refine seq_assoc (WP.seq (WP.mono (absorbWhole_ok v L E hR hK hRo hy hP hl hd hn) fun s₁ ⟨A₁, hd₁, hn₁⟩ => ?_))
  have hRb : 16 * (R + 1) ≤ 240 := by rcases hR with rfl | rfl | rfl <;> decide
  have hb : 16 * (len / 16) ≤ len := Nat.mul_div_le len 16
  have hQ : 0 < len % 16 → Buf W SP s₁ (P + BitVec.ofNat 32 (16 * (len / 16))) (len % 16) := fun h => by
    have hP := hP (by omega_arith)
    have := (hP.drop hb (by have := hP.wrap; omega_arith)).of_eq A₁.rd A₁.wr
    rwa [show len - 16 * (len / 16) = len % 16 by omega_arith] at this
  refine WP.mono (absorbTail_ok v L A₁.env hR (by rw [slot_kept L hy A₁.frame (by decide) (by decide)]; exact hK)
    (by rw [slot_kept L hy A₁.frame (by decide) (by decide)]; exact hRo) hy (Nat.mod_lt _ (by decide)) hd₁ hn₁ hQ)
    fun s₂ A₂ => ⟨A₂.env, A₁.frame.trans A₂.frame, ?_, A₂.rd.trans A₁.rd, A₂.wr.trans A₁.wr⟩
  rw [A₂.out, A₁.out, ctxCiph_frame A₁.frame (k_macR L (by omega_arith)) hRb, ← Proof.Cmac.chain_append,
    Proof.AesCcm.blocks_pad16, length_bytesAt]
  congr 2
  by_cases h0 : len % 16 = 0
  · simp only [h0, ↓reduceIte]
  · simp only [h0, ↓reduceIte, List.cons.injEq, and_true]
    have hP := hP (by omega_arith)
    have hw : P.toNat + 16 * (len / 16) < 2 ^ 32 := by have := hP.wrap; omega_arith
    have e : bytesAt s₁.mem (w64 (P + BitVec.ofNat 32 (16 * (len / 16)))) (len % 16) =
        (bytesAt s.mem (w64 P) len).drop (16 * (len / 16)) := by
      rw [show len % 16 = len - 16 * (len / 16) by omega_arith, buf_kept (hP.drop hb hw) (by omega_arith) A₁.frame, Buf.ptr hw,
        Proof.AesCcm.bytesAt_suffix _ _ hb]
    rw [e]

end VG.Proof.AesCcm.X86
