import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.EncEM

/-!
# RSAES-PKCS1-v1_5 encryption on x86-64: up to the call

From the frame's push, the first four pieces (`setup`, `psLoop`, `sep`,
`msgCopy`) leave the slots, the call's stack arguments, the zero test of
`PS` and `EM = 0x00 ‖ 0x02 ‖ PS ‖ 0x00 ‖ M` in the frame (`PreCall`,
`em_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.X86_64

open VG VG.X86_64 VG.Impl.RsaPkcs1Enc.X86_64.Encrypt
open VG.Proof.MlKem.X86_64 VG.Proof.Bignum.X86_64

/-- The message, the padding string and the modulus' length of an entry
state. -/
abbrev msgB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 0) (stackArg s 1).toNat
abbrev psB (s : State) : List Byte := Spec.Rsa.bytesAt s.mem (stackArg s 2) (stackArg s 3).toNat
abbrev kOf (s : State) : Nat := (s.gpr .rcx).toNat

/-- The slots and the call's stack arguments, in memory `m`. -/
structure Slots (s : State) (m : Mem) : Prop where
  sOut : word m (fb s) oOut = s.gpr .rdi
  sN : word m (fb s) oN = s.gpr .rdx
  sK : word m (fb s) oK = s.gpr .rcx
  sE : word m (fb s) oE = s.gpr .r8
  sEl : word m (fb s) oEl = s.gpr .r9
  a0 : m.readW (fb s) 64 = off (fb s) oEM
  a1 : word m (fb s) 8 = s.gpr .rcx
  a2 : word m (fb s) 16 = stackArg s 4
  a3 : word m (fb s) 24 = stackArg s 5

/-- Changes from offset `oZ` on keep the slots. -/
theorem Slots.outside {s : State} {m m' : Mem} (h : Slots s m) {o n : Nat} (ho : oZ ≤ o)
    (h' : Outside (fb s) o n m m') : Slots s m' := by
  have w : ∀ {d : Nat}, d + 8 ≤ oZ → word m' (fb s) d = word m (fb s) d := fun hd =>
    h'.word (.inl (by omega)) (by unfold oZ at hd; omega)
  refine ⟨(w (by decide)).trans h.sOut, (w (by decide)).trans h.sN, (w (by decide)).trans h.sK,
    (w (by decide)).trans h.sE, (w (by decide)).trans h.sEl, ?_, (w (by decide)).trans h.a1,
    (w (by decide)).trans h.a2, (w (by decide)).trans h.a3⟩
  have := w (d := 0) (by decide)
  simp only [Bignum.X86_64.word, off_zero] at this
  rw [this]; exact h.a0

theorem setupMem_slots (s : State) : Slots s (setupMem s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := first | decide | omega) only [setupMem, word_ww, word_wb, word_ww0,
      word0_ww, word0_wb, Mem.readW_writeW_self64]

theorem setupMem_outside (s : State) : Outside (fb s) 0 frameBytes s.mem (setupMem s) := by
  unfold setupMem
  refine Outside.wb (Outside.wb (Outside.ww (Outside.ww (Outside.ww (Outside.ww0 (Outside.ww (Outside.ww
    (Outside.ww (Outside.ww (Outside.ww (Outside.refl _ _ _ _) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_)
    _ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_) _ ?_ ?_ ?_ <;> decide

theorem setupMem_b0 (s : State) : byte (setupMem s) (fb s) oEM = 0 := by
  unfold setupMem
  rw [byte_wb _ _ _ (by decide) (by decide) (by decide), byte_wb_self]

theorem setupMem_b1 (s : State) : byte (setupMem s) (fb s) (oEM + 1) = 2 := by
  unfold setupMem
  rw [byte_wb_self]

/-- Just before the call's arguments: the slots, the zero test of `PS` and
`EM`, with memory changed only in the frame. -/
structure PreCall (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  out : Outside (fb s) 0 frameBytes s.mem t.mem
  slots : Slots s t.mem
  sZ : word t.mem (fb s) oZ = zmask (psB s)
  em : Spec.Rsa.bytesAt t.mem (off (fb s) oEM) (kOf s) = Spec.RsaPkcs1Enc.encode (msgB s) (psB s)

theorem getD_bytesAt (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (Spec.Rsa.bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [Spec.Rsa.bytesAt, hi]

theorem bytesAt_len (m : Mem) (p : Addr) (n : Nat) : (Spec.Rsa.bytesAt m p n).length = n := by
  simp [Spec.Rsa.bytesAt]

/-! ## The pieces -/

/-- After the first block. -/
structure AfterSetup (s t : State) : Prop where
  mem : t.mem = setupMem s
  rsi : t.gpr .rsi = stackArg s 2
  rcx : t.gpr .rcx = stackArg s 3
  r10 : t.gpr .r10 = BitVec.ofNat 64 0
  rdx : t.gpr .rdx = 0
  keep : Keep [.r10, .r11, .rsi, .rax, .rdi, .rcx, .rdx] (allocState frameBytes s) t

theorem setup_step {s : State} (hp : EPre s) : WP isa (.block setup) (allocState frameBytes s) (AfterSetup s) :=
  WP.mono (setup_run hp) fun _ ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩

/-- What the bytes of `EM` and the frame hold from `PS` on. -/
structure AfterPs (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  out : Outside (fb s) 0 frameBytes s.mem t.mem
  slots : Slots s t.mem
  e0 : byte t.mem (fb s) oEM = 0
  e1 : byte t.mem (fb s) (oEM + 1) = 2
  ep : ∀ i < (stackArg s 3).toNat, byte t.mem (fb s) (oEM + 2 + i) = (psB s).getD i 0
  rcx : t.gpr .rcx = stackArg s 3
  rdx : t.gpr .rdx = zmask (psB s)

theorem ps_step {s t₁ : State} (hp : EPre s) (h : AfterSetup s t₁) : WP isa psLoop t₁ (AfterPs s) := by
  have hF := fb_toNat hp
  have hP := hp.psLen
  have hk2 := hp.k2
  have hml := hp.hml
  have hfb : frameBytes = 1112 := rfl
  have hoEM : oEM = 80 := rfl
  have hsp₁ : t₁.gpr .rsp = fb s := (h.keep.gpr (by decide)).trans rfl
  have hrd₁ : t₁.rd = s.rd := h.keep.2.1
  have hwr₁ : t₁.wr = ⟨fb s, frameBytes⟩ :: s.wr := h.keep.2.2
  have ho₁ : Outside (fb s) 0 frameBytes s.mem t₁.mem := h.mem ▸ setupMem_outside s
  refine WP.mono (psLoop_ok hp hsp₁ hrd₁ hwr₁ ho₁ h.rsi h.rcx h.r10 h.rdx) fun t₂ hI => ?_
  have hb₂ : ∀ d, d < oEM + 2 → byte t₂.mem (fb s) d = byte t₁.mem (fb s) d := fun d hd =>
    hI.out _ (.inl (by rw [ofs_off0 _ (by omega)]; omega))
  exact ⟨(hI.keep.gpr (by decide)).trans hsp₁, hI.keep.2.1.trans hrd₁, hI.keep.2.2.trans hwr₁,
    Outside.trans ho₁ (Outside.mono hI.out (by omega) (by omega)),
    Slots.outside (h.mem ▸ setupMem_slots s) (by decide) hI.out,
    by rw [hb₂ _ (by omega), h.mem, setupMem_b0], by rw [hb₂ _ (by omega), h.mem, setupMem_b1],
    fun i hi => by rw [hI.ps i hi, getD_bytesAt _ _ hi], (hI.keep.gpr (by decide)).trans h.rcx, hI.rdx⟩

/-- After the separator: what the copy of `M` needs and keeps. -/
structure Mid (s t : State) : Prop where
  rsp : t.gpr .rsp = fb s
  rd : t.rd = s.rd
  wr : t.wr = ⟨fb s, frameBytes⟩ :: s.wr
  out : Outside (fb s) 0 frameBytes s.mem t.mem
  slots : Slots s t.mem
  e0 : byte t.mem (fb s) oEM = 0
  e1 : byte t.mem (fb s) (oEM + 1) = 2
  ep : ∀ i < (stackArg s 3).toNat, byte t.mem (fb s) (oEM + 2 + i) = (psB s).getD i 0
  es : byte t.mem (fb s) (oEM + 2 + (stackArg s 3).toNat) = 0
  ez : word t.mem (fb s) oZ = zmask (psB s)
  rdi : t.gpr .rdi = off (fb s) (oEM + 3 + (stackArg s 3).toNat)
  rsi : t.gpr .rsi = stackArg s 0
  rcx : t.gpr .rcx = stackArg s 1
  r10 : t.gpr .r10 = BitVec.ofNat 64 0
  zf : t.zf = some (stackArg s 1 == 0)

theorem sep_step {s t₂ : State} (hp : EPre s) (h : AfterPs s t₂) : WP isa (.block sep) t₂ (Mid s) := by
  have hF := fb_toNat hp
  have hP := hp.psLen
  have hk2 := hp.k2
  have hml := hp.hml
  have hfb : frameBytes = 1112 := rfl
  have hoEM : oEM = 80 := rfl
  refine WP.mono (sep_run hp h.rsp h.rd h.wr h.out h.rcx) fun t₃ ⟨hm₃, hdi₃, hsi₃, hcx₃, h10₃, hz₃, k₃⟩ => ?_
  have hb₃ : ∀ d, oEM ≤ d → d < oEM + 2 + (stackArg s 3).toNat → byte t₃.mem (fb s) d = byte t₂.mem (fb s) d := by
    intro d hd hd'
    rw [hm₃, byte_ww _ _ _ (by unfold oZ oEM at *; omega) (by omega) (by decide),
      byte_wb _ _ _ (by omega) (by omega) (by omega)]
  refine ⟨(k₃.gpr (by decide)).trans h.rsp, k₃.2.1.trans h.rd, k₃.2.2.trans h.wr, ?_, ?_,
    by rw [hb₃ _ (le_refl _) (by omega)]; exact h.e0, by rw [hb₃ _ (by omega) (by omega)]; exact h.e1,
    fun i hi => by rw [hb₃ _ (by omega) (by omega)]; exact h.ep i hi, ?_, ?_, hdi₃, hsi₃, hcx₃, h10₃, hz₃⟩
  · rw [hm₃]
    exact Outside.ww (Outside.wb h.out _ (by omega) (by omega) (by omega)) _ (by decide) (by decide) (by decide)
  · rw [hm₃]
    have s₂' : Slots s (t₂.mem.writeW (off (fb s) (oEM + 2 + (stackArg s 3).toNat)) (0 : Byte)) :=
      Slots.outside h.slots (o := oEM + 2 + (stackArg s 3).toNat) (n := 1) (by unfold oZ oEM; omega)
        (writeB_outside _ _ _ (by omega))
    exact Slots.outside s₂' (o := oZ) (n := 8) (Nat.le_refl _) (writeW_outside _ _ _ (by decide))
  · rw [hm₃, byte_ww _ _ _ (by unfold oZ oEM at *; omega) (by omega) (by decide), byte_wb_self]
  · rw [hm₃, word_writeW_self]; exact h.rdx

/-- From what `Mid` keeps, and `M` after the separator: `PreCall`. -/
theorem preCall_of {s t₃ t₄ : State} (hp : EPre s) (h : Mid s t₃) (hsp₄ : t₄.gpr .rsp = fb s) (hrd₄ : t₄.rd = s.rd)
    (hwr₄ : t₄.wr = ⟨fb s, frameBytes⟩ :: s.wr)
    (ho : Outside (fb s) (oEM + 3 + (stackArg s 3).toNat) (stackArg s 1).toNat t₃.mem t₄.mem)
    (hm : ∀ i < (stackArg s 1).toNat, byte t₄.mem (fb s) (oEM + 3 + (stackArg s 3).toNat + i) =
      s.mem (stackArg s 0 + BitVec.ofNat 64 i)) : PreCall s t₄ := by
  have hF := fb_toNat hp
  have hP := hp.psLen
  have hk2 := hp.k2
  have hml := hp.hml
  have hfb : frameBytes = 1112 := rfl
  have hoEM : oEM = 80 := rfl
  have hk1 := hp.k1
  have hPS : (psB s).length = (stackArg s 3).toNat := bytesAt_len _ _ _
  have hM : (msgB s).length = (stackArg s 1).toNat := bytesAt_len _ _ _
  have hk : ∀ d, d < oEM + 3 + (stackArg s 3).toNat → byte t₄.mem (fb s) d = byte t₃.mem (fb s) d :=
    fun d hd => ho _ (.inl (by rw [ofs_off0 _ (by omega)]; omega))
  refine ⟨hsp₄, hrd₄, hwr₄, Outside.trans h.out (Outside.mono ho (by omega) (by unfold frameBytes oEM; omega)),
    Slots.outside h.slots (by unfold oZ oEM; omega) ho, ?_, ?_⟩
  · rw [ho.word (.inl (by unfold oZ oEM; omega)) (by decide)]; exact h.ez
  · refine em_eq (by rw [hPS, hM]; simp only [kOf]; omega) (by simp only [kOf]; omega) ?_ ?_ (fun i hi => ?_) ?_
      (fun j hj => ?_)
    · rw [off_off]; show byte t₄.mem (fb s) (oEM + 0) = 0
      rw [Nat.add_zero, hk _ (by omega), h.e0]
    · rw [off_off]; show byte t₄.mem (fb s) (oEM + 1) = 2
      rw [hk _ (by omega), h.e1]
    · rw [off_off]; show byte t₄.mem (fb s) (oEM + (2 + i)) = _
      rw [← Nat.add_assoc, hk _ (by omega), h.ep i (by omega)]
    · rw [off_off]; show byte t₄.mem (fb s) (oEM + (2 + (psB s).length)) = 0
      rw [← Nat.add_assoc, hPS, hk _ (by omega), h.es]
    · rw [off_off]; show byte t₄.mem (fb s) (oEM + (3 + (psB s).length + j)) = _
      rw [hPS, show oEM + (3 + (stackArg s 3).toNat + j) = oEM + 3 + (stackArg s 3).toNat + j by
        omega, hm j (by omega), getD_bytesAt _ _ (by omega)]

theorem eval_ne_mid {s t : State} (h : Mid s t) : isa.eval .ne t = some (!(stackArg s 1 == 0)) := by
  simp only [eval, h.zf, Option.map_some]

/-- The copy of `M`, when it is not empty. -/
theorem msgLoop_step {s t₃ : State} (hp : EPre s) (h : Mid s t₃) (hm0 : 0 < (stackArg s 1).toNat) :
    WP isa msgLoop t₃ (PreCall s) := by
  have hP := hp.psLen
  refine WP.mono (msgLoop_ok hp (o := oEM + 3 + (stackArg s 3).toNat) (by omega) (by omega) hm0 h.rd h.wr h.out
    h.rdi h.rsi h.rcx h.r10) fun t₄ hJ => ?_
  exact preCall_of hp h ((hJ.keep.gpr (by decide)).trans h.rsp) (hJ.keep.2.1.trans h.rd)
    (hJ.keep.2.2.trans h.wr) hJ.out hJ.msg

/-- An empty `M`. -/
theorem empty_step {s t₃ : State} (hp : EPre s) (h : Mid s t₃) (hm0 : (stackArg s 1).toNat = 0) :
    PreCall s t₃ :=
  preCall_of hp h h.rsp h.rd h.wr (by rw [hm0]; exact Outside.refl _ _ _ _) fun i hi => absurd hi (by omega)

theorem copy_step {s t₃ : State} (hp : EPre s) (h : Mid s t₃) : WP isa msgCopy t₃ (PreCall s) := by
  refine WP.ite (!(stackArg s 1 == 0)) (eval_ne_mid h) (fun hne => ?_) (fun heq => ?_)
  · refine msgLoop_step hp h ?_
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne] at hne
    exact Nat.pos_of_ne_zero fun h => hne (BitVec.eq_of_toNat_eq (by simp [h]))
  · refine WP.block_nil (empty_step hp h ?_)
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, beq_iff_eq] at heq
    rw [heq]; rfl

theorem em_ok {s : State} (hp : EPre s) :
    WP isa (.seq (.block setup) (.seq psLoop (.seq (.block sep) msgCopy))) (allocState frameBytes s)
      (PreCall s) :=
  WP.seq (WP.mono (setup_step hp) fun _ h₁ => WP.seq (WP.mono (ps_step hp h₁) fun _ h₂ =>
    WP.seq (WP.mono (sep_step hp h₂) fun _ h₃ => copy_step hp h₃)))

end VG.Proof.RsaPkcs1Enc.X86_64
