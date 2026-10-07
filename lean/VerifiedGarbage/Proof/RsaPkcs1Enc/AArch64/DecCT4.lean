import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.DecCT3

/-!
# RSAES-PKCS1-v1_5 decryption on AArch64: constant time, the selection

The mask, the alternative length, the scan and the output: each loop is
checked by the taint analysis from the registers its setup pins as functions
of the layout (`RelCT.wp` with that setup's correctness), and so are the
pointers the output's setup loads from the frame (`ldrSp_ok`).
-/

namespace VG.Proof.RsaPkcs1Enc.AArch64.Dec

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Decrypt

/-- `ldr r, [sp, #off]`. -/
theorem ldrSp_ok (r : Reg) {off : Nat} {t : State} {Q : Addr} (hsp : t.sp = Q) (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (t.rd ++ t.wr) (Q + BitVec.ofNat 64 off) 8) :
    WP isa (.block [.ldrSp r off]) t fun u => u.sp = t.sp ∧ u.mem = t.mem ∧ u.gpr r = slot t Q off := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load, Size.bits,
    BitVec.setWidth_eq, ho, and_self, ite_true, hsp, h, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_write_self, RegUpd.sp_write, RegUpd.mem_write]
  exact ⟨trivial, trivial, rfl⟩

/-- Code checked by the taint analysis from the registers `rs`, with what
each run's correctness gives (`F`). -/
theorem taint_wp {P : State → State → Prop} {c : Prog isa} {F : State → Prop} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r)
    (hw : ∀ a b, P a b → WP isa c a F ∧ WP isa c b F) : RelCT isa P c fun a b => F a ∧ F b :=
  ((RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hp => ⟨(hag a b hp).1,
    fun r hr => (hag a b hp).2 r (Taint.mem_ofRegs.mp hr)⟩) h).wp hw).mono (fun _ _ h => h) fun _ _ h => h.2

theorem taint_of {P : State → State → Prop} {c : Prog isa} (rs : List Reg)
    {hc : VG.Taint.Hint VG.AArch64.Taint.T} (h : (taint.check (Taint.ofRegs rs) c hc).isSome = true)
    (hag : ∀ a b, P a b → a.sp = b.sp ∧ ∀ r ∈ rs, a.gpr r = b.gpr r) : RelCT isa P c fun _ _ => True :=
  RelCT.taint (A := taint) (Taint.ofRegs rs) (fun a b hp => ⟨(hag a b hp).1,
    fun r hr => (hag a b hp).2 r (Taint.mem_ofRegs.mp hr)⟩) h

theorem pair_eq {a b : State} {x y z : Reg} {vx vy : BitVec 64} (ha : a.gpr x = vx ∧ a.gpr y = vy)
    (hb : b.gpr x = vx ∧ b.gpr y = vy) (hz : z ∈ [x, y]) : a.gpr z = b.gpr z := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl
  exacts [ha.1.trans hb.1.symm, ha.2.trans hb.2.symm]

/-! ## The mask, the alternative length and the scan -/

abbrev AMΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, AMR L g vv m₀ R EM kd t
abbrev MKΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, MK L g vv m₀ R EM kd t
abbrev ALΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, AL L g vv m₀ R EM kd t
abbrev SCΦ : Inv := fun L g vv m₀ t => ∃ R EM kd, SC L g vv m₀ R EM kd t

theorem k_sub {k : BitVec 64} {n : Nat} (h : n ≤ k.toNat) : k - BitVec.ofNat 64 n = BitVec.ofNat 64 (k.toNat - n) := by
  have := k.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The mask's loop after `j` iterations. -/
def MG (L : Lay) (j : Nat) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x8 = BitVec.ofNat 64 (2 ^ j - 1) ∧ u.gpr .x9 = BitVec.ofNat 64 (L.k.toNat - 11)

theorem maskPart_ct {S : Nat} : RelCT isa (Two S AMΦ) maskPart (Two S MKΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (maskPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hk := hp.1.k1024
  have hk64 := hp.1.k64
  have hw : ∀ g vv m₀ (t : State), AMΦ e.L g vv m₀ t → WP isa (.block maskInit) t (MG e.L 0) :=
    fun _ _ _ t ⟨_, _, _, h⟩ => WP.mono (maskInit_ok h.post.ctx.sp h.post.slots) fun _ ⟨hs, x9, x8⟩ =>
      ⟨hs.sp.trans h.post.ctx.sp, x8, by rw [x9, slot, h.post.ctx.kept.k, k_sub (by omega)]⟩
  refine RelCT.seq (Q := fun _ _ => True) (taint_wp (F := MG e.L 0) [] (by taint_decide)
    (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨f₁.post.ctx.sp.trans f₂.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ ⟨_, _, _, f₁, f₂⟩ => ⟨hw _ _ _ _ f₁, hw _ _ _ _ f₂⟩) ?_ _ _ _ _ _ _ hp e₁ e₂
  refine (count_ct (bitLength_pos (x := e.L.k.toNat - 11) (by omega)) (fun j a b => MG e.L j a ∧ MG e.L j b)
    fun j hj => ?_).mono (fun _ _ h => h) fun _ _ _ => trivial
  refine (taint_wp (F := fun w => MG e.L (j + 1) w ∧
      (w.gpr .x10 != 0) = decide (j + 1 ≠ Spec.RsaPkcs1Enc.bitLength (e.L.k.toNat - 11))) [.x8, .x9]
    (by taint_decide) (fun _ _ ⟨⟨a, a8, a9⟩, ⟨b, b8, b9⟩⟩ => ⟨a.trans b.symm, fun _ => pair_eq ⟨a8, a9⟩ ⟨b8, b9⟩⟩)
    fun a b ⟨ga, gb⟩ => ⟨?_, ?_⟩).mono (fun _ _ h => h) fun _ _ ⟨⟨ga, ca⟩, ⟨gb, cb⟩⟩ => ⟨⟨ga, gb⟩, ca, cb⟩
  · exact WP.mono (maskStep_ok (by omega) (by omega) hj ga.2.1 ga.2.2) fun _ ⟨hw, w8, w9, w10⟩ =>
      ⟨⟨hw.sp.trans ga.1, w8, w9⟩, w10⟩
  · exact WP.mono (maskStep_ok (by omega) (by omega) hj gb.2.1 gb.2.2) fun _ ⟨hw, w8, w9, w10⟩ =>
      ⟨⟨hw.sp.trans gb.1, w8, w9⟩, w10⟩

/-- After `alInit`. -/
def AG (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x11 = scA L sCL ∧ u.gpr .x12 = BitVec.ofNat 64 128

/-- After `scanInit`. -/
def SG₀ (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x11 = L.out + BitVec.ofNat 64 2 ∧ u.gpr .x12 = L.k - BitVec.ofNat 64 2

theorem alPart_ct {S : Nat} : RelCT isa (Two S MKΦ) alPart (Two S ALΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (alPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  have hw : ∀ g vv m₀ (t : State), MKΦ e.L g vv m₀ t → WP isa (.block alInit) t fun u =>
      AG e.L u := fun _ _ _ t ⟨_, _, _, h⟩ =>
    WP.mono (alInit_ok h.amr.post.ctx.sp h.amr.post.slots) fun _ ⟨hs, x11, x12, _⟩ =>
      ⟨hs.sp.trans h.amr.post.ctx.sp, by rw [x11, slot, h.amr.post.ctx.kept.scr], x12⟩
  exact (taint_wp (F := AG e.L) [] (by taint_decide)
    (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨f₁.amr.post.ctx.sp.trans f₂.amr.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ ⟨_, _, _, f₁, f₂⟩ => ⟨hw _ _ _ _ f₁, hw _ _ _ _ f₂⟩).seq
    (taint_of [.x11, .x12] (by taint_decide) fun _ _ ⟨⟨a, a11, a12⟩, ⟨b, b11, b12⟩⟩ =>
      ⟨a.trans b.symm, fun _ => pair_eq ⟨a11, a12⟩ ⟨b11, b12⟩⟩)

theorem scanPart_ct {S : Nat} : RelCT isa (Two S ALΦ) scanPart (Two S SCΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (scanPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  have hw : ∀ g vv m₀ (t : State), ALΦ e.L g vv m₀ t → WP isa (.block scanInit) t fun u =>
      SG₀ e.L u :=
    fun _ _ _ t ⟨_, _, _, h⟩ => WP.mono (scanInit_ok h.amr.post.ctx.sp h.amr.post.slots)
      fun _ ⟨hs, x11, x12, _⟩ => ⟨hs.sp.trans h.amr.post.ctx.sp, by rw [x11, slot, h.amr.post.ctx.kept.out],
        by rw [x12, slot, h.amr.post.ctx.kept.k]⟩
  exact (taint_wp (F := SG₀ e.L) [] (by taint_decide)
    (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨f₁.amr.post.ctx.sp.trans f₂.amr.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
    fun _ _ ⟨_, _, _, f₁, f₂⟩ => ⟨hw _ _ _ _ f₁, hw _ _ _ _ f₂⟩).seq
    (taint_of [.x11, .x12] (by taint_decide) fun _ _ ⟨⟨a, a11, a12⟩, ⟨b, b11, b12⟩⟩ =>
      ⟨a.trans b.symm, fun _ => pair_eq ⟨a11, a12⟩ ⟨b11, b12⟩⟩)

/-! ## The output -/

/-- What the output's setup leaves. -/
abbrev FinΦ : Inv := fun L g vv m₀ t => ∃ R EM kd,
  Fin L g vv m₀ R EM (amOf L kd) (vOfEM L EM) (decide (R = 1)) (lenOf L EM kd) t

theorem validSame_ok {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {R : BitVec 64}
    {EM kd : List Byte} (hL : L.Ok) {t : State} (h : SC L g vv m₀ R EM kd t) :
    WP isa (.block validBlock) t (Same t) := by
  have hk := hL.k1024
  have hk64 := hL.k64
  have hc := h.amr.post
  have hK : slot t L.Q oK = BitVec.ofNat 64 L.k.toNat := by
    rw [slot, hc.ctx.kept.k, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hO : slot t L.Q oOut = L.out := hc.ctx.kept.out
  exact WP.mono (validBlock_ok hc.ctx.sp hc.slots (by rw [hO]; exact hc.ctx.outR (by omega))
    (by rw [hO]; exact hc.ctx.outR (by omega)) h.x17 h.x15 h.x16 h.al hK
    (by have := sep_lt EM (k := L.k.toNat) (by omega); omega)) fun _ h => h.1

/-- Before `outInit`: where `*msg_len`'s pointer is. -/
def OH (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.mem.readW (L.Q + BitVec.ofNat 64 oML) 64 = L.ml ∧
    InRegions (u.rd ++ u.wr) (L.Q + BitVec.ofNat 64 oML) 8

/-- Before the selection's loop. -/
def SG (L : Lay) (u : State) : Prop :=
  u.sp = L.Q ∧ u.gpr .x10 = scA L sAM + BitVec.ofNat 64 0 ∧ u.gpr .x11 = L.out + BitVec.ofNat 64 0 ∧
    u.gpr .x12 = BitVec.ofNat 64 (L.k.toNat - 0)

theorem selPart_ct {S : Nat} : RelCT isa (Two S SCΦ) selPart (Two S FinΦ) := by
  refine two_wp (fun e => ?_) fun _ _ _ _ _ hL _ ⟨_, _, _, h⟩ => WP.mono (selPart_ok hL h) fun _ h' => ⟨_, _, _, h'⟩
  -- `out` into `x11`, then the validity.
  have vb : RelCT isa (TwoE S SCΦ e) (.block validBlock) fun _ _ => True :=
    RelCT.block_append (l₁ := ([.ldrSp .x11 oOut] : List Instr)) (l₂ := validBlock.tail)
      ((taint_wp (F := fun u => u.sp = e.L.Q ∧ u.gpr .x11 = e.L.out) [] (by taint_decide)
        (fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
          ⟨f₁.amr.post.ctx.sp.trans f₂.amr.post.ctx.sp.symm, fun _ h => absurd h List.not_mem_nil⟩)
        fun _ _ ⟨_, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
          ⟨WP.mono (ldrSp_ok .x11 f₁.amr.post.ctx.sp (by decide) (f₁.amr.post.slots oOut (by decide)))
            fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans f₁.amr.post.ctx.sp, by rw [hx, slot, f₁.amr.post.ctx.kept.out]⟩,
          WP.mono (ldrSp_ok .x11 f₂.amr.post.ctx.sp (by decide) (f₂.amr.post.slots oOut (by decide)))
            fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans f₂.amr.post.ctx.sp, by rw [hx, slot, f₂.amr.post.ctx.kept.out]⟩⟩).seq
      (taint_of [.x11] (by taint_decide) fun _ _ ⟨⟨a0, a11⟩, ⟨b0, b11⟩⟩ =>
        ⟨a0.trans b0.symm, fun r hr => by rw [List.mem_singleton.mp hr, a11, b11]⟩))
  have oh : ∀ g vv m₀ (t : State), e.L.Ok → SCΦ e.L g vv m₀ t → WP isa (.block validBlock) t (OH e.L) :=
    fun _ _ _ _ hL ⟨_, _, _, h⟩ => WP.mono (validSame_ok hL h) fun _ hs =>
      ⟨hs.sp.trans h.amr.post.ctx.sp, by rw [hs.mem]; exact h.amr.post.ctx.kept.ml,
        by rw [hs.rd, hs.wr]; exact h.amr.post.slots oML (by decide)⟩
  -- `*msg_len`'s pointer into `x10`, then its store.
  have oi : RelCT isa (fun a b => True ∧ OH e.L a ∧ OH e.L b) (.block outInit) fun _ _ => True :=
    RelCT.block_append (l₁ := ([.ldrSp .x10 oML] : List Instr)) (l₂ := outInit.tail)
      ((taint_wp (F := fun u => u.sp = e.L.Q ∧ u.gpr .x10 = e.L.ml) [] (by taint_decide)
        (fun _ _ ⟨_, ha, hb⟩ => ⟨ha.1.trans hb.1.symm, fun _ h => absurd h List.not_mem_nil⟩)
        fun _ _ ⟨_, ha, hb⟩ =>
          ⟨WP.mono (ldrSp_ok .x10 ha.1 (by decide) ha.2.2) fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans ha.1, hx.trans ha.2.1⟩,
          WP.mono (ldrSp_ok .x10 hb.1 (by decide) hb.2.2) fun _ ⟨hsp, _, hx⟩ => ⟨hsp.trans hb.1, hx.trans hb.2.1⟩⟩).seq
      (taint_of [.x10] (by taint_decide) fun _ _ ⟨⟨a0, a10⟩, ⟨b0, b10⟩⟩ =>
        ⟨a0.trans b0.symm, fun r hr => by rw [List.mem_singleton.mp hr, a10, b10]⟩))
  refine RelCT.assoc ((((vb.wp fun _ _ ⟨hL, _, _, f₁, f₂⟩ => ⟨oh _ _ _ _ hL f₁, oh _ _ _ _ hL f₂⟩).seq oi).wp
    (F₁ := SG e.L) (F₂ := SG e.L) fun _ _ ⟨hL, _, _, ⟨_, _, _, f₁⟩, ⟨_, _, _, f₂⟩⟩ =>
      ⟨WP.mono (selInit_ok hL f₁) fun _ h => ⟨h.ctx.sp, h.x10, h.x11, h.x12⟩,
        WP.mono (selInit_ok hL f₂) fun _ h => ⟨h.ctx.sp, h.x10, h.x11, h.x12⟩⟩).seq ?_)
  exact taint_of [.x11, .x10, .x12] (by taint_decide) fun _ _ ⟨_, ⟨a0, a10, a11, a12⟩, ⟨b0, b10, b11, b12⟩⟩ =>
    ⟨a0.trans b0.symm, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      exacts [a11.trans b11.symm, a10.trans b10.symm, a12.trans b12.symm]⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Dec
