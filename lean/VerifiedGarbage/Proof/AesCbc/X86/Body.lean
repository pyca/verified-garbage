import VerifiedGarbage.Proof.AesCbc.X86.Loop

/-!
# AES-CBC on x86: one block

`encBody_ok` and `decBody_ok`: one run of `encBody` or `decBody` takes the
loop invariant from `k` blocks to `k + 1` (`BodyOk`), for any implementation
of the block functions (`BlocksImpl`).
-/

namespace VG.Proof.AesCbc.X86

open VG VG.X86 VG.Impl.AesCbc.X86
open VG.Impl.CmacAes.X86 (argOp advance xor4 zero4)
open VG.Proof.CmacAes.X86 (wp_arg xor4_ok zero4_ok add0 arg_ofNat)
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi)
open VG.Proof.Aes.X86 (BlocksImpl)
open VG.Spec.Aes (bytesAt)

/-- The block `esi` points at, as a 32-bit address. -/
abbrev D32 (s₀ : State) (k : Nat) : BitVec 32 := Dp s₀ + BitVec.ofNat 32 (16 * k)

/-- The saved ciphertext block. -/
abbrev Sv (s₀ : State) : Addr := (S s₀).setWidth 64 + BitVec.ofNat 64 2048

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.d32 {k : Nat} (hk : k < N s₀) : (D32 s₀ k).setWidth 64 = blk s₀ k := hp.dataA hk

theorem UPre.blk_iv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint (ivR s₀) :=
  hp.iv_data.symm.sub_left (UPre.data_sub hk)

theorem UPre.blk_sv {k : Nat} (hk : k < N s₀) : (⟨blk s₀ k, 16⟩ : Region).Disjoint ⟨Sv s₀, 16⟩ :=
  (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (UPre.scr_sub (by decide))

theorem UPre.iv_sv : (ivR s₀).Disjoint ⟨Sv s₀, 16⟩ := hp.iv_scr.sub_right (UPre.scr_sub (by decide))

theorem UPre.sv_scr : (⟨Sv s₀, 16⟩ : Region).Disjoint ⟨(S s₀).setWidth 64, 2048⟩ :=
  Offset.disjoint_base _ (by decide) (by have := hp.scr_fit; omega)

/-- The stack arguments, in a state whose memory differs only within `Big`. -/
theorem UPre.args_of {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    ∀ i < 6, m.readW (argAddr s₀ i) 32 = arg s₀ i := fun _ hi => hp.arg_keep hf hi

/-- The arguments of a call on block `k`, with the working space at the start
of the scratch buffer. -/
theorem UPre.blkPre {k : Nat} (hk : k < N s₀) {s : State}
    (eax : s.gpr .eax = W s₀) (ecx : s.gpr .ecx = arg s₀ 1) (ebx : s.gpr .ebx = D32 s₀ k)
    (edi : s.gpr .edi = 1) (ebp : s.gpr .ebp = S s₀) (esp : s.gpr .esp = E s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    BlkPre s (W s₀) (D32 s₀ k) (S s₀) (R s₀) := by
  have hb : below (s.gpr .esp) 24 = stkR s₀ := by rw [esp]; exact hp.below_eq
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  refine ⟨eax, by rw [ecx]; exact arg_ofNat s₀ 1, ebx, edi, ebp, hp.rounds, by rw [esp]; exact hp.esp24,
    ?_, hp.sch_scr.sub_right (Region.sub_prefix (by decide)), ?_, by rw [hb]; exact hp.b_sch, ?_,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), hp.sch_fit, ?_,
    by have := hp.scr_fit; omega, ?_, ?_⟩
  · rw [hd]; exact hp.sch_data.sub_right (UPre.data_sub hk)
  · rw [hd]; exact (hp.data_scr.sub_left (UPre.data_sub hk)).sub_right (Region.sub_prefix (by decide))
  · rw [hb, hd]; exact hp.b_data.sub_right (UPre.data_sub hk)
  · rw [qN]; omega
  · rw [hrd, hwr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [hwr, hp.wr, hd]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩

omit hp in
theorem covBlk {k : Nat} (hk : k < N s₀) {rs : List Region} (h : dataR s₀ ∈ rs) :
    Covers [⟨blk s₀ k, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨dataR s₀, h, 16 * k, rfl, by simp; omega⟩

omit hp in
theorem covIv {rs : List Region} (h : ivR s₀ ∈ rs) : Covers [⟨(Iv s₀).setWidth 64, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ivR s₀, h, 0, by simp, by simp⟩

omit hp in
theorem covSv {rs : List Region} (h : scrR s₀ ∈ rs) : Covers [⟨Sv s₀, 16⟩] rs :=
  Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, h, 2048, rfl, by simp⟩

end

section
variable {s₀ : State}

/-- The frame of a step, in the regions the invariant allows. -/
theorem stepFrame {k : Nat} (hk : k < N s₀) {m m' : Mem}
    (hf : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m') :
    Frame [ivR s₀, dataR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- A frame within the regions a step may change, from the frames of its pieces. -/
theorem stepIn {k : Nat} {r : Region}
    (h : r = ⟨blk s₀ k, 16⟩ ∨ r = ivR s₀ ∨ Region.Sub r ⟨(S s₀).setWidth 64, 2064⟩ ∨ r = stkR s₀) :
    ∃ r' ∈ [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀], Region.Sub r r' := by
  rcases h with rfl | rfl | h | rfl
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

end

theorem one {r : Region} {P : Addr} (hd : (⟨P, 16⟩ : Region).Disjoint r) :
    ∀ r' ∈ [r], (⟨P, 16⟩ : Region).Disjoint r' := fun r' hr' => by
  simp only [List.mem_singleton] at hr'; subst hr'; exact hd

/-! ## The arguments of the call -/

/-- What the code before the call leaves. -/
structure PreA (s₀ : State) (k : Nat) (s : State) (m : Mem) (s₁ : State) : Prop where
  pre : BlkPre s₁ (W s₀) (D32 s₀ k) (S s₀) (R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = m
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem callArgs_eq : callArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (.reg .esi),
    .mov .edi (.imm 1), .mov .ebp (argOp 5)] := rfl

theorem callArgs_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hesi : s.gpr .esi = D32 s₀ k) (hesp : s.gpr .esp = E s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) :
    WP isa (.block callArgs) s (PreA s₀ k s s.mem) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  rw [callArgs_eq]
  refine wp_arg (s₀ := s₀) hesp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 0 (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 1 (by decide)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_movi fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 5 (by decide)) fun s₅ u₅ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebx → r ≠ .edi → r ≠ .ebp → s₅.gpr r = s.gpr r :=
    fun r ha hc hb hd hp' => by
      rw [u₅.other _ hp', u₄.other _ hd, u₃.other _ hb, u₂.other _ hc, u₁.other _ ha]
  have rd₅ : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₅ : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have esp₅ : s₅.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), hesp]
  refine ⟨hp.blkPre hk ?_ ?_ ?_ ?_ u₅.gpr esp₅ (by rw [rd₅, hrd]) (by rw [wr₅, hwr]),
    keep _ (by decide) (by decide) (by decide) (by decide) (by decide), by rw [esp₅, hesp],
    by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], rd₅, wr₅⟩
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide),
      hesi]
  · rw [u₅.other _ (by decide), u₄.gpr]

/-! ## Encryption -/

theorem encPre_eq : encPre = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++ callArgs) := rfl

theorem encA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode true) s₀ k s) :
    WP isa (.block encPre) s (PreA s₀ k s
      (Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64))) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have big := UPre.big_of h.frame
  have hargs := hp.args_of big
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  rw [encPre_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide)) fun s₁ u₁ => ?_
  have i₁ : s₁.gpr .esi = D32 s₀ k := by rw [u₁.other _ (by decide), h.esi]
  have b₁ : s₁.gpr .ebx = Iv s₀ := u₁.gpr
  have rw₁ : s₁.rd ++ s₁.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  have w₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₁.wr, h.wr, hp.wr]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₁, qN]; omega) (by rw [b₁]; omega) (by rw [i₁, qN]; omega)
    (by rw [i₁, add0, hd, rw₁]; exact covBlk hk (by simp))
    (by rw [b₁, add0, rw₁]; exact covIv (by simp))
    (by rw [i₁, add0, hd, w₁]; exact covBlk hk (by simp)) fun s₂ g₂ => ?_
  have m₂ : s₂.mem = Proof.Cmac.xor4Mem s.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₂.mem, i₁, b₁, add0, add0, hd, u₁.mem]
  have f₂ : Frame [⟨blk s₀ k, 16⟩] s.mem s₂.mem := by rw [m₂]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := big.trans (f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩)
  refine WP.mono (callArgs_wp hp hk (by rw [g₂.gpr _ (by decide) (by decide), i₁])
    (by rw [g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), h.esp])
    (by rw [g₂.rd, u₁.rd, h.rd]) (by rw [g₂.wr, u₁.wr, h.wr]) (hp.args_of big₂)) fun s₃ a => ?_
  exact ⟨a.pre, by rw [a.esi, g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide)],
    by rw [a.esp, g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide)], by rw [a.mem, m₂],
    by rw [a.rd, g₂.rd, u₁.rd], by rw [a.wr, g₂.wr, u₁.wr]⟩

theorem encPost_eq : encPost = .mov .ebx (argOp 2) :: (zero4 .ebx 0 ++ (xor4 .ebx .esi .ebx 0 0 0 ++ advance)) := rfl

theorem encBody_ok (v : BlocksImpl) : BodyOk (cbcMode true) (encBody v.enc) := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  refine WP.seq (WP.mono (encA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.encOk v.encNosp v.encStack a.pre) fun s₂ c => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  -- Memory so far.
  have f₁ : Frame [⟨blk s₀ k, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨dataR s₀, by simp, UPre.data_sub hk⟩)
  have big₂ : Frame (Big s₀) s₀.mem s₂.mem := (UPre.big_of h.frame).trans ((stepFrame hk fs₂).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [encPost_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  refine zero4_ok (by decide) (by rw [b₃]; omega) (by rw [b₃, add0, u₃.wr, w₂]; exact covIv (by simp))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  have b₄ : s₄.gpr .ebx = Iv s₀ := by rw [g₄ _ (by decide), b₃]
  have i₄ : s₄.gpr .esi = D32 s₀ k := by rw [g₄ _ (by decide), u₃.other _ (by decide), esi₂]
  have rw₄ : s₄.rd ++ s₄.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₄, wr₄, u₃.rd, u₃.wr, rw₂, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₄]; omega) (by rw [i₄, qN]; omega) (by rw [b₄]; omega)
    (by rw [b₄, add0, rw₄]; exact covIv (by simp))
    (by rw [i₄, add0, hd, rw₄]; exact covBlk hk (by simp))
    (by rw [b₄, add0, wr₄, u₃.wr, w₂]; exact covIv (by simp)) fun s₅ g₅ => ?_
  have m₅ : s₅.mem = copy4Mem s₂.mem ((Iv s₀).setWidth 64) (blk s₀ k) := by
    rw [g₅.mem, b₄, i₄, add0, add0, hd, m₄, b₃, add0, u₃.mem]; rfl
  have f₅ : Frame [ivR s₀] s₂.mem s₅.mem := by rw [m₅]; exact copy4Mem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₅.mem :=
    fs₂.trans (f₅.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  have big₅ : Frame (Big s₀) s₀.mem s₅.mem := (UPre.big_of h.frame).trans ((stepFrame hk fStep).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  refine WP.mono (advance_wp hp hk (by rw [g₅.gpr _ (by decide) (by decide), i₄])
    (by rw [g₅.gpr _ (by decide) (by decide), g₄ _ (by decide), u₃.other _ (by decide), esp₂])
    (hp.args_of big₅) (by rw [g₅.rd, g₅.wr, rd₄, wr₄, u₃.rd, u₃.wr, rw₂]))
    fun s₆ ⟨esi₆, esp₆, _, mem₆, rd₆, wr₆, zf₆⟩ => ⟨?_, zf₆⟩
  -- The new block, and the chaining value.
  have hblk := h.block hk
  have newBlk : bytesAt s₆.mem (blk s₀ k) 16 =
      Spec.Cbc.aesWith (R s₀) (bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)))
        (Spec.Cbc.xor ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk))
          (Spec.Cbc.next (iv0 s₀) (outK (cbcMode true) s₀ k))) := by
    rw [mem₆, Proof.Cmac.bytesAt_frame f₅ (one (hp.blk_iv hk)) (by decide), ← hd, c.out, hd,
      ← UPre.sched_bytes hp big₁, ← aesWith_state, a.mem, xorIn4_bytes _ (hp.blk_iv hk), hblk, h.iv]
    rfl
  have newIv : bytesAt s₆.mem ((Iv s₀).setWidth 64) 16 = bytesAt s₆.mem (blk s₀ k) 16 := by
    rw [mem₆, m₅, copy4Mem_bytes _ (hp.blk_iv hk).symm,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame s₂.mem ((Iv s₀).setWidth 64) (blk s₀ k)) (one (hp.blk_iv hk))
        (by decide)]
  have hl : (outK (cbcMode true) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (cbcMode true) s₀ (k + 1) = outK (cbcMode true) s₀ k ++ [bytesAt s₆.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, ite_true, take_succ_blks s₀ hk, encrypt_snoc]
  refine ⟨esi₆, esp₆, by rw [rd₆, g₅.rd, rd₄, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₆, g₅.wr, wr₄, u₃.wr, c.wr, a.wr, h.wr], by rw [mem₆]; exact h.frame.trans (stepFrame hk fStep),
    ?_, ?_⟩
  · rw [mem₆, hp.blocksAt_step hk fStep, h.data, ← mem₆, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, ite_true, outSucc, next_snoc]

/-! ## Decryption -/

theorem decPre_eq : decPre = .mov .ebp (argOp 5) :: (zero4 .ebp cOff ++ (xor4 .ebp .esi .ebp cOff 0 cOff ++ callArgs)) :=
  rfl

theorem decA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀)
    {s : State} (h : LInv (cbcMode false) s₀ k s) :
    WP isa (.block decPre) s (PreA s₀ k s (copy4Mem s.mem (Sv s₀) (blk s₀ k))) := by
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have big := UPre.big_of h.frame
  have hargs := hp.args_of big
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hsc := hp.scr_fit
  rw [decPre_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 5 (by decide)) fun s₁ u₁ => ?_
  have p₁ : s₁.gpr .ebp = S s₀ := u₁.gpr
  have w₁ : s₁.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₁.wr, h.wr, hp.wr]
  refine zero4_ok (by decide) (by rw [p₁]; unfold cOff; omega) (by rw [p₁, w₁]; exact covSv (by simp))
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  have p₂ : s₂.gpr .ebp = S s₀ := by rw [g₂ _ (by decide), p₁]
  have i₂ : s₂.gpr .esi = D32 s₀ k := by rw [g₂ _ (by decide), u₁.other _ (by decide), h.esi]
  have rw₂ : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₂, wr₂, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₂]; unfold cOff; omega) (by rw [i₂, qN]; omega) (by rw [p₂]; unfold cOff; omega)
    (by rw [p₂, rw₂]; exact covSv (by simp))
    (by rw [i₂, add0, hd, rw₂]; exact covBlk hk (by simp))
    (by rw [p₂, wr₂, w₁]; exact covSv (by simp)) fun s₃ g₃ => ?_
  have m₃ : s₃.mem = copy4Mem s.mem (Sv s₀) (blk s₀ k) := by
    rw [g₃.mem, p₂, i₂, add0, hd, m₂, p₁, u₁.mem]; rfl
  have f₃ : Frame [⟨Sv s₀, 16⟩] s.mem s₃.mem := by rw [m₃]; exact copy4Mem_frame _ _ _
  have big₃ : Frame (Big s₀) s₀.mem s₃.mem := big.trans (f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩)
  refine WP.mono (callArgs_wp hp hk (by rw [g₃.gpr _ (by decide) (by decide), i₂])
    (by rw [g₃.gpr _ (by decide) (by decide), g₂ _ (by decide), u₁.other _ (by decide), h.esp])
    (by rw [g₃.rd, rd₂, u₁.rd, h.rd]) (by rw [g₃.wr, wr₂, u₁.wr, h.wr]) (hp.args_of big₃)) fun s₄ a => ?_
  exact ⟨a.pre, by rw [a.esi, g₃.gpr _ (by decide) (by decide), g₂ _ (by decide), u₁.other _ (by decide)],
    by rw [a.esp, g₃.gpr _ (by decide) (by decide), g₂ _ (by decide), u₁.other _ (by decide)], by rw [a.mem, m₃],
    by rw [a.rd, g₃.rd, rd₂, u₁.rd], by rw [a.wr, g₃.wr, wr₂, u₁.wr]⟩

theorem decPost_eq : decPost = .mov .ebx (argOp 2) :: (xor4 .esi .ebx .esi 0 0 0 ++
    (.mov .ebp (argOp 5) :: (zero4 .ebx 0 ++ (xor4 .ebx .ebp .ebx 0 cOff 0 ++ advance)))) := rfl

theorem decBody_ok (v : BlocksImpl) : BodyOk (cbcMode false) (decBody v.dec) := by
  intro s₀ hp k hk s h
  have hd := hp.d32 hk
  have qN := hp.dataN hk
  have hdf := hp.data_fit
  have hiv := hp.iv_fit
  have hsc := hp.scr_fit
  refine WP.seq (WP.mono (decA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (blk_call v.decOk v.decNosp v.decStack a.pre) fun s₂ c => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 24 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  have svSub : Region.Sub ⟨Sv s₀, 16⟩ ⟨(S s₀).setWidth 64, 2064⟩ := Offset.sub_base _ (by decide)
  -- Memory so far.
  have f₁ : Frame [⟨Sv s₀, 16⟩] s.mem s₁.mem := by rw [a.mem]; exact copy4Mem_frame _ _ _
  have f₂ : Frame [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := c.frame; rw [hb, hd] at fr; exact fr
  have fs₂ : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₂.mem :=
    (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub)))).trans
      (f₂.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact stepIn (.inl rfl)
        · exact stepIn (.inr (.inr (.inl (Region.sub_prefix (by decide)))))
        · exact stepIn (.inr (.inr (.inr rfl))))
  have bigOf : ∀ {m : Mem}, Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem m →
      Frame (Big s₀) s₀.mem m := fun hf => (UPre.big_of h.frame).trans ((stepFrame hk hf).sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨ivR s₀, by simp, fun _ h => h⟩
    · exact ⟨dataR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := bigOf (f₁.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inr (.inl svSub))))
  have big₂ := bigOf fs₂
  have esi₂ : s₂.gpr .esi = D32 s₀ k := by rw [c.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [c.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [c.rd, c.wr, a.rd, a.wr, h.rd, h.wr]
  have rwl : s₂.rd ++ s₂.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rw₂, hp.rd, hp.wr]; rfl
  have w₂ : s₂.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [c.wr, a.wr, h.wr, hp.wr]
  rw [decPost_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [rw₂]; exact hp.arg_in (by decide)) (hp.args_of big₂ 2 (by decide))
    fun s₃ u₃ => ?_
  have b₃ : s₃.gpr .ebx = Iv s₀ := u₃.gpr
  have i₃ : s₃.gpr .esi = D32 s₀ k := by rw [u₃.other _ (by decide), esi₂]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [i₃, qN]; omega) (by rw [b₃]; omega) (by rw [i₃, qN]; omega)
    (by rw [i₃, add0, hd, u₃.rd, u₃.wr, rwl]; exact covBlk hk (by simp))
    (by rw [b₃, add0, u₃.rd, u₃.wr, rwl]; exact covIv (by simp))
    (by rw [i₃, add0, hd, u₃.wr, w₂]; exact covBlk hk (by simp)) fun s₄ g₄ => ?_
  have m₄ : s₄.mem = Proof.Cmac.xor4Mem s₂.mem (blk s₀ k) (blk s₀ k) ((Iv s₀).setWidth 64) := by
    rw [g₄.mem, i₃, b₃, add0, add0, hd, u₃.mem]
  have f₄ : Frame [⟨blk s₀ k, 16⟩] s₂.mem s₄.mem := by rw [m₄]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  have big₄ : Frame (Big s₀) s₀.mem s₄.mem := bigOf (fs₂.trans (f₄.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl)))
  have esp₄ : s₄.gpr .esp = E s₀ := by rw [g₄.gpr _ (by decide) (by decide), u₃.other _ (by decide), esp₂]
  have rw₄ : s₄.rd ++ s₄.wr = s₀.rd ++ s₀.wr := by rw [g₄.rd, g₄.wr, u₃.rd, u₃.wr, rw₂]
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rw₄]; exact hp.arg_in (by decide)) (hp.args_of big₄ 5 (by decide))
    fun s₅ u₅ => ?_
  have b₅ : s₅.gpr .ebx = Iv s₀ := by rw [u₅.other _ (by decide), g₄.gpr _ (by decide) (by decide), b₃]
  have p₅ : s₅.gpr .ebp = S s₀ := u₅.gpr
  have w₅ : s₅.wr = [ivR s₀, dataR s₀, scrR s₀] := by rw [u₅.wr, g₄.wr, u₃.wr, w₂]
  refine zero4_ok (by decide) (by rw [b₅]; omega) (by rw [b₅, add0, w₅]; exact covIv (by simp))
    fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have b₆ : s₆.gpr .ebx = Iv s₀ := by rw [g₆ _ (by decide), b₅]
  have p₆ : s₆.gpr .ebp = S s₀ := by rw [g₆ _ (by decide), p₅]
  have rw₆ : s₆.rd ++ s₆.wr = [schR s₀, argsR s₀, ivR s₀, dataR s₀, scrR s₀] := by
    rw [rd₆, wr₆, u₅.rd, u₅.wr, rw₄, hp.rd, hp.wr]; rfl
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₆]; omega) (by rw [p₆]; unfold cOff; omega) (by rw [b₆]; omega)
    (by rw [b₆, add0, rw₆]; exact covIv (by simp))
    (by rw [p₆, rw₆]; exact covSv (by simp))
    (by rw [b₆, add0, wr₆, w₅]; exact covIv (by simp)) fun s₇ g₇ => ?_
  have m₇ : s₇.mem = copy4Mem s₄.mem ((Iv s₀).setWidth 64) (Sv s₀) := by
    rw [g₇.mem, b₆, p₆, add0, m₆, b₅, add0, u₅.mem]; rfl
  have f₇ : Frame [ivR s₀] s₄.mem s₇.mem := by rw [m₇]; exact copy4Mem_frame _ _ _
  have fStep : Frame [⟨blk s₀ k, 16⟩, ivR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₇.mem :=
    (fs₂.trans (f₄.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inl rfl))).trans
      (f₇.sub fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact stepIn (.inr (.inl rfl)))
  refine WP.mono (advance_wp hp hk
    (by rw [g₇.gpr _ (by decide) (by decide), g₆ _ (by decide), u₅.other _ (by decide),
      g₄.gpr _ (by decide) (by decide), i₃])
    (by rw [g₇.gpr _ (by decide) (by decide), g₆ _ (by decide), u₅.other _ (by decide), esp₄])
    (hp.args_of (bigOf fStep)) (by rw [g₇.rd, g₇.wr, rd₆, wr₆, u₅.rd, u₅.wr, rw₄]))
    fun s₈ ⟨esi₈, esp₈, _, mem₈, rd₈, wr₈, zf₈⟩ => ⟨?_, zf₈⟩
  have callIv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (ivR s₀).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_iv hk).symm
    · exact hp.iv_scr.sub_right (Region.sub_prefix (by decide))
    · exact hp.b_iv.symm
  have callSv : ∀ r ∈ [⟨blk s₀ k, 16⟩, ⟨(S s₀).setWidth 64, 2048⟩, stkR s₀], (⟨Sv s₀, 16⟩ : Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.blk_sv hk).symm
    · exact hp.sv_scr
    · exact (hp.b_scr.sub_right (UPre.scr_sub (by decide))).symm
  have hblk := h.block hk
  have ivIn : bytesAt s₂.mem ((Iv s₀).setWidth 64) 16 = Spec.Cbc.next (iv0 s₀) ((blks s₀).take k) := by
    rw [Proof.Cmac.bytesAt_frame f₂ callIv (by decide), a.mem,
      Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one hp.iv_sv) (by decide), h.iv]
    rfl
  have blkIn : bytesAt s₁.mem (blk s₀ k) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [a.mem, Proof.Cmac.bytesAt_frame (copy4Mem_frame _ _ _) (one (hp.blk_sv hk)) (by decide), hblk]
  have newBlk : bytesAt s₈.mem (blk s₀ k) 16 =
      Spec.Cbc.xor (Spec.Cbc.aesInvWith (R s₀) (bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)))
          ((blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk)))
        (Spec.Cbc.next (iv0 s₀) ((blks s₀).take k)) := by
    rw [mem₈, Proof.Cmac.bytesAt_frame f₇ (one (hp.blk_iv hk)) (by decide), m₄, xorIn4_bytes _ (hp.blk_iv hk),
      ivIn, ← hd, c.out, hd, ← UPre.sched_bytes hp big₁, ← aesInvWith_state, blkIn]
  have newIv : bytesAt s₈.mem ((Iv s₀).setWidth 64) 16 = (blks s₀)[k]'(by simp [Spec.Cbc.blocksAt]; exact hk) := by
    rw [mem₈, m₇, copy4Mem_bytes _ hp.iv_sv, m₄,
      Proof.Cmac.bytesAt_frame (Proof.Cmac.xor4Mem_frame _ _ _ _) (one (hp.blk_sv hk).symm) (by decide),
      Proof.Cmac.bytesAt_frame f₂ callSv (by decide), a.mem, copy4Mem_bytes _ (hp.blk_sv hk).symm, hblk]
  have hl : (outK (cbcMode false) s₀ k).length = k := by
    rw [outK, Mode.length_out]; simp [Spec.Cbc.blocksAt]; omega
  have outSucc :
      outK (cbcMode false) s₀ (k + 1) = outK (cbcMode false) s₀ k ++ [bytesAt s₈.mem (blk s₀ k) 16] := by
    rw [newBlk]
    simp only [outK, cbcMode_out, cbc, ciphOf, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, decrypt_snoc]
  refine ⟨esi₈, esp₈, by rw [rd₈, g₇.rd, rd₆, u₅.rd, g₄.rd, u₃.rd, c.rd, a.rd, h.rd],
    by rw [wr₈, g₇.wr, wr₆, u₅.wr, g₄.wr, u₃.wr, c.wr, a.wr, h.wr],
    by rw [mem₈]; exact h.frame.trans (stepFrame hk fStep), ?_, ?_⟩
  · rw [mem₈, hp.blocksAt_step hk fStep, h.data, ← mem₈, outSucc,
      set_prefix _ _ _ hl (by simp [Spec.Cbc.blocksAt]; exact hk)]
  · rw [newIv]
    simp only [chainK, cbcMode_chain, cts, Bool.false_eq_true, ite_false, take_succ_blks s₀ hk, next_snoc]

end VG.Proof.AesCbc.X86
