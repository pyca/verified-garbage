import VerifiedGarbage.Proof.Blowfish.X86_64.Block

/-!
# The ECB functions

`ecb_correct`: every block becomes its encryption or decryption, one at a
time, through the working space.
-/

namespace VG.Proof.Blowfish.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Blowfish.X86_64 VG.Spec.Blowfish VG.Proof.Blowfish

/-- A block's encryption (`up`) or decryption. -/
def blockOut (K : Schedule) (up : Bool) (b : Block) : Block :=
  if up then encryptBlock K b else decryptBlock K b

theorem blockOut_eq (K : Schedule) (up : Bool) (b : Block) :
    blockOut K up b = encodeBlock (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).1
      (feistel K (ord up) (decodeWord b 0) (decodeWord b 4)).2 := by
  cases up <;> rfl

/-- The block at `p`. -/
abbrev wAt (p : Addr) (b : Nat) : Addr := p + BitVec.ofNat 64 (8 * b)

theorem constants_run (t : State) :
    ∃ t', runBlock isa constants t = some t' ∧ t'.xmm onesReg = wordsOf 1 ∧ t'.xmm sixteenReg = wordsOf 16 ∧
      t'.xmm lowReg = wordsOf 0xFF ∧
      (∀ d, d ≠ onesReg → d ≠ sixteenReg → d ≠ lowReg → d ≠ tmp → t'.xmm d = t.xmm d) ∧
      (∀ g, g ≠ .r11 → t'.gpr g = t.gpr g) ∧ Upd t t' := by
  obtain ⟨t₁, r₁, v₁, k₁, g₁, e₁⟩ := loadConst_run t (dst := onesReg) (by decide) (wordsOf 1)
  obtain ⟨t₂, r₂, v₂, k₂, g₂, e₂⟩ := loadConst_run t₁ (dst := sixteenReg) (by decide) (wordsOf 16)
  obtain ⟨t₃, r₃, v₃, k₃, g₃, e₃⟩ := loadConst_run t₂ (dst := lowReg) (by decide) (wordsOf 0xFF)
  refine ⟨t₃, cat_run (cat_run r₁ r₂) r₃, by rw [k₃ _ (by decide) (by decide), k₂ _ (by decide) (by decide), v₁],
    by rw [k₃ _ (by decide) (by decide), v₂], v₃, fun d h1 h2 h3 h4 => by rw [k₃ _ h3 h4, k₂ _ h2 h4, k₁ _ h1 h4],
    fun g h => by rw [g₃ _ h, g₂ _ h, g₁ _ h], ?_⟩
  have u : ∀ {a c : State}, a = { c with gpr := a.gpr, xmm := a.xmm } → Upd c a := fun h => by
    unfold Upd; rw [h]
  exact Upd.trans (u e₃) (Upd.trans (u e₂) (u e₁))

theorem blockAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (⟨p, 8⟩ : Region).Disjoint r) : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  simp only [blockAt, Vector.getElem_ofFn]
  exact hf.bytes (R := ⟨p, 8⟩) hd (by show 8 ≤ 2 ^ 64; decide) hi

/-- What ECB may assume: the schedule readable, the `n` blocks and the
working space writable, apart. -/
structure EcbPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rdi, 4168⟩]
  wr : s.wr = [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 256⟩]
  keyData : (⟨s.gpr .rdi, 4168⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  keyBuf : (⟨s.gpr .rdi, 4168⟩ : Region).Disjoint ⟨s.gpr .rcx, 256⟩
  dataBuf : (⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩ : Region).Disjoint ⟨s.gpr .rcx, 256⟩
  retData : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩
  retBuf : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rcx, 256⟩
  fit : (s.gpr .rsi).toNat + 8 * (s.gpr .rdx).toNat ≤ 2 ^ 64

/-- The loop's fixed facts: the state after the constants. -/
structure LoopEnv (S D B : Addr) (n : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [⟨S, 4168⟩]
  wr : s₀.wr = [⟨D, 8 * n⟩, ⟨B, 256⟩]
  keyData : (⟨S, 4168⟩ : Region).Disjoint ⟨D, 8 * n⟩
  keyBuf : (⟨S, 4168⟩ : Region).Disjoint ⟨B, 256⟩
  dataBuf : (⟨D, 8 * n⟩ : Region).Disjoint ⟨B, 256⟩
  fit : D.toNat + 8 * n ≤ 2 ^ 64
  rdi : s₀.gpr .rdi = S
  rcx : s₀.gpr .rcx = B
  ones : s₀.xmm onesReg = wordsOf 1
  sixteen : s₀.xmm sixteenReg = wordsOf 16
  low : s₀.xmm lowReg = wordsOf 0xFF

/-- After `k` blocks. -/
structure EInv (S D B : Addr) (n : Nat) (up : Bool) (s₀ : State) (k : Nat) (u : State) : Prop where
  le : k ≤ n
  rsi : u.gpr .rsi = wAt D k
  rdx : u.gpr .rdx = BitVec.ofNat 64 (n - k)
  rdi : u.gpr .rdi = S
  rcx : u.gpr .rcx = B
  gpr : ∀ g, g ≠ .rsi → g ≠ .rdx → g ≠ .r11 → g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → u.gpr g = s₀.gpr g
  xmm : ∀ d, d ∉ cXRegs → u.xmm d = s₀.xmm d
  done : ∀ b < k, blockAt u.mem (wAt D b) = blockOut (scheduleAt s₀.mem S) up (blockAt s₀.mem (wAt D b))
  rest : ∀ b, k ≤ b → b < n → blockAt u.mem (wAt D b) = blockAt s₀.mem (wAt D b)
  frame : Frame [⟨D, 8 * n⟩, ⟨B, 256⟩] s₀.mem u.mem
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr

theorem ecb_step {S D B : Addr} {n : Nat} {up : Bool} {s₀ : State} (L : LoopEnv S D B n s₀) {k : Nat}
    (hk : k < n) {u : State} (I : EInv S D B n up s₀ k u) :
    WP isa (.seq (.block loadBlock) (.seq (cipher .rdi up)
      (.block (storeBlock ++ ([.alu .add .rsi (.imm 8), .alu .sub .rdx (.imm 1)] : List Instr))))) u
      (fun u' => EInv S D B n up s₀ (k + 1) u' ∧ u'.zf = some (BitVec.ofNat 64 (n - (k + 1)) == 0)) := by
  have fit := L.fit
  have hrdw : u.rd ++ u.wr = [⟨S, 4168⟩, ⟨D, 8 * n⟩, ⟨B, 256⟩] := by rw [I.rd, I.wr, L.rd, L.wr]; rfl
  have dR : (⟨D, 8 * n⟩ : Region) ∈ u.wr := by rw [I.wr, L.wr]; exact List.mem_cons_self
  have bR : (⟨B, 256⟩ : Region) ∈ u.wr := by rw [I.wr, L.wr]; exact List.mem_cons_of_mem _ List.mem_cons_self
  have sR : (⟨S, 4168⟩ : Region) ∈ u.rd ++ u.wr := by rw [hrdw]; exact List.mem_cons_self
  -- the block in
  obtain ⟨u₁, r₁, l₁, h₁, k₁, g₁, up₁⟩ := loadBlock_run u (wAt D k) I.rsi fun o ho =>
    ⟨_, List.mem_append_right _ dR, by rw [Offset.add_add]; exact Offset.contains_base D (by omega) (by omega)⟩
  apply WP.seq
  refine WP.of_runBlock ⟨u₁, r₁, ?_⟩
  have m₁ : u₁.mem = u.mem := by rw [up₁]
  have hK : scheduleAt u.mem S = scheduleAt s₀.mem S :=
    scheduleAt_eq_of_frame S I.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact L.keyData
      · exact L.keyBuf
  have CE : CipherEnv .rdi S u₁ := by
    have rdw₁ : u₁.rd ++ u₁.wr = u.rd ++ u.wr := by rw [up₁]
    refine ⟨⟨by rw [g₁ _ (by decide), I.rdi], by decide, by decide, by decide, fun off h => ?_,
      by rw [k₁ _ (by decide) (by decide), I.xmm _ (by decide), L.ones],
      by rw [k₁ _ (by decide) (by decide), I.xmm _ (by decide), L.sixteen],
      by rw [k₁ _ (by decide) (by decide), I.xmm _ (by decide), L.low]⟩, by decide, by decide, fun i hi => ?_⟩
    · rw [rdw₁]; exact ⟨_, sR, Offset.contains_base S (by omega) (by omega)⟩
    · rw [rdw₁]; exact ⟨_, sR, Offset.contains_base S (by omega) (by omega)⟩
  apply WP.seq
  refine WP.mono (cipher_run CE up) fun u₂ ⟨c₁, c₂, O⟩ => ?_
  have up₂ : Upd u u₂ := Upd.trans O.upd up₁
  have wr₂ : u₂.wr = u.wr := by rw [up₂]
  have m₂ : u₂.mem = u.mem := by rw [up₂]
  have gu : ∀ g, g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → g ≠ .r11 → u₂.gpr g = u.gpr g :=
    fun g h1 h2 h3 h4 h5 => by rw [O.gpr _ h1 h2 h3 h4 h5, g₁ _ h5]
  have subK : Region.Sub ⟨wAt D k, 8⟩ ⟨D, 8 * n⟩ := Offset.sub_base D (by omega)
  have subB : Region.Sub ⟨B, 16⟩ ⟨B, 256⟩ := Region.sub_prefix (by omega)
  have dKB : (⟨wAt D k, 8⟩ : Region).Disjoint ⟨B, 16⟩ := (L.dataBuf.sub_left subK).sub_right subB
  have SE : StoreEnv (wAt D k) B u₂ := by
    refine ⟨by rw [gu _ (by decide) (by decide) (by decide) (by decide) (by decide), I.rsi],
      by rw [gu _ (by decide) (by decide) (by decide) (by decide) (by decide), I.rcx],
      ⟨_, by rw [wr₂]; exact dR, Offset.contains_base D (by omega) (by omega)⟩,
      ⟨_, by rw [wr₂]; exact bR, by simp [Region.Contains]⟩, sep_of_disjoint dKB, sep_of_disjoint dKB.symm⟩
  obtain ⟨u₃, r₃, b₃, f₃, g₃, e₃⟩ := storeBlock_run SE
  obtain ⟨u₄, r₄, a₄, k₄, x₄, up₄⟩ := add_imm_run u₃ .rsi 8
  obtain ⟨u₅, r₅, a₅, z₅, k₅, x₅, up₅⟩ := sub_imm_run u₄ .rdx 1
  refine WP.of_runBlock ⟨u₅, ?_, ?_, ?_⟩
  · refine cat_run r₃ ?_
    rw [runBlock_cons, r₄, runStep_some, runBlock_cons, r₅, runStep_some, runBlock_nil]
  have m₅ : u₅.mem = u₃.mem := by rw [up₅, up₄]
  have g₅ : ∀ g, g ≠ .rsi → g ≠ .rdx → u₅.gpr g = u₃.gpr g := fun g h1 h2 => by rw [k₅ _ h2, k₄ _ h1]
  have hgk : ∀ g, g ≠ .rsi → g ≠ .rdx → g ≠ .r11 → g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → u₅.gpr g = u.gpr g :=
    fun g h1 h2 h3 h4 h5 h6 h7 => by rw [g₅ _ h1 h2, g₃ _ h3, gu _ h4 h5 h6 h7 h3]
  have other : ∀ b, b < n → b ≠ k → blockAt u₅.mem (wAt D b) = blockAt u.mem (wAt D b) := fun b hb hne => by
    rw [m₅, blockAt_frame f₃ fun r hr => ?_, m₂]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint D (by omega) (by omega) (by omega)
    · exact (L.dataBuf.sub_left (Offset.sub_base D (by omega))).sub_right subB
  refine ⟨by omega, ?_, ?_, ?_, ?_,
    fun g h1 h2 h3 h4 h5 h6 h7 => by rw [hgk _ h1 h2 h3 h4 h5 h6 h7, I.gpr _ h1 h2 h3 h4 h5 h6 h7], fun d hd => ?_, fun b hb => ?_, fun b h1 h2 => ?_, ?_, ?_, ?_⟩
  · rw [k₅ _ (by decide), a₄, g₃ _ (by decide), gu _ (by decide) (by decide) (by decide) (by decide) (by decide),
      I.rsi, wAt, wAt, show BitVec.signExtend 64 (8 : BitVec 32) = BitVec.ofNat 64 8 from rfl, Offset.add_add]
    congr 2
  · rw [a₅, k₄ _ (by decide), g₃ _ (by decide),
      gu _ (by decide) (by decide) (by decide) (by decide) (by decide), I.rdx]
    apply BitVec.eq_of_toNat_eq; simp; omega
  · rw [hgk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I.rdi]
  · rw [hgk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), I.rcx]
  · rw [x₅, x₄, show u₃.xmm = u₂.xmm by rw [e₃], O.xmm _ hd, k₁ _ (fun e => hd (by rw [e]; decide))
      (fun e => hd (by rw [e]; decide)), I.xmm _ hd]
  · by_cases hbk : b = k
    · subst hbk
      refine blockAt_eq _ _ _ fun i hi => ?_
      rw [m₅, b₃ i hi, c₁, c₂, l₁, h₁, show u₁.mem = u.mem from m₁, hK,
        I.rest b (by omega) hk, blockOut_eq]
    · rw [other b (by omega) hbk]; exact I.done b (by omega)
  · rw [other b h2 (by omega)]; exact I.rest b (by omega) h2
  · rw [m₅]
    refine I.frame.trans ?_
    rw [← m₂]
    refine Frame.sub f₃ fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, subK⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, subB⟩
  · rw [show u₅.rd = u₂.rd by rw [up₅, up₄, e₃], up₂, I.rd]
  · rw [show u₅.wr = u₂.wr by rw [up₅, up₄, e₃], up₂, I.wr]
  · rw [z₅, k₄ _ (by decide), g₃ _ (by decide), gu _ (by decide) (by decide) (by decide) (by decide) (by decide),
      I.rdx, show BitVec.ofNat 64 (n - k) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (n - (k + 1)) from by
        apply BitVec.eq_of_toNat_eq; simp; omega]

/-- What ECB guarantees. -/
structure EcbPost (up : Bool) (s s' : State) : Prop where
  done : ∀ b < (s.gpr .rdx).toNat, blockAt s'.mem (wAt (s.gpr .rsi) b) =
    blockOut (scheduleAt s.mem (s.gpr .rdi)) up (blockAt s.mem (wAt (s.gpr .rsi) b))
  gpr : ∀ g, g ≠ .rsi → g ≠ .rdx → g ≠ .r11 → g ≠ .rax → g ≠ .r8 → g ≠ .r9 → g ≠ .r10 → s'.gpr g = s.gpr g
  frame : Frame [⟨s.gpr .rsi, 8 * (s.gpr .rdx).toNat⟩, ⟨s.gpr .rcx, 256⟩] s.mem s'.mem

theorem exec_test (t : State) (d : Reg) :
    exec (.alu .test d (.reg d)) t = some (arithFlags t (t.gpr d &&& t.gpr d) false false) := rfl

theorem ecb_correct (up : Bool) {s : State} (h : EcbPre s) : WP isa (ecb up) s (EcbPost up s) := by
  have fit := h.fit
  let n := (s.gpr .rdx).toNat
  let D := s.gpr .rsi
  let S := s.gpr .rdi
  let B := s.gpr .rcx
  rw [Impl.Blowfish.X86_64.ecb]
  apply WP.seq
  obtain ⟨s₀, r₀, o₀, x₀, l₀, k₀, g₀, up₀⟩ := constants_run s
  refine WP.of_runBlock ⟨s₀, r₀, ?_⟩
  have m₀ : s₀.mem = s.mem := by rw [up₀]
  have L : LoopEnv S D B n s₀ := by
    refine ⟨by rw [up₀]; exact h.rd, by rw [up₀]; exact h.wr, h.keyData, h.keyBuf, h.dataBuf, fit,
      g₀ _ (by decide), g₀ _ (by decide), o₀, x₀, l₀⟩
  apply WP.seq
  let s₁ := arithFlags s₀ (s₀.gpr .rdx &&& s₀.gpr .rdx) false false
  refine WP.of_runBlock ⟨s₁, by rw [runBlock_cons, exec_test, runStep_some, runBlock_nil], ?_⟩
  have g₁ : s₁.gpr = s₀.gpr := by simp only [s₁, gpr_arithFlags]
  have I0 : EInv S D B n up s₀ 0 s₁ := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, fun g _ _ _ _ _ _ _ => by rw [g₁], fun d _ => rfl,
      fun b hb => by omega, fun b _ _ => rfl, Frame.refl _ _, rfl, rfl⟩
    · rw [g₁, g₀ _ (by decide)]; simp [wAt, D]
    · rw [g₁, g₀ _ (by decide)]; simp [n]
    · rw [g₁, g₀ _ (by decide)]
    · rw [g₁, g₀ _ (by decide)]
  have fin : ∀ u, EInv S D B n up s₀ n u → EcbPost up s u := fun u I => by
    refine ⟨fun b hb => ?_, fun g h1 h2 h3 h4 h5 h6 h7 => ?_, ?_⟩
    · rw [I.done b hb, m₀]
    · rw [I.gpr _ h1 h2 h3 h4 h5 h6 h7, g₀ _ h3]
    · rw [← m₀]; exact I.frame
  have zf₁ : s₁.zf = some (s.gpr .rdx == 0) := by
    simp only [s₁, zf_arithFlags, g₀ _ (show Reg.rdx ≠ .r11 by decide), BitVec.and_self]
  apply WP.ite (s.gpr .rdx == 0) zf₁
  · intro hz
    have hn : n = 0 := by
      have := congrArg BitVec.toNat (beq_iff_eq.mp hz)
      simpa [n] using this
    apply WP.block_nil
    exact fin s₁ (hn ▸ I0)
  · intro hz
    have hn : 0 < n := by
      have : s.gpr .rdx ≠ 0 := by simpa using hz
      have : (s.gpr .rdx).toNat ≠ 0 := fun e => this (BitVec.eq_of_toNat_eq e)
      omega
    refine WP.mono (WP.loop (M := isa) (Q := EInv S D B n up s₀ n)
      (fun m u => ∃ k, k < n ∧ m = n - k ∧ EInv S D B n up s₀ k u) ?_ n s₁ ⟨0, hn, rfl, I0⟩) fin
    intro m u ⟨k, hk, hm, I⟩
    refine WP.mono (ecb_step L hk I) fun u' ⟨I', zu⟩ => ?_
    have ev : isa.eval .ne u' = some (!(BitVec.ofNat 64 (n - (k + 1)) == 0)) := by
      show u'.zf.map (!·) = _; rw [zu]; rfl
    by_cases e : k + 1 = n
    · left
      refine ⟨by rw [ev, e, Nat.sub_self]; rfl, e ▸ I'⟩
    · right
      have nz : BitVec.ofNat 64 (n - (k + 1)) ≠ 0 := by
        intro h'; have := congrArg BitVec.toNat h'; simp at this; omega
      exact ⟨by rw [ev, show (BitVec.ofNat 64 (n - (k + 1)) == 0) = false from beq_false_of_ne nz]; rfl,
        n - (k + 1), by omega, k + 1, by omega, rfl, I'⟩

end VG.Proof.Blowfish.X86_64
