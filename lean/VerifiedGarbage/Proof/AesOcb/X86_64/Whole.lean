import VerifiedGarbage.Proof.AesOcb.X86_64.Pass

/-!
# AES-OCB on x86-64: the whole blocks (`whole`)

Untrusted: everything here is checked by Lean. `whole f pre post` runs the
first pass (each block XORed with its offset, `pre`), `f` on all the blocks
(`ENCIPHER` or `DECIPHER`), and the second pass from `Offset_0` again
(`post`), each pass also updating the checksum (`whole_ok`): block `k`
becomes `Offset_{k+1} ⊕ g(X_k ⊕ Offset_{k+1})`. The table of `L_j` is
outside what the passes and the call write.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Ocb (Block Cipher blockAtMem lAt ntz)
open VG.Proof.Ocb (offAt)
open VG.Proof.AesCcm.X86_64 (runBlock_append toNat_ofNat_of_lt imm_eq eval_e eval_ne)

/-- What `whole` writes: the offset and the checksum, `L_{ntz(i)}`, the
working space of the functions called, the stack below `SP` and the data. -/
abbrev wholeR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 16, 32⟩, ⟨W + BitVec.ofNat 64 96, 16⟩, wC W, below SP 8, ⟨D, n⟩]

theorem wholeR_mut {W SP D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wholeR W SP D n) m m') :
    Frame (mutR W SP D n) m m' := h.sub fun r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_self .., sub_wA (by decide)⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- The first `k` bytes of a buffer, as a buffer at the same place. -/
theorem DBuf.take' {K W SP : Addr} {s : State} {D : Addr} {n k : Nat} (h : DBuf K W SP s D n) (hk : k ≤ n) :
    DBuf K W SP s D k := by
  have := h.slice (a := 0) (k := k) (by omega)
  rwa [BitVec.add_zero] at this

/-- The `m` blocks of the data. -/
theorem dataArgs_ok {W D : Addr} {t : State} (h15 : t.gpr .r15 = W) {m : Nat}
    (hdata : t.mem.readW (W + BitVec.ofNat 64 208) 64 = D) (h13 : t.gpr .r13 = BitVec.ofNat 64 m)
    (r : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8) :
    ArgsOk [ld .rdx .r15 dataO, mvr .rcx .r13] t D m := by
  refine ⟨_, by orun [h15, hdata, r], ?_, ?_, fun r h1 h2 _ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13]
  · simp only [gpr_setReg, h1, h2, ite_false]
  all_goals rfl

/-- What `whole` leaves. -/
structure WholePost (K W SP D : Addr) (n m : Nat) (O0 l : Block) (Z : Nat → Block) (ck : Block) (t t' : State) : Prop where
  env : Env K W SP t'
  frame : Frame (wholeR W SP D n) t.mem t'.mem
  rd : t'.rd = t.rd
  wr : t'.wr = t.wr
  blk : ∀ k < m, blockAtMem t'.mem (D + BitVec.ofNat 64 (16 * k)) = Z k ^^^ offAt O0 l (k + 1)
  ofs : blockAtMem t'.mem (W + BitVec.ofNat 64 ofsO) = offAt O0 l m
  ck : blockAtMem t'.mem (W + BitVec.ofNat 64 ckO) = ck

theorem whole_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0) {G : List Byte → Cipher}
    (hcall : ∀ {s s' : State} {K D S : Addr} {R n : Nat}, BPost f s K D S R n s' → ∀ i < n,
      blockAtMem s'.mem (D + BitVec.ofNat 64 (16 * i)) = G (bytesAt s.mem K (16 * (R + 1)))
        (blockAtMem s.mem (D + BitVec.ofNat 64 (16 * i))))
    {pre post : List Instr} {fC1 fC2 : Block → Block → Block → Block} {ckF1 ckF2 : Nat → Block}
    (hB1 : BodyOk pre (fun b o => b ^^^ o) fC1) (hB2 : BodyOk post (fun b o => b ^^^ o) fC2)
    {K W SP : Addr} (L : Lay K W SP) {t : State} (E : Env K W SP t) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    {D : Addr} {n m : Nat} (hD : DBuf K W SP t D n) (hmn : 16 * m ≤ n) (hm0 : 0 < m)
    {O0 l : Block} (hdata : t.mem.readW (W + BitVec.ofNat 64 dataO) 64 = D) (h13 : t.gpr .r13 = BitVec.ofNat 64 m)
    (hrnd : t.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    (hofs : blockAtMem t.mem (W + BitVec.ofNat 64 ofsO) = O0) (ho0 : blockAtMem t.mem (W + BitVec.ofNat 64 o0O) = O0)
    (hck : blockAtMem t.mem (W + BitVec.ofNat 64 ckO) = ckF1 0)
    (hT : ∃ M, Tbl W l M t.mem ∧ m ≤ M)
    (hckF1 : ∀ i, ckF1 (i + 1) = fC1 (ckF1 i) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i))) (offAt O0 l (i + 1)))
    (hckF2₀ : ckF2 0 = ckF1 m)
    (hckF2 : ∀ i, ckF2 (i + 1) = fC2 (ckF2 i)
      (G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * i)) ^^^ offAt O0 l (i + 1)))
      (offAt O0 l (i + 1))) :
    WP isa (whole b pre post) t (WholePost K W SP D n m O0 l
      (fun k => G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)))
      (ckF2 m) t) := by
  have hDm := hD.take' hmn
  have r₁ : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 208) 8 := E.perm.wR (by decide)
  simp only [dataO] at hdata
  have hw := hD.wrap
  -- the first pass
  have start : ∀ {u : State}, Env K W SP u → u.mem.readW (W + BitVec.ofNat 64 208) 64 = D →
      u.gpr .r13 = BitVec.ofNat 64 m → ∃ u₁, runBlock isa [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)] u =
        some u₁ ∧ u₁.gpr .rbx = D ∧ u₁.gpr .r12 = BitVec.ofNat 64 m ∧ u₁.gpr .rbp = BitVec.ofNat 64 1 ∧
        Env K W SP u₁ ∧ (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rbp → u₁.gpr r = u.gpr r) ∧ u₁.mem = u.mem ∧
        u₁.rd = u.rd ∧ u₁.wr = u.wr := fun {u} Eu hd h13u => by
    have r : InRegions (u.rd ++ u.wr) (W + BitVec.ofNat 64 208) 8 := Eu.perm.wR (by decide)
    obtain ⟨u₁, run, h1, h2, h3, g, m₁, rd, wr⟩ : ∃ u₁, runBlock isa
        [ld .rbx .r15 dataO, mvr .r12 .r13, .mov .rbp (.imm 1)] u = some u₁ ∧ u₁.gpr .rbx = D ∧
        u₁.gpr .r12 = BitVec.ofNat 64 m ∧ u₁.gpr .rbp = BitVec.ofNat 64 1 ∧
        (∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .rbp → u₁.gpr r = u.gpr r) ∧ u₁.mem = u.mem ∧ u₁.rd = u.rd ∧
        u₁.wr = u.wr := by
      refine ⟨_, by orun [Eu.r15, r, hd], ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
      · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq]
      · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, h13u]
      · simp only [gpr_setReg, ite_true, sext1]
      · simp only [gpr_setReg, h1, h2, h3, ite_false]
      all_goals rfl
    exact ⟨u₁, run, h1, h2, h3, Eu.keep (fun r hr => g r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      rd wr, g, m₁, rd, wr⟩
  obtain ⟨s₁, run₁, rbx₁, r12₁, rbp₁, E₁, g₁, m₁, rd₁, wr₁⟩ := start E hdata h13
  have hD₁ : DBuf K W SP s₁ D (16 * m) := hDm.of_eq rd₁ wr₁
  have C₁ : PCtx K W SP D m l s₁ := ⟨L, hD₁, by rw [m₁]; exact hT⟩
  unfold whole
  refine WP.seq (WP.of_runBlock ⟨s₁, run₁, ?_⟩)
  refine WP.seq (WP.mono (pass_ok hB1 (ckF := ckF1) (fun i _ => by rw [hckF1, m₁]) C₁ E₁ hm0 rbx₁ rbp₁ r12₁
    (by rw [m₁, hofs]) (by rw [m₁, hck])) fun s₂ P₂ => ?_)
  -- the slots and the blocks of `W` that the pass does not write
  have kP : ∀ {d : Nat}, (d + 8 ≤ 16 ∨ 48 ≤ d) → d + 8 ≤ 3584 →
      s₂.mem.readW (W + BitVec.ofNat 64 d) 64 = s₁.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun h₁ h₂ => P₂.frame.readW (r := ⟨W + BitVec.ofNat 64 _, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) h₂ (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) h₂ (by decide)
      · exact (hD₁.w.sub_left (Region.sub_prefix (Nat.le_refl _))).symm.sub_left (Lay.wSub h₂)) (by decide)
  have h15₂ : s₂.gpr .r15 = W := P₂.env.r15
  have h13₂ : s₂.gpr .r13 = BitVec.ofNat 64 m := by
    rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₁ _ (by decide) (by decide) (by decide), h13]
  have hdata₂ : s₂.mem.readW (W + BitVec.ofNat 64 208) 64 = D := by rw [kP (by decide) (by decide), m₁, hdata]
  have hrnd₂ : s₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [kP (by decide) (by decide), m₁, hrnd]
  have hD₂ : DBuf K W SP s₂ D (16 * m) := hD₁.of_eq P₂.rd P₂.wr
  refine WP.seq (WP.mono (callBlocks_ok (f := f) (b := b) ok nosp depth L P₂.env hR hrnd₂
    (dataArgs_ok h15₂ hdata₂ h13₂ (P₂.env.perm.wR (by decide))) (dstD hD₂)) fun s₃ P₃ => ?_)
  have E₃ : Env K W SP s₃ := P₂.env.of_saved P₃.saved P₃.rd P₃.wr
  have kC : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨D, 16 * m⟩ → (⟨Q, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩ →
      (below SP 8).Disjoint ⟨Q, 16⟩ → blockAtMem s₃.mem Q = blockAtMem s₂.mem Q := fun h₁ h₂ h₃ =>
    blockAtMem_frame P₃.frame fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · rw [P₂.env.rsp]; exact h₃.symm
  have kWP : ∀ {d : Nat}, (d + 16 ≤ 16 ∨ (48 ≤ d ∧ d + 16 ≤ 512)) →
      blockAtMem s₃.mem (W + BitVec.ofNat 64 d) = blockAtMem s₁.mem (W + BitVec.ofNat 64 d) := fun hd => by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by omega))).symm) (L.w_w (.inl (by omega)) (by omega) (by decide))
      (L.stk_w' (by omega)), blockAtMem_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact L.w_w (a := _) (d := 16) (k := 16) (by omega) (by omega) (by decide)
      · exact L.w_w (a := _) (d := 32) (k := 16) (by omega) (by omega) (by decide)
      · exact (hD₁.w.sub_right (Lay.wSub (by omega))).symm)]
  have o0₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 o0O) = O0 := by rw [kWP (by decide), m₁, ho0]
  -- the table, after the first pass and the call
  have tW : ∀ r ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩],
      (wT W).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact L.wT_w (by decide)
    · exact L.wT_w (by decide)
    · exact hD₁.w.symm.sub_left (Lay.wSub (by decide))
  obtain ⟨M, T, hM⟩ := hT
  have T₃ : Tbl W l M s₃.mem := ((by rw [m₁]; exact T : Tbl W l M s₁.mem).frame P₂.frame tW).frame P₃.frame
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hD₂.w.symm.sub_left (Lay.wSub (by decide))
      · exact L.w_w (.inr (by decide)) (by decide) (by decide)
      · rw [P₂.env.rsp]; exact (L.stk_w' (by decide)).symm
  -- `Offset_0` again
  obtain ⟨s₄a, run₄a, B₄⟩ := copy16_ok (s := s₃) (a := o0O) (d := ofsO) E₃.r15 (E₃.perm.wR (by decide))
    (E₃.perm.wR (by decide)) (E₃.perm.wW (by decide)) (E₃.perm.wW (by decide))
  have E₄a : Env K W SP s₄a := E₃.keep (fun r hr => B₄.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    B₄.rd B₄.wr
  have hdata₄ : s₄a.mem.readW (W + BitVec.ofNat 64 208) 64 = D := by
    rw [B₄.frame.readW (r := ⟨W + BitVec.ofNat 64 208, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)) (by decide),
      P₃.frame.readW (r := ⟨W + BitVec.ofNat 64 208, 8⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (hD₂.w.sub_right (Lay.wSub (by decide))).symm
      · exact L.w_w (.inl (by decide)) (by decide) (by decide)
      · rw [P₂.env.rsp]; exact (L.stk_w' (by decide)).symm) (by decide), hdata₂]
  have h13₄ : s₄a.gpr .r13 = BitVec.ofNat 64 m := by rw [B₄.gpr _ (by decide), P₃.saved _ (by decide), h13₂]
  obtain ⟨s₄, run₄, rbx₄, r12₄, rbp₄, E₄, g₄, m₄, rd₄, wr₄⟩ := start E₄a hdata₄ h13₄
  have hD₄ : DBuf K W SP s₄ D (16 * m) := hD₂.of_eq (by rw [rd₄, B₄.rd, P₃.rd]) (by rw [wr₄, B₄.wr, P₃.wr])
  have kB₄ : ∀ {Q : Addr}, (⟨Q, 16⟩ : Region).Disjoint ⟨W, 3584⟩ → blockAtMem s₄.mem Q = blockAtMem s₃.mem Q :=
    fun hQ => by
      rw [m₄]; exact blockAtMem_frame B₄.frame fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hQ.sub_right (Lay.wSub (by decide))
  have hK : bytesAt s₂.mem K (16 * (R + 1)) = bytesAt t.mem K (16 * (R + 1)) := by
    have hRb : 16 * (R + 1) ≤ 256 := by rcases hR with rfl | rfl | rfl <;> decide
    rw [Proof.AesCcm.X86_64.bytesAt_frame P₂.frame (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact (L.k_w.sub_left (Region.sub_prefix hRb)).sub_right (Lay.wSub (by decide))
      · exact hD₁.k.sub_left (Region.sub_prefix hRb)) (by omega), m₁]
  have X₄ : ∀ k < m, blockAtMem s₄.mem (D + BitVec.ofNat 64 (16 * k)) =
      G (bytesAt t.mem K (16 * (R + 1))) (blockAtMem t.mem (D + BitVec.ofNat 64 (16 * k)) ^^^ offAt O0 l (k + 1)) :=
    fun k hk => by
      rw [kB₄ (hD₂.slice (a := 16 * k) (k := 16) (by omega)).w, hcall P₃ k hk, hK, P₂.blk k hk, m₁]
  have ck₃ : blockAtMem s₃.mem (W + BitVec.ofNat 64 ckO) = ckF2 0 := by
    rw [kC ((hD₂.w.sub_right (Lay.wSub (by decide))).symm) (L.w_w (.inl (by decide)) (by decide) (by decide))
      (L.stk_w' (by decide)), P₂.ck, hckF2₀]
  have T₄ : Tbl W l M s₄.mem := by
    rw [m₄]; exact T₃.frame B₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact L.wT_w (by decide)
  have C₄ : PCtx K W SP D m l s₄ := ⟨L, hD₄, M, T₄, hM⟩
  refine WP.seq (WP.of_runBlock ⟨s₄, by rw [runBlock_append, run₄a, Option.bind_some, run₄], ?_⟩)
  refine WP.mono (pass_ok hB2 (ckF := ckF2) (fun i hi => by rw [hckF2, X₄ i hi]) C₄ E₄ hm0 rbx₄ rbp₄ r12₄
    (by rw [m₄, B₄.val, o0₃]) (by
      rw [m₄, blockAtMem_frame B₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact L.w_w (.inr (by decide)) (by decide) (by decide)), ck₃]))
    fun s₅ P₅ => ?_
  have subW : ∀ r ∈ [(⟨W + BitVec.ofNat 64 ofsO, 16⟩ : Region), ⟨W + BitVec.ofNat 64 ckO, 16⟩, ⟨D, 16 * m⟩],
      ∃ r' ∈ wholeR W SP D n, Region.Sub r r' := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 32) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩
    · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix hmn⟩
  refine ⟨P₅.env, ?_, by rw [P₅.rd, rd₄, B₄.rd, P₃.rd, P₂.rd, rd₁], by rw [P₅.wr, wr₄, B₄.wr, P₃.wr, P₂.wr, wr₁],
    fun k hk => ?_, P₅.ofs, P₅.ck⟩
  · rw [← m₁]
    refine (P₂.frame.sub subW).trans ((P₃.frame.sub fun r hr => ?_).trans ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨D, n⟩, by simp, Region.sub_prefix hmn⟩
      · exact ⟨wC W, by simp, sub_wC (by decide) (by decide)⟩
      · rw [P₂.env.rsp]; exact ⟨below SP 8, by simp, fun _ h => h⟩
    · have F₅ := P₅.frame
      rw [m₄] at F₅
      exact (B₄.frame.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_cons_self .., Offset.sub W (d := 16) (n := 16) (e := 16) (k := 32) (by decide) (by decide)⟩).trans
        (F₅.sub subW)
  · rw [P₅.blk k hk, X₄ k hk]

end VG.Proof.AesOcb.X86_64
