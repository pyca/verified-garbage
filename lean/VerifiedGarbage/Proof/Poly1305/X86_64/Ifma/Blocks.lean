import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Final
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks

/-!
# Poly1305 on x86-64 with AVX-512 IFMA: `vg_poly1305_blocks_ifma`

The whole function: with fewer than 16 blocks it calls
`vg_poly1305_blocks_avx2`; otherwise it absorbs the blocks eight at a time
(see `Impl/Poly1305/X86_64/Ifma.lean`), reduces the accumulator with
`vg_poly1305_blocks`'s code, and calls `vg_poly1305_blocks` for the last
`n mod 8`.

As for AVX-512 (`Avx512/Blocks.lean`), the vector code computes the right
numbers only if the accumulator on entry is below `2¹⁹⁴`, which holds whenever
the state represents a message: each block's effect on the vector registers
is established under that assumption, and its execution without it (`guard`).
-/

namespace VG.Proof.Poly1305.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Ifma
open VG.Impl.Poly1305.X86_64 (at_ save restore reduce)
open VG.Proof.Poly1305.X86_64 (off off_eq st nb bp R0 R1 Rn A0 H2 blks blkAddr hR wR sR sub_sR Saved save_ok
  reduce_ok storeRestore_ok storeH_frame storeH_saved storeH_acc key_frame clamp_key leNum_acc off_24
  toNat_ofNat_lt blks_zero)
open VG.Proof.Poly1305.X86_64.Avx2 (guard Post TailPre tail_ok done_ok cs_ne mxMem mxMem_read mxMem_frame
  mxMem_mx mx_hi mx_bits H2_lt bytesAt_frame vec vec_trans vec_gpr vec_mem vec_rd vec_wr vec_keep
  mxcsrIn_ok mxcsrOut_ok xi xr_xi)
open VG.Proof.Poly1305.X86_64.Avx512 (APre qz VKeep MemOK rcx_val and7_toNat grp_sub ctx_of grp_bytes
  absorb_grp add128 rcx_ok adv_ok)
open VG.Spec.Poly1305 (P leNum bytesAt accumulate Repr clamp)
open VG.Proof.Poly1305 (absorbAll)

/-! ## Executions -/

theorem vecs_ok {ld : Bool} {l : List Instr} {σ : Sym} {s : State} (h : Sym.init.run ld l = some σ)
    (hc : ld = true → Ctx s) : WP isa (.block l) s fun s' => GK s s' :=
  WP.mono (run_ok hc h) fun _ h => GK.of_vec h.eq

theorem seq_gk {a b : List Instr} {s : State} (ha : WP isa (.block a) s (GK s))
    (hb : ∀ s', GK s s' → WP isa (.block b) s' (GK s')) : WP isa (.block (a ++ b)) s (GK s) :=
  WP.block_append (WP.mono ha fun s' g => WP.mono (hb s' g) fun _ g' => g.trans g')

theorem loadYG_exec {R : Nat} {s : State} (hE : EndCtx R s) {d : Nat} (h₁ : 56 ≤ d) (h₂ : d + 24 ≤ 120) :
    WP isa (.block (loadYG fun i => at_ .rdi (d + 8 * i))) s (GK s) :=
  WP.mono (loadYG_ok s d (region_ok hE.ctx d h₁ h₂)) fun _ ⟨_, o, m, k⟩ => GK.of_vk k o m

theorem splitG_exec (s : State) : WP isa (.block splitG) s (GK s) :=
  WP.mono (splitG_ok s) fun _ ⟨_, _, _, o, m, k⟩ => GK.of_vk k o m

theorem setMulFold_exec {R : Nat} {seg fold : List Instr} {σ τ : Sym} {s : State} (hE : EndCtx R s)
    (h₁ : Sym.init.run true seg = some σ) (h₂ : Sym.init.run false fold = some τ) :
    WP isa (.block (seg ++ mul ++ fold)) s (GK s) :=
  seq_gk (seq_gk (vecs_ok h₁ fun _ => hE.ctx) fun _ g => vecs_ok mulS_eq fun _ => (hE.of_gk g).ctx)
    fun _ _ => vecs_ok h₂ fun h => by cases h

/-- The end's vector code runs, whatever the accumulator. -/
theorem last_exec {R : Nat} {s : State} (hE : EndCtx R s) :
    WP isa (.block (addGroup ++ step1 ++ step2 ++ step3)) s (GK s) := by
  refine seq_gk (seq_gk (seq_gk (vecs_ok addS_eq fun _ => hE.ctx) fun s₁ g₁ => ?_) fun s₂ g₂ => ?_)
    fun s₃ g₃ => ?_
  · have E := hE.of_gk g₁
    rw [step1_eq]
    exact seq_gk (loadYG_exec E (by decide) (by decide)) fun _ g => setMulFold_exec (E.of_gk g) s1S_eq f1S_eq
  · have E := hE.of_gk g₂
    rw [step2_eq]
    exact seq_gk (splitG_exec _) fun _ g => setMulFold_exec (E.of_gk g) s2S_eq f2S_eq
  · have E := hE.of_gk g₃
    rw [step3_eq]
    refine seq_gk (loadYG_exec E (by decide) (by decide)) fun s₄ g₄ => ?_
    refine seq_gk (seq_gk (vecs_ok s3S_eq fun _ => (E.of_gk g₄).ctx) fun _ g =>
      vecs_ok mulS_eq fun _ => ((E.of_gk g₄).of_gk g).ctx) fun s₅ g₅ => ?_
    refine seq_gk (vecs_ok f3S_eq fun h => by cases h) fun s₆ g₆ => ?_
    refine seq_gk (splitG_exec _) fun s₇ g₇ => ?_
    have E' := (((E.of_gk g₄).of_gk g₅).of_gk g₆).of_gk g₇
    exact seq_gk (vecs_ok s0S_eq fun h => by cases h) fun _ g => vecs_ok mulS_eq fun _ => (E'.of_gk g).ctx

/-! ## The accumulator into `H` -/

theorem lhS_keep : ∀ i < 3, lhS.reg (xi (yreg i)) = .reg (xi (yreg i)) ∧
    lhS.reg (xi (sreg i)) = .reg (xi (sreg i)) := by decide +kernel

/-- `loadH`: the accumulator (its top word below 4) into quadword 0 of `H`
as limbs, zeros elsewhere. -/
theorem loadH_ok {s : State} (r₀ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 0) 8)
    (r₁ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 8) 8) (r₂ : InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) 16) 8)
    (hr8 : s.gpr .r8 = 0xfffffffffff) :
    WP isa (.block loadH) s fun s' => GK s s' ∧ (∀ k < 8, yv s' k = yv s k) ∧ (∀ k < 8, sv s' k = sv s k) ∧
      ((s.mem.readW (off (s.gpr .rdi) 16) 64).toNat < 4 →
        hval s' 0 = leNum (bytesAt s.mem (s.gpr .rdi) 24) ∧ (∀ k < 8, ∀ i < 3, hv s' k i ≤ 2 ^ 44) ∧
        ∀ k, 0 < k → k < 8 → hval s' k = 0) := by
  rw [loadH_eq]
  refine WP.block_append (WP.mono (loadHG_ok s r₀ r₁ r₂) fun s₁ ⟨a₁, c₁, n₁, o₁, m₁, k₁⟩ => ?_)
  refine WP.mono (run_ok (fun h => by cases h) lhS_eq) fun s₂ h => ?_
  have H : ∀ i < 3, ∀ k < 8, hv s₂ k i = if k = 0 then (s₁.gpr (lg i)).toNat else 0 := fun i hi k hk => by
    simp only [hv]
    rw [h.natw _ hk, lhS_shape i hi]
    simp only [Q.natw]
    split <;> rfl
  have ey : ∀ k < 8, yv s₂ k = yv s k := by
    refine fun k hk => (yv_of (fun i hi k hk => ?_) k hk).trans (by rw [VKeep.yv k₁])
    rw [h.reg _ k hk, (lhS_keep i hi).1]; simp only [Q.eval, xr_xi]
  have es : ∀ k < 8, sv s₂ k = sv s k := by
    refine fun k hk => (sv_of (fun i hi k hk => ?_) k hk).trans (by rw [VKeep.sv k₁])
    rw [h.reg _ k hk, (lhS_keep i hi).2]; simp only [Q.eval, xr_xi]
  refine ⟨(GK.of_vk k₁ o₁ m₁).trans (GK.of_vec h.eq), ey, es, fun h2 => ?_⟩
  have w0 := (s.mem.readW (off (s.gpr .rdi) 0) 64).isLt
  have w1 := (s.mem.readW (off (s.gpr .rdi) 8) 64).isLt
  have e₀ : (s₁.gpr .rax).toNat = (s.mem.readW (off (s.gpr .rdi) 0) 64).toNat % 2 ^ 44 := by
    rw [a₁, hr8, BitVec.toNat_and]; exact Limbs44.and_mask _
  have e₁ : (s₁.gpr .rcx).toNat = (s.mem.readW (off (s.gpr .rdi) 0) 64).toNat / 2 ^ 44 +
      2 ^ 20 * ((s.mem.readW (off (s.gpr .rdi) 8) 64).toNat % 2 ^ 24) := by
    rw [c₁, hr8, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.or_comm]
    exact Limbs44.split1 w0 _
  have e₂ : (s₁.gpr .r9).toNat = 2 ^ 40 * ((s.mem.readW (off (s.gpr .rdi) 16) 64).toNat % 2 ^ 24) +
      (s.mem.readW (off (s.gpr .rdi) 8) 64).toNat / 2 ^ 24 := by
    rw [n₁, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ushiftRight,
      Nat.shiftRight_eq_div_pow, Nat.or_comm]
    exact Limbs44.split2 w1 _
  refine ⟨?_, fun k hk i hi => ?_, fun k h0 hk => ?_⟩
  · simp only [hval, Limbs44.val]
    rw [H 0 (by decide) 0 (by decide), H 1 (by decide) 0 (by decide), H 2 (by decide) 0 (by decide)]
    simp only [ite_true]
    show (s₁.gpr .rax).toNat + 2 ^ 44 * (s₁.gpr .rcx).toNat + 2 ^ 88 * (s₁.gpr .r9).toNat = _
    rw [e₀, e₁, e₂, leNum_acc, off_eq _ 0, BitVec.add_zero]
    have := Limbs44.split_val (s.mem.readW (off (s.gpr .rdi) 0) 64).toNat
      (s.mem.readW (off (s.gpr .rdi) 8) 64).toNat ((s.mem.readW (off (s.gpr .rdi) 16) 64).toNat % 2 ^ 24)
    rw [off_eq _ 0, BitVec.add_zero] at this
    omega
  · rw [H i hi k hk]
    split
    · rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · show (s₁.gpr .rax).toNat ≤ _; rw [e₀]; omega
      · show (s₁.gpr .rcx).toNat ≤ _; rw [e₁]; omega
      · show (s₁.gpr .r9).toNat ≤ _; rw [e₂]; omega
    · omega
  · simp only [hval, Limbs44.val]
    rw [H 0 (by decide) k hk, H 1 (by decide) k hk, H 2 (by decide) k hk, ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The prologue -/

/-- What the prologue leaves in memory for the rest: nothing written outside
the working space, MXCSR (bits 31:16 cleared) at byte 120, and `r²`, `r⁴`,
the mask and the pad bit. -/
structure IMem (s₀ : State) (m₁ : Mem) : Prop where
  ok : MemOK s₀ m₁
  r : MemR (st s₀) (Rn s₀) m₁

/-- Before group `j` of eight blocks (the loop's invariant), with the memory
`m₁` the prologue leaves. -/
structure LInv (s₀ : State) (m₁ : Mem) (j : Nat) (s : State) : Prop where
  lt : j < nb s₀ / 8
  rdi : s.gpr .rdi = st s₀
  rsi : s.gpr .rsi = blkAddr s₀ (8 * j)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j)
  rdx : s.gpr .rdx = s₀.gpr .rdx
  r8 : s.gpr .r8 = 0xfffffffffff
  r10 : s.gpr .r10 = R0 s₀
  r11 : s.gpr .r11 = R1 s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁
  acc : H2 s₀ < 4 → LaneInv (Rn s₀) (absorbAll (Rn s₀) (A0 s₀) (blks s₀ (8 * j))) s

theorem cs_ne' {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rsi ∧ r ≠ .r8 ∧
    r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11 ∧ r ≠ .rdi := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem pro_ok {s₀ : State} (hp : APre s₀) (hbig : 16 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ powers ++ loadH ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr))) s
      (fun s' => IMem s₀ s'.mem ∧ LInv s₀ s'.mem 0 s') := by
  have hp2 := hp.avx2
  have hb := hp2.bpre.nb_lt
  rw [List.append_assoc, List.append_assoc]
  have rdi₀ : s.gpr .rdi = st s₀ := by rw [hg]
  have wr₀ : s.wr = s₀.wr := hk.wr
  refine WP.block_append (WP.mono (mxcsrIn_ok s (hp2.inW wr₀ rdi₀ (by omega)) (hp2.inW wr₀ rdi₀ (by omega))
    (hp2.inRW wr₀ rdi₀ (by omega)) (hp2.inRW wr₀ rdi₀ (by omega)))
    fun s₁ ⟨g₁, m₁, _, _, _, rd₁, wr₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [g₁ _ (by decide), rdi₀]
  have rsi₁ : s₁.gpr .rsi = blkAddr s₀ (8 * 0) := by rw [g₁ _ (by decide), hg]; simp [blkAddr]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, wr₀]
  have rd₁' : s₁.rd = s₀.rd := by rw [rd₁, hk.rd]
  have mm₁ : s₁.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [m₁, hm, rdi₀, hk.mxcsr]
  have hc₁ : Ctx s₁ := ctx_of hp rd₁' wr₁' rdi₁ rsi₁ (by omega)
  refine WP.block_append (WP.mono (powers_ok hc₁ (by rw [wr₁', hp.wr, rdi₁]; exact List.mem_singleton_self _))
    fun s₂ P₂ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rdi₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [P₂.wr, wr₁']
  have r10₂ : s₂.gpr .r10 = R0 s₀ := by rw [P₂.r10, rdi₁, mm₁, mxMem_read _ _ _ (by omega)]
  have r11₂ : s₂.gpr .r11 = R1 s₀ := by rw [P₂.r11, rdi₁, mm₁, mxMem_read _ _ _ (by omega)]
  have F₂ : Frame [wR (st s₀)] s₀.mem s₂.mem :=
    (mxMem_frame s₀.mem (st s₀) s₀.mxcsr).trans (by rw [← mm₁, ← rdi₁]; exact P₂.frame)
  have acc₂ : bytesAt s₂.mem (st s₀) 24 = bytesAt s₀.mem (st s₀) 24 :=
    bytesAt_frame F₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [wR, off, Proof.Poly1305.X86_64.ofInt_natCast]
      exact Offset.base_disjoint _ (by decide) (by decide)) (by decide)
  refine WP.block_append (WP.mono (loadH_ok (hp2.inRW (by rw [wr₂]) rdi₂ (by omega))
    (hp2.inRW (by rw [wr₂]) rdi₂ (by omega)) (hp2.inRW (by rw [wr₂]) rdi₂ (by omega)) P₂.r8)
    fun s₃ ⟨G₃, y₃, z₃, L₃⟩ => ?_)
  refine WP.mono (rcx_ok s₃) fun s₄ ⟨c₄, g₄, m₄, k₄⟩ => ?_
  have gk : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s₄.gpr r = s₀.gpr r := by
    intro r a c e f g h
    rw [g₄ r c, G₃.gpr r a c f, P₂.gpr r a c e f g h, g₁ r a, hg]
  have gk' : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s₄.gpr r = s₂.gpr r := fun r a c f => by
    rw [g₄ r c, G₃.gpr r a c f]
  have mm₄ : s₄.mem = s₂.mem := by rw [m₄, G₃.mem]
  have rdx₃ : s₃.gpr .rdx = s₀.gpr .rdx := by
    rw [G₃.gpr _ (by decide) (by decide) (by decide),
      P₂.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide), hg]
  have hM := P₂.m
  rw [r10₂, r11₂, rdi₁] at hM
  refine ⟨⟨⟨by rw [mm₄]; exact F₂, by rw [mm₄, ← rdi₁, P₂.mx, mm₁, rdi₁, mxMem_mx]⟩, by rw [mm₄]; exact hM⟩,
    by omega, gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_,
    gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_,
    fun r hr => ?_, ?_, ?_, rfl, fun hA => ?_⟩
  · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [blkAddr]
  · rw [c₄, rdx₃, rcx_val _ (by have := hbig; simp only [nb] at this; omega), Nat.sub_zero]
  · rw [g₄ _ (by decide), G₃.gpr _ (by decide) (by decide) (by decide), P₂.r8]
  · rw [gk' _ (by decide) (by decide) (by decide), r10₂]
  · rw [gk' _ (by decide) (by decide) (by decide), r11₂]
  · obtain ⟨a, c, -, -, e, f, g, h, -⟩ := cs_ne' hr
    exact gk r a c e f g h
  · rw [k₄.rd, G₃.rd, P₂.rd, rd₁']
  · rw [k₄.wr, G₃.wr, wr₂]
  · -- The accumulator in quadword 0 of `H`, zeros elsewhere, and `Y` from `powers`.
    have w2 : (s₂.mem.readW (off (s₂.gpr .rdi) 16) 64).toNat < 4 := by
      have e := congrArg leNum acc₂
      rw [leNum_acc, leNum_acc] at e
      have := (s₂.mem.readW (off (st s₀) 0) 64).isLt
      have := (s₂.mem.readW (off (st s₀) 8) 64).isLt
      have := (s₀.mem.readW (off (st s₀) 0) 64).isLt
      have := (s₀.mem.readW (off (st s₀) 8) 64).isLt
      simp only [H2] at hA
      rw [rdi₂]
      omega
    obtain ⟨L0, Lb, Lz⟩ := L₃ w2
    rw [rdi₂, acc₂] at L0
    have ev := VKeep.hv k₄
    refine ⟨⟨fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩, fun k hk => by rw [ev]; exact Lb k hk, ?_⟩
    · have e := P₂.y k hk
      rw [r10₂, r11₂] at e
      simp only [yval] at e ⊢; rw [VKeep.yv k₄, y₃ k hk]; exact e
    · rw [VKeep.yv k₄, y₃ k hk]; exact P₂.yb k hk
    · rw [VKeep.sv k₄, VKeep.yv k₄, z₃ k hk, y₃ k hk]; exact P₂.sr k hk
    · simp only [wsum, hval, ev]
      simp only [hval] at L0 Lz
      rw [L0, Lz 1 (by decide) (by decide), Lz 2 (by decide) (by decide), Lz 3 (by decide) (by decide),
        Lz 4 (by decide) (by decide), Lz 5 (by decide) (by decide), Lz 6 (by decide) (by decide),
        Lz 7 (by decide) (by decide), Nat.mul_zero, blks_zero, Poly1305.absorbAll_nil]
      simp only [Poly1305.lanes8, Nat.mul_zero, Nat.add_zero]
      rfl

end VG.Proof.Poly1305.X86_64.Ifma
