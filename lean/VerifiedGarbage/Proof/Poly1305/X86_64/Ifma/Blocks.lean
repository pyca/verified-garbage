module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Final
public import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Gpr
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Final
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Blocks
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Gpr
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
public import VerifiedGarbage.Proof.Poly1305.Contract

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

@[expose] public section

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
    omega_arith
  · rw [H i hi k hk]
    split
    · rcases (by omega_arith : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
      · show (s₁.gpr .rax).toNat ≤ _; rw [e₀]; omega_arith
      · show (s₁.gpr .rcx).toNat ≤ _; rw [e₁]; omega_arith
      · show (s₁.gpr .r9).toNat ≤ _; rw [e₂]; omega_arith
    · omega_arith
  · simp only [hval, Limbs44.val]
    rw [H 0 (by decide) k hk, H 1 (by decide) k hk, H 2 (by decide) k hk, ite_eq_right (by omega_arith),
      ite_eq_right (by omega_arith), ite_eq_right (by omega_arith)]

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

theorem pro_ok {s₀ : State} (hp : APre s₀) (hbig : 28 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa (.block (Impl.Poly1305.X86_64.Avx2.mxcsrIn ++ powers ++ loadH ++
      ([.mov .rcx (.reg .rdx), .shift .shr .rcx 3, .alu .sub .rcx (.imm 1)] : List Instr))) s
      (fun s' => IMem s₀ s'.mem ∧ LInv s₀ s'.mem 0 s') := by
  have hp2 := hp.avx2
  have hb := hp2.bpre.nb_lt
  rw [List.append_assoc, List.append_assoc]
  have rdi₀ : s.gpr .rdi = st s₀ := by rw [hg]
  have wr₀ : s.wr = s₀.wr := hk.wr
  refine WP.block_append (WP.mono (mxcsrIn_ok s (hp2.inW wr₀ rdi₀ (by omega_arith)) (hp2.inW wr₀ rdi₀ (by omega_arith))
    (hp2.inRW wr₀ rdi₀ (by omega_arith)) (hp2.inRW wr₀ rdi₀ (by omega_arith)))
    fun s₁ ⟨g₁, m₁, _, _, _, rd₁, wr₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [g₁ _ (by decide), rdi₀]
  have rsi₁ : s₁.gpr .rsi = blkAddr s₀ (8 * 0) := by rw [g₁ _ (by decide), hg]; simp [blkAddr]
  have wr₁' : s₁.wr = s₀.wr := by rw [wr₁, wr₀]
  have rd₁' : s₁.rd = s₀.rd := by rw [rd₁, hk.rd]
  have mm₁ : s₁.mem = mxMem s₀.mem (st s₀) s₀.mxcsr := by rw [m₁, hm, rdi₀, hk.mxcsr]
  have hc₁ : Ctx s₁ := ctx_of hp rd₁' wr₁' rdi₁ rsi₁ (by omega_arith)
  refine WP.block_append (WP.mono (powers_ok hc₁ (by rw [wr₁', hp.wr, rdi₁]; exact List.mem_singleton_self _))
    fun s₂ P₂ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [P₂.gpr _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), rdi₁]
  have wr₂ : s₂.wr = s₀.wr := by rw [P₂.wr, wr₁']
  have r10₂ : s₂.gpr .r10 = R0 s₀ := by rw [P₂.r10, rdi₁, mm₁, mxMem_read _ _ _ (by omega_arith)]
  have r11₂ : s₂.gpr .r11 = R1 s₀ := by rw [P₂.r11, rdi₁, mm₁, mxMem_read _ _ _ (by omega_arith)]
  have F₂ : Frame [wR (st s₀)] s₀.mem s₂.mem :=
    (mxMem_frame s₀.mem (st s₀) s₀.mxcsr).trans (by rw [← mm₁, ← rdi₁]; exact P₂.frame)
  have acc₂ : bytesAt s₂.mem (st s₀) 24 = bytesAt s₀.mem (st s₀) 24 :=
    bytesAt_frame F₂ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      simp only [wR, off, Proof.Poly1305.X86_64.ofInt_natCast]
      exact Offset.base_disjoint _ (by decide) (by decide)) (by decide)
  refine WP.block_append (WP.mono (loadH_ok (hp2.inRW (by rw [wr₂]) rdi₂ (by omega_arith))
    (hp2.inRW (by rw [wr₂]) rdi₂ (by omega_arith)) (hp2.inRW (by rw [wr₂]) rdi₂ (by omega_arith)) P₂.r8)
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
    by omega_arith, gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_,
    gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, ?_,
    fun r hr => ?_, ?_, ?_, rfl, fun hA => ?_⟩
  · rw [gk _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [blkAddr]
  · rw [c₄, rdx₃, rcx_val _ (by have := hbig; simp only [nb] at this; omega_arith), Nat.sub_zero]
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
      omega_arith
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

/-! ## The loop -/

theorem IMem.consts {s₀ : State} {m₁ : Mem} (hm : IMem s₀ m₁) {s : State} (hd : s.gpr .rdi = st s₀)
    (hs : s.mem = m₁) : Consts s :=
  MemR.consts (by rw [hs]; exact hm.r) hd

theorem group_body_ok {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : IMem s₀ m₁) {j : Nat}
    (hj : j + 1 < nb s₀ / 8) {s : State} (h : LInv s₀ m₁ j s) :
    WP isa groupBody s fun s' => LInv s₀ m₁ (j + 1) s' ∧ s'.zf = some (decide (nb s₀ / 8 - 1 - j = 1)) := by
  have hb := hp.avx2.bpre.nb_lt
  have hc := ctx_of hp h.rd h.wr h.rdi h.rsi (j := j) (by omega_arith)
  refine WP.block_append (WP.mono (guard (R := fun s' => vec s s' = s') (A := H2 s₀ < 4) ?_
    fun hA => group_ok hc (hm.consts h.rdi h.mem) (h.acc hA)) fun s₁ ⟨v₁, G₁⟩ => ?_)
  · exact WP.block_append (WP.mono (run_ok (fun _ => hc) addS_eq) fun s₁ h₁ =>
      WP.mono (run_ok (fun _ => Ctx.of_vec hc h₁.eq) mulS_eq) fun s₂ h₂ => vec_trans h₁.eq h₂.eq)
  obtain ⟨vg₁, vm₁, vrd₁, vwr₁, -⟩ := vec_keep v₁
  refine WP.mono (adv_ok s₁) fun s₂ ⟨si₂, cx₂, zf₂, g₂, m₂, k₂⟩ => ?_
  have gk : ∀ r, r ≠ .rsi → r ≠ .rcx → s₂.gpr r = s.gpr r := fun r a b => by rw [g₂ r a b, vg₁]
  have hcx : s₁.gpr .rcx = BitVec.ofNat 64 (nb s₀ / 8 - 1 - j) := by rw [vg₁, h.rcx]
  refine ⟨⟨hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun hA => ?_⟩, ?_⟩
  · rw [gk _ (by decide) (by decide), h.rdi]
  · rw [si₂, vg₁, h.rsi, add128]
  · rw [cx₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega_arith),
      Nat.sub_sub]
  · rw [gk _ (by decide) (by decide), h.rdx]
  · rw [gk _ (by decide) (by decide), h.r8]
  · rw [gk _ (by decide) (by decide), h.r10]
  · rw [gk _ (by decide) (by decide), h.r11]
  · obtain ⟨-, c, -, e, -⟩ := cs_ne' hr
    rw [gk r e c, h.keep r hr]
  · rw [k₂.rd, vrd₁, h.rd]
  · rw [k₂.wr, vwr₁, h.wr]
  · rw [m₂, vm₁, h.mem]
  · have G := (G₁ hA).2
    rw [h.mem, h.rsi, grp_bytes hp hm.ok (by omega_arith), absorb_grp] at G
    exact G.of_vk k₂
  · rw [zf₂, hcx, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      Offset.ofNat_sub_ofNat_beq (by omega_arith) (by omega_arith)]

theorem loop_ok {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : IMem s₀ m₁) (hG : 1 < nb s₀ / 8) {s : State}
    (h₀ : LInv s₀ m₁ 0 s) : WP isa (.loop groupBody .ne) s (LInv s₀ m₁ (nb s₀ / 8 - 1)) := by
  let Inv : Nat → State → Prop := fun n s => ∃ j, n = nb s₀ / 8 - 1 - j ∧ j < nb s₀ / 8 - 1 ∧ LInv s₀ m₁ j s
  have hstep : ∀ n s, Inv n s → WP isa groupBody s (fun s' =>
      (eval .ne s' = some false ∧ LInv s₀ m₁ (nb s₀ / 8 - 1) s') ∨
      (eval .ne s' = some true ∧ ∃ n' < n, Inv n' s')) := by
    rintro n s ⟨j, rfl, hj, hI⟩
    refine WP.mono (group_body_ok hp hm (by omega_arith) hI) fun s' ⟨h', hz⟩ => ?_
    by_cases e : nb s₀ / 8 - 1 - j = 1
    · have e' : j + 1 = nb s₀ / 8 - 1 := by omega_arith
      exact .inl ⟨by simp [eval, hz, e], e' ▸ h'⟩
    · exact .inr ⟨by simp [eval, hz, e], nb s₀ / 8 - 1 - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, h'⟩
  exact WP.loop (M := isa) Inv hstep _ s ⟨0, rfl, by omega_arith, h₀⟩

/-! ## The epilogue's integer code -/

/-- `save`, keeping the vector registers and MXCSR. -/
theorem saveX_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.mxcsr = s.mxcsr ∧
      Frame [Proof.Poly1305.X86_64.svR (s.gpr .rdi)] s.mem s'.mem ∧ Saved (s.gpr .rdi) s s'.mem := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, Proof.Poly1305.X86_64.contains_off hd (by omega_arith)⟩
  have o0 := o 72 (by decide); have o1 := o 80 (by decide); have o2 := o 88 (by decide)
  have o3 := o 96 (by decide); have o4 := o 104 (by decide); have o5 := o 112 (by decide)
  apply WP.of_runBlock
  rw [Proof.Poly1305.X86_64.save_eq]
  simp only [off] at o0 o1 o2 o3 o4 o5
  simp only [↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    Proof.Poly1305.X86_64.ea_at, State.store64, o0, o1, o2, o3, o4, o5, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, trivial, ?_, ?_⟩
  · have c : ∀ d, 72 ≤ d → d + 8 ≤ 120 →
        (Proof.Poly1305.X86_64.svR (s.gpr .rdi)).Contains (off (s.gpr .rdi) d) (64 / 8) :=
      fun d h₁ h₂ => Proof.Poly1305.X86_64.svR_contains _ h₁ h₂
    refine (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 72 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 80 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 88 ?_ ?_)).writeW
      (List.mem_singleton_self _) _ (c 96 ?_ ?_)).writeW (List.mem_singleton_self _) _ (c 104 ?_ ?_)
      |>.writeW (List.mem_singleton_self _) _ (c 112 ?_ ?_) <;> omega_arith
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [off, Mem.readW_writeW_self64, Proof.Poly1305.X86_64.readW_writeW_off]

/-- Storing `h` and restoring the callee-saved registers, keeping the rest. -/
theorem storeRestoreX_ok (s : State) (hw : sR (s.gpr .rdi) ∈ s.wr) :
    WP isa (.block (([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx,
      .store (at_ .rdi 16) .rbp] : List Instr) ++ restore)) s fun s' =>
      let m := Proof.Poly1305.X86_64.storeH s.mem (s.gpr .rdi) (s.gpr .r11) (s.gpr .rbx) (s.gpr .rbp)
      s'.mem = m ∧ s'.gpr .rbx = m.readW (off (s.gpr .rdi) 72) 64 ∧
      s'.gpr .rbp = m.readW (off (s.gpr .rdi) 80) 64 ∧ s'.gpr .r12 = m.readW (off (s.gpr .rdi) 88) 64 ∧
      s'.gpr .r13 = m.readW (off (s.gpr .rdi) 96) 64 ∧ s'.gpr .r14 = m.readW (off (s.gpr .rdi) 104) 64 ∧
      s'.gpr .r15 = m.readW (off (s.gpr .rdi) 112) 64 ∧
      (∀ r, r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mxcsr = s.mxcsr := by
  have o : ∀ d, d + 8 ≤ 128 → InRegions s.wr (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, hw, Proof.Poly1305.X86_64.contains_off hd (by omega_arith)⟩
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, Proof.Poly1305.X86_64.contains_off hd (by omega_arith)⟩
  have o0 := o 0 (by decide); have o8 := o 8 (by decide); have o16 := o 16 (by decide)
  have i0 := i 72 (by decide); have i1 := i 80 (by decide); have i2 := i 88 (by decide)
  have i3 := i 96 (by decide); have i4 := i 104 (by decide); have i5 := i 112 (by decide)
  simp only [off] at o0 o8 o16 i0 i1 i2 i3 i4 i5
  apply WP.of_runBlock
  rw [Proof.Poly1305.X86_64.storeRestore_eq]
  simp only [reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec,
    Proof.Poly1305.X86_64.ea_at, readSrc, State.store64, State.load64, State.setReg, o0, o8, o16, i0, i1, i2,
    i3, i4, i5, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r a b c d e f => ?_, trivial, trivial, trivial⟩
  simp only [a, b, c, d, e, f, ite_false]

/-! ## The epilogue -/

theorem reduce_mx : ∀ i ∈ instrs (.block reduce : Prog isa), loadsMxcsr i = false := by decide

theorem epi_eq : addGroup ++ step1 ++ step2 ++ step3 ++ Impl.Poly1305.X86_64.Avx2.mxcsrOut ++
    ([.vop .vzeroupper] : List Instr) ++ save ++ toWords ++ ([.mov .r9 (.reg .rdx)] : List Instr) ++ reduce ++
    ([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp] : List Instr) ++
    restore ++ ([.mov .rdx (.reg .r9), .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr) =
    (addGroup ++ step1 ++ step2 ++ step3) ++ (Impl.Poly1305.X86_64.Avx2.mxcsrOut ++
      (([.vop .vzeroupper] : List Instr) ++ (save ++ (toWords ++ (([.mov .r9 (.reg .rdx)] : List Instr) ++
      (reduce ++ ((([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp] :
        List Instr) ++ restore) ++
      ([.mov .rdx (.reg .r9), .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr)))))))) := by
  simp only [List.append_assoc]

theorem epi_ok {s₀ : State} (hp : APre s₀) {m₁ : Mem} (hm : IMem s₀ m₁) {s : State}
    (h : LInv s₀ m₁ (nb s₀ / 8 - 1) s) :
    WP isa (.block (addGroup ++ step1 ++ step2 ++ step3 ++ Impl.Poly1305.X86_64.Avx2.mxcsrOut ++
      ([.vop .vzeroupper] : List Instr) ++ save ++ toWords ++ ([.mov .r9 (.reg .rdx)] : List Instr) ++ reduce ++
      ([.store (at_ .rdi 0) .r11, .store (at_ .rdi 8) .rbx, .store (at_ .rdi 16) .rbp] : List Instr) ++
      restore ++ ([.mov .rdx (.reg .r9), .alu .add .rsi (.imm 128), .alu .and .rdx (.imm 7)] : List Instr)))
      s (TailPre s₀ (8 * (nb s₀ / 8))) := by
  have hp2 := hp.avx2
  have hb := hp2.bpre.nb_lt
  have hlt := h.lt
  have h1 : 1 ≤ nb s₀ / 8 := by omega_arith
  rw [epi_eq]
  have hE : EndCtx (Rn s₀) s :=
    ⟨ctx_of hp h.rd h.wr h.rdi h.rsi (by omega_arith), by rw [h.rdi, h.mem]; exact hm.r,
      by rw [h.r10, h.r11], h.r8⟩
  -- The last group and the folds.
  refine WP.block_append (WP.mono (guard (R := GK s) (A := H2 s₀ < 4) (last_exec hE)
    fun hA => last_ok hE (h.acc hA)) fun s₁ ⟨G₁, L₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := by rw [G₁.gpr _ (by decide) (by decide) (by decide), h.rdi]
  have wr₁ : s₁.wr = s₀.wr := by rw [G₁.wr, h.wr]
  have mm₁ : s₁.mem = m₁ := by rw [G₁.mem, h.mem]
  -- MXCSR restored.
  refine WP.block_append (WP.mono (mxcsrOut_ok s₁ (hp2.inRW wr₁ rdi₁ (by omega_arith))
    (by rw [mm₁, rdi₁, hm.ok.mx]; exact mx_hi _)) fun s₂ ⟨g₂, m₂, mx₂, x₂, _, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono (vzu_ok s₂) fun s₃ ⟨g₃, m₃, x₃, mx₃, rd₃, wr₃⟩ => ?_)
  have rdi₃ : s₃.gpr .rdi = st s₀ := by rw [g₃, g₂, rdi₁]
  have wr₃ : s₃.wr = s₀.wr := by rw [wr₃, wr₂, wr₁]
  -- The callee-saved registers saved, and the accumulator to words.
  refine WP.block_append (WP.mono (saveX_ok s₃ (by rw [wr₃, hp.wr, rdi₃]; exact List.mem_singleton_self _))
    fun s₄ ⟨g₄, rd₄, wr₄, x₄, mx₄, F₄, S₄⟩ => ?_)
  refine WP.block_append (WP.mono (toWords_ok s₄) fun s₅ ⟨T₅, K₅⟩ => ?_)
  refine WP.block_append (WP.mono (movR9_ok s₅) fun s₆ ⟨r9₆, g₆, m₆, mx₆, rd₆, wr₆⟩ => ?_)
  refine WP.block_append (WP.mono (Avx2.and_exec (reduce_ok s₆) fun _ _ he => Exec.mxcsr reduce_mx he)
    fun s₇ ⟨⟨R₇, K₇⟩, mx₇⟩ => ?_)
  have rdi₇ : s₇.gpr .rdi = st s₀ := by
    rw [K₇.1 _ (by decide), g₆ _ (by decide), K₅.gpr _ (by decide), g₄, rdi₃]
  have wr₇ : s₇.wr = s₀.wr := by rw [K₇.2.2.2, wr₆, K₅.wr, wr₄, wr₃]
  refine WP.block_append (WP.mono (storeRestoreX_ok s₇ (by rw [wr₇, hp.wr, rdi₇]; exact List.mem_singleton_self _))
    fun s₈ ⟨m₈, b₈, p₈, r12₈, r13₈, r14₈, r15₈, g₈, rd₈, wr₈, mx₈⟩ => ?_)
  refine WP.mono (fin3_ok s₈) fun s₉ ⟨si₉, dx₉, g₉, m₉, mx₉, rd₉, wr₉⟩ => ?_
  -- The registers the integer code leaves as they were.
  have k₇ : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .r11 → r ≠ .rbx → r ≠ .rbp → r ≠ .r12 → r ≠ .r13 → r ≠ .r14 →
      s₇.gpr r = s₆.gpr r := fun r a b c d e f g i => K₇.1 r (by simp [a, b, c, d, e, f, g, i])
  have gs : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r9 → s₃.gpr r = s.gpr r := fun r a c n => by
    rw [g₃, g₂, G₁.gpr r a c n]
  have rsi₈ : s₈.gpr .rsi = s.gpr .rsi := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      g₆ _ (by decide), K₅.gpr _ (by decide), g₄, gs _ (by decide) (by decide) (by decide)]
  have r9₈ : s₈.gpr .r9 = s₀.gpr .rdx := by
    rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      r9₆, K₅.gpr _ (by decide), g₄, gs _ (by decide) (by decide) (by decide), h.rdx]
  have mm₇ : s₇.mem = s₄.mem := by rw [K₇.2.1, m₆, K₅.mem]
  have rdi₇' : s₇.gpr .rdi = s₃.gpr .rdi := by rw [rdi₇, rdi₃]
  have mmx : s₉.mxcsr = s₀.mxcsr &&& 0xffff := by
    rw [mx₉, mx₈, mx₇, mx₆, K₅.mxcsr, mx₄, mx₃, mx₂, mm₁, rdi₁, hm.ok.mx]
  have hframe : Frame [hR (st s₀), wR (st s₀)] s₀.mem s₉.mem := by
    rw [m₉, m₈, rdi₇]
    refine storeH_frame ?_ _ _ _
    rw [mm₇]
    refine (hm.ok.frame.mono (by simp)).trans ?_
    have e : s₃.mem = m₁ := by rw [m₃, m₂, mm₁]
    rw [← e]
    exact F₄.sub fun r hr => ⟨wR (st s₀), by simp, by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hr, rdi₃]; exact Proof.Poly1305.X86_64.svR_sub_wR _⟩
  refine ⟨by omega_arith, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, hframe, by rw [mmx, mx_bits], fun key msg hr => ?_⟩
  · rw [g₉ _ (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), rdi₇]
  · rw [si₉, rsi₈, h.rsi, add128, Nat.sub_add_cancel h1]
  · rw [dx₉, r9₈]
    apply BitVec.eq_of_toNat_eq
    rw [and7_toNat, toNat_ofNat_lt (by omega_arith)]
    simp only [nb]
    omega_arith
  · -- The callee-saved registers, restored from the state.
    have sv : ∀ d, 24 ≤ d → d < 2 ^ 32 →
        (Proof.Poly1305.X86_64.storeH s₇.mem (s₇.gpr .rdi) (s₇.gpr .r11) (s₇.gpr .rbx) (s₇.gpr .rbp)).readW
          (off (s₇.gpr .rdi) d) 64 = s₄.mem.readW (off (s₃.gpr .rdi) d) 64 := fun d h₁ h₂ => by
      rw [storeH_saved _ _ _ _ _ h₁ h₂, mm₇, rdi₇']
    obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := S₄
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g₉ _ (by decide) (by decide), b₈, sv _ (by decide) (by decide), sv1,
        gs _ (by decide) (by decide) (by decide), h.keep _ (by decide)]
    · rw [g₉ _ (by decide) (by decide), p₈, sv _ (by decide) (by decide), sv2,
        gs _ (by decide) (by decide) (by decide), h.keep _ (by decide)]
    · rw [g₉ _ (by decide) (by decide), g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), k₇ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), g₆ _ (by decide), K₅.gpr _ (by decide), g₄, gs _ (by decide) (by decide) (by decide),
        h.keep _ (by decide)]
    · rw [g₉ _ (by decide) (by decide), r12₈, sv _ (by decide) (by decide), sv3,
        gs _ (by decide) (by decide) (by decide), h.keep _ (by decide)]
    · rw [g₉ _ (by decide) (by decide), r13₈, sv _ (by decide) (by decide), sv4,
        gs _ (by decide) (by decide) (by decide), h.keep _ (by decide)]
    · rw [g₉ _ (by decide) (by decide), r14₈, sv _ (by decide) (by decide), sv5,
        gs _ (by decide) (by decide) (by decide), h.keep _ (by decide)]
    · rw [g₉ _ (by decide) (by decide), r15₈, sv _ (by decide) (by decide), sv6,
        gs _ (by decide) (by decide) (by decide), h.keep _ (by decide)]
  · rw [rd₉, rd₈, K₇.2.2.1, rd₆, K₅.rd, rd₄, rd₃, rd₂, G₁.rd, h.rd]
  · rw [wr₉, wr₈, wr₇]
  · -- The accumulator represents the blocks absorbed.
    have hA := H2_lt hr
    obtain ⟨hlen, hkey, hacc⟩ := hr
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := by rw [off_24]; exact hkey
    have hA0 : accumulate (Rn s₀) msg = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    have hlt : A0 s₀ < P := by rw [← hA0]; exact Poly1305.accumulate_lt _ _
    obtain ⟨-, Lb, L⟩ := L₁ hA
    rw [h.mem, h.rsi, grp_bytes hp hm.ok (by omega_arith), absorb_grp, Nat.sub_add_cancel h1] at L
    have ex : ∀ i < 3, (h0w s₄ i).toNat = hv s₁ 0 i := fun i _ => by
      simp only [h0w, x₄, x₃, x₂]; rfl
    obtain ⟨T, T4⟩ := T₅ fun i hi => by rw [ex i hi]; exact Nat.le_trans (Lb i hi) (by decide)
    have e₆ : Proof.Poly1305.X86_64.hval s₆ = Proof.Poly1305.X86_64.hval s₅ := by
      simp only [Proof.Poly1305.X86_64.hval, g₆ .r11 (by decide), g₆ .rbx (by decide), g₆ .rbp (by decide)]
    have R := R₇ (by rw [g₆ .rbp (by decide)]; exact T4)
    have e₄ : h0val s₄ = hval s₁ 0 := by
      simp only [h0val, hval, Limbs44.val, ex 0 (by decide), ex 1 (by decide), ex 2 (by decide)]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.length_append, Poly1305.length_bytesAt]; omega_arith
    · rw [← off_24, key_frame hframe, hkey']
    · rw [m₉, m₈, rdi₇, storeH_acc, ← hkey', clamp_key, Poly1305.accumulate_append hlen]
      change Proof.Poly1305.X86_64.hval s₇ = Poly1305.absorbAll (Rn s₀) (accumulate (Rn s₀) msg) _
      rw [R, e₆, T, e₄, hA0, (L : _ ≡ _ [MOD P]), Nat.mod_eq_of_lt (Poly1305.absorbAll_lt hlt _)]

/-! ## The whole function -/

theorem body_ok {s₀ : State} (hp : APre s₀) (hbig : 28 ≤ nb s₀) {s : State} (hg : s.gpr = s₀.gpr)
    (hm : s.mem = s₀.mem) (hk : VKeep s₀ s) :
    WP isa body s (TailPre s₀ (8 * (nb s₀ / 8))) :=
  WP.seq (WP.mono (pro_ok hp hbig hg hm hk) fun _ h₁ =>
    WP.seq (WP.mono (loop_ok hp h₁.1 (by omega_arith) h₁.2) fun _ h₂ => epi_ok hp h₁.1 h₂))

theorem correct {s₀ : State} (hp : APre s₀) : WP isa blocksIfma s₀ (Post s₀) := by
  have hb := hp.avx2.bpre.nb_lt
  refine WP.seq (WP.mono (cmp_ok s₀) fun s₁ ⟨g₁, m₁, k₁, cf₁⟩ => ?_)
  refine WP.ite (decide (nb s₀ < 32)) (by simp [eval, cf₁]) (fun hlt => ?_) (fun hge => ?_)
  · refine Avx512.avx2_ok hp ⟨by omega_arith, by rw [g₁], by rw [g₁]; simp [blkAddr], ?_,
      fun r _ => by rw [g₁], k₁.rd, k₁.wr, by rw [m₁]; exact Frame.refl _ _, by rw [k₁.mxcsr],
      fun key msg hr => by rw [m₁, blks_zero, List.append_nil]; exact hr⟩
    rw [g₁, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.seq (WP.mono (body_ok hp (by omega_arith) g₁ m₁ k₁) fun s₂ h₂ => ?_)
    refine WP.seq (WP.mono (Avx2.test_ok s₂) fun s₃ ⟨z₃, g₃, m₃, mx₃, rd₃, wr₃⟩ => ?_)
    have h₃ := h₂.congr g₃ m₃ mx₃ rd₃ wr₃
    refine WP.ite (s₃.gpr .rdx &&& s₃.gpr .rdx == 0) (by simp [eval, z₃, g₃]) (fun h => ?_)
      (fun _ => tail_ok hp.avx2 h₃)
    have e : 8 * (nb s₀ / 8) = nb s₀ := by
      have := h₃.rdx
      simp only [BitVec.and_self, beq_iff_eq] at h
      rw [h] at this
      have := congrArg BitVec.toNat this
      rw [toNat_ofNat_lt (by omega_arith)] at this
      rw [show (0 : BitVec 64).toNat = 0 from rfl] at this
      simp only [nb] at this ⊢
      omega_arith
    exact WP.block_nil (M := isa) (done_ok hp.avx2 (e ▸ h₃))

theorem blocksIfma_ok (s : State) (hs : Avx512.blocksAvx512X86_64.pre s) :
    ∃ t s', Exec isa blocksIfma s t s' ∧ abiPreserved s s' ∧ Avx512.blocksAvx512X86_64.post s s' :=
  correct (APre.of s hs)

/-! ## Constant time -/

theorem blocksIfma_ct :
    ConstantTime isa Avx512.blocksAvx512X86_64.pre Avx512.blocksAvx512X86_64.pub blocksIfma := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rsp]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨⟨h1, h2, h3⟩, h4⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption

theorem blocksIfma_verified :
    Verified X86_64.target blocksIfma (Proof.Poly1305.blocksContract X86_64.abi 16) :=
  Verified.of_correct blocksIfma_ok blocksIfma_ct (by
    sig_implies [Proof.Poly1305.blocksContract, Proof.Poly1305.blocksSig, Avx512.blocksAvx512X86_64,
      Proof.Poly1305.blocksStack, Proof.Poly1305.blocksX86_64, X86_64.abi, X86_64.argRegs]
      [Avx2.sat] using Avx2.sat)

end VG.Proof.Poly1305.X86_64.Ifma
