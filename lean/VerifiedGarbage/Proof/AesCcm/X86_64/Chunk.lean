import VerifiedGarbage.Proof.AesCcm.X86_64.Tag

/-!
# AES-CCM on x86-64: a chunk of counter mode (`ctrChunk`)

Untrusted: everything here is checked by Lean. After `b` whole blocks
(`CtrInv`), `ctrChunk` encrypts `k = min (n/16 − b, 2³² − (1 + b) mod 2³²)`
more by `vg_aes_ctr32` from `Ctr₁₊ᵦ`, whose counters do not wrap around in
their low 32 bits, so that they are CCM's (`chunk_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesCcm.X86_64
open VG.Impl.AesGcm.X86_64 (at_ imm ptr)
open VG.Spec.Aes (bytesAt)
open VG.Proof.Aes.X86_64 (Ctr32Impl)

/-- What `ctr` writes: `Ctrⱼ` and the keystream block at `W + 64`, `k` at
`W + 216`, the working space of the functions called, the stack below `SP`
and the data. -/
abbrev ctrR (W SP D : Addr) (n : Nat) : List Region :=
  [⟨W + BitVec.ofNat 64 64, 32⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨W + BitVec.ofNat 64 384, 2176⟩, below SP 16, ⟨D, n⟩]

/-- What `ctr` writes, within what the pieces may write. -/
theorem ctrR_mut (W SP D : Addr) (n : Nat) : ∀ r ∈ ctrR W SP D n, ∃ r' ∈ mutR W SP D n, Region.Sub r r' := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact ⟨wA W, by simp, Offset.sub_base W (by decide)⟩
  · exact ⟨wK W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨wC W, by simp, Offset.sub W (by decide) (by decide)⟩
  · exact ⟨_, by simp, fun _ h => h⟩
  · exact ⟨_, by simp, fun _ h => h⟩

/-- What `ctr` needs, of the state `s` it starts from. -/
structure CtrCtx (K W SP : Addr) (s : State) (R : Nat) (nonce : List Byte) (D : Addr) (n : Nat) : Prop where
  lay : Lay K W SP
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  ro : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R
  h7 : 7 ≤ nonce.length
  h13 : nonce.length ≤ 13
  hn : n < 256 ^ (15 - nonce.length)
  c0 : bytesAt s.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0
  buf : Buf K W SP s D n
  dw : Covers [⟨D, n⟩] s.wr
  dk : (⟨K, 240⟩ : Region).Disjoint ⟨D, n⟩

namespace CtrCtx

variable {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}

/-- The parts of `W` that `ctr` does not write. -/
theorem disj (C : CtrCtx K W SP s R nonce D n) {d k : Nat}
    (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 216) ∨ (224 ≤ d ∧ d + k ≤ 384)) :
    ∀ r ∈ ctrR W SP D n, (⟨W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact C.lay.w_w (by omega_arith) (by omega_arith) (by decide)
  · exact C.lay.w_w (.inl (by omega_arith)) (by omega_arith) (by decide)
  · exact (C.lay.stk_w' (by omega_arith)).symm
  · exact (C.buf.w.sub_right (Lay.wSub (by omega_arith))).symm

theorem kdisj (C : CtrCtx K W SP s R nonce D n) : ∀ r ∈ ctrR W SP D n, (⟨K, 240⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.k_w.sub_right (Lay.wSub (by decide))
  · exact C.lay.stk_k.symm
  · exact C.dk

theorem bytes_kept (C : CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) {d k : Nat}
    (h : d + k ≤ 64 ∨ (96 ≤ d ∧ d + k ≤ 216) ∨ (224 ≤ d ∧ d + k ≤ 384)) :
    bytesAt m (W + BitVec.ofNat 64 d) k = bytesAt s.mem (W + BitVec.ofNat 64 d) k :=
  bytesAt_frame hf (C.disj h) (by omega_arith)

theorem readW_kept (C : CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) {d : Nat}
    (h : d + 8 ≤ 64 ∨ (96 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 384)) :
    m.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (w := 64) (Region.contains_self _ _) (C.disj h) (by decide)

theorem ciph_kept (C : CtrCtx K W SP s R nonce D n) {m : Mem} (hf : Frame (ctrR W SP D n) s.mem m) :
    Spec.Ccm.ctxCiph m K R = Spec.Ccm.ctxCiph s.mem K R :=
  ctxCiph_frame hf C.kdisj (by rcases C.rounds with h | h | h <;> subst h <;> decide)

end CtrCtx

/-- The state of `ctr` after `b` whole blocks: those encrypted, the rest of
the data as it was. -/
structure CtrInv (K W SP : Addr) (s : State) (R : Nat) (nonce : List Byte) (D : Addr) (n b : Nat) (t : State) :
    Prop where
  env : Env K W SP t
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  r12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b)
  rbx : t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b)
  r14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b)
  le : b ≤ n / 16
  frame : Frame (ctrR W SP D n) s.mem t.mem
  done : bytesAt t.mem D (16 * b) = xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D (16 * b))
  rest : bytesAt t.mem (D + BitVec.ofNat 64 (16 * b)) (n - 16 * b) =
    bytesAt s.mem (D + BitVec.ofNat 64 (16 * b)) (n - 16 * b)

theorem low32 (x : Nat) : ((BitVec.ofNat 64 x).setWidth 32).setWidth 64 = BitVec.ofNat 64 (x % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

theorem two32_sub {y : Nat} (hy : y < 2 ^ 32) :
    (4294967296 : BitVec 64) - BitVec.ofNat 64 y = BitVec.ofNat 64 (2 ^ 32 - y) :=
  ofNat_sub (a := 2 ^ 32) (b := y) (Nat.le_of_lt hy) (by decide)

/-- `k = min (m, 2³² − (1 + b) mod 2³²)` in `r8`, for `m` blocks left. -/
theorem kSel_ok {b m : Nat} {t : State} (hbx : t.gpr .rbx = BitVec.ofNat 64 m)
    (h14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b)) (hm : m < 2 ^ 64) :
    WP isa (.seq (.block [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)]) (.ite .b (.block []) (.block [.mov .r8 (.reg .rcx)]))) t
      fun t₂ => t₂.mem = t.mem ∧ t₂.gpr .r8 = BitVec.ofNat 64 (min m (2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
        (∀ r, r ≠ .r8 → r ≠ .rcx → t₂.gpr r = t.gpr r) ∧ t₂.rd = t.rd ∧ t₂.wr = t.wr := by
  obtain ⟨t₁, run₁, hm₁, hr8₁, hcx₁, hcf₁, hg₁, hrd₁, hwr₁⟩ : ∃ t₁, runBlock isa
      [.mov32 .r8 (.reg .r14), .movImm64 .rcx 0x100000000, .alu .sub .rcx (.reg .r8),
        .mov .r8 (.reg .rbx), .alu .cmp .rbx (.reg .rcx)] t = some t₁ ∧ t₁.mem = t.mem ∧
      t₁.gpr .r8 = BitVec.ofNat 64 m ∧ t₁.gpr .rcx = BitVec.ofNat 64 (2 ^ 32 - (1 + b) % 2 ^ 32) ∧
      t₁.cf = some (decide (m < 2 ^ 32 - (1 + b) % 2 ^ 32)) ∧
      (∀ r, r ≠ .r8 → r ≠ .rcx → t₁.gpr r = t.gpr r) ∧ t₁.rd = t.rd ∧ t₁.wr = t.wr := by
    refine ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hbx]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14]
      rw [low32, two32_sub (Nat.mod_lt _ (by decide))]
    · simp only [cf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14, hbx]
      rw [low32, two32_sub (Nat.mod_lt _ (by decide)), toNat_ofNat_of_lt hm,
        toNat_ofNat_of_lt (by omega_arith)]
    · intro r h₁ h₂; simp only [gpr_setReg, gpr_arithFlags, h₁, h₂, ite_false]
    all_goals rfl
  refine WP.seq (WP.of_runBlock ⟨t₁, run₁, ?_⟩)
  refine WP.ite _ (eval_b hcf₁) (fun ht => ?_) (fun hf => ?_)
  · have h := of_decide_eq_true ht
    exact WP.of_runBlock ⟨t₁, rfl, hm₁, by rw [hr8₁, Nat.min_eq_left (by omega_arith)], hg₁, hrd₁, hwr₁⟩
  · have h := of_decide_eq_false hf
    refine WP.of_runBlock ⟨_, by crun [], ?_, ?_, ?_, ?_, ?_⟩
    · exact hm₁
    · simp only [gpr_setReg, ite_true, hcx₁, Nat.min_eq_right (Nat.le_of_not_lt h)]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, ite_false]; exact hg₁ r h₁ h₂
    · exact hrd₁
    · exact hwr₁

/-- The arguments of the call, and `Ctr₁₊ᵦ`. -/
theorem setup_ok {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {b k : Nat} {t t₂ : State} (I : CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) (hm₂ : t₂.mem = t.mem) (hr8₂ : t₂.gpr .r8 = BitVec.ofNat 64 k)
    (hg₂ : ∀ r, r ≠ .r8 → r ≠ .rcx → t₂.gpr r = t.gpr r) (hrd₂ : t₂.rd = t.rd) (hwr₂ : t₂.wr = t.wr) :
    ∃ t₅, runBlock isa (([.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] : List Instr) ++ ctrAt ++
        ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] : List Instr) ++ ptr .rdx .r15 c1O ++ ([.mov .rcx (.reg .r12)] : List Instr) ++
        ptr .r9 .r15 scrO) t₂ = some t₅ ∧
      Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem ∧
      bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b) ∧
      t₅.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k ∧
      t₅.gpr .rdi = K ∧ t₅.gpr .rsi = BitVec.ofNat 64 R ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₅.gpr .rcx = D + BitVec.ofNat 64 (16 * b) ∧ t₅.gpr .r8 = BitVec.ofNat 64 k ∧
      t₅.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
  have E := I.env
  have E₂ : Env K W SP t₂ := E.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₂ _ (by decide) (by decide)) hrd₂ hwr₂
  have h15 := E₂.r15
  have rR := E₂.perm.wR (show 232 + 8 ≤ 2560 by decide)
  have hRo : t₂.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by
    rw [hm₂, C.readW_kept I.frame (by omega_arith), C.ro]
  obtain ⟨t₃, run₃, hm₃, hsi₃, hax₃, hg₃, hrd₃, hwr₃⟩ : ∃ t₃, runBlock isa
      [.mov .rsi (.mem (at_ .r15 roundsO)), .mov .rax (.reg .r14)] t₂ = some t₃ ∧ t₃.mem = t₂.mem ∧
      t₃.gpr .rsi = BitVec.ofNat 64 R ∧ t₃.gpr .rax = BitVec.ofNat 64 (1 + b) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → t₃.gpr r = t₂.gpr r) ∧ t₃.rd = t₂.rd ∧ t₃.wr = t₂.wr := by
    refine ⟨_, by crun [h15, rR], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rfl
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hRo]
    · simp only [gpr_setReg, ite_true, ite_false, reduceCtorEq, hg₂ .r14 (by decide) (by decide), I.r14]
    · intro r h₁ h₂; simp only [gpr_setReg, h₁, h₂, ite_false]
    all_goals rfl
  have E₃ : Env K W SP t₃ := E₂.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₃ _ (by decide) (by decide)) hrd₃ hwr₃
  have hc0₃ : bytesAt t₃.mem (W + BitVec.ofNat 64 48) 16 = Spec.Ccm.ctrBlock nonce 0 := by
    rw [hm₃, hm₂, C.bytes_kept I.frame (by omega_arith), C.c0]
  have hq16 : n / 16 < 256 ^ (15 - nonce.length) := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) C.hn
  obtain ⟨t₄, run₄, f₄, hc₄, hg₄, hrd₄, hwr₄⟩ :=
    ctrAt_ok E₃ C.h7 C.h13 hc0₃ (i := 1 + b) (by omega_arith) hax₃
  have E₄ : Env K W SP t₄ := E₃.keep (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact hg₄ _ (by decide) (by decide) (by decide)) hrd₄ hwr₄
  have h15₄ := E₄.r15
  have wk := E₄.perm.wW (show 216 + 8 ≤ 2560 by decide)
  have g₄ : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .rdx → r ≠ .rsi → r ≠ .r8 → t₄.gpr r = t.gpr r := fun r a c d e f => by
    rw [hg₄ r a c d, hg₃ r a e, hg₂ r f c]
  have r8₄ : t₄.gpr .r8 = BitVec.ofNat 64 k := by
    rw [hg₄ .r8 (by decide) (by decide) (by decide), hg₃ .r8 (by decide) (by decide), hr8₂]
  obtain ⟨t₅, run₅, hm₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ : ∃ t₅, runBlock isa
      ([.store (at_ .r15 kO) .r8, .mov .rdi (.reg .r13)] ++ ptr .rdx .r15 c1O ++ [.mov .rcx (.reg .r12)] ++
        ptr .r9 .r15 scrO) t₄ = some t₅ ∧ t₅.mem = t₄.mem.writeW (W + BitVec.ofNat 64 216) (BitVec.ofNat 64 k) ∧
      t₅.gpr .rdi = K ∧ t₅.gpr .rsi = BitVec.ofNat 64 R ∧ t₅.gpr .rdx = W + BitVec.ofNat 64 64 ∧
      t₅.gpr .rcx = D + BitVec.ofNat 64 (16 * b) ∧ t₅.gpr .r8 = BitVec.ofNat 64 k ∧
      t₅.gpr .r9 = W + BitVec.ofNat 64 384 ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp, .rbx, .r12, .r14], t₅.gpr r = t.gpr r) ∧ t₅.rd = t.rd ∧ t₅.wr = t.wr := by
    refine ⟨_, by crun [h15₄, wk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [mem_setReg, mem_arithFlags, r8₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, E₄.r13]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        hg₄ .rsi (by decide) (by decide) (by decide), hsi₃]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq,
        g₄ .r12 (by decide) (by decide) (by decide) (by decide) (by decide), I.r12]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, r8₄]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15₄]
    · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq] <;>
        exact g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [rd_setReg, rd_arithFlags]; rw [hrd₄, hrd₃, hrd₂]
    · simp only [wr_setReg, wr_arithFlags]; rw [hwr₄, hwr₃, hwr₂]
  have hdis : (⟨W + BitVec.ofNat 64 64, 16⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 216, 8⟩ :=
    C.lay.w_w (.inl (by decide)) (by decide) (by decide)
  refine ⟨t₅, ?_, ?_, ?_, by rw [hm₅, Mem.readW_writeW_self64], hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩
  · simp only [List.append_assoc]
    rw [runBlock_append, run₃, Option.bind_some, runBlock_append, run₄, Option.bind_some]
    simpa only [List.append_assoc] using run₅
  · rw [hm₅, ← hm₂, ← hm₃]
    exact (f₄.sub fun r hr => ⟨r, by simp only [List.mem_singleton] at hr; subst hr; simp, fun _ h => h⟩).writeW
      (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (by simp) _ (Region.contains_self _ _)
  · rw [hm₅, bytesAt_frame ((Frame.refl _ _).writeW (List.mem_singleton_self ⟨W + BitVec.ofNat 64 216, 8⟩) _
      (Region.contains_self _ _)) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hdis)
      (by decide), hc₄]

/-- What follows the call: `k` blocks past them, and ZF set when none is left. -/
theorem step_ok {W D : Addr} {t : State} {n b k : Nat} (h15 : t.gpr .r15 = W)
    (rk : InRegions (t.rd ++ t.wr) (W + BitVec.ofNat 64 216) 8)
    (hkO : t.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k)
    (hbx : t.gpr .rbx = BitVec.ofNat 64 (n / 16 - b)) (h14 : t.gpr .r14 = BitVec.ofNat 64 (1 + b))
    (h12 : t.gpr .r12 = D + BitVec.ofNat 64 (16 * b)) (hkb : b + k ≤ n / 16) (hn : n < 2 ^ 64) :
    ∃ t', runBlock isa
      [.mov .rax (.mem (at_ .r15 kO)), .alu .sub .rbx (.reg .rax), .alu .add .r14 (.reg .rax),
        .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax), .alu .add .rax (.reg .rax),
        .alu .add .r12 (.reg .rax), .alu .test .rbx (.reg .rbx)] t = some t' ∧ t'.mem = t.mem ∧
      t'.gpr .rbx = BitVec.ofNat 64 (n / 16 - (b + k)) ∧ t'.gpr .r14 = BitVec.ofNat 64 (1 + (b + k)) ∧
      t'.gpr .r12 = D + BitVec.ofNat 64 (16 * (b + k)) ∧ t'.zf = some (decide (b + k = n / 16)) ∧
      (∀ r ∈ [Reg.r13, .r15, .rsp], t'.gpr r = t.gpr r) ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
  refine ⟨_, by crun [h15, rk], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, hbx]
    rw [show n / 16 - (b + k) = n / 16 - b - k by omega_arith]
    exact ofNat_sub (by omega_arith) (by omega_arith)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, h14]
    rw [ofNat_add_ofNat, Nat.add_assoc]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, h12, ofNat_add_ofNat,
      BitVec.add_assoc]
    rw [show 16 * b + (k + k + (k + k) + (k + k + (k + k)) + (k + k + (k + k) + (k + k + (k + k)))) =
      16 * (b + k) by omega_arith]
  · simp only [zf_arithFlags, gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, hkO, hbx]
    rw [ofNat_sub (by omega_arith) (by omega_arith), and_self_beq (by omega_arith)]
    simp only [Option.some.injEq, decide_eq_decide]
    omega_arith
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  all_goals rfl

/-- The state after a chunk of `k` blocks. -/
theorem chunk_inv {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {b k : Nat} {t : State} (I : CtrInv K W SP s R nonce D n b t)
    (hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32) (hkb : b + k ≤ n / 16) {t₅ t₆ t₇ : State}
    (f₅ : Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩] t.mem t₅.mem)
    (hc₅ : bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16 = Spec.Ccm.ctrBlock nonce (1 + b))
    (hsp : t₅.gpr .rsp = SP)
    (h : CtrPost t₅ K (W + BitVec.ofNat 64 64) (D + BitVec.ofNat 64 (16 * b)) (W + BitVec.ofNat 64 384) R k t₆)
    (hm₇ : t₇.mem = t₆.mem) :
    Frame (ctrR W SP D n) s.mem t₇.mem ∧
      bytesAt t₇.mem D (16 * (b + k)) =
        xorFrom (Spec.Ccm.ctxCiph s.mem K R) nonce 1 (bytesAt s.mem D (16 * (b + k))) ∧
      bytesAt t₇.mem (D + BitVec.ofNat 64 (16 * (b + k))) (n - 16 * (b + k)) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * (b + k))) (n - 16 * (b + k)) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  have cR : Frame [⟨W + BitVec.ofNat 64 64, 16⟩, ⟨W + BitVec.ofNat 64 216, 8⟩, ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8] t.mem t₇.mem := by
    have fc := h.frame
    rw [hsp] at fc
    rw [hm₇]
    refine (f₅.sub fun r hr => ?_).trans (fc.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact ⟨_, by simp, fun _ h => h⟩
  have toR : ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩,
      ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8],
      ∃ r' ∈ ctrR W SP D n, Region.Sub r r' := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
    · exact ⟨_, by simp, fun _ h => h⟩
    · exact ⟨⟨D, n⟩, by simp, Offset.sub_base D (by omega_arith)⟩
    · exact ⟨⟨W + BitVec.ofNat 64 384, 2176⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨below SP 16, by simp, below8_sub SP⟩
  -- Separation of the data from what the chunk wrote.
  have sep : ∀ {a l : Nat}, (a + l ≤ 16 * b ∨ 16 * (b + k) ≤ a) → a + l ≤ n →
      ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨W + BitVec.ofNat 64 216, 8⟩,
        ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩, ⟨W + BitVec.ofNat 64 384, 2048⟩, below SP 8],
        (⟨D + BitVec.ofNat 64 a, l⟩ : Region).Disjoint r := by
    intro a l ha hl r hr
    have hB := C.buf.slice (a := a) (k := l) hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact Offset.disjoint D (by omega_arith) (by omega_arith) (by omega_arith)
    · exact hB.w.sub_right (Lay.wSub (by decide))
    · exact (hB.stk.sub_left (below8_sub SP)).symm
  have hbk : 16 * (b + k) = 16 * b + 16 * k := Nat.mul_add _ _ _
  refine ⟨I.frame.trans (cR.sub toR), ?_, ?_⟩
  · -- The blocks done.
    have h₁ : bytesAt t₇.mem D (16 * b) = bytesAt t.mem D (16 * b) := by
      have := bytesAt_frame cR (sep (a := 0) (l := 16 * b) (.inl (by omega_arith)) (by omega_arith)) (by omega_arith)
      rwa [BitVec.add_zero] at this
    have hinc : ∀ i < k, Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.blockAt t₅.mem (W + BitVec.ofNat 64 64)) =
        Spec.Gcm.ofBytes (Spec.Ccm.ctrBlock nonce (1 + b + i)) := fun i hi => by
      show Nat.repeat Spec.Gcm.inc32 i (Spec.Gcm.ofBytes (bytesAt t₅.mem (W + BitVec.ofNat 64 64) 16)) = _
      rw [hc₅]
      exact repeat_inc32_ctrBlock C.h7 C.h13 hk32
        (by have := Nat.lt_of_le_of_lt (Nat.div_le_self n 16) C.hn; omega_arith) i hi
    have hx := ctr32_ccm (by have := C.h13; omega_arith) hinc h.out
    have f₅' : Frame (ctrR W SP D n) s.mem t₅.mem := I.frame.trans (f₅.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨W + BitVec.ofNat 64 64, 32⟩, by simp, Offset.sub W (by decide) (by decide)⟩
      · exact ⟨_, by simp, fun _ h => h⟩)
    have hx₅ : bytesAt t₅.mem (D + BitVec.ofNat 64 (16 * b)) (16 * k) =
        bytesAt s.mem (D + BitVec.ofNat 64 (16 * b)) (16 * k) := by
      have hB := C.buf.slice (a := 16 * b) (k := n - 16 * b) (by omega_arith)
      rw [bytesAt_prefix t₅.mem _ (show 16 * k ≤ n - 16 * b by omega_arith),
        bytesAt_prefix s.mem _ (show 16 * k ≤ n - 16 * b by omega_arith), ← I.rest,
        bytesAt_frame f₅ (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact hB.w.sub_right (Lay.wSub (by decide))
          · exact hB.w.sub_right (Lay.wSub (by decide))) (by omega_arith)]
    rw [hbk, Proof.Cmac.Stream.bytesAt_append, Proof.Cmac.Stream.bytesAt_append, h₁, I.done, hm₇, hx, hx₅,
      C.ciph_kept f₅', xorFrom_append _ _ _ (length_bytesAt _ _ _), Nat.add_comm 1 b]
  · -- The rest of the data.
    have hR' := bytesAt_frame cR (sep (a := 16 * (b + k)) (l := n - 16 * (b + k)) (.inr (Nat.le_refl _))
      (by omega_arith)) (by omega_arith)
    rw [hR', show D + BitVec.ofNat 64 (16 * (b + k)) = D + BitVec.ofNat 64 (16 * b) + BitVec.ofNat 64 (16 * k) by
        rw [add_ofNat_assoc, hbk],
      show n - 16 * (b + k) = n - 16 * b - 16 * k by omega_arith, bytesAt_suffix _ _ (show 16 * k ≤ n - 16 * b by omega_arith),
      bytesAt_suffix _ _ (show 16 * k ≤ n - 16 * b by omega_arith), I.rest]

/-- One chunk. -/
theorem chunk_ok (v : Ctr32Impl) {K W SP : Addr} {s : State} {R : Nat} {nonce : List Byte} {D : Addr} {n : Nat}
    (C : CtrCtx K W SP s R nonce D n) {b : Nat} {t : State} (I : CtrInv K W SP s R nonce D n b t)
    (hb : b < n / 16) :
    WP isa (ctrChunk v.callee) t fun t' => ∃ k, k = min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) ∧ 1 ≤ k ∧
      b + k ≤ n / 16 ∧ CtrInv K W SP s R nonce D n (b + k) t' ∧ t'.zf = some (decide (b + k = n / 16)) := by
  have L := C.lay
  have hn64 : n < 2 ^ 64 := C.buf.lt
  refine seq_assoc (WP.seq (WP.mono (kSel_ok I.rbx I.r14 (by omega_arith)) fun t₂ ⟨hm₂, hr8₂, hg₂, hrd₂, hwr₂⟩ => ?_))
  obtain ⟨k, hk⟩ : ∃ k, k = min (n / 16 - b) (2 ^ 32 - (1 + b) % 2 ^ 32) := ⟨_, rfl⟩
  rw [← hk] at hr8₂
  have hk1 : 1 ≤ k := by rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  have hkb : b + k ≤ n / 16 := by rw [hk]; omega_arith
  have hk32 : (1 + b) % 2 ^ 32 + k ≤ 2 ^ 32 := by
    rw [hk]; have := Nat.mod_lt (1 + b) (show 0 < 2 ^ 32 by decide); omega_arith
  obtain ⟨t₅, run₅, f₅, hc₅, hkO₅, hdi, hsi, hdx, hcx, hr8, hr9, hg₅, hrd₅, hwr₅⟩ :=
    setup_ok C I hb hm₂ hr8₂ hg₂ hrd₂ hwr₂
  have E₅ : Env K W SP t₅ := I.env.keep (fun r hr => hg₅ r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)) hrd₅ hwr₅
  refine WP.seq (WP.of_runBlock ⟨t₅, run₅, ?_⟩)
  -- The call.
  have hS := (C.buf.of_eq (hrd₅.trans I.rd) (hwr₅.trans I.wr)).slice (a := 16 * b) (k := 16 * k) (by omega_arith)
  have hqc : (⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 64, 16⟩ :=
    hS.w.sub_right (Lay.wSub (by decide))
  have hqk : (⟨K, 240⟩ : Region).Disjoint ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩ :=
    C.dk.sub_right (Offset.sub_base D (by omega_arith))
  have hqw : Covers [⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩] t₅.wr := by
    rw [hwr₅, I.wr]; exact covers_off C.dw (by omega_arith) hn64
  refine WP.seq (WP.mono (ctr_call v (cargs L E₅ C.rounds (c := 64) (by decide) (srcBuf hS) hqc hqk hqw
    hdi hsi hdx hcx hr8 hr9)) fun t₆ h => ?_)
  have E₆ : Env K W SP t₆ := E₅.of_saved h.saved h.rd h.wr
  have sv : ∀ r ∈ [Reg.rbx, .r12, .r14], t₆.gpr r = t.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h.saved r (by rcases hr with rfl | rfl | rfl <;> decide), hg₅ r (by rcases hr with rfl | rfl | rfl <;> simp)]
  have dK : ∀ r ∈ [(⟨W + BitVec.ofNat 64 64, 16⟩ : Region), ⟨D + BitVec.ofNat 64 (16 * b), 16 * k⟩,
      ⟨W + BitVec.ofNat 64 384, 2048⟩, below (t₅.gpr .rsp) 8], (⟨W + BitVec.ofNat 64 216, 8⟩ : Region).Disjoint r := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact L.w_w (.inr (by decide)) (by decide) (by decide)
    · exact (hS.w.sub_right (Lay.wSub (by decide))).symm
    · exact L.w_w (.inl (by decide)) (by decide) (by decide)
    · rw [E₅.rsp]; exact ((L.stk_w' (by decide)).sub_left (below8_sub _)).symm
  have hkO : t₆.mem.readW (W + BitVec.ofNat 64 216) 64 = BitVec.ofNat 64 k := by
    rw [h.frame.readW (r := ⟨W + BitVec.ofNat 64 216, 8⟩) (Region.contains_self _ _) dK (by decide), hkO₅]
  obtain ⟨t₇, run₇, hm₇, hbx₇, h14₇, h12₇, hzf₇, hg₇, hrd₇, hwr₇⟩ :=
    step_ok E₆.r15 (E₆.perm.wR (show 216 + 8 ≤ 2560 by decide)) hkO (by rw [sv .rbx (by simp), I.rbx])
      (by rw [sv .r14 (by simp), I.r14]) (by rw [sv .r12 (by simp), I.r12]) hkb hn64
  obtain ⟨fr, dn, rs⟩ := chunk_inv C I hk32 hkb f₅ hc₅ E₅.rsp h hm₇
  exact WP.of_runBlock ⟨t₇, run₇, k, hk, hk1, hkb, ⟨E₆.keep hg₇ hrd₇ hwr₇, by rw [hrd₇, h.rd, hrd₅, I.rd],
    by rw [hwr₇, h.wr, hwr₅, I.wr], h12₇, hbx₇, h14₇, hkb, fr, dn, rs⟩, hzf₇⟩

end VG.Proof.AesCcm.X86_64
