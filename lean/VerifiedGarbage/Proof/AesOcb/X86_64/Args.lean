import VerifiedGarbage.Proof.AesOcb.X86_64.Callee

/-!
# AES-OCB on x86-64: the calls of the block functions

Untrusted: everything here is checked by Lean. `callBlocks b args` sets up
a call of `b` (`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`) with the
key schedule of the key context, the rounds kept in `W`, the `n` blocks at
`D` that `args` sets (`Dst`: blocks of `W` below 512, `dstW`, or the data,
`dstD`) and the working space at `W + 512` (`callBlocks_ok`).
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesOcb.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesOcb.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesCcm.X86_64 (covers_left covers_cons covers_nil covers_append covers_off runBlock_append)

/-- `n` blocks at `D` for a call: apart from the key context, the working
space at `W + 512` and the stack below `SP`, and readable and writable. -/
structure Dst (K W SP : Addr) (s : State) (D : Addr) (n : Nat) : Prop where
  wrap : D.toNat + 16 * n ≤ 2 ^ 64
  k : (⟨K, 256⟩ : Region).Disjoint ⟨D, 16 * n⟩
  scr : (⟨D, 16 * n⟩ : Region).Disjoint ⟨W + BitVec.ofNat 64 512, 2048⟩
  stk : (below SP 8).Disjoint ⟨D, 16 * n⟩
  rd : Covers [⟨D, 16 * n⟩] (s.rd ++ s.wr)
  wr : Covers [⟨D, 16 * n⟩] s.wr

theorem covers_prefix {p : Addr} {k n : Nat} {rs : List Region} (h : Covers [⟨p, k⟩] rs) (hn : n ≤ k) :
    Covers [⟨p, n⟩] rs := fun a m ⟨r, hr, hc⟩ => by
  simp only [List.mem_singleton] at hr; subst hr
  exact h a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega⟩

theorem toNat_W {W : Addr} (hw : W.toNat + 2560 ≤ 2 ^ 64) {d : Nat} (hd : d < 2560) :
    (W + BitVec.ofNat 64 d).toNat = W.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]

/-- Blocks of `W` below 512. -/
theorem dstW {K W SP : Addr} {s : State} (L : Lay K W SP) (P : Perm K W s) {d n : Nat} (h : d + 16 * n ≤ 512) :
    Dst K W SP s (W + BitVec.ofNat 64 d) n where
  wrap := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt (W + BitVec.ofNat 64 d).isLt
    · rw [toNat_W L.ww (by omega)]; have := L.ww; omega
  k := L.k_w.sub_right (Lay.wSub (by omega))
  scr := L.w_w (.inl (by omega)) (by omega) (by decide)
  stk := L.stk_w' (by omega)
  rd := covers_left (P.wC (by omega))
  wr := P.wC (by omega)

/-- Blocks of the data. -/
theorem dstD {K W SP : Addr} {s : State} {D : Addr} {n : Nat} (h : DBuf K W SP s D (16 * n)) :
    Dst K W SP s D n where
  wrap := h.wrap
  k := h.k
  scr := h.w.sub_right (Lay.wSub (by decide))
  stk := h.stk
  rd := h.rd
  wr := h.wr

theorem Dst.of_eq {K W SP : Addr} {s s' : State} {D : Addr} {n : Nat} (h : Dst K W SP s D n)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Dst K W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd, wr := by rw [hwr]; exact h.wr }

/-- What the arguments `args` of a call set: `rdx` and `rcx` (to `D` and `n`),
nothing else but `rax`. -/
def ArgsOk (args : List Instr) (s : State) (D : Addr) (n : Nat) : Prop :=
  ∃ s₁, runBlock isa args s = some s₁ ∧ s₁.gpr .rdx = D ∧ s₁.gpr .rcx = BitVec.ofNat 64 n ∧
    (∀ r, r ≠ .rdx → r ≠ .rcx → r ≠ .rax → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
    s₁.wr = s.wr

theorem sext1 : BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 := by decide

/-- One block at `W + d`. -/
theorem oneBlock_ok {W : Addr} {s : State} (h15 : s.gpr .r15 = W) (d : Nat) (hd : d < 2 ^ 31) :
    ArgsOk (oneBlock d) s (W + BitVec.ofNat 64 d) 1 := by
  refine ⟨_, by orun [oneBlock, h15], ?_, ?_, fun r h1 h2 _ => ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, sext1]
  · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h1, h2]
  all_goals rfl

theorem BPost.congr {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {s₀ s s' : State} {K D S : Addr}
    {R n : Nat} (h : BPost f s K D S R n s') (hm : s.mem = s₀.mem) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hsp : s.gpr .rsp = s₀.gpr .rsp) :
    BPost f s₀ K D S R n s' where
  rd := by rw [h.rd, hrd]
  wr := by rw [h.wr, hwr]
  saved r hr := by rw [h.saved r hr, hg r hr]
  frame := by rw [← hm, ← hsp]; exact h.frame
  out := by rw [← hm]; exact h.out

/-- A call of `b`, after `args`. -/
theorem callBlocks_ok {f : Nat → List Byte → Spec.Aes.State → Spec.Aes.State} {b : Impl.Aes.X86_64.Blocks}
    (ok : ∀ s, (Proof.Aes.blocksX86_64 f).pre s →
      ∃ t s', Exec isa b.code s t s' ∧ abiPreserved s s' ∧ (Proof.Aes.blocksX86_64 f).post s s')
    (nosp : NoSp b.code) (depth : b.code.depth = 0)
    {K W SP : Addr} (L : Lay K W SP) {s : State} (E : Env K W SP s) {R : Nat} (hR : R = 10 ∨ R = 12 ∨ R = 14)
    (hrnd : s.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R)
    {args : List Instr} {D : Addr} {n : Nat} (ha : ArgsOk args s D n) (hD : Dst K W SP s D n) :
    WP isa (callBlocks b args) s (BPost f s K D (W + BitVec.ofNat 64 512) R n) := by
  obtain ⟨s₁, run₁, rdx₁, rcx₁, g₁, m₁, rd₁, wr₁⟩ := ha
  have r₁ : InRegions (s₁.rd ++ s₁.wr) (W + BitVec.ofNat 64 232) 8 := by
    rw [rd₁, wr₁]; exact E.perm.wR (by decide)
  have h15 : s₁.gpr .r15 = W := by rw [g₁ _ (by decide) (by decide) (by decide), E.r15]
  have h14 : s₁.gpr .r14 = K := by rw [g₁ _ (by decide) (by decide) (by decide), E.r14]
  have hrnd₁ : s₁.mem.readW (W + BitVec.ofNat 64 232) 64 = BitVec.ofNat 64 R := by rw [m₁, hrnd]
  obtain ⟨s₂, run₂, rdi₂, rsi₂, rdx₂, rcx₂, r8₂, g₂, m₂, rd₂, wr₂⟩ : ∃ s₂,
      runBlock isa [mvr .rdi .r14, ld .rsi .r15 rndO, mvr .r8 .r15, addi .r8 scrO] s₁ = some s₂ ∧
      s₂.gpr .rdi = K ∧ s₂.gpr .rsi = BitVec.ofNat 64 R ∧ s₂.gpr .rdx = D ∧ s₂.gpr .rcx = BitVec.ofNat 64 n ∧
      s₂.gpr .r8 = W + BitVec.ofNat 64 512 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → s₂.gpr r = s₁.gpr r) ∧ s₂.mem = s₁.mem ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr := by
    refine ⟨_, by orun [h14, h15, r₁, hrnd₁], ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h14]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15, hrnd₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rdx₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, rcx₁]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, reduceCtorEq, h15]
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, ite_false, h1, h2, h3]
    all_goals rfl
  have hs : s₂.gpr .rsp = SP := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide), E.rsp]
  refine WP.seq (WP.of_runBlock ⟨s₂, by rw [runBlock_append, run₁, Option.bind_some, run₂], ?_⟩)
  have hD₂ := hD.of_eq (s' := s₂) (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
  have hc : BCall s₂ K D (W + BitVec.ofNat 64 512) R n :=
    { rdi := rdi₂, rsi := rsi₂, rdx := rdx₂, rcx := rcx₂, r8 := r8₂, rounds := hR, wrap := hD.wrap
      kd := hD.k.sub_left (Region.sub_prefix (by decide))
      ks := (L.k_w.sub_left (Region.sub_prefix (by decide))).sub_right (Lay.wSub (by decide))
      ds := hD.scr
      stkK := by rw [hs]; exact L.stk_k.sub_right (Region.sub_prefix (by decide))
      stkD := by rw [hs]; exact hD.stk
      stkS := by rw [hs]; exact L.stk_w' (by decide)
      reads := covers_append (covers_cons (covers_prefix (by rw [rd₂, rd₁, wr₂, wr₁]; exact E.perm.k)
          (by decide)) covers_nil)
        (covers_cons hD₂.rd (covers_cons (covers_left (by rw [wr₂, wr₁]; exact E.perm.wC (by decide))) covers_nil))
      writes := covers_cons hD₂.wr (covers_cons (by rw [wr₂, wr₁]; exact E.perm.wC (by decide)) covers_nil) }
  refine WP.mono (blk_call ok nosp depth hc) fun s' h => h.congr (by rw [m₂, m₁]) (by rw [rd₂, rd₁])
    (by rw [wr₂, wr₁]) (fun r hr => ?_) (by rw [hs, E.rsp])
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rw [g₂ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
    g₁ _ (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]

end VG.Proof.AesOcb.X86_64
