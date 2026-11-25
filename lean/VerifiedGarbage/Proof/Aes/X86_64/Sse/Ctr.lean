module

public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Copy
public import VerifiedGarbage.Proof.Aes.Blocks
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Interleave

/-! # Counter blocks, and the keystream XORed into the data -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes
open VG.Proof.Aes.Memory (Processed)
open VG.Spec.Gcm (blockAt inc32 toBytes Block)

theorem rep_add {α : Type} (f : α → α) (a : α) (i : Nat) :
    ∀ k, Nat.repeat f k (Nat.repeat f i a) = Nat.repeat f (i + k) a
  | 0 => rfl
  | k + 1 => congrArg f (rep_add f a i k)

/-! ## The counter's word -/

theorem bswap32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  rw [show bswap32 v = byteRev32 v from rfl, byteRev32_getLsbD _ (by omega), show (8 * k + j) / 8 = k by omega,
    show (8 * k + j) % 8 = j by omega]

/-- The last word of the counter block at `p`, as a number. -/
theorem icb_lo (m : Mem) (p : Addr) :
    bswap32 (m.readW (p + BitVec.ofNat 64 12) 32) = (blockAt m p).extractLsb' 0 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [show t = 8 * (t / 8) + t % 8 by omega, bswap32_bit _ (by omega) (by omega), BitVec.getLsbD_extractLsb', Nat.zero_add,
    decide_eq_true (by omega), Bool.true_and, show 8 * (t / 8) + t % 8 = 8 * (15 - (15 - t / 8)) + t % 8 by omega,
    blockAt_bit _ _ (by omega) (by omega), Mem.readW, BitVec.getLsbD_setWidth, decide_eq_true (by omega), Bool.true_and,
    getLsbD_read _ _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add,
    show 12 + (8 * (3 - t / 8) + t % 8) / 8 = 15 - t / 8 by omega, show (8 * (3 - t / 8) + t % 8) % 8 = t % 8 by omega]

theorem writeW32_byte (m : Mem) (a : Addr) (v : BitVec 32) {n : Nat} (hn : n < 4) :
    (m.writeW a v) (a + BitVec.ofNat 64 n) = v.extractLsb' (8 * n) 8 := by
  rw [Mem.writeW, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left (by omega)]
  simp

/-- The bytes of a block with the word `bswap (bswap w₀ + i)` in its last four:
the counter block `i` on. -/
theorem ctr_bytes {m m' : Mem} {p q : Addr} {i : Nat}
    (h1 : ∀ k < 12, m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k))
    (h2 : ∀ k < 4, m' (q + BitVec.ofNat 64 (12 + k)) =
      (bswap32 (bswap32 (m.readW (p + BitVec.ofNat 64 12) 32) + BitVec.ofNat 32 i)).extractLsb' (8 * k) 8) {k : Nat} (hk : k < 16) :
    m' (q + BitVec.ofNat 64 k) = (toBytes (Nat.repeat inc32 i (blockAt m p))).getD k 0 := by
  rw [ctrBlock_byte _ _ hk]
  split
  · rename_i h; rw [h1 k h, toBytes_blockAt _ _ hk]
  · rename_i h
    have := h2 (k - 12) (by omega)
    rw [show 12 + (k - 12) = k by omega] at this
    rw [this, icb_lo]
    refine byte_ext fun j hj => ?_
    rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb', bswap32_bit _ (by omega) hj]
    simp only [hj, decide_true, Bool.true_and]
    congr 1; omega

theorem ctr_block {m m' : Mem} {p q : Addr} {i : Nat}
    (h : ∀ k < 16, m' (q + BitVec.ofNat 64 k) = (toBytes (Nat.repeat inc32 i (blockAt m p))).getD k 0) :
    blockAt m' q = Nat.repeat inc32 i (blockAt m p) :=
  block_ext fun k hk => by rw [toBytes_blockAt _ _ hk, h k hk]

/-! ## The counter blocks of a batch -/

/-- The bytes of counter block `i` in the buffer at `q`, from the counter block at `p`. -/
def CtrAt (m₀ m : Mem) (p q : Addr) (i : Nat) : Prop :=
  ∀ k < 16, m (q + BitVec.ofNat 64 k) = (toBytes (Nat.repeat inc32 i (blockAt m₀ p))).getD k 0

/-- After the counter blocks below `n`. -/
structure CB (s₁ : State) (b C : Addr) (n : Nat) (s : State) : Prop where
  xmm0 : s.xmm .xmm0 = s₁.mem.readW C 128
  rax : (s.gpr .rax).setWidth 32 = bswap32 (s₁.mem.readW (C + BitVec.ofNat 64 12) 32)
  r9 : s.gpr .r9 = b
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → s.gpr x = s₁.gpr x
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [bufR b] s₁.mem s.mem
  ctr : ∀ i < n, CtrAt s₁.mem s.mem C (bufAddr b i) i

theorem ctrBlock_ok {s₁ : State} {b C : Addr} {n : Nat} (hn : n < 8) (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16)
    {s : State} (h : CB s₁ b C n s) : WP isa (.block (ctrBlock n)) s (CB s₁ b C (n + 1)) := by
  have h1 : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 (16 * bufSlot n)) 16 := by
    rw [h.r9, h.wr]; exact hbuf n hn
  have h2 : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 (16 * bufSlot n + 12)) 4 := by
    rw [h.r9, h.wr]
    obtain ⟨R, hR, hc⟩ := hbuf n hn
    refine ⟨R, hR, ?_⟩
    simp only [Region.Contains, bufAddr, bufSlot] at hc ⊢
    bv_omega
  apply WP.of_runBlock
  simp only [ctrBlock, stx, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu32, readSrc32, State.store128,
    State.store32, State.setReg32, ea_slot, ea_at, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h1, h2,
    wr_setReg, wr_arithFlags, mem_setReg, mem_arithFlags, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', setWidth_setWidth_32]
  have fw1 : Frame [⟨bufAddr b n, 16⟩] s.mem (s.mem.writeW (bufAddr b n) (s.xmm .xmm0)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)
  have e12 : s.gpr .r9 + BitVec.ofNat 64 (16 * bufSlot n + 12) = bufAddr b n + BitVec.ofNat 64 12 := by
    rw [h.r9, bufAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e0 : s.gpr .r9 + BitVec.ofNat 64 (16 * bufSlot n) = bufAddr b n := by rw [h.r9, bufAddr]
  rw [e12, e0, h.rax]
  have fw : ∀ v : BitVec 32, Frame [⟨bufAddr b n, 16⟩] s.mem
      ((s.mem.writeW (bufAddr b n) (s.xmm .xmm0)).writeW (bufAddr b n + BitVec.ofNat 64 12) v) := fun v =>
    fw1.writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  have sub : Region.Sub ⟨bufAddr b n, 16⟩ (bufR b) := fun x hx => by
    simp only [Region.Contains, bufR, bufAddr, bufSlot] at hx ⊢
    bv_omega
  refine ⟨h.xmm0, ?_, h.r9, fun x a c => ?_, h.rd, h.wr, h.frame.trans ((fw _).sub fun r hr => ⟨_, List.mem_singleton.mpr rfl, by
    rw [List.mem_singleton.mp hr]; exact sub⟩), fun i hi => ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]; exact h.rax
  · simp only [gpr_setReg, gpr_arithFlags, c, ite_false]; exact h.gpr x a c
  · dsimp only
    by_cases hin : i = n
    · subst hin
      intro k hk
      refine ctr_bytes (m := s₁.mem) (p := C) (fun k hk => ?_) (fun k hk => ?_) hk
      · rw [show ∀ v : BitVec 32, ((s.mem.writeW (bufAddr b i) (s.xmm .xmm0)).writeW (bufAddr b i + BitVec.ofNat 64 12) v)
            (bufAddr b i + BitVec.ofNat 64 k) = (s.mem.writeW (bufAddr b i) (s.xmm .xmm0)) (bufAddr b i + BitVec.ofNat 64 k) from
          fun v => ((Frame.refl [⟨bufAddr b i + BitVec.ofNat 64 12, 4⟩] _).writeW List.mem_cons_self v
            (Region.contains_self _ _)).bytes (R := ⟨bufAddr b i, 12⟩) (fun r hr => by
              rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide))
              (show (12 : Nat) ≤ 2 ^ 64 by decide) hk]
        rw [writeW128_byte _ _ _ (by omega), h.xmm0, readW128_byte _ _ (by omega)]
      · rw [BitVec.ofNat_add 12 k, ← BitVec.add_assoc, writeW32_byte _ _ _ hk]
    · intro k hk
      rw [← h.ctr i (by omega) k hk]
      refine (fw _).bytes (R := ⟨bufAddr b i, 16⟩) (fun r hr => ?_) (show (16 : Nat) ≤ 2 ^ 64 by decide) hk
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := 16 * bufSlot i) (n := 16) (e := 16 * bufSlot n) (k := 16) (by simp only [bufSlot]; omega)
        (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega)

theorem ctrBlocks_ok {s₁ : State} {b C : Addr} (h9 : s₁.gpr .r9 = b) (hC : s₁.gpr .rdx = C)
    (hin : InRegions (s₁.rd ++ s₁.wr) C 16) (hin4 : InRegions (s₁.rd ++ s₁.wr) (C + BitVec.ofNat 64 12) 4)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16) :
    WP isa (.block ctrBlocks) s₁ (CB s₁ b C 8) := by
  refine WP.block_append ?_
  refine WP.mono (Q := CB s₁ b C 0) ?_ fun s2 h2 => ?_
  · apply WP.of_runBlock
    have hin' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdx + BitVec.ofNat 64 0) 16 := by rw [add00, hC]; exact hin
    have hin4' : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdx + BitVec.ofNat 64 12) 4 := by rw [hC]; exact hin4
    simp only [runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, readSrc32, State.load128, State.load32,
      State.setReg32, ea_at, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, hin', hin4', ite_true, Option.map_some,
      gpr_setReg, Option.some.injEq, exists_eq_left', setWidth_setWidth_32]
    rw [hC]
    refine ⟨?_, ?_, ?_, fun x a c => ?_, rfl, rfl, Frame.refl _ _, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · simp only [xmm_setReg, xmm_setXmm, ite_true, add00]
    · simp only [gpr_setReg, ite_true, setWidth_setWidth_32]
    · simp only [gpr_setReg, gpr_setXmm, reduceCtorEq, ite_false]; exact h9
    · simp only [gpr_setReg, gpr_setXmm, a, ite_false]
  have go : ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap ctrBlock)) s2 (CB s₁ b C n) := by
    intro n hn
    induction n with
    | zero => exact WP.block_nil h2
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact WP.block_append (WP.mono (ih (by omega)) fun s3 h3 => ctrBlock_ok (by omega) hbuf h3)
  exact go 8 (Nat.le_refl _)

/-! ## The keystream XORed into the data -/

/-- Where the source may be: at the output, or apart from it. -/
def Mode (X D : Addr) (n : Nat) : Prop := X = D ∨ Region.Disjoint ⟨X, 16 * n⟩ ⟨D, 16 * n⟩

/-- After `j` blocks of the batch that starts at block `k` (`s₁`: before the loop). -/
structure CX (s₁ : State) (m₀ : Mem) (b X D : Addr) (n k t : Nat) (F : Nat → Spec.Aes.State) (j : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = X + BitVec.ofNat 64 (16 * (k + j))
  r11 : s.gpr .r11 = D + BitVec.ofNat 64 (16 * (k + j))
  rax : s.gpr .rax = b + BitVec.ofNat 64 (16 * bufSlot 0 + 16 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (t - j)
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → x ≠ .r11 → s.gpr x = s₁.gpr x
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨D, 16 * n⟩] s₁.mem s.mem
  done : Processed m₀ s.mem D n (k + j) F

/-- The arguments of the loop. -/
structure XP (s₁ : State) (m₀ : Mem) (b X D : Addr) (n k t : Nat) (F K : Nat → Spec.Aes.State) : Prop where
  t8 : t ≤ 8
  kt : k + t ≤ n
  n16 : 16 * n < 2 ^ 64
  inD : ⟨D, 16 * n⟩ ∈ s₁.wr
  inX : ⟨X, 16 * n⟩ ∈ s₁.rd ++ s₁.wr
  buf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16
  disj : Region.Disjoint (bufR b) ⟨D, 16 * n⟩
  mode : Mode X D n
  src : ∀ i < 16 * n, 16 * k ≤ i → s₁.mem (X + BitVec.ofNat 64 i) = m₀ (X + BitVec.ofNat 64 i)
  ks : ∀ i < t, ∀ x < 16, s₁.mem (bufAddr b i + BitVec.ofNat 64 x) = (K (k + i)).getD x 0
  out : ∀ i < n, ∀ x < 16, (F i).getD x 0 = (K i).getD x 0 ^^^ m₀ (X + BitVec.ofNat 64 (16 * i + x))

theorem xorBlock_ok {s₁ : State} {m₀ : Mem} {b X D : Addr} {n k t : Nat} {F K : Nat → Spec.Aes.State}
    (hp : XP s₁ m₀ b X D n k t F K) {j : Nat} (hj : j < t) {s : State} (h : CX s₁ m₀ b X D n k t F j s) :
    WP isa (.block xorBlock) s fun s' => CX s₁ m₀ b X D n k t F (j + 1) s' ∧
      X86_64.eval .ne s' = some (decide (t - (j + 1) ≠ 0)) := by
  have ht8 := hp.t8
  have hkt := hp.kt
  have hn := hp.n16
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 0) 16 := by
    rw [add00, h.rax, h.wr, ← bufAddr_eq]
    obtain ⟨R, hR, hc⟩ := hp.buf j (by omega)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have hinX : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 0) 16 := by
    rw [add00, h.rcx, h.rd, h.wr]
    exact ⟨_, hp.inX, Offset.contains_base _ (by omega) (by omega)⟩
  have hout : InRegions s.wr (s.gpr .r11 + BitVec.ofNat 64 0) 16 := by
    rw [add00, h.r11, h.wr]
    exact ⟨_, hp.inD, Offset.contains_base _ (by omega) (by omega)⟩
  have ecnt : s.gpr .r10 - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (t - (j + 1)) := by
    rw [h.r10, show t - j = t - (j + 1) + 1 by omega, subOne]
  have hb : ∀ x < 16, s.mem (bufAddr b j + BitVec.ofNat 64 x) = (K (k + j)).getD x 0 := fun x hx => by
    rw [← hp.ks j hj x hx]
    refine h.frame.bytes (R := ⟨bufAddr b j, 16⟩) (fun r hr => ?_) (show (16 : Nat) ≤ 2 ^ 64 by decide) hx
    rw [List.mem_singleton.mp hr]
    exact hp.disj.sub_left fun y hy => by
      simp only [Region.Contains, bufR, bufAddr, bufSlot] at hy ⊢
      bv_omega
  have hsrc : ∀ x < 16, s.mem (X + BitVec.ofNat 64 (16 * (k + j) + x)) = m₀ (X + BitVec.ofNat 64 (16 * (k + j) + x)) := by
    intro x hx
    rcases hp.mode with rfl | hd
    · rw [h.done _ (by omega), ite_eq_right (by omega)]
    · rw [← hp.src _ (by omega) (by omega)]
      exact h.frame.bytes (R := ⟨X, 16 * n⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd)
        (show 16 * n ≤ 2 ^ 64 by omega) (show 16 * (k + j) + x < 16 * n by omega)
  have hv : ∀ x < 16, (s.mem.readW (bufAddr b j) 128 ^^^ s.mem.readW (X + BitVec.ofNat 64 (16 * (k + j))) 128).extractLsb' (8 * x) 8 =
      (F (k + j)).getD x 0 := fun x hx => by
    rw [BitVec.extractLsb'_xor, readW128_byte _ _ hx, readW128_byte _ _ hx, hb x hx, BitVec.add_assoc, ← BitVec.ofNat_add,
      hsrc x hx, hp.out _ (by omega) x hx]
  obtain ⟨hp', hf⟩ := Processed.store (by omega) (by omega) h.done hv
  apply WP.of_runBlock
  simp only [xorBlock, px, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, State.load128,
    State.store128, XOp.exec, XBinOp.eval, ea_at, hin, hinX, hout, ite_true, Option.map_some, Option.bind_some, gpr_setXmm, rd_setXmm,
    wr_setXmm, mem_setXmm, xmm_setXmm, gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq,
    exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_, fun x a c d e => ?_, h.rd, h.wr, ?_, ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rcx]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.r11]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rax]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, c, d, e, ite_false]; exact h.gpr x a c d e
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.rcx, h.r11, add00, ← bufAddr_eq, writeW128]
    exact h.frame.trans hf
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.rcx, h.r11, add00, ← bufAddr_eq, writeW128]
    exact hp'
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem xor_loop {s₁ : State} {m₀ : Mem} {b X D : Addr} {n k t : Nat} {F K : Nat → Spec.Aes.State}
    (hp : XP s₁ m₀ b X D n k t F K) (h0 : 0 < t) {s : State} (h : CX s₁ m₀ b X D n k t F 0 s) :
    WP isa (.loop (.block xorBlock) .ne) s (CX s₁ m₀ b X D n k t F t) := by
  let I : Nat → State → Prop := fun c s => ∃ j, c = t - j ∧ j < t ∧ CX s₁ m₀ b X D n k t F j s
  refine WP.loop (M := isa) I ?_ t s ⟨0, rfl, h0, h⟩
  rintro c s' ⟨j, rfl, hj, hs'⟩
  refine WP.mono (xorBlock_ok hp hj hs') fun s2 ⟨h2, hz⟩ => ?_
  by_cases hl : t - (j + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = t by omega] at h2
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, j + 1, rfl, by omega, h2⟩

/-! ## The counter moved on -/

theorem ctrNext_ok {s : State} {C : Addr} {t r : Nat} (hC : s.gpr .rdx = C) (hd : s.gpr .rdi = BitVec.ofNat 64 t)
    (hr : s.gpr .r8 = BitVec.ofNat 64 (r + t)) (hr64 : r < 2 ^ 64) (hw : ⟨C, 16⟩ ∈ s.wr) :
    WP isa (.block ctrNext) s fun s' => blockAt s'.mem C = Nat.repeat inc32 t (blockAt s.mem C) ∧
      Frame [⟨C, 16⟩] s.mem s'.mem ∧ s'.gpr .r8 = BitVec.ofNat 64 r ∧
      (∀ x, x ≠ .rax → x ≠ .r8 → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      X86_64.eval .ne s' = some (decide (r ≠ 0)) := by
  have hin : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 12) 4 := by
    rw [hC]; exact ⟨_, hw, Offset.contains_base _ (by decide) (by decide)⟩
  have hin' : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 12) 4 := by
    obtain ⟨R, hR, hc⟩ := hin; exact ⟨R, List.mem_append_right _ hR, hc⟩
  have ecnt : s.gpr .r8 - s.gpr .rdi = BitVec.ofNat 64 r := by
    rw [hr, hd, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [ctrNext, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execAlu32, readSrc, readSrc32,
    State.load32, State.store32, State.setReg32, ea_at, hin, hin', ite_true, Option.map_some, Option.bind_some, gpr_setReg,
    gpr_arithFlags, wr_setReg, wr_arithFlags, mem_setReg, mem_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq,
    exists_eq_left', setWidth_setWidth_32]
  have ew : (s.gpr .rdi).setWidth 32 = BitVec.ofNat 32 t := by
    rw [hd]; apply BitVec.eq_of_toNat_eq; simp
  rw [hC, ew]
  refine ⟨ctr_block fun k hk => ctr_bytes (fun k hk => ?_) (fun k hk => ?_) hk, ?_, ?_, fun x a c => ?_, rfl, ?_, ?_⟩
  · exact ((Frame.refl [⟨C + BitVec.ofNat 64 12, 4⟩] s.mem).writeW List.mem_cons_self _ (Region.contains_self _ _)).bytes
      (R := ⟨C, 12⟩) (fun r hr => by rw [List.mem_singleton.mp hr]; exact Offset.base_disjoint _ (by decide) (by decide))
      (show (12 : Nat) ≤ 2 ^ 64 by decide) hk
  · rw [BitVec.ofNat_add 12 k, ← BitVec.add_assoc]
    exact writeW32_byte _ _ _ hk
  · exact (Frame.refl _ _).writeW List.mem_cons_self _ (Offset.contains_base _ (by decide) (by decide))
  · trivial
  · simp only [a, c, ite_false]
  · trivial
  · show some (!(BitVec.ofNat 64 r == 0)) = _
    rw [beq_zero hr64]
    simp

end VG.Proof.Aes.X86_64.Sse
