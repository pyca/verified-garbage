module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailO
public import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Tail
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Rounds3
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailRounds3
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Out3
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.TailKL
import VerifiedGarbage.Proof.ChaCha20Poly1305.X86_64.Stitch.Loop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep

/-!
# ChaCha20 and Poly1305 together (x86-64): the last 257 to 511 bytes of `open`

After `open`'s whole chunks, with `n` bytes left (at least `16 k`), their
keystream stored at `ctx + 736` (`kA buf`) while their first `k` blocks are
absorbed, the accumulator stored and the registers restored, `rbx`, `rbp` at
the bytes after those blocks (`TailMidKO`): up to 384 bytes by
`Stitch.tail3O` (`tail3Og_ok`): the constants stored and `Avx2Tail`'s setup
of three sets (`tailA3_ok`), the rounds (two loops, `roundsL_ok`, of
`K3.round4` and `K3.round0`), and the output through `rsi` (`tailBO3_ok`,
`out3_ok`); up to 512 by `Stitch.tailKO` (`tailKOg_ok`): the kernel's eight
blocks (`tailKL_ok`) and `leaveTO`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.X86_64.Stitch

open VG VG.X86_64 VG.Impl.ChaCha20Poly1305.X86_64.Stitch
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64.Avx2 (Consts stR bufR slotsR pairs_ok pairsCode constPairs constPairs_le tPairs
  tPairs_le tconsts_eq consts_eq consts_mem tincs_mem)
open VG.Proof.ChaCha20.X86_64.Avx2Tail (HB YM3 Incs)
open VG.Proof.ChaCha20.X86_64.Avx512Tail (Ctx regn baseR bsize wregs S0)
open VG.Proof.ChaCha20 (CState ctr)
open VG.Spec.ChaCha20 (stateAt serialize keystream innerBlock)
open VG.Spec.Poly1305 (P bytesAt leNum)
open VG.Proof.Poly1305 (absorbAll)
open VG.Proof.Poly1305.X86_64 (hval absorbRegs)

/-- The schedules of `tail3O`'s rounds: four blocks, and none. -/
theorem schedOk_o4 : SchedOk (oblocks 4) (ofirst 4) 4 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem schedOk_o0 : SchedOk (oblocks 0) (ofirst 0) 0 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- After `n` double rounds of three sets from `s₁`, the first `j` blocks at
`q` absorbed: as `TB3`, with `rsi` and `rdi` free. -/
structure K3 (q : Addr) (R0 R1 : BitVec 64) (X : Nat) (V : Nat → CState) (s₁ : State)
    (n j : Nat) (s : State) : Prop where
  hb : HB 3 (fun l => Nat.repeat innerBlock n (V l)) s
  ym : YM3 s
  mem : s.mem = s₁.mem
  gpr : ∀ r, r ∉ absorbRegs → r ≠ .rsi → r ≠ .rdi → s.gpr r = s₁.gpr r
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  acc : Acc R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s

section
variable {q : Addr} {R0 R1 : BitVec 64} {X : Nat} {V : Nat → CState} {s₁ : State}

theorem K3.keep {n j : Nat} {s s' : State} (h : K3 q R0 R1 X V s₁ n j s)
    (g : ∀ r, r ≠ .rsi → r ≠ .rdi → s'.gpr r = s.gpr r) (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : K3 q R0 R1 X V s₁ n j s' :=
  ⟨fun k hk l hl i hi => by simpa only [State.lane, hx, hy] using h.hb k hk l hl i hi,
    fun l => by simpa only [State.lane, hx, hy] using h.ym l, by rw [hm, h.mem],
    fun r hr h₁ h₂ => by rw [g r h₁ h₂, h.gpr r hr h₁ h₂], by rw [hrd, h.rd], by rw [hwr, h.wr],
    acc_keep h.acc g⟩

/-- A double round of three sets absorbing the four blocks at `rsi`. -/
theorem K3.round4 {k : Nat} (hk : Key R0 R1)
    (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {n j : Nat} (hj : j + 4 ≤ k) {s : State}
    (h : K3 q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q + BitVec.ofNat 64 (16 * j)) :
    WP isa (.block (troundG3 (oblocks 4) (ofirst 4) 0)) s fun s' => K3 q R0 R1 X V s₁ (n + 1) (j + 4) s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  have hin' : ∀ off n', off + n' ≤ 16 * 4 →
      InRegions (s.rd ++ s.wr) (q + BitVec.ofNat 64 (16 * j) + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    rw [h.rd, h.wr, Offset.add_add]
    exact hin _ _ (by omega_arith)
  have i₀ : TB3 s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo (q + BitVec.ofNat 64 (16 * j)) R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s
        (ofirst 4 0)) s :=
    ⟨h.hb, h.ym, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, show ofirst 4 0 = 0 from rfl, Nat.mul_zero]
      rw [show bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (troundG3_ok hk hrsi hin' schedOk_o4 (Nat.le_refl _) (by decide) i₀) fun s' h' => ?_
  have hm : bytesAt s.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) =
      bytesAt s₁.mem (q + BitVec.ofNat 64 (16 * j)) (16 * 4) := by rw [h.mem]
  exact ⟨⟨h'.hb, h'.ym, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], acc_next hm h'.poly⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

/-- A double round of three sets absorbing nothing. -/
theorem K3.round0 {k : Nat} (hk : Key R0 R1)
    (hin : ∀ off n, off + n ≤ 16 * k → InRegions (s₁.rd ++ s₁.wr) (q + BitVec.ofNat 64 off) n)
    {n j : Nat} {s : State} (h : K3 q R0 R1 X V s₁ n j s) (hrsi : s.gpr .rsi = q) :
    WP isa (.block (troundG3 (oblocks 0) (ofirst 0) 0)) s fun s' => K3 q R0 R1 X V s₁ (n + 1) j s' ∧
      s'.gpr .rsi = s.gpr .rsi ∧ s'.gpr .rdi = s.gpr .rdi := by
  have i₀ : TB3 s (fun l => Nat.repeat innerBlock n (V l))
      (AccTo q R0 R1 (absorbAll (rN R0 R1) X (bytesAt s₁.mem q (16 * j))) s (ofirst 0 0)) s :=
    ⟨h.hb, h.ym, rfl, fun _ _ => rfl, rfl, rfl, by
      simp only [AccTo, show ofirst 0 0 = 0 from rfl, Nat.mul_zero]
      rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
      exact h.acc⟩
  refine WP.mono (troundG3_ok hk hrsi (fun off n' hn => by rw [h.rd, h.wr]; exact hin off n' hn) schedOk_o0
    (Nat.zero_le _) (by decide) i₀) fun s' h' => ?_
  have a := h'.poly
  simp only [AccTo, show ofirst 0 1 = 0 from rfl, Nat.mul_zero] at a
  rw [show bytesAt s.mem q 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil] at a
  exact ⟨⟨h'.hb, h'.ym, by rw [h'.mem, h.mem], fun r hr h₁ h₂ => by rw [h'.gpr r hr, h.gpr r hr h₁ h₂],
    by rw [h'.rd, h.rd], by rw [h'.wr, h.wr], a⟩, h'.gpr _ (by decide), h'.gpr _ (by decide)⟩

end

section
variable {c : Addr}

/-- The state, 64 bytes below `buf`, where `roundsL` leaves `rdi`. -/
theorem bf_sub64 : bfA c - 64 = stA c := by
  simp only [bfA, stA]
  rw [show BitVec.ofNat 64 128 = BitVec.ofNat 64 64 + 64 from rfl, ← BitVec.add_assoc, BitVec.add_sub_cancel]

theorem tailA3_eq : tailA3 = pairsCode tPairs ++ (pairsCode constPairs ++
    (([.mov .r12 (.reg .r9), .mov .r9 (.reg .rcx)] : List Instr) ++
    (Impl.ChaCha20.X86_64.Avx2Tail.setup3 ++ ([.mov .r9 (.reg .r12)] : List Instr)))) := by
  simp only [tailA3, tconsts_eq, consts_eq, List.append_assoc]

/-- `tailA3`: the constants stored, and the input states of the six blocks
after the counter of the state at `stA c` in the vector registers. -/
theorem tailA3_ok {s : State} (hrcx : s.gpr .rcx = bfA c) (hrdi : s.gpr .rdi = stA c)
    (hst : stR (stA c) ∈ s.wr) (hb : bufR (bfA c) ∈ s.wr) :
    WP isa (.block tailA3) s fun s' =>
      HB 3 (fun j => ctr (stateAt s.mem (stA c)) j) s' ∧ YM3 s' ∧ s'.mem = tMem c s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .r12 → s'.gpr r = s.gpr r) ∧ s'.gpr .r12 = s.gpr .r9 ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [tailA3_eq]
  refine WP.block_append (WP.mono (pairs_ok tPairs tPairs_le hrcx hb) fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => ?_)
  refine WP.block_append (WP.mono (pairs_ok (buf := bfA c) constPairs constPairs_le (s := s₁)
    (by rw [g₁ _ (by decide), hrcx]) (by rw [wr₁]; exact hb)) fun s₂ ⟨m₂, g₂, rd₂, wr₂⟩ => ?_)
  refine WP.block_append (WP.mono movs_ok fun s₃ ⟨r12₃, r9₃, g₃, m₃, rd₃, wr₃, _, _⟩ => ?_)
  have mm : s₃.mem = tMem c s.mem := by rw [m₃, m₂, m₁]
  have rdi₃ : s₃.gpr .rdi = stA c := by
    rw [g₃ _ (by decide) (by decide), g₂ _ (by decide), g₁ _ (by decide), hrdi]
  have r9₃' : s₃.gpr .r9 = bfA c := by rw [r9₃, g₂ _ (by decide), g₁ _ (by decide), hrcx]
  have wr₃' : s₃.wr = s.wr := by rw [wr₃, wr₂, wr₁]
  have hc : Ctx 0 s₃ := ctx0 rdi₃ r9₃' (by rw [wr₃']; exact hst) (by rw [wr₃']; exact hb)
  have cst : Consts s₃.mem (s₃.gpr .r9) := by rw [mm, r9₃']; exact consts_mem _ _
  have inc : Incs s₃.mem (s₃.gpr .r9) := by rw [mm, r9₃']; exact tincs_mem _ _
  have S₃ : S0 s₃ = stateAt s.mem (stA c) := by
    simp only [S0, rdi₃, mm]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame (tMem_frame _) (by simpa using st_bf)
  refine WP.block_append (WP.mono (setup3_ok0 hc cst inc) fun s₄ ⟨hz, ym, m₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.mono mov9_ok fun s₅ ⟨r9₅, g₅, m₅, rd₅, wr₅, x₅, y₅⟩ => ⟨?_, ?_, by rw [m₅, m₄, mm], fun r h₁ h₂ => ?_,
    by rw [g₅ _ (by decide), g₄, r12₃, g₂ _ (by decide), g₁ _ (by decide)], by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃']⟩
  · intro k hk l hl i hi
    simp only [State.lane, x₅, y₅]
    rw [← S₃]; exact hz k hk l hl i hi
  · intro l; simp only [State.lane, x₅, y₅]; exact ym l
  · by_cases h9 : r = .r9
    · subst h9; rw [r9₅, g₄, r12₃, g₂ _ (by decide), g₁ _ (by decide)]
    · rw [g₅ r h9, g₄, g₃ r h₂ h9, g₂ r h₁, g₁ r h₁]

/-- The regions of `tail3O`'s output: the ChaCha20 state at `rdi`, `buf` at
`r9`, and 384 bytes at `ctx + 736` (in `kA buf`) at `rsi`. -/
theorem ctx96 {s : State} (hrdi : s.gpr .rdi = stA c) (hr9 : s.gpr .r9 = bfA c)
    (hrsi : s.gpr .rsi = c + BitVec.ofNat 64 736) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) (hk : kR (bfA c) ∈ s.wr) : Ctx 96 s := by
  have r0 : regn 96 s 0 = stR (stA c) := by simp only [regn, baseR, bsize, hrdi, Nat.reduceMul]
  have r1 : regn 96 s 1 = bufR (bfA c) := by simp only [regn, baseR, bsize, hr9, Nat.reduceMul]
  have r2 : regn 96 s 2 = ⟨c + BitVec.ofNat 64 736, 384⟩ := by
    simp only [regn, baseR, bsize, hrsi, Nat.reduceMul]
  have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  have d01 : (regn 96 s 0).Disjoint (regn 96 s 1) := by rw [r0, r1]; exact st_bf (c := c)
  have d02 : (regn 96 s 0).Disjoint (regn 96 s 2) := by
    rw [r0, r2]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have d12 : (regn 96 s 1).Disjoint (regn 96 s 2) := by
    rw [r1, r2]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  refine ⟨fun b i n hb3 h hn => ?_, fun b b' hb hb' ne => ?_, by decide⟩
  · rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;> simp only [bsize] at h
    · rw [r0]; exact ⟨_, hst, Offset.contains_base _ (by omega_arith) (by lit_omega)⟩
    · rw [r1]; exact ⟨_, hb, Offset.contains_base _ (by omega_arith) (by lit_omega)⟩
    · rw [r2]; refine ⟨_, hk, ?_⟩; rw [kc, Offset.add_add]
      exact Offset.contains c (by omega_arith) (by omega_arith) (by decide)
  · rcases (by omega_arith : b = 0 ∨ b = 1 ∨ b = 2) with rfl | rfl | rfl <;>
      rcases (by omega_arith : b' = 0 ∨ b' = 1 ∨ b' = 2) with rfl | rfl | rfl
    · exact absurd rfl ne
    · exact d01
    · exact d02
    · exact d01.symm
    · exact absurd rfl ne
    · exact d12
    · exact d02.symm
    · exact d12.symm
    · exact absurd rfl ne

theorem rsi736_ok {s : State} (hr15 : s.gpr .r15 = c) :
    WP isa (.block (Impl.ChaCha20Poly1305.X86_64.ptr .rsi .r15 736)) s fun s' =>
      s'.gpr .rsi = c + BitVec.ofNat 64 736 ∧ (∀ r, r ≠ .rsi → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm ∧ s'.ymmHi = s.ymmHi := by
  have se : BitVec.signExtend 64 (BitVec.ofNat 32 736) = BitVec.ofNat 64 736 := by decide
  apply WP.of_runBlock
  simp only [Impl.ChaCha20Poly1305.X86_64.ptr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', ↓reduceIte, se, hr15]
  exact ⟨trivial, fun r hr => by simp [hr], trivial, trivial, trivial, rfl, rfl⟩

/-- `tailBO3`: the accumulator reduced and stored, the registers restored,
`rbx`, `rbp` past the first `k` blocks, and the keystream of the three sets
at `ctx + 736`. -/
theorem tailBO3_ok {k : Nat} (sk : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * k)) = BitVec.ofNat 64 (16 * k))
    (sc : scalCode (.block (storeTO k)) = true) {vs : Nat → CState} {s : State}
    (hz : HB 3 vs s) (hrcx : s.gpr .rcx = bfA c) (hrdi : s.gpr .rdi = stA c) (hst : stR (stA c) ∈ s.wr)
    (hb : bufR (bfA c) ∈ s.wr) (hps : psR c ∈ s.wr) (hkr : kR (bfA c) ∈ s.wr) (hi : Incs s.mem (bfA c))
    (h2 : (s.gpr .rbp).toNat ≤ 4) :
    WP isa (.block (tailBO3 k)) s fun s' =>
      (∀ k' < 384, s'.mem (kA (bfA c) + BitVec.ofNat 64 k') =
        (serialize (Proof.ChaCha20.X86_64.Avx2.plus vs (stateAt s.mem (stA c)) (k' / 64))).getD (k' % 64) 0) ∧
      leNum (bytesAt s'.mem (psA c) 24) = hval s % P ∧
      Frame [accR c, bufR (bfA c), kR (bfA c)] s.mem s'.mem ∧
      s'.gpr .rbx = s.gpr .rsi + BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .rbp = s.mem.readW (c + BitVec.ofNat 64 544) 64 - BitVec.ofNat 64 (16 * k) ∧
      s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64 ∧
      s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64 ∧
      s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64 ∧ s'.gpr .r15 = c ∧
      s'.gpr .rcx = bfA c ∧ s'.gpr .rsp = s.gpr .rsp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  have ka : kA (bfA c) = c + BitVec.ofNat 64 736 := by simp only [kA, bfA, Offset.add_add]
  simp only [tailBO3, leaveTO_eq, List.append_assoc]
  refine WP.block_append (WP.mono (WP.vecKeep scal_reduce (Proof.Poly1305.X86_64.reduce_ok s))
    fun s₁ ⟨⟨red, k₁⟩, x₁, y₁⟩ => ?_)
  refine WP.block_append (WP.mono (WP.vecKeep sc (storeTO_ok sk (c := c) (s := s₁)
    (by rw [k₁.gpr', hrcx]) (by rw [k₁.2.2.2]; exact hps)))
    fun s₂ ⟨⟨m₂, rbx₂, rbp₂, r12₂, r13₂, r14₂, r15₂, g₂, rd₂, wr₂⟩, x₂, y₂⟩ => ?_)
  refine WP.block_append (WP.mono (movR_ok .r9 .rcx) fun s₃ ⟨r9₃, g₃, m₃, rd₃, wr₃, x₃, y₃⟩ => ?_)
  refine WP.block_append (WP.mono (rsi736_ok (c := c) (s := s₃) (by rw [g₃ _ (by decide), r15₂]))
    fun s₄ ⟨rsi₄, g₄, m₄, rd₄, wr₄, x₄, y₄⟩ => ?_)
  have k12 : ∀ r, r = .rdi ∨ r = .rcx ∨ r = .rsi ∨ r = .rsp → s₂.gpr r = s.gpr r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), k₁.gpr']
  have g34 : ∀ r, r ≠ .r9 → r ≠ .rsi → s₄.gpr r = s₂.gpr r := fun r h9 hs => by rw [g₄ r hs, g₃ r h9]
  have rdi₄ : s₄.gpr .rdi = stA c := by rw [g34 _ (by decide) (by decide), k12 _ (.inl rfl), hrdi]
  have rcx₄ : s₄.gpr .rcx = bfA c := by rw [g34 _ (by decide) (by decide), k12 _ (.inr (.inl rfl)), hrcx]
  have r9₄ : s₄.gpr .r9 = bfA c := by rw [g₄ _ (by decide), r9₃, k12 _ (.inr (.inl rfl)), hrcx]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, wr₃, wr₂, k₁.2.2.2]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, rd₃, rd₂, k₁.2.2.1]
  have m₄' : s₄.mem = accMem s.mem c (s₁.gpr .r11) (s₁.gpr .rbx) (s₁.gpr .rbp) := by rw [m₄, m₃, m₂, k₁.2.1]
  have fa : Frame [accR c] s.mem s₄.mem := by rw [m₄']; exact accMem_frame _ _ _ _ _
  have hc : Ctx 96 s₄ := ctx96 rdi₄ r9₄ rsi₄ (by rw [wr₄']; exact hst) (by rw [wr₄']; exact hb)
    (by rw [wr₄']; exact hkr)
  have hi₄ : Incs s₄.mem (s₄.gpr .r9) := by
    rw [r9₄]
    refine Proof.ChaCha20.X86_64.Avx2Tail.incs_frame hi fa ?_
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    have e : Proof.ChaCha20.X86_64.Avx2.hiR (bfA c) = ⟨c + BitVec.ofNat 64 256, 192⟩ := by
      simp only [Proof.ChaCha20.X86_64.Avx2.hiR, bfA, Offset.add_add]
    rw [e]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have hz₄ : HB 3 vs s₄ := hb_of_vec hz (by rw [x₄, x₃, x₂, x₁]) (by rw [y₄, y₃, y₂, y₁])
  have S₄ : S0 s₄ = stateAt s.mem (stA c) := by
    simp only [S0, rdi₄]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame fa (by
      intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide))
  have acc₄ : leNum (bytesAt s₄.mem (psA c) 24) = hval s % P := by
    rw [m₄', accMem_acc]; exact red h2
  rw [show Impl.ChaCha20.X86_64.Avx2Tail.addIn3 ++ (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++
      (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++ (storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256 ++
      ([.vop .vzeroupper] : List Instr)))) = (Impl.ChaCha20.X86_64.Avx2Tail.addIn3 ++
      (storeSetS .xmm0 .xmm1 .xmm2 .xmm3 0 ++ (storeSetS .xmm4 .xmm5 .xmm6 .xmm7 128 ++
      storeSetS .xmm8 .xmm9 .xmm10 .xmm11 256))) ++ ([.vop .vzeroupper] : List Instr) by
    simp only [List.append_assoc]]
  refine WP.block_append (WP.mono (out3_ok hc hi₄ hz₄) fun s₅ ⟨b₅, f₅, g₅, rd₅, wr₅⟩ => ?_)
  refine WP.mono (Proof.ChaCha20.X86_64.Avx2.vz_ok s₅) fun s₆ ⟨g₆, m₆, rd₆, wr₆⟩ => ?_
  have gg : ∀ r, s₆.gpr r = s₄.gpr r := fun r => by rw [g₆, g₅]
  have f₄₆ : Frame [bufR (bfA c), kR (bfA c)] s₄.mem s₆.mem := by
    rw [m₆]
    refine f₅.sub fun r hr => ?_
    simp only [wregs, r9₄, rsi₄, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR (bfA c), by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨kR (bfA c), by simp, by rw [kc]; exact Region.sub_prefix (by decide)⟩
  have hb9 : bytesAt s₆.mem (psA c) 24 = bytesAt s₄.mem (psA c) 24 :=
    bytesAt_frame f₄₆ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact Offset.disjoint c (Or.inr (by decide)) (by decide) (by decide)
      · rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)) (by decide)
  refine ⟨fun k' hk' => ?_, by rw [hb9, acc₄], (fa.mono (by simp)).trans (f₄₆.mono (by simp)), ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, by rw [rd₆, rd₅, rd₄'], by rw [wr₆, wr₅, wr₄']⟩
  · rw [m₆, ka, ← rsi₄, b₅ k' hk', S₄]
  · rw [gg, g34 _ (by decide) (by decide), rbx₂, k₁.gpr']
  · rw [gg, g34 _ (by decide) (by decide), rbp₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r12₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r13₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r14₂, k₁.2.1]
  · rw [gg, g34 _ (by decide) (by decide), r15₂]
  · rw [gg, rcx₄]
  · rw [gg, g34 _ (by decide) (by decide), k12 _ (.inr (.inr (.inr rfl)))]

end

/-- After `tail3O` or `tailKO`, from `s`: the keystream of the `n` bytes
left at `kA buf` (`ctx + 736`), their first `k` blocks absorbed, the
accumulator stored, `rbx`, `rbp` the bytes after those blocks, and the
stashed registers restored. -/
structure TailMidKO (c dp : Addr) (o n k : Nat) (R0 R1 : BitVec 64) (X : Nat) (sp : Addr)
    (s s' : State) : Prop where
  ks : ∀ i < n, s'.mem (kA (bfA c) + BitVec.ofNat 64 i) = (keystream (stateAt s.mem (stA c)) n).getD i 0
  acc : leNum (bytesAt s'.mem (psA c) 24) =
    absorbAll (rN R0 R1) X (bytesAt s.mem (dp + BitVec.ofNat 64 o) (16 * k)) % P
  frame : Frame [accR c, bufR (bfA c), kR (bfA c)] s.mem s'.mem
  rbx : s'.gpr .rbx = dp + BitVec.ofNat 64 (o + 16 * k)
  rbp : s'.gpr .rbp = BitVec.ofNat 64 (n - 16 * k)
  r12 : s'.gpr .r12 = s.mem.readW (c + BitVec.ofNat 64 520) 64
  r13 : s'.gpr .r13 = s.mem.readW (c + BitVec.ofNat 64 528) 64
  r14 : s'.gpr .r14 = s.mem.readW (c + BitVec.ofNat 64 536) 64
  r15 : s'.gpr .r15 = c
  rsp : s'.gpr .rsp = sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- `tail3O 16`, with 256 to 384 bytes left. -/
theorem tail3Og_ok {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1) {X : Nat}
    {o n : Nat} {sp : Addr} (hkn : 256 ≤ n) (hhi : n ≤ 384) {s : State} (h : TPO c dp L o n R0 R1 X sp s)
    (hkr : kR (bfA c) ∈ s.wr) :
    WP isa (tail3O 16) s (TailMidKO c dp o n 16 R0 R1 X sp s) := by
  have hLe := hl.L_lt
  have hTL := h.le
  unfold tail3O
  -- The constants and the setup.
  refine WP.seq (WP.mono (tailA3_ok h.rcx h.rdi h.st h.bf)
    fun s₁ ⟨hz₁, ym₁, m₁, gk₁, _, rd₁, wr₁⟩ => ?_)
  have tb₁ : TB3 s₁ (fun j => ctr (stateAt s.mem (stA c)) j) (AccTo (dp + BitVec.ofNat 64 o) R0 R1 X s₁ 0) s₁ := by
    refine ⟨hz₁, ym₁, rfl, fun _ _ => rfl, rfl, rfl, ?_⟩
    simp only [AccTo, Nat.mul_zero]
    rw [show bytesAt s₁.mem (dp + BitVec.ofNat 64 o) 0 = [] from rfl, VG.Proof.Poly1305.absorbAll_nil]
    have a := h.acc
    exact ⟨by rw [gk₁ _ (by decide) (by decide)]; exact a.r8, by rw [gk₁ _ (by decide) (by decide)]; exact a.r9,
      by rw [gk₁ _ (by decide) (by decide)]; exact a.r10, by rw [gk₁ _ (by decide) (by decide)]; exact a.h2,
      by simp only [hval, gk₁ (Reg.r11) (by decide) (by decide), gk₁ (Reg.rbx) (by decide) (by decide),
        gk₁ (Reg.rbp) (by decide) (by decide)]; exact a.val⟩
  have hrsi₁ : s₁.gpr .rsi = dp + BitVec.ofNat 64 o := by rw [gk₁ _ (by decide) (by decide), h.rsi]
  have hin : ∀ off n', off + n' ≤ 16 * 16 →
      InRegions (s₁.rd ++ s₁.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    refine ⟨_, List.mem_append_right _ (by rw [wr₁]; exact h.dw), ?_⟩
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  -- The rounds.
  have k₁ : K3 (dp + BitVec.ofNat 64 o) R0 R1 X (fun j => ctr (stateAt s.mem (stA c)) j) s₁ 0 0 s₁ :=
    ⟨tb₁.hb, tb₁.ym, rfl, fun _ _ _ _ => rfl, rfl, rfl, tb₁.poly⟩
  refine WP.seq (WP.mono (roundsL_ok (K3 (dp + BitVec.ofNat 64 o) R0 R1 X _ s₁) (k := 16) (by decide) (by decide)
    (by decide) (by decide) (fun _ _ _ _ h' g x y m rd wr => h'.keep g x y m rd wr)
    (fun n s hn h' hr => K3.round4 hk hin (j := 4 * n) (show 4 * n + 4 ≤ 16 by omega_arith) h' hr)
    (fun n s _ _ h' hr => K3.round0 hk hin h' hr) k₁ hrsi₁) fun s₂ ⟨tb₂, r₂, d₂⟩ => ?_)
  have hrcx₂ : s₂.gpr .rcx = bfA c := by
    rw [tb₂.gpr _ (by decide) (by decide) (by decide), gk₁ _ (by decide) (by decide), h.rcx]
  have hrdi₂ : s₂.gpr .rdi = stA c := by rw [d₂, hrcx₂, bf_sub64]
  have hrsi₂ : s₂.gpr .rsi = dp + BitVec.ofNat 64 o := r₂
  have wr₂ : s₂.wr = s.wr := by rw [tb₂.wr, wr₁]
  have m₂ : s₂.mem = tMem c s.mem := by rw [tb₂.mem, m₁]
  have hi₂ : Incs s₂.mem (bfA c) := by rw [m₂]; exact Proof.ChaCha20.X86_64.Avx2.tincs_mem _ _
  refine (WP.mono (tailBO3_ok (k := 16) (by decide) (by decide) tb₂.hb hrcx₂ hrdi₂ (by rw [wr₂]; exact h.st)
    (by rw [wr₂]; exact h.bf) (by rw [wr₂]; exact h.ps) (by rw [wr₂]; exact hkr) hi₂ tb₂.acc.h2)
    fun s₃ ⟨ks₃, acc₃, f₃, rbx₃, rbp₃, r12₃, r13₃, r14₃, r15₃, rcx₃, rsp₃, rd₃, wr₃⟩ => ?_)
  -- What the stores of `tailA3` keep in the context.
  have ctxk : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₂.mem.readW (c + BitVec.ofNat 64 d) 64 = s.mem.readW (c + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    rw [m₂]
    refine (tMem_frame _).readW (r := ⟨c + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
  have hslot : s₂.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 n := by
    rw [ctxk 544 (by decide) (by decide), ← slot_eq, h.left]
  have S₂ : stateAt s₂.mem (stA c) = stateAt s.mem (stA c) := by
    rw [m₂]
    exact Proof.ChaCha20.X86_64.Xor.stateAt_frame (tMem_frame _) (by simpa using st_bf)
  refine ⟨fun i hi => ?_, ?_, ?_, by rw [rbx₃, hrsi₂, Offset.add_add],
    by rw [rbp₃, hslot, Offset.ofNat_sub_ofNat (by omega_arith)],
    by rw [r12₃, ctxk 520 (by decide) (by decide)], by rw [r13₃, ctxk 528 (by decide) (by decide)],
    by rw [r14₃, ctxk 536 (by decide) (by decide)], r15₃,
    by rw [rsp₃, tb₂.gpr _ (by decide) (by decide) (by decide), gk₁ _ (by decide) (by decide), h.rsp],
    by rw [rd₃, tb₂.rd, rd₁],
    by rw [wr₃, wr₂]⟩
  · rw [ks₃ i (by omega_arith), S₂, Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hi]
  · -- The accumulator: the first 16 blocks absorbed.
    have hb1 : bytesAt s₁.mem (dp + BitVec.ofNat 64 o) (16 * 16) =
        bytesAt s.mem (dp + BitVec.ofNat 64 o) (16 * 16) := by
      rw [m₁]
      refine bytesAt_frame (tMem_frame _) (fun r hr => ?_) (by omega_arith)
      simp only [List.mem_singleton] at hr; subst hr
      exact (hl.bf_d.symm.sub_left (Offset.sub_base _ (by omega_arith)))
    have v := tb₂.acc.val
    rw [hb1] at v
    rw [acc₃, v]
  · have f1 : Frame [bufR (bfA c)] s.mem s₂.mem := by rw [m₂]; exact tMem_frame _
    exact (f1.mono (by simp)).trans f₃

/-- `tailKO vl 24`, with 384 to 512 bytes left. -/
theorem tailKOg_ok (vl : Bool) {c dp : Addr} {L : Nat} (hl : Lay c dp L) {R0 R1 : BitVec 64} (hk : Key R0 R1)
    {X : Nat} {o n : Nat} {sp : Addr} (hkn : 384 ≤ n) (hhi : n ≤ 512) {s : State}
    (h : TPO c dp L o n R0 R1 X sp s) (hkr : kR (bfA c) ∈ s.wr) (hcs : Consts s.mem (bfA c)) :
    WP isa (tailKO vl 24) s (TailMidKO c dp o n 24 R0 R1 X sp s) := by
  have hLe := hl.L_lt
  have hTL := h.le
  have kc : kR (bfA c) = ⟨c + BitVec.ofNat 64 736, 512⟩ := by simp only [kR, kA, bfA, Offset.add_add]
  have dsk : (stR (stA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dbk : (bufR (bfA c)).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dak : (accR c).Disjoint (kR (bfA c)) := by
    rw [kc]; exact Offset.disjoint c (Or.inl (by decide)) (by decide) (by decide)
  have dqs : (⟨dp + BitVec.ofNat 64 o, 16 * 24⟩ : Region).Disjoint (slotsR (bfA c)) :=
    ((hl.cd (d := 128) (n := 128) (by decide)).sub_right (Offset.sub_base _ (by omega_arith))).symm
  have hin : ∀ off n', off + n' ≤ 16 * 24 →
      InRegions (s.rd ++ s.wr) (dp + BitVec.ofNat 64 o + BitVec.ofNat 64 off) n' := by
    intro off n' hn
    refine ⟨_, List.mem_append_right _ h.dw, ?_⟩
    rw [Offset.add_add]
    exact Offset.contains_base _ (by omega_arith) (by omega_arith)
  unfold tailKO
  refine WP.seq (WP.mono (tailKL_ok vl (k := 24) (by decide) (by decide) (by decide) (by decide) (by decide) hk
    h.rdi h.rcx h.rsi bf_sub64 h.st h.bf hkr hin
    hcs st_bf dsk dbk dqs h.acc) fun s₂ ⟨d₂, a₂, f₂, g₂, rd₂, wr₂⟩ => ?_)
  rw [leaveTO_eq, List.append_assoc]
  refine WP.block_append (WP.mono (Proof.Poly1305.X86_64.reduce_ok s₂) fun s₃ ⟨red, k₃⟩ => ?_)
  refine WP.block_append (WP.mono (storeTO_ok (k := 24) (by decide) (c := c) (s := s₃)
    (by rw [k₃.gpr', g₂ _ (by decide), h.rcx]) (by rw [k₃.2.2.2, wr₂]; exact h.ps))
    fun s₄ ⟨m₄, rbx₄, rbp₄, r12₄, r13₄, r14₄, r15₄, g₄, rd₄, wr₄⟩ => ?_)
  refine WP.mono (Proof.ChaCha20.X86_64.Avx2.vz_ok s₄) fun s₅ ⟨g₅, m₅, rd₅, wr₅⟩ => ?_
  have m₃ : s₃.mem = s₂.mem := k₃.2.1
  have mA : s₅.mem = accMem s₂.mem c (s₃.gpr .r11) (s₃.gpr .rbx) (s₃.gpr .rbp) := by rw [m₅, m₄, m₃]
  have fa : Frame [accR c] s₂.mem s₅.mem := by rw [mA]; exact accMem_frame _ _ _ _ _
  have f₂' : Frame [bufR (bfA c), kR (bfA c)] s.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨bufR (bfA c), by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨kR (bfA c), by simp, fun _ h => h⟩
  have rd₂' : ∀ d, 520 ≤ d → d + 8 ≤ 552 →
      s₃.mem.readW (c + BitVec.ofNat 64 d) 64 = s.mem.readW (c + BitVec.ofNat 64 d) 64 := fun d h₁ h₂ => by
    rw [m₃]
    refine f₂'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint c (Or.inr (by omega_arith)) (by omega_arith) (by decide)
    · rw [kc]; exact Offset.disjoint c (Or.inl (by omega_arith)) (by omega_arith) (by decide)
  have gs : ∀ r, r = .rsi ∨ r = .rsp → s₃.gpr r = s.gpr r := by
    intro r hr; rcases hr with rfl | rfl <;> rw [k₃.gpr', g₂ _ (by decide)]
  have hslot : s₃.mem.readW (c + BitVec.ofNat 64 544) 64 = BitVec.ofNat 64 n := by
    rw [rd₂' 544 (by decide) (by decide), ← slot_eq, h.left]
  refine ⟨fun i hi => ?_, ?_, (f₂'.mono (by simp)).trans (fa.mono (by simp)),
    by rw [g₅, rbx₄, gs _ (.inl rfl), h.rsi, Offset.add_add],
    by rw [g₅, rbp₄, hslot, Offset.ofNat_sub_ofNat (by omega_arith)],
    by rw [g₅, r12₄, rd₂' 520 (by decide) (by decide)], by rw [g₅, r13₄, rd₂' 528 (by decide) (by decide)],
    by rw [g₅, r14₄, rd₂' 536 (by decide) (by decide)], by rw [g₅, r15₄],
    by rw [g₅, g₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), gs _ (.inr rfl), h.rsp],
    by rw [rd₅, rd₄, k₃.2.2.1, rd₂], by rw [wr₅, wr₄, k₃.2.2.2, wr₂]⟩
  · rw [fa _ (fun r hr hc => by
      simp only [List.mem_singleton] at hr; subst hr
      exact dak _ hc (kR_contains _ (by omega_arith))), d₂ i (by omega_arith),
      Proof.ChaCha20.X86_64.Avx2.plus_block, VG.Proof.ChaCha20.keystream_getD _ hi]
  · rw [mA, accMem_acc]
    show hval s₃ = _
    rw [red a₂.h2, a₂.val]

end VG.Proof.ChaCha20Poly1305.X86_64.Stitch
