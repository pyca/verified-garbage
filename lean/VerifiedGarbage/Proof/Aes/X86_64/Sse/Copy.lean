module

public import VerifiedGarbage.Proof.Aes.X86_64.Sse.Keys
public import VerifiedGarbage.Proof.Aes.Memory
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-! # Blocks in and out of the buffer -/

@[expose] public section

namespace VG.Proof.Aes.X86_64.Sse

open VG VG.X86_64 VG.X86_64.RegUpd VG.X86_64.StraightX VG.Bitslice VG.Impl.Aes.X86_64.Sse VG.Proof.Aes
open VG.Proof.Aes.Memory (Processed)

/-! ## Bytes -/

theorem writeW128 (m : Mem) (a : Addr) (v : BitVec 128) : m.writeW a v = m.write a 16 v := by
  rw [Mem.writeW]; simp

theorem readW128_byte (m : Mem) (a : Addr) {n : Nat} (hn : n < 16) :
    (m.readW a 128).extractLsb' (8 * n) 8 = m (a + BitVec.ofNat 64 n) := by
  rw [← Mem.extractLsb'_read m a (n := 16) hn]
  simp only [Mem.readW]
  rfl

theorem writeW128_byte (m : Mem) (a : Addr) (v : BitVec 128) {n : Nat} (hn : n < 16) :
    (m.writeW a v) (a + BitVec.ofNat 64 n) = v.extractLsb' (8 * n) 8 := by
  rw [writeW128, Mem.write, Offset.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ite_eq_left hn]

/-- The blocks of the buffer. -/
def bufS (m : Mem) (b : Addr) (i : Nat) : Spec.Aes.State := Spec.Aes.stateAt m (bufAddr b i)

theorem bufIs_bufS (m : Mem) (b : Addr) : BufIs m b (bufS m b) := fun i _ n hn => by
  rw [bufS, Spec.Aes.stateAt, getD_ofFn _ hn]

/-! ## The size of a batch -/

theorem batchSize_ok {s : State} {r : Nat} (hr : r < 2 ^ 64) (h8 : s.gpr .r8 = BitVec.ofNat 64 r) :
    WP isa (.block batchSize) s fun s' =>
      s'.gpr .rdi = BitVec.ofNat 64 (min 8 r) ∧ s'.gpr .r10 = BitVec.ofNat 64 (min 8 r) ∧
      s'.gpr .rax = bufAddr (s.gpr .r9) 0 ∧
      (∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rdi → s'.gpr x = s.gpr x) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  have e8 : BitVec.signExtend 64 (8 : BitVec 32) = 8 := by decide
  have hlt : ((s.gpr .r8).toNat < (8 : BitVec 64).toNat) = (r < 8) := by
    rw [h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]; rfl
  have e0 : BitVec.signExtend 64 (BitVec.ofNat 32 (16 * bufSlot 0)) = BitVec.ofNat 64 (16 * bufSlot 0) := by decide
  by_cases h : r < 8
  · simp only [batchSize, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execCmov, readSrc, e8,
      Option.map_some, Option.bind_some, gpr_setReg, reduceCtorEq, ite_false, arithFlags, State.setFlags, X86_64.eval,
      hlt, h, decide_true, ite_true, Option.some.injEq, exists_eq_left', e0]
    refine ⟨?_, ?_, ?_, fun x a c d => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [h8, Nat.min_eq_right (Nat.le_of_lt h)]
    · simp only [h8, Nat.min_eq_right (Nat.le_of_lt h)]
    · rfl
    · simp only [a, c, d, ite_false]
  · simp only [batchSize, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, execCmov, readSrc, e8,
      Option.map_some, Option.bind_some, gpr_setReg, reduceCtorEq, ite_false, arithFlags, State.setFlags, X86_64.eval,
      hlt, h, decide_false, ite_true, Option.some.injEq, exists_eq_left', e0, Bool.false_eq_true]
    refine ⟨?_, ?_, ?_, fun x a c d => ?_, rfl, rfl, rfl, rfl⟩
    · simp only [Nat.min_eq_left (Nat.le_of_not_lt h)]; rfl
    · simp only [Nat.min_eq_left (Nat.le_of_not_lt h)]; rfl
    · rfl
    · simp only [a, c, d, ite_false]

theorem add00 (a : BitVec 64) : a + BitVec.ofNat 64 0 = a := BitVec.add_zero a

theorem addNat (a : BitVec 64) (x k : Nat) (h : BitVec.signExtend 64 (BitVec.ofNat 32 k) = BitVec.ofNat 64 k) :
    a + BitVec.ofNat 64 x + BitVec.signExtend 64 (BitVec.ofNat 32 k) = a + BitVec.ofNat 64 (x + k) := by
  rw [h, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem subOne (c : Nat) : BitVec.ofNat 64 (c + 1) - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 c := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 1 by decide, BitVec.ofNat_add, BitVec.add_sub_cancel]

/-! ## Into the buffer -/

/-- After `j` blocks from `p` (`s₁`: before the loop). -/
structure CI (s₁ : State) (b p : Addr) (t j : Nat) (s : State) : Prop where
  r11 : s.gpr .r11 = p + BitVec.ofNat 64 (16 * j)
  rax : s.gpr .rax = b + BitVec.ofNat 64 (16 * bufSlot 0 + 16 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (t - j)
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .r11 → s.gpr x = s₁.gpr x
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [bufR b] s₁.mem s.mem
  buf : ∀ i < j, ∀ n < 16, s.mem (bufAddr b i + BitVec.ofNat 64 n) = s₁.mem (p + BitVec.ofNat 64 (16 * i + n))

theorem bufAddr_eq (b : Addr) (j : Nat) : bufAddr b j = b + BitVec.ofNat 64 (16 * bufSlot 0 + 16 * j) := by
  rw [bufAddr, show 16 * bufSlot j = 16 * bufSlot 0 + 16 * j by simp only [bufSlot]; omega]

theorem copyIn_ok {s₁ : State} {b p : Addr} {t : Nat} (ht : t ≤ 8)
    (hsrc : ∀ i < t, InRegions (s₁.rd ++ s₁.wr) (p + BitVec.ofNat 64 (16 * i)) 16)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16)
    (hd : ∀ i < t, Region.Disjoint ⟨p + BitVec.ofNat 64 (16 * i), 16⟩ (bufR b)) {j : Nat} (hj : j < t) {s : State}
    (h : CI s₁ b p t j s) :
    WP isa (.block copyIn) s fun s' => CI s₁ b p t (j + 1) s' ∧ X86_64.eval .ne s' = some (decide (t - (j + 1) ≠ 0)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .r11 + BitVec.ofNat 64 0) 16 := by
    rw [h.r11, h.rd, h.wr]; simpa using hsrc j hj
  have hout : InRegions s.wr (s.gpr .rax + BitVec.ofNat 64 0) 16 := by
    rw [h.rax, h.wr, ← bufAddr_eq]; simpa using hbuf j (by omega)
  have ecnt : s.gpr .r10 - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (t - (j + 1)) := by
    rw [h.r10, show t - j = t - (j + 1) + 1 by omega, subOne]
  apply WP.of_runBlock
  simp only [copyIn, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, State.load128,
    State.store128, ea_at, hin, hout, ite_true, Option.map_some, Option.bind_some, gpr_setXmm, wr_setXmm, mem_setXmm, xmm_setXmm,
    gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  have hfw : Frame [bufR b] s.mem (s.mem.writeW (bufAddr b j) (s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 128)) :=
    (Frame.refl _ _).writeW List.mem_cons_self _ (buf_contains b (by omega))
  refine ⟨⟨?_, ?_, ?_, fun x a c d => ?_, h.rd, h.wr, ?_, fun i hi n hn => ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.r11]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rax]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, c, d, ite_false]; exact h.gpr x a c d
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.r11, add00, ← bufAddr_eq]
    exact h.frame.trans hfw
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.r11, add00, ← bufAddr_eq]
    by_cases hij : i = j
    · subst hij
      rw [writeW128_byte _ _ _ hn, readW128_byte _ _ hn, BitVec.add_assoc, ← BitVec.ofNat_add]
      have := h.frame.bytes (R := ⟨p + BitVec.ofNat 64 (16 * i), 16⟩)
        (fun r hr => by rw [List.mem_singleton.mp hr]; exact hd i hj) (show (16 : Nat) ≤ 2 ^ 64 by decide) hn
      rwa [BitVec.add_assoc, ← BitVec.ofNat_add] at this
    · rw [← h.buf i (by omega) n hn]
      have := (Frame.refl [⟨bufAddr b j, 16⟩] s.mem).writeW List.mem_cons_self
        (s.mem.readW (p + BitVec.ofNat 64 (16 * j)) 128) (Region.contains_self _ _)
      refine this.bytes (R := ⟨bufAddr b i, 16⟩) (fun r hr => ?_) (show (16 : Nat) ≤ 2 ^ 64 by decide) hn
      rw [List.mem_singleton.mp hr]
      exact Offset.disjoint b (d := 16 * bufSlot i) (n := 16) (e := 16 * bufSlot j) (k := 16) (by simp only [bufSlot]; omega)
        (by simp only [bufSlot]; omega) (by simp only [bufSlot]; omega)
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem copyIn_loop {s₁ : State} {b p : Addr} {t : Nat} (ht : t ≤ 8) (h0 : 0 < t)
    (hsrc : ∀ i < t, InRegions (s₁.rd ++ s₁.wr) (p + BitVec.ofNat 64 (16 * i)) 16)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16)
    (hd : ∀ i < t, Region.Disjoint ⟨p + BitVec.ofNat 64 (16 * i), 16⟩ (bufR b)) {s : State} (h : CI s₁ b p t 0 s) :
    WP isa (.loop (.block copyIn) .ne) s (CI s₁ b p t t) := by
  let I : Nat → State → Prop := fun c s => ∃ j, c = t - j ∧ j < t ∧ CI s₁ b p t j s
  refine WP.loop (M := isa) I ?_ t s ⟨0, rfl, h0, h⟩
  rintro c s' ⟨j, rfl, hj, hs'⟩
  refine WP.mono (copyIn_ok ht hsrc hbuf hd hj hs') fun s2 ⟨h2, hz⟩ => ?_
  by_cases hl : t - (j + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = t by omega] at h2
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, j + 1, rfl, by omega, h2⟩

/-! ## Out of the buffer -/

/-- After `j` blocks of the batch that starts at block `k` (`s₁`: before the loop). -/
structure CO (s₁ : State) (m₀ : Mem) (b D : Addr) (n k t : Nat) (F : Nat → Spec.Aes.State) (j : Nat) (s : State) : Prop where
  rcx : s.gpr .rcx = D + BitVec.ofNat 64 (16 * (k + j))
  rax : s.gpr .rax = b + BitVec.ofNat 64 (16 * bufSlot 0 + 16 * j)
  r10 : s.gpr .r10 = BitVec.ofNat 64 (t - j)
  gpr : ∀ x, x ≠ .rax → x ≠ .r10 → x ≠ .rcx → s.gpr x = s₁.gpr x
  rd : s.rd = s₁.rd
  wr : s.wr = s₁.wr
  frame : Frame [⟨D, 16 * n⟩] s₁.mem s.mem
  done : Processed m₀ s.mem D n (k + j) F

theorem copyOut_ok {s₁ : State} {m₀ : Mem} {b D : Addr} {n k t : Nat} {F : Nat → Spec.Aes.State} (ht : t ≤ 8)
    (hkt : k + t ≤ n) (hn : 16 * n ≤ 2 ^ 64) (hD : ⟨D, 16 * n⟩ ∈ s₁.wr)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16) (hd : Region.Disjoint (bufR b) ⟨D, 16 * n⟩)
    (hb : ∀ i < t, ∀ x < 16, s₁.mem (bufAddr b i + BitVec.ofNat 64 x) = (F (k + i)).getD x 0) {j : Nat} (hj : j < t)
    {s : State} (h : CO s₁ m₀ b D n k t F j s) :
    WP isa (.block copyOut) s fun s' => CO s₁ m₀ b D n k t F (j + 1) s' ∧
      X86_64.eval .ne s' = some (decide (t - (j + 1) ≠ 0)) := by
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .rax + BitVec.ofNat 64 0) 16 := by
    rw [add00, h.rax, h.wr, ← bufAddr_eq]
    obtain ⟨R, hR, hc⟩ := hbuf j (by omega)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  have hout : InRegions s.wr (s.gpr .rcx + BitVec.ofNat 64 0) 16 := by
    rw [add00, h.rcx, h.wr]
    exact ⟨_, hD, Offset.contains_base _ (by omega) (by omega)⟩
  have ecnt : s.gpr .r10 - BitVec.signExtend 64 (1 : BitVec 32) = BitVec.ofNat 64 (t - (j + 1)) := by
    rw [h.r10, show t - j = t - (j + 1) + 1 by omega, subOne]
  have hv : ∀ x < 16, (s.mem.readW (bufAddr b j) 128).extractLsb' (8 * x) 8 = (F (k + j)).getD x 0 := fun x hx => by
    rw [readW128_byte _ _ hx, ← hb j hj x hx]
    refine h.frame.bytes (R := ⟨bufAddr b j, 16⟩) (fun r hr => ?_) (show (16 : Nat) ≤ 2 ^ 64 by decide) hx
    rw [List.mem_singleton.mp hr]
    exact hd.sub_left fun y hy => by
      simp only [Region.Contains, bufR, bufAddr, bufSlot] at hy ⊢
      bv_omega
  obtain ⟨hp, hf⟩ := Processed.store hn (by omega) h.done hv
  apply WP.of_runBlock
  simp only [copyOut, runBlock_cons, runStep_some, runBlock_nil, isa, reduceExec, execAlu, readSrc, State.load128,
    State.store128, ea_at, hin, hout, ite_true, Option.map_some, Option.bind_some, gpr_setXmm, wr_setXmm, mem_setXmm, xmm_setXmm,
    gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ecnt, Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, fun x a c d => ?_, h.rd, h.wr, ?_, ?_⟩, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rcx]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true, h.rax]
    exact addNat _ _ 16 (by decide)
  · simp only [gpr_setReg, gpr_arithFlags, ite_true]
  · simp only [gpr_setReg, gpr_arithFlags, a, c, d, ite_false]; exact h.gpr x a c d
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.rcx, add00, ← bufAddr_eq, writeW128]
    exact h.frame.trans hf
  · simp only [mem_setReg, mem_arithFlags, h.rax, h.rcx, add00, ← bufAddr_eq, writeW128]
    exact hp
  · simp only [X86_64.eval, zf_setReg, zf_arithFlags, Option.map_some, Option.some.injEq]
    rw [beq_zero (by omega)]
    simp

theorem copyOut_loop {s₁ : State} {m₀ : Mem} {b D : Addr} {n k t : Nat} {F : Nat → Spec.Aes.State} (ht : t ≤ 8)
    (h0 : 0 < t) (hkt : k + t ≤ n) (hn : 16 * n ≤ 2 ^ 64) (hD : ⟨D, 16 * n⟩ ∈ s₁.wr)
    (hbuf : ∀ i < 8, InRegions s₁.wr (bufAddr b i) 16) (hd : Region.Disjoint (bufR b) ⟨D, 16 * n⟩)
    (hb : ∀ i < t, ∀ x < 16, s₁.mem (bufAddr b i + BitVec.ofNat 64 x) = (F (k + i)).getD x 0) {s : State}
    (h : CO s₁ m₀ b D n k t F 0 s) : WP isa (.loop (.block copyOut) .ne) s (CO s₁ m₀ b D n k t F t) := by
  let I : Nat → State → Prop := fun c s => ∃ j, c = t - j ∧ j < t ∧ CO s₁ m₀ b D n k t F j s
  refine WP.loop (M := isa) I ?_ t s ⟨0, rfl, h0, h⟩
  rintro c s' ⟨j, rfl, hj, hs'⟩
  refine WP.mono (copyOut_ok ht hkt hn hD hbuf hd hb hj hs') fun s2 ⟨h2, hz⟩ => ?_
  by_cases hl : t - (j + 1) = 0
  · refine .inl ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], ?_⟩
    rwa [show j + 1 = t by omega] at h2
  · exact .inr ⟨by rw [show isa.eval = X86_64.eval from rfl, hz]; simp [hl], _, by omega, j + 1, rfl, by omega, h2⟩

end VG.Proof.Aes.X86_64.Sse
