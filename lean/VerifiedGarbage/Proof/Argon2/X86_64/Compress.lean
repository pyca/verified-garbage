import VerifiedGarbage.Impl.Argon2.X86_64.ClearBlock
import VerifiedGarbage.Impl.Argon2.X86_64.MemoryInit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.PermuteRows
import VerifiedGarbage.Impl.Argon2.X86_64.Compress
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitClear`. -/
section

/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit

def clearMem (m : Mem) (p : Addr) : Nat → Mem
  | 0 => m
  | n + 1 => (VG.Proof.Argon2.X86_64.MemoryInit.clearMem m p n).writeW (p + BitVec.ofNat 64 (8 * n)) (0 : BitVec 64)

theorem clearMem_frame (m : Mem) (p : Addr) (n : Nat) (bound : 8 * n < 2 ^ 64) :
    Frame [⟨p, 8 * n⟩] m (VG.Proof.Argon2.X86_64.MemoryInit.clearMem m p n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    have smaller : Frame [⟨p, 8 * (n + 1)⟩] m (VG.Proof.Argon2.X86_64.MemoryInit.clearMem m p n) :=
      (ih (by omega)).sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by omega)⟩)
    exact smaller.writeW (List.mem_singleton_self _) (0 : BitVec 64)
      (Offset.contains_base _ (by omega) (by omega))

theorem clearMem_word (m : Mem) (p : Addr) (n j : Nat)
    (bound : 8 * n < 2 ^ 64) (hj : j < n) :
    (VG.Proof.Argon2.X86_64.MemoryInit.clearMem m p n).readW (p + BitVec.ofNat 64 (8 * j)) 64 = 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [VG.Proof.Argon2.X86_64.MemoryInit.clearMem]
    by_cases eq : j = n
    · subst j; exact Mem.readW_writeW_self64 _ _ _
    · rw [Mem.readW_writeW_sep ?_ (by decide)]
      · exact ih (by omega) (by omega)
      · exact Offset.sep p (by omega) (by omega) (by omega)

theorem clearWord_ok (s : State) (hw : InRegions s.wr (s.gpr .r14) 8) :
    WP isa (.block clearWord) s fun t =>
      t.mem = s.mem.writeW (s.gpr .r14) (s.gpr .rcx) ∧
      t.gpr .r14 = s.gpr .r14 + 8 ∧ t.gpr .rax = s.gpr .rax - 1 ∧
      t.zf = some (s.gpr .rax - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .r14 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [clearWord, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    State.store64, execAlu, HPrime.ea_at, BitVec.add_zero,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    show (BitVec.signExtend 64 (8 : BitVec 32)) = 8 from rfl,
    show (BitVec.signExtend 64 (1 : BitVec 32)) = 1 from rfl,
    hw, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial,
    fun r h1 h2 => by simp only [h1, h2, ite_false], trivial, trivial⟩

structure ClearI (s₀ : State) (p : Addr) (n j : Nat) (s : State) : Prop where
  bound : j ≤ n
  destination : s.gpr .r14 = p + BitVec.ofNat 64 (8 * j)
  count : s.gpr .rax = BitVec.ofNat 64 (n - j)
  zero : s.gpr .rcx = 0
  other : ∀ r, r ≠ .rax → r ≠ .r14 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.Argon2.X86_64.MemoryInit.clearMem s₀.mem p j

theorem clearLoop_ok (s₀ : State) (p : Addr) (n : Nat) (lo : 1 ≤ n)
    (bound : 8 * n < 2 ^ 64) (dst : s₀.gpr .r14 = p)
    (count : s₀.gpr .rax = BitVec.ofNat 64 n) (zero : s₀.gpr .rcx = 0)
    (write : ∀ j < n, InRegions s₀.wr (p + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.loop (.block clearWord) .ne) s₀ (VG.Proof.Argon2.X86_64.MemoryInit.ClearI s₀ p n n) := by
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ VG.Proof.Argon2.X86_64.MemoryInit.ClearI s₀ p n j s)
    ?_ n s₀ ⟨0, by omega, lo, by omega, by simpa using dst, by simpa only [Nat.sub_zero] using count,
      zero, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro k s ⟨j, rfl, hj, h⟩
  have hw : InRegions s.wr (s.gpr .r14) 8 := by
    rw [h.wr, h.destination]; exact write j hj
  refine (VG.Proof.Argon2.X86_64.MemoryInit.clearWord_ok s hw).mono ?_
  rintro t ⟨memT, dstT, countT, zfT, otherT, rdT, wrT⟩
  have nextCount : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : VG.Proof.Argon2.X86_64.MemoryInit.ClearI s₀ p n (j + 1) t := by
    refine ⟨by omega, ?_, ?_, (otherT _ (by decide) (by decide)).trans h.zero,
      fun r h1 h2 => (otherT r h1 h2).trans (h.other r h1 h2),
      rdT.trans h.rd, wrT.trans h.wr, ?_⟩
    · rw [dstT, h.destination, BitVec.add_assoc, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 2
    · rw [countT, h.count, nextCount]
    · rw [memT, h.mem, h.destination, h.zero]; rfl
  have zf : t.zf = some (decide (n - (j + 1) = 0)) := by
    rw [zfT, h.count, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  by_cases done : j + 1 = n
  · refine .inl ⟨?_, done ▸ next⟩
    simp only [eval, zf, show n - (j + 1) = 0 by omega, decide_true,
      Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    simp only [eval, zf, show n - (j + 1) ≠ 0 by omega, decide_false,
      Option.map_some, Bool.not_false]

end VG.Proof.Argon2.X86_64.MemoryInit

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Mix`. -/
section

/-! # Argon2's modified addition on x86-64 -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Impl.Argon2.X86_64

theorem low32 (x : BitVec 64) :
    (x.setWidth 32).setWidth 64 = x &&& 0xffffffff := by
  rw [BitVec.setWidth_eq_append (by decide)]
  exact (BitVec.and_setWidth_allOnes 32 32 x).symm

theorem addMul_value (a b : BitVec 64) :
    a + b + (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 +
      (a.setWidth 32).setWidth 64 * (b.setWidth 32).setWidth 64 =
      Spec.Argon2.addMul a b := by
  rw [VG.Proof.Argon2.X86_64.low32, VG.Proof.Argon2.X86_64.low32, BitVec.add_assoc, ← BitVec.two_mul, Spec.Argon2.addMul,
    BitVec.mul_assoc]
  rfl

theorem addMul_ok {a b : Reg}
    (ha0 : a ≠ .rax) (ha2 : a ≠ .rdx) (ha6 : a ≠ .rsi)
    (hb0 : b ≠ .rax) (hb2 : b ≠ .rdx) (hb6 : b ≠ .rsi)
    (s : State) :
    WP isa (.block (addMul a b)) s fun t =>
      t.gpr a = Spec.Argon2.addMul (s.gpr a) (s.gpr b) ∧
      (∀ r, r ≠ a → r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [addMul, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.X86_64.readSrc32, VG.X86_64.readSrc, State.setReg32, execMul, execAlu,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setFlags, RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, ha0, ha2, ha6, hb0, hb2, hb6, ha0.symm,
    reduceCtorEq, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨VG.Proof.Argon2.X86_64.addMul_value _ _, ?_, trivial, trivial, trivial⟩
  intro r h1 h2 h3 h4
  simp only [h1, h2, h3, h4, ite_false]

/-- A register XOR followed by one of GB's rotations. -/
theorem xorRotate_ok {a d : Reg} (n : Nat)
    (hn : 1 ≤ n) (hn' : n ≤ 63) (s : State) :
    WP isa (.block [.alu .xor d (.reg a), .shift .ror d n]) s fun t =>
      t.gpr d = (s.gpr d ^^^ s.gpr a).rotateRight n ∧
      (∀ r, r ≠ d → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc, execAlu,
    execShift, hn, hn', and_self, ite_true, Option.bind_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setFlags,
    RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial⟩

/-- One half of GB, with all memory and non-working registers preserved. -/
theorem halfGB_ok (r1 r2 : Nat) (h1 : 1 ≤ r1) (h1' : r1 ≤ 63)
    (h2 : 1 ≤ r2) (h2' : r2 ≤ 63) (s : State) :
    let a := Spec.Argon2.addMul (s.gpr .r8) (s.gpr .r9)
    let d := (s.gpr .r11 ^^^ a).rotateRight r1
    let c := Spec.Argon2.addMul (s.gpr .r10) d
    let b := (s.gpr .r9 ^^^ c).rotateRight r2
    WP isa (.block (halfGB r1 r2)) s fun t =>
      t.gpr .r8 = a ∧ t.gpr .r9 = b ∧ t.gpr .r10 = c ∧ t.gpr .r11 = d ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  rw [halfGB, List.append_assoc, List.append_assoc]
  apply WP.block_append
  refine (VG.Proof.Argon2.X86_64.addMul_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s).mono ?_
  rintro s1 ⟨ha, hk1, hm1, hr1, hw1⟩
  apply WP.block_append
  refine (VG.Proof.Argon2.X86_64.xorRotate_ok r1 h1 h1' s1).mono ?_
  rintro s2 ⟨hd, hk2, hm2, hr2, hw2⟩
  apply WP.block_append
  refine (VG.Proof.Argon2.X86_64.addMul_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) s2).mono ?_
  rintro s3 ⟨hc, hk3, hm3, hr3, hw3⟩
  refine (VG.Proof.Argon2.X86_64.xorRotate_ok r2 h2 h2' s3).mono ?_
  rintro s4 ⟨hb, hk4, hm4, hr4, hw4⟩
  have hd' : s2.gpr .r11 =
      (s.gpr .r11 ^^^ Spec.Argon2.addMul (s.gpr .r8) (s.gpr .r9)).rotateRight r1 := by
    rw [hd, ha, hk1 .r11 (by decide) (by decide) (by decide) (by decide)]
  have hc' : s3.gpr .r10 = Spec.Argon2.addMul (s.gpr .r10) (s2.gpr .r11) := by
    rw [hc, hk2 .r10 (by decide), hk1 .r10 (by decide) (by decide) (by decide) (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, hm4.trans (hm3.trans (hm2.trans hm1)),
    hr4.trans (hr3.trans (hr2.trans hr1)), hw4.trans (hw3.trans (hw2.trans hw1))⟩
  · rw [hk4 .r8 (by decide), hk3 .r8 (by decide) (by decide) (by decide) (by decide),
      hk2 .r8 (by decide), ha]
  · rw [hb, hc', hd', hk3 .r9 (by decide) (by decide) (by decide) (by decide),
      hk2 .r9 (by decide), hk1 .r9 (by decide) (by decide) (by decide) (by decide)]
  · rw [hk4 .r10 (by decide), hc', hd']
  · rw [hk4 .r11 (by decide), hk3 .r11 (by decide) (by decide) (by decide) (by decide), hd']
  · intro r h8 h9 h10 h11 h0 hdx hsi
    rw [hk4 r h9, hk3 r h10 h0 hdx hsi, hk2 r h11, hk1 r h8 h0 hdx hsi]

/-- The complete GB operation agrees with the four-word specification. -/
theorem gb_ok (s : State) :
    let v := Proof.Argon2.mix (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
    WP isa (.block gb) s fun t =>
      t.gpr .r8 = v.1 ∧ t.gpr .r9 = v.2.1 ∧
      t.gpr .r10 = v.2.2.1 ∧ t.gpr .r11 = v.2.2.2 ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  rw [gb]
  apply WP.block_append
  refine (VG.Proof.Argon2.X86_64.halfGB_ok 32 24 (by decide) (by decide) (by decide) (by decide) s).mono ?_
  rintro t ⟨ha, hb, hc, hd, hk, hm, hr, hw⟩
  refine (VG.Proof.Argon2.X86_64.halfGB_ok 16 63 (by decide) (by decide) (by decide) (by decide) t).mono ?_
  rintro u ⟨ha', hb', hc', hd', hk', hm', hr', hw'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hm'.trans hm, hr'.trans hr, hw'.trans hw⟩
  · rw [ha', ha, hb]; rfl
  · rw [hb', ha, hb, hc, hd]; rfl
  · rw [hc', ha, hb, hc, hd]; rfl
  · rw [hd', ha, hb, hd]; rfl
  · intro r h8 h9 h10 h11 h0 hdx hsi
    exact (hk' r h8 h9 h10 h11 h0 hdx hsi).trans (hk r h8 h9 h10 h11 h0 hdx hsi)

end VG.Proof.Argon2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Memory`. -/
section

/-! # Argon2 compression working memory -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Impl.Argon2.X86_64

abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d
abbrev word (m : Mem) (p : Addr) (i : Nat) : BitVec 64 := m.readW (VG.Proof.Argon2.X86_64.off p (1024 + 8 * i)) 64

/-- Scratch permissions and its stable base register. -/
structure Scratch (s : State) (p : Addr) : Prop where
  reg : s.gpr .rcx = p
  wr : (⟨p, 4096⟩ : Region) ∈ s.wr

theorem Scratch.write {s : State} {p : Addr} (h : VG.Proof.Argon2.X86_64.Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions s.wr (VG.Proof.Argon2.X86_64.off p d) n :=
  ⟨_, h.wr, Offset.contains_base p hd (by omega)⟩

theorem Scratch.read {s : State} {p : Addr} (h : VG.Proof.Argon2.X86_64.Scratch s p) {d n : Nat}
    (hd : d + n ≤ 4096) : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off p d) n :=
  ⟨_, List.mem_append_right _ h.wr, Offset.contains_base p hd (by omega)⟩

theorem ea_at (s : State) (r : Reg) (d : Nat) :
    s.ea (VG.Impl.Argon2.X86_64.at_ r d) = VG.Proof.Argon2.X86_64.off (s.gpr r) d := by
  simp only [State.ea, VG.Impl.Argon2.X86_64.at_, BitVec.ofInt_natCast]

/-- Load the four words of GB without changing memory or any other register. -/
theorem loadGB_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .mov .r8 (.mem (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * a))),
      .mov .r9 (.mem (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * b))),
      .mov .r10 (.mem (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * c))),
      .mov .r11 (.mem (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * d)))]) s fun t =>
      t.gpr .r8 = VG.Proof.Argon2.X86_64.word s.mem p a ∧ t.gpr .r9 = VG.Proof.Argon2.X86_64.word s.mem p b ∧
      t.gpr .r10 = VG.Proof.Argon2.X86_64.word s.mem p c ∧ t.gpr .r11 = VG.Proof.Argon2.X86_64.word s.mem p d ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have la := hs.read (d := 1024 + 8 * a) (n := 8) (by omega)
  have lb := hs.read (d := 1024 + 8 * b) (n := 8) (by omega)
  have lc := hs.read (d := 1024 + 8 * c) (n := 8) (by omega)
  have ld := hs.read (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    State.load64, VG.Proof.Argon2.X86_64.ea_at, RegUpd.gpr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, hs.reg, la, lb, lc, ld, reduceCtorEq,
    ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial,
    fun r h1 h2 h3 h4 => by simp only [h1, h2, h3, h4, ite_false], trivial, trivial, trivial⟩

/-- Store the GB result in order, leaving all registers and permissions intact. -/
theorem storeGB_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (.block [
      .store (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * a)) .r8,
      .store (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * b)) .r9,
      .store (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * c)) .r10,
      .store (VG.Impl.Argon2.X86_64.at_ .rcx (1024 + 8 * d)) .r11]) s fun t =>
      t.mem = (((s.mem.writeW (VG.Proof.Argon2.X86_64.off p (1024 + 8 * a)) (s.gpr .r8)).writeW
        (VG.Proof.Argon2.X86_64.off p (1024 + 8 * b)) (s.gpr .r9)).writeW
        (VG.Proof.Argon2.X86_64.off p (1024 + 8 * c)) (s.gpr .r10)).writeW
        (VG.Proof.Argon2.X86_64.off p (1024 + 8 * d)) (s.gpr .r11) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have wa := hs.write (d := 1024 + 8 * a) (n := 8) (by omega)
  have wb := hs.write (d := 1024 + 8 * b) (n := 8) (by omega)
  have wc := hs.write (d := 1024 + 8 * c) (n := 8) (by omega)
  have wd := hs.write (d := 1024 + 8 * d) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    VG.Proof.Argon2.X86_64.ea_at, hs.reg, wa, wb, wc, wd, ite_true, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Four stores implementing one GB in scratch. -/
def storeMix (m : Mem) (p : Addr) (a b c d : Nat)
    (v : Spec.Argon2.Word × Spec.Argon2.Word × Spec.Argon2.Word × Spec.Argon2.Word) : Mem :=
  (((m.writeW (VG.Proof.Argon2.X86_64.off p (1024 + 8 * a)) v.1).writeW
    (VG.Proof.Argon2.X86_64.off p (1024 + 8 * b)) v.2.1).writeW
    (VG.Proof.Argon2.X86_64.off p (1024 + 8 * c)) v.2.2.1).writeW
    (VG.Proof.Argon2.X86_64.off p (1024 + 8 * d)) v.2.2.2

/-- The complete load/mix/store operation, independently of surrounding words. -/
theorem gbAt_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) {a b c d : Nat}
    (ha : a < 128) (hb : b < 128) (hc : c < 128) (hd : d < 128) :
    WP isa (gbAt a b c d) s fun t =>
      t.mem = VG.Proof.Argon2.X86_64.storeMix s.mem p a b c d
        (Proof.Argon2.mix (VG.Proof.Argon2.X86_64.word s.mem p a) (VG.Proof.Argon2.X86_64.word s.mem p b)
          (VG.Proof.Argon2.X86_64.word s.mem p c) (VG.Proof.Argon2.X86_64.word s.mem p d)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  rw [gbAt]
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.loadGB_ok s hs ha hb hc hd).mono ?_
  rintro s1 ⟨ha1, hb1, hc1, hd1, hk1, hm1, hr1, hw1⟩
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.gb_ok s1).mono ?_
  rintro s2 ⟨ha2, hb2, hc2, hd2, hk2, hm2, hr2, hw2⟩
  have hs2 : VG.Proof.Argon2.X86_64.Scratch s2 p := by
    refine ⟨?_, (hw2.trans hw1) ▸ hs.wr⟩
    rw [hk2 .rcx (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
      hk1 .rcx (by decide) (by decide) (by decide) (by decide), hs.reg]
  refine (VG.Proof.Argon2.X86_64.storeGB_ok s2 hs2 ha hb hc hd).mono ?_
  rintro t ⟨hm3, hk3, hr3, hw3⟩
  refine ⟨?_, ?_, hr3.trans (hr2.trans hr1), hw3.trans (hw2.trans hw1)⟩
  · rw [hm3, ha2, hb2, hc2, hd2, ha1, hb1, hc1, hd1, hm2, hm1]
    rfl
  · intro r h8 h9 h10 h11 h0 hdx hsi
    rw [hk3, hk2 r h8 h9 h10 h11 h0 hdx hsi, hk1 r h8 h9 h10 h11]

end VG.Proof.Argon2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Words`. -/
section

/-! # The scratch block as a vector of words -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

/-- The permuted half of scratch. -/
def working (m : Mem) (p : Addr) : Block := Vector.ofFn fun i => VG.Proof.Argon2.X86_64.word m p i.val

theorem working_get (m : Mem) (p : Addr) (i : Fin 128) :
    (VG.Proof.Argon2.X86_64.working m p)[i] = VG.Proof.Argon2.X86_64.word m p i.val := by
  simp only [VG.Proof.Argon2.X86_64.working, Fin.getElem_fin, Vector.getElem_ofFn]

/-- A write changes exactly the selected word of the block. -/
theorem working_write (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    VG.Proof.Argon2.X86_64.working (m.writeW (VG.Proof.Argon2.X86_64.off p (1024 + 8 * i.val)) v) p = (VG.Proof.Argon2.X86_64.working m p).set i v := by
  apply Vector.ext
  intro j hj
  simp only [VG.Proof.Argon2.X86_64.working, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : i.val = j
  · subst j
    simp only [ite_true, VG.Proof.Argon2.X86_64.word, Mem.readW_writeW_self64]
  · simp only [h, ite_false, VG.Proof.Argon2.X86_64.word]
    exact Mem.readW_writeW_sep
      (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem working_storeMix (m : Mem) (p : Addr) (a b c d : Fin 128)
    (v : Word × Word × Word × Word) :
    VG.Proof.Argon2.X86_64.working (VG.Proof.Argon2.X86_64.storeMix m p a.val b.val c.val d.val v) p =
      ((((VG.Proof.Argon2.X86_64.working m p).set a v.1).set b v.2.1).set c v.2.2.1).set d v.2.2.2 := by
  simp only [VG.Proof.Argon2.X86_64.storeMix, VG.Proof.Argon2.X86_64.working_write]

theorem storeMix_frame (m : Mem) (p : Addr) (a b c d : Fin 128)
    (v : Word × Word × Word × Word) :
    Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] m (VG.Proof.Argon2.X86_64.storeMix m p a.val b.val c.val d.val v) := by
  have inside (i : Fin 128) :
      (⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩ : Region).Contains (VG.Proof.Argon2.X86_64.off p (1024 + 8 * i.val)) 8 := by
    exact Offset.contains p (by omega) (by omega) (by omega)
  exact ((((Frame.refl [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] m).writeW (by simp) v.1 (inside a)).writeW
    (by simp) v.2.1 (inside b)).writeW (by simp) v.2.2.1 (inside c)).writeW
    (by simp) v.2.2.2 (inside d)

/-- GB updates the block vector and only the permuted half of scratch. -/
theorem gbAt_words (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) (a b c d : Fin 128) :
    WP isa (Impl.Argon2.X86_64.gbAt a.val b.val c.val d.val) s fun t =>
      VG.Proof.Argon2.X86_64.working t.mem p = Proof.Argon2.mixWords (VG.Proof.Argon2.X86_64.working s.mem p) a b c d ∧
      Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] s.mem t.mem ∧
      (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
        r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  refine (VG.Proof.Argon2.X86_64.gbAt_ok s hs a.isLt b.isLt c.isLt d.isLt).mono ?_
  rintro t ⟨hm, hk, hr, hw⟩
  refine ⟨?_, ?_, hk, hr, hw⟩
  · rw [hm, VG.Proof.Argon2.X86_64.working_storeMix]
    simp only [Proof.Argon2.mixWords, VG.Proof.Argon2.X86_64.working_get]
  · rw [hm]
    exact VG.Proof.Argon2.X86_64.storeMix_frame s.mem p a b c d _

end VG.Proof.Argon2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Initialize`. -/
section

/-! Merged from `Proof.Argon2.X86_64.Copy`. -/
section
/-! # Initial XOR and final XOR, one word at a time -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Impl.Argon2.X86_64

theorem initWord_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) (i : Fin 128)
    (hx : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rdi) (8 * i.val)) 8)
    (hy : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off (s.gpr .rsi) (8 * i.val)) 8) :
    let v := s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rdi) (8 * i.val)) 64 ^^^
      s.mem.readW (VG.Proof.Argon2.X86_64.off (s.gpr .rsi) (8 * i.val)) 64
    WP isa (.block (initWord i.val)) s fun t =>
      t.mem = (s.mem.writeW (VG.Proof.Argon2.X86_64.off p (8 * i.val)) v).writeW (VG.Proof.Argon2.X86_64.off p (1024 + 8 * i.val)) v ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  dsimp only
  have w1 := hs.write (d := 8 * i.val) (n := 8) (by omega)
  have w2 := hs.write (d := 1024 + 8 * i.val) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [initWord, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    State.load64, State.store64, execAlu, VG.Proof.Argon2.X86_64.ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hs.reg, hx, hy, w1, w2, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial⟩

theorem finishWord_ok (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) (i : Fin 128)
    (hout : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rdi) (8 * i.val)) 8) :
    WP isa (.block (finishWord i.val)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Argon2.X86_64.off (s.gpr .rdi) (8 * i.val))
        (VG.Proof.Argon2.X86_64.word s.mem p i.val ^^^ s.mem.readW (VG.Proof.Argon2.X86_64.off p (8 * i.val)) 64) ∧
      (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have r1 := hs.read (d := 8 * i.val) (n := 8) (by omega)
  have r2 := hs.read (d := 1024 + 8 * i.val) (n := 8) (by omega)
  apply WP.of_runBlock
  simp only [finishWord, runBlock_cons, runStep_some, runBlock_nil, exec, VG.X86_64.readSrc,
    State.load64, State.store64, execAlu, VG.Proof.Argon2.X86_64.ea_at,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    hs.reg, hout, r1, r2, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial⟩

end VG.Proof.Argon2.X86_64
end

/-! # Copy X XOR Y into both scratch blocks -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

theorem blockAt_get (m : Mem) (p : Addr) (i : Fin 128) :
    (blockAt m p)[i] = m.readW (VG.Proof.Argon2.X86_64.off p (8 * i.val)) 64 := by
  simp only [blockAt, Fin.getElem_fin, Vector.getElem_ofFn, Mem.readW, BitVec.setWidth_eq]

/-- Copying loops change only rax, memory, and flags. -/
def CopyKeeps (s t : State) : Prop :=
  (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr

theorem CopyKeeps.refl (s : State) : VG.Proof.Argon2.X86_64.CopyKeeps s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem CopyKeeps.trans {s t u : State} (h : VG.Proof.Argon2.X86_64.CopyKeeps s t) (h' : VG.Proof.Argon2.X86_64.CopyKeeps t u) : VG.Proof.Argon2.X86_64.CopyKeeps s u :=
  ⟨fun r hr => (h'.1 r hr).trans (h.1 r hr), h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_copy {s t : State} {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) (h : VG.Proof.Argon2.X86_64.CopyKeeps s t) :
    VG.Proof.Argon2.X86_64.Scratch t p := ⟨(h.1 .rcx (by decide)).trans hs.reg, h.2.2 ▸ hs.wr⟩

structure Inputs (s : State) (x y p : Addr) : Prop where
  xreg : s.gpr .rdi = x
  yreg : s.gpr .rsi = y
  xread : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr
  yread : (⟨y, 1024⟩ : Region) ∈ s.rd ++ s.wr
  xsep : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩
  ysep : (⟨y, 1024⟩ : Region).Disjoint ⟨p, 4096⟩

theorem Inputs.of_copy {s t : State} {x y p : Addr} (h : VG.Proof.Argon2.X86_64.Inputs s x y p) (hk : VG.Proof.Argon2.X86_64.CopyKeeps s t) :
    VG.Proof.Argon2.X86_64.Inputs t x y p := ⟨(hk.1 .rdi (by decide)).trans h.xreg,
      (hk.1 .rsi (by decide)).trans h.yreg, by simpa only [hk.2.1, hk.2.2] using h.xread,
      by simpa only [hk.2.1, hk.2.2] using h.yread, h.xsep, h.ysep⟩

theorem input_read {s : State} {x : Addr} (h : (⟨x, 1024⟩ : Region) ∈ s.rd ++ s.wr)
    (i : Fin 128) : InRegions (s.rd ++ s.wr) (VG.Proof.Argon2.X86_64.off x (8 * i.val)) 8 :=
  ⟨_, h, Offset.contains_base x (by omega) (by omega)⟩

theorem input_unchanged {m m' : Mem} {x p : Addr} (hf : Frame [⟨p, 4096⟩] m m')
    (hd : (⟨x, 1024⟩ : Region).Disjoint ⟨p, 4096⟩) (i : Fin 128) :
    m'.readW (VG.Proof.Argon2.X86_64.off x (8 * i.val)) 64 = m.readW (VG.Proof.Argon2.X86_64.off x (8 * i.val)) 64 :=
  hf.readW (r := ⟨x, 1024⟩) (Offset.contains_base x (by omega) (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- A prefix of the two scratch copies is initialized. -/
def Initialized (m : Mem) (p : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n →
    m.readW (VG.Proof.Argon2.X86_64.off p (8 * i.val)) 64 = r[i] ∧ VG.Proof.Argon2.X86_64.word m p i.val = r[i]

theorem init_store_frame (m : Mem) (p : Addr) (i : Fin 128) (v : Word) :
    Frame [⟨p, 4096⟩] m
      ((m.writeW (VG.Proof.Argon2.X86_64.off p (8 * i.val)) v).writeW (VG.Proof.Argon2.X86_64.off p (1024 + 8 * i.val)) v) :=
  ((Frame.refl [⟨p, 4096⟩] m).writeW (r := ⟨p, 4096⟩) (by simp) v (Offset.contains_base p (by omega) (by omega))).writeW (r := ⟨p, 4096⟩)
    (by simp) v (Offset.contains_base p (by omega) (by omega))

theorem initialized_step {m : Mem} {p : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : VG.Proof.Argon2.X86_64.Initialized m p r n) :
    VG.Proof.Argon2.X86_64.Initialized ((m.writeW (VG.Proof.Argon2.X86_64.off p (8 * n)) r[n]).writeW
      (VG.Proof.Argon2.X86_64.off p (1024 + 8 * n)) r[n]) p r (n + 1) := by
  intro i hi
  have lower (v : Word) :
      ((m.writeW (VG.Proof.Argon2.X86_64.off p (8 * n)) r[n]).writeW (VG.Proof.Argon2.X86_64.off p (1024 + 8 * n)) v).readW
        (VG.Proof.Argon2.X86_64.off p (8 * i.val)) 64 = (m.writeW (VG.Proof.Argon2.X86_64.off p (8 * n)) r[n]).readW
        (VG.Proof.Argon2.X86_64.off p (8 * i.val)) 64 :=
    Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)
  by_cases he : i.val = n
  · subst n
    simp only [VG.Proof.Argon2.X86_64.word, lower, Mem.readW_writeW_self64]
    exact ⟨rfl, rfl⟩
  · have hi' : i.val < n := by omega
    have sep1 : Mem.Sep (VG.Proof.Argon2.X86_64.off p (8 * i.val)) 8 (VG.Proof.Argon2.X86_64.off p (8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    have sep2 : Mem.Sep (VG.Proof.Argon2.X86_64.off p (1024 + 8 * i.val)) 8 (VG.Proof.Argon2.X86_64.off p (1024 + 8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    have sep3 : Mem.Sep (VG.Proof.Argon2.X86_64.off p (1024 + 8 * i.val)) 8 (VG.Proof.Argon2.X86_64.off p (8 * n)) 8 :=
      Offset.sep p (by omega) (by omega) (by omega)
    simp only [VG.Proof.Argon2.X86_64.word, lower, Mem.readW_writeW_sep (w := 64) (w' := 64) sep1 (by decide),
      Mem.readW_writeW_sep (w := 64) (w' := 64) sep2 (by decide), Mem.readW_writeW_sep (w := 64) (w' := 64) sep3 (by decide)]
    exact h i hi'

theorem xorBlock_get (a b : Block) (i : Fin 128) :
    (xorBlock a b)[i] = a[i] ^^^ b[i] := by
  simp only [xorBlock, Fin.getElem_fin, Vector.getElem_zipWith]

/-- Initialize an arbitrary prefix, framing both input blocks. -/
theorem init_prefix (n : Nat) (hn : n ≤ 128) (s : State) {x y p : Addr}
    (hs : VG.Proof.Argon2.X86_64.Scratch s p) (hin : VG.Proof.Argon2.X86_64.Inputs s x y p) :
    WP isa (.block ((List.range n).flatMap Impl.Argon2.X86_64.initWord)) s fun t =>
      VG.Proof.Argon2.X86_64.Initialized t.mem p (xorBlock (blockAt s.mem x) (blockAt s.mem y)) n ∧
      Frame [⟨p, 4096⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.CopyKeeps s t := by
  induction n with
  | zero =>
    exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega
    have htIn := hin.of_copy hk
    have lx : InRegions (t.rd ++ t.wr) (VG.Proof.Argon2.X86_64.off (t.gpr .rdi) (8 * n)) 8 := by
      rw [htIn.xreg]
      exact VG.Proof.Argon2.X86_64.input_read htIn.xread ⟨n, hn'⟩
    have ly : InRegions (t.rd ++ t.wr) (VG.Proof.Argon2.X86_64.off (t.gpr .rsi) (8 * n)) 8 := by
      rw [htIn.yreg]
      exact VG.Proof.Argon2.X86_64.input_read htIn.yread ⟨n, hn'⟩
    refine (VG.Proof.Argon2.X86_64.initWord_ok t (hs.of_copy hk) ⟨n, hn'⟩ lx ly).mono ?_
    rintro u ⟨hm, hreg, hr, hw⟩
    have hv : t.mem.readW (VG.Proof.Argon2.X86_64.off x (8 * n)) 64 ^^^ t.mem.readW (VG.Proof.Argon2.X86_64.off y (8 * n)) 64 =
        (xorBlock (blockAt s.mem x) (blockAt s.mem y))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [VG.Proof.Argon2.X86_64.xorBlock_get, VG.Proof.Argon2.X86_64.blockAt_get, VG.Proof.Argon2.X86_64.blockAt_get,
        VG.Proof.Argon2.X86_64.input_unchanged hf hin.xsep ⟨n, hn'⟩, VG.Proof.Argon2.X86_64.input_unchanged hf hin.ysep ⟨n, hn'⟩]
    refine ⟨?_, ?_, hk.trans ⟨hreg, hr, hw⟩⟩
    · rw [hm, htIn.xreg, htIn.yreg, hv]
      exact VG.Proof.Argon2.X86_64.initialized_step hn' ht
    · rw [hm, htIn.xreg, htIn.yreg]
      exact hf.trans (VG.Proof.Argon2.X86_64.init_store_frame t.mem p ⟨n, hn'⟩ _)

/-- The initialized copies both contain X XOR Y. -/
theorem initialized_blocks {m : Mem} {p : Addr} {r : Block} (h : VG.Proof.Argon2.X86_64.Initialized m p r 128) :
    blockAt m p = r ∧ VG.Proof.Argon2.X86_64.working m p = r := by
  constructor
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).1
    rw [← VG.Proof.Argon2.X86_64.blockAt_get m p ⟨i, hi⟩] at he
    exact he
  · apply Vector.ext
    intro i hi
    have he := (h ⟨i, hi⟩ hi).2
    rw [← VG.Proof.Argon2.X86_64.working_get m p ⟨i, hi⟩] at he
    exact he

end VG.Proof.Argon2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.ClearBlock`. -/
section

/-! Zero every word, preserving the enclosing loop's registers and memory. -/

namespace VG.Proof.Argon2.X86_64.ClearBlock

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.ClearBlock

theorem word_ok (s : State) (i : Nat)
    (hw : InRegions s.wr (VG.Proof.Argon2.X86_64.off (s.gpr .rdi) (8 * i)) 8) :
    WP isa (.block (Impl.Argon2.X86_64.ClearBlock.word i)) s fun t =>
      t.mem = s.mem.writeW (VG.Proof.Argon2.X86_64.off (s.gpr .rdi) (8 * i)) (s.gpr .rax) ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.ClearBlock.word, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.store64, VG.Proof.Argon2.X86_64.ea_at, hw, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem prefix_ok (n : Nat) (hn : n ≤ 128) (s : State) (zero : s.gpr .rax = 0)
    (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr) :
    WP isa (.block (words n)) s fun t =>
      t.mem = MemoryInit.clearMem s.mem (s.gpr .rdi) n ∧
      t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [words, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro a ⟨mem, regs, rd, wr, mx⟩
    have hw : InRegions a.wr (VG.Proof.Argon2.X86_64.off (a.gpr .rdi) (8 * n)) 8 := by
      rw [regs, wr]
      exact write _ _ ⟨⟨s.gpr .rdi, 1024⟩, by simp,
        Offset.contains_base _ (d := 8 * n) (n := 8) (k := 1024) (by omega) (by omega)⟩
    refine (VG.Proof.Argon2.X86_64.ClearBlock.word_ok a n hw).mono ?_
    rintro t ⟨mem', regs', rd', wr', mx'⟩
    refine ⟨?_, regs'.trans regs, rd'.trans rd, wr'.trans wr, mx'.trans mx⟩
    rw [mem', regs, zero, mem]
    rfl

theorem zero_ok (s : State) : WP isa (.block [.mov .rax (.imm 0)]) s fun t =>
    t.gpr .rax = 0 ∧ (∀ r, r ≠ .rax → t.gpr r = s.gpr r) ∧
    t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.mxcsr = s.mxcsr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg, ite_true]
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hr
  exact ite_eq_right hr

theorem code_ok (s : State) (write : Covers [⟨s.gpr .rdi, 1024⟩] s.wr) :
    WP isa code s fun t => blockAt t.mem (s.gpr .rdi) = zeroBlock ∧
      Frame [⟨s.gpr .rdi, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.CopyKeeps s t ∧ t.mxcsr = s.mxcsr := by
  unfold code
  refine WP.seq ((VG.Proof.Argon2.X86_64.ClearBlock.zero_ok s).mono ?_)
  rintro a ⟨zero, regs, mem, rd, wr, mx⟩
  have dest : a.gpr .rdi = s.gpr .rdi := regs .rdi (by decide)
  have write' : Covers [⟨a.gpr .rdi, 1024⟩] a.wr := by rw [dest, wr]; exact write
  refine (VG.Proof.Argon2.X86_64.ClearBlock.prefix_ok 128 (by decide) a zero write').mono ?_
  rintro t ⟨mem', regs', rd', wr', mx'⟩
  have cleared : t.mem = MemoryInit.clearMem s.mem (s.gpr .rdi) 128 := by
    rw [mem', mem, dest]
  refine ⟨?_, ?_, ⟨fun r hr => (congrFun regs' r).trans (regs r hr), rd'.trans rd, wr'.trans wr⟩,
    mx'.trans mx⟩
  · rw [cleared]
    apply Vector.ext
    intro i hi
    change (blockAt _ _)[(⟨i, hi⟩ : Fin 128)] = zeroBlock[(⟨i, hi⟩ : Fin 128)]
    rw [VG.Proof.Argon2.X86_64.blockAt_get, MemoryInit.clearMem_word _ _ 128 i (by decide) hi]
    simp only [zeroBlock, Fin.getElem_fin, Vector.getElem_replicate]
  · rw [cleared]
    exact MemoryInit.clearMem_frame _ _ 128 (by decide)

end VG.Proof.Argon2.X86_64.ClearBlock

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Finish`. -/
section

/-! # XOR the permuted block with R and write the output -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

/-- A prefix of the output block has been written. -/
def Written (m : Mem) (out : Addr) (r : Block) (n : Nat) : Prop :=
  ∀ i : Fin 128, i.val < n → m.readW (VG.Proof.Argon2.X86_64.off out (8 * i.val)) 64 = r[i]

theorem written_step {m : Mem} {out : Addr} {r : Block} {n : Nat}
    (hn : n < 128) (h : VG.Proof.Argon2.X86_64.Written m out r n) :
    VG.Proof.Argon2.X86_64.Written (m.writeW (VG.Proof.Argon2.X86_64.off out (8 * n)) r[n]) out r (n + 1) := by
  intro i hi
  by_cases he : i.val = n
  · subst n
    exact Mem.readW_writeW_self64 _ _ _
  · rw [Mem.readW_writeW_sep (Offset.sep out (by omega) (by omega) (by omega)) (by decide)]
    exact h i (by omega)

theorem scratch_unchanged {m m' : Mem} {out p : Addr} (hf : Frame [⟨out, 1024⟩] m m')
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) {d : Nat} (hd' : d + 8 ≤ 4096) :
    m'.readW (VG.Proof.Argon2.X86_64.off p d) 64 = m.readW (VG.Proof.Argon2.X86_64.off p d) 64 :=
  hf.readW (r := ⟨p, 4096⟩) (Offset.contains_base p hd' (by omega))
    (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact hd) (by decide)

/-- Finish an arbitrary prefix while preserving the complete scratch allocation. -/
theorem finish_prefix (n : Nat) (hn : n ≤ 128) (s : State) {p out : Addr}
    (hs : VG.Proof.Argon2.X86_64.Scratch s p) (ho : s.gpr .rdi = out) (hw : (⟨out, 1024⟩ : Region) ∈ s.wr)
    (hd : (⟨p, 4096⟩ : Region).Disjoint ⟨out, 1024⟩) :
    WP isa (.block ((List.range n).flatMap Impl.Argon2.X86_64.finishWord)) s fun t =>
      VG.Proof.Argon2.X86_64.Written t.mem out (xorBlock (VG.Proof.Argon2.X86_64.working s.mem p) (blockAt s.mem p)) n ∧
      Frame [⟨out, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.CopyKeeps s t := by
  induction n with
  | zero => exact WP.block_nil ⟨fun i hi => by omega, Frame.refl _ _, CopyKeeps.refl s⟩
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    apply WP.block_append
    refine (ih (by omega)).mono ?_
    rintro t ⟨ht, hf, hk⟩
    have hn' : n < 128 := by omega
    have ho' : t.gpr .rdi = out := (hk.1 .rdi (by decide)).trans ho
    have hout : InRegions t.wr (VG.Proof.Argon2.X86_64.off (t.gpr .rdi) (8 * n)) 8 := by
      rw [ho', hk.2.2]
      exact ⟨_, hw, Offset.contains_base out (by omega) (by omega)⟩
    refine (VG.Proof.Argon2.X86_64.finishWord_ok t (hs.of_copy hk) ⟨n, hn'⟩ hout).mono ?_
    rintro u ⟨hm, hreg, hr, hw'⟩
    have hv : VG.Proof.Argon2.X86_64.word t.mem p n ^^^ t.mem.readW (VG.Proof.Argon2.X86_64.off p (8 * n)) 64 =
        (xorBlock (VG.Proof.Argon2.X86_64.working s.mem p) (blockAt s.mem p))[(⟨n, hn'⟩ : Fin 128)] := by
      rw [VG.Proof.Argon2.X86_64.xorBlock_get, VG.Proof.Argon2.X86_64.working_get, VG.Proof.Argon2.X86_64.blockAt_get]
      simp only [VG.Proof.Argon2.X86_64.word, VG.Proof.Argon2.X86_64.scratch_unchanged hf hd (d := 1024 + 8 * n) (by omega),
        VG.Proof.Argon2.X86_64.scratch_unchanged hf hd (d := 8 * n) (by omega)]
    refine ⟨?_, ?_, hk.trans ⟨hreg, hr, hw'⟩⟩
    · rw [hm, ho', hv]
      exact VG.Proof.Argon2.X86_64.written_step hn' ht
    · rw [hm, ho']
      exact hf.writeW (r := ⟨out, 1024⟩) (by simp) _
        (Offset.contains_base out (by omega) (by omega))

theorem written_block {m : Mem} {out : Addr} {r : Block} (h : VG.Proof.Argon2.X86_64.Written m out r 128) :
    blockAt m out = r := by
  apply Vector.ext
  intro i hi
  have he := h ⟨i, hi⟩ hi
  rw [← VG.Proof.Argon2.X86_64.blockAt_get m out ⟨i, hi⟩] at he
  exact he

end VG.Proof.Argon2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Taint`. -/
section

/-! Merged from `Proof.Argon2.X86_64.Lit`. -/
section
/-! # Argon2 compression as a checked instruction literal -/

namespace VG.Proof.Argon2.X86_64

materialize_code compress := Impl.Argon2.X86_64.compress

end VG.Proof.Argon2.X86_64
end

/-! Merged from `Proof.Argon2.X86_64.Contract`. -/
section
/-! # A local contract for Argon2 block compression -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

def compressLocal : Contract isa where
  pre s :=
    let x : Region := ⟨s.gpr .rdi, 1024⟩
    let y : Region := ⟨s.gpr .rsi, 1024⟩
    let out : Region := ⟨s.gpr .rdx, 1024⟩
    let scratch : Region := ⟨s.gpr .rcx, 4096⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [x, y] ∧ s.wr = [out, scratch] ∧
      out.Disjoint scratch ∧ x.Disjoint scratch ∧ y.Disjoint scratch ∧
      ret.Disjoint out ∧ ret.Disjoint scratch
  post s t := blockAt t.mem (s.gpr .rdx) =
    compress (blockAt s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rsi))
  pub s t := s.gpr .rdi = t.gpr .rdi ∧ s.gpr .rsi = t.gpr .rsi ∧
    s.gpr .rdx = t.gpr .rdx ∧ s.gpr .rcx = t.gpr .rcx

def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩, ⟨0x4000, 4096⟩]

theorem compress_implies : compressLocal.Implies (compressContract X86_64.abi) := by
  sig_implies [compressContract, compressSig, VG.Proof.Argon2.X86_64.compressLocal, X86_64.abi, X86_64.argRegs]
    [satState] using VG.Proof.Argon2.X86_64.satState

end VG.Proof.Argon2.X86_64
end

/-! # Constant time of Argon2 block compression -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64

def initialTaint : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx], flags := false,
    lens := [1024, 4096], bases := [(.rdx, 0, 0), (.rcx, 1, 0)] }

theorem initial_agree {s t : State} (hs : compressLocal.pre s) (ht : compressLocal.pre t)
    (hp : compressLocal.pub s t) : X86_64.Taint.Agree VG.Proof.Argon2.X86_64.initialTaint s t := by
  obtain ⟨p1, p2, p3, p4⟩ := hp
  have wf : ∀ s, compressLocal.pre s → X86_64.Taint.Wf VG.Proof.Argon2.X86_64.initialTaint s := by
    intro s hs
    obtain ⟨_, hw, hd, _⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.Argon2.X86_64.initialTaint], by simp [hw, hd], ?_⟩, fun p hp => ?_⟩
    · simp only [hw, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl) <;> dsimp only <;> decide
    · simp only [VG.Proof.Argon2.X86_64.initialTaint, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ hs, wf _ ht,
    ?_, ?_, ?_⟩
  · simp only [VG.Proof.Argon2.X86_64.initialTaint, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · rw [hs.2.1, ht.2.1, p3, p4]
  · intro sl h; simp [VG.Proof.Argon2.X86_64.initialTaint] at h
  · intro sl h; simp [VG.Proof.Argon2.X86_64.initialTaint] at h
  · intro r h; simp [VG.Proof.Argon2.X86_64.initialTaint] at h

theorem compress_ct : ConstantTime isa compressLocal.pre compressLocal.pub
    Impl.Argon2.X86_64.compress :=
  VG.Taint.constantTime (A := taint) VG.Proof.Argon2.X86_64.initialTaint (fun _ _ hs ht hp => VG.Proof.Argon2.X86_64.initial_agree hs ht hp)
    (by taint_decide)

end VG.Proof.Argon2.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Argon2.X86_64.Compress`. -/
section

/-! Merged from `Proof.Argon2.X86_64.Round`. -/
section
/-! # The row and column permutations in scratch -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2
open VG.Proof.Argon2

/-- Registers and permissions preserved throughout a scratch permutation. -/
def Keeps (s t : State) : Prop :=
  (∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 →
    r ≠ .rax → r ≠ .rdx → r ≠ .rsi → t.gpr r = s.gpr r) ∧
  t.rd = s.rd ∧ t.wr = s.wr

theorem Keeps.refl (s : State) : VG.Proof.Argon2.X86_64.Keeps s s := ⟨fun _ _ _ _ _ _ _ _ => rfl, rfl, rfl⟩

theorem Keeps.trans {s t u : State} (h : VG.Proof.Argon2.X86_64.Keeps s t) (h' : VG.Proof.Argon2.X86_64.Keeps t u) : VG.Proof.Argon2.X86_64.Keeps s u :=
  ⟨fun r h8 h9 h10 h11 h0 hdx hsi =>
    (h'.1 r h8 h9 h10 h11 h0 hdx hsi).trans (h.1 r h8 h9 h10 h11 h0 hdx hsi),
    h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩

theorem Scratch.of_keeps {s t : State} {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p)
    (hk : VG.Proof.Argon2.X86_64.Keeps s t) : VG.Proof.Argon2.X86_64.Scratch t p :=
  ⟨(hk.1 .rcx (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans hs.reg, hk.2.2 ▸ hs.wr⟩

/-- The selected sixteen words and the unchanged words outside them. -/
def Holds (index : Fin 16 → Fin 128) (b : Block) (v : Vector Word 16)
    (m : Mem) (p : Addr) : Prop :=
  gather index (VG.Proof.Argon2.X86_64.working m p) = v ∧
  ∀ k : Fin 128, (∀ j, index j ≠ k) → (VG.Proof.Argon2.X86_64.working m p)[k] = b[k]

theorem holds_self (index : Fin 16 → Fin 128) (m : Mem) (p : Addr) :
    VG.Proof.Argon2.X86_64.Holds index (VG.Proof.Argon2.X86_64.working m p) (gather index (VG.Proof.Argon2.X86_64.working m p)) m p :=
  ⟨rfl, fun _ _ => rfl⟩

/-- One GB advances the selected row or column and preserves its complement. -/
theorem step_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) (base : Block) (v : Vector Word 16)
    (hv : VG.Proof.Argon2.X86_64.Holds index base v s.mem p) (a b c d : Fin 16)
    (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
    (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
    WP isa (Impl.Argon2.X86_64.gbAt (index a).val (index b).val (index c).val (index d).val)
      s fun t => VG.Proof.Argon2.X86_64.Holds index base (GB v a b c d) t.mem p ∧
        Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Keeps s t := by
  refine (VG.Proof.Argon2.X86_64.gbAt_words s hs (index a) (index b) (index c) (index d)).mono ?_
  rintro t ⟨hw, hf, hk⟩
  refine ⟨⟨?_, ?_⟩, hf, hk⟩
  · rw [hw, gather_mixWords index hi, hv.1, GB_eq_mixWords v hab hac had hbc hbd hcd]
  · intro k hn
    rw [hw]
    have ne (j : Fin 16) : (index j).val ≠ k.val := fun h => hn j (Fin.ext h)
    simp only [mixWords, Fin.getElem_fin, Vector.getElem_set, ne, ite_false]
    exact hv.2 k hn

/-- P on any injectively selected row or column, with a cumulative memory frame. -/
theorem permuteAt_holds (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) (base : Block) (v : Vector Word 16)
    (hv : VG.Proof.Argon2.X86_64.Holds index base v s.mem p) :
    WP isa (Impl.Argon2.X86_64.permuteAt index) s fun t =>
      VG.Proof.Argon2.X86_64.Holds index base (permute v) t.mem p ∧
      Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Keeps s t := by
  have advance (t : State) (v' : Vector Word 16)
      (h : VG.Proof.Argon2.X86_64.Holds index base v' t.mem p ∧ Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Keeps s t)
      (a b c d : Fin 16)
      (hab : a.val ≠ b.val) (hac : a.val ≠ c.val) (had : a.val ≠ d.val)
      (hbc : b.val ≠ c.val) (hbd : b.val ≠ d.val) (hcd : c.val ≠ d.val) :
      WP isa (Impl.Argon2.X86_64.gbAt (index a).val (index b).val (index c).val (index d).val)
        t fun u => VG.Proof.Argon2.X86_64.Holds index base (GB v' a b c d) u.mem p ∧
          Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] s.mem u.mem ∧ VG.Proof.Argon2.X86_64.Keeps s u := by
    refine (VG.Proof.Argon2.X86_64.step_ok index hi t (hs.of_keeps h.2.2) base v' h.1 a b c d
      hab hac had hbc hbd hcd).mono ?_
    rintro u ⟨hu, hf, hk⟩
    exact ⟨hu, h.2.1.trans hf, h.2.2.trans hk⟩
  unfold Impl.Argon2.X86_64.permuteAt
  apply WP.seq
  refine (advance s _ ⟨hv, Frame.refl _ _, Keeps.refl s⟩ 0 4 8 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s1 h1
  apply WP.seq
  refine (advance s1 _ h1 1 5 9 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s2 h2
  apply WP.seq
  refine (advance s2 _ h2 2 6 10 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s3 h3
  apply WP.seq
  refine (advance s3 _ h3 3 7 11 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s4 h4
  apply WP.seq
  refine (advance s4 _ h4 0 5 10 15
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s5 h5
  apply WP.seq
  refine (advance s5 _ h5 1 6 11 12
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s6 h6
  apply WP.seq
  refine (advance s6 _ h6 2 7 8 13
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mono ?_
  intro s7 h7
  exact advance s7 _ h7 3 4 9 14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The row/column code meets the specification's gather, P, scatter definition. -/
theorem permuteAt_ok (index : Fin 16 → Fin 128) (hi : Function.Injective index)
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) :
    WP isa (Impl.Argon2.X86_64.permuteAt index) s fun t =>
      VG.Proof.Argon2.X86_64.working t.mem p = Spec.Argon2.permuteAt index (VG.Proof.Argon2.X86_64.working s.mem p) ∧
      Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Keeps s t := by
  refine (VG.Proof.Argon2.X86_64.permuteAt_holds index hi s hs (VG.Proof.Argon2.X86_64.working s.mem p)
    (gather index (VG.Proof.Argon2.X86_64.working s.mem p)) (VG.Proof.Argon2.X86_64.holds_self index s.mem p)).mono ?_
  rintro t ⟨ht, hf, hk⟩
  exact ⟨eq_scatter index hi _ _ _ ht.1 ht.2, hf, hk⟩

/-- Compose a list of row or column permutations without re-executing any GB proof. -/
theorem rounds_ok (index : Fin 8 → Fin 16 → Fin 128)
    (hi : ∀ i, Function.Injective (index i)) (is : List (Fin 8))
    (s : State) {p : Addr} (hs : VG.Proof.Argon2.X86_64.Scratch s p) :
    WP isa (is.foldr (fun i rest => .seq (Impl.Argon2.X86_64.permuteAt (index i)) rest)
      (.block [])) s fun t =>
      VG.Proof.Argon2.X86_64.working t.mem p = is.foldl (fun b i => Spec.Argon2.permuteAt (index i) b) (VG.Proof.Argon2.X86_64.working s.mem p) ∧
      Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] s.mem t.mem ∧ VG.Proof.Argon2.X86_64.Keeps s t := by
  induction is generalizing s with
  | nil => exact WP.block_nil ⟨rfl, Frame.refl _ _, Keeps.refl s⟩
  | cons i is ih =>
    apply WP.seq
    refine (VG.Proof.Argon2.X86_64.permuteAt_ok (index i) (hi i) s hs).mono ?_
    rintro t ⟨ht, hf, hk⟩
    refine (ih t (hs.of_keeps hk)).mono ?_
    rintro u ⟨hu, hf', hk'⟩
    refine ⟨?_, hf.trans hf', hk.trans hk'⟩
    simpa only [List.foldl_cons, ht] using hu

end VG.Proof.Argon2.X86_64
end

/-! # Verified Argon2 block compression on x86-64 -/

namespace VG.Proof.Argon2.X86_64

open VG VG.X86_64 VG.Spec.Argon2

theorem CopyKeeps.callee {s t : State} (h : VG.Proof.Argon2.X86_64.CopyKeeps s t) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  apply h.1
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Keeps.callee {s t : State} (h : VG.Proof.Argon2.X86_64.Keeps s t) :
    ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact h.1 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem move_output (s : State) :
    WP isa (.block [.mov .rdi (.reg .rdx)]) s fun t =>
      t.gpr .rdi = s.gpr .rdx ∧
      (∀ r, r ≠ .rdi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, ite_true]
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial, trivial, trivial⟩

theorem original_preserved {m m' : Mem} {p : Addr}
    (hf : Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] m m') : blockAt m' p = blockAt m p := by
  apply Vector.ext
  intro i hi
  have he : m'.readW (VG.Proof.Argon2.X86_64.off p (8 * i)) 64 = m.readW (VG.Proof.Argon2.X86_64.off p (8 * i)) 64 :=
    hf.readW (r := ⟨p, 1024⟩) (Offset.contains_base p (by omega) (by omega))
      (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact Offset.base_disjoint p (by decide) (by decide)) (by decide)
  rw [← VG.Proof.Argon2.X86_64.blockAt_get m' p ⟨i, hi⟩, ← VG.Proof.Argon2.X86_64.blockAt_get m p ⟨i, hi⟩] at he
  exact he

theorem round_frame {m m' : Mem} {p out : Addr}
    (hf : Frame [⟨VG.Proof.Argon2.X86_64.off p 1024, 1024⟩] m m') : Frame [⟨out, 1024⟩, ⟨p, 4096⟩] m m' := by
  apply hf.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨p, 4096⟩, by simp, Offset.sub_base p (by decide)⟩

theorem compress_wp (s : State) (hs : compressLocal.pre s) :
    WP isa Impl.Argon2.X86_64.compress s fun t =>
      compressLocal.post s t ∧ (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
      Frame s.wr s.mem t.mem := by
  obtain ⟨hrd, hwr, hout, hx, hy, _, _⟩ := hs
  have scr : VG.Proof.Argon2.X86_64.Scratch s (s.gpr .rcx) := ⟨rfl, by simp [hwr]⟩
  have inputs : VG.Proof.Argon2.X86_64.Inputs s (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rcx) :=
    ⟨rfl, rfl, by simp [hrd], by simp [hrd], hx, hy⟩
  unfold Impl.Argon2.X86_64.compress
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.init_prefix 128 (by decide) s scr inputs).mono ?_
  rintro s1 ⟨hinit, hf1, hk1⟩
  obtain ⟨horig, hwork⟩ := VG.Proof.Argon2.X86_64.initialized_blocks hinit
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.move_output s1).mono ?_
  rintro s2 ⟨hout2, hk2, hm2, hr2, hw2⟩
  have scr2 : VG.Proof.Argon2.X86_64.Scratch s2 (s.gpr .rcx) :=
    ⟨(hk2 .rcx (by decide)).trans ((hk1.1 .rcx (by decide)).trans rfl),
      (hw2.trans hk1.2.2) ▸ scr.wr⟩
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.rounds_ok rowIndex Proof.Argon2.rowIndex_injective (List.finRange 8) s2 scr2).mono ?_
  rintro s3 ⟨hrow, hf3, hk3⟩
  apply WP.seq
  refine (VG.Proof.Argon2.X86_64.rounds_ok colIndex Proof.Argon2.colIndex_injective (List.finRange 8)
    s3 (scr2.of_keeps hk3)).mono ?_
  rintro s4 ⟨hcol, hf4, hk4⟩
  have hout4 : s4.gpr .rdi = s.gpr .rdx := by
    rw [hk4.1 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hk3.1 .rdi (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hout2, hk1.1 .rdx (by decide)]
  have hw4 : s4.wr = s.wr := hk4.2.2.trans (hk3.2.2.trans (hw2.trans hk1.2.2))
  refine (VG.Proof.Argon2.X86_64.finish_prefix 128 (by decide) s4 ((scr2.of_keeps hk3).of_keeps hk4) hout4
    (by rw [hw4, hwr]; simp) hout.symm).mono ?_
  rintro t ⟨hfinish, hf5, hk5⟩
  refine ⟨?_, ?_, ?_⟩
  · have ho4 := VG.Proof.Argon2.X86_64.original_preserved (hf3.trans hf4)
    rw [hm2, horig] at ho4
    have he := VG.Proof.Argon2.X86_64.written_block hfinish
    rw [hcol, hrow, hm2, hwork, ho4] at he
    exact he
  · intro r hr
    have ne : r ≠ .rdi := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hk5.callee r hr).trans ((hk4.callee r hr).trans ((hk3.callee r hr).trans
      ((hk2 r ne).trans (hk1.callee r hr))))
  · rw [hwr]
    have f1 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s.mem s1.mem :=
      hf1.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    have f2 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s1.mem s2.mem := by
      rw [hm2]; exact Frame.refl _ _
    have f5 : Frame [⟨s.gpr .rdx, 1024⟩, ⟨s.gpr .rcx, 4096⟩] s4.mem t.mem :=
      hf5.mono (by intro r hr; simp only [List.mem_singleton] at hr; subst r; simp)
    exact (((f1.trans f2).trans (VG.Proof.Argon2.X86_64.round_frame hf3)).trans (VG.Proof.Argon2.X86_64.round_frame hf4)).trans f5

/-- Correctness, termination, memory safety, and the System V ABI. -/
theorem compress_correct (s : State) (hs : compressLocal.pre s) :
    ∃ tr t, Exec isa Impl.Argon2.X86_64.compress s tr t ∧ abiPreserved s t ∧
      compressLocal.post s t := by
  obtain ⟨tr, t, he, hp, hk, hf⟩ := VG.Proof.Argon2.X86_64.compress_wp s hs
  refine ⟨tr, t, he, abiPreserved_of_exec (by lit_decide) he ⟨hk, ?_⟩, hp⟩
  apply hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) _ (by decide)
  intro r hr
  rw [hs.2.1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs.2.2.2.2.2.1
  · exact hs.2.2.2.2.2.2

/-- The emitted primitive is verified against the merged, target-independent contract. -/
theorem compress_verified : Verified X86_64.target Impl.Argon2.X86_64.compress
    (Spec.Argon2.compressContract X86_64.abi) :=
  Verified.of_correct VG.Proof.Argon2.X86_64.compress_correct VG.Proof.Argon2.X86_64.compress_ct VG.Proof.Argon2.X86_64.compress_implies

end VG.Proof.Argon2.X86_64

end
