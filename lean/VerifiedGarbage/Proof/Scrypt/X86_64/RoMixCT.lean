import VerifiedGarbage.Proof.Scrypt.X86_64.BlockMixCT
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Scrypt.X86_64.Lit
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import Mathlib.Tactic.DefEqTransformations
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86_64.RoMixLoops`. -/
section

/-!
# scryptROMix on x86-64: the small loops

The word copy (`copyLoop`), the word exclusive-or (`xorLoop`), the
multiplication by shifts and adds (`mulLoop`) and the computation of `2 N` by
doubling (`nLoop`).
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.MdStream.X86_64 (Upd wp_movm wp_store wp_add wp_addi wp_subi wp_cmp ofNat_pred
  ofNat_beq_zero sub_beq)
open VG.Proof.Scrypt.X86_64.BlockMix (ea_at wp_xorm)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat copy_mem xor_mem dbl_pow)

/-! ## Instructions and arithmetic -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

/-- `test d, imm`: only ZF matters here. -/
theorem wp_testi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.imm v) :: is)) s Q :=
  Proof.MdStream.X86_64.WP.cons rfl (k _ rfl rfl rfl rfl rfl)

/-- `shr d, 1`. -/
theorem wp_shr1 {d : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr d >>> 1) → s'.zf = some (s.gpr d >>> 1 == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d 1 :: is)) s Q :=
  Proof.MdStream.X86_64.WP.cons rfl
    (k _ ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩ rfl)

end

theorem ea_at0 (s : State) (b : Reg) : s.ea (at_ b 0) = s.gpr b := by
  rw [VG.Proof.Scrypt.X86_64.BlockMix.ea_at]; exact BitVec.add_zero _

theorem sx8 : (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 := by decide

theorem sx1 : (1 : BitVec 32).signExtend 64 = 1 := by decide

/-- A pointer advanced by one word. -/
theorem next_ptr (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + (8 : BitVec 32).signExtend 64 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [VG.Proof.Scrypt.X86_64.RoMix.sx8, add_ofNat, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [VG.Proof.Scrypt.X86_64.RoMix.sx1, ofNat_pred (by omega), Nat.sub_sub]

theorem dec_zf {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 == 0) = decide (k + 1 = n) := by
  rw [VG.Proof.Scrypt.X86_64.RoMix.dec_count hk, ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

theorem ofNat_zero_add (p : Addr) : p + BitVec.ofNat 64 (8 * 0) = p := by
  rw [Nat.mul_zero]; exact BitVec.add_zero _

/-! ## Counted loops -/

/-- A do-while loop over `ne` that runs its body `n > 0` times, with ZF set
exactly on the last iteration. -/
theorem count_loop {body : Prog isa} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ s'.zf = some (decide (k + 1 = n)))
    {s : State} (h0 : I 0 s) : WP isa (.loop body .ne) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hz⟩ => ?_
  by_cases hl : k + 1 = n
  · exact .inl ⟨by simp [eval, hz, hl], hl ▸ hi'⟩
  · exact .inr ⟨by simp [eval, hz, hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## `copyLoop` -/

/-- After `k` words of `copyLoop`. -/
structure CopyInv (s : State) (src dst : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → t.gpr r = s.gpr r
  rdi : t.gpr .rdi = src + BitVec.ofNat 64 (8 * k)
  rsi : t.gpr .rsi = dst + BitVec.ofNat 64 (8 * k)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - k)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem dst (bytesAt s.mem src (8 * k))

theorem copy_step {s : State} {src dst : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) {k : Nat} (hk : k < n) {t : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.CopyInv s src dst n k t) :
    WP isa (.block [.mov .rax (.mem (at_ .rdi 0)), .store (at_ .rsi 0) .rax,
      .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]) t
      fun t' => VG.Proof.Scrypt.X86_64.RoMix.CopyInv s src dst n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := src + BitVec.ofNat 64 (8 * k)) (by rw [VG.Proof.Scrypt.X86_64.RoMix.ea_at0, h.rdi])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store (a := dst + BitVec.ofNat 64 (8 * k)) (by rw [VG.Proof.Scrypt.X86_64.RoMix.ea_at0, u₁.other _ (by decide), h.rsi])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → t₂.gpr r = t.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha hdi hsi hcx => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other r hcx, u₄.other r hsi, u₃.other r hdi, g r ha, h.other r ha hdi hsi hcx]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.rdi, VG.Proof.Scrypt.X86_64.RoMix.next_ptr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.rsi, VG.Proof.Scrypt.X86_64.RoMix.next_ptr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx, VG.Proof.Scrypt.X86_64.RoMix.dec_count hk]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact copy_mem s.mem src dst k 8
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx,
      VG.Proof.Scrypt.X86_64.RoMix.dec_zf hk (by omega)]

/-- `copyLoop` copies `8 n` bytes from `rdi` to `rsi` (`rcx = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (hdi : s.gpr .rdi = src) (hsi : s.gpr .rsi = dst) (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem dst (bytesAt s.mem src (8 * n)) := by
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.count_loop hn (VG.Proof.Scrypt.X86_64.RoMix.CopyInv s src dst n)
    (fun k hk t h => VG.Proof.Scrypt.X86_64.RoMix.copy_step hlt hin hout hsep hk h) ?_) fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [VG.Proof.Scrypt.X86_64.RoMix.ofNat_zero_add, hdi], by rw [VG.Proof.Scrypt.X86_64.RoMix.ofNat_zero_add, hsi],
    by rw [hcx, Nat.sub_zero], by rw [Nat.mul_zero]; exact (VG.WriteBytes.writeBytes_nil _ _).symm⟩

/-! ## `xorLoop` -/

/-- After `k` words of `xorLoop`. -/
structure XorInv (s : State) (x y d : Addr) (n k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  other : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .rcx → t.gpr r = s.gpr r
  rdi : t.gpr .rdi = x + BitVec.ofNat 64 (8 * k)
  rsi : t.gpr .rsi = y + BitVec.ofNat 64 (8 * k)
  r8 : t.gpr .r8 = d + BitVec.ofNat 64 (8 * k)
  rcx : t.gpr .rcx = BitVec.ofNat 64 (n - k)
  mem : t.mem = VG.WriteBytes.writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * k)) (bytesAt s.mem y (8 * k)))

theorem xor_step {s : State} {x y d : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : VG.Proof.Scrypt.X86_64.RoMix.XorInv s x y d n k t) :
    WP isa (.block [.mov .rax (.mem (at_ .rdi 0)), .alu .xor .rax (.mem (at_ .rsi 0)),
      .store (at_ .r8 0) .rax, .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8),
      .alu .add .r8 (.imm 8), .alu .sub .rcx (.imm 1)]) t
      fun t' => VG.Proof.Scrypt.X86_64.RoMix.XorInv s x y d n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := x + BitVec.ofNat 64 (8 * k)) (by rw [VG.Proof.Scrypt.X86_64.RoMix.ea_at0, h.rdi])
    (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_xorm (a := y + BitVec.ofNat 64 (8 * k)) (by rw [VG.Proof.Scrypt.X86_64.RoMix.ea_at0, u₁.other _ (by decide), h.rsi])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_store (a := d + BitVec.ofNat 64 (8 * k))
    (by rw [VG.Proof.Scrypt.X86_64.RoMix.ea_at0, u₂.other _ (by decide), u₁.other _ (by decide), h.r8])
    (by rw [u₂.wr, u₁.wr, h.wr]; exact hout k hk) fun t₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_addi fun t₄ u₄ => wp_addi fun t₅ u₅ => wp_addi fun t₆ u₆ =>
    wp_subi fun t₇ u₇ z₇ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → t₃.gpr r = t.gpr r := fun r hr => by
    rw [g₃, u₂.other r hr, u₁.other r hr]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, u₁.rd, h.rd],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, u₁.wr, h.wr],
    fun r ha hdi hsi h8 hcx => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₇.other r hcx, u₆.other r h8, u₅.other r hsi, u₄.other r hdi, g r ha,
      h.other r ha hdi hsi h8 hcx]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      g _ (by decide), h.rdi, VG.Proof.Scrypt.X86_64.RoMix.next_ptr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      g _ (by decide), h.rsi, VG.Proof.Scrypt.X86_64.RoMix.next_ptr]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.r8, VG.Proof.Scrypt.X86_64.RoMix.next_ptr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, VG.Proof.Scrypt.X86_64.RoMix.dec_count hk]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact xor_mem s.mem hk hlt hdx hdy
  · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, VG.Proof.Scrypt.X86_64.RoMix.dec_zf hk (by omega)]

/-- `xorLoop` writes `[rdi] xor [rsi]` to `r8`, `8 n` bytes. -/
theorem xorLoop_ok {s : State} {x y d : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (hdi : s.gpr .rdi = x) (hsi : s.gpr .rsi = y) (hr8 : s.gpr .r8 = d)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩) :
    WP isa xorLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) := by
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.count_loop hn (VG.Proof.Scrypt.X86_64.RoMix.XorInv s x y d n)
    (fun k hk t h => VG.Proof.Scrypt.X86_64.RoMix.xor_step hlt hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ _ => rfl, by rw [VG.Proof.Scrypt.X86_64.RoMix.ofNat_zero_add, hdi], by rw [VG.Proof.Scrypt.X86_64.RoMix.ofNat_zero_add, hsi],
    by rw [VG.Proof.Scrypt.X86_64.RoMix.ofNat_zero_add, hr8], by rw [hcx, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (VG.WriteBytes.writeBytes_nil _ _).symm⟩

/-! ## `mulLoop` -/

/-- `rax = m`, and `rdx + rax * rcx` is still `a + j c`. -/
structure MulInv (s : State) (j c : Nat) (a : Addr) (m : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → t.gpr r = s.gpr r
  lt : m < 2 ^ 64
  rax : t.gpr .rax = BitVec.ofNat 64 m
  sum : t.gpr .rdx + BitVec.ofNat 64 m * t.gpr .rcx = a + BitVec.ofNat 64 (j * c)

theorem and_one_beq {m : Nat} (h : m < 2 ^ 64) :
    (BitVec.ofNat 64 m &&& (1 : BitVec 32).signExtend 64 == 0) = decide (m % 2 = 0) := by
  have e : BitVec.ofNat 64 m &&& (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (m % 2) := by
    apply BitVec.eq_of_toNat_eq
    rw [VG.Proof.Scrypt.X86_64.RoMix.sx1, BitVec.toNat_and, VG.Proof.Scrypt.Memory.toNat_ofNat_lt h, VG.Proof.Scrypt.Memory.toNat_ofNat_lt (by omega),
      show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  rw [e, ofNat_beq_zero (by omega)]

theorem shr_one {m : Nat} (h : m < 2 ^ 64) : BitVec.ofNat 64 m >>> 1 = BitVec.ofNat 64 (m / 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, VG.Proof.Scrypt.Memory.toNat_ofNat_lt h, VG.Proof.Scrypt.Memory.toNat_ofNat_lt (by omega), Nat.shiftRight_eq_div_pow,
    Nat.pow_one]

/-- The invariant across one iteration: `rdx` gains `rcx` if `m` is odd. -/
theorem mul_sum (d r : BitVec 64) (m : Nat) :
    (d + (if m % 2 = 1 then r else 0)) + BitVec.ofNat 64 (m / 2) * (r + r) =
      d + BitVec.ofNat 64 m * r := by
  have e : BitVec.ofNat 64 m = BitVec.ofNat 64 (m / 2) + BitVec.ofNat 64 (m / 2) +
      BitVec.ofNat 64 (m % 2) := by
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]; exact congrArg (BitVec.ofNat _) (by omega)
  by_cases h : m % 2 = 1
  · simp only [h, ↓reduceIte]
    rw [e, h, show BitVec.ofNat 64 1 = 1 from rfl]; grind
  · simp only [h, ↓reduceIte]
    rw [e, show m % 2 = 0 by omega, show BitVec.ofNat 64 0 = 0 from rfl]; grind

/-- The conditional add: `rdx ← rdx + rcx` if `rax` is odd. -/
theorem mul_ite {m : Nat} (hm : m < 2 ^ 64) {t : State} (hax : t.gpr .rax = BitVec.ofNat 64 m)
    (hz : t.zf = some (t.gpr .rax &&& (1 : BitVec 32).signExtend 64 == 0)) :
    WP isa (.ite .ne (.block [.alu .add .rdx (.reg .rcx)]) (.block [])) t fun t' =>
      VG.Proof.MdStream.X86_64.Upd t t' .rdx (t.gpr .rdx + if m % 2 = 1 then t.gpr .rcx else 0) := by
  refine WP.ite (!decide (m % 2 = 0)) (by simp only [eval, hz, hax, VG.Proof.Scrypt.X86_64.RoMix.and_one_beq hm, Option.map_some])
    (fun hb => wp_add fun t₁ u₁ => WP.block_nil ?_) (fun hb => WP.block_nil ?_)
  · have : m % 2 = 1 := by simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hb; omega
    simp only [this, ↓reduceIte]; exact u₁
  · have : ¬ m % 2 = 1 := by simp only [Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at hb; omega
    simp only [this, ↓reduceIte]
    rw [show t.gpr .rdx + 0 = t.gpr .rdx from BitVec.add_zero _]
    exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem mul_step {s : State} {j c : Nat} {a : Addr} {m : Nat} {t : State} (h : VG.Proof.Scrypt.X86_64.RoMix.MulInv s j c a m t) :
    WP isa (.seq (.block [.alu .test .rax (.imm 1)]) <|
      .seq (.ite .ne (.block [.alu .add .rdx (.reg .rcx)]) (.block []))
        (.block [.alu .add .rcx (.reg .rcx), .shift .shr .rax 1])) t
      fun t' => VG.Proof.Scrypt.X86_64.RoMix.MulInv s j c a (m / 2) t' ∧ t'.zf = some (decide (m / 2 = 0)) := by
  refine WP.seq (VG.Proof.Scrypt.X86_64.RoMix.wp_testi fun t₁ g₁ m₁ rd₁ wr₁ z₁ => WP.block_nil ?_)
  have ax₁ : t₁.gpr .rax = BitVec.ofNat 64 m := by rw [g₁, h.rax]
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.mul_ite h.lt ax₁ (by rw [z₁, g₁])) fun t₂ u₂ => ?_)
  refine wp_add fun t₃ u₃ => VG.Proof.Scrypt.X86_64.RoMix.wp_shr1 fun t₄ u₄ z₄ => WP.block_nil ?_
  have ax₃ : t₃.gpr .rax = BitVec.ofNat 64 m := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), ax₁]
  refine ⟨⟨by rw [u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd], by rw [u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr],
    by rw [u₄.mem, u₃.mem, u₂.mem, m₁, h.mem], fun r ha hd hc => ?_, by have := h.lt; omega, ?_, ?_⟩, ?_⟩
  · rw [u₄.other r ha, u₃.other r hc, u₂.other r hd, g₁, h.other r ha hd hc]
  · rw [u₄.gpr, ax₃, VG.Proof.Scrypt.X86_64.RoMix.shr_one h.lt]
  · rw [u₄.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr,
      u₂.other _ (by decide), g₁, VG.Proof.Scrypt.X86_64.RoMix.mul_sum, h.sum]
  · rw [z₄, ax₃, VG.Proof.Scrypt.X86_64.RoMix.shr_one h.lt, ofNat_beq_zero (by have := h.lt; omega)]

/-- `mulLoop` adds `rax * rcx` to `rdx` (modulo 2^64), for any `rax`. -/
theorem mulLoop_ok {s : State} {j c : Nat} {a : Addr} (hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = a) (hcx : s.gpr .rcx = BitVec.ofNat 64 c) :
    WP isa mulLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.gpr .rdx = a + BitVec.ofNat 64 (j * c) := by
  refine WP.loop (M := isa) (VG.Proof.Scrypt.X86_64.RoMix.MulInv s j c a) ?_ j s
    ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, hj, hax, by rw [hdx, hcx, BitVec.ofNat_mul]⟩
  intro m t h
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.mul_step h) fun t' ⟨h', hz⟩ => ?_
  by_cases hl : m / 2 = 0
  · refine .inl ⟨by simp [eval, hz, hl], h'.rd, h'.wr, h'.mem, h'.other, ?_⟩
    have := h'.sum
    rwa [hl, BitVec.zero_mul, BitVec.add_zero] at this
  · exact .inr ⟨by simp [eval, hz, hl], m / 2, by omega, h'⟩

/-! ## `nLoop` -/

/-- After `k` doublings. -/
structure NInv (s : State) (r : Nat) (k : Nat) (t : State) : Prop where
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mem : t.mem = s.mem
  other : ∀ r', r' ≠ .rax → r' ≠ .rdx → t.gpr r' = s.gpr r'
  rax : t.gpr .rax = BitVec.ofNat 64 (r * 2 ^ k)
  rdx : t.gpr .rdx = BitVec.ofNat 64 (2 ^ k)

theorem n_step {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (r * 2 ^ (e + 1))) {k : Nat} (hk : k < e + 1) {t : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.NInv s r k t) :
    WP isa (.block [.alu .add .rax (.reg .rax), .alu .add .rdx (.reg .rdx),
      .alu .cmp .rax (.reg .rcx)]) t
      fun t' => VG.Proof.Scrypt.X86_64.RoMix.NInv s r (k + 1) t' ∧ t'.zf = some (decide (k + 1 = e + 1)) := by
  refine wp_add fun t₁ u₁ => wp_add fun t₂ u₂ => wp_cmp fun t₃ g₃ m₃ rd₃ wr₃ _ z₃ => WP.block_nil ?_
  have ax : t₂.gpr .rax = BitVec.ofNat 64 (r * 2 ^ (k + 1)) := by
    rw [u₂.other _ (by decide), u₁.gpr, h.rax, dbl_pow]
  have le : r * 2 ^ (k + 1) ≤ r * 2 ^ (e + 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
  refine ⟨⟨by rw [rd₃, u₂.rd, u₁.rd, h.rd], by rw [wr₃, u₂.wr, u₁.wr, h.wr],
    by rw [m₃, u₂.mem, u₁.mem, h.mem], fun r' ha hd => ?_, by rw [g₃, ax], ?_⟩, ?_⟩
  · rw [g₃, u₂.other r' hd, u₁.other r' ha, h.other r' ha hd]
  · rw [g₃, u₂.gpr, u₁.other _ (by decide), h.rdx, ← Nat.one_mul (2 ^ k), dbl_pow, Nat.one_mul]
  · rw [z₃, ax, u₂.other _ (by decide), u₁.other _ (by decide), h.other _ (by decide) (by decide),
      hcx, sub_beq (by omega) hlt]
    refine congrArg some (decide_eq_decide.mpr ⟨fun hh => ?_, fun hh => by rw [hh]⟩)
    exact (Nat.pow_right_inj (by decide)).mp (Nat.eq_of_mul_eq_mul_left hr hh)

/-- `nLoop` doubles `rax` (from `r`) and `rdx` (from 1) until `rax = rcx = r * 2^(e+1)`. -/
theorem nLoop_ok {s : State} {r e : Nat} (hr : 0 < r) (hlt : r * 2 ^ (e + 1) < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 r) (hdx : s.gpr .rdx = 1)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (r * 2 ^ (e + 1))) :
    WP isa nLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r', r' ≠ .rax → r' ≠ .rdx → s'.gpr r' = s.gpr r') ∧
      s'.gpr .rdx = BitVec.ofNat 64 (2 ^ (e + 1)) := by
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.count_loop (Nat.succ_pos e) (VG.Proof.Scrypt.X86_64.RoMix.NInv s r)
    (fun k hk t h => VG.Proof.Scrypt.X86_64.RoMix.n_step hr hlt hcx hk h) ?_) fun t h => ⟨h.rd, h.wr, h.mem, h.other, h.rdx⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [hax, Nat.pow_zero, Nat.mul_one], by rw [hdx]; rfl⟩

end VG.Proof.Scrypt.X86_64.RoMix

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86_64.RoMixCT`. -/
section

/-!
# scryptROMix on x86-64: the precondition and the calls

The regions the function works on, and `BlockMixSpec`: what a call of the
verified `vg_scrypt_blockmix` does, from its `Verified` proof by `WP.call`.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

namespace Stream
export VG.Proof.MdStream.X86_64 (Upd)
end Stream

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.X86_64 (callEntry_byte)

/-! ## What a call of `vg_scrypt_blockmix` does -/

/-- A call of `c` writes scryptBlockMix of the `128 r` bytes at `rdi` to
`rdx`, with the 128 bytes at `r8` as working space. -/
def BlockMixSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (src dst scr : Addr) (r : Nat), s.gpr .rdi = src → s.gpr .rsi = BitVec.ofNat 64 r →
    s.gpr .rdx = dst → s.gpr .rcx = BitVec.ofNat 64 r → s.gpr .r8 = scr → 0 < r →
    128 * r < 2 ^ 64 →
    Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩ → Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩ →
    Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨src, 128 * r⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨dst, 128 * r⟩ →
    (below (s.gpr .rsp) 16).Disjoint ⟨scr, 128⟩ →
    src.toNat + 128 * r ≤ 2 ^ 64 → dst.toNat + 128 * r ≤ 2 ^ 64 → scr.toNat + 128 ≤ 2 ^ 64 →
    InRegions (s.rd ++ s.wr) src (128 * r) → InRegions s.wr dst (128 * r) →
    InRegions s.wr scr 128 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr →
        (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨dst, 128 * r⟩, ⟨scr, 128⟩, below (s.gpr .rsp) 16] s.mem s'.mem →
        bytesAt s'.mem dst (128 * r) = blockMix r (bytesAt s.mem src (128 * r)) → Q s') →
    WP isa (.call "vg_scrypt_blockmix" c) s Q

theorem blockMix_depth : Impl.Scrypt.X86_64.blockMix.depth = 1 := by decide +kernel

theorem blockMix_nosp : NoSp Impl.Scrypt.X86_64.blockMix := by
  have : ((instrs Impl.Scrypt.X86_64.blockMix).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; decide +kernel
  intro i hi
  simpa using List.all_eq_true.mp this i hi

/-- The 8 bytes below the stack pointer after a call are within the 16 below it before. -/
theorem below8_sub (sp : Addr) : Region.Sub (below (sp - 8) 8) (below sp 16) :=
  below_callee sp 8

/-- The return address slot of a call from `sp`. -/
theorem ret8_sub (sp : Addr) : Region.Sub ⟨sp - 8, 8⟩ (below sp 16) := by
  intro a h
  simp only [Region.Contains] at h ⊢
  have e : a - (sp - BitVec.ofNat 64 16) = (a - (sp - 8)) + 8 := by bv_omega
  rw [e, BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
  have := Nat.mod_le ((a - (sp - 8)).toNat + 8) (2 ^ 64)
  omega

/-- What a call of `vg_scrypt_blockmix` needs: its contract's precondition,
once the return address is stored and its permissions are narrowed. -/
theorem bm_pre {s : State} {src dst scr : Addr} {r : Nat} (hdi : s.gpr .rdi = src)
    (hsi : s.gpr .rsi = BitVec.ofNat 64 r) (hdx : s.gpr .rdx = dst) (hcx : s.gpr .rcx = BitVec.ofNat 64 r)
    (hr8 : s.gpr .r8 = scr) (hr : 0 < r) (hlt : 128 * r < 2 ^ 64)
    (hds : Region.Disjoint ⟨dst, 128 * r⟩ ⟨scr, 128⟩) (hsd : Region.Disjoint ⟨src, 128 * r⟩ ⟨dst, 128 * r⟩)
    (hss : Region.Disjoint ⟨src, 128 * r⟩ ⟨scr, 128⟩)
    (bsrc : (below (s.gpr .rsp) 16).Disjoint ⟨src, 128 * r⟩)
    (bdst : (below (s.gpr .rsp) 16).Disjoint ⟨dst, 128 * r⟩)
    (bscr : (below (s.gpr .rsp) 16).Disjoint ⟨scr, 128⟩)
    (nsrc : src.toNat + 128 * r ≤ 2 ^ 64) (ndst : dst.toNat + 128 * r ≤ 2 ^ 64)
    (nscr : scr.toNat + 128 ≤ 2 ^ 64)
    (isrc : InRegions (s.rd ++ s.wr) src (128 * r)) (idst : InRegions s.wr dst (128 * r))
    (iscr : InRegions s.wr scr 128) :
    Proof.Scrypt.blockMixX86_64.pre
      (s.callEntry.withRegions [⟨src, 128 * r⟩] [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) ∧
    Covers ([⟨src, 128 * r⟩] ++ [⟨dst, 128 * r⟩, ⟨scr, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨dst, 128 * r⟩, ⟨scr, 128⟩] s.wr := by
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have tr : (BitVec.ofNat 64 r).toNat = r := Memory.toNat_ofNat_lt (by omega)
  have c128 : r * 128 = 128 * r := Nat.mul_comm _ _
  have cw := Covers.pair (Covers.one idst) (Covers.one iscr)
  refine ⟨?_, ?_, cw⟩
  · simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), hne _ (by decide : Reg.r8 ≠ .rsp), hdi, hsi, hdx, hcx,
      hr8, tr, c128]
    refine ⟨trivial, trivial, hds, hsd, hss, ?_, ?_, ?_, ?_, ?_, nsrc, ndst, nscr, trivial, hr⟩
    · exact bdst.sub_left (VG.Proof.Scrypt.X86_64.RoMix.ret8_sub _)
    · exact bscr.sub_left (VG.Proof.Scrypt.X86_64.RoMix.ret8_sub _)
    · exact bsrc.sub_left (VG.Proof.Scrypt.X86_64.RoMix.below8_sub _)
    · exact bdst.sub_left (VG.Proof.Scrypt.X86_64.RoMix.below8_sub _)
    · exact bscr.sub_left (VG.Proof.Scrypt.X86_64.RoMix.below8_sub _)
  · have h1 := Covers.one isrc
    intro a n h
    simp only [List.cons_append, List.nil_append] at h
    obtain ⟨R, hR, hc⟩ := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with rfl | rfl | rfl
    · exact h1 a n ⟨_, List.mem_singleton_self _, hc⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩
    · obtain ⟨R', hR', hc'⟩ := cw a n ⟨_, by simp, hc⟩
      exact ⟨R', List.mem_append_right _ hR', hc'⟩

theorem blockMixSpec : VG.Proof.Scrypt.X86_64.RoMix.BlockMixSpec Impl.Scrypt.X86_64.blockMix := by
  intro s src dst scr r hdi hsi hdx hcx hr8 hr hlt hds hsd hss bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr Q hQ
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  have tr : (BitVec.ofNat 64 r).toNat = r := Memory.toNat_ofNat_lt (by omega)
  obtain ⟨p, c₁, c₂⟩ := VG.Proof.Scrypt.X86_64.RoMix.bm_pre hdi hsi hdx hcx hr8 hr hlt hds hsd hss bsrc bdst bscr nsrc ndst nscr
    isrc idst iscr
  refine WP.call (k := Proof.Scrypt.blockMixX86_64) BlockMix.blockMix_correct VG.Proof.Scrypt.X86_64.RoMix.blockMix_nosp
    (by rw [VG.Proof.Scrypt.X86_64.RoMix.blockMix_depth]; decide) p c₁ c₂ ?_
  intro s₂ hrd hwr hcs hf _ ⟨s₃, hm₃, _, hpost⟩
  simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), hdi, hsi, hdx, hm₃, tr] at hpost
  rw [VG.Proof.Scrypt.X86_64.RoMix.blockMix_depth] at hf
  refine hQ s₂ hrd hwr hcs (by simpa using hf) ?_
  rw [hpost]
  congr 1
  exact Memory.bytesAt_congr fun i hi =>
    callEntry_byte s (R := ⟨src, 128 * r⟩) (bsrc.sub_left (below_sub (by omega) (by omega)))
      (by show 128 * r ≤ 2 ^ 64; omega) hi

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : Addr := s₀.gpr .rdi
abbrev rr : Nat := (s₀.gpr .rsi).toNat
abbrev vP : Addr := s₀.gpr .rdx
abbrev vl : Nat := (s₀.gpr .rcx).toNat
abbrev sc : Addr := s₀.gpr .r8
/-- `N`. -/
abbrev NN : Nat := VG.Proof.Scrypt.X86_64.RoMix.vl s₀ / VG.Proof.Scrypt.X86_64.RoMix.rr s₀
abbrev bR : Region := ⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * 128⟩
abbrev vR : Region := ⟨VG.Proof.Scrypt.X86_64.RoMix.vP s₀, VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128⟩
abbrev scR : Region := ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, (VG.Proof.Scrypt.X86_64.RoMix.rr s₀ + 2) * 128⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
/-- `(V[i]'(by omega))`. -/
abbrev vAt (i : Nat) : Addr := VG.Proof.Scrypt.X86_64.RoMix.vP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i)
/-- `T`. -/
abbrev tP : Addr := VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 192

/-- The caller's callee-saved registers are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) s₀.gpr rmSaved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀]
  b_v : (VG.Proof.Scrypt.X86_64.RoMix.bR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.vR s₀)
  b_s : (VG.Proof.Scrypt.X86_64.RoMix.bR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.scR s₀)
  v_s : (VG.Proof.Scrypt.X86_64.RoMix.vR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.scR s₀)
  ret_b : (VG.Proof.Scrypt.X86_64.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.bR s₀)
  ret_v : (VG.Proof.Scrypt.X86_64.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.vR s₀)
  ret_s : (VG.Proof.Scrypt.X86_64.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.scR s₀)
  stk_b : (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.bR s₀)
  stk_v : (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.vR s₀)
  stk_s : (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.scR s₀)
  b_nw : (VG.Proof.Scrypt.X86_64.RoMix.bP s₀).toNat + VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * 128 ≤ 2 ^ 64
  v_nw : (VG.Proof.Scrypt.X86_64.RoMix.vP s₀).toNat + VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128 ≤ 2 ^ 64
  s_nw : (VG.Proof.Scrypt.X86_64.RoMix.sc s₀).toNat + (VG.Proof.Scrypt.X86_64.RoMix.rr s₀ + 2) * 128 ≤ 2 ^ 64
  pos : 0 < VG.Proof.Scrypt.X86_64.RoMix.rr s₀
  vl_eq : VG.Proof.Scrypt.X86_64.RoMix.vl s₀ = VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀
  pow : (VG.Proof.Scrypt.X86_64.RoMix.NN s₀).isPowerOfTwo
  r9 : (s₀.gpr .r9).toNat = VG.Proof.Scrypt.X86_64.RoMix.rr s₀ + 2

theorem pre_of {s₀ : State} (h : Proof.Scrypt.roMixX86_64.pre s₀) : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  simp only [h18] at h2 h4 h5 h8 h11 h14
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, ?_, h17, h18⟩
  exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h16)).symm

theorem ret_stk (s₀ : State) : (VG.Proof.Scrypt.X86_64.RoMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀)
include hp

theorem NN_pos : 0 < VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by
  obtain ⟨e, he⟩ := hp.pow
  rw [he]; exact Nat.two_pow_pos _

/-- `v` is not the whole address space, since `scratch` is not in it. -/
theorem v_lt : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ < 2 ^ 64 := by
  have e : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ = VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128 := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  rw [e]
  by_contra hc
  refine hp.v_s (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) ?_ (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
  simp only [Region.Contains]
  have := (VG.Proof.Scrypt.X86_64.RoMix.sc s₀ - VG.Proof.Scrypt.X86_64.RoMix.vP s₀).isLt
  omega

theorem r_lt : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ < 2 ^ 64 := by
  have := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have := VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp
  have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- `(V[i]'(by omega))` is in `v`. -/
theorem vAt_sub {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) : Region.Sub ⟨VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86_64.RoMix.vR s₀) := by
  have := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have e : VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128 = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  show Region.Sub ⟨VG.Proof.Scrypt.X86_64.RoMix.vP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i), 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.vP s₀, VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128⟩
  exact Memory.sub_off (by rw [e]; omega) (by omega)

theorem vAt_disj {i k : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (hk : k < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (hik : i ≠ k) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ := by
  have := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have hle : ∀ j, j < VG.Proof.Scrypt.X86_64.RoMix.NN s₀ → 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * j + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := fun j hj => by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
  have h1 := hle i hi
  have h2 := hle k hk
  have hpos := hp.pos
  refine Memory.disj_off _ ?_ (by omega) (by omega) (by omega) (by omega)
  rcases Nat.lt_or_gt_of_ne hik with h | h
  · left
    have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * k := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    exact this
  · right
    have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * k + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    exact this

/-- `T` is in `scratch`. -/
theorem t_sub : Region.Sub ⟨VG.Proof.Scrypt.X86_64.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86_64.RoMix.scR s₀) := by
  have := hp.s_nw
  exact Memory.sub_off (by omega) (by omega)

omit hp in
/-- The block-mix working space is in `scratch`. -/
theorem w_sub : Region.Sub ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩ (VG.Proof.Scrypt.X86_64.RoMix.scR s₀) := Region.sub_prefix (by omega)

theorem t_w : Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩ := by
  have := hp.s_nw
  have := hp.pos
  have := Memory.disj_off (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) (o₁ := 192) (n₁ := 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    (VG.Proof.Scrypt.X86_64.RoMix.scR s₀).Contains (VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 o) n :=
  Memory.contains_off (by omega) (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 256) :
    Region.Sub ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.X86_64.RoMix.scR s₀) :=
  Memory.sub_off (by omega) (by omega)

/-! ## What stays in `scratch`: the caller's registers and `N` -/

/-- Bytes `[128, 184)` of `scratch`. -/
abbrev keepR (s₀ : State) : Region := ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 128, 56⟩

def Kept (s₀ : State) (m : Mem) : Prop :=
  VG.Proof.Scrypt.X86_64.RoMix.Saved s₀ m ∧ m.readW (VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 176) 64 = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀)

theorem word_sub (s₀ : State) {d : Nat} (h₁ : 128 ≤ d) (h₂ : d + 8 ≤ 184) :
    Region.Sub ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 d, 8⟩ (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀) := by
  rw [show d = 128 + (d - 128) by omega, ← Memory.add_ofNat]
  exact Memory.sub_off (by omega) (by omega)

theorem saved_offs {p : Reg × Nat} (hp : p ∈ rmSaved) : 128 ≤ p.2 ∧ p.2 + 8 ≤ 176 :=
  (show ∀ p ∈ rmSaved, 128 ≤ p.2 ∧ p.2 + 8 ≤ 176 by decide) p hp

theorem Kept.frame {s₀ : State} {m m' : Mem} {rs : List Region} (h : VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀).Disjoint r) : VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ m' := by
  refine ⟨fun p hp => ?_, ?_⟩
  · have ho := VG.Proof.Scrypt.X86_64.RoMix.saved_offs hp
    rw [← h.1 p hp]
    exact hf.readW (r := ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 p.2, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Scrypt.X86_64.RoMix.word_sub s₀ ho.1 (by omega))) (by decide)
  · rw [← h.2]
    exact hf.readW (r := ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 176, 8⟩) (Region.contains_self _ _)
      (fun r hr => (hd r hr).sub_left (VG.Proof.Scrypt.X86_64.RoMix.word_sub s₀ (by omega) (by omega))) (by decide)

theorem keep_sub (s₀ : State) : Region.Sub (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀) (VG.Proof.Scrypt.X86_64.RoMix.scR s₀) := VG.Proof.Scrypt.X86_64.RoMix.s_sub s₀ (by omega)

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀)
include hp

theorem keep_b : (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.bR s₀) := hp.b_s.symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.keep_sub s₀)
theorem keep_v : (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.vR s₀) := hp.v_s.symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.keep_sub s₀)
theorem keep_stk : (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀).Disjoint (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀) := hp.stk_s.symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.keep_sub s₀)

omit hp in
theorem keep_w : (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀).Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩ := by
  have := Memory.disj_off (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 0) (n₂ := 128) (by omega)
    (by omega) (by omega) (by omega) (by omega)
  simpa using this

theorem keep_t : (VG.Proof.Scrypt.X86_64.RoMix.keepR s₀).Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ := by
  have := hp.s_nw
  have := hp.pos
  exact Memory.disj_off (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) (o₁ := 128) (n₁ := 56) (o₂ := 192) (n₂ := 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (by omega)
    (by omega) (by omega) (by omega) (by omega)

omit hp in
theorem b_sub' : Region.Sub ⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86_64.RoMix.bR s₀) := by
  rw [Nat.mul_comm]; exact fun _ h => h

end

/-! ## Instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_shr {d : Reg} {n : Nat} (h₁ : 1 ≤ n) (h₂ : n ≤ 63)
    (k : ∀ s', Stream.Upd s s' d (s.gpr d >>> n) → s'.zf = some ((s.gpr d >>> n) == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine Proof.MdStream.X86_64.WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_ rfl)
  · simp [exec, execShift, h₁, h₂]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl,
      rfl⟩

theorem wp_and {d r : Reg}
    (k : ∀ s', Stream.Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  Proof.MdStream.X86_64.WP.cons rfl (k _ (VG.Proof.MdStream.X86_64.Upd.flags _ _ _ _ _ _))

end

theorem shr_ofNat {a : Nat} (n : Nat) (h : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> n = BitVec.ofNat 64 (a / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Memory.toNat_ofNat_lt h, Memory.toNat_ofNat_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow]

end VG.Proof.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: correctness

The prologue saves our caller's registers in `scratch` and computes `N`; step
2 and step 3 are loops whose bodies call `vg_scrypt_blockmix` (through
`BlockMixSpec`); the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix roMix)
open VG.Proof.MdStream.X86_64 (wp_mov wp_movm wp_store wp_add wp_addi wp_subi wp_mov32i)
open VG.Proof.Sha256.Stream (writeBytes)

theorem frame_bytesAt' {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  Memory.frame_bytesAt hf hd hn

/-! ## The prologue -/

/-- The memory after the prologue's stores. -/
abbrev saveMem (s₀ : State) : Mem := Spill.saveMem s₀.mem (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) s₀.gpr rmSaved

theorem saveMem_saved (s₀ : State) : VG.Proof.Scrypt.X86_64.RoMix.Saved s₀ (VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀) :=
  Spill.saveMem_saved _ _ _ _ (by decide)

theorem saveMem_frame (s₀ : State) : Frame [VG.Proof.Scrypt.X86_64.RoMix.scR s₀] s₀.mem (VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀) :=
  Spill.saveMem_frame _ _ _ _ fun _ hp => VG.Proof.Scrypt.X86_64.RoMix.in_s s₀ (by have := VG.Proof.Scrypt.X86_64.RoMix.saved_offs hp; omega)

theorem prologue_eq : rmPrologue =
    ([.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp, .store (at_ .r8 144) .r12,
     .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15, .store (at_ .r8 168) .r13] : List Instr) ++
    ([.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8), .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)] : List Instr) := rfl

theorem save_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, s₁.gpr = s₀.gpr → s₁.rd = s₀.rd → s₁.wr = s₀.wr → s₁.mem = VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀ →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (([.store (at_ .r8 128) .rbx, .store (at_ .r8 136) .rbp,
      .store (at_ .r8 144) .r12, .store (at_ .r8 152) .r14, .store (at_ .r8 160) .r15,
      .store (at_ .r8 168) .r13] : List Instr) ++ rest)) s₀ Q := by
  refine Spill.save_then .r8 rmSaved (fun p hp' => ?_) (k _ rfl rfl rfl rfl)
  have := VG.Proof.Scrypt.X86_64.RoMix.saved_offs hp'
  rw [hp.wr]; exact Memory.InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86_64.RoMix.in_s s₀ (by omega))

/-- After the prologue. -/
structure P1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀
  r12 : s.gpr .r12 = VG.Proof.Scrypt.X86_64.RoMix.vP s₀
  r13 : s.gpr .r13 = VG.Proof.Scrypt.X86_64.RoMix.sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  rax : s.gpr .rax = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  rdx : s.gpr .rdx = 1
  rcx : s.gpr .rcx = BitVec.ofNat 64 (2 * VG.Proof.Scrypt.X86_64.RoMix.vl s₀)

set_option linter.unusedSimpArgs false in
theorem setup_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s₁ : State} (g : s₁.gpr = s₀.gpr) (hrd : s₁.rd = s₀.rd)
    (hwr : s₁.wr = s₀.wr) (hm : s₁.mem = VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .r8),
     .mov .r14 (.reg .rsi),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14), .alu .add .r14 (.reg .r14),
     .alu .add .r14 (.reg .r14),
     .mov .rax (.reg .rsi), .mov32 .rdx (.imm 1), .alu .add .rcx (.reg .rcx)]) s₁ (VG.Proof.Scrypt.X86_64.RoMix.P1 s₀) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun c uc _ _ => wp_mov fun d ud _ _ =>
    wp_add fun e1 u1 => wp_add fun e2 u2 => wp_add fun e3 u3 => wp_add fun e4 u4 =>
    wp_add fun e5 u5 => wp_add fun e6 u6 => wp_add fun e7 u7 => wp_mov fun f uf _ _ =>
    wp_mov32i fun h uh _ _ => wp_add fun i ui => WP.block_nil ?_
  have x0 : d.gpr .r14 = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
    rw [ud.gpr, uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have x1 := u1.gpr.trans (BlockMix.dbl x0)
  have x2 := u2.gpr.trans (BlockMix.dbl x1)
  have x3 := u3.gpr.trans (BlockMix.dbl x2)
  have x4 := u4.gpr.trans (BlockMix.dbl x3)
  have x5 := u5.gpr.trans (BlockMix.dbl x4)
  have x6 := u6.gpr.trans (BlockMix.dbl x5)
  have x7 : e7.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
    rw [u7.gpr.trans (BlockMix.dbl x6)]; exact congrArg (BitVec.ofNat _) (by omega)
  have xc : h.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.vl s₀) := by
    simp (disch := decide) only [uh.other, uf.other, u7.other, u6.other, u5.other, u4.other,
      u3.other, u2.other, u1.other, ud.other, uc.other, ub.other, ua.other, g,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ui.rd, uh.rd, uf.rd, u7.rd, u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, ud.rd,
      uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uh.wr, uf.wr, u7.wr, u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, ud.wr,
      uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.mem, uh.mem, uf.mem, u7.mem, u6.mem, u5.mem, u4.mem, u3.mem, u2.mem,
      u1.mem, ud.mem, uc.mem, ub.mem, ua.mem, hm]
  all_goals simp (disch := decide) only [ua.gpr, ua.other, ub.gpr, ub.other, uc.gpr, uc.other,
    ud.other, u1.other, u2.other, u3.other, u4.other, u5.other, u6.other, u7.other, x7,
    uf.gpr, uf.other, uh.gpr, uh.other, ui.gpr, ui.other, g, xc, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]
  all_goals first | rfl | decide |
    exact BlockMix.dbl (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])

theorem prologue_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) : WP isa (.block rmPrologue) s₀ (VG.Proof.Scrypt.X86_64.RoMix.P1 s₀) := by
  rw [VG.Proof.Scrypt.X86_64.RoMix.prologue_eq]
  exact VG.Proof.Scrypt.X86_64.RoMix.save_ok hp fun _ g hrd hwr hm => VG.Proof.Scrypt.X86_64.RoMix.setup_ok hp g hrd hwr hm

/-! ## Computing `N` -/

/-- After `i` iterations of step 2. -/
structure Inv2 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ VG.Proof.Scrypt.X86_64.RoMix.NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀
  rbp : s.gpr .rbp = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i
  r12 : s.gpr .r12 = VG.Proof.Scrypt.X86_64.RoMix.vP s₀
  r13 : s.gpr .r13 = VG.Proof.Scrypt.X86_64.RoMix.sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)
  frame : Frame [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] s₀.mem s.mem
  kept : VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ s.mem
  x : bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) i (VG.Proof.Scrypt.X86_64.RoMix.B s₀)
  done : ∀ k < i, bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86_64.RoMix.B s₀)

theorem setupMem_kept (s₀ : State) :
    VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ ((VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀).writeW (VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀))) :=
  ⟨Spill.Saved.writeW (VG.Proof.Scrypt.X86_64.RoMix.saveMem_saved s₀) _ (fun _ hp => by have := VG.Proof.Scrypt.X86_64.RoMix.saved_offs hp; omega)
    (fun _ hp => by have := VG.Proof.Scrypt.X86_64.RoMix.saved_offs hp; omega) (by decide), Mem.readW_writeW_self64 _ _ _⟩

/-- After the loop computing `N`. -/
structure N1 (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀
  r12 : s.gpr .r12 = VG.Proof.Scrypt.X86_64.RoMix.vP s₀
  r13 : s.gpr .r13 = VG.Proof.Scrypt.X86_64.RoMix.sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  rdx : s.gpr .rdx = BitVec.ofNat 64 (2 * VG.Proof.Scrypt.X86_64.RoMix.NN s₀)

theorem nloop_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.P1 s₀ s) : WP isa nLoop s (VG.Proof.Scrypt.X86_64.RoMix.N1 s₀) := by
  obtain ⟨e, he⟩ := hp.pow
  have lt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have pos := hp.pos
  have e2 : VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * 2 ^ (e + 1) = 2 * VG.Proof.Scrypt.X86_64.RoMix.vl s₀ := by
    rw [hp.vl_eq, he, Nat.pow_succ]; simp only [Nat.mul_assoc, Nat.mul_comm]
  have hNe : 2 * VG.Proof.Scrypt.X86_64.RoMix.vl s₀ < 2 ^ 64 := by
    have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ = 128 * VG.Proof.Scrypt.X86_64.RoMix.vl s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.nLoop_ok (r := VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (e := e) hp.pos (by omega) h.rax h.rdx
    (by rw [h.rcx, e2])) fun t ⟨rd, wr, mem, oth, rdx⟩ => ?_
  have k : ∀ r, r ≠ .rax → r ≠ .rdx → t.gpr r = s.gpr r := oth
  exact ⟨by rw [rd, h.rd], by rw [wr, h.wr], by rw [mem, h.mem],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx],
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [rdx, he, Nat.pow_succ, Nat.mul_comm]⟩

theorem setup2_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.N1 s₀ s) :
    WP isa (.block rmSetup) s (VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ 0) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have n1 := VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp
  have : 2 * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ < 2 ^ 64 := by
    have : 2 * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by
      have := hp.pos
      have : 2 ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := by omega
      exact Nat.mul_le_mul_right _ this
    omega
  unfold rmSetup
  refine VG.Proof.Scrypt.X86_64.RoMix.wp_shr (by decide) (by decide) fun t1 u1 _ => ?_
  have hd : t1.gpr .rdx = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) := by
    rw [u1.gpr, h.rdx, VG.Proof.Scrypt.X86_64.RoMix.shr_ofNat _ (by omega), Nat.pow_one, Nat.mul_div_cancel_left _ (by decide)]
  refine wp_store (a := VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 176)
    (by rw [BlockMix.ea_at, u1.other _ (by decide), h.r13])
    (by rw [u1.wr, h.wr, hp.wr]; exact Memory.InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86_64.RoMix.in_s s₀ (by omega)))
    fun t2 g2 m2 rd2 wr2 => wp_mov fun t3 u3 _ _ => wp_mov fun t4 u4 _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdx → r ≠ .r15 → r ≠ .rbp → t4.gpr r = s.gpr r := fun r b c d => by
    rw [u4.other _ d, u3.other _ c, g2, u1.other _ b]
  have hm : t4.mem = (VG.Proof.Scrypt.X86_64.RoMix.saveMem s₀).writeW (VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 176) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀)) := by
    rw [u4.mem, u3.mem, m2, hd, u1.mem, h.mem]
  have fr : Frame [VG.Proof.Scrypt.X86_64.RoMix.scR s₀] s₀.mem t4.mem := by
    rw [hm]; exact (VG.Proof.Scrypt.X86_64.RoMix.saveMem_frame s₀).writeW (List.mem_singleton_self _) _ (VG.Proof.Scrypt.X86_64.RoMix.in_s s₀ (by omega))
  refine ⟨Nat.zero_le _, by rw [u4.rd, u3.rd, rd2, u1.rd, h.rd],
    by rw [u4.wr, u3.wr, wr2, u1.wr, h.wr], by rw [g _ (by decide) (by decide) (by decide), h.rsp],
    by rw [g _ (by decide) (by decide) (by decide), h.rbx], ?_,
    by rw [g _ (by decide) (by decide) (by decide), h.r12],
    by rw [g _ (by decide) (by decide) (by decide), h.r13],
    by rw [g _ (by decide) (by decide) (by decide), h.r14], ?_,
    fr.mono (by simp), by rw [hm]; exact VG.Proof.Scrypt.X86_64.RoMix.setupMem_kept s₀, ?_, fun k hk => absurd hk (by omega)⟩
  · rw [u4.gpr, u3.other _ (by decide), g2, u1.other _ (by decide), h.r12]
    simp
  · rw [u4.other _ (by decide), u3.gpr, g2, hd]; rfl
  · refine VG.Proof.Scrypt.X86_64.RoMix.frame_bytesAt' fr (fun r hr => ?_) (by have := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp; omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_s.sub_left (VG.Proof.Scrypt.X86_64.RoMix.b_sub' (s₀ := s₀))

theorem start_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.P1 s₀ s) {rest : Prog isa}
    {Q : State → Prop} (hk : ∀ s', VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ 0 s' → WP isa rest s' Q) :
    WP isa (.seq nLoop (.seq (.block rmSetup) rest)) s Q :=
  WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.nloop_ok hp h) fun _ h' => WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.setup2_ok hp h') hk))

/-! ## A call of `vg_scrypt_blockmix` into `b` -/

/-- The instructions before the call, after `rdi` is set. -/
abbrev bmTail : List Instr :=
  [.mov .rsi (.reg .r14), .shift .shr .rsi 7, .mov .rcx (.reg .rsi), .mov .rdx (.reg .rbx),
    .mov .r8 (.reg .r13)]

theorem blockMixTo_eq (c : Prog isa) (src : List Instr) :
    blockMixTo c src = .seq (.block (src ++ VG.Proof.Scrypt.X86_64.RoMix.bmTail)) (.call "vg_scrypt_blockmix" c) := rfl

theorem b_in {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) : InRegions s₀.wr (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
  rw [hp.wr]
  refine Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.bR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem w_in {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) : InRegions s₀.wr (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) 128 := by
  rw [hp.wr]
  refine Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.scR s₀) (by simp) ?_
  simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem calleeSaved_tail {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Setting up and making the call, from `rdi = A`. -/
theorem bm_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86_64.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State} {A : Addr}
    (hA : s.gpr .rdi = A) (hbx : s.gpr .rbx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (h13 : s.gpr .r13 = VG.Proof.Scrypt.X86_64.RoMix.sc s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) (hsp : s.gpr .rsp = s₀.gpr .rsp)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hAb : Region.Disjoint ⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩)
    (hAw : Region.Disjoint ⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩)
    (hAs : (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀).Disjoint ⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩) (hAn : A.toNat + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 2 ^ 64)
    (hAi : InRegions (s₀.rd ++ s₀.wr) A (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (bytesAt s.mem A (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) →
      Q s') :
    WP isa (.block VG.Proof.Scrypt.X86_64.RoMix.bmTail) s fun s' => WP isa (.call "vg_scrypt_blockmix" c) s' Q := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  refine wp_mov fun a ua _ _ => VG.Proof.Scrypt.X86_64.RoMix.wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ?_
  have k : ∀ r, r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → f.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [uf.other _ h4, ue.other _ h3, ud.other _ h2, ub.other _ h1, ua.other _ h1]
  have hsi : b.gpr .rsi = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
    rw [ub.gpr, ua.gpr, h14, VG.Proof.Scrypt.X86_64.RoMix.shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  have hm : f.mem = s.mem := by rw [uf.mem, ue.mem, ud.mem, ub.mem, ua.mem]
  have hsp' : f.gpr .rsp = s₀.gpr .rsp := by rw [k _ (by decide) (by decide) (by decide) (by decide), hsp]
  refine hS f A (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
    (by rw [k _ (by decide) (by decide) (by decide) (by decide), hA])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi])
    (by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), hbx])
    (by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi])
    (by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h13])
    hp.pos lt ((hp.b_s.sub_left (VG.Proof.Scrypt.X86_64.RoMix.b_sub' (s₀ := s₀))).sub_right (VG.Proof.Scrypt.X86_64.RoMix.w_sub (s₀ := s₀))) hAb hAw
    (by rw [hsp']; exact hAs) (by rw [hsp']; exact hp.stk_b.sub_right (VG.Proof.Scrypt.X86_64.RoMix.b_sub' (s₀ := s₀)))
    (by rw [hsp']; exact hp.stk_s.sub_right (VG.Proof.Scrypt.X86_64.RoMix.w_sub (s₀ := s₀))) hAn (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega)
    (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hrd, hwr]; exact hAi)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact VG.Proof.Scrypt.X86_64.RoMix.b_in hp)
    (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr, hwr]; exact VG.Proof.Scrypt.X86_64.RoMix.w_in hp) _
    fun s' rd' wr' cs' f' b' => hQ s' (by rw [rd', uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [wr', uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      (fun r hr => by
        obtain ⟨h1, h2, h3, h4⟩ := VG.Proof.Scrypt.X86_64.RoMix.calleeSaved_tail hr
        rw [cs' r hr, k r h1 h2 h3 h4])
      (by rw [hm, hsp'] at f'; exact f') (by rw [b', hm])

/-! ## Step 2 -/

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀)
include hp

theorem vAt_nw {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) : (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i).toNat + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 2 ^ 64 := by
  have := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have := hp.pos
  have hv := hp.v_nw
  have e : VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128 = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [Memory.toNat_add_ofNat _ (by omega)]
  omega

theorem vAt_in {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) : InRegions s₀.wr (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
  rw [hp.wr]
  have e : VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128 = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have lt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.vR s₀) (by simp)
    (Memory.contains_off (by rw [e]; omega) (by omega))

/-- `(V[i]'(by omega))` and the parts of `scratch` and the stack we use. -/
theorem vAt_b {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) : Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86_64.RoMix.bR s₀) :=
  hp.b_v.symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.vAt_sub hp hi)
theorem vAt_s {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) : Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86_64.RoMix.scR s₀) :=
  hp.v_s.sub_left (VG.Proof.Scrypt.X86_64.RoMix.vAt_sub hp hi)
theorem vAt_stk {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) : Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀) :=
  hp.stk_v.symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.vAt_sub hp hi)

omit hp in
/-- The frame of a call writing `b`, from the one we keep. -/
theorem call_frame {m m' : Mem} (hf : Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] m m') :
    Frame [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Scrypt.X86_64.RoMix.bR s₀, by simp, VG.Proof.Scrypt.X86_64.RoMix.b_sub'⟩
    · exact ⟨VG.Proof.Scrypt.X86_64.RoMix.scR s₀, by simp, VG.Proof.Scrypt.X86_64.RoMix.w_sub⟩
    · exact ⟨VG.Proof.Scrypt.X86_64.RoMix.stkR s₀, by simp, fun _ h => h⟩

/-- What a call writing `b` keeps: `(V[k]'(by omega))`. -/
theorem call_keeps_v {m m' : Mem} (hf : Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] m m')
    {k : Nat} (hk : k < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) :
    bytesAt m' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = bytesAt m (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
  refine VG.Proof.Scrypt.X86_64.RoMix.frame_bytesAt' hf (fun r hr => ?_) (by have := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (VG.Proof.Scrypt.X86_64.RoMix.vAt_b hp hk).sub_right VG.Proof.Scrypt.X86_64.RoMix.b_sub'
  · exact (VG.Proof.Scrypt.X86_64.RoMix.vAt_s hp hk).sub_right VG.Proof.Scrypt.X86_64.RoMix.w_sub
  · exact VG.Proof.Scrypt.X86_64.RoMix.vAt_stk hp hk

theorem call_kept {m m' : Mem} (hf : Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] m m')
    (h : VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ m) : VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ m' :=
  h.frame hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (VG.Proof.Scrypt.X86_64.RoMix.keep_b hp).sub_right VG.Proof.Scrypt.X86_64.RoMix.b_sub'
    · exact VG.Proof.Scrypt.X86_64.RoMix.keep_w
    · exact VG.Proof.Scrypt.X86_64.RoMix.keep_stk hp

/-- The memory after iteration `i` of step 2. -/
theorem mem2_ok {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ i s) {m₃ : Mem}
    (f₃ : Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀]
      (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))) m₃)
    (b₃ : bytesAt m₃ (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
      (bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))) (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i)
        (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))) :
    Frame [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] s₀.mem m₃ ∧ VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ m₃ ∧
    bytesAt m₃ (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) (i + 1) (VG.Proof.Scrypt.X86_64.RoMix.B s₀) ∧
    ∀ k < i + 1, bytesAt m₃ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86_64.RoMix.B s₀) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  have hl : (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)).length = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := Memory.bytesAt_length _ _ _
  have hself : bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))) (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i)
      (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) i (VG.Proof.Scrypt.X86_64.RoMix.B s₀) := by
    have := Memory.bytesAt_writeBytes_self s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))
      (by rw [hl]; exact lt)
    rw [hl] at this
    rw [this, h.x]
  have f₂ : Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩] s.mem
      (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] s.mem
      (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Scrypt.X86_64.RoMix.vR s₀, by simp, VG.Proof.Scrypt.X86_64.RoMix.vAt_sub hp hi⟩
  refine ⟨(h.frame.trans f₂').trans (VG.Proof.Scrypt.X86_64.RoMix.call_frame f₃), VG.Proof.Scrypt.X86_64.RoMix.call_kept hp f₃ (h.kept.frame f₂ fun r hr => ?_),
    by rw [b₃, hself]; rfl, fun k hk => ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact (VG.Proof.Scrypt.X86_64.RoMix.keep_v hp).sub_right (VG.Proof.Scrypt.X86_64.RoMix.vAt_sub hp hi)
  · rw [VG.Proof.Scrypt.X86_64.RoMix.call_keeps_v hp f₃ (by omega)]
    by_cases hki : k = i
    · subst hki; exact hself
    · rw [Memory.bytesAt_writeBytes_sep _ _ (by rw [hl]; exact VG.Proof.Scrypt.X86_64.RoMix.vAt_disj hp (by omega) hi hki) lt]
      exact h.done k (by omega)

end

theorem cs_ne {r : Reg} (hr : r ∈ calleeSaved) :
    r ≠ .rax ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .r8 := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem vAt_succ (s₀ : State) (i : Nat) :
    VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ (i + 1) := by
  show _ = VG.Proof.Scrypt.X86_64.RoMix.vP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * (i + 1))
  rw [Memory.add_ofNat, Nat.mul_succ]

theorem b_word {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {k : Nat} (hk : k < 16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) :
    InRegions (s₀.rd ++ s₀.wr) (VG.Proof.Scrypt.X86_64.RoMix.bP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  rw [hp.rd, hp.wr]
  exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.bR s₀) (by simp) (Memory.contains_off (by omega) (by omega))

theorem v_word {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {i k : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (hk : k < 16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) :
    InRegions s₀.wr (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i + BitVec.ofNat 64 (8 * k)) 8 := by
  rw [hp.wr]
  have e : VG.Proof.Scrypt.X86_64.RoMix.vl s₀ * 128 = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by rw [hp.vl_eq]; simp only [Nat.mul_comm, Nat.mul_left_comm]
  have : 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  have lt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  show InRegions _ (VG.Proof.Scrypt.X86_64.RoMix.vP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * i) + BitVec.ofNat 64 (8 * k)) 8
  rw [Memory.add_ofNat]
  exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.vR s₀) (by simp)
    (Memory.contains_off (by rw [e]; omega) (by omega))

/-- One iteration of step 2. -/
theorem step2_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86_64.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {i : Nat}
    (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ i s) :
    WP isa (step2 c) s fun s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀)) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  have vlt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have pos := hp.pos
  have n1 := VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp
  have hN : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ < 2 ^ 64 := by
    have : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold step2
  refine WP.seq (wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ =>
    VG.Proof.Scrypt.X86_64.RoMix.wp_shr (by decide) (by decide) fun e ue _ => WP.block_nil ?_)
  have ke : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → e.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [ue.other _ h3, ud.other _ h3, ub.other _ h2, ua.other _ h1]
  have erd : e.rd = s₀.rd := by rw [ue.rd, ud.rd, ub.rd, ua.rd, h.rd]
  have ewr : e.wr = s₀.wr := by rw [ue.wr, ud.wr, ub.wr, ua.wr, h.wr]
  have hme : e.mem = s.mem := by rw [ue.mem, ud.mem, ub.mem, ua.mem]
  have ecx : e.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
    rw [ue.gpr, ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r14, VG.Proof.Scrypt.X86_64.RoMix.shr_ofNat _ lt]
    congr 1; omega
  have e8 : 8 * (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := by omega
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.copyLoop_ok (src := VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (dst := VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (n := 16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (by omega)
    (by omega) (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.gpr, h.rbx])
    (by rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.rbp])
    ecx (fun k hk => by rw [erd, ewr]; exact VG.Proof.Scrypt.X86_64.RoMix.b_word hp hk)
    (fun k hk => by rw [ewr]; exact VG.Proof.Scrypt.X86_64.RoMix.v_word hp hi hk)
    (by rw [e8]; exact (VG.Proof.Scrypt.X86_64.RoMix.vAt_b hp hi).symm.sub_left VG.Proof.Scrypt.X86_64.RoMix.b_sub'))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [hme, e8] at mt
  have kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, -⟩ := VG.Proof.Scrypt.X86_64.RoMix.cs_ne hr
    rw [gt r h1 h2 h3 h4, ke r h2 h3 h4]
  rw [VG.Proof.Scrypt.X86_64.RoMix.blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun f uf _ _ => ?_))
  have kf : ∀ r ∈ calleeSaved, f.gpr r = s.gpr r := fun r hr => by
    rw [uf.other _ (VG.Proof.Scrypt.X86_64.RoMix.cs_ne hr).2.1, kt r hr]
  have cs : ∀ r ∈ calleeSaved, r ∈ calleeSaved := fun _ h => h
  refine VG.Proof.Scrypt.X86_64.RoMix.bm_ok hS hp (A := VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (by rw [uf.gpr, kt _ (by simp [calleeSaved]), h.rbp])
    (by rw [kf _ (by simp [calleeSaved]), h.rbx]) (by rw [kf _ (by simp [calleeSaved]), h.r13])
    (by rw [kf _ (by simp [calleeSaved]), h.r14]) (by rw [kf _ (by simp [calleeSaved]), h.rsp])
    (by rw [uf.rd, rdt, erd]) (by rw [uf.wr, wrt, ewr])
    ((VG.Proof.Scrypt.X86_64.RoMix.vAt_b hp hi).sub_right VG.Proof.Scrypt.X86_64.RoMix.b_sub') ((VG.Proof.Scrypt.X86_64.RoMix.vAt_s hp hi).sub_right VG.Proof.Scrypt.X86_64.RoMix.w_sub) (VG.Proof.Scrypt.X86_64.RoMix.vAt_stk hp hi).symm
    (VG.Proof.Scrypt.X86_64.RoMix.vAt_nw hp hi) (Memory.InRegions.right (VG.Proof.Scrypt.X86_64.RoMix.vAt_in hp hi)) fun s4 rd4 wr4 cs4 f4 b4 => ?_
  rw [uf.mem, mt] at f4 b4
  obtain ⟨F, K, X, D⟩ := VG.Proof.Scrypt.X86_64.RoMix.mem2_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [cs4 r hr, kf r hr]
  refine wp_add fun s5 u5 => wp_subi fun s6 u6 z6 => WP.block_nil ?_
  have k6 : ∀ r ∈ calleeSaved, r ≠ .rbp → r ≠ .r15 → s6.gpr r = s.gpr r := fun r hr h1 h2 => by
    rw [u6.other _ h2, u5.other _ h1, k4 r hr]
  have e15 : s5.gpr .r15 = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i) := by
    rw [u5.other _ (by decide), k4 _ (by simp [calleeSaved]), h.r15]
  refine ⟨⟨by omega, by rw [u6.rd, u5.rd, rd4, uf.rd, rdt, erd], by rw [u6.wr, u5.wr, wr4, uf.wr, wrt, ewr],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.rsp],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.rbx], ?_,
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r12],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r13],
    by rw [k6 _ (by simp [calleeSaved]) (by decide) (by decide), h.r14],
    by rw [u6.gpr, e15, VG.Proof.Scrypt.X86_64.RoMix.dec_count hi],
    by rw [u6.mem, u5.mem]; exact F, by rw [u6.mem, u5.mem]; exact K,
    by rw [u6.mem, u5.mem]; exact X, by rw [u6.mem, u5.mem]; exact D⟩, ?_⟩
  · rw [u6.other _ (by decide), u5.gpr, k4 _ (by simp [calleeSaved]), k4 _ (by simp [calleeSaved]),
      h.rbp, h.r14, VG.Proof.Scrypt.X86_64.RoMix.vAt_succ]
  · rw [z6, e15, VG.Proof.Scrypt.X86_64.RoMix.dec_zf hi hN]

theorem loop2_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86_64.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ 0 s) : WP isa (.loop (step2 c) .ne) s (VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀)) :=
  VG.Proof.Scrypt.X86_64.RoMix.count_loop (VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp) (VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀) (fun _ hi _ h => VG.Proof.Scrypt.X86_64.RoMix.step2_ok hS hp hi h) h

/-! ## Step 3 -/

/-- After `i` iterations of step 3. -/
structure Inv3 (s₀ : State) (i : Nat) (s : State) : Prop where
  i_le : i ≤ VG.Proof.Scrypt.X86_64.RoMix.NN s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀
  rbp : s.gpr .rbp = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - 1)
  r12 : s.gpr .r12 = VG.Proof.Scrypt.X86_64.RoMix.vP s₀
  r13 : s.gpr .r13 = VG.Proof.Scrypt.X86_64.RoMix.sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  r15 : s.gpr .r15 = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)
  frame : Frame [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] s₀.mem s.mem
  kept : VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ s.mem
  v : ∀ k < VG.Proof.Scrypt.X86_64.RoMix.NN s₀, bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86_64.RoMix.B s₀)
  x : (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)
    (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))).1 = roMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)
  /-- The indices still to come. -/
  js : (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)
    (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))).2 =
      (Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)).drop i

theorem mid_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s) :
    WP isa (.block rmMid) s (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ 0) := by
  have n1 := VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp
  unfold rmMid
  refine wp_movm (a := VG.Proof.Scrypt.X86_64.RoMix.sc s₀ + BitVec.ofNat 64 176) (by rw [BlockMix.ea_at, h.r13])
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.scR s₀) (by simp) (VG.Proof.Scrypt.X86_64.RoMix.in_s s₀ (by omega)))
    fun a ua => wp_mov fun b ub _ _ => wp_subi fun d ud _ => WP.block_nil ?_
  have ka : a.gpr .r15 = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) := by rw [ua.gpr, h.kept.2]
  have k : ∀ r, r ≠ .r15 → r ≠ .rbp → d.gpr r = s.gpr r := fun r h1 h2 => by
    rw [ud.other _ h2, ub.other _ h2, ua.other _ h1]
  have hm : d.mem = s.mem := by rw [ud.mem, ub.mem, ua.mem]
  refine ⟨Nat.zero_le _, by rw [ud.rd, ub.rd, ua.rd, h.rd], by rw [ud.wr, ub.wr, ua.wr, h.wr],
    by rw [k _ (by decide) (by decide), h.rsp], by rw [k _ (by decide) (by decide), h.rbx], ?_,
    by rw [k _ (by decide) (by decide), h.r12], by rw [k _ (by decide) (by decide), h.r13],
    by rw [k _ (by decide) (by decide), h.r14], by rw [ud.other _ (by decide), ub.other _ (by decide), ka]; rfl,
    by rw [hm]; exact h.frame, by rw [hm]; exact h.kept, fun k hk => by rw [hm]; exact h.done k hk, ?_,
    ?_⟩
  · rw [ud.gpr, ub.gpr, ka]
    have := VG.Proof.Scrypt.X86_64.RoMix.dec_count (n := VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (k := 0) n1
    simpa using this
  · rw [hm, h.x, Nat.sub_zero]
    exact (roMix_eq _ _ _).symm
  · rw [hm, h.x, Nat.sub_zero, List.drop_zero]
    exact (roMixIndices_eq _ _ _).symm

/-- The address of the low word of `X`'s last 64-byte block. -/
theorem ea_j {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) (s : State) (hbx : s.gpr .rbx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) :
    s.ea { base := .rbx, index := some .r14, disp := -64 } =
      VG.Proof.Scrypt.X86_64.RoMix.bP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ - 64) := by
  have := hp.pos
  simp only [State.ea, hbx, h14]
  rw [ofNat_split (a := 64) (b := 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (by omega),
    show BitVec.ofInt 64 (-64) = 0 - BitVec.ofNat 64 64 by decide]
  bv_omega

/-- The index `j`. -/
abbrev jOf (s₀ : State) (m : Mem) : Nat :=
  Spec.Scrypt.integerify (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (bytesAt m (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) % VG.Proof.Scrypt.X86_64.RoMix.NN s₀

theorem jOf_lt {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) (m : Mem) : VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ m < VG.Proof.Scrypt.X86_64.RoMix.NN s₀ :=
  Nat.mod_lt _ (VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp)

/-- `j` as the code computes it. -/
theorem jOf_eq {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) (m : Mem) :
    m.readW (VG.Proof.Scrypt.X86_64.RoMix.bP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ - 64)) 64 &&& BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - 1) =
      BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ m) := by
  obtain ⟨e, he⟩ := hp.pow
  have vlt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
  have he' : e ≤ 64 := by
    by_contra hc
    have : 2 ^ 64 < 2 ^ e := Nat.pow_lt_pow_right (by decide) (by omega)
    omega
  apply BitVec.eq_of_toNat_eq
  rw [Memory.toNat_ofNat_lt (by have := VG.Proof.Scrypt.X86_64.RoMix.jOf_lt hp m; omega), he, and_mask _ he', VG.Proof.Scrypt.X86_64.RoMix.jOf, he,
    integerify_mod _ _ hp.pos he']

theorem t_word {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {k : Nat} (hk : k < 16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) :
    InRegions s₀.wr (VG.Proof.Scrypt.X86_64.RoMix.tP s₀ + BitVec.ofNat 64 (8 * k)) 8 := by
  have := hp.s_nw
  rw [hp.wr, Memory.add_ofNat]
  exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.scR s₀) (by simp) (Memory.contains_off (by omega) (by omega))

theorem t_in {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) : InRegions s₀.wr (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
  have := hp.s_nw
  rw [hp.wr]
  exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.scR s₀) (by simp) (Memory.contains_off (by omega) (by omega))

theorem t_b {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86_64.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ :=
  (hp.b_s.symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.t_sub hp)).sub_right VG.Proof.Scrypt.X86_64.RoMix.b_sub'

theorem t_nw {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) : (VG.Proof.Scrypt.X86_64.RoMix.tP s₀).toNat + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 2 ^ 64 := by
  have := hp.s_nw
  rw [Memory.toNat_add_ofNat _ (by omega)]
  omega

/-- The memory after iteration `i` of step 3. -/
theorem mem3_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s)
    {m₄ : Mem}
    (f₄ : Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀]
      (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))
        (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ (VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem)) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)))) m₄)
    (b₄ : bytesAt m₄ (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
      (bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))
        (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ (VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem)) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)))) (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))) :
    Frame [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] s₀.mem m₄ ∧ VG.Proof.Scrypt.X86_64.RoMix.Kept s₀ m₄ ∧
    (∀ k < VG.Proof.Scrypt.X86_64.RoMix.NN s₀, bytesAt m₄ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86_64.RoMix.B s₀)) ∧
    (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - (i + 1))
      (bytesAt m₄ (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))).1 = roMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀) ∧
    (Spec.Scrypt.mixLoop (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (vList (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - (i + 1))
      (bytesAt m₄ (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))).2 =
        (Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)).drop (i + 1) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  have hj := VG.Proof.Scrypt.X86_64.RoMix.jOf_lt hp s.mem
  set T := Spec.Pbkdf2.xorBytes (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀))
    (bytesAt s.mem (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ (VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem)) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) with hT
  have hl : T.length = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := by
    rw [hT, Memory.xorBytes_length _ _ (by simp [Memory.bytesAt_length]), Memory.bytesAt_length]
  have hself : bytesAt (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) T) (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = T := by
    have := Memory.bytesAt_writeBytes_self s.mem (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) T (by rw [hl]; exact lt)
    rwa [hl] at this
  have f₂ : Frame [⟨VG.Proof.Scrypt.X86_64.RoMix.tP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) T) :=
    Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [hl]; exact Region.contains_self _ _)
  have f₂' : Frame [VG.Proof.Scrypt.X86_64.RoMix.bR s₀, VG.Proof.Scrypt.X86_64.RoMix.vR s₀, VG.Proof.Scrypt.X86_64.RoMix.scR s₀, VG.Proof.Scrypt.X86_64.RoMix.stkR s₀] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) T) :=
    f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Scrypt.X86_64.RoMix.scR s₀, by simp, VG.Proof.Scrypt.X86_64.RoMix.t_sub hp⟩
  have hv : ∀ k < VG.Proof.Scrypt.X86_64.RoMix.NN s₀, bytesAt m₄ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ k) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = Nat.repeat (blockMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) k (VG.Proof.Scrypt.X86_64.RoMix.B s₀) :=
    fun k hk => by
      rw [VG.Proof.Scrypt.X86_64.RoMix.call_keeps_v hp f₄ hk, Memory.bytesAt_writeBytes_sep _ _
        (by rw [hl]; exact (VG.Proof.Scrypt.X86_64.RoMix.vAt_s hp hk).sub_right (VG.Proof.Scrypt.X86_64.RoMix.t_sub hp)) lt]
      exact h.v k hk
  have e : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i = VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - (i + 1) + 1 := by omega
  refine ⟨(h.frame.trans f₂').trans (VG.Proof.Scrypt.X86_64.RoMix.call_frame f₄),
    VG.Proof.Scrypt.X86_64.RoMix.call_kept hp f₄ (h.kept.frame f₂ fun r hr => ?_), hv, ?_, ?_⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact VG.Proof.Scrypt.X86_64.RoMix.keep_t hp
  · rw [← h.x, e, mixLoop_succ_fst, b₄, hself, hT, vList_getD _ hj, h.v _ hj]
  · have hs := h.js
    rw [e, mixLoop_succ_snd, vList_getD _ hj, ← h.v _ hj] at hs
    rw [← List.tail_drop, ← hs, b₄, hself, hT]
    rfl

theorem sx192 : (192 : BitVec 32).signExtend 64 = BitVec.ofNat 64 192 := by decide

/-- One iteration of step 3. -/
theorem step3_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86_64.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {i : Nat}
    (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s) :
    WP isa (step3 c) s fun s' => VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀)) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  have vlt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have pos := hp.pos
  have hN : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ < 2 ^ 64 := by
    have : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hj := VG.Proof.Scrypt.X86_64.RoMix.jOf_lt hp s.mem
  have e8 : 8 * (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := by omega
  have hrd : s.rd = s₀.rd := h.rd
  have hwr : s.wr = s₀.wr := h.wr
  unfold step3 jBlock
  refine WP.seq (wp_movm (a := VG.Proof.Scrypt.X86_64.RoMix.bP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ - 64)) (VG.Proof.Scrypt.X86_64.RoMix.ea_j hp s h.rbx h.r14)
    (by rw [hrd, hwr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.bR s₀) (by simp)
          (Memory.contains_off (by omega) (by omega)))
    fun a ua => VG.Proof.Scrypt.X86_64.RoMix.wp_and fun b ub => WP.block_nil ?_)
  have hax : b.gpr .rax = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem) := by
    rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp]; exact VG.Proof.Scrypt.X86_64.RoMix.jOf_eq hp s.mem
  refine WP.seq (wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => WP.block_nil ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.mulLoop_ok (j := VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem) (c := 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (a := VG.Proof.Scrypt.X86_64.RoMix.vP s₀)
    (by omega) (by rw [ue.other _ (by decide), ud.other _ (by decide), hax])
    (by rw [ue.other _ (by decide), ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r12])
    (by rw [ue.gpr, ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14]))
    fun f ⟨rdf, wrf, mf, gf, dxf⟩ => ?_)
  have hdx : f.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ (VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem) := by rw [dxf, Nat.mul_comm]
  refine WP.seq (wp_mov fun g1 u1 _ _ => wp_mov fun g2 u2 _ _ => wp_mov fun g3 u3 _ _ =>
    wp_addi fun g4 u4 => wp_mov fun g5 u5 _ _ => VG.Proof.Scrypt.X86_64.RoMix.wp_shr (by decide) (by decide) fun g6 u6 _ =>
    WP.block_nil ?_)
  have rd6 : g6.rd = s₀.rd := by
    rw [u6.rd, u5.rd, u4.rd, u3.rd, u2.rd, u1.rd, rdf, ue.rd, ud.rd, ub.rd, ua.rd, hrd]
  have wr6 : g6.wr = s₀.wr := by
    rw [u6.wr, u5.wr, u4.wr, u3.wr, u2.wr, u1.wr, wrf, ue.wr, ud.wr, ub.wr, ua.wr, hwr]
  have m6 : g6.mem = s.mem := by
    rw [u6.mem, u5.mem, u4.mem, u3.mem, u2.mem, u1.mem, mf, ue.mem, ud.mem, ub.mem, ua.mem]
  have k6 : ∀ r ∈ calleeSaved, g6.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := VG.Proof.Scrypt.X86_64.RoMix.cs_ne hr
    rw [u6.other _ h4, u5.other _ h4, u4.other _ h6, u3.other _ h6, u2.other _ h3, u1.other _ h2,
      gf _ h1 h5 h4, ue.other _ h4, ud.other _ h5, ub.other _ h1, ua.other _ h1]
  have x6 : g6.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.tP s₀ := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.gpr, u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r13, VG.Proof.Scrypt.X86_64.RoMix.sx192]
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.xorLoop_ok (x := VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (y := VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ (VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem)) (d := VG.Proof.Scrypt.X86_64.RoMix.tP s₀)
    (n := 16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (by omega) (by omega)
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.other _ (by decide), u1.gpr, gf _ (by decide) (by decide) (by decide),
      ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide),
      h.rbx])
    (by rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), u2.gpr, u1.other _ (by decide), hdx])
    x6
    (by rw [u6.gpr, u5.gpr, u4.other _ (by decide), u3.other _ (by decide), u2.other _ (by decide),
      u1.other _ (by decide), gf _ (by decide) (by decide) (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), h.r14,
      VG.Proof.Scrypt.X86_64.RoMix.shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega))
    (fun k hk => by rw [rd6, wr6]; exact VG.Proof.Scrypt.X86_64.RoMix.b_word hp hk)
    (fun k hk => by rw [rd6, wr6]; exact Memory.InRegions.right (VG.Proof.Scrypt.X86_64.RoMix.v_word hp hj hk))
    (fun k hk => by rw [wr6]; exact VG.Proof.Scrypt.X86_64.RoMix.t_word hp hk)
    (by rw [e8]; exact VG.Proof.Scrypt.X86_64.RoMix.t_b hp) (by rw [e8]; exact (VG.Proof.Scrypt.X86_64.RoMix.vAt_s hp hj).symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.t_sub hp)))
    fun t ⟨rdt, wrt, gt, mt⟩ => ?_)
  rw [m6, e8] at mt
  have kt : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := fun r hr => by
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := VG.Proof.Scrypt.X86_64.RoMix.cs_ne hr
    rw [gt r h1 h2 h3 h6 h4, k6 r hr]
  rw [VG.Proof.Scrypt.X86_64.RoMix.blockMixTo_eq]
  refine WP.seq (WP.seq (wp_mov fun q1 v1 _ _ => wp_addi fun q2 v2 => ?_))
  have kq : ∀ r ∈ calleeSaved, q2.gpr r = s.gpr r := fun r hr => by
    rw [v2.other _ (VG.Proof.Scrypt.X86_64.RoMix.cs_ne hr).2.1, v1.other _ (VG.Proof.Scrypt.X86_64.RoMix.cs_ne hr).2.1, kt r hr]
  refine VG.Proof.Scrypt.X86_64.RoMix.bm_ok hS hp (A := VG.Proof.Scrypt.X86_64.RoMix.tP s₀)
    (by rw [v2.gpr, v1.gpr, kt _ (by decide), h.r13, VG.Proof.Scrypt.X86_64.RoMix.sx192])
    (by rw [kq _ (by decide), h.rbx]) (by rw [kq _ (by decide), h.r13])
    (by rw [kq _ (by decide), h.r14]) (by rw [kq _ (by decide), h.rsp])
    (by rw [v2.rd, v1.rd, rdt, rd6]) (by rw [v2.wr, v1.wr, wrt, wr6])
    (VG.Proof.Scrypt.X86_64.RoMix.t_b hp) (VG.Proof.Scrypt.X86_64.RoMix.t_w hp) (hp.stk_s.sub_right (VG.Proof.Scrypt.X86_64.RoMix.t_sub hp)) (VG.Proof.Scrypt.X86_64.RoMix.t_nw hp)
    (Memory.InRegions.right (VG.Proof.Scrypt.X86_64.RoMix.t_in hp)) fun s4 rd4 wr4 cs4 f4 b4 => ?_
  rw [v2.mem, v1.mem, mt] at f4 b4
  obtain ⟨F, K, V, X, J⟩ := VG.Proof.Scrypt.X86_64.RoMix.mem3_ok hp hi h f4 b4
  have k4 : ∀ r ∈ calleeSaved, s4.gpr r = s.gpr r := fun r hr => by rw [cs4 r hr, kq r hr]
  refine wp_subi fun s5 u5 z5 => WP.block_nil ?_
  have k5 : ∀ r ∈ calleeSaved, r ≠ .r15 → s5.gpr r = s.gpr r := fun r hr h1 => by
    rw [u5.other _ h1, k4 r hr]
  have e15 : s4.gpr .r15 = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i) := by rw [k4 _ (by decide), h.r15]
  refine ⟨⟨by omega, by rw [u5.rd, rd4, v2.rd, v1.rd, rdt, rd6],
    by rw [u5.wr, wr4, v2.wr, v1.wr, wrt, wr6],
    by rw [k5 _ (by decide) (by decide), h.rsp], by rw [k5 _ (by decide) (by decide), h.rbx],
    by rw [k5 _ (by decide) (by decide), h.rbp], by rw [k5 _ (by decide) (by decide), h.r12],
    by rw [k5 _ (by decide) (by decide), h.r13], by rw [k5 _ (by decide) (by decide), h.r14],
    by rw [u5.gpr, e15, VG.Proof.Scrypt.X86_64.RoMix.dec_count hi],
    by rw [u5.mem]; exact F, by rw [u5.mem]; exact K, by rw [u5.mem]; exact V,
    by rw [u5.mem]; exact X, by rw [u5.mem]; exact J⟩, by rw [z5, e15, VG.Proof.Scrypt.X86_64.RoMix.dec_zf hi hN]⟩

theorem loop3_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86_64.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ 0 s) : WP isa (.loop (step3 c) .ne) s (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀)) :=
  VG.Proof.Scrypt.X86_64.RoMix.count_loop (VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp) (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀) (fun _ hi _ h => VG.Proof.Scrypt.X86_64.RoMix.step3_ok hS hp hi h) h

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s) :
    WP isa (.block rmEpilogue) s fun s' => s'.mem = s.mem ∧
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  refine WP.mono (Spill.restore_ok .r13 rmSaved s₀.gpr s (by decide) (fun p hp' => ?_)
    (by rw [h.r13]; exact h.kept.1)) fun s' ⟨h₁, h₂, hm, _⟩ =>
    ⟨hm, Spill.calleeSaved_ok h₁ h₂ (by decide) h.rsp⟩
  have := VG.Proof.Scrypt.X86_64.RoMix.saved_offs hp'
  rw [h.r13, h.rd, h.wr, hp.rd, hp.wr]
  exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.scR s₀) (by simp) (VG.Proof.Scrypt.X86_64.RoMix.in_s s₀ (by omega))

/-! ## The whole function -/

theorem correct {c : Prog isa} (hS : VG.Proof.Scrypt.X86_64.RoMix.BlockMixSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) :
    WP isa (roMixWith c) s₀ fun s' =>
      gprPreserved s₀ s' ∧ Proof.Scrypt.roMixX86_64.post s₀ s' := by
  unfold roMixWith
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.prologue_ok hp) fun s₁ h₁ => ?_)
  refine VG.Proof.Scrypt.X86_64.RoMix.start_ok hp h₁ fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.loop2_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.mid_ok hp h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86_64.RoMix.loop3_ok hS hp h₄) fun s₅ h₅ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.restore_ok hp h₅) fun s' ⟨hm', hg'⟩ => ?_
  refine ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₅.frame.readW (r := VG.Proof.Scrypt.X86_64.RoMix.retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hp.ret_b
    · exact hp.ret_v
    · exact hp.ret_s
    · exact VG.Proof.Scrypt.X86_64.RoMix.ret_stk s₀
  · show bytesAt s'.mem (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = roMix (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)
    rw [hm', ← h₅.x, Nat.sub_self]
    rfl

end VG.Proof.Scrypt.X86_64.RoMix

/-!
# scryptROMix on x86-64: constant time, up to the indices `j`

As for scryptBlockMix (`BlockMixCT.lean`), we relate two runs (`RelCT`):
correctness determines our registers from the public arguments, so they
agree between the calls, where the taint analysis proves each block
constant time; the calls are constant time by scryptBlockMix's own proof.
In step 3, the address of `(V[j]'(by omega))` and the branches of the multiplication
depend on `j`, which the contract declares public: the two runs compute the
same `j`, since both compute their indices in order (`Inv3.js`) and agree on
the whole list.
-/

namespace VG.Proof.Scrypt.X86_64.RoMix

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Spec.Scrypt (bytesAt blockMix)
open VG.Proof.MdStream.X86_64 (wp_mov wp_addi wp_add wp_subi)

/-! ## What each run knows -/

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

section
variable {s₀ s₀' : State} (hq : VG.Proof.Scrypt.X86_64.RoMix.PubEq s₀ s₀')
include hq

theorem PubEq.rr : VG.Proof.Scrypt.X86_64.RoMix.rr s₀ = VG.Proof.Scrypt.X86_64.RoMix.rr s₀' := by simp only [RoMix.rr, hq.rsi]
theorem PubEq.NN : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ = VG.Proof.Scrypt.X86_64.RoMix.NN s₀' := by simp only [RoMix.NN, RoMix.vl, RoMix.rr, hq.rsi, hq.rcx]
theorem PubEq.vAt (i : Nat) : VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i := by
  simp only [RoMix.vAt, RoMix.vP, RoMix.rr, hq.rsi, hq.rdx]
theorem PubEq.tP : VG.Proof.Scrypt.X86_64.RoMix.tP s₀ = VG.Proof.Scrypt.X86_64.RoMix.tP s₀' := by simp only [RoMix.tP, RoMix.sc, hq.r8]

end

/-- The registers the loops keep, with `rbp = bp` and `r15 = q`. -/
structure KR (s₀ : State) (bp q : Addr) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀
  rbp : s.gpr .rbp = bp
  r12 : s.gpr .r12 = VG.Proof.Scrypt.X86_64.RoMix.vP s₀
  r13 : s.gpr .r13 = VG.Proof.Scrypt.X86_64.RoMix.sc s₀
  r14 : s.gpr .r14 = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  r15 : s.gpr .r15 = q

theorem KR.keep {s₀ : State} {bp q : Addr} {s s' : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hk : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) :
    VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hk _ (by simp [calleeSaved])).trans h.rsp,
    (hk _ (by simp [calleeSaved])).trans h.rbx, (hk _ (by simp [calleeSaved])).trans h.rbp,
    (hk _ (by simp [calleeSaved])).trans h.r12, (hk _ (by simp [calleeSaved])).trans h.r13,
    (hk _ (by simp [calleeSaved])).trans h.r14, (hk _ (by simp [calleeSaved])).trans h.r15⟩

/-- `KR` survives instructions that write none of its registers. -/
theorem KR.upd {s₀ : State} {bp q : Addr} {s s' : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hk : ∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) :
    VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' :=
  h.keep hrd hwr fun r hr => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := VG.Proof.Scrypt.X86_64.RoMix.cs_ne hr
    exact hk r h1 h2 h3 h4 h5 h6

theorem Inv2.kr {s₀ : State} {i : Nat} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ i s) :
    VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem Inv3.kr {s₀ : State} {i : Nat} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s) :
    VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - 1)) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s :=
  ⟨h.rd, h.wr, h.rsp, h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

/-- The registers `KR` fixes agree in two runs. -/
theorem KR.agree {s₀ s₀' : State} (hq : VG.Proof.Scrypt.X86_64.RoMix.PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) (h' : VG.Proof.Scrypt.X86_64.RoMix.KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, VG.Proof.Scrypt.X86_64.RoMix.bP, VG.Proof.Scrypt.X86_64.RoMix.bP, hq.rdi]
  · rw [h.rbp, h'.rbp, hbp]
  · rw [h.r12, h'.r12, VG.Proof.Scrypt.X86_64.RoMix.vP, VG.Proof.Scrypt.X86_64.RoMix.vP, hq.rdx]
  · rw [h.r13, h'.r13, VG.Proof.Scrypt.X86_64.RoMix.sc, VG.Proof.Scrypt.X86_64.RoMix.sc, hq.r8]
  · rw [h.r14, h'.r14, hq.rr]
  · rw [h.r15, h'.r15, hq']
  · rw [h.rsp, h'.rsp, hq.rsp]

/-- The arguments of a call of `vg_scrypt_blockmix` from `A` into `b`. -/
structure Args (s₀ : State) (A : Addr) (s : State) : Prop where
  rdi : s.gpr .rdi = A
  rsi : s.gpr .rsi = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  rcx : s.gpr .rcx = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
  rdx : s.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.bP s₀
  r8 : s.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.sc s₀

/-- A block that may be the source of such a call. -/
structure SrcOK (s₀ : State) (A : Addr) : Prop where
  b : Region.Disjoint ⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩
  w : Region.Disjoint ⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩ ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩
  stk : (VG.Proof.Scrypt.X86_64.RoMix.stkR s₀).Disjoint ⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩
  nw : A.toNat + 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ ≤ 2 ^ 64
  inr : InRegions (s₀.rd ++ s₀.wr) A (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)

theorem srcOK_v {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) : VG.Proof.Scrypt.X86_64.RoMix.SrcOK s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) :=
  ⟨(VG.Proof.Scrypt.X86_64.RoMix.vAt_b hp hi).sub_right VG.Proof.Scrypt.X86_64.RoMix.b_sub', (VG.Proof.Scrypt.X86_64.RoMix.vAt_s hp hi).sub_right VG.Proof.Scrypt.X86_64.RoMix.w_sub, (VG.Proof.Scrypt.X86_64.RoMix.vAt_stk hp hi).symm,
    VG.Proof.Scrypt.X86_64.RoMix.vAt_nw hp hi, Memory.InRegions.right (VG.Proof.Scrypt.X86_64.RoMix.vAt_in hp hi)⟩

theorem srcOK_t {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) : VG.Proof.Scrypt.X86_64.RoMix.SrcOK s₀ (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) :=
  ⟨VG.Proof.Scrypt.X86_64.RoMix.t_b hp, VG.Proof.Scrypt.X86_64.RoMix.t_w hp, hp.stk_s.sub_right (VG.Proof.Scrypt.X86_64.RoMix.t_sub hp), VG.Proof.Scrypt.X86_64.RoMix.t_nw hp, Memory.InRegions.right (VG.Proof.Scrypt.X86_64.RoMix.t_in hp)⟩

/-! ## The call -/

theorem call_pre {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {A : Addr} (hA : VG.Proof.Scrypt.X86_64.RoMix.SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) (ha : VG.Proof.Scrypt.X86_64.RoMix.Args s₀ A s) :
    Proof.Scrypt.blockMixX86_64.pre (s.callEntry.withRegions [⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩]
      [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩]) ∧
    Covers ([⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩] ++ [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩] s.wr := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  exact VG.Proof.Scrypt.X86_64.RoMix.bm_pre ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (VG.Proof.Scrypt.X86_64.RoMix.b_sub' (s₀ := s₀))).sub_right (VG.Proof.Scrypt.X86_64.RoMix.w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (VG.Proof.Scrypt.X86_64.RoMix.b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (VG.Proof.Scrypt.X86_64.RoMix.w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.b_in hp)
    (by rw [h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.w_in hp)

theorem call_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {A : Addr} (hA : VG.Proof.Scrypt.X86_64.RoMix.SrcOK s₀ A) {bp q : Addr} {s : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) (ha : VG.Proof.Scrypt.X86_64.RoMix.Args s₀ A s) :
    WP isa (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMix) s (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  exact VG.Proof.Scrypt.X86_64.RoMix.blockMixSpec s A (VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (VG.Proof.Scrypt.X86_64.RoMix.sc s₀) (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) ha.rdi ha.rsi ha.rdx ha.rcx ha.r8 hp.pos lt
    ((hp.b_s.sub_left (VG.Proof.Scrypt.X86_64.RoMix.b_sub' (s₀ := s₀))).sub_right (VG.Proof.Scrypt.X86_64.RoMix.w_sub (s₀ := s₀))) hA.b hA.w
    (by rw [h.rsp]; exact hA.stk) (by rw [h.rsp]; exact hp.stk_b.sub_right (VG.Proof.Scrypt.X86_64.RoMix.b_sub' (s₀ := s₀)))
    (by rw [h.rsp]; exact hp.stk_s.sub_right (VG.Proof.Scrypt.X86_64.RoMix.w_sub (s₀ := s₀))) hA.nw (by have := hp.b_nw; omega)
    (by have := hp.s_nw; omega) (by rw [h.rd, h.wr]; exact hA.inr) (by rw [h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.b_in hp)
    (by rw [h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.w_in hp) _ fun _ rd wr cs _ _ => h.keep rd wr cs

theorem call_rel {s₀ s₀' : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) (hp' : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀') (hq : VG.Proof.Scrypt.X86_64.RoMix.PubEq s₀ s₀') {A A' : Addr}
    (hA : VG.Proof.Scrypt.X86_64.RoMix.SrcOK s₀ A) (hA' : VG.Proof.Scrypt.X86_64.RoMix.SrcOK s₀' A') (hAA : A = A') {bp q bp' q' : Addr} :
    RelCT isa (fun s s' => (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀ A s) ∧ (VG.Proof.Scrypt.X86_64.RoMix.KR s₀' bp' q' s' ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀' A' s'))
      (.call "vg_scrypt_blockmix" Impl.Scrypt.X86_64.blockMix)
      fun s s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s ∧ VG.Proof.Scrypt.X86_64.RoMix.KR s₀' bp' q' s' := by
  subst hAA
  have eb : VG.Proof.Scrypt.X86_64.RoMix.bP s₀' = VG.Proof.Scrypt.X86_64.RoMix.bP s₀ := hq.rdi.symm
  have es : VG.Proof.Scrypt.X86_64.RoMix.sc s₀' = VG.Proof.Scrypt.X86_64.RoMix.sc s₀ := hq.r8.symm
  have er : VG.Proof.Scrypt.X86_64.RoMix.rr s₀' = VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := hq.rr.symm
  have call := RelCT.call (n := "vg_scrypt_blockmix") (P := fun s s' =>
      (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀ A s) ∧ (VG.Proof.Scrypt.X86_64.RoMix.KR s₀' bp' q' s' ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀' A s'))
    BlockMix.blockMix_correct BlockMix.blockMix_ct [⟨A, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩]
    [⟨VG.Proof.Scrypt.X86_64.RoMix.bP s₀, 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀⟩, ⟨VG.Proof.Scrypt.X86_64.RoMix.sc s₀, 128⟩] fun s s' ⟨⟨h, ha⟩, ⟨h', ha'⟩⟩ => by
      obtain ⟨p₁, c₁, w₁⟩ := VG.Proof.Scrypt.X86_64.RoMix.call_pre hp hA h ha
      obtain ⟨p₂, c₂, w₂⟩ := VG.Proof.Scrypt.X86_64.RoMix.call_pre hp' hA' h' ha'
      rw [eb, es, er] at p₂ c₂ w₂
      refine ⟨p₁, p₂, ?_, c₁, w₁, c₂, w₂, by rw [h.rsp, h'.rsp, hq.rsp]⟩
      simp only [Proof.Scrypt.blockMixX86_64, State.withRegions_gpr, State.callEntry_rsp,
        State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp), ha.rdi, ha.rsi, ha.rdx, ha.rcx, ha.r8,
        ha'.rdi, ha'.rsi, ha'.rdx, ha'.rcx, ha'.r8, eb, es, er, h.rsp, h'.rsp, hq.rsp]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩
  exact (call.wp fun s s' h => ⟨VG.Proof.Scrypt.X86_64.RoMix.call_wp hp hA h.1.1 h.1.2, VG.Proof.Scrypt.X86_64.RoMix.call_wp hp' hA' h.2.1 h.2.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

/-! ## What each piece does to the registers -/

/-- The registers `KR` fixes. -/
abbrev kRegs : List Reg := [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp]

theorem agree_K {s₀ s₀' : State} (hq : VG.Proof.Scrypt.X86_64.RoMix.PubEq s₀ s₀') {bp q bp' q' : Addr} {s s' : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) (h' : VG.Proof.Scrypt.X86_64.RoMix.KR s₀' bp' q' s') (hbp : bp = bp') (hq' : q = q') {extra : List Reg}
    (hx : ∀ r ∈ extra, s.gpr r = s'.gpr r) :
    X86_64.Taint.Agree (Taint.ofRegs (extra ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs)) s s' :=
  Taint.agree_ofRegs fun r hr => (List.mem_append.mp hr).elim (hx r) (KR.agree hq h h' hbp hq' r)

theorem a2_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {bp q : Addr} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
      .shift .shr .rcx 3]) s fun s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' ∧ s'.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀ ∧ s'.gpr .rsi = bp ∧
        s'.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ =>
    VG.Proof.Scrypt.X86_64.RoMix.wp_shr (by decide) (by decide) fun e ue _ => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · exact h.upd (by rw [ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [ue.wr, ud.wr, ub.wr, ua.wr])
      fun r _ h2 h3 h4 _ _ => by rw [ue.other _ h4, ud.other _ h4, ub.other _ h3, ua.other _ h2]
  · rw [ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.rbx]
  · rw [ue.other _ (by decide), ud.other _ (by decide), ub.gpr, ua.other _ (by decide), h.rbp]
  · rw [ue.gpr, ud.gpr, ub.other _ (by decide), ua.other _ (by decide), h.r14, VG.Proof.Scrypt.X86_64.RoMix.shr_ofNat _ lt]
    congr 1; omega

theorem copy_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) {q : Addr} {s : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) q s) (hdi : s.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (hsi : s.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) :
    WP isa copyLoop s (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) q) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  have e8 : 8 * (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := by omega
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.copyLoop_ok (src := VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (dst := VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (n := 16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
    (by have := hp.pos; omega) (by omega) hdi hsi hcx
    (fun k hk => by rw [h.rd, h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.b_word hp hk)
    (fun k hk => by rw [h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.v_word hp hi hk)
    (by rw [e8]; exact (VG.Proof.Scrypt.X86_64.RoMix.vAt_b hp hi).symm.sub_left VG.Proof.Scrypt.X86_64.RoMix.b_sub')) fun t ⟨rd, wr, g, _⟩ =>
    h.upd rd wr fun r h1 h2 h3 h4 _ _ => g r h1 h2 h3 h4

theorem tail_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {bp q A : Addr} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s)
    (hA : s.gpr .rdi = A) :
    WP isa (.block VG.Proof.Scrypt.X86_64.RoMix.bmTail) s fun s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀ A s' := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  refine wp_mov fun a ua _ _ => VG.Proof.Scrypt.X86_64.RoMix.wp_shr (by decide) (by decide) fun b ub _ =>
    wp_mov fun d ud _ _ => wp_mov fun e ue _ _ => wp_mov fun f uf _ _ => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [uf.rd, ue.rd, ud.rd, ub.rd, ua.rd]) (by rw [uf.wr, ue.wr, ud.wr, ub.wr, ua.wr])
      fun r _ _ h3 h4 h5 h6 => by
        rw [uf.other _ h6, ue.other _ h5, ud.other _ h4, ub.other _ h3, ua.other _ h3]
  have hsi : b.gpr .rsi = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
    rw [ub.gpr, ua.gpr, h.r14, VG.Proof.Scrypt.X86_64.RoMix.shr_ofNat _ lt]; exact congrArg (BitVec.ofNat _) (by omega)
  exact ⟨by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), hA],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.other _ (by decide), hsi],
    by rw [uf.other _ (by decide), ue.other _ (by decide), ud.gpr, hsi],
    by rw [uf.other _ (by decide), ue.gpr, ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.rbx],
    by rw [uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r13]⟩

theorem x2_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {bp q : Addr} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) :
    WP isa (.block (([.mov .rdi (.reg .rbp)] : List Instr) ++ VG.Proof.Scrypt.X86_64.RoMix.bmTail)) s fun s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀ bp s' :=
  wp_mov fun a ua _ _ => VG.Proof.Scrypt.X86_64.RoMix.tail_wp hp (h.upd ua.rd ua.wr fun r _ h2 _ _ _ _ => ua.other r h2)
    (by rw [ua.gpr, h.rbp])

theorem x3_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {bp q : Addr} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) :
    WP isa (.block (([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] : List Instr) ++ VG.Proof.Scrypt.X86_64.RoMix.bmTail)) s
      fun s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀ (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) s' :=
  wp_mov fun a ua _ _ => wp_addi fun b ub => VG.Proof.Scrypt.X86_64.RoMix.tail_wp hp
    (h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ h2 _ _ _ _ => by
      rw [ub.other r h2, ua.other r h2])
    (by rw [ub.gpr, ua.gpr, h.r13, VG.Proof.Scrypt.X86_64.RoMix.sx192])

/-! ## Step 2, in two runs -/

section
variable {s₀ s₀' : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) (hp' : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀') (hq : VG.Proof.Scrypt.X86_64.RoMix.PubEq s₀ s₀')
include hp hp' hq

theorem body2_rel {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ i s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' i s') (step2 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀))) ∧
        (VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀'))) := by
  have hi' : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀' := hq.NN ▸ hi
  have ev : VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i := hq.vAt i
  have e15 : BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i) = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i) := by rw [hq.NN]
  have a : RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ i s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' i s')
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rcx (.reg .r14),
        .shift .shr .rcx 3]) fun s s' =>
        (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s ∧ s.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀ ∧
          s.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i ∧ s.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) ∧
        (VG.Proof.Scrypt.X86_64.RoMix.KR s₀' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i)) s' ∧ s'.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀' ∧
          s'.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i ∧ s'.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1.kr h.2.kr ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.a2_wp hp h.1.kr, VG.Proof.Scrypt.X86_64.RoMix.a2_wp hp' h.2.kr⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have c : RelCT isa (fun s s' =>
        (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s ∧ s.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀ ∧
          s.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i ∧ s.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) ∧
        (VG.Proof.Scrypt.X86_64.RoMix.KR s₀' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i)) s' ∧ s'.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀' ∧
          s'.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i ∧ s'.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀')))
      copyLoop fun s s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s ∧
        VG.Proof.Scrypt.X86_64.RoMix.KR s₀' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i)) s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdi, .rsi, .rcx] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ ⟨⟨h, d, si, cx⟩, ⟨h', d', si', cx'⟩⟩ => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h h' ev e15 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [d, d', VG.Proof.Scrypt.X86_64.RoMix.bP, VG.Proof.Scrypt.X86_64.RoMix.bP, hq.rdi]
        · rw [si, si', ev]
        · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, d, si, cx⟩, ⟨h', d', si', cx'⟩⟩ =>
        ⟨VG.Proof.Scrypt.X86_64.RoMix.copy_wp hp hi h d si cx, VG.Proof.Scrypt.X86_64.RoMix.copy_wp hp' hi' h' d' si' cx'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have x : RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s ∧
        VG.Proof.Scrypt.X86_64.RoMix.KR s₀' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i)) s')
      (.block ([.mov .rdi (.reg .rbp)] ++ VG.Proof.Scrypt.X86_64.RoMix.bmTail)) fun s s' =>
        (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) s) ∧
        (VG.Proof.Scrypt.X86_64.RoMix.KR s₀' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i)) s' ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i) s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.x2_wp hp h.1, VG.Proof.Scrypt.X86_64.RoMix.x2_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := VG.Proof.Scrypt.X86_64.RoMix.call_rel hp hp' hq (VG.Proof.Scrypt.X86_64.RoMix.srcOK_v hp hi) (VG.Proof.Scrypt.X86_64.RoMix.srcOK_v hp' hi') ev
    (bp := VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (q := BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) (bp' := VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i)
    (q' := BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i))
  have e : RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i)) s ∧
        VG.Proof.Scrypt.X86_64.RoMix.KR s₀' (VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' i) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i)) s')
      (.block [.alu .add .rbp (.reg .r14), .alu .sub .r15 (.imm 1)]) fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1 h.2 ev e15 (by simp)) (by taint_decide)
  have body := a.seq (c.seq ((x.seq cl).seq e))
  rw [← VG.Proof.Scrypt.X86_64.RoMix.blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.step2_ok VG.Proof.Scrypt.X86_64.RoMix.blockMixSpec hp hi h.1, VG.Proof.Scrypt.X86_64.RoMix.step2_ok VG.Proof.Scrypt.X86_64.RoMix.blockMixSpec hp' hi' h.2⟩).mono
    (fun _ _ h => h) fun _ _ h => h.2

theorem loop2_rel :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ 0 s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' 0 s') (.loop (step2 Impl.Scrypt.X86_64.blockMix) .ne)
      fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' (VG.Proof.Scrypt.X86_64.RoMix.NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step2 Impl.Scrypt.X86_64.blockMix) (c := .ne)
    (Q := fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' (VG.Proof.Scrypt.X86_64.RoMix.NN s₀') s')
    (fun n s s' => ∃ i, n = VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i ∧ i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀ ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ i s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := VG.Proof.Scrypt.X86_64.RoMix.body2_rel hp hp' hq hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by simpa using ht'
        exact ⟨VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp, h.1, h.2⟩) fun _ _ h => h

end

/-! ## Step 3: what each piece does to the registers -/

theorem j_wp {s₀ : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {q : Addr} {s : State}
    (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - 1)) q s) {j : Nat} (hj : VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem = j) :
    WP isa (.block jBlock) s fun s' =>
      VG.Proof.Scrypt.X86_64.RoMix.KR s₀ (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - 1)) q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  have := hp.pos
  unfold jBlock
  refine Proof.MdStream.X86_64.wp_movm (a := VG.Proof.Scrypt.X86_64.RoMix.bP s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ - 64))
    (VG.Proof.Scrypt.X86_64.RoMix.ea_j hp s h.rbx h.r14)
    (by rw [h.rd, h.wr, hp.rd, hp.wr]
        exact Memory.InRegions.of_mem (R := VG.Proof.Scrypt.X86_64.RoMix.bR s₀) (by simp)
          (Memory.contains_off (by omega) (by omega)))
    fun a ua => VG.Proof.Scrypt.X86_64.RoMix.wp_and fun b ub => WP.block_nil ⟨?_, ?_⟩
  · exact h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r h1 _ _ _ _ _ => by
      rw [ub.other _ h1, ua.other _ h1]
  · rw [ub.gpr, ua.gpr, ua.other .rbp (by decide), h.rbp, VG.Proof.Scrypt.X86_64.RoMix.jOf_eq hp, hj]

theorem m1_wp {bp q : Addr} {s₀ : State} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) {j : Nat}
    (hax : s.gpr .rax = BitVec.ofNat 64 j) :
    WP isa (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) s fun s' =>
      VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) :=
  wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => WP.block_nil
    ⟨h.upd (by rw [ub.rd, ua.rd]) (by rw [ub.wr, ua.wr]) fun r _ _ _ h4 h5 _ => by
      rw [ub.other _ h4, ua.other _ h5],
    by rw [ub.other _ (by decide), ua.other _ (by decide), hax],
    by rw [ub.other _ (by decide), ua.gpr, h.r12], by rw [ub.gpr, ua.other _ (by decide), h.r14]⟩

theorem mul_wp {bp q : Addr} {s₀ : State} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) {j : Nat} (hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vP s₀)
    (hcx : s.gpr .rcx = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) :
    WP isa mulLoop s fun s' => VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' ∧ s'.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j :=
  WP.mono (VG.Proof.Scrypt.X86_64.RoMix.mulLoop_ok hj hax hdx hcx) fun _ ⟨rd, wr, _, g, dx⟩ =>
    ⟨h.upd rd wr fun r h1 _ _ h4 h5 _ => g r h1 h5 h4, by rw [dx, Nat.mul_comm]⟩

theorem m2_wp {bp q : Addr} {s₀ : State} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {j : Nat}
    (hdx : s.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j) :
    WP isa (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
      .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 3]) s fun s' =>
      VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s' ∧ s'.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀ ∧ s'.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j ∧ s'.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.tP s₀ ∧
        s'.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  refine wp_mov fun a ua _ _ => wp_mov fun b ub _ _ => wp_mov fun d ud _ _ => wp_addi fun e ue =>
    wp_mov fun f uf _ _ => VG.Proof.Scrypt.X86_64.RoMix.wp_shr (by decide) (by decide) fun g ug _ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h.upd (by rw [ug.rd, uf.rd, ue.rd, ud.rd, ub.rd, ua.rd])
      (by rw [ug.wr, uf.wr, ue.wr, ud.wr, ub.wr, ua.wr]) fun r _ h2 h3 h4 _ h6 => by
        rw [ug.other _ h4, uf.other _ h4, ue.other _ h6, ud.other _ h6, ub.other _ h3, ua.other _ h2]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.other _ (by decide), ua.gpr, h.rbx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), ub.gpr, ua.other _ (by decide), hdx]
  · rw [ug.other _ (by decide), uf.other _ (by decide), ue.gpr, ud.gpr, ub.other _ (by decide),
      ua.other _ (by decide), h.r13, VG.Proof.Scrypt.X86_64.RoMix.sx192]
  · rw [ug.gpr, uf.gpr, ue.other _ (by decide), ud.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), h.r14, VG.Proof.Scrypt.X86_64.RoMix.shr_ofNat _ lt]
    congr 1; omega

theorem xor_wp {bp q : Addr} {s₀ : State} {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q s) (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) {j : Nat}
    (hj : j < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (hdi : s.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (hsi : s.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j)
    (hr8 : s.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.tP s₀) (hcx : s.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) :
    WP isa xorLoop s (VG.Proof.Scrypt.X86_64.RoMix.KR s₀ bp q) := by
  have lt := VG.Proof.Scrypt.X86_64.RoMix.r_lt hp
  have e8 : 8 * (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀) = 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ := by omega
  refine WP.mono (VG.Proof.Scrypt.X86_64.RoMix.xorLoop_ok (x := VG.Proof.Scrypt.X86_64.RoMix.bP s₀) (y := VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j) (d := VG.Proof.Scrypt.X86_64.RoMix.tP s₀) (n := 16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)
    (by have := hp.pos; omega) (by omega) hdi hsi hr8 hcx
    (fun k hk => by rw [h.rd, h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.b_word hp hk)
    (fun k hk => by rw [h.rd, h.wr]; exact Memory.InRegions.right (VG.Proof.Scrypt.X86_64.RoMix.v_word hp hj hk))
    (fun k hk => by rw [h.wr]; exact VG.Proof.Scrypt.X86_64.RoMix.t_word hp hk)
    (by rw [e8]; exact VG.Proof.Scrypt.X86_64.RoMix.t_b hp) (by rw [e8]; exact (VG.Proof.Scrypt.X86_64.RoMix.vAt_s hp hj).symm.sub_left (VG.Proof.Scrypt.X86_64.RoMix.t_sub hp)))
    fun _ ⟨rd, wr, g, _⟩ => h.upd rd wr fun r h1 h2 h3 h4 _ h6 => g r h1 h2 h3 h6 h4

/-- The next index, from the ones still to come. -/
theorem drop_js {s₀ : State} {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) {s : State} (h : VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s) :
    ∃ rest, (Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀)).drop i = VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem :: rest := by
  have e : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i = VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - (i + 1) + 1 := by omega
  have hs := h.js
  rw [e, mixLoop_succ_snd] at hs
  exact ⟨_, hs.symm⟩

theorem RelCT.exists' {α : Type} {P : α → State → State → Prop} {c : Prog isa}
    {Q : State → State → Prop} (h : ∀ a, RelCT isa (P a) c Q) :
    RelCT isa (fun s s' => ∃ a, P a s s') c Q :=
  fun _ _ _ _ _ _ ⟨a, hp⟩ e e' => h a _ _ _ _ _ _ hp e e'

/-! ## Step 3, in two runs -/

section
variable {s₀ s₀' : State} (hp : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀) (hp' : VG.Proof.Scrypt.X86_64.RoMix.Pre s₀') (hq : VG.Proof.Scrypt.X86_64.RoMix.PubEq s₀ s₀')
include hp hp' hq

theorem body3_rel_j {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (j : Nat) (hj : j < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) :
    RelCT isa (fun s s' => (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem = j) ∧ (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' i s' ∧ VG.Proof.Scrypt.X86_64.RoMix.jOf s₀' s'.mem = j))
      (step3 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀))) ∧
        (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀'))) := by
  have hi' : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀' := hq.NN ▸ hi
  have hj' : j < VG.Proof.Scrypt.X86_64.RoMix.NN s₀' := hq.NN ▸ hj
  have vlt := VG.Proof.Scrypt.X86_64.RoMix.v_lt hp
  have hjl : j < 2 ^ 64 := by
    have : VG.Proof.Scrypt.X86_64.RoMix.NN s₀ ≤ 128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀ * VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := Nat.le_mul_of_pos_left _ (by have := hp.pos; omega)
    omega
  have e1 : BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - 1) = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - 1) := by rw [hq.NN]
  have e15 : BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i) = BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i) := by rw [hq.NN]
  -- The registers `KR` fixes, in step 3's iteration `i`.
  let K (t₀ t : State) : Prop := VG.Proof.Scrypt.X86_64.RoMix.KR t₀ (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN t₀ - 1)) (BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN t₀ - i)) t
  have jb : RelCT isa (fun s s' => (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem = j) ∧
        (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' i s' ∧ VG.Proof.Scrypt.X86_64.RoMix.jOf s₀' s'.mem = j)) (.block jBlock) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧ (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1.1.kr h.2.1.kr e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.j_wp hp h.1.1.kr h.1.2, VG.Proof.Scrypt.X86_64.RoMix.j_wp hp' h.2.1.kr h.2.2⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have m1 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j))
      (.block [.mov .rdx (.reg .r12), .mov .rcx (.reg .r14)]) fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2]) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.m1_wp h.1.1 h.1.2, VG.Proof.Scrypt.X86_64.RoMix.m1_wp h.2.1 h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have ml : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rax = BitVec.ofNat 64 j ∧ s.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rax = BitVec.ofNat 64 j ∧ s'.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀')))
      mulLoop fun s s' => (K s₀ s ∧ s.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' j) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rax, .rdx, .rcx] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h h' e1 e15 fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ax, ax']
        · rw [dx, dx', VG.Proof.Scrypt.X86_64.RoMix.vP, VG.Proof.Scrypt.X86_64.RoMix.vP, hq.rdx]
        · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, ax, dx, cx⟩, ⟨h', ax', dx', cx'⟩⟩ =>
        ⟨VG.Proof.Scrypt.X86_64.RoMix.mul_wp h hjl ax dx cx, VG.Proof.Scrypt.X86_64.RoMix.mul_wp h' hjl ax' dx' cx'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have m2 : RelCT isa (fun s s' => (K s₀ s ∧ s.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j) ∧ (K s₀' s' ∧ s'.gpr .rdx = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' j))
      (.block [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rdx), .mov .r8 (.reg .r13),
        .alu .add .r8 (.imm 192), .mov .rcx (.reg .r14), .shift .shr .rcx 3]) fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀ ∧ s.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j ∧ s.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀' ∧ s'.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' j ∧ s'.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀')) :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdx] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1.1 h.2.1 e1 e15 fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.1.2, h.2.2, hq.vAt])
      (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.m2_wp h.1.1 hp h.1.2, VG.Proof.Scrypt.X86_64.RoMix.m2_wp h.2.1 hp' h.2.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have xl : RelCT isa (fun s s' =>
        (K s₀ s ∧ s.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀ ∧ s.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀ j ∧ s.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.tP s₀ ∧
          s.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀)) ∧
        (K s₀' s' ∧ s'.gpr .rdi = VG.Proof.Scrypt.X86_64.RoMix.bP s₀' ∧ s'.gpr .rsi = VG.Proof.Scrypt.X86_64.RoMix.vAt s₀' j ∧ s'.gpr .r8 = VG.Proof.Scrypt.X86_64.RoMix.tP s₀' ∧
          s'.gpr .rcx = BitVec.ofNat 64 (16 * VG.Proof.Scrypt.X86_64.RoMix.rr s₀')))
      xorLoop fun s s' => K s₀ s ∧ K s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([.rdi, .rsi, .r8, .rcx] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h h' e1 e15
        fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [di, di', VG.Proof.Scrypt.X86_64.RoMix.bP, VG.Proof.Scrypt.X86_64.RoMix.bP, hq.rdi]
          · rw [si, si', hq.vAt]
          · rw [r8, r8', hq.tP]
          · rw [cx, cx', hq.rr]) (by taint_decide)).wp
      fun _ _ ⟨⟨h, di, si, r8, cx⟩, ⟨h', di', si', r8', cx'⟩⟩ =>
        ⟨VG.Proof.Scrypt.X86_64.RoMix.xor_wp h hp hj di si r8 cx, VG.Proof.Scrypt.X86_64.RoMix.xor_wp h' hp' hj' di' si' r8' cx'⟩).mono (fun _ _ h => h)
      fun _ _ h => h.2
  have x : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s')
      (.block ([.mov .rdi (.reg .r13), .alu .add .rdi (.imm 192)] ++ VG.Proof.Scrypt.X86_64.RoMix.bmTail)) fun s s' =>
        (K s₀ s ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀ (VG.Proof.Scrypt.X86_64.RoMix.tP s₀) s) ∧ (K s₀' s' ∧ VG.Proof.Scrypt.X86_64.RoMix.Args s₀' (VG.Proof.Scrypt.X86_64.RoMix.tP s₀') s') :=
    ((RelCT.taint (A := taint) (Taint.ofRegs ([] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.x3_wp hp h.1, VG.Proof.Scrypt.X86_64.RoMix.x3_wp hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cl := VG.Proof.Scrypt.X86_64.RoMix.call_rel hp hp' hq (VG.Proof.Scrypt.X86_64.RoMix.srcOK_t hp) (VG.Proof.Scrypt.X86_64.RoMix.srcOK_t hp') hq.tP
    (bp := BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - 1)) (q := BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i))
    (bp' := BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - 1)) (q' := BitVec.ofNat 64 (VG.Proof.Scrypt.X86_64.RoMix.NN s₀' - i))
  have e : RelCT isa (fun s s' => K s₀ s ∧ K s₀' s') (.block [.alu .sub .r15 (.imm 1)])
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs ([] ++ VG.Proof.Scrypt.X86_64.RoMix.kRegs))
      (fun _ _ h => VG.Proof.Scrypt.X86_64.RoMix.agree_K hq h.1 h.2 e1 e15 (by simp)) (by taint_decide)
  have body := jb.seq (m1.seq (ml.seq (m2.seq (xl.seq ((x.seq cl).seq e)))))
  rw [← VG.Proof.Scrypt.X86_64.RoMix.blockMixTo_eq] at body
  exact (body.wp fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.step3_ok VG.Proof.Scrypt.X86_64.RoMix.blockMixSpec hp hi h.1.1,
    VG.Proof.Scrypt.X86_64.RoMix.step3_ok VG.Proof.Scrypt.X86_64.RoMix.blockMixSpec hp' hi' h.2.1⟩).mono (fun _ _ h => h) fun _ _ h => h.2

variable (hL : Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86_64.RoMix.rr s₀) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) (VG.Proof.Scrypt.X86_64.RoMix.B s₀) =
  Spec.Scrypt.roMixIndices (VG.Proof.Scrypt.X86_64.RoMix.rr s₀') (VG.Proof.Scrypt.X86_64.RoMix.NN s₀') (VG.Proof.Scrypt.X86_64.RoMix.B s₀'))
include hL

theorem body3_rel {i : Nat} (hi : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀) :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' i s') (step3 Impl.Scrypt.X86_64.blockMix)
      fun s s' => (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (i + 1) s ∧ s.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀))) ∧
        (VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' (i + 1) s' ∧ s'.zf = some (decide (i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀'))) := by
  have hi' : i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀' := hq.NN ▸ hi
  refine (RelCT.exists' fun (j : Fin (VG.Proof.Scrypt.X86_64.RoMix.NN s₀)) => VG.Proof.Scrypt.X86_64.RoMix.body3_rel_j hp hp' hq hi j.1 j.2).mono
    (fun s s' ⟨h, h'⟩ => ?_) fun _ _ h => h
  obtain ⟨r, hr⟩ := VG.Proof.Scrypt.X86_64.RoMix.drop_js hi h
  obtain ⟨r', hr'⟩ := VG.Proof.Scrypt.X86_64.RoMix.drop_js hi' h'
  rw [← hL, hr] at hr'
  have e := (List.cons.inj hr').1
  exact ⟨⟨VG.Proof.Scrypt.X86_64.RoMix.jOf s₀ s.mem, VG.Proof.Scrypt.X86_64.RoMix.jOf_lt hp s.mem⟩, ⟨h, rfl⟩, ⟨h', e.symm⟩⟩

theorem loop3_rel :
    RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ 0 s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' 0 s') (.loop (step3 Impl.Scrypt.X86_64.blockMix) .ne)
      fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' (VG.Proof.Scrypt.X86_64.RoMix.NN s₀') s' := by
  have lp := RelCT.loop (M := isa) (body := step3 Impl.Scrypt.X86_64.blockMix) (c := .ne)
    (Q := fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' (VG.Proof.Scrypt.X86_64.RoMix.NN s₀') s')
    (fun n s s' => ∃ i, n = VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - i ∧ i < VG.Proof.Scrypt.X86_64.RoMix.NN s₀ ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ i s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' i s') (fun n => by
      intro s s' t t' u u' ⟨i, hn, hi, h, h'⟩ e e'
      obtain ⟨ht, ⟨j, z⟩, ⟨j', z'⟩⟩ := VG.Proof.Scrypt.X86_64.RoMix.body3_rel hp hp' hq hL hi _ _ _ _ _ _ ⟨h, h'⟩ e e'
      have ev : ∀ x : State, isa.eval .ne x = x.zf.map (!·) := fun _ => rfl
      beta_reduce
      rw [ev, ev, z, z', ← hq.NN]
      refine ⟨ht, rfl, fun hf => ?_, fun ht' => ?_⟩
      · have hl : i + 1 = VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by simpa using hf
        exact ⟨hl ▸ j, hl ▸ j'⟩
      · have hl : i + 1 ≠ VG.Proof.Scrypt.X86_64.RoMix.NN s₀ := by simpa using ht'
        exact ⟨VG.Proof.Scrypt.X86_64.RoMix.NN s₀ - (i + 1), by omega, i + 1, rfl, by omega, j, j'⟩) (VG.Proof.Scrypt.X86_64.RoMix.NN s₀)
  exact lp.mono (fun _ _ h => ⟨0, rfl, VG.Proof.Scrypt.X86_64.RoMix.NN_pos hp, h.1, h.2⟩) fun _ _ h => h

theorem roMix_rel :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') Impl.Scrypt.X86_64.roMix fun _ _ => True := by
  show RelCT isa _ (roMixWith Impl.Scrypt.X86_64.blockMix) _
  unfold roMixWith
  have pro : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block rmPrologue)
      fun s s' => VG.Proof.Scrypt.X86_64.RoMix.P1 s₀ s ∧ VG.Proof.Scrypt.X86_64.RoMix.P1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .rsp])
      (P := fun s s' => s = s₀ ∧ s' = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) (c := .block rmPrologue) (by taint_decide)).wp
      (F₁ := VG.Proof.Scrypt.X86_64.RoMix.P1 s₀) (F₂ := VG.Proof.Scrypt.X86_64.RoMix.P1 s₀') fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨VG.Proof.Scrypt.X86_64.RoMix.prologue_ok hp, VG.Proof.Scrypt.X86_64.RoMix.prologue_ok hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have nl : RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.P1 s₀ s ∧ VG.Proof.Scrypt.X86_64.RoMix.P1 s₀' s') nLoop fun s s' => VG.Proof.Scrypt.X86_64.RoMix.N1 s₀ s ∧ VG.Proof.Scrypt.X86_64.RoMix.N1 s₀' s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rax, .rdx, .rcx])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rax, h'.rax, hq.rr]
        · rw [h.rdx, h'.rdx]
        · rw [h.rcx, h'.rcx, RoMix.vl, RoMix.vl, hq.rcx]) (c := nLoop) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.nloop_ok hp h.1, VG.Proof.Scrypt.X86_64.RoMix.nloop_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have st : RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.N1 s₀ s ∧ VG.Proof.Scrypt.X86_64.RoMix.N1 s₀' s') (.block rmSetup)
      fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ 0 s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdx, .r12, .r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [h.rdx, h'.rdx, hq.NN]
        · rw [h.r12, h'.r12, VG.Proof.Scrypt.X86_64.RoMix.vP, VG.Proof.Scrypt.X86_64.RoMix.vP, hq.rdx]
        · rw [h.r13, h'.r13, VG.Proof.Scrypt.X86_64.RoMix.sc, VG.Proof.Scrypt.X86_64.RoMix.sc, hq.r8]) (c := .block rmSetup) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.setup2_ok hp h.1, VG.Proof.Scrypt.X86_64.RoMix.setup2_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have md : RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv2 s₀' (VG.Proof.Scrypt.X86_64.RoMix.NN s₀') s') (.block rmMid)
      fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ 0 s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' 0 s' :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.r13])
      (fun _ _ ⟨h, h'⟩ => Taint.agree_ofRegs fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [h.r13, h'.r13, VG.Proof.Scrypt.X86_64.RoMix.sc, VG.Proof.Scrypt.X86_64.RoMix.sc, hq.r8]) (c := .block rmMid) (by taint_decide)).wp
      fun _ _ h => ⟨VG.Proof.Scrypt.X86_64.RoMix.mid_ok hp h.1, VG.Proof.Scrypt.X86_64.RoMix.mid_ok hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have epi : RelCT isa (fun s s' => VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀ (VG.Proof.Scrypt.X86_64.RoMix.NN s₀) s ∧ VG.Proof.Scrypt.X86_64.RoMix.Inv3 s₀' (VG.Proof.Scrypt.X86_64.RoMix.NN s₀') s') (.block rmEpilogue)
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r13]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r13, h.2.r13, VG.Proof.Scrypt.X86_64.RoMix.sc, VG.Proof.Scrypt.X86_64.RoMix.sc, hq.r8]) (by taint_decide)
  exact pro.seq (nl.seq (st.seq ((VG.Proof.Scrypt.X86_64.RoMix.loop2_rel hp hp' hq).seq
    (md.seq ((VG.Proof.Scrypt.X86_64.RoMix.loop3_rel hp hp' hq hL).seq epi)))))

end

/-! ## Verified -/

theorem pubEq_of {s₁ s₂ : State} (h : Proof.Scrypt.roMixX86_64.pub s₁ s₂) : VG.Proof.Scrypt.X86_64.RoMix.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 1 | .rdx => 0x2000 | .rcx => 1 | .r8 => 0x3000 | .r9 => 3
    | .rsp => 0x5000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x2000, 128⟩, ⟨0x3000, 384⟩]

theorem roMix_correct (s : State) (hs : Proof.Scrypt.roMixX86_64.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86_64.roMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.roMixX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Scrypt.X86_64.RoMix.correct VG.Proof.Scrypt.X86_64.RoMix.blockMixSpec (VG.Proof.Scrypt.X86_64.RoMix.pre_of hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩

theorem roMix_ct : ConstantTime isa Proof.Scrypt.roMixX86_64.pre Proof.Scrypt.roMixX86_64.pub
    Impl.Scrypt.X86_64.roMix := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (VG.Proof.Scrypt.X86_64.RoMix.roMix_rel (VG.Proof.Scrypt.X86_64.RoMix.pre_of h₁) (VG.Proof.Scrypt.X86_64.RoMix.pre_of h₂) (VG.Proof.Scrypt.X86_64.RoMix.pubEq_of hpub) hpub.2.2.2.2.2.2.2
    _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

theorem roMix_verified :
    Verified X86_64.target Impl.Scrypt.X86_64.roMix (Spec.Scrypt.roMixContract X86_64.abi 16) :=
  Verified.of_correct VG.Proof.Scrypt.X86_64.RoMix.roMix_correct VG.Proof.Scrypt.X86_64.RoMix.roMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        sig_implies_post [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      pub := by
        sig_implies_pub [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Scrypt.roMixContract, Spec.Scrypt.roMixSig,
          Proof.Scrypt.roMixX86_64, X86_64.abi, X86_64.argRegs,
          Proof.Scrypt.X86_64.RoMix.satState]
          [Proof.Scrypt.X86_64.RoMix.satState] using Proof.Scrypt.X86_64.RoMix.satState }

end VG.Proof.Scrypt.X86_64.RoMix

end
