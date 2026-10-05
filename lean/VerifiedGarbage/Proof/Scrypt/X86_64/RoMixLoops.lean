import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Scrypt.X86_64.Common
import VerifiedGarbage.Impl.Scrypt.X86_64.RoMix
import VerifiedGarbage.Proof.Scrypt.X86_64.Lit

/-!
# scryptROMix on x86-64: the small loops

The word copy (`copyLoop`), the word exclusive-or (`xorLoop`), the
direct address multiplication (`mulLoop`) and the computation of `2 N` by
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


theorem ea_at0 (s : State) (b : Reg) : s.ea (at_ b 0) = s.gpr b := by
  rw [ea_at]; exact BitVec.add_zero _

theorem sx8 : (8 : BitVec 32).signExtend 64 = BitVec.ofNat 64 8 := by decide

theorem sx1 : (1 : BitVec 32).signExtend 64 = 1 := by decide

/-- A pointer advanced by one word. -/
theorem next_ptr (p : Addr) (k : Nat) :
    p + BitVec.ofNat 64 (8 * k) + (8 : BitVec 32).signExtend 64 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
  rw [sx8, add_ofNat, Nat.mul_succ]

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n - (k + 1)) := by
  rw [sx1, ofNat_pred (by omega), Nat.sub_sub]

theorem dec_zf {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - k) - (1 : BitVec 32).signExtend 64 == 0) = decide (k + 1 = n) := by
  rw [dec_count hk, ofNat_beq_zero (by omega)]
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
  mem : t.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * k))

theorem copy_step {s : State} {src dst : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) {k : Nat} (hk : k < n) {t : State}
    (h : CopyInv s src dst n k t) :
    WP isa (.block [.mov .rax (.mem (at_ .rdi 0)), .store (at_ .rsi 0) .rax,
      .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8), .alu .sub .rcx (.imm 1)]) t
      fun t' => CopyInv s src dst n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := src + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, h.rdi])
    (by rw [h.rd, h.wr]; exact hin k hk) fun t₁ u₁ => ?_
  refine wp_store (a := dst + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, u₁.other _ (by decide), h.rsi])
    (by rw [u₁.wr, h.wr]; exact hout k hk) fun t₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → t₂.gpr r = t.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr],
    fun r ha hdi hsi hcx => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other r hcx, u₄.other r hsi, u₃.other r hdi, g r ha, h.other r ha hdi hsi hcx]
  · rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g _ (by decide), h.rdi, next_ptr]
  · rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), g _ (by decide), h.rsi, next_ptr]
  · rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx, dec_count hk]
  · rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.gpr, u₁.mem, h.mem, Nat.mul_succ]
    exact copy_mem s.mem src dst k 8
      (hsep.sep (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)
        (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega)) (by omega)
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), g _ (by decide), h.rcx,
      dec_zf hk (by omega)]

/-- `copyLoop` copies `8 n` bytes from `rdi` to `rsi` (`rcx = n > 0` words). -/
theorem copyLoop_ok {s : State} {src dst : Addr} {n : Nat} (hn : 0 < n) (hlt : 8 * n < 2 ^ 64)
    (hdi : s.gpr .rdi = src) (hsi : s.gpr .rsi = dst) (hcx : s.gpr .rcx = BitVec.ofNat 64 n)
    (hin : ∀ k < n, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (dst + BitVec.ofNat 64 (8 * k)) 8)
    (hsep : Region.Disjoint ⟨src, 8 * n⟩ ⟨dst, 8 * n⟩) :
    WP isa copyLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rdi → r ≠ .rsi → r ≠ .rcx → s'.gpr r = s.gpr r) ∧
      s'.mem = writeBytes s.mem dst (bytesAt s.mem src (8 * n)) := by
  refine WP.mono (count_loop hn (CopyInv s src dst n)
    (fun k hk t h => copy_step hlt hin hout hsep hk h) ?_) fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ => rfl, by rw [ofNat_zero_add, hdi], by rw [ofNat_zero_add, hsi],
    by rw [hcx, Nat.sub_zero], by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

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
  mem : t.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * k)) (bytesAt s.mem y (8 * k)))

theorem xor_step {s : State} {x y d : Addr} {n : Nat} (hlt : 8 * n < 2 ^ 64)
    (hinx : ∀ k < n, InRegions (s.rd ++ s.wr) (x + BitVec.ofNat 64 (8 * k)) 8)
    (hiny : ∀ k < n, InRegions (s.rd ++ s.wr) (y + BitVec.ofNat 64 (8 * k)) 8)
    (hout : ∀ k < n, InRegions s.wr (d + BitVec.ofNat 64 (8 * k)) 8)
    (hdx : Region.Disjoint ⟨d, 8 * n⟩ ⟨x, 8 * n⟩) (hdy : Region.Disjoint ⟨d, 8 * n⟩ ⟨y, 8 * n⟩)
    {k : Nat} (hk : k < n) {t : State} (h : XorInv s x y d n k t) :
    WP isa (.block [.mov .rax (.mem (at_ .rdi 0)), .alu .xor .rax (.mem (at_ .rsi 0)),
      .store (at_ .r8 0) .rax, .alu .add .rdi (.imm 8), .alu .add .rsi (.imm 8),
      .alu .add .r8 (.imm 8), .alu .sub .rcx (.imm 1)]) t
      fun t' => XorInv s x y d n (k + 1) t' ∧ t'.zf = some (decide (k + 1 = n)) := by
  refine wp_movm (a := x + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, h.rdi])
    (by rw [h.rd, h.wr]; exact hinx k hk) fun t₁ u₁ => ?_
  refine wp_xorm (a := y + BitVec.ofNat 64 (8 * k)) (by rw [ea_at0, u₁.other _ (by decide), h.rsi])
    (by rw [u₁.rd, u₁.wr, h.rd, h.wr]; exact hiny k hk) fun t₂ u₂ => ?_
  refine wp_store (a := d + BitVec.ofNat 64 (8 * k))
    (by rw [ea_at0, u₂.other _ (by decide), u₁.other _ (by decide), h.r8])
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
      g _ (by decide), h.rdi, next_ptr]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      g _ (by decide), h.rsi, next_ptr]
  · rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.r8, next_ptr]
  · rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, dec_count hk]
  · rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, u₂.gpr, u₂.mem, u₁.gpr, u₁.mem, h.mem]
    exact xor_mem s.mem hk hlt hdx hdy
  · rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      g _ (by decide), h.rcx, dec_zf hk (by omega)]

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
      s'.mem = writeBytes s.mem d (xorBytes (bytesAt s.mem x (8 * n)) (bytesAt s.mem y (8 * n))) := by
  refine WP.mono (count_loop hn (XorInv s x y d n)
    (fun k hk t h => xor_step hlt hinx hiny hout hdx hdy hk h) ?_)
    fun t h => ⟨h.rd, h.wr, h.other, h.mem⟩
  exact ⟨rfl, rfl, fun _ _ _ _ _ _ => rfl, by rw [ofNat_zero_add, hdi], by rw [ofNat_zero_add, hsi],
    by rw [ofNat_zero_add, hr8], by rw [hcx, Nat.sub_zero],
    by rw [Nat.mul_zero]; exact (writeBytes_nil _ _).symm⟩

/-! ## `mulLoop` -/

/-- The low half of `mul` is multiplication modulo 2^64. -/
theorem mul_low (s : State) :
    (execMul .rcx s).gpr .rax = s.gpr .rax * s.gpr .rcx := by
  simp only [execMul, RegUpd.gpr_setReg,
    show Reg.rax ≠ Reg.rdx by decide, ↓reduceIte]
  exact (BitVec.ofNat_mul _ _).trans (by simp)

/-- Add `rax * rcx` to `rdx`; `rdi` is a temporary and memory is unchanged. -/
theorem mulLoop_ok {s : State} {j c : Nat} {a : Addr} (_hj : j < 2 ^ 64)
    (hax : s.gpr .rax = BitVec.ofNat 64 j) (hdx : s.gpr .rdx = a) (hcx : s.gpr .rcx = BitVec.ofNat 64 c) :
    WP isa mulLoop s fun s' => s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .rax → r ≠ .rdx → r ≠ .rcx → r ≠ .rdi → s'.gpr r = s.gpr r) ∧
      s'.gpr .rdx = a + BitVec.ofNat 64 (j * c) := by
  unfold mulLoop
  refine Proof.MdStream.X86_64.wp_mov fun t u _ _ => ?_
  refine Proof.MdStream.X86_64.WP.cons (s' := execMul .rcx t) rfl ?_
  refine Proof.MdStream.X86_64.wp_mov fun v uv _ _ => wp_add fun w uw => WP.block_nil ?_
  refine ⟨by rw [uw.rd, uv.rd]; exact u.rd,
    by rw [uw.wr, uv.wr]; exact u.wr,
    by rw [uw.mem, uv.mem]; exact u.mem, ?_, ?_⟩
  · intro r ha hd _ hi
    rw [uw.other _ hd, uv.other _ hd, Taint.execMul_gpr _ _ ha hd, u.other _ hi]
  · rw [uw.gpr, uv.gpr, Taint.execMul_gpr _ _ (by decide) (by decide), u.gpr,
      uv.other _ (by decide), mul_low, u.other _ (by decide), u.other _ (by decide),
      hdx, hax, hcx, ← BitVec.ofNat_mul]

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
    (h : NInv s r k t) :
    WP isa (.block [.alu .add .rax (.reg .rax), .alu .add .rdx (.reg .rdx),
      .alu .cmp .rax (.reg .rcx)]) t
      fun t' => NInv s r (k + 1) t' ∧ t'.zf = some (decide (k + 1 = e + 1)) := by
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
  refine WP.mono (count_loop (Nat.succ_pos e) (NInv s r)
    (fun k hk t h => n_step hr hlt hcx hk h) ?_) fun t h => ⟨h.rd, h.wr, h.mem, h.other, h.rdx⟩
  exact ⟨rfl, rfl, rfl, fun _ _ _ => rfl, by rw [hax, Nat.pow_zero, Nat.mul_one], by rw [hdx]; rfl⟩

end VG.Proof.Scrypt.X86_64.RoMix
