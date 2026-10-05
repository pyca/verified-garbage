import VerifiedGarbage.Proof.Scrypt.X86.Salsa
import VerifiedGarbage.Proof.Scrypt.Whole
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Impl.Scrypt.X86.BlockMix
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Scrypt.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86.Common`. -/
section

/-!
# scrypt on x86 (32-bit): common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are 32-bit pointers as addresses, `mul`, the
64-byte exclusive-or, and saving and restoring registers.
-/

namespace VG.Proof.Scrypt.X86

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil)
open VG.Proof.Sha256.X86.Stream (Upd Mupd wp_mov wp_movi wp_movm wp_store)
open VG.Proof.Scrypt.Memory (sub_off xorBytes_length bytesAt_length bytesAt_add
  bytesAt_writeBytes_sep)

/-! ## 32-bit pointers -/

theorem toNat_add32 {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).toNat = p.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
    Nat.mod_eq_of_lt h]

theorem add32 (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + BitVec.ofNat 32 j = p + BitVec.ofNat 32 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A register plus a small constant, as the code writes it. -/
theorem add32_lit (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + (OfNat.ofNat j : BitVec 32) =
      p + BitVec.ofNat 32 (o + (OfNat.ofNat j : Nat)) :=
  VG.Proof.Scrypt.X86.add32 p o j

theorem sub32 (p : BitVec 32) {o : Nat} (h : 64 ≤ o) :
    p + BitVec.ofNat 32 o - 64 = p + BitVec.ofNat 32 (o - 64) := by
  rw [show o = (o - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem ofNat_pred32 {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

/-- `[p + o]`, for a pointer `p` into a region that does not wrap around. -/
theorem addr_add {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).setWidth 64 = p.setWidth 64 + BitVec.ofNat 64 o := by
  have := addr_eq (x := p) (k := o) h
  exact this

/-- `[(p + o) + d]`, where nothing wraps around. -/
theorem addr_off {p : BitVec 32} {o d : Nat} (h : p.toNat + o + d < 2 ^ 32) :
    addr (p + BitVec.ofNat 32 o) d = p.setWidth 64 + BitVec.ofNat 64 o + BitVec.ofNat 64 d := by
  rw [Proof.Sha256.X86.Stream.addr_add_ofNat h, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem addr_zero (p : BitVec 32) : addr p 0 = p.setWidth 64 := by
  simp [addr]

/-- `and d, r` -/
theorem wp_and {is : List Instr} {s : State} {Q : State → Prop} {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d &&& s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.reg r) :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-! ## `mul` -/

/-- `mul r`: `eax` is the low half of `eax * r`; `edx` and the flags change too. -/
theorem wp_mul {is : List Instr} {s : State} {Q : State → Prop} {r : Reg}
    (k : ∀ s', s'.gpr .eax = BitVec.ofNat 32 ((s.gpr .eax).toNat * (s.gpr r).toNat) →
      (∀ q, q ≠ .eax → q ≠ .edx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.mul r :: is)) s Q :=
  Proof.Sha256.X86.Stream.WP.cons rfl (k _ (by simp [execMul, State.setReg])
    (fun q h₁ h₂ => by simp [execMul, State.setReg, State.setFlags, h₁, h₂]) rfl rfl rfl)

/-- `timesR m`: `eax = m r`, for the word `r` at `[esp + 8]`. -/
theorem timesR_ok {m : BitVec 32} {s : State} {r : BitVec 32}
    (hr : s.mem.readW (addr (s.gpr .esp) 8) 32 = r) (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 8) 4)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr .eax = BitVec.ofNat 32 (r.toNat * m.toNat) →
      (∀ q, q ≠ .eax → q ≠ .ecx → q ≠ .edx → s'.gpr q = s.gpr q) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block rest) s' Q) :
    WP isa (.block (timesR m ++ rest)) s Q := by
  refine wp_movm (a := addr (s.gpr .esp) 8) rfl hin fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  refine VG.Proof.Scrypt.X86.wp_mul fun s₃ e₃ o₃ m₃ rd₃ wr₃ => k s₃ ?_ (fun q h1 h2 h3 => ?_) (by rw [m₃, u₂.mem, u₁.mem])
    (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  · rw [e₃, u₂.other _ (by decide), u₁.gpr, hr, u₂.gpr]
  · rw [o₃ q h1 h3, u₂.other q h2, u₁.other q h1]

/-! ## Words of bytes -/

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m' a 4) (bytesAt m' b 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    Proof.Sha256.Stream.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁,
    Mem.extractLsb'_read _ _ h₁]

/-- One more word of `[d] ← [x] xor [y]`. -/
theorem xor_mem4 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 4 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 4 * n⟩ ⟨x, 4 * n⟩) (hdy : Region.Disjoint ⟨d, 4 * n⟩ ⟨y, 4 * n⟩) :
    (VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).writeW
      (d + BitVec.ofNat 64 (4 * k))
      ((VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (x + BitVec.ofNat 64 (4 * k)) 32 ^^^
        (VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k)))).readW
          (y + BitVec.ofNat 64 (4 * k)) 32) =
      VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (4 * (k + 1))) (bytesAt m y (4 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length = 4 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (4 * k), 4⟩
      ⟨d, (xorBytes (bytesAt m x (4 * k)) (bytesAt m y (4 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [VG.Proof.Scrypt.X86.writeW_xor32, bytesAt_writeBytes_sep _ _ sx (by omega),
    bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := VG.WriteBytes.writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (4 * k)) 4)
    (bytesAt m (y + BitVec.ofNat 64 (4 * k)) 4))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-! ## Blocks of bytes -/

theorem writeW_xor128 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 128 ^^^ m'.readW b 128) =
      VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m' a 16) (bytesAt m' b 16)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (128 : Nat) / 8 = 16 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    Proof.Sha256.Stream.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Mem.extractLsb'_read _ _ h₁,
    Mem.extractLsb'_read _ _ h₁]

/-- Sixteen more bytes of `[d] ← [x] xor [y]`. -/
theorem xor_mem16 (m : Mem) {d x y : Addr} {n k : Nat} (hk : k < n) (hlt : 16 * n < 2 ^ 64)
    (hdx : Region.Disjoint ⟨d, 16 * n⟩ ⟨x, 16 * n⟩) (hdy : Region.Disjoint ⟨d, 16 * n⟩ ⟨y, 16 * n⟩) :
    (VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).writeW
      (d + BitVec.ofNat 64 (16 * k))
      ((VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (x + BitVec.ofNat 64 (16 * k)) 128 ^^^
        (VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k)))).readW
          (y + BitVec.ofNat 64 (16 * k)) 128) =
      VG.WriteBytes.writeBytes m d (xorBytes (bytesAt m x (16 * (k + 1))) (bytesAt m y (16 * (k + 1)))) := by
  have hl : (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length = 16 * k := by
    rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
  have sx : Region.Disjoint ⟨x + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  have sy : Region.Disjoint ⟨y + BitVec.ofNat 64 (16 * k), 16⟩
      ⟨d, (xorBytes (bytesAt m x (16 * k)) (bytesAt m y (16 * k))).length⟩ := by
    rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
      (Region.sub_prefix (by omega))
  rw [VG.Proof.Scrypt.X86.writeW_xor128, bytesAt_writeBytes_sep _ _ sx (by omega),
    bytesAt_writeBytes_sep _ _ sy (by omega)]
  have e := VG.WriteBytes.writeBytes_append m d _ (xorBytes (bytesAt m (x + BitVec.ofNat 64 (16 * k)) 16)
    (bytesAt m (y + BitVec.ofNat 64 (16 * k)) 16))
    (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
  rw [hl] at e
  rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
    List.zipWith_append (by simp [bytesAt])]

/-! ## The 64-byte exclusive-or -/

/-- The first `n` sixteen-byte blocks of `[dst] ← [x] xor [src]`, for 64-byte
blocks at `d`, `x`, `y`, where `d` overlaps neither of the others. The code
uses `xmm0` and `xmm1`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .eax) (hx : xR ≠ .eax) (hs : sR ≠ .eax)
    {d x y : BitVec 32} (fd : d.toNat + 64 ≤ 2 ^ 32) (fx : x.toNat + 64 ≤ 2 ^ 32)
    (fy : y.toNat + 64 ≤ 2 ^ 32)
    (hdx : Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨x.setWidth 64, 64⟩)
    (hdy : Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨y.setWidth 64, 64⟩) :
    ∀ n ≤ 4, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 4, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ k < 4, InRegions (s.rd ++ s.wr) (y.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ k < 4, InRegions s.wr (d.setWidth 64 + BitVec.ofNat 64 (16 * k)) 16) →
    (∀ s', (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (d.setWidth 64)
        (xorBytes (bytesAt s.mem (x.setWidth 64) (16 * n)) (bytesAt s.mem (y.setWidth 64) (16 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ => rfl) rfl rfl (by simp [bytesAt, xorBytes, VG.WriteBytes.writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ldq (a := x.setWidth 64 + BitVec.ofNat 64 (16 * n))
      (by rw [ea_at, g₁ _ hx, gx]; exact addr_eq (by omega)) (by rw [rd₁, wr₁]; exact hinx n (by omega))
      fun s₂ R₂ m₂ x₂ _ => ?_
    refine wp_ldq (a := y.setWidth 64 + BitVec.ofNat 64 (16 * n))
      (by rw [ea_at, R₂.gpr, g₁ _ hs, gy]; exact addr_eq (by omega))
      (by rw [R₂.rd, R₂.wr, rd₁, wr₁]; exact hiny n (by omega)) fun s₃ R₃ m₃ x₃ o₃ => ?_
    refine wp_xbin fun s₄ R₄ m₄ x₄ _ => ?_
    refine wp_stq (a := d.setWidth 64 + BitVec.ofNat 64 (16 * n))
      (by rw [ea_at, R₄.gpr, R₃.gpr, R₂.gpr, g₁ _ hd, gd]; exact addr_eq (by omega))
      (by rw [R₄.wr, R₃.wr, R₂.wr, wr₁]; exact hout n (by omega))
      fun s₅ R₅ m₅ _ => k s₅ (fun r h => by rw [R₅.gpr, R₄.gpr, R₃.gpr, R₂.gpr, g₁ r h])
        (by rw [R₅.rd, R₄.rd, R₃.rd, R₂.rd, rd₁]) (by rw [R₅.wr, R₄.wr, R₃.wr, R₂.wr, wr₁]) ?_
    rw [m₅, x₄, o₃ .xmm0 (by decide), x₂, x₃, m₄, m₃, m₂, m₁]
    exact VG.Proof.Scrypt.X86.xor_mem16 s.mem (n := 4) (by omega) (by omega) hdx hdy

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
  have he : isa.eval .ne s' = some (!decide (k + 1 = n)) := by
    show s'.zf.map (!·) = _; rw [hz]; rfl
  by_cases hl : k + 1 = n
  · exact .inl ⟨by rw [he]; simp [hl], hl ▸ hi'⟩
  · exact .inr ⟨by rw [he]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-- The count after one more iteration of `n`. -/
theorem dec_count {n k : Nat} (hk : k < n) :
    BitVec.ofNat 32 (n - k) - 1 = BitVec.ofNat 32 (n - (k + 1)) := by
  rw [VG.Proof.Scrypt.X86.ofNat_pred32 (by omega), Nat.sub_sub]

theorem dec_z {n k : Nat} (hk : k < n) (hn : n < 2 ^ 32) :
    (BitVec.ofNat 32 (n - k) - 1 == 0) = decide (k + 1 = n) := by
  rw [VG.Proof.Scrypt.X86.dec_count hk, Proof.Sha256.X86.Stream.ofNat_beq_zero (by omega)]
  exact decide_eq_decide.mpr (by omega)

end VG.Proof.Scrypt.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86.BlockMix`. -/
section

/-!
# scryptBlockMix on x86 (32-bit): the loop

As on 32-bit ARM (`Proof/Scrypt/Arm/BlockMixVerified.lean`), the calls of
`vg_salsa20_8` are used through `SalsaSpec`, what its proof says about a call in
a frame of its arguments; the proof of this file holds for any code meeting it.
Pointers are read from the arguments on the stack, which nothing writes; the
calls use the 12 bytes below `esp` (`stkR`), which the memory frames include, as
on x86-64 (`Proof/Scrypt/X86_64/BlockMixCT.lean`).
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_add wp_addi wp_cmp addr_toNat)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat contains_off sub_off disj_off
  InRegions.of_mem frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c`, in a frame of its arguments pushed from `eax` and `dR`,
replaces the 64 bytes at `dR` by their Salsa20/8 Core, with the 64 bytes at
`eax` as working space, using the 12 bytes below `esp`. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (dR : Reg) (d sc : BitVec 32), dR ≠ .esp → s.gpr dR = d → s.gpr .eax = sc →
    d.toNat + 64 ≤ 2 ^ 32 → sc.toNat + 64 ≤ 2 ^ 32 →
    Region.Disjoint ⟨d.setWidth 64, 64⟩ ⟨sc.setWidth 64, 64⟩ → 12 ≤ (s.gpr .esp).toNat →
    (below (s.gpr .esp) 12).Disjoint ⟨d.setWidth 64, 64⟩ →
    (below (s.gpr .esp) 12).Disjoint ⟨sc.setWidth 64, 64⟩ →
    InRegions s.wr (d.setWidth 64) 64 → InRegions s.wr (sc.setWidth 64) 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
        Frame [⟨d.setWidth 64, 64⟩, ⟨sc.setWidth 64, 64⟩, below (s.gpr .esp) 12] s.mem s'.mem →
        bytesAt s'.mem (d.setWidth 64) 64 = salsa (bytesAt s.mem (d.setWidth 64) 64) → Q s') →
    WP isa (.frame (.push [.eax, dR]) (.call "vg_salsa20_8" c) (.pop .eax 2)) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev bP : BitVec 32 := arg s₀ 0
abbrev rr : Nat := (arg s₀ 1).toNat
abbrev yP : BitVec 32 := arg s₀ 2
abbrev sc : BitVec 32 := arg s₀ 4
abbrev bA : Addr := (VG.Proof.Scrypt.X86.BlockMix.bP s₀).setWidth 64
abbrev yA : Addr := (VG.Proof.Scrypt.X86.BlockMix.yP s₀).setWidth 64
abbrev scA : Addr := (VG.Proof.Scrypt.X86.BlockMix.sc s₀).setWidth 64
abbrev bR : Region := ⟨VG.Proof.Scrypt.X86.BlockMix.bA s₀, VG.Proof.Scrypt.X86.BlockMix.rr s₀ * 128⟩
abbrev yR : Region := ⟨VG.Proof.Scrypt.X86.BlockMix.yA s₀, VG.Proof.Scrypt.X86.BlockMix.rr s₀ * 128⟩
abbrev scR : Region := ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 128⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64, 4⟩
/-- The stack the calls use. -/
abbrev stkR : Region := below (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 12
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀) (128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 (64 * (VG.Proof.Scrypt.X86.BlockMix.rr s₀ + i))
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ - 64)
  | k + 1 => VG.Proof.Scrypt.X86.BlockMix.yO s₀ k
/-- `xP`, as the 32-bit pointer in `ebp`. -/
def xP32 : Nat → BitVec 32
  | 0 => VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 (128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ - 64)
  | k + 1 => VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 (64 * (VG.Proof.Scrypt.X86.BlockMix.rr s₀ + k))

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` are saved in the scratch space. -/
abbrev Saved (m : Mem) : Prop := Spill.Saved m (VG.Proof.Scrypt.X86.BlockMix.scA s₀ + BitVec.ofNat 64 ·) s₀.gpr bmSaved

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Scrypt.X86.BlockMix.bR s₀, VG.Proof.Scrypt.X86.BlockMix.argR s₀]
  wr : s₀.wr = [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀]
  y_s : (VG.Proof.Scrypt.X86.BlockMix.yR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.scR s₀)
  b_y : (VG.Proof.Scrypt.X86.BlockMix.bR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.yR s₀)
  b_s : (VG.Proof.Scrypt.X86.BlockMix.bR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.scR s₀)
  a_y : (VG.Proof.Scrypt.X86.BlockMix.argR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.yR s₀)
  a_s : (VG.Proof.Scrypt.X86.BlockMix.argR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.scR s₀)
  ret_y : (VG.Proof.Scrypt.X86.BlockMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.yR s₀)
  ret_s : (VG.Proof.Scrypt.X86.BlockMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.scR s₀)
  stk_b : (VG.Proof.Scrypt.X86.BlockMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.bR s₀)
  stk_y : (VG.Proof.Scrypt.X86.BlockMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.yR s₀)
  stk_s : (VG.Proof.Scrypt.X86.BlockMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.scR s₀)
  b_nw : (VG.Proof.Scrypt.X86.BlockMix.bP s₀).toNat + VG.Proof.Scrypt.X86.BlockMix.rr s₀ * 128 ≤ 2 ^ 32
  y_nw : (VG.Proof.Scrypt.X86.BlockMix.yP s₀).toNat + VG.Proof.Scrypt.X86.BlockMix.rr s₀ * 128 ≤ 2 ^ 32
  s_nw : (VG.Proof.Scrypt.X86.BlockMix.sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_lo : 12 ≤ (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).toNat
  sp_fit : (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).toNat + 24 ≤ 2 ^ 32
  r3 : arg s₀ 3 = arg s₀ 1
  pos : 0 < VG.Proof.Scrypt.X86.BlockMix.rr s₀

/-- The 12 bytes of stack below `E`, as the contracts write them. -/
theorem stk_eq {E : BitVec 32} (h : 12 ≤ E.toNat) : below E 12 = ⟨E.setWidth 64 - 12, 12⟩ := by
  simp only [below]; rw [Taint.sub_setWidth h]; rfl

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixX86.pre s₀) : VG.Proof.Scrypt.X86.BlockMix.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  have e := VG.Proof.Scrypt.X86.BlockMix.stk_eq h16
  simp only [h18] at h2 h3 h4 h6 h8 h11 h14
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by rw [VG.Proof.Scrypt.X86.BlockMix.stkR, e]; exact h10, by rw [VG.Proof.Scrypt.X86.BlockMix.stkR, e]; exact h11,
    by rw [VG.Proof.Scrypt.X86.BlockMix.stkR, e]; exact h12, h13, h14, h15, h16, h17, h18, h19⟩

section
variable {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ < 2 ^ 32 := by
  by_contra hc
  have hy : VG.Proof.Scrypt.X86.BlockMix.yA s₀ = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_toNat]; show _ = 0; have := hp.y_nw; omega
  have hs : (VG.Proof.Scrypt.X86.BlockMix.scA s₀).toNat < 2 ^ 32 := by rw [addr_toNat]; exact (VG.Proof.Scrypt.X86.BlockMix.sc s₀).isLt
  refine hp.y_s (VG.Proof.Scrypt.X86.BlockMix.scA s₀) ?_ ?_
  · show (VG.Proof.Scrypt.X86.BlockMix.scA s₀ - VG.Proof.Scrypt.X86.BlockMix.yA s₀).toNat + 1 ≤ VG.Proof.Scrypt.X86.BlockMix.rr s₀ * 128
    rw [hy, show (0 : Addr) = 0#64 from rfl, BitVec.sub_zero]; omega
  · show (VG.Proof.Scrypt.X86.BlockMix.scA s₀ - VG.Proof.Scrypt.X86.BlockMix.scA s₀).toNat + 1 ≤ 128
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega

theorem in_y {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.yR s₀).Contains (VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := VG.Proof.Scrypt.X86.BlockMix.r_lt hp; omega)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.bR s₀).Contains (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := VG.Proof.Scrypt.X86.BlockMix.r_lt hp; omega)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := VG.Proof.Scrypt.X86.BlockMix.r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) : Region.Sub ⟨VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.X86.BlockMix.yR s₀) :=
  sub_off (by omega) (by have := VG.Proof.Scrypt.X86.BlockMix.r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) : Region.Sub ⟨VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.X86.BlockMix.bR s₀) :=
  sub_off (by omega) (by have := VG.Proof.Scrypt.X86.BlockMix.r_lt hp; omega)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) (h₂ : o₂ + n₂ ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    Region.Disjoint ⟨VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (VG.Proof.Scrypt.X86.BlockMix.y_sub hp h₁)).sub_right (VG.Proof.Scrypt.X86.BlockMix.b_sub hp h₂)

/-- A pointer into `y`, as an address. -/
theorem y_addr {o : Nat} (h : o < 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o :=
  VG.Proof.Scrypt.X86.addr_add (by have := hp.y_nw; omega)

theorem b_addr {o : Nat} (h : o < 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 o :=
  VG.Proof.Scrypt.X86.addr_add (by have := hp.b_nw; omega)

theorem y_fit {o : Nat} (h : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) : (VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.y_nw
  rw [VG.Proof.Scrypt.X86.toNat_add32 (by omega)]; omega

theorem b_fit {o : Nat} (h : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) : (VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.b_nw
  rw [VG.Proof.Scrypt.X86.toNat_add32 (by omega)]; omega

/-- The argument words are in the arguments' region. -/
theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    Region.Sub ⟨addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) d, 4⟩ (VG.Proof.Scrypt.X86.BlockMix.argR s₀) := by
  have := hp.sp_fit
  intro a ha
  simp only [Region.Contains, argAddr] at ha ⊢
  rw [addr_eq (by omega)] at ha
  rw [show (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 4 from rfl,
    addr_eq (by omega)]
  generalize (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) d) 4 := by
  have hs := hp.sp_fit
  refine ⟨VG.Proof.Scrypt.X86.BlockMix.argR s₀, by simp [hp.rd], ?_⟩
  show (addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) d - addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 4).toNat + 4 ≤ 20
  rw [addr_eq (by omega), addr_eq (by omega),
    show (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d - ((VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 4) =
      BitVec.ofNat 64 (d - 4) by rw [show d = (d - 4) + 4 by omega, BitVec.ofNat_add]; bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem stk_arg : (VG.Proof.Scrypt.X86.BlockMix.stkR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.argR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains, argAddr] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₁
  rw [show (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀ + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 4 from rfl,
    addr_eq (by omega)] at h₂
  have hE : ((VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64).toNat = (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).toNat := addr_toNat _
  generalize (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64 = b at *
  bv_omega

theorem ret_stk : (VG.Proof.Scrypt.X86.BlockMix.retR s₀).Disjoint (VG.Proof.Scrypt.X86.BlockMix.stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rw [Taint.sub_setWidth (by omega)] at h₂
  have hE : ((VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64).toNat = (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).toNat := addr_toNat _
  generalize (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀).setWidth 64 = b at *
  bv_omega

/-- The arguments are kept by anything that writes only `y`, `scratch` and the
stack below `esp`. -/
theorem arg_keep {m : Mem} (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem m) {d : Nat} (hd₁ : 4 ≤ d)
    (hd : d + 4 ≤ 24) : m.readW (addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.a_y.sub_left (VG.Proof.Scrypt.X86.BlockMix.arg_sub hp hd₁ hd)
  · exact hp.a_s.sub_left (VG.Proof.Scrypt.X86.BlockMix.arg_sub hp hd₁ hd)
  · exact (VG.Proof.Scrypt.X86.BlockMix.stk_arg hp).symm.sub_left (VG.Proof.Scrypt.X86.BlockMix.arg_sub hp hd₁ hd)

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (VG.Proof.Scrypt.X86.BlockMix.scR s₀).Contains (VG.Proof.Scrypt.X86.BlockMix.scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀ + BitVec.ofNat 64 o, n⟩ (VG.Proof.Scrypt.X86.BlockMix.scR s₀) :=
  sub_off h (by omega)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ VG.Proof.Scrypt.X86.BlockMix.rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀
  ebx : s.gpr .ebx = VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 (128 * k)
  esi : s.gpr .esi = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 (64 * k)
  edi : s.gpr .edi = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 (64 * (VG.Proof.Scrypt.X86.BlockMix.rr s₀ + k))
  ebp : s.gpr .ebp = VG.Proof.Scrypt.X86.BlockMix.xP32 s₀ k
  frame : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Scrypt.X86.BlockMix.Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i) ∧
    bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i + 1)
  x : bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.xP s₀ k) 64 = xBefore (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y`, `scratch` and the stack. -/
theorem b_frame {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    bytesAt m (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := VG.Proof.Scrypt.X86.BlockMix.r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.b_y.sub_left (VG.Proof.Scrypt.X86.BlockMix.b_sub hp ho)
  · exact hp.b_s.sub_left (VG.Proof.Scrypt.X86.BlockMix.b_sub hp ho)
  · exact hp.stk_b.symm.sub_left (VG.Proof.Scrypt.X86.BlockMix.b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    blk (VG.Proof.Scrypt.X86.BlockMix.B s₀) i = bytesAt s₀.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o, 64⟩

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .eax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem salsaAt_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {dR : Reg}
    (hdR : dR ≠ .esp) (hdR' : dR ≠ .eax) {s : State} {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀)
    (hd : s.gpr dR = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 o) (hesp : s.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s.mem) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  have lt := VG.Proof.Scrypt.X86.BlockMix.r_lt hp
  unfold salsaAt
  refine WP.seq (wp_movm (a := addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 20) (by rw [ea_at, hesp])
    (by rw [hrd, hwr]; exact VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega)) fun s₁ u₁ => WP.block_nil ?_)
  have e₁ : s₁.gpr .eax = VG.Proof.Scrypt.X86.BlockMix.sc s₀ := by rw [u₁.gpr, VG.Proof.Scrypt.X86.BlockMix.arg_keep hp hf (by omega) (by omega)]; rfl
  have e₃ : ∀ r ∈ calleeSaved, s₁.gpr r = s.gpr r := fun r hr => u₁.other _ (VG.Proof.Scrypt.X86.BlockMix.calleeSaved_ne hr)
  have e₄ : s₁.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀ := by rw [e₃ _ (by simp [calleeSaved]), hesp]
  have ea : (VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o := VG.Proof.Scrypt.X86.BlockMix.y_addr hp (by omega)
  have hsub : Region.Sub (VG.Proof.Scrypt.X86.BlockMix.slot s₀ o) (VG.Proof.Scrypt.X86.BlockMix.yR s₀) := VG.Proof.Scrypt.X86.BlockMix.y_sub hp ho
  have hsub' : Region.Sub ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩ (VG.Proof.Scrypt.X86.BlockMix.scR s₀) := Region.sub_prefix (by omega)
  have hsc : (VG.Proof.Scrypt.X86.BlockMix.scR s₀).Contains (VG.Proof.Scrypt.X86.BlockMix.scA s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine hS s₁ dR _ _ hdR (by rw [u₁.other _ hdR', hd]) e₁ (VG.Proof.Scrypt.X86.BlockMix.y_fit hp ho) (by have := hp.s_nw; omega)
    (by rw [ea]; exact hp.y_s.sub_left hsub |>.sub_right hsub') (by rw [e₄]; exact hp.sp_lo)
    (by rw [e₄, ea]; exact hp.stk_y.sub_right hsub) (by rw [e₄]; exact hp.stk_s.sub_right hsub')
    (by rw [u₁.wr, hwr, hp.wr, ea]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_y hp ho))
    (by rw [u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := VG.Proof.Scrypt.X86.BlockMix.scR s₀) (by simp) hsc)
    _ fun s' hrd' hwr' hcs hf' hb => hQ s' (by rw [hrd', u₁.rd]) (by rw [hwr', u₁.wr])
      (fun r hr => by rw [hcs r hr, e₃ r hr]) (by rw [u₁.mem, ea, e₄] at hf'; exact hf')
      (by rw [ea] at hb; rw [hb, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.slot s₀ o).Disjoint ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩ :=
  (hp.y_s.sub_left (VG.Proof.Scrypt.X86.BlockMix.y_sub hp ho)).sub_right (Region.sub_prefix (by omega))

theorem slot_stk {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.slot s₀ o).Disjoint (VG.Proof.Scrypt.X86.BlockMix.stkR s₀) :=
  (hp.stk_y.sub_right (VG.Proof.Scrypt.X86.BlockMix.y_sub hp ho)).symm

/-- Where `X` is, as an address. -/
theorem xP_addr {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.xP32 s₀ k).setWidth 64 = VG.Proof.Scrypt.X86.BlockMix.xP s₀ k := by
  cases k with
  | zero => exact VG.Proof.Scrypt.X86.BlockMix.b_addr hp (by have := hp.pos; omega)
  | succ j => exact VG.Proof.Scrypt.X86.BlockMix.y_addr hp (by omega)

theorem xP_fit {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    (VG.Proof.Scrypt.X86.BlockMix.xP32 s₀ k).toNat + 64 ≤ 2 ^ 32 := by
  cases k with
  | zero => exact VG.Proof.Scrypt.X86.BlockMix.b_fit hp (by have := hp.pos; omega)
  | succ j => exact VG.Proof.Scrypt.X86.BlockMix.y_fit hp (by omega)

theorem xP_in {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) {s : State}
    (hrd : s.rd = [VG.Proof.Scrypt.X86.BlockMix.bR s₀, VG.Proof.Scrypt.X86.BlockMix.argR s₀]) (hwr : s.wr = [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀]) :
    ∀ i < 4, InRegions (s.rd ++ s.wr) (VG.Proof.Scrypt.X86.BlockMix.xP s₀ k + BitVec.ofNat 64 (16 * i)) 16 := by
  intro i hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [VG.Proof.Scrypt.X86.BlockMix.xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_b hp (by have := hp.pos; omega))
  | succ j =>
    simp only [VG.Proof.Scrypt.X86.BlockMix.xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_y hp (by omega))

theorem xP_disj {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) :
    Region.Disjoint (VG.Proof.Scrypt.X86.BlockMix.slot s₀ (64 * k)) ⟨VG.Proof.Scrypt.X86.BlockMix.xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact VG.Proof.Scrypt.X86.BlockMix.yb_disj hp (by omega) (by have := hp.pos; omega)
  | succ j => exact VG.Proof.Scrypt.X86.BlockMix.y_disj hp (by omega) (by omega) (by omega)

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] m m') (h : VG.Proof.Scrypt.X86.BlockMix.Saved s₀ m) : VG.Proof.Scrypt.X86.BlockMix.Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have hp4 : p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl <;> simp
  have hsub : Region.Sub ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (VG.Proof.Scrypt.X86.BlockMix.scR s₀) := VG.Proof.Scrypt.X86.BlockMix.s_sub s₀ (by omega)
  refine hf.readW (r := ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (hp.y_s.sub_left (VG.Proof.Scrypt.X86.BlockMix.y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (VG.Proof.Scrypt.X86.BlockMix.scA s₀) (o₁ := p.2) (n₁ := 4) (o₂ := 0) (n₂ := 64) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    simpa using this
  · exact (hp.stk_s.sub_right hsub).symm

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀)
    (ho' : o' + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] m m') :
    bytesAt m' (VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact VG.Proof.Scrypt.X86.BlockMix.y_disj hp hd ho' ho
  · exact VG.Proof.Scrypt.X86.BlockMix.slot_s hp ho'
  · exact VG.Proof.Scrypt.X86.BlockMix.slot_stk hp ho'

theorem frame_big {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) {m m' : Mem}
    (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] m m') : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.Scrypt.X86.BlockMix.yR s₀, List.mem_cons_self, VG.Proof.Scrypt.X86.BlockMix.y_sub hp ho⟩
    · exact ⟨VG.Proof.Scrypt.X86.BlockMix.scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩
    · exact ⟨VG.Proof.Scrypt.X86.BlockMix.stkR s₀, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        fun _ h => h⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .eax) (hd' : dR ≠ .esp) (hx : xR ≠ .eax) (hs : sR ≠ .eax) {o : Nat}
    (ho : o + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) {x : BitVec 32} (fx : x.toNat + 64 ≤ 2 ^ 32) {ob : Nat}
    (hob : ob + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hesp : s.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s.mem)
    (gd : s.gpr dR = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 ob)
    (hdx : Region.Disjoint (VG.Proof.Scrypt.X86.BlockMix.slot s₀ o) ⟨x.setWidth 64, 64⟩)
    (hinx : ∀ i < 4, InRegions (s.rd ++ s.wr) (x.setWidth 64 + BitVec.ofNat 64 (16 * i)) 16)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ o, ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s.mem s'.mem →
      bytesAt s'.mem (VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem (x.setWidth 64) 64)
          (bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  have lt := VG.Proof.Scrypt.X86.BlockMix.r_lt hp
  have ed : (VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 o).setWidth 64 = VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o := VG.Proof.Scrypt.X86.BlockMix.y_addr hp (by omega)
  have eb : (VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 ob).setWidth 64 = VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 ob := VG.Proof.Scrypt.X86.BlockMix.b_addr hp (by omega)
  rw [← List.append_nil (xor64 dR xR sR)]
  refine VG.Proof.Scrypt.X86.xor64_ok hd hx hs (VG.Proof.Scrypt.X86.BlockMix.y_fit hp ho) fx (VG.Proof.Scrypt.X86.BlockMix.b_fit hp hob) (by rw [ed]; exact hdx)
    (by rw [ed, eb]; exact VG.Proof.Scrypt.X86.BlockMix.yb_disj hp ho hob) 4 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, hp.rd, hp.wr, eb, add_ofNat]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, hp.wr, ed, add_ofNat]; exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_y hp (by omega)))
    fun s₁ g₁ rd₁ wr₁ m₁ => WP.block_nil ?_
  rw [ed, eb, show 16 * 4 = 64 from rfl] at m₁
  have l1 : (xorBytes (bytesAt s.mem (x.setWidth 64) 64)
      (bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 ob) 64)).length = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact VG.WriteBytes.writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (VG.Proof.Scrypt.X86.BlockMix.yA s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  have hf₁ : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s₁.mem :=
    hf.trans (f₁.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨VG.Proof.Scrypt.X86.BlockMix.yR s₀, List.mem_cons_self, VG.Proof.Scrypt.X86.BlockMix.y_sub hp ho⟩)
  refine WP.seq (VG.Proof.Scrypt.X86.BlockMix.salsaAt_ok hS hp hd' hd ho (by rw [g₁ _ hd, gd]) (by rw [g₁ _ (by decide), hesp])
    (by rw [rd₁, hrd]) (by rw [wr₁, hwr]) hf₁ fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁])
    (fun r hr => by rw [cs₂ r hr, g₁ r (VG.Proof.Scrypt.X86.BlockMix.calleeSaved_ne hr)])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀
  ebx : s.gpr .ebx = VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1))
  esi : s.gpr .esi = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 (64 * k)
  edi : s.gpr .edi = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 (64 * (VG.Proof.Scrypt.X86.BlockMix.rr s₀ + k))
  frame : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.Scrypt.X86.BlockMix.Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i) ∧
    bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) {s s₂ s₅ : State}
    (h : VG.Proof.Scrypt.X86.BlockMix.Inv s₀ k s)
    (f₂ : Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ (64 * k), ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (VG.Proof.Scrypt.X86.BlockMix.yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.xP s₀ k) 64) (bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 (128 * k)) 64)))
    (f₅ : Frame [VG.Proof.Scrypt.X86.BlockMix.slot s₀ (64 * (VG.Proof.Scrypt.X86.BlockMix.rr s₀ + k)), ⟨VG.Proof.Scrypt.X86.BlockMix.scA s₀, 64⟩, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (VG.Proof.Scrypt.X86.BlockMix.yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (VG.Proof.Scrypt.X86.BlockMix.yE s₀ k) 64)
      (bytesAt s₂.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s₅.mem ∧ VG.Proof.Scrypt.X86.BlockMix.Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (VG.Proof.Scrypt.X86.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i) ∧
      bytesAt s₅.mem (VG.Proof.Scrypt.X86.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i + 1) := by
  have lt := VG.Proof.Scrypt.X86.BlockMix.r_lt hp
  have oE : 64 * k + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ := by omega
  have oO : 64 * (VG.Proof.Scrypt.X86.BlockMix.rr s₀ + k) + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ := by omega
  have F₂ := h.frame.trans (VG.Proof.Scrypt.X86.BlockMix.frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (VG.Proof.Scrypt.X86.BlockMix.yE s₀ k) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * k) := by
    rw [b₂, h.x, VG.Proof.Scrypt.X86.BlockMix.b_frame hp h.frame (by omega : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega, ← VG.Proof.Scrypt.X86.BlockMix.blk_B s₀ (by omega), yAt_eq]
  have hb : bytesAt s₂.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (VG.Proof.Scrypt.X86.BlockMix.B s₀) (2 * k + 1) := by
    rw [VG.Proof.Scrypt.X86.BlockMix.blk_B s₀ (by omega)]
    exact VG.Proof.Scrypt.X86.BlockMix.b_frame hp F₂ (by omega)
  refine ⟨F₂.trans (VG.Proof.Scrypt.X86.BlockMix.frame_big hp oO f₅), VG.Proof.Scrypt.X86.BlockMix.saved_keep hp oO f₅ (VG.Proof.Scrypt.X86.BlockMix.saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [VG.Proof.Scrypt.X86.BlockMix.slot_keep hp oO oE (by omega) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [VG.Proof.Scrypt.X86.BlockMix.slot_keep hp oO (by omega) (by omega) f₅, VG.Proof.Scrypt.X86.BlockMix.slot_keep hp oE (by omega) (by omega) f₂, d₁]
    · rw [VG.Proof.Scrypt.X86.BlockMix.slot_keep hp oO (by omega) (by omega) f₅, VG.Proof.Scrypt.X86.BlockMix.slot_keep hp oE (by omega) (by omega) f₂, d₂]

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat}
    (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) {s : State} (h : VG.Proof.Scrypt.X86.BlockMix.Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.Scrypt.X86.BlockMix.Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .esi .ebp .ebx)) <| .seq (salsaAt c .esi) <|
      .seq (.block (.alu .add .ebx (.imm 64) :: xor64 .edi .esi .ebx)) <| .seq (salsaAt c .edi) P)
      s Q := by
  have lt := VG.Proof.Scrypt.X86.BlockMix.r_lt hp
  have hrd : s.rd = [VG.Proof.Scrypt.X86.BlockMix.bR s₀, VG.Proof.Scrypt.X86.BlockMix.argR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ := by omega
  have oO : 64 * (VG.Proof.Scrypt.X86.BlockMix.rr s₀ + k) + 64 ≤ 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ := by omega
  have ex := VG.Proof.Scrypt.X86.BlockMix.xP_addr hp hk
  refine WP.seq (VG.Proof.Scrypt.X86.BlockMix.half_ok hS hp (by decide) (by decide) (by decide) (by decide) oE (VG.Proof.Scrypt.X86.BlockMix.xP_fit hp hk)
    (ob := 128 * k) (by omega) h.rd h.wr h.esp h.frame h.esi h.ebp h.ebx
    (by rw [ex]; exact VG.Proof.Scrypt.X86.BlockMix.xP_disj hp hk) (by rw [ex]; exact VG.Proof.Scrypt.X86.BlockMix.xP_in hp hk hrd hwr)
    fun s₂ rd₂ wr₂ cs₂ f₂ b₂ => ?_)
  rw [ex] at b₂
  refine WP.seq (wp_addi fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .ebx → r ∈ calleeSaved → s₃.gpr r = s.gpr r := fun r h1 h2 => by
    rw [u₃.other _ h1, cs₂ r h2]
  have e3 : s₃.gpr .ebx = VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by simp [calleeSaved]), h.ebx, VG.Proof.Scrypt.X86.add32_lit]; congr 2; omega
  have hf₂ : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s₃.mem := by
    rw [u₃.mem]; exact h.frame.trans (VG.Proof.Scrypt.X86.BlockMix.frame_big hp oE f₂)
  have e5 : s₃.gpr .esi = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 (64 * k) := by
    rw [k3 _ (by decide) (by simp [calleeSaved]), h.esi]
  refine VG.Proof.Scrypt.X86.BlockMix.half_ok hS hp (by decide) (by decide) (by decide) (by decide) oO (VG.Proof.Scrypt.X86.BlockMix.y_fit hp oE)
    (ob := 64 * (2 * k + 1)) (by omega) (by rw [u₃.rd, rd₂, h.rd]) (by rw [u₃.wr, wr₂, h.wr])
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.esp]) hf₂
    (by rw [k3 _ (by decide) (by simp [calleeSaved]), h.edi]) e5 e3
    (by rw [VG.Proof.Scrypt.X86.BlockMix.y_addr hp (by omega)]; exact VG.Proof.Scrypt.X86.BlockMix.y_disj hp (by omega) oO oE)
    (fun i hi => by
      rw [u₃.rd, u₃.wr, rd₂, wr₂, hrd, hwr, VG.Proof.Scrypt.X86.BlockMix.y_addr hp (by omega), add_ofNat]
      exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_y hp (by omega)))
    fun s₅ rd₅ wr₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem, VG.Proof.Scrypt.X86.BlockMix.y_addr hp (by omega)] at b₅
  rw [u₃.mem] at f₅
  obtain ⟨F, S, D⟩ := VG.Proof.Scrypt.X86.BlockMix.mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .ebx → r ∈ calleeSaved → s₅.gpr r = s.gpr r := fun r h1 h2 => by
    rw [cs₅ r h2, k3 r h1 h2]
  exact hQ s₅ ⟨by rw [rd₅, u₃.rd, rd₂, h.rd], by rw [wr₅, u₃.wr, wr₂, h.wr],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.esp],
    by rw [cs₅ _ (by simp [calleeSaved]), e3],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.esi],
    by rw [k5 _ (by decide) (by simp [calleeSaved]), h.edi], F, S, D⟩

/-- `y + 64 (k + 1)` is `y + 64 r` exactly when `k + 1 = r`. -/
theorem cmp_end (y : BitVec 32) {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (y + BitVec.ofNat 32 a - (BitVec.ofNat 32 b + y) == 0) = decide (a = b) := by
  rw [show y + BitVec.ofNat 32 a - (BitVec.ofNat 32 b + y) = BitVec.ofNat 32 a - BitVec.ofNat 32 b by
    bv_omega]
  exact Proof.Sha256.X86.Stream.sub_beq ha hb

theorem bmNext_eq : bmNext = .mov .ebp (.reg .edi) :: .alu .add .ebx (.imm 64) ::
    .alu .add .esi (.imm 64) :: .alu .add .edi (.imm 64) ::
    (timesR 64 ++ ([.mov .ecx (.mem (at_ .esp 12)), .alu .add .eax (.reg .ecx), .alu .cmp .esi (.reg .eax)] :
      List Instr)) := rfl

/-- The pointers move on, and ZF is set after the last pair. -/
theorem regs_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat} (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) {s : State}
    (h : VG.Proof.Scrypt.X86.BlockMix.Mid s₀ k s) :
    WP isa (.block bmNext) s fun s' => VG.Proof.Scrypt.X86.BlockMix.Inv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = VG.Proof.Scrypt.X86.BlockMix.rr s₀)) := by
  have lt := VG.Proof.Scrypt.X86.BlockMix.r_lt hp
  rw [VG.Proof.Scrypt.X86.BlockMix.bmNext_eq]
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_addi fun s₉ u₉ => ?_
  have m₉ : s₉.mem = s.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g₉ : ∀ r, r ≠ .ebp → r ≠ .ebx → r ≠ .esi → r ≠ .edi → s₉.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₉.other _ h4, u₈.other _ h3, u₇.other _ h2, u₆.other _ h1]
  have esp₉ : s₉.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀ := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide), h.esp]
  have rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  have wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  refine VG.Proof.Scrypt.X86.timesR_ok (r := arg s₀ 1) (by rw [esp₉, m₉, VG.Proof.Scrypt.X86.BlockMix.arg_keep hp h.frame (by omega) (by omega)]; rfl)
    (by rw [esp₉, rd₉, wr₉]; exact VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega)) fun t e o mt rdt wrt => ?_
  refine wp_movm (a := addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 12) (by rw [ea_at, o _ (by decide) (by decide) (by decide), esp₉])
    (by rw [rdt, wrt, rd₉, wr₉]; exact VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega)) fun t₀ u₀ => ?_
  refine wp_add fun t₁ u₁ => wp_cmp fun t₂ f₂ _ z₂ => WP.block_nil ?_
  have gt : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → t₂.gpr r = s₉.gpr r := fun r h1 h2 h3 => by
    rw [f₂.gpr, u₁.other _ h1, u₀.other _ h2, o r h1 h2 h3]
  have mt₂ : t₂.mem = s.mem := by rw [f₂.mem, u₁.mem, u₀.mem, mt, m₉]
  have esi₉ : s₉.gpr .esi = VG.Proof.Scrypt.X86.BlockMix.yP s₀ + BitVec.ofNat 32 (64 * (k + 1)) := by
    rw [u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), h.esi, VG.Proof.Scrypt.X86.add32_lit]
    congr 2
  refine ⟨⟨(by omega), by rw [f₂.rd, u₁.rd, u₀.rd, rdt, rd₉], by rw [f₂.wr, u₁.wr, u₀.wr, wrt, wr₉],
    by rw [gt _ (by decide) (by decide) (by decide), esp₉], ?_, ?_, ?_, ?_,
    by rw [mt₂]; exact h.frame, by rw [mt₂]; exact h.saved, by rw [mt₂]; exact h.done, ?_⟩, ?_⟩
  · rw [gt _ (by decide) (by decide) (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.gpr, u₆.other _ (by decide), h.ebx, VG.Proof.Scrypt.X86.add32_lit]
    congr 2; omega
  · rw [gt _ (by decide) (by decide) (by decide), esi₉]
  · rw [gt _ (by decide) (by decide) (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.edi, VG.Proof.Scrypt.X86.add32_lit]
    congr 2
  · rw [gt _ (by decide) (by decide) (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.edi]
    rfl
  · rw [mt₂]
    show bytesAt s.mem (VG.Proof.Scrypt.X86.BlockMix.yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl
  · have hax : t₁.gpr .eax = BitVec.ofNat 32 (64 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) + VG.Proof.Scrypt.X86.BlockMix.yP s₀ := by
      rw [u₁.gpr, u₀.gpr, u₀.other _ (by decide), e, mt, m₉, VG.Proof.Scrypt.X86.BlockMix.arg_keep hp h.frame (by omega) (by omega),
        show (64 : BitVec 32).toNat = 64 from rfl, Nat.mul_comm]
      rfl
    rw [z₂, u₁.other _ (by decide), u₀.other _ (by decide), o _ (by decide) (by decide) (by decide), esi₉,
      hax,
      VG.Proof.Scrypt.X86.BlockMix.cmp_end _ (by omega) (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))

theorem body_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {k : Nat}
    (hk : k < VG.Proof.Scrypt.X86.BlockMix.rr s₀) {s : State} (h : VG.Proof.Scrypt.X86.BlockMix.Inv s₀ k s) :
    WP isa (bmBody c) s fun s' => VG.Proof.Scrypt.X86.BlockMix.Inv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = VG.Proof.Scrypt.X86.BlockMix.rr s₀)) :=
  VG.Proof.Scrypt.X86.BlockMix.halves_ok hS hp hk h fun _ hm => VG.Proof.Scrypt.X86.BlockMix.regs_ok hp hk hm

end VG.Proof.Scrypt.X86.BlockMix

end

/- Proofs formerly in `VerifiedGarbage.Proof.Scrypt.X86.BlockMixVerified`. -/
section

section

/-!
# scryptBlockMix on x86 (32-bit): the whole function

The prologue saves our caller's `ebx`, `esi`, `edi` and `ebp` in `scratch` and
sets up the loop's registers from the arguments; the loop runs the `r` pairs;
the epilogue restores the registers.
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movm wp_add wp_subi)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add
  bytesAt_blocks)

/-! ## The prologue -/

/-- The prologue's register moves. -/
def bmSetup : List Instr :=
  .mov .ebx (.mem (at_ .esp 4)) :: .mov .esi (.mem (at_ .esp 12)) ::
    (timesR 64 ++ ([.mov .edi (.reg .esi), .alu .add .edi (.reg .eax), .mov .ebp (.reg .ebx),
      .alu .add .ebp (.reg .eax), .alu .add .ebp (.reg .eax), .alu .sub .ebp (.imm 64)] : List Instr))

theorem prologue_eq : bmPrologue =
    .mov .eax (.mem (at_ .esp 20)) :: (bmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ VG.Proof.Scrypt.X86.BlockMix.bmSetup) :=
  rfl

theorem bmSaved_bound : ∀ p ∈ bmSaved, p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 ∧ p.1 ≠ .eax := by decide

theorem bmSaved_fits : Spill.Fits 128 bmSaved := by decide

theorem bmSaved_addr (s₀ : State) (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) :
    ∀ p ∈ bmSaved, addr (VG.Proof.Scrypt.X86.BlockMix.sc s₀) p.2 = VG.Proof.Scrypt.X86.BlockMix.scA s₀ + BitVec.ofNat 64 p.2 :=
  Spill.addr_eq_of_fits hp.s_nw VG.Proof.Scrypt.X86.BlockMix.bmSaved_fits

theorem save_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r) → s₁.gpr .eax = VG.Proof.Scrypt.X86.BlockMix.sc s₀ → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → Frame [VG.Proof.Scrypt.X86.BlockMix.scR s₀] s₀.mem s₁.mem → VG.Proof.Scrypt.X86.BlockMix.Saved s₀ s₁.mem → WP isa (.block rest) s₁ Q) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 20)) ::
      (bmSaved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++ rest))) s₀ Q := by
  have hs := hp.s_nw
  refine wp_movm (a := addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 20) rfl (VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega)) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = VG.Proof.Scrypt.X86.BlockMix.sc s₀ := u₁.gpr
  have ha := VG.Proof.Scrypt.X86.BlockMix.bmSaved_addr s₀ hp
  refine Spill.save_ok bmSaved (fun p hp' => ?_) fun s₂ u₂ => ?_
  · rw [e, u₁.wr, hp.wr, ha p hp']
    exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_s s₀ (bmSaved_fits.1 p hp'))
  refine k s₂ (fun r hr => by rw [u₂.gpr, u₁.other r hr]) (by rw [u₂.gpr, e]) (by rw [u₂.rd, u₁.rd])
    (by rw [u₂.wr, u₁.wr]) ?_ ?_
  · rw [u₂.mem, e, u₁.mem]
    exact Spill.saveMem_frame List.mem_cons_self _ _ _ _ fun p hp' => by
      rw [ha p hp']; exact VG.Proof.Scrypt.X86.BlockMix.in_s s₀ (bmSaved_fits.1 p hp')
  · rw [u₂.mem, e, u₁.mem]
    exact (Spill.saveMem_saved_addr _ _ VG.Proof.Scrypt.X86.BlockMix.bmSaved_fits hs).congr ha
      fun p hp' => u₁.other _ (VG.Proof.Scrypt.X86.BlockMix.bmSaved_bound p hp').2.2

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {s₁ : State} (g : ∀ r, r ≠ .eax → s₁.gpr r = s₀.gpr r)
    (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hf : Frame [VG.Proof.Scrypt.X86.BlockMix.scR s₀] s₀.mem s₁.mem)
    (hsv : VG.Proof.Scrypt.X86.BlockMix.Saved s₀ s₁.mem) :
    WP isa (.block VG.Proof.Scrypt.X86.BlockMix.bmSetup) s₁ (VG.Proof.Scrypt.X86.BlockMix.Inv s₀ 0) := by
  have lt := VG.Proof.Scrypt.X86.BlockMix.r_lt hp
  have pos := hp.pos
  have hesp : s₁.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀ := g _ (by decide)
  have hf' : Frame [VG.Proof.Scrypt.X86.BlockMix.yR s₀, VG.Proof.Scrypt.X86.BlockMix.scR s₀, VG.Proof.Scrypt.X86.BlockMix.stkR s₀] s₀.mem s₁.mem := hf.mono (by simp)
  have rd₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [hrd, hwr]
  unfold VG.Proof.Scrypt.X86.BlockMix.bmSetup
  refine wp_movm (a := addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 4) (by rw [ea_at, hesp])
    (by rw [rd₁]; exact VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega)) fun a ua => ?_
  refine wp_movm (a := addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 12) (by rw [ea_at, ua.other _ (by decide), hesp])
    (by rw [ua.rd, ua.wr, rd₁]; exact VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega)) fun b ub => ?_
  have eb : b.gpr .esp = VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀ := by rw [ub.other _ (by decide), ua.other _ (by decide), hesp]
  have mb : b.mem = s₁.mem := by rw [ub.mem, ua.mem]
  have bx : b.gpr .ebx = VG.Proof.Scrypt.X86.BlockMix.bP s₀ := by
    rw [ub.other _ (by decide), ua.gpr, VG.Proof.Scrypt.X86.BlockMix.arg_keep hp hf' (by omega) (by omega)]; rfl
  have bs : b.gpr .esi = VG.Proof.Scrypt.X86.BlockMix.yP s₀ := by
    rw [ub.gpr, ua.mem, VG.Proof.Scrypt.X86.BlockMix.arg_keep hp hf' (by omega) (by omega)]; rfl
  refine VG.Proof.Scrypt.X86.timesR_ok (r := arg s₀ 1) (by rw [eb, mb, VG.Proof.Scrypt.X86.BlockMix.arg_keep hp hf' (by omega) (by omega)]; rfl)
    (by rw [eb, ub.rd, ub.wr, ua.rd, ua.wr, rd₁]; exact VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega))
    fun t e o mt rdt wrt => ?_
  refine wp_mov fun c uc => wp_add fun d ud => wp_mov fun f uf => wp_add fun i ui => wp_add fun j uj =>
    wp_subi fun l ul _ => WP.block_nil ?_
  have e64 : t.gpr .eax = BitVec.ofNat 32 (VG.Proof.Scrypt.X86.BlockMix.rr s₀ * 64) := by rw [e]; rfl
  have kl : ∀ r, r ≠ .ebp → r ≠ .edi → r ≠ .eax → r ≠ .ecx → r ≠ .edx → l.gpr r = b.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [ul.other _ h1, uj.other _ h1, ui.other _ h1, uf.other _ h1, ud.other _ h2, uc.other _ h2,
        o r h3 h4 h5]
  have ml : l.mem = s₁.mem := by rw [ul.mem, uj.mem, ui.mem, uf.mem, ud.mem, uc.mem, mt, mb]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => absurd hi (by omega), ?_⟩
  · rw [ul.rd, uj.rd, ui.rd, uf.rd, ud.rd, uc.rd, rdt, ub.rd, ua.rd, hrd]
  · rw [ul.wr, uj.wr, ui.wr, uf.wr, ud.wr, uc.wr, wrt, ub.wr, ua.wr, hwr]
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), eb]
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), bx]; simp
  · rw [kl _ (by decide) (by decide) (by decide) (by decide) (by decide), bs]; simp
  · rw [ul.other _ (by decide), uj.other _ (by decide), ui.other _ (by decide), uf.other _ (by decide),
      ud.gpr, uc.gpr, uc.other _ (by decide), e64, o _ (by decide) (by decide) (by decide), bs]
    congr 2; omega
  · rw [ul.gpr, uj.gpr, ui.gpr, ui.other .eax (by decide), uf.gpr, uf.other .eax (by decide),
      ud.other .ebx (by decide), ud.other .eax (by decide), uc.other .ebx (by decide),
      uc.other .eax (by decide), e64, o _ (by decide) (by decide) (by decide), bx, VG.Proof.Scrypt.X86.add32,
      VG.Proof.Scrypt.X86.sub32 _ (by omega)]
    show _ = VG.Proof.Scrypt.X86.BlockMix.bP s₀ + BitVec.ofNat 32 (128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ - 64)
    congr 2; omega
  · rw [ml]; exact hf'
  · rw [ml]; exact hsv
  · rw [ml]
    show bytesAt s₁.mem (VG.Proof.Scrypt.X86.BlockMix.bA s₀ + BitVec.ofNat 64 (128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ - 64)) 64 =
      blk (VG.Proof.Scrypt.X86.BlockMix.B s₀) (2 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ - 1)
    rw [VG.Proof.Scrypt.X86.BlockMix.blk_B s₀ (by omega), show 64 * (2 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ - 1) = 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ - 64 by omega]
    exact VG.Proof.Scrypt.X86.BlockMix.b_frame hp hf' (by omega)

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : VG.Proof.Scrypt.X86.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {s : State}
    (h : VG.Proof.Scrypt.X86.BlockMix.Inv s₀ 0 s) : WP isa (.loop (bmBody c) .ne) s (VG.Proof.Scrypt.X86.BlockMix.Inv s₀ (VG.Proof.Scrypt.X86.BlockMix.rr s₀)) :=
  VG.Proof.Scrypt.X86.count_loop hp.pos (VG.Proof.Scrypt.X86.BlockMix.Inv s₀) (fun _ hk _ h => VG.Proof.Scrypt.X86.BlockMix.body_ok hS hp hk h) h

/-! ## The epilogue -/

theorem epilogue_eq : bmEpilogue =
    .mov .eax (.mem (at_ .esp 20)) :: (bmSaved.map (fun p => Instr.mov p.1 (.mem (at_ .eax p.2))) ++ []) :=
  rfl

theorem restore_ok {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) {s : State} (h : VG.Proof.Scrypt.X86.BlockMix.Inv s₀ (VG.Proof.Scrypt.X86.BlockMix.rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) := by
  have hs := hp.s_nw
  rw [VG.Proof.Scrypt.X86.BlockMix.epilogue_eq]
  refine wp_movm (a := addr (VG.Proof.Scrypt.X86.BlockMix.esp₀ s₀) 20) (by rw [ea_at, h.esp])
    (by rw [h.rd, h.wr]; exact VG.Proof.Scrypt.X86.BlockMix.arg_in hp (by omega) (by omega)) fun s₁ u₁ => ?_
  have e : s₁.gpr .eax = VG.Proof.Scrypt.X86.BlockMix.sc s₀ := by rw [u₁.gpr, VG.Proof.Scrypt.X86.BlockMix.arg_keep hp h.frame (by omega) (by omega)]; rfl
  have ha := VG.Proof.Scrypt.X86.BlockMix.bmSaved_addr s₀ hp
  refine Spill.restore_ok bmSaved (by decide) (fun p hp' => ?_)
    (by rw [e, u₁.mem]; exact h.saved.congr (fun p hp' => (ha p hp').symm) fun _ _ => rfl)
    fun s₂ u => WP.block_nil ⟨by rw [u.mem, u₁.mem],
      u.abi (by decide) (by decide) (by rw [u₁.other _ (by decide), h.esp])⟩
  rw [e, u₁.rd, u₁.wr, h.rd, h.wr, hp.rd, hp.wr, ha p hp']
  exact InRegions.of_mem (by simp) (VG.Proof.Scrypt.X86.BlockMix.in_s s₀ (bmSaved_fits.1 p hp'))

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < VG.Proof.Scrypt.X86.BlockMix.rr s₀, bytesAt m (VG.Proof.Scrypt.X86.BlockMix.yE s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i) ∧
      bytesAt m (VG.Proof.Scrypt.X86.BlockMix.yO s₀ i) 64 = yAt (VG.Proof.Scrypt.X86.BlockMix.B s₀) (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (2 * i + 1)) :
    bytesAt m (VG.Proof.Scrypt.X86.BlockMix.yA s₀) (128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) = blockMix (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (VG.Proof.Scrypt.X86.BlockMix.B s₀) := by
  rw [blockMix_eq, show 128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ = 64 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ + 64 * VG.Proof.Scrypt.X86.BlockMix.rr s₀ by omega, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem correct {c : Prog isa} (hS : VG.Proof.Scrypt.X86.BlockMix.SalsaSpec c) {s₀ : State} (hp : VG.Proof.Scrypt.X86.BlockMix.Pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixX86.post s₀ s' := by
  unfold blockMixWith
  refine WP.seq ?_
  rw [VG.Proof.Scrypt.X86.BlockMix.prologue_eq]
  refine VG.Proof.Scrypt.X86.BlockMix.save_ok hp fun s₁ g _ hrd hwr hf hsv => ?_
  refine WP.mono (VG.Proof.Scrypt.X86.BlockMix.setup_ok hp g hrd hwr hf hsv) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (VG.Proof.Scrypt.X86.BlockMix.loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (VG.Proof.Scrypt.X86.BlockMix.restore_ok hp h₃) fun s' ⟨hm', hg'⟩ => ⟨⟨hg', ?_⟩, ?_⟩
  · rw [hm']
    refine h₃.frame.readW (r := VG.Proof.Scrypt.X86.BlockMix.retR s₀) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_y, hp.ret_s, VG.Proof.Scrypt.X86.BlockMix.ret_stk hp]
  · show bytesAt s'.mem (VG.Proof.Scrypt.X86.BlockMix.yA s₀) (128 * VG.Proof.Scrypt.X86.BlockMix.rr s₀) = blockMix (VG.Proof.Scrypt.X86.BlockMix.rr s₀) (VG.Proof.Scrypt.X86.BlockMix.B s₀)
    rw [hm']
    exact VG.Proof.Scrypt.X86.BlockMix.post_of fun i hi => h₃.done i hi

end VG.Proof.Scrypt.X86.BlockMix

end

/-!
# scryptBlockMix on x86 (32-bit): verified

`SalsaSpec` of the verified Salsa20/8 Core, from its proof by `WP.callWith`;
then the `Verified` proof of `vg_scrypt_blockmix`. Only `esp` and the
arguments are public, and the taint analysis checks that nothing else reaches
an address or a branch: the words holding `y` and `scratch` are the bases of
the two writable regions, and the code reads the pointers and `r` from the
arguments, which it never writes. The proof is written against a contract
under which the code only reads its arguments, and moved to the shared
contract with `Verified.narrowTo`.
-/

namespace VG.Proof.Scrypt.X86.BlockMix

open VG VG.X86

theorem salsa_nosp : NoSp Impl.Scrypt.X86.salsa := NoSp.of_all (by decide +kernel)

theorem salsa_stack : stackUse Impl.Scrypt.X86.salsa = 0 := by decide +kernel

theorem salsaSpec : VG.Proof.Scrypt.X86.BlockMix.SalsaSpec Impl.Scrypt.X86.salsa := by
  intro s dR d sc hdR hd hsc fd fsc hds hlo hsd hss hind hins Q hQ
  set E := s.gpr .esp with hE
  have hrs : Reg.esp ∉ [Reg.eax, dR] := by simp [Ne.symm hdR]
  have fit : 4 * [Reg.eax, dR].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega
  set sE := (pushed [Reg.eax, dR] s).callEntry with hsE
  have a0 : arg sE 0 = d := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hd]
  have a1 : arg sE 1 = sc := by rw [hsE, callEntry_arg fit hrs (by simp)]; simp [hsc]
  have eA : argAddr sE 0 = (E - BitVec.ofNat 32 8).setWidth 64 := by
    rw [hsE, callEntry_argAddr0]; rfl
  have eSp : sE.gpr .esp = E - BitVec.ofNat 32 12 := by
    rw [hsE, callEntry_esp']; rfl
  have b8 : Region.Sub (below E 8) (below E 12) := below_sub (by omega) hlo
  have r4 : Region.Sub ⟨(E - BitVec.ofNat 32 12).setWidth 64, 4⟩ (below E 12) := by
    have := below_inner (sp := E) (a := 4) (b := 12) (k := 8) (by omega) hlo
    rw [show E - BitVec.ofNat 32 12 = E - BitVec.ofNat 32 8 - BitVec.ofNat 32 4 by bv_omega]
    exact this
  have e12 : 4 * [Reg.eax, dR].length + stackUse Impl.Scrypt.X86.salsa + 4 = 12 := by
    rw [VG.Proof.Scrypt.X86.BlockMix.salsa_stack]; rfl
  refine WP.callWith (k := Proof.Scrypt.salsaX86) salsa_correct VG.Proof.Scrypt.X86.BlockMix.salsa_nosp (by simp) hrs
    (by rw [e12]; exact hlo)
    (rd := [⟨argAddr sE 0, 8⟩]) (wr := [⟨d.setWidth 64, 64⟩, ⟨sc.setWidth 64, 64⟩])
    ⟨?_, ?_, ?_⟩ fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  · rw [← hsE]
    simp only [Proof.Scrypt.salsaX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, eA, eSp]
    refine ⟨trivial, trivial, hds, hsd.sub_left b8, hss.sub_left b8, hsd.sub_left r4, hss.sub_left r4,
      fd, fsc, ?_⟩
    rw [sub_toNat hlo]; have := E.isLt; omega
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine InRegions_append_cons.mpr (.inl ?_)
      rw [eA] at hcn
      exact hcn
    · obtain ⟨r', hr', hc'⟩ := hind
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', by
        have : (⟨d.setWidth 64, 64⟩ : Region).Contains a n := hcn
        simp only [Region.Contains] at this hc' ⊢
        bv_omega⟩)
    · obtain ⟨r', hr', hc'⟩ := hins
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', by
        have : (⟨sc.setWidth 64, 64⟩ : Region).Contains a n := hcn
        simp only [Region.Contains] at this hc' ⊢
        bv_omega⟩)
  · intro a n ⟨r, hr, hcn⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := hind
      refine ⟨r', List.mem_cons_of_mem _ hr', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
    · obtain ⟨r', hr', hc'⟩ := hins
      refine ⟨r', List.mem_cons_of_mem _ hr', ?_⟩
      simp only [Region.Contains] at hcn hc' ⊢
      bv_omega
  · rw [e12] at f'
    have hsE' := callEntry_frame fit hrs
    rw [show 4 * [Reg.eax, dR].length + 4 = 12 from rfl, ← hsE] at hsE'
    rw [← hsE] at post
    simp only [Proof.Scrypt.salsaX86, arg_withRegions, State.withRegions_mem, a0, m₂] at post
    refine hQ s' rd' wr' cs' (f'.mono fun r hr => by simpa using hr) ?_
    rw [post]
    congr 1
    refine Proof.Scrypt.Memory.frame_bytesAt hsE' (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact hsd.symm

/-! ## Constant time -/

/-- The initial taint: `esp` and the arguments are public, the words holding
`y` and `scratch` are the base addresses of the writable regions (`y` of a
length the analysis does not know), and the 12 bytes below `esp` are outside
them. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [0, 128], argLen := 24,
    argBases := [(12, 0), (20, 1)], room := 12 }

theorem wf₀ {s : State} (h : Proof.Scrypt.blockMixX86.pre s) : VG.X86.Taint.Wf VG.Proof.Scrypt.X86.BlockMix.τ₀ s := by
  have hp := VG.Proof.Scrypt.X86.BlockMix.pre_of h
  have hy := hp.y_nw; have hsc := hp.s_nw; have hs := hp.sp_fit; have hlo := hp.sp_lo
  obtain ⟨-, -, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Scrypt.X86.BlockMix.τ₀], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.y_s, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_y hp.a_y
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_s hp.a_s
  · intro p hp'
    simp only [VG.Proof.Scrypt.X86.BlockMix.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · rw [hp.r3] at k1; exact k1
    · exact k2

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Scrypt.blockMixX86.pre s₁)
    (h₂ : Proof.Scrypt.blockMixX86.pre s₂) (hpub : Proof.Scrypt.blockMixX86.pub s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Scrypt.X86.BlockMix.τ₀ s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := VG.Proof.Scrypt.X86.BlockMix.pre_of h₁; have hp₂ := VG.Proof.Scrypt.X86.BlockMix.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Scrypt.X86.BlockMix.wf₀ h₁, VG.Proof.Scrypt.X86.BlockMix.wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Scrypt.X86.BlockMix.τ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [VG.Proof.Scrypt.X86.BlockMix.yR, VG.Proof.Scrypt.X86.BlockMix.scR, VG.Proof.Scrypt.X86.BlockMix.yA, VG.Proof.Scrypt.X86.BlockMix.scA, VG.Proof.Scrypt.X86.BlockMix.yP, VG.Proof.Scrypt.X86.BlockMix.sc, VG.Proof.Scrypt.X86.BlockMix.rr, ha 1 (by omega), ha 2 (by omega), ha 4 (by omega)]
  · simp only [VG.Proof.Scrypt.X86.BlockMix.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.sp_fit h4 hk, VG.X86.Taint.argByte_eq hp₂.sp_fit h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega))]
    exact congrArg _ (ha _ (by omega))

/-- Memory holding the arguments `0x1000, 1, 0x2000, 1, 0x3000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500d then 0x20 else
  if a = 0x5010 then 1 else if a = 0x5015 then 0x30 else 0

/-- A state satisfying the precondition. -/
def sat : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Scrypt.X86.BlockMix.satMem
  rd := [⟨0x1000, 128⟩, ⟨0x5004, 20⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem sat_pre : Proof.Scrypt.blockMixX86.pre VG.Proof.Scrypt.X86.BlockMix.sat := by
  have a0 : arg VG.Proof.Scrypt.X86.BlockMix.sat 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Scrypt.X86.BlockMix.sat 1 = 1 := by decide
  have a2 : arg VG.Proof.Scrypt.X86.BlockMix.sat 2 = 0x2000 := by decide
  have a3 : arg VG.Proof.Scrypt.X86.BlockMix.sat 3 = 1 := by decide
  have a4 : arg VG.Proof.Scrypt.X86.BlockMix.sat 4 = 0x3000 := by decide
  have e : argAddr VG.Proof.Scrypt.X86.BlockMix.sat 0 = 0x5004 := by decide
  simp only [Proof.Scrypt.blockMixX86, a0, a1, a2, a3, a4, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
    by decide, trivial, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixX86.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.X86.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixX86.post s s' := by
  obtain ⟨t, s', he, h⟩ := BlockMix.correct VG.Proof.Scrypt.X86.BlockMix.salsaSpec (VG.Proof.Scrypt.X86.BlockMix.pre_of hs)
  exact ⟨t, s', he, h⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixX86.pre Proof.Scrypt.blockMixX86.pub
    Impl.Scrypt.X86.blockMix :=
  VG.Taint.constantTime (A := VG.X86.sseTaint) VG.Proof.Scrypt.X86.BlockMix.τ₀ (fun _ _ h₁ h₂ hp => VG.Proof.Scrypt.X86.BlockMix.agree₀ h₁ h₂ hp) (by taint_decide)

/-! ## The shared contract -/

/-- `blockMixX86` with its arguments writable, as the shared contract lets them be. -/
def blockMixWide : Contract isa :=
  { Proof.Scrypt.blockMixX86 with
    pre := fun s =>
      let r := (arg s 1).toNat
      let b : Region := ⟨(arg s 0).setWidth 64, r * 128⟩
      let y : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 128⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 12, 12⟩
      s.rd = [b] ∧ s.wr = [y, scratch, args] ∧
      y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧ args.Disjoint y ∧ args.Disjoint scratch ∧
      ret.Disjoint y ∧ ret.Disjoint scratch ∧ stack.Disjoint b ∧ stack.Disjoint y ∧
      stack.Disjoint scratch ∧
      (arg s 0).toNat + r * 128 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat * 128 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 128 ≤ 2 ^ 32 ∧ 12 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧
      arg s 3 = arg s 1 ∧ 0 < r }

/-- The regions `blockMixX86` lets the code read and write. -/
def narrowRd (s : State) : List Region :=
  [⟨(arg s 0).setWidth 64, (arg s 1).toNat * 128⟩, ⟨argAddr s 0, 20⟩]
def narrowWr (s : State) : List Region :=
  [⟨(arg s 2).setWidth 64, (arg s 3).toNat * 128⟩, ⟨(arg s 4).setWidth 64, 128⟩]

/-- Rewrites the contracts at a narrowed state (`arg` does not unfold
cheaply). -/
local macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Scrypt.blockMixX86, VG.Proof.Scrypt.X86.BlockMix.blockMixWide,
    VG.Proof.Scrypt.X86.BlockMix.narrowRd, VG.Proof.Scrypt.X86.BlockMix.narrowWr, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, VG.X86.State.withRegions_gpr, VG.X86.State.withRegions_mem,
    VG.X86.State.withRegions_rd, VG.X86.State.withRegions_wr] $(loc)?)

theorem blockMixWide_pre (s : State) (h : blockMixWide.pre s) :
    Proof.Scrypt.blockMixX86.pre (s.withRegions (VG.Proof.Scrypt.X86.BlockMix.narrowRd s) (VG.Proof.Scrypt.X86.BlockMix.narrowWr s)) := by
  obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
  narrow
  exact ⟨trivial, trivial, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩

/-- A state satisfying `blockMixWide.pre`. -/
def wideSat : State :=
  { VG.Proof.Scrypt.X86.BlockMix.sat with
             rd := [⟨0x1000, 128⟩], wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩, ⟨0x5004, 20⟩] }

theorem blockMixWide_implies :
    blockMixWide.Implies (Spec.Scrypt.blockMixContract X86.abi 12) := by
  have a0 : arg VG.Proof.Scrypt.X86.BlockMix.wideSat 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Scrypt.X86.BlockMix.wideSat 1 = 1 := by decide
  have a2 : arg VG.Proof.Scrypt.X86.BlockMix.wideSat 2 = 0x2000 := by decide
  have a3 : arg VG.Proof.Scrypt.X86.BlockMix.wideSat 3 = 1 := by decide
  have a4 : arg VG.Proof.Scrypt.X86.BlockMix.wideSat 4 = 0x3000 := by decide
  have e : argAddr VG.Proof.Scrypt.X86.BlockMix.wideSat 0 = 0x5004 := by decide
  have esp : wideSat.gpr .esp = 0x5000 := rfl
  sig_implies [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig, VG.Proof.Scrypt.X86.BlockMix.blockMixWide,
    Proof.Scrypt.blockMixX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp] using VG.Proof.Scrypt.X86.BlockMix.wideSat

/-- The proof is written against `blockMixX86`, widened to writable arguments. -/
theorem blockMix_verified :
    Verified X86.target Impl.Scrypt.X86.blockMix (Spec.Scrypt.blockMixContract X86.abi 12) :=
  have hsat := blockMixWide_implies.sat_left
  (Verified.narrowTo (Verified.of_correct VG.Proof.Scrypt.X86.BlockMix.blockMix_correct VG.Proof.Scrypt.X86.BlockMix.blockMix_ct (.refl ⟨VG.Proof.Scrypt.X86.BlockMix.sat, VG.Proof.Scrypt.X86.BlockMix.sat_pre⟩))
    VG.Proof.Scrypt.X86.BlockMix.narrowRd VG.Proof.Scrypt.X86.BlockMix.narrowWr VG.Proof.Scrypt.X86.BlockMix.blockMixWide_pre
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [VG.Proof.Scrypt.X86.BlockMix.narrowRd, VG.Proof.Scrypt.X86.BlockMix.narrowWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [VG.Proof.Scrypt.X86.BlockMix.narrowWr, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat).of_implies VG.Proof.Scrypt.X86.BlockMix.blockMixWide_implies

end VG.Proof.Scrypt.X86.BlockMix

end
