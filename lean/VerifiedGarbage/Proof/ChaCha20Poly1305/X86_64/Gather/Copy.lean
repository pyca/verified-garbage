import VerifiedGarbage.Proof.AesGcm.X86_64.Short.Copy
import VerifiedGarbage.Proof.Framework.X86_64.StraightY
import VerifiedGarbage.Proof.Framework.X86_64.StraightZ
import VerifiedGarbage.Impl.ChaCha20Poly1305.X86_64.SealGather

/-!
# ChaCha20-Poly1305 encryption out of place, from a list of slices, x86-64: copying a slice

Untrusted: everything here is checked by Lean. `copyBytes w` copies `rcx`
bytes from `rsi` to `rdi` (`copyBytes_ok`): `c = 2 ^ w.log` at a time
through `xmm0` (`wideStep_ok`, by SSE2's `movdqu`, AVX's `vmovdqu` of `ymm0`
or AVX-512's `vmovdqu32` of `zmm0`), then, after a wider copy, 16 at a time
with AVX (`vexStep_ok`), then one at a time, as AES-GCM's short path does
(`Proof/AesGcm/X86_64/Short/Copy.lean`, whose byte loop it shares). Each
loop runs from where the one before stopped (`chunks_ok`); the buffers do
not overlap.
-/

set_option linter.unusedSimpArgs false

namespace VG.Proof.ChaCha20Poly1305.X86_64.Gather

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64 VG.WriteBytes
open VG.Impl.ChaCha20Poly1305.X86_64.SealGather (Width wideBody vex16Body copyTail copyBytes)
open VG.Proof.AesGcm.X86_64 (ea_idx succ_ofNat bytesAt_succ in_of_covers copyBody copyStep_ok src_kept length_bytesAt
  writeBytes_frame' bytesAt_add ofNat_add_ofNat sub_beq bytesAt_frame)
open VG.Proof.AesGcm.X86_64.Short (writeW_readW128 CopyPre shl_ofNat)
open VG.Spec.Aes (bytesAt)

/-! ## One step of each loop -/

/-- A store of `n` bytes loaded is a write of the bytes loaded. -/
theorem writeW_readW_n (m src : Mem) (a b : Addr) (n : Nat) :
    m.writeW a (src.readW b (8 * n)) = writeBytes m a (bytesAt src b n) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show 8 * n / 8 = n by omega, BitVec.setWidth_eq, BitVec.setWidth_eq, write_eq_writeBytes]
  congr 1
  simp only [bytesAt]
  exact List.map_congr_left fun j hj => Mem.extractLsb'_read _ _ (List.mem_range.mp hj)

/-- The number of bytes `w` copies at a time. -/
abbrev cbytes (w : Width) : Nat := 2 ^ w.log

theorem cbytes_pos (w : Width) : 0 < cbytes w := Nat.two_pow_pos _

/-- What one step of a copy loop of `c` bytes at a time does, from `[rsi + r10]`
to `[rdi + r10]`, with the loop's end in `r8`. -/
def StepOk (body : List Instr) (c : Nat) : Prop :=
  ∀ (s : State) {S D : Addr} {i k : Nat}, s.gpr .rsi = S → s.gpr .rdi = D → s.gpr .r10 = BitVec.ofNat 64 i →
    s.gpr .r8 = BitVec.ofNat 64 k → InRegions (s.rd ++ s.wr) (S + BitVec.ofNat 64 i) c →
    InRegions s.wr (D + BitVec.ofNat 64 i) c →
    ∃ s', runBlock isa body s = some s' ∧
      s'.mem = writeBytes s.mem (D + BitVec.ofNat 64 i) (bytesAt s.mem (S + BitVec.ofNat 64 i) c) ∧
      s'.gpr .r10 = BitVec.ofNat 64 i + BitVec.ofNat 64 c ∧
      s'.zf = some (BitVec.ofNat 64 i + BitVec.ofNat 64 c - BitVec.ofNat 64 k == 0) ∧
      (∀ r, r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem gpr_setZ' (s : State) (r : XReg) (a b c d : BitVec 128) : (s.setZ r a b c d).gpr = s.gpr := rfl
theorem mem_setZ' (s : State) (r : XReg) (a b c d : BitVec 128) : (s.setZ r a b c d).mem = s.mem := rfl
theorem rd_setZ' (s : State) (r : XReg) (a b c d : BitVec 128) : (s.setZ r a b c d).rd = s.rd := rfl
theorem wr_setZ' (s : State) (r : XReg) (a b c d : BitVec 128) : (s.setZ r a b c d).wr = s.wr := rfl

theorem wideStep_ok (w : Width) : StepOk (wideBody w) (cbytes w) := by
  intro s S D i k hs hd hi hk r wr
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  cases w <;> simp only [cbytes, Width.log, Nat.reducePow] at r wr ⊢
  case x16 =>
    refine ⟨_, by
      simp only [wideBody, Width.log, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, execAlu, State.load128, State.store128, State.ea, e₁, r, ite_true, Option.map_some,
        Option.bind_some, gpr_setXmm, rd_setXmm, wr_setXmm, mem_setXmm, xmm_setXmm_self, e₂, wr, Nat.reducePow]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
      exact writeW_readW128 _ _ _ _
    · simp [gpr_setReg, gpr_arithFlags, hi]
    · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
    · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
  case y32 =>
    refine ⟨_, by
      simp only [wideBody, Width.log, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, execAlu, State.load256, State.store256, State.ea, e₁, r, ite_true, Option.map_some,
        Option.bind_some, gpr_setV, rd_setV, wr_setV, mem_setV, StraightY.ymm_setV, e₂, wr, Nat.reducePow]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags, StraightY.split_eq]
      exact writeW_readW_n _ _ _ _ 32
    · simp [gpr_setReg, gpr_arithFlags, hi]
    · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
    · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]
  case z64 =>
    refine ⟨_, by
      simp only [wideBody, Width.log, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil,
        exec, readSrc, execAlu, State.load512, State.store512, State.ea, e₁, r, ite_true, Option.map_some,
        Option.bind_some, gpr_setZ', rd_setZ', wr_setZ', mem_setZ', StraightZ.zmm_load, e₂, wr, Nat.reducePow]
      rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
    · simp only [mem_setReg, mem_arithFlags, mem_setFlags]
      exact writeW_readW_n _ _ _ _ 64
    · simp [gpr_setReg, gpr_arithFlags, hi]
    · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
    · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]

theorem vexStep_ok : StepOk vex16Body 16 := by
  intro s S D i k hs hd hi hk r wr
  have e₁ := ea_idx s .rsi hs hi
  have e₂ := ea_idx s .rdi hd hi
  refine ⟨_, by
    simp only [vex16Body, srcB, dstB, imm, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
      State.load128, State.store128, State.ea, e₁, r, ite_true, Option.map_some, Option.bind_some, gpr_setV,
      rd_setV, wr_setV, mem_setV, e₂, wr]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl⟩
  · simp only [mem_setReg, mem_arithFlags, mem_setFlags, State.setV, State.xmm, ite_true]
    exact writeW_readW128 _ _ _ _
  · simp [gpr_setReg, gpr_arithFlags, hi]
  · simp [gpr_setReg, gpr_arithFlags, zf_arithFlags, hi, hk]
  · intro r h₁; simp [gpr_setReg, gpr_arithFlags, h₁]

/-! ## The loops -/

/-- The first `i` bytes copied, and the registers but `rax`, `r8` and `r10`
kept. -/
structure Copied (s : State) (S D : Addr) (i : Nat) (t : State) : Prop where
  r10 : t.gpr .r10 = BitVec.ofNat 64 i
  mem : t.mem = writeBytes s.mem D (bytesAt s.mem S i)
  keep : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr

/-- What the copy needs, and what it leaves: the `n` bytes at `S` copied to
`D`. -/
def CopyPost (s : State) (S D : Addr) (n : Nat) (s' : State) : Prop :=
  s'.mem = writeBytes s.mem D (bytesAt s.mem S n) ∧
    (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr

section
variable {s : State} {S D : Addr} {n : Nat} (h : CopyPre s S D n)
include h

/-- A loop copying `c` bytes at a time, from byte `c j` to byte `c q`. -/
theorem chunks_ok {body : List Instr} {c : Nat} (hc : 0 < c) (step : StepOk body c) {j q : Nat} (hjq : j < q)
    (hq : c * q ≤ n) {t : State} (ht : Copied s S D (c * j) t) (h8 : t.gpr .r8 = BitVec.ofNat 64 (c * q)) :
    WP isa (.loop (.block body) .ne) t (Copied s S D (c * q)) := by
  have hn63 := h.lt
  refine WP.loop (M := isa) (body := .block body) (c := .ne)
    (fun (k : Nat) (u : State) => ∃ i, k = q - i ∧ i < q ∧ Copied s S D (c * i) u ∧
      u.gpr .r8 = BitVec.ofNat 64 (c * q)) ?_ (q - j) _ ⟨j, rfl, hjq, ht, h8⟩
  rintro k u ⟨i, rfl, hi, hu, r8⟩
  have hic : c * i + c ≤ n := by
    have := Nat.mul_le_mul_left c (show i + 1 ≤ q by omega); rw [Nat.mul_succ] at this; omega
  obtain ⟨u', run', mem', r10', zf', g', rd', wr'⟩ := step u
    (by rw [hu.keep _ (by decide) (by decide) (by decide), h.rsi])
    (by rw [hu.keep _ (by decide) (by decide) (by decide), h.rdi]) hu.r10 r8
    (by rw [hu.rd, hu.wr]; exact h.rd _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base S hic (by omega)⟩)
    (by rw [hu.wr]; exact h.wr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base D hic (by omega)⟩)
  refine WP.of_runBlock ⟨u', run', ?_⟩
  have hlen : (bytesAt s.mem S (c * i)).length = c * i := length_bytesAt _ _ _
  have hsrc : bytesAt u.mem (S + BitVec.ofNat 64 (c * i)) c =
      bytesAt s.mem (S + BitVec.ofNat 64 (c * i)) c := by
    rw [hu.mem]
    refine bytesAt_frame (writeBytes_frame' s.mem hlen) (fun r hr => ?_) (by omega)
    simp only [List.mem_singleton] at hr; subst hr
    exact (h.disj.sub_left (Offset.sub_base S hic)).sub_right (Region.sub_prefix (by omega))
  have hmem : u'.mem = writeBytes s.mem D (bytesAt s.mem S (c * (i + 1))) := by
    rw [mem', hsrc, hu.mem, Nat.mul_succ, bytesAt_add]
    conv => lhs; rw [show D + BitVec.ofNat 64 (c * i) = D + BitVec.ofNat 64 (bytesAt s.mem S (c * i)).length
      by rw [hlen]]
    exact writeBytes_append s.mem D (bytesAt s.mem S (c * i)) (bytesAt s.mem (S + BitVec.ofNat 64 (c * i)) c)
      (by rw [length_bytesAt, length_bytesAt]; omega)
  have hz : u'.zf = some (decide (i + 1 = q)) := by
    rw [zf', ofNat_add_ofNat, sub_beq (by omega) (by omega)]
    congr 1; simp only [decide_eq_decide]
    constructor
    · intro e; exact Nat.eq_of_mul_eq_mul_left hc (by rw [Nat.mul_succ]; exact e)
    · intro e; rw [← e, Nat.mul_succ]
  have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → u'.gpr r = s.gpr r := fun r a b c' => by
    rw [g' r c', hu.keep r a b c']
  have r10'' : u'.gpr .r10 = BitVec.ofNat 64 (c * (i + 1)) := by
    rw [r10', ofNat_add_ofNat, Nat.mul_succ]
  by_cases he : i + 1 = q
  · left
    refine ⟨by simp [eval, hz, he], ⟨by rw [r10'', he], by rw [hmem, he], gg, by rw [rd', hu.rd],
      by rw [wr', hu.wr]⟩⟩
  · right
    refine ⟨by simp [eval, hz, he], q - (i + 1), by omega, i + 1, rfl, by omega,
      ⟨r10'', hmem, gg, by rw [rd', hu.rd], by rw [wr', hu.wr]⟩, by rw [g' _ (by decide), r8]⟩

end

/-! ## The setup and the last bytes -/

theorem shr_ofNat' (n k : Nat) (hn : n < 2 ^ 64) : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)]

/-- The setup: `r10 = 0` and `r8 = c ⌊n / c⌋`, for `c = 2 ^ k`. -/
theorem setup_ok (s : State) {n k : Nat} (hk : 1 ≤ k ∧ k ≤ 63) (hn : s.gpr .rcx = BitVec.ofNat 64 n)
    (hlt : n < 2 ^ 63) :
    WP isa (.block [.mov32 .r10 (imm 0), .mov .r8 (.reg .rcx), .shift .shr .r8 k, .shift .shl .r8 k,
        .alu .cmp .r8 (imm 0)]) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 0 ∧ s'.gpr .r8 = BitVec.ofNat 64 (2 ^ k * (n / 2 ^ k)) ∧
      s'.zf = some (decide (2 ^ k * (n / 2 ^ k) = 0)) ∧
      (∀ r, r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hq : 2 ^ k * (n / 2 ^ k) ≤ n := Nat.mul_div_le n (2 ^ k)
  have e₁ : BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := shr_ofNat' n k (by omega)
  have e₂ : BitVec.ofNat 64 (n / 2 ^ k) <<< k = BitVec.ofNat 64 (2 ^ k * (n / 2 ^ k)) := by
    rw [shl_ofNat (by rw [Nat.mul_comm]; omega), Nat.mul_comm]
  apply WP.of_runBlock
  refine ⟨_, by xrun [execShift, hn, e₁, e₂, hk], ?_⟩
  refine ⟨by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags], by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags],
    ?_, fun r h₁ h₂ => by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, h₁, h₂], rfl, rfl, rfl⟩
  simp only [zf_arithFlags]
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sub_beq (by omega) (by decide)]

section
variable {s : State} {S D : Addr} {n : Nat} (h : CopyPre s S D n)
include h

/-- `copyTail`: from `16 ⌊n / 16⌋` bytes copied, all `n`. -/
theorem copyTail_ok {t : State} (ht : Copied s S D (16 * (n / 16)) t) :
    WP isa copyTail t (CopyPost s S D n) := by
  have hn63 := h.lt
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have hcx : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  refine WP.seq (WP.mono (Q := fun (u : State) => u.zf = some (decide (16 * (n / 16) = n)) ∧ u.gpr = t.gpr ∧
      u.mem = t.mem ∧ u.rd = t.rd ∧ u.wr = t.wr) ?_ fun u ⟨zf₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · apply WP.of_runBlock
    refine ⟨_, by xrun [ht.r10, hcx], ?_⟩
    refine ⟨?_, by simp [gpr_arithFlags], rfl, rfl, rfl⟩
    simp only [zf_arithFlags]; rw [sub_beq (by omega) (by omega)]
  refine WP.ite (decide (16 * (n / 16) = n)) (by simp only [eval, zf₃]) (fun hz => ?_) (fun hz => ?_)
  · have hq' : 16 * (n / 16) = n := of_decide_eq_true hz
    exact WP.block_nil ⟨by rw [m₃, ht.mem, hq'], fun r a b c => by rw [g₃, ht.keep r a b c], by rw [rd₃, ht.rd],
      by rw [wr₃, ht.wr]⟩
  · have hq' : 16 * (n / 16) < n := by have := of_decide_eq_false hz; omega
    refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
      (fun (k : Nat) (v : State) => ∃ i, k = n - i ∧ i < n ∧ v.gpr .r10 = BitVec.ofNat 64 i ∧
        v.mem = writeBytes s.mem D (bytesAt s.mem S i) ∧
        (∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → v.gpr r = s.gpr r) ∧ v.rd = s.rd ∧ v.wr = s.wr) ?_
      (n - 16 * (n / 16)) _
      ⟨16 * (n / 16), rfl, hq', by rw [g₃, ht.r10], by rw [m₃, ht.mem], fun r a b c => by rw [g₃, ht.keep r a b c],
        by rw [rd₃, ht.rd], by rw [wr₃, ht.wr]⟩
    rintro k v ⟨i, rfl, hi, r10, mem, g, rd, wr⟩
    obtain ⟨v', run', mem', r10', zf', g', rd', wr'⟩ := copyStep_ok v
      (by rw [g _ (by decide) (by decide) (by decide), h.rsi])
      (by rw [g _ (by decide) (by decide) (by decide), h.rdi]) r10
      (by rw [g _ (by decide) (by decide) (by decide), h.rcx])
      (by rw [rd, wr]; exact in_of_covers h.rd hi (by omega))
      (by rw [wr]; exact in_of_covers h.wr hi (by omega))
    refine WP.of_runBlock ⟨v', run', ?_⟩
    have hlen : (bytesAt s.mem S i).length = i := length_bytesAt _ _ _
    have hmem : v'.mem = writeBytes s.mem D (bytesAt s.mem S (i + 1)) := by
      rw [mem', mem, src_kept h.disj hi h.lt _ hlen, bytesAt_succ,
        writeBytes_snoc s.mem D (bytesAt s.mem S i) _ (by rw [hlen]; omega), hlen]
    have hz : v'.zf = some (decide (i + 1 = n)) := by
      rw [zf', succ_ofNat, Offset.ofNat_sub_ofNat_beq (by omega) (by omega)]
    have gg : ∀ r, r ≠ .rax → r ≠ .r8 → r ≠ .r10 → v'.gpr r = s.gpr r := fun r a b c => by
      rw [g' r a c, g r a b c]
    by_cases he : i + 1 = n
    · left
      exact ⟨by simp [eval, hz, he], by rw [hmem, he], gg, by rw [rd', rd], by rw [wr', wr]⟩
    · right
      exact ⟨by simp [eval, hz, he], n - (i + 1), by omega, i + 1, rfl, by omega, by rw [r10', succ_ofNat],
        hmem, gg, by rw [rd', rd], by rw [wr', wr]⟩

/-- A loop of `c` bytes at a time, if any, from `r10 = c j` (bytes copied)
to `r8 = c q`, with `zf` telling whether there are none. -/
theorem stage_ok {body : List Instr} {c : Nat} (hc : 0 < c) (step : StepOk body c) {j q : Nat} (hjq : j ≤ q)
    (hq : c * q ≤ n) {t : State} (ht : Copied s S D (c * j) t) (h8 : t.gpr .r8 = BitVec.ofNat 64 (c * q))
    (hz : t.zf = some (decide (c * j = c * q))) :
    WP isa (.ite .e (.block []) (.loop (.block body) .ne)) t (Copied s S D (c * q)) := by
  refine WP.ite (decide (c * j = c * q)) (by simp only [eval, hz]) (fun he => ?_) (fun he => ?_)
  · have e : c * j = c * q := of_decide_eq_true he
    exact WP.block_nil (e ▸ ht)
  · have e : c * j ≠ c * q := of_decide_eq_false he
    exact chunks_ok h hc step (by rcases Nat.lt_or_eq_of_le hjq with hl | hl; exact hl; exact absurd (hl ▸ rfl) e)
      hq ht h8

/-- After a copy of `c = 16 d` bytes at a time: 16 at a time, `vzeroupper`, and
the last bytes. -/
theorem wideRest_ok {d : Nat} {t : State} (ht : Copied s S D (16 * d * (n / (16 * d))) t) :
    WP isa (.seq (.block [.mov .r8 (.reg .rcx), .shift .shr .r8 4, .shift .shl .r8 4, .alu .cmp .r10 (.reg .r8)])
      (.seq (.ite .e (.block []) (.loop (.block vex16Body) .ne))
      (.seq (.block [.vop .vzeroupper]) copyTail))) t (CopyPost s S D n) := by
  have hn63 := h.lt
  have hcx : t.gpr .rcx = BitVec.ofNat 64 n := by rw [ht.keep _ (by decide) (by decide) (by decide), h.rcx]
  rw [Nat.mul_assoc] at ht
  have hj : d * (n / (16 * d)) ≤ n / 16 := by
    rw [Nat.le_div_iff_mul_le (by decide), Nat.mul_comm, ← Nat.mul_assoc]
    exact Nat.mul_div_le n (16 * d)
  have hq : 16 * (n / 16) ≤ n := Nat.mul_div_le n 16
  have e₁ : BitVec.ofNat 64 n >>> 4 = BitVec.ofNat 64 (n / 16) := shr_ofNat' n 4 (by omega)
  have e₂ : BitVec.ofNat 64 (n / 16) <<< 4 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [shl_ofNat (by omega), Nat.mul_comm]
  have hr10 : t.gpr .r10 = BitVec.ofNat 64 (16 * (d * (n / (16 * d)))) := ht.r10
  refine WP.seq (WP.mono (Q := fun (u : State) => Copied s S D (16 * (d * (n / (16 * d)))) u ∧
      u.gpr .r8 = BitVec.ofNat 64 (16 * (n / 16)) ∧
      u.zf = some (decide (16 * (d * (n / (16 * d))) = 16 * (n / 16)))) ?_ fun u ⟨hu, r8, zf⟩ => ?_)
  · apply WP.of_runBlock
    refine ⟨_, by xrun [execShift, hcx, e₁, e₂], ?_⟩
    refine ⟨⟨by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr10], ?_, fun r a b c => ?_, ?_, ?_⟩,
      by simp [gpr_setReg, gpr_setFlags, gpr_arithFlags], ?_⟩
    · exact ht.mem
    · simp [gpr_setReg, gpr_setFlags, gpr_arithFlags, b, ht.keep r a b c]
    · exact ht.rd
    · exact ht.wr
    · simp only [zf_arithFlags, gpr_setReg, gpr_setFlags, gpr_arithFlags]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, ite_false, ite_true, hr10]
      rw [sub_beq (by omega) (by omega)]
  refine WP.seq (WP.mono (stage_ok h (j := d * (n / (16 * d))) (q := n / 16) (by decide) vexStep_ok hj hq hu r8 zf)
    fun v hv => ?_)
  refine WP.seq (WP.mono (Q := Copied s S D (16 * (n / 16))) ?_ fun x hx => copyTail_ok h hx)
  apply WP.of_runBlock
  exact ⟨_, rfl, hv.r10, hv.mem, hv.keep, hv.rd, hv.wr⟩

/-- `copyBytes w`: the `n` bytes at `S` copied to `D`. -/
theorem copyBytes_ok (w : Width) : WP isa (copyBytes w) s (CopyPost s S D n) := by
  have hn63 := h.lt
  have hk : 1 ≤ w.log ∧ w.log ≤ 63 := by cases w <;> decide
  have hc := cbytes_pos w
  have hq : cbytes w * (n / cbytes w) ≤ n := Nat.mul_div_le n _
  refine WP.seq (WP.mono (setup_ok s hk h.rcx h.lt) fun s₁ ⟨r10₁, r8₁, zf₁, g₁, m₁, rd₁, wr₁⟩ => ?_)
  have c₀ : Copied s S D (cbytes w * 0) s₁ :=
    ⟨by rw [r10₁, Nat.mul_zero], by rw [m₁, Nat.mul_zero]; simp [bytesAt, writeBytes_nil],
      fun r _ b c => g₁ r b c, rd₁, wr₁⟩
  refine WP.seq (WP.mono (stage_ok h hc (wideStep_ok w) (Nat.zero_le _) hq c₀ r8₁
    (by rw [zf₁, Nat.mul_zero]; simp only [eq_comm])) fun t ht => ?_)
  cases w with
  | x16 => exact copyTail_ok h ht
  | y32 => exact wideRest_ok h (d := 2) ht
  | z64 => exact wideRest_ok h (d := 4) ht

end

end VG.Proof.ChaCha20Poly1305.X86_64.Gather
