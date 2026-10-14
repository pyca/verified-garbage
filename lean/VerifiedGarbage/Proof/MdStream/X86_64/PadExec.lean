module

public import VerifiedGarbage.Proof.MdStream.X86_64.Words
public import VerifiedGarbage.Proof.MdStream.X86_64.Pad
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.Block
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# Streaming Merkle–Damgård hash functions on x86-64: running the padding

What `finalize`'s padding code (`Impl/MdStream/X86_64.lean`) computes: the
bytes `0, 1, …, 15` (`idxV_ok`), a byte in every byte (`bcast_ok`), and the
first 16 bytes of the padding (`head_ok`).
-/

@[expose] public section

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64 VG.Impl.MdStream.X86_64 VG.X86_64.RegUpd

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_imul {d r : Reg} (k : WP isa (.block is) (execImul d r s) Q) :
    WP isa (.block (.imul d r :: is)) s Q :=
  WP.cons rfl k

theorem wp_movdquLoad {d : XReg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 16) (k : WP isa (.block is) (s.setXmm d (s.mem.readW a 128)) Q) :
    WP isa (.block (.movdquLoad d m :: is)) s Q := by
  refine WP.cons ?_ k
  simp [exec, State.load128, ha, hin]

/-- `mov`, keeping the SSE registers. -/
theorem wp_movX {d r : Reg} (k : ∀ s', Upd s s' d (s.gpr r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

/-- `and` of an immediate, keeping the SSE registers. -/
theorem wp_andiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `add` of an immediate, keeping the SSE registers. -/
theorem wp_addiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d + v.signExtend 64) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `cmp` with an immediate, keeping the SSE registers. -/
theorem wp_cmpiX {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.xmm = s.xmm →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

/-- A 16-byte store, keeping the SSE registers. -/
theorem wp_movdquStoreX {m : MemOp} {r : XReg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 16)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.xmm r) → s'.rd = s.rd →
      s'.wr = s.wr → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.movdquStore m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.xmm r) }) ?_ (k _ rfl rfl rfl rfl rfl)
  simp [exec, State.store128, ha, hout]

/-- `test`, keeping the SSE registers. -/
theorem wp_testX {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → s'.xmm = s.xmm →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

/-- An SSE shift by an immediate count. -/
theorem wp_xshift {op : XShiftOp} {d : XReg} {n : BitVec 8}
    (k : WP isa (.block is) (s.setXmm d (op.eval (s.xmm d) n)) Q) :
    WP isa (.block (.xop (.shift op d n) :: is)) s Q :=
  WP.cons rfl k

/-- `add` of a register, keeping the SSE registers. -/
theorem wp_addX {d r : Reg}
    (k : ∀ s', Upd s s' d (s.gpr d + s.gpr r) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

/-- `bswap`, keeping the SSE registers. -/
theorem wp_bswapX {d : Reg}
    (k : ∀ s', Upd s s' d (bswap64 (s.gpr d)) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl)

/-- `shr`, keeping the SSE registers. -/
theorem wp_shrX {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → s'.xmm = s.xmm → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some (s.gpr d >>> n == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_ rfl)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

end

/-- `imul` by `0x0101010101010101` of a byte. -/
theorem imul_bcast : ∀ b < 256, BitVec.ofInt 64 ((BitVec.ofNat 64 b).toInt * (0x0101010101010101 : BitVec 64).toInt) =
    BitVec.ofNat 64 (b * 0x0101010101010101) := by
  decide +kernel

theorem and15 : ∀ n < 128, BitVec.ofNat 64 n &&& (15 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (n % 16) := by
  decide +kernel

theorem andM16 : ∀ n < 128, BitVec.ofNat 64 n &&& (0xFFFFFFF0 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (16 * (n / 16)) := by
  decide +kernel

/-- `bcast x` puts the byte in `rax` in every byte of `x`. -/
theorem bcast_ok {x : XReg} {b : Nat} (hb : b < 256) {s : State} (hrax : s.gpr .rax = BitVec.ofNat 64 b)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → r ≠ .r10 → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.xmm x = bcastVal b → (∀ y, y ≠ x → s'.xmm y = s.xmm y) → WP isa (.block rest) s' Q) :
    WP isa (.block (bcast x ++ rest)) s Q := by
  simp only [bcast, List.cons_append, List.nil_append]
  refine wp_movImm64' (wp_imul (wp_movqx (wp_xbin (k _ ?_ rfl rfl rfl ?_ ?_))))
  · intro r h1 h2
    simp only [gpr_setXmm, execImul, gpr_setReg_of_ne _ _ h1, gpr_setFlags, gpr_setReg_of_ne _ _ h2]
  · simp only [xmm_setXmm_self, execImul, gpr_setReg_self, gpr_setReg_of_ne _ _ (by decide : ¬ Reg.rax = .r10),
      hrax]
    rw [imul_bcast b hb]
    rfl
  · intro y hy
    simp only [xmm_setXmm_of_ne _ _ hy, execImul, xmm_setReg, xmm_setFlags]

/-- `idxV` puts the bytes `0, 1, …, 15` in `xmm1`. -/
theorem idxV_ok {s : State} {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.xmm .xmm1 = idxVal → (∀ y, y ≠ .xmm1 → y ≠ .xmm2 → s'.xmm y = s.xmm y) → WP isa (.block rest) s' Q) :
    WP isa (.block (idxV ++ rest)) s Q := by
  simp only [idxV, List.cons_append, List.nil_append]
  refine wp_movImm64' (wp_movqx (wp_movImm64' (wp_movqx (wp_xbin (k _ ?_ rfl rfl rfl ?_ ?_)))))
  · intro r h
    simp only [gpr_setXmm, gpr_setReg_of_ne _ _ h]
  · simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm1 = .xmm2), gpr_setReg_self,
      xmm_setReg]
    rfl
  · intro y h1 h2
    simp only [xmm_setXmm_of_ne _ _ h1, xmm_setXmm_of_ne _ _ h2, xmm_setReg]

/-- The address of buffer byte `r13`. -/
theorem ea_bufByte (P : Params) (s : State) {c : Nat} (h13 : s.gpr .r13 = BitVec.ofNat 64 c) :
    s.ea (bufByte P) = s.gpr .rbx + BitVec.ofNat 64 (P.N + c) := by
  simp only [State.ea, bufByte, h13, BitVec.mul_one, ofInt_natCast, BitVec.ofNat_add]
  ac_rfl

/-- `head` leaves in `xmm0` the first 16 bytes of the padding: those of the
buffer at `n` rounded down to a multiple of 16, with the bytes before `n`
kept, `mk` at `n` and zeros after it. -/
theorem head_ok (P : Params) {s : State} {n mk : Nat} (hn : n < 128) (hmk : mk < 256)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (h9 : s.gpr .r9 = BitVec.ofNat 64 mk)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rbx + BitVec.ofNat 64 (P.N + 16 * (n / 16))) 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r13 → s'.gpr r = s.gpr r) →
      s'.gpr .r13 = BitVec.ofNat 64 (16 * (n / 16)) → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      (∀ i < 16, byte (s'.xmm .xmm0) i = if i < n % 16 then
        s.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + 16 * (n / 16) + i))
        else if i = n % 16 then BitVec.ofNat 8 mk else 0) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (head P ++ rest)) s Q := by
  simp only [head, List.append_assoc, List.cons_append, List.nil_append]
  refine idxV_ok fun s₁ g₁ m₁ rd₁ wr₁ x1₁ xo₁ => ?_
  refine wp_movX fun s₂ u₂ x₂ => wp_andiX fun s₃ u₃ x₃ => ?_
  have hrax₃ : s₃.gpr .rax = BitVec.ofNat 64 (n % 16) := by
    rw [u₃.gpr, u₂.gpr, g₁ _ (by decide), h13, and15 n hn]
  refine bcast_ok (x := .xmm3) (by omega) hrax₃ fun s₄ g₄ m₄ rd₄ wr₄ x3₄ xo₄ => ?_
  refine wp_movX fun s₅ u₅ x₅ => ?_
  have hrax₅ : s₅.gpr .rax = BitVec.ofNat 64 mk := by
    rw [u₅.gpr, g₄ _ (by decide) (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      g₁ _ (by decide), h9]
  refine bcast_ok (x := .xmm4) hmk hrax₅ fun s₆ g₆ m₆ rd₆ wr₆ x4₆ xo₆ => ?_
  refine wp_xbin (wp_xbin (wp_xbin (wp_xbin (wp_andiX fun s₇ u₇ x₇ => ?_))))
  have keep₆ : ∀ r, r ≠ .rax → r ≠ .r10 → s₆.gpr r = s.gpr r := fun r h1 h2 => by
    rw [g₆ r h1 h2, u₅.other r h1, g₄ r h1 h2, u₃.other r h1, u₂.other r h1, g₁ r h1]
  have h13₇ : s₇.gpr .r13 = BitVec.ofNat 64 (16 * (n / 16)) := by
    rw [u₇.gpr, gpr_setXmm, gpr_setXmm, gpr_setXmm, gpr_setXmm, keep₆ _ (by decide) (by decide), h13,
      andM16 n hn]
  have hrbx₇ : s₇.gpr .rbx = s.gpr .rbx := by
    rw [u₇.other _ (by decide), gpr_setXmm, gpr_setXmm, gpr_setXmm, gpr_setXmm, keep₆ _ (by decide) (by decide)]
  have hm₇ : s₇.mem = s.mem := by
    rw [u₇.mem, mem_setXmm, mem_setXmm, mem_setXmm, mem_setXmm, m₆, u₅.mem, m₄, u₃.mem, u₂.mem, m₁]
  have hrd₇ : s₇.rd = s.rd := by
    rw [u₇.rd, rd_setXmm, rd_setXmm, rd_setXmm, rd_setXmm, rd₆, u₅.rd, rd₄, u₃.rd, u₂.rd, rd₁]
  have hwr₇ : s₇.wr = s.wr := by
    rw [u₇.wr, wr_setXmm, wr_setXmm, wr_setXmm, wr_setXmm, wr₆, u₅.wr, wr₄, u₃.wr, u₂.wr, wr₁]
  have ea₇ : s₇.ea (bufByte P) = s.gpr .rbx + BitVec.ofNat 64 (P.N + 16 * (n / 16)) := by
    rw [ea_bufByte P s₇ h13₇, hrbx₇]
  refine wp_movdquLoad ea₇ (by rw [hrd₇, hwr₇]; exact hin) (wp_xbin (wp_xbin (k _ ?_ ?_ ?_ ?_ ?_ ?_)))
  · intro r h1 h2 h3
    rw [gpr_setXmm, gpr_setXmm, gpr_setXmm, u₇.other r h3, gpr_setXmm, gpr_setXmm, gpr_setXmm, gpr_setXmm,
      keep₆ r h1 h2]
  · rw [gpr_setXmm, gpr_setXmm, gpr_setXmm, h13₇]
  · rw [mem_setXmm, mem_setXmm, mem_setXmm, hm₇]
  · rw [rd_setXmm, rd_setXmm, rd_setXmm, hrd₇]
  · rw [wr_setXmm, wr_setXmm, wr_setXmm, hwr₇]
  intro i hi
  -- The SSE registers along the block.
  have x1₆ : s₆.xmm .xmm1 = idxVal := by
    rw [xo₆ _ (by decide), x₅, xo₄ _ (by decide), x₃, x₂, x1₁]
  have x3₆ : s₆.xmm .xmm3 = bcastVal (n % 16) := by rw [xo₆ _ (by decide), x₅, x3₄]
  have mv : ∀ a b : BitVec 128, XBinOp.movdqa.eval a b = b := fun _ _ => rfl
  simp only [xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm3 = .xmm0),
    xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm5 = .xmm0), xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm5 = .xmm3),
    xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm3 = .xmm5), xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm1 = .xmm5),
    xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm4 = .xmm3), xmm_setXmm_of_ne _ _ (by decide : ¬ XReg.xmm4 = .xmm5),
    x₇, x1₆, x3₆, x4₆, hm₇, mv]
  rw [head_byte _ (Nat.mod_lt _ (by decide)) hmk hi, byte, byte_readW _ _ (by omega), add_ofNat]

/-- A byte after a 16-byte write at `p + e`. -/
theorem writeW128_at (m : Mem) (p : Addr) (v : BitVec 128) {e i : Nat} (he : e + 16 < 2 ^ 63)
    (hi : i < 2 ^ 63) :
    (m.writeW (p + BitVec.ofNat 64 e) v) (p + BitVec.ofNat 64 i) =
      if e ≤ i ∧ i < e + 16 then byte v (i - e) else m (p + BitVec.ofNat 64 i) := by
  split
  · rename_i h
    rw [show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 e + BitVec.ofNat 64 (i - e) by
      rw [add_ofNat, Nat.add_sub_cancel' h.1]]
    exact writeW_byte _ _ _ (by omega) (by decide)
  · rename_i h
    refine writeW_byte_off _ _ _ _ ?_
    rw [Offset.sub_toNat' p (by omega) (by omega)]
    split <;> omega

/-- The loop's invariant after `j` 16-byte stores from `c`: the first stored
`v`, the others zeros. -/
structure CInv (P : Params) (s : State) (c j : Nat) (s' : State) : Prop where
  lt : c + 16 * j < P.B - 16
  r13 : s'.gpr .r13 = BitVec.ofNat 64 (c + 16 * j)
  gpr : ∀ r, r ≠ .r13 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ x, x ≠ .xmm0 → s'.xmm x = s.xmm x
  x0 : s'.xmm .xmm0 = if j = 0 then s.xmm .xmm0 else 0
  frame : Frame [⟨s.gpr .rbx + BitVec.ofNat 64 (P.N + c), 16 * j⟩] s.mem s'.mem
  bytes : ∀ i, c ≤ i → i < c + 16 * j →
    s'.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + i)) = if i < c + 16 then byte (s.xmm .xmm0) (i - c) else 0

/-- `chunks` stores `xmm0` at the buffer's byte `c` and zeros after it, up to
its last 16 bytes. -/
theorem chunks_ok (P : Params) (hB : P.B = 64 ∨ P.B = 128) (hN : P.N ≤ 64) {s : State} {c : Nat}
    (hc : c + 16 ≤ P.B) (hc16 : c % 16 = 0) (h13 : s.gpr .r13 = BitVec.ofNat 64 c)
    (hout : ∀ e, e + 16 ≤ P.B → InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (P.N + e)) 16)
    {Q : State → Prop}
    (k : ∀ s', (∀ r, r ≠ .r13 → s'.gpr r = s.gpr r) → s'.gpr .r13 = BitVec.ofNat 64 (P.B - 16) →
      s'.rd = s.rd → s'.wr = s.wr → (∀ x, x ≠ .xmm0 → s'.xmm x = s.xmm x) →
      s'.xmm .xmm0 = (if c = P.B - 16 then s.xmm .xmm0 else 0) →
      Frame [⟨s.gpr .rbx + BitVec.ofNat 64 (P.N + c), P.B - 16 - c⟩] s.mem s'.mem →
      (∀ i, c ≤ i → i < P.B - 16 → s'.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + i)) =
        if i < c + 16 then byte (s.xmm .xmm0) (i - c) else 0) →
      Q s') :
    WP isa (chunks P) s Q := by
  have hB' : P.B ≤ 128 := by omega
  unfold chunks
  refine WP.seq (wp_cmpiX fun s₁ g₁ m₁ rd₁ wr₁ x₁ cf₁ => WP.block_nil ?_)
  have e16 : (BitVec.ofNat 32 (P.B - 16)).signExtend 64 = BitVec.ofNat 64 (P.B - 16) := sx_ofNat (by omega)
  have hcf₁ : s₁.cf = some (decide (c < P.B - 16)) := by
    rw [cf₁, h13, e16, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
  refine WP.ite (!decide (c < P.B - 16)) (by simp [eval, hcf₁]) (fun hb => ?_) (fun hb => ?_)
  · -- `c` is the last 16 bytes: nothing to store.
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    have hc' : c = P.B - 16 := by omega
    refine WP.block_nil (k s₁ (fun r _ => by rw [g₁]) (by rw [g₁, h13, hc']) rd₁ wr₁ (fun x _ => by rw [x₁])
      (by simp [hc', x₁]) (by rw [m₁, hc', Nat.sub_self]; exact Frame.refl _ _) fun i h1 h2 => by omega)
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    have hI₀ : CInv P s c 0 s₁ := ⟨by omega, by rw [g₁, h13]; rfl, fun r _ => by rw [g₁], rd₁, wr₁,
      fun _ _ => by rw [x₁], by simp [x₁], by rw [m₁, Nat.mul_zero]; exact Frame.refl _ _, fun i h1 h2 => by omega⟩
    refine WP.loop (M := isa) (fun m t => ∃ j, m = P.B - c - 16 * j ∧ CInv P s c j t) ?_ _ s₁ ⟨0, rfl, hI₀⟩
    rintro m t ⟨j, rfl, hI⟩
    have hlt := hI.lt
    have ea : t.ea (bufByte P) = s.gpr .rbx + BitVec.ofNat 64 (P.N + (c + 16 * j)) := by
      rw [ea_bufByte P t hI.r13, hI.gpr _ (by decide)]
    refine wp_movdquStoreX ea (by rw [hI.wr]; exact hout _ (by omega)) fun t₁ g₁ m₁ rd₁ wr₁ xs₁ => ?_
    refine wp_xbin (wp_addiX fun t₂ u₂ x₂ => wp_cmpiX fun t₃ g₃ m₃ rd₃ wr₃ x₃ cf₃ => WP.block_nil ?_)
    have s16 : (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 16 := by decide
    have a16 : BitVec.ofNat 64 (c + 16 * j) + (16 : BitVec 32).signExtend 64 = BitVec.ofNat 64 (c + 16 * (j + 1)) := by
      rw [s16, ← BitVec.ofNat_add, show c + 16 * j + 16 = c + 16 * (j + 1) by omega]
    have h13₃ : t₃.gpr .r13 = BitVec.ofNat 64 (c + 16 * (j + 1)) := by
      rw [g₃, u₂.gpr, gpr_setXmm, g₁, hI.r13, a16]
    have hcf₃ : t₃.cf = some (decide (c + 16 * (j + 1) < P.B - 16)) := by
      rw [cf₃, u₂.gpr, gpr_setXmm, g₁, hI.r13, a16, e16, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by omega)]
    have hm₃ : t₃.mem = t.mem.writeW (s.gpr .rbx + BitVec.ofNat 64 (P.N + (c + 16 * j))) (t.xmm .xmm0) := by
      rw [m₃, u₂.mem, mem_setXmm, m₁]
    have hg₃ : ∀ r, r ≠ .r13 → t₃.gpr r = s.gpr r := fun r h => by
      rw [g₃, u₂.other r h, gpr_setXmm, g₁, hI.gpr r h]
    have hx₃ : ∀ x, x ≠ .xmm0 → t₃.xmm x = s.xmm x := fun x h => by
      rw [x₃, x₂, xmm_setXmm_of_ne _ _ h, xs₁, hI.xmm x h]
    have hx0₃ : t₃.xmm .xmm0 = 0 := by
      have px : ∀ a : BitVec 128, XBinOp.pxor.eval a a = 0 := fun a => BitVec.xor_self
      rw [x₃, x₂, xmm_setXmm_self, px]
    have hfr₃ : Frame [⟨s.gpr .rbx + BitVec.ofNat 64 (P.N + c), 16 * (j + 1)⟩] s.mem t₃.mem := by
      rw [hm₃]
      refine (hI.frame.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩).writeW (List.mem_singleton_self _) _ ?_
      · simp only [List.mem_singleton] at hr; subst hr; exact Region.sub_prefix (by omega)
      · exact Offset.contains (s.gpr .rbx) (d := P.N + (c + 16 * j)) (n := 128 / 8) (e := P.N + c)
          (k := 16 * (j + 1)) (by omega) (by omega) (by omega)
    have hby₃ : ∀ i, c ≤ i → i < c + 16 * (j + 1) →
        t₃.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + i)) = if i < c + 16 then byte (s.xmm .xmm0) (i - c) else 0 := by
      intro i h1 h2
      rw [hm₃, writeW128_at _ _ _ (by omega) (by omega)]
      split
      · rename_i h
        rw [hI.x0]
        by_cases hj : j = 0
        · subst hj
          simp only [ite_true, Nat.mul_zero, Nat.add_zero] at h ⊢
          simp only [show i < c + 16 by omega, ↓reduceIte, show P.N + i - (P.N + c) = i - c by omega]
        · have h' : ¬ i < c + 16 := by omega
          simp only [hj, h', ↓reduceIte, byte]
          exact BitVec.extractLsb'_zero
      · exact hI.bytes i h1 (by omega)
    by_cases hlast : c + 16 * (j + 1) < P.B - 16
    · refine .inr ⟨by simp [eval, hcf₃, hlast], P.B - c - 16 * (j + 1), by omega, j + 1, rfl,
        ⟨hlast, h13₃, hg₃, by rw [rd₃, u₂.rd, rd_setXmm, rd₁, hI.rd], by rw [wr₃, u₂.wr, wr_setXmm, wr₁, hI.wr], hx₃,
          by rw [hx0₃]; simp, hfr₃, hby₃⟩⟩
    · have he : c + 16 * (j + 1) = P.B - 16 := by omega
      have hfr : Frame [⟨s.gpr .rbx + BitVec.ofNat 64 (P.N + c), P.B - 16 - c⟩] s.mem t₃.mem := by
        rw [show P.B - 16 - c = 16 * (j + 1) by omega]; exact hfr₃
      exact .inl ⟨by simp [eval, hcf₃, hlast], k t₃ hg₃ (by rw [h13₃, he]) (by rw [rd₃, u₂.rd, rd_setXmm, rd₁, hI.rd])
        (by rw [wr₃, u₂.wr, wr_setXmm, wr₁, hI.wr]) hx₃ (by rw [hx0₃]; simp only [show ¬ (c = P.B - 16) by omega, ↓reduceIte]) hfr
        (fun i h1 h2 => hby₃ i h1 (by omega))⟩

/-- The length part of the last 16 bytes of a block: the length field in its
last `L` bytes, in the last block (`k = 0`). -/
def lenPart (P : Params) (k : Nat) (lv : List Byte) (j : Nat) : Byte :=
  if k = 0 then (List.replicate (16 - P.L) 0 ++ lv).getD j 0 else 0

theorem byte_zero (j : Nat) : byte 0 j = 0 := BitVec.extractLsb'_zero

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) {a b : α} : (if c then a else b) = a :=
  by simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} : (if c then a else b) = b :=
  by simp [h]

/-- Below the length field, the length part is zero. -/
theorem lenPart_low (P : Params) (k : Nat) (lv : List Byte) {j : Nat} (hj : j < 16 - P.L) :
    lenPart P k lv j = 0 := by
  unfold lenPart
  split
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
    simp [hj]
  · rfl

theorem or_zero_byte (x : Byte) : x ||| 0 = x := BitVec.or_zero
theorem zero_or_byte (x : Byte) : 0 ||| x = x := BitVec.zero_or

/-- `finalizePad` writes the block to compress: the `n` bytes buffered, `mk`,
zeros, and in the last block (`k = 0`) the length field `lv` of `count`. -/
theorem pad_exec (P : Params) (hB : P.B = 64 ∨ P.B = 128) (hN : P.N ≤ 64) (hL : 0 < P.L ∧ P.L ≤ 16)
    (lv : BitVec 64 → List Byte)
    (hlv : ∀ s : State, WP isa (.block P.lenV) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.xmm .xmm0 = s.xmm .xmm0 ∧
      vbytes (s'.xmm .xmm7) = List.replicate (16 - P.L) 0 ++ lv (s.gpr .r12))
    {s : State} {n mk k : Nat} (hk : k ≤ 1) (hn : n < (if k = 0 then P.B - P.L else P.B)) (hmk : mk < 256)
    (h13 : s.gpr .r13 = BitVec.ofNat 64 n) (h9 : s.gpr .r9 = BitVec.ofNat 64 mk)
    (h14 : s.gpr .r14 = BitVec.ofNat 64 k)
    (hout : ∀ e, e + 16 ≤ P.B → InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (P.N + e)) 16)
    {Q : State → Prop}
    (kont : ∀ s', (∀ r, r ≠ .rax → r ≠ .r10 → r ≠ .r13 → r ≠ .rsi → s'.gpr r = s.gpr r) →
      s'.gpr .rsi = s.gpr .rbx + BitVec.ofNat 64 P.N → s'.rd = s.rd → s'.wr = s.wr →
      Frame [⟨s.gpr .rbx + BitVec.ofNat 64 P.N, P.B⟩] s.mem s'.mem →
      (∀ i < P.B, s'.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + i)) =
        if i < n then s.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + i))
        else if i = n then BitVec.ofNat 8 mk
        else if P.B - 16 ≤ i then lenPart P k (lv (s.gpr .r12)) (i - (P.B - 16)) else 0) →
      Q s') :
    WP isa (finalizePad P) s Q := by
  have hB' : P.B ≤ 128 := by omega
  have hn' : n < P.B := by split at hn <;> omega
  have hc : 16 * (n / 16) + 16 ≤ P.B := by omega
  unfold finalizePad
  -- The first 16 bytes.
  refine WP.seq ?_
  rw [← List.append_nil (head P)]
  refine head_ok P (by omega) hmk h13 h9 ?_ fun s₁ g₁ h13₁ m₁ rd₁ wr₁ x0₁ => WP.block_nil ?_
  · obtain ⟨R, hR, hc'⟩ := hout _ hc
    exact ⟨R, List.mem_append_right _ hR, hc'⟩
  have hrbx₁ : s₁.gpr .rbx = s.gpr .rbx := g₁ _ (by decide) (by decide) (by decide)
  -- The 16 bytes after them, up to the last.
  refine WP.seq (chunks_ok P hB hN hc (by omega) h13₁ (fun e he => by rw [wr₁, hrbx₁]; exact hout e he)
    fun s₂ g₂ h13₂ rd₂ wr₂ xo₂ x0₂ fr₂ by₂ => ?_)
  have hrbx₂ : s₂.gpr .rbx = s.gpr .rbx := by rw [g₂ _ (by decide), hrbx₁]
  -- The length field.
  refine WP.seq (wp_testX fun s₃ g₃ m₃ rd₃ wr₃ x₃ z₃ => WP.block_nil ?_)
  have hz₃ : s₃.zf = some (decide (k = 0)) := by
    rw [z₃, g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide), h14, BitVec.and_self,
      ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => (∀ r, r ≠ .rax → s₄.gpr r = s₃.gpr r) ∧ s₄.mem = s₃.mem ∧
      s₄.rd = s₃.rd ∧ s₄.wr = s₃.wr ∧ ∀ j < 16,
        byte (s₄.xmm .xmm0) j = byte (s₃.xmm .xmm0) j ||| lenPart P k (lv (s.gpr .r12)) j) ?_
    fun s₄ ⟨g₄, m₄, rd₄, wr₄, x0₄⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₃]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      subst hb
      rw [WP.block_append_iff]
      refine WP.mono (hlv s₃) fun s₄ ⟨g, rd, wr, m, x0, x7⟩ => wp_xbin (WP.block_nil ⟨fun r h => ?_, ?_, ?_, ?_, ?_⟩)
      · rw [gpr_setXmm, g r h]
      · rw [mem_setXmm, m]
      · rw [rd_setXmm, rd]
      · rw [wr_setXmm, wr]
      · intro j hj
        have hr12 : s₃.gpr .r12 = s.gpr .r12 := by
          rw [g₃, g₂ _ (by decide), g₁ _ (by decide) (by decide) (by decide)]
        have e7 : byte (s₄.xmm .xmm7) j = (List.replicate (16 - P.L) 0 ++ lv (s.gpr .r12)).getD j 0 := by
          rw [← hr12, ← x7, ← List.getElem_eq_getD (h := by rw [vbytes_length]; exact hj) 0, vbytes_getElem]
        rw [xmm_setXmm_self, show XBinOp.por.eval (s₄.xmm .xmm0) (s₄.xmm .xmm7) =
          s₄.xmm .xmm0 ||| s₄.xmm .xmm7 from rfl, byte_or, x0, e7]
        simp only [lenPart, ↓reduceIte]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨fun r _ => rfl, rfl, rfl, rfl, fun j _ => ?_⟩
      simp only [lenPart, hb, ↓reduceIte, or_zero_byte]
  -- The last 16 bytes, and the block's address.
  have hrbx₄ : s₄.gpr .rbx = s.gpr .rbx := by rw [g₄ _ (by decide), g₃, hrbx₂]
  have ea : s₄.ea (at_ .rbx (P.N + P.B - 16)) = s.gpr .rbx + BitVec.ofNat 64 (P.N + (P.B - 16)) := by
    rw [ea_at, hrbx₄, ofInt_natCast, show P.N + P.B - 16 = P.N + (P.B - 16) by omega]
  refine wp_movdquStore ea (by rw [wr₄, wr₃, wr₂, wr₁]; exact hout _ (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_mov fun s₆ u₆ _ _ => wp_addi fun s₇ u₇ => WP.block_nil ?_
  refine kont s₇ (fun r h1 h2 h3 h4 => ?_) ?_ ?_ ?_ ?_ ?_
  · rw [u₇.other r h4, u₆.other r h4, g₅, g₄ r h1, g₃, g₂ r h3, g₁ r h1 h2 h3]
  · rw [u₇.gpr, u₆.gpr, g₅, hrbx₄, sx_ofNat (by omega)]
  · rw [u₇.rd, u₆.rd, rd₅, rd₄, rd₃, rd₂, rd₁]
  · rw [u₇.wr, u₆.wr, wr₅, wr₄, wr₃, wr₂, wr₁]
  · -- Only the buffer changes.
    have fr₂' : Frame [⟨s.gpr .rbx + BitVec.ofNat 64 P.N, P.B⟩] s.mem s₂.mem := by
      rw [← m₁]
      refine fr₂.sub fun r hr => ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [List.mem_singleton] at hr; subst hr
      rw [hrbx₁]
      exact Offset.sub _ (by omega) (by omega)
    rw [u₇.mem, u₆.mem, m₅, m₄, m₃]
    refine fr₂'.writeW (List.mem_singleton_self _) _ ?_
    exact Offset.contains (s.gpr .rbx) (d := P.N + (P.B - 16)) (n := 128 / 8) (e := P.N) (k := P.B)
      (by omega) (by omega) (by omega)
  · intro i hi
    rw [u₇.mem, u₆.mem, m₅, m₄, m₃, writeW128_at _ _ _ (by omega) (by omega)]
    have x0₃ : s₃.xmm .xmm0 = if 16 * (n / 16) = P.B - 16 then s₁.xmm .xmm0 else 0 := by rw [x₃, x0₂]
    have hlow : ∀ j, j < 16 → P.B - 16 + j ≤ n → lenPart P k (lv (s.gpr .r12)) j = 0 := by
      intro j hj hle
      by_cases hk0 : k = 0
      · exact lenPart_low P k _ (by subst hk0; simp at hn; omega)
      · simp [lenPart, hk0]
    split
    · -- The last 16 bytes.
      rename_i hl
      rw [x0₄ _ (by omega), x0₃, show P.N + i - (P.N + (P.B - 16)) = i - (P.B - 16) by omega]
      split
      · rename_i hcl
        rw [x0₁ _ (by omega)]
        by_cases h1 : i < n
        · rw [ite_t (by omega : i - (P.B - 16) < n % 16), ite_t h1, hlow _ (by omega) (by omega), or_zero_byte,
            show P.N + 16 * (n / 16) + (i - (P.B - 16)) = P.N + i by omega]
        · by_cases h2 : i = n
          · subst h2
            rw [ite_f (by omega), ite_t (by omega), ite_f h1, ite_t rfl, hlow _ (by omega) (by omega), or_zero_byte]
          · rw [ite_f (by omega), ite_f (by omega), ite_f h1, ite_f h2, ite_t (by omega), zero_or_byte]
      · rw [byte_zero, zero_or_byte, ite_f (by omega), ite_f (by omega), ite_t (by omega)]
    · rename_i hl
      by_cases hci : 16 * (n / 16) ≤ i
      · have b := by₂ i hci (by omega)
        rw [hrbx₁] at b
        rw [b]
        split
        · rw [x0₁ _ (by omega)]
          by_cases h1 : i < n
          · rw [ite_t (by omega : i - 16 * (n / 16) < n % 16), ite_t h1,
              show P.N + 16 * (n / 16) + (i - 16 * (n / 16)) = P.N + i by omega]
          · by_cases h2 : i = n
            · subst h2; rw [ite_f (by omega), ite_t (by omega), ite_f h1, ite_t rfl]
            · rw [ite_f (by omega), ite_f (by omega), ite_f h1, ite_f h2, ite_f (by omega)]
        · rw [ite_f (by omega), ite_f (by omega), ite_f (by omega)]
      · have hfr := fr₂.bytes (R := ⟨s₁.gpr .rbx + BitVec.ofNat 64 (P.N + i), 1⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (.inl (by omega)) (by omega) (by omega)) (by show 1 ≤ 2 ^ 64; decide) (i := 0) (by show 0 < 1; decide)
        have z : ∀ x : BitVec 64, x + BitVec.ofNat 64 0 = x := fun x => by simp
        simp only [z] at hfr
        rw [hrbx₁] at hfr
        rw [hfr, m₁, ite_t (by omega)]

/-! ## The length field, in the last 16 bytes -/

/-- The 16 bytes of two quadwords. -/
theorem vbytes_append (hi lo : BitVec 64) :
    vbytes (hi ++ lo) = (List.range 8).map (fun j => lo.extractLsb' (8 * j) 8) ++
      (List.range 8).map (fun j => hi.extractLsb' (8 * j) 8) := by
  simp only [vbytes, byte, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append]
  simp (disch := decide) only [Nat.reduceMul, Nat.reduceSub, BitVec.extractLsb'_append_eq_of_le,
    BitVec.extractLsb'_append_eq_of_add_le]

theorem pslldq8 (w : BitVec 64) : XShiftOp.pslldq.eval ((0 : BitVec 64) ++ w) 8 = w ++ (0 : BitVec 64) := by
  simp only [XShiftOp.eval]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp [h]
  · have h' : i - 64 < 64 := by omega
    simp [h, hi, h']

theorem punpck0 (hi lo : BitVec 64) :
    XBinOp.punpcklqdq.eval ((0 : BitVec 64) ++ hi) ((0 : BitVec 64) ++ lo) = lo ++ hi := by
  simp (disch := decide) only [XBinOp.eval, qword, Nat.mul_zero, BitVec.extractLsb'_append_eq_of_add_le,
    BitVec.extractLsb'_eq_self]

theorem bytes_zero64 : (List.range 8).map (fun j => (0 : BitVec 64).extractLsb' (8 * j) 8) = List.replicate 8 0 := by
  decide

/-- `lenV64 be` puts `8 · count` in the last 8 of the 16 bytes of `xmm7`. -/
theorem lenV64_ok (be : Bool) (s : State) :
    WP isa (.block (lenV64 be)) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.xmm .xmm0 = s.xmm .xmm0 ∧
      vbytes (s'.xmm .xmm7) = List.replicate 8 0 ++ bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .r12).toNat)) := by
  unfold lenV64
  simp only [List.cons_append, List.nil_append]
  refine wp_movX fun s₁ u₁ x₁ => wp_addX fun s₂ u₂ x₂ => wp_addX fun s₃ u₃ x₃ => wp_addX fun s₄ u₄ x₄ => ?_
  have g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s.gpr r := fun r h => by
    rw [u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  have v₄ : s₄.gpr .rax = BitVec.ofNat 64 (8 * (s.gpr .r12).toNat) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, times8]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have xm₄ : s₄.xmm = s.xmm := by rw [x₄, x₃, x₂, x₁]
  cases be
  · simp only [Bool.false_eq_true, ite_false, List.nil_append]
    refine wp_movqx (wp_xshift (WP.block_nil ⟨fun r h => ?_, by rw [rd_setXmm, rd_setXmm, rd₄],
      by rw [wr_setXmm, wr_setXmm, wr₄], ?_, ?_, ?_⟩))
    · rw [gpr_setXmm, gpr_setXmm, g₄ r h]
    · rw [mem_setXmm, mem_setXmm, m₄]
    · rw [xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_of_ne _ _ (by decide), xm₄]
    · rw [xmm_setXmm_self, xmm_setXmm_self]
      rw [v₄, pslldq8, vbytes_append, bytes_zero64, ← bytes64_store false]
      rfl
  · simp only [ite_true, List.cons_append, List.nil_append]
    refine wp_bswapX fun s₅ u₅ x₅ => wp_movqx (wp_xshift (WP.block_nil ⟨fun r h => ?_, ?_, ?_, ?_, ?_, ?_⟩))
    · rw [gpr_setXmm, gpr_setXmm, u₅.other r h, g₄ r h]
    · rw [rd_setXmm, rd_setXmm, u₅.rd, rd₄]
    · rw [wr_setXmm, wr_setXmm, u₅.wr, wr₄]
    · rw [mem_setXmm, mem_setXmm, u₅.mem, m₄]
    · rw [xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_of_ne _ _ (by decide), x₅, xm₄]
    · rw [xmm_setXmm_self, xmm_setXmm_self]
      rw [u₅.gpr, v₄, pslldq8, vbytes_append, bytes_zero64, ← bytes64_store true]
      rfl

/-- `lenV128` puts `count >> 61` and `8 · count`, big-endian, in the 16 bytes of `xmm7`. -/
theorem lenV128_ok (s : State) :
    WP isa (.block lenV128) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = s.mem ∧ s'.xmm .xmm0 = s.xmm .xmm0 ∧
      vbytes (s'.xmm .xmm7) = bytes64 true (s.gpr .r12 >>> 61) ++
        bytes64 true (BitVec.ofNat 64 (8 * (s.gpr .r12).toNat)) := by
  unfold lenV128
  refine wp_movX fun s₁ u₁ x₁ => wp_shrX (by decide) fun s₂ u₂ x₂ => wp_bswapX fun s₃ u₃ x₃ => wp_movqx ?_
  refine wp_movX fun s₄ u₄ x₄ => wp_addX fun s₅ u₅ x₅ => wp_addX fun s₆ u₆ x₆ => wp_addX fun s₇ u₇ x₇ => ?_
  refine wp_bswapX fun s₈ u₈ x₈ => wp_movqx (wp_xbin (WP.block_nil ⟨fun r h => ?_, ?_, ?_, ?_, ?_, ?_⟩))
  · rw [gpr_setXmm, gpr_setXmm, u₈.other r h, u₇.other r h, u₆.other r h, u₅.other r h, u₄.other r h,
      gpr_setXmm, u₃.other r h, u₂.other r h, u₁.other r h]
  · rw [rd_setXmm, rd_setXmm, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd_setXmm, u₃.rd, u₂.rd, u₁.rd]
  · rw [wr_setXmm, wr_setXmm, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr_setXmm, u₃.wr, u₂.wr, u₁.wr]
  · rw [mem_setXmm, mem_setXmm, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, mem_setXmm, u₃.mem, u₂.mem, u₁.mem]
  · rw [xmm_setXmm_of_ne _ _ (by decide), xmm_setXmm_of_ne _ _ (by decide), x₈, x₇, x₆, x₅, x₄,
      xmm_setXmm_of_ne _ _ (by decide), x₃, x₂, x₁]
  · have hr12 : s₃.gpr .r12 = s.gpr .r12 := by
      rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
    rw [xmm_setXmm_self, xmm_setXmm_of_ne _ _ (by decide), x₈, x₇, x₆, x₅, x₄, xmm_setXmm_self, xmm_setXmm_self,
      u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr, u₄.gpr, gpr_setXmm, hr12, times8, u₃.gpr, u₂.gpr, u₁.gpr,
      punpck0, vbytes_append, ← bytes64_store true, ← bytes64_store true]
    rfl

/-- The block `pad_exec` describes, as a list: the bytes `g` before `n`, then
`mk`, zeros, and in the last block (`k = 0`) the length field `lb`. -/
theorem pad_list {B L n k : Nat} {g : Nat → Byte} {mk : Byte} {lb : List Byte} (hlb : lb.length = L)
    (hL : L ≤ 16) (hB : 16 ≤ B) (hk : k ≤ 1) (hn : n < if k = 0 then B - L else B) :
    (List.range B).map (fun i => if i < n then g i else if i = n then mk else if B - 16 ≤ i then
      (if k = 0 then (List.replicate (16 - L) 0 ++ lb).getD (i - (B - 16)) 0 else 0) else 0) =
      (List.range n).map g ++ [mk] ++
        (if k = 1 then List.replicate (B - 1 - n) 0 else List.replicate (B - L - 1 - n) 0 ++ lb) := by
  have hn' : n < B := by split at hn <;> omega
  apply List.ext_getElem
  · by_cases hk1 : k = 1
    · simp [hk1]; omega
    · have hk0 : k = 0 := by omega
      simp [hk0] at hn ⊢; omega
  · intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_append, List.length_append, List.length_map,
      List.length_range, List.length_singleton]
    by_cases hi : i < n
    · simp [hi, show i < n + 1 by omega]
    · by_cases he : i = n
      · subst he; simp
      · have hgt : ¬ i < n + 1 := by omega
        simp only [hi, he, hgt, ↓reduceIte, dite_false]
        by_cases hk1 : k = 1
        · subst hk1; simp
        · have hk0 : k = 0 := by omega
          subst hk0
          simp only [show ¬ ((0 : Nat) = 1) by decide, ↓reduceIte, List.getElem_append, List.length_replicate]
          by_cases hb : B - 16 ≤ i
          · simp only [hb, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_replicate]
            by_cases hl : i - (n + 1) < B - L - 1 - n
            · have : i - (B - 16) < 16 - L := by simp at hn; omega
              simp [hl, this]
            · have : ¬ i - (B - 16) < 16 - L := by simp at hn; omega
              simp only [hl, this, dite_false, ↓reduceIte]
              simp at hn
              rw [List.getElem?_eq_getElem (by omega)]
              simp only [Option.getD_some]
              congr 1; omega
          · have hl : i - (n + 1) < B - L - 1 - n := by simp at hn; omega
            simp [hb, hl]

end VG.Proof.MdStream.X86_64
