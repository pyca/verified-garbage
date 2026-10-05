import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Poly1305.X86_64.Blocks
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Poly1305.Contract

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Buffer`. -/
section

section

/-!
# Poly1305 on x86-64: one instruction at a time

Weakest-precondition rules for the instruction forms of the byte loops and the
counts of `update` and `finalize`, exposing only what changes, and facts about
the counters.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : VG.Proof.Poly1305.X86_64.Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.withFlags (s : State) (cf o zf sf : Option Bool) (d : Reg) (v : BitVec 64) :
    VG.Proof.Poly1305.X86_64.Upd s ((s.setFlags cf o zf sf).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, State.setFlags, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    VG.Proof.Poly1305.X86_64.Upd s ((arithFlags s x c o).setReg d v) d v :=
  Upd.withFlags _ _ _ _ _ _ _

theorem Upd.trans {s₁ s₂ s₃ : State} {d : Reg} {v w : BitVec 64} (h₁ : VG.Proof.Poly1305.X86_64.Upd s₁ s₂ d v)
    (h₂ : VG.Proof.Poly1305.X86_64.Upd s₂ s₃ d w) : VG.Proof.Poly1305.X86_64.Upd s₁ s₃ d w :=
  ⟨h₂.gpr, fun r h => (h₂.other r h).trans (h₁.other r h), h₂.mem.trans h₁.mem,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', VG.Proof.Poly1305.X86_64.Upd s s' d (s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Poly1305.X86_64.Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_mov32i {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Poly1305.X86_64.Upd s s' d (v.setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.Poly1305.X86_64.Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.Poly1305.X86_64.Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

theorem wp_sub {d r : Reg}
    (k : ∀ s', VG.Proof.Poly1305.X86_64.Upd s s' d (s.gpr d - s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

end

end VG.Proof.Poly1305.X86_64

end

/-!
# Poly1305 on x86-64: the buffer

Bytes stored into the buffer (bytes 56–71 of the state), absorbing the buffer
as a block, and a message with its last bytes buffered (`Buffered`) as its
whole blocks and the rest.
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P leNum bytesAt Repr Buffered)

/-! ## Bytes in memory -/

theorem off_56 (p : Addr) : off p 56 = p + 56 := by rw [off_eq]; rfl

/-! ## The buffer -/

/-- Byte `k` of the buffer. -/
abbrev bufB (st : Addr) (k : Nat) : Addr := st + BitVec.ofNat 64 (56 + k)

theorem bufB_eq (st : Addr) (k : Nat) : VG.Proof.Poly1305.X86_64.bufB st k = off st 56 + BitVec.ofNat 64 k := by
  rw [off_eq, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The address `[rdi + i + 56]`, for `i = j`. -/
theorem ea_bufAt (s : State) (i : Reg) {j : Nat} (h : s.gpr i = BitVec.ofNat 64 j) :
    s.ea (bufAt i) = VG.Proof.Poly1305.X86_64.bufB (s.gpr .rdi) j := by
  simp only [State.ea, bufAt, h]
  rw [BitVec.mul_one, show BitVec.ofInt 64 56 = BitVec.ofNat 64 56 by decide, VG.Proof.Poly1305.X86_64.bufB,
    Offset.add_add, Nat.add_comm]

theorem bfR_contains (st : Addr) {d n : Nat} (h : d + n ≤ 16) :
    (bfR st).Contains (off st 56 + BitVec.ofNat 64 d) n := by
  exact Offset.contains_base _ h (by omega_using [h])

theorem bufB_ne {st : Addr} {j k : Nat} (hj : j < 16) (hk : k < 16) (h : j ≠ k) :
    VG.Proof.Poly1305.X86_64.bufB st j ≠ VG.Proof.Poly1305.X86_64.bufB st k := by
  intro he
  have := congrArg BitVec.toNat (show BitVec.ofNat 64 (56 + j) = BitVec.ofNat 64 (56 + k) by
    simpa [VG.Proof.Poly1305.X86_64.bufB] using he)
  rw [toNat_ofNat_lt (by omega_using [hj]), toNat_ofNat_lt (by omega_using [hk])] at this
  omega_using [h, this]

/-- The buffer is writable when the state is. -/
theorem bufB_in {s : State} (hw : sR (s.gpr .rdi) ∈ s.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (VG.Proof.Poly1305.X86_64.bufB (s.gpr .rdi) k) 1 :=
  ⟨_, hw, by rw [VG.Proof.Poly1305.X86_64.bufB, ← ofInt_natCast]; exact contains_off (by omega_using [hk]) (by omega_using [hk])⟩

/-- The saved registers are not in the buffer. -/
theorem Saved.of_frame {st : Addr} {s₀ : State} {m m' : Mem} (h : Saved st s₀ m) (hf : Frame [bfR st] m m') :
    Saved st s₀ m' := by
  have e : ∀ d, 72 ≤ d → d + 8 ≤ 128 → m'.readW (off st d) 64 = m.readW (off st d) 64 := by
    intro d h₁ h₂
    refine hf.readW (r := ⟨off st d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq, bfR, off, ofInt_natCast]
    exact Offset.disjoint st (by omega_using [h₁, h₂]) (by omega_using [h₁, h₂]) (by decide)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨(e 72 (by decide) (by decide)).trans h1, (e 80 (by decide) (by decide)).trans h2,
    (e 88 (by decide) (by decide)).trans h3, (e 96 (by decide) (by decide)).trans h4,
    (e 104 (by decide) (by decide)).trans h5, (e 112 (by decide) (by decide)).trans h6⟩

theorem bfR_disjoint_svR (st : Addr) : (bfR st).Disjoint (svR st) := by
  simp only [bfR, svR, off, ofInt_natCast]
  exact Offset.disjoint st (by decide) (by decide) (by decide)

/-- The first `n` bytes of the buffer are not where the registers are saved. -/
theorem buf_disjoint_svR (st : Addr) {n : Nat} (hn : n ≤ 16) :
    (⟨off st 56, n⟩ : Region).Disjoint (svR st) :=
  (VG.Proof.Poly1305.X86_64.bfR_disjoint_svR st).sub_left (Region.sub_prefix hn)

theorem bfR_sub_wR (st : Addr) : Region.Sub (bfR st) (wR st) := by
  simp only [bfR, wR, off, ofInt_natCast]
  exact Offset.sub st (by decide) (by decide)

/-- Absorbing the buffer: its 16 bytes, and `pad · 2¹²⁸`. -/
theorem absorbBuf_ok (s : State) {pad : BitVec 32} (hpad : pad = 0 ∨ pad = 1)
    (hw : sR (s.gpr .rdi) ∈ s.wr) {q : Nat} (hr0 : (s.gpr .r8).toNat < 2 ^ 60)
    (hr1 : (s.gpr .r9).toNat = 4 * q) (hq : q < 2 ^ 58) (hs1 : (s.gpr .r10).toNat = 5 * q) :
    WP isa (.block (absorbAt .rdi 56 pad)) s fun s' =>
      ((s.gpr .rbp).toNat ≤ 4 →
        hval s' % P = ((hval s + (leNum (bytesAt s.mem (off (s.gpr .rdi) 56) 16) + 2 ^ 128 * pad.toNat)) *
          ((s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat)) % P ∧
        (s'.gpr .rbp).toNat ≤ 4) ∧ Keeps absorbRegs s s' := by
  have hin : ∀ d : Nat, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hw, contains_off hd (by omega_using [hd])⟩
  refine WP.mono (absorbAt_ok s (b := .rdi) (d := 56) (by decide) hpad hr0 hr1 hq hs1 (hin 56 (by decide))
    (hin (56 + 8) (by decide))) fun s' ⟨ha, k⟩ => ⟨fun hb => ?_, k⟩
  obtain ⟨hv, hb'⟩ := ha hb
  refine ⟨?_, hb'⟩
  rw [hv, leNum_key, off_off, off_off]

/-! ## Instructions -/

theorem and15 (x : BitVec 64) :
    x &&& BitVec.signExtend 64 (15 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.signExtend 64 (15 : BitVec 32)).toNat = 2 ^ 4 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x.toNat % 16) (by omega_using [])]

theorem se16' : BitVec.signExtend 64 (16 : BitVec 32) = BitVec.ofNat 64 16 := by decide

/-! ## Copying bytes into the buffer -/

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.movzx8 .r13 (at_ .rsi 0), .store8 (bufAt .r12) .r13, .alu .add .rsi (.imm 1),
    .alu .add .r12 (.imm 1), .alu .sub .rax (.imm 1)]

theorem copyIn_eq : copyIn = .loop (.block VG.Proof.Poly1305.X86_64.copyBody) .ne := rfl

/-- While copying the `n` bytes at `src`, as in the memory `m₀`, to the buffer
from byte `j0` on, from the state `sI`: after `j` bytes. -/
structure CopyInv (sI : State) (m₀ : Mem) (src : Addr) (j0 n j : Nat) (s : State) : Prop where
  j_le : j ≤ n
  rsi : s.gpr .rsi = src + BitVec.ofNat 64 j
  r12 : s.gpr .r12 = BitVec.ofNat 64 (j0 + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (n - j)
  keep : ∀ r, r ≠ .rsi → r ≠ .r12 → r ≠ .rax → r ≠ .r13 → s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  mem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.Poly1305.X86_64.bufB (sI.gpr .rdi) j0) ((bytesAt m₀ src n).take j)

/-- What copying needs of the source: its bytes are readable, not in the
buffer, and as in `m₀`. -/
def SrcOk (sI : State) (m₀ : Mem) (src : Addr) (n : Nat) : Prop :=
  ∀ i < n, InRegions (sI.rd ++ sI.wr) (src + BitVec.ofNat 64 i) 1 ∧
    ¬ (bfR (sI.gpr .rdi)).Contains (src + BitVec.ofNat 64 i) 1 ∧
    sI.mem (src + BitVec.ofNat 64 i) = m₀ (src + BitVec.ofNat 64 i)

theorem ofNat_add_one (a : Addr) (j : Nat) :
    a + BitVec.ofNat 64 j + BitVec.signExtend 64 (1 : BitVec 32) = a + BitVec.ofNat 64 (j + 1) := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, ofNat_succ, BitVec.add_assoc]

theorem copy_step {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16)
    (hw : sR (sI.gpr .rdi) ∈ sI.wr) (hs : VG.Proof.Poly1305.X86_64.SrcOk sI m₀ src n) {j : Nat} (hj : j < n) {s : State}
    (h : VG.Proof.Poly1305.X86_64.CopyInv sI m₀ src j0 n j s) :
    WP isa (.block VG.Proof.Poly1305.X86_64.copyBody) s fun s' =>
      VG.Proof.Poly1305.X86_64.CopyInv sI m₀ src j0 n (j + 1) s' ∧ s'.zf = some (decide (n - (j + 1) = 0)) := by
  obtain ⟨hin, hnb, hm₀⟩ := hs j hj
  have hrdi : s.gpr .rdi = sI.gpr .rdi := h.keep _ (by decide) (by decide) (by decide) (by decide)
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have hq : (bfR (sI.gpr .rdi)).Contains (VG.Proof.Poly1305.X86_64.bufB (sI.gpr .rdi) j0) ((bytesAt m₀ src n).take j).length := by
    rw [VG.Proof.Poly1305.X86_64.bufB_eq, List.length_take]; exact VG.Proof.Poly1305.X86_64.bfR_contains _ (by omega_using [hj0, hj, hxs])
  -- The byte read.
  have hbyte : s.mem (src + BitVec.ofNat 64 j) = m₀ (src + BitVec.ofNat 64 j) := by
    rw [h.mem, ← hm₀]
    exact VG.WriteBytes.writeBytes_frame _ _ _ hq _ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hnb
  refine VG.Proof.Poly1305.X86_64.wp_movzx8 (d := .r13) (a := src + BitVec.ofNat 64 j)
    (by rw [ea_at, h.rsi, ofInt_natCast, BitVec.add_zero]) (by rw [h.rd, h.wr]; exact hin)
    fun s₁ u₁ => ?_
  refine VG.Proof.Poly1305.X86_64.wp_store8 (r := .r13) (a := VG.Proof.Poly1305.X86_64.bufB (sI.gpr .rdi) (j0 + j))
    (by rw [VG.Proof.Poly1305.X86_64.ea_bufAt s₁ .r12 (by rw [u₁.other _ (by decide), h.r12]), u₁.other _ (by decide), hrdi])
    (by rw [u₁.wr, h.wr]; exact VG.Proof.Poly1305.X86_64.bufB_in hw (by omega_using [hj0, hj, hxs])) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine VG.Proof.Poly1305.X86_64.wp_addi fun s₃ u₃ => VG.Proof.Poly1305.X86_64.wp_addi fun s₄ u₄ => VG.Proof.Poly1305.X86_64.wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r12 → r ≠ .rsi → r ≠ .r13 → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, g₂, u₁.other r h4]
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have hrax : s₅.gpr .rax = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [u₅.gpr, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax,
      e1, ofNat_pred (by omega_using [hj, hxs]), Nat.sub_sub]
  refine ⟨⟨by omega_using [hj, hxs], ?_, ?_, hrax, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₅.other .rsi (by decide), u₄.other .rsi (by decide), u₃.gpr, g₂, u₁.other .rsi (by decide), h.rsi,
      VG.Proof.Poly1305.X86_64.ofNat_add_one]
  · rw [u₅.other .r12 (by decide), u₄.gpr, u₃.other .r12 (by decide), g₂, u₁.other .r12 (by decide), h.r12,
      e1, ← Nat.add_assoc, ofNat_succ]
  · rw [g r h3 h2 h1 h4, h.keep r h1 h2 h3 h4]
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
  · have hj' : j < (bytesAt m₀ src n).length := by omega_using [hj, hxs]
    have hl : ((bytesAt m₀ src n).take j).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    have ea : VG.Proof.Poly1305.X86_64.bufB (sI.gpr .rdi) (j0 + j) =
        VG.Proof.Poly1305.X86_64.bufB (sI.gpr .rdi) j0 + BitVec.ofNat 64 ((bytesAt m₀ src n).take j).length := by
      rw [hl, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc]
    have hv : (BitVec.setWidth 64 (s.mem (src + BitVec.ofNat 64 j))).setWidth 8 = (bytesAt m₀ src n)[j] := by
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq, hbyte]; simp [bytesAt]
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hv, ea, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some, VG.WriteBytes.writeBytes_snoc _ _ _ _ (by omega_using [hj0, hj, hxs, hl])]
  · rw [hz₅, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax, e1,
      ofNat_pred (by omega_using [hj, hxs]), ofNat_beq_zero (by omega_using [hj0, hj, hxs]), show n - j - 1 = n - (j + 1) by omega_using []]

theorem copy_ok {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) (hn : 0 < n)
    (hw : sR (sI.gpr .rdi) ∈ sI.wr) (hs : VG.Proof.Poly1305.X86_64.SrcOk sI m₀ src n) (hrsi : sI.gpr .rsi = src)
    (hr12 : sI.gpr .r12 = BitVec.ofNat 64 j0) (hrax : sI.gpr .rax = BitVec.ofNat 64 n) :
    WP isa copyIn sI (VG.Proof.Poly1305.X86_64.CopyInv sI m₀ src j0 n n) := by
  have h₀ : VG.Proof.Poly1305.X86_64.CopyInv sI m₀ src j0 n 0 sI :=
    ⟨by omega_using [hn], by rw [hrsi]; simp, by rw [hr12]; simp, by rw [hrax]; simp, fun _ _ _ _ _ => rfl, rfl, rfl,
      by rw [List.take_zero, VG.WriteBytes.writeBytes_nil]⟩
  rw [VG.Proof.Poly1305.X86_64.copyIn_eq]
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ VG.Proof.Poly1305.X86_64.CopyInv sI m₀ src j0 n j s)
    ?_ n sI ⟨0, rfl, hn, h₀⟩
  rintro k s ⟨j, rfl, hj, hc⟩
  refine WP.mono (VG.Proof.Poly1305.X86_64.copy_step hj0 hw hs hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : n - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = n by omega_using [hj, hl]] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], hc'⟩

/-- After copying: the buffer's first `j0` bytes and the `n` bytes copied. -/
theorem CopyInv.buf {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : VG.Proof.Poly1305.X86_64.CopyInv sI m₀ src j0 n n s) :
    bytesAt s.mem (off (sI.gpr .rdi) 56) (j0 + n) = bytesAt sI.mem (off (sI.gpr .rdi) 56) j0 ++ bytesAt m₀ src n := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  have e := bytesAt_writeBytes sI.mem (off (sI.gpr .rdi) 56) j0 (bytesAt m₀ src n) (by omega_using [hj0, hxs])
  rw [hxs] at e
  rw [h.mem, List.take_of_length_le (by omega_using [hxs]), VG.Proof.Poly1305.X86_64.bufB_eq]
  exact e

theorem CopyInv.frame {sI : State} {m₀ : Mem} {src : Addr} {j0 n : Nat} (hj0 : j0 + n ≤ 16) {s : State}
    (h : VG.Proof.Poly1305.X86_64.CopyInv sI m₀ src j0 n n s) : Frame [bfR (sI.gpr .rdi)] sI.mem s.mem := by
  have hxs : (bytesAt m₀ src n).length = n := Poly1305.length_bytesAt _ _ _
  rw [h.mem, List.take_of_length_le (by omega_using [hxs])]
  refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
  rw [VG.Proof.Poly1305.X86_64.bufB_eq, hxs]; exact VG.Proof.Poly1305.X86_64.bfR_contains _ hj0

/-- The proof contracts of `update` and `finalize` only need the length
of the message modulo 16. -/
theorem count_mod {count : BitVec 64} {n : Nat} (h : count = BitVec.ofNat 64 n) :
    count.toNat % 16 = n % 16 := by
  rw [h, BitVec.toNat_ofNat]; omega_using []

end VG.Proof.Poly1305.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.Poly1305.X86_64.Finalize`. -/
section

/-!
# Poly1305 on x86-64: `finalize`
-/

open VG.Proof.Poly1305.Limbs64

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr Buffered leBytes mac)

/-- The buffer's bytes are `f k`. -/
def BufHas (m : Mem) (st : Addr) (f : Nat → Byte) : Prop := ∀ k < 16, m (VG.Proof.Poly1305.X86_64.bufB st k) = f k

/-- The bytes of the buffer, as read from memory. -/
theorem bytesAt_buf {m : Mem} {st : Addr} {f : Nat → Byte} (h : VG.Proof.Poly1305.X86_64.BufHas m st f) :
    bytesAt m (off st 56) 16 = (List.range 16).map f := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro k hk
  rw [← h k (List.mem_range.mp hk), VG.Proof.Poly1305.X86_64.bufB_eq]

/-! ## The precondition -/

section
variable (s₀ : State)
/-- The number of bytes buffered. -/
abbrev kf : Nat := (s₀.gpr .rsi).toNat % 16
abbrev op : Addr := s₀.gpr .rdx
abbrev oR : Region := ⟨VG.Proof.Poly1305.X86_64.op s₀, 16⟩
/-- The bytes buffered. -/
abbrev tail : List Byte := bytesAt s₀.mem (off (st s₀) 56) (VG.Proof.Poly1305.X86_64.kf s₀)
end

structure FPre (s₀ : State) : Prop where
  st_in : sR (st s₀) ∈ s₀.wr
  o_in : VG.Proof.Poly1305.X86_64.oR s₀ ∈ s₀.wr
  st_o : (sR (st s₀)).Disjoint (VG.Proof.Poly1305.X86_64.oR s₀)
  ret_st : (retR s₀).Disjoint (sR (st s₀))
  ret_o : (retR s₀).Disjoint (VG.Proof.Poly1305.X86_64.oR s₀)

theorem FPre.of (s₀ : State) (h : Proof.Poly1305.finalizeX86_64.pre s₀) : VG.Proof.Poly1305.X86_64.FPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem kf_lt (s₀ : State) : VG.Proof.Poly1305.X86_64.kf s₀ < 16 := Nat.mod_lt _ (by decide)

/-! ## Prologue -/

/-- The state after the prologue, with the memory `m₁` it leaves. -/
structure F0 (s₀ : State) (m₁ : Mem) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.rdi, .rsp], s.gpr r = s₀.gpr r
  rcx : s.gpr .rcx = VG.Proof.Poly1305.X86_64.op s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kf s₀)
  r8 : s.gpr .r8 = R0 s₀
  r9 : s.gpr .r9 = R1 s₀
  r10 : (s.gpr .r10).toNat = 5 * ((R1 s₀).toNat / 4)
  hv : hval s = A0 s₀
  rbp : (s.gpr .rbp).toNat = H2 s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = m₁

set_option simprocs false in
theorem args_ok (s : State) :
    WP isa (.block [.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)]) s fun s' =>
      s'.gpr .rcx = s.gpr .rdx ∧ s'.gpr .rdx = BitVec.ofNat 64 ((s.gpr .rsi).toNat % 16) ∧
      Keeps [.rcx, .rdx] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, ite_true, ite_false, Option.bind_some,
    Option.map_some, Option.some.injEq, exists_eq_left', VG.Proof.Poly1305.X86_64.and15]
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [hr.1, hr.2]

theorem fprologue_eq : [Instr.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)] ++
    save ++ setup ++ ([.alu .test .rdx (.reg .rdx)] : List Instr) =
    [Instr.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)] ++
    (save ++ (setup ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) := by
  simp only [List.append_assoc]

theorem fprologue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) :
    WP isa (.block (([.mov .rcx (.reg .rdx), .mov .rdx (.reg .rsi), .alu .and .rdx (.imm 15)] : List Instr) ++ save ++
      setup ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s₀ fun s =>
      ∃ m₁, Mem₁ s₀ m₁ ∧ VG.Proof.Poly1305.X86_64.F0 s₀ m₁ s ∧
        s.zf = some (BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kf s₀) &&& BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kf s₀) == 0) := by
  rw [VG.Proof.Poly1305.X86_64.fprologue_eq]
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.args_ok s₀) fun s₁ ⟨c₁, d₁, k₁⟩ => ?_)
  have rdi₁ : s₁.gpr .rdi = st s₀ := k₁.gpr'
  have hw₁ : sR (s₁.gpr .rdi) ∈ s₁.wr := by rw [k₁.2.2.2, rdi₁]; exact hp.st_in
  refine WP.block_append (WP.mono (save_ok s₁ hw₁) fun s₂ ⟨g₂, rd₂, wr₂, _, _, f₂, sv₂⟩ => ?_)
  refine WP.block_append (WP.mono (setup_ok s₂ (by
    rw [wr₂, g₂]; exact List.mem_append_right _ hw₁))
    fun s₃ ⟨e8, e9, e10, e11, e12, e13, k₃⟩ => ?_)
  refine WP.mono (test_ok s₃ .rdx) fun s₄ ⟨z₄, k₄⟩ => ?_
  -- The callee-saved registers are those on entry: `args` does not write them.
  have sv : Saved (st s₀) s₀ s₂.mem := by
    rw [← rdi₁]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := sv₂
    exact ⟨a1.trans k₁.gpr', a2.trans k₁.gpr', a3.trans k₁.gpr', a4.trans k₁.gpr', a5.trans k₁.gpr',
      a6.trans k₁.gpr'⟩
  have hm : Mem₁ s₀ s₂.mem := ⟨by rw [← rdi₁, ← k₁.2.1]; exact f₂, sv⟩
  have k := k₃.trans k₄
  rw [g₂, rdi₁, hm.readW_low (by decide)] at e8 e9 e11 e12 e13
  refine ⟨s₂.mem, hm, ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> rw [k.gpr', g₂, k₁.gpr']
  · rw [k.gpr' (r := .rcx), g₂, c₁]
  · rw [k.gpr' (r := .rdx), g₂, d₁]
  · rw [k₄.gpr' (r := .r8), e8]
  · rw [k₄.gpr' (r := .r9), e9]
  · rw [k₄.gpr' (r := .r10), e10, e9]
  · simp only [hval, k₄.gpr' (r := .r11), k₄.gpr' (r := .rbx), k₄.gpr' (r := .rbp), e11, e12, e13]
    rw [A0, leNum_acc]
  · rw [k₄.gpr' (r := .rbp), e13]
  · rw [k.2.2.1, rd₂, k₁.2.2.1]
  · rw [k.2.2.2, wr₂, k₁.2.2.2]
  · rw [k.2.1]
  · rw [z₄, k₃.gpr' (r := .rdx), g₂, d₁]

/-! ## Padding the buffer in place -/

/-- The padded block: the buffered bytes, `0x01`, zeros. -/
def padded (s₀ : State) (k : Nat) : Byte :=
  if k < VG.Proof.Poly1305.X86_64.kf s₀ then (VG.Proof.Poly1305.X86_64.tail s₀).getD k 0 else if k = VG.Proof.Poly1305.X86_64.kf s₀ then 1 else 0

/-- The buffered bytes in the memory the prologue leaves. -/
theorem Mem₁.tail {s₀ : State} {m₁ : Mem} (hm : Mem₁ s₀ m₁) {k : Nat} (hk : k < VG.Proof.Poly1305.X86_64.kf s₀) :
    m₁ (VG.Proof.Poly1305.X86_64.bufB (st s₀) k) = (VG.Proof.Poly1305.X86_64.tail s₀).getD k 0 := by
  have hkl := VG.Proof.Poly1305.X86_64.kf_lt s₀
  simp only [bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some]
  rw [← VG.Proof.Poly1305.X86_64.bufB_eq]
  refine hm.frame _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  simp only [svR, off, ofInt_natCast] at hc
  exact Offset.disjoint (st s₀) (d := 56 + k) (n := 1) (by omega_using [hk, hkl]) (by omega_using [hk, hkl]) (by decide) _
    (Region.contains_self _ _) hc

/-- The zero loop's invariant, before byte `j`, from the state `s₁` after the
prologue. -/
structure ZInv (s₀ : State) (m₁ : Mem) (s₁ : State) (j : Nat) (s : State) : Prop where
  j_le : VG.Proof.Poly1305.X86_64.kf s₀ ≤ j ∧ j ≤ 16
  r12 : s.gpr .r12 = BitVec.ofNat 64 j
  rax : s.gpr .rax = 0
  keep : ∀ r, r ≠ .rax → r ≠ .r12 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  buf : VG.Proof.Poly1305.X86_64.BufHas s.mem (st s₀) fun k =>
    if k < VG.Proof.Poly1305.X86_64.kf s₀ then (VG.Proof.Poly1305.X86_64.tail s₀).getD k 0 else if k < j then 0 else m₁ (VG.Proof.Poly1305.X86_64.bufB (st s₀) k)

theorem zinit_ok {s₀ : State} {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State} (h₁ : VG.Proof.Poly1305.X86_64.F0 s₀ m₁ s₁) :
    WP isa (.block [.mov32 .rax (.imm 0), .mov .r12 (.reg .rdx)]) s₁ (VG.Proof.Poly1305.X86_64.ZInv s₀ m₁ s₁ (VG.Proof.Poly1305.X86_64.kf s₀)) := by
  refine VG.Proof.Poly1305.X86_64.wp_mov32i fun s₂ u₂ => VG.Proof.Poly1305.X86_64.wp_mov fun s₃ u₃ => WP.block_nil ?_
  refine ⟨⟨(Nat.le_refl _), Nat.le_of_lt (VG.Proof.Poly1305.X86_64.kf_lt s₀)⟩, by rw [u₃.gpr, u₂.other _ (by decide), h₁.rdx], by
    rw [u₃.other _ (by decide), u₂.gpr]; rfl, fun r h1 h2 => by rw [u₃.other r h2, u₂.other r h1],
    by rw [u₃.rd, u₂.rd, h₁.rd], by rw [u₃.wr, u₂.wr, h₁.wr],
    by rw [u₃.mem, u₂.mem, h₁.mem]; exact Frame.refl _ _, fun k hk => ?_⟩
  rw [u₃.mem, u₂.mem, h₁.mem]
  by_cases hkf : k < VG.Proof.Poly1305.X86_64.kf s₀
  · simp only [hkf, ite_true]; exact hm.tail hkf
  · simp only [hkf, ite_false]

theorem FPre.buf_in {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) {s : State} (hwr : s.wr = s₀.wr) {k : Nat} (hk : k < 16) :
    InRegions s.wr (VG.Proof.Poly1305.X86_64.bufB (st s₀) k) 1 := by
  rw [hwr]
  exact ⟨_, hp.st_in, by rw [VG.Proof.Poly1305.X86_64.bufB, ← ofInt_natCast]; exact contains_off (by omega_using [hk]) (by omega_using [hk])⟩

theorem zero_step {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : VG.Proof.Poly1305.X86_64.F0 s₀ m₁ s₁) {j : Nat}
    (hj : j < 16) {s : State} (h : VG.Proof.Poly1305.X86_64.ZInv s₀ m₁ s₁ j s) :
    WP isa (.block [.store8 (bufAt .r12) .rax, .alu .add .r12 (.imm 1), .alu .cmp .r12 (.imm 16)]) s
      fun s' => VG.Proof.Poly1305.X86_64.ZInv s₀ m₁ s₁ (j + 1) s' ∧ s'.zf = some (decide (j + 1 = 16)) := by
  have hrdi : s.gpr .rdi = st s₀ := by
    rw [h.keep _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  refine VG.Proof.Poly1305.X86_64.wp_store8 (r := .rax) (a := VG.Proof.Poly1305.X86_64.bufB (st s₀) j) (by rw [VG.Proof.Poly1305.X86_64.ea_bufAt s .r12 h.r12, hrdi])
    (hp.buf_in h.wr hj) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine VG.Proof.Poly1305.X86_64.wp_addi fun s₃ u₃ => VG.Proof.Poly1305.X86_64.wp_cmpi fun s₄ g₄ m₄ rd₄ wr₄ _ z₄ => WP.block_nil ?_
  have hr12 : s₃.gpr .r12 = BitVec.ofNat 64 (j + 1) := by
    rw [u₃.gpr, g₂, h.r12, show BitVec.signExtend 64 (1 : BitVec 32) = 1 by decide, ofNat_succ]
  refine ⟨⟨⟨Nat.le_trans h.j_le.1 (Nat.le_succ _), by omega_using [hj]⟩, by rw [g₄, hr12], by
      rw [g₄, u₃.other _ (by decide), g₂, h.rax], fun r h1 h2 => by
      rw [g₄, u₃.other r h2, g₂, h.keep r h1 h2], by rw [rd₄, u₃.rd, rd₂, h.rd],
      by rw [wr₄, u₃.wr, wr₂, h.wr], ?_, fun k hk => ?_⟩, ?_⟩
  · rw [m₄, u₃.mem, m₂]
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [VG.Proof.Poly1305.X86_64.bufB_eq]; exact VG.Proof.Poly1305.X86_64.bfR_contains _ (by omega_using [hj]))
  · rw [m₄, u₃.mem, m₂, VG.WriteBytes.writeW8_apply]
    by_cases hkj : k = j
    · subst hkj
      simp only [ite_true, h.rax, show ¬ k < VG.Proof.Poly1305.X86_64.kf s₀ by have := h.j_le.1; omega_using [this],
        show k < k + 1 by omega_using [], ite_false]
      rfl
    · simp only [VG.Proof.Poly1305.X86_64.bufB_ne hk hj hkj, ite_false]
      rw [h.buf k hk]
      by_cases h1 : k < VG.Proof.Poly1305.X86_64.kf s₀
      · simp only [h1, ite_true]
      · simp only [h1, ite_false]
        by_cases h2 : k < j
        · simp only [h2, ite_true, show k < j + 1 by omega_using [h2]]
        · simp only [h2, ite_false, show ¬ k < j + 1 by omega_using [hkj, h2]]
  · rw [z₄, hr12, VG.Proof.Poly1305.X86_64.se16', sub_beq (by omega_using [hj]) (by decide)]

theorem zeroLoop_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : VG.Proof.Poly1305.X86_64.F0 s₀ m₁ s₁) {s : State}
    (h : VG.Proof.Poly1305.X86_64.ZInv s₀ m₁ s₁ (VG.Proof.Poly1305.X86_64.kf s₀) s) : WP isa zeroLoop s (VG.Proof.Poly1305.X86_64.ZInv s₀ m₁ s₁ 16) := by
  have hk := VG.Proof.Poly1305.X86_64.kf_lt s₀
  refine WP.loop (M := isa) (fun n s => ∃ j, n = 16 - j ∧ j < 16 ∧ VG.Proof.Poly1305.X86_64.ZInv s₀ m₁ s₁ j s) ?_ _ s
    ⟨VG.Proof.Poly1305.X86_64.kf s₀, rfl, hk, h⟩
  rintro n s ⟨j, rfl, hj, hz⟩
  refine WP.mono (VG.Proof.Poly1305.X86_64.zero_step hp h₁ hj hz) fun s' ⟨h', hz'⟩ => ?_
  by_cases hl : j + 1 = 16
  · exact .inl ⟨by simp [eval, hz', hl], hl ▸ h'⟩
  · exact .inr ⟨by simp [eval, hz', hl], _, by omega_using [hj], j + 1, rfl, by omega_using [hj, hl], h'⟩

/-- After the `0x01` byte. -/
structure PInv (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r, r ≠ .rax → r ≠ .r12 → s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  buf : VG.Proof.Poly1305.X86_64.BufHas s.mem (st s₀) (VG.Proof.Poly1305.X86_64.padded s₀)

theorem pad1_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) {m₁ : Mem} {s₁ : State} (h₁ : VG.Proof.Poly1305.X86_64.F0 s₀ m₁ s₁) {s : State}
    (h : VG.Proof.Poly1305.X86_64.ZInv s₀ m₁ s₁ 16 s) :
    WP isa (.block [.mov32 .rax (.imm 1), .store8 (bufAt .rdx) .rax]) s (VG.Proof.Poly1305.X86_64.PInv s₀ m₁ s₁) := by
  have hk := VG.Proof.Poly1305.X86_64.kf_lt s₀
  have hrdi : s.gpr .rdi = st s₀ := by
    rw [h.keep _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  refine VG.Proof.Poly1305.X86_64.wp_mov32i fun s₂ u₂ => ?_
  refine VG.Proof.Poly1305.X86_64.wp_store8 (r := .rax) (a := VG.Proof.Poly1305.X86_64.bufB (st s₀) (VG.Proof.Poly1305.X86_64.kf s₀))
    (by rw [VG.Proof.Poly1305.X86_64.ea_bufAt s₂ .rdx (by rw [u₂.other _ (by decide), h.keep _ (by decide) (by decide), h₁.rdx]),
      u₂.other _ (by decide), hrdi])
    (by rw [u₂.wr]; exact hp.buf_in h.wr hk) fun s₃ g₃ m₃ rd₃ wr₃ => WP.block_nil ?_
  refine ⟨fun r h1 h2 => by rw [g₃, u₂.other r h1, h.keep r h1 h2], by rw [rd₃, u₂.rd, h.rd],
    by rw [wr₃, u₂.wr, h.wr], ?_, fun k hk' => ?_⟩
  · rw [m₃, u₂.mem]
    exact h.frame.writeW (List.mem_singleton_self _) _ (by rw [VG.Proof.Poly1305.X86_64.bufB_eq]; exact VG.Proof.Poly1305.X86_64.bfR_contains _ (by omega_using [hk]))
  · rw [m₃, u₂.mem, VG.WriteBytes.writeW8_apply, u₂.gpr]
    by_cases hkj : k = VG.Proof.Poly1305.X86_64.kf s₀
    · subst hkj
      simp only [ite_true, VG.Proof.Poly1305.X86_64.padded, Nat.lt_irrefl, ite_false]
      decide
    · simp only [VG.Proof.Poly1305.X86_64.bufB_ne hk' hk hkj, ite_false]
      rw [h.buf k hk']
      by_cases h1 : k < VG.Proof.Poly1305.X86_64.kf s₀
      · simp only [h1, ite_true, VG.Proof.Poly1305.X86_64.padded]
      · simp only [h1, ite_false, hk', ite_true, VG.Proof.Poly1305.X86_64.padded, hkj]

/-- The padded block as a number: the buffered bytes with `0x01` appended. -/
theorem padded_value {s₀ : State} {m : Mem} (h : VG.Proof.Poly1305.X86_64.BufHas m (st s₀) (VG.Proof.Poly1305.X86_64.padded s₀)) :
    leNum (bytesAt m (off (st s₀) 56) 16) + 2 ^ 128 * (0 : BitVec 32).toNat = leNum (VG.Proof.Poly1305.X86_64.tail s₀ ++ [0x01]) := by
  have hk := VG.Proof.Poly1305.X86_64.kf_lt s₀
  have hlen : (VG.Proof.Poly1305.X86_64.tail s₀).length = VG.Proof.Poly1305.X86_64.kf s₀ := Poly1305.length_bytesAt _ _ _
  have hl : (List.range 16).map (VG.Proof.Poly1305.X86_64.padded s₀) = (VG.Proof.Poly1305.X86_64.tail s₀ ++ [0x01]) ++ List.replicate (15 - VG.Proof.Poly1305.X86_64.kf s₀) 0 := by
    apply List.ext_getElem
    · simp [hlen]; omega_using [hk, hlen]
    · intro k h₁ h₂
      simp only [List.getElem_map, List.getElem_range]
      rcases Nat.lt_trichotomy k (VG.Proof.Poly1305.X86_64.kf s₀) with hk' | rfl | hk'
      · rw [List.getElem_append_left (by simp [hlen]; omega_using [hlen, hk']), List.getElem_append_left (by omega_using [hlen, hk'])]
        simp only [VG.Proof.Poly1305.X86_64.padded, hk', ite_true]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (VG.Proof.Poly1305.X86_64.tail s₀).length by omega_using [hlen, hk'])]
      · rw [List.getElem_append_left (by simp [hlen]), List.getElem_append_right (by omega_using [hlen])]
        simp [VG.Proof.Poly1305.X86_64.padded, hlen]
      · rw [List.getElem_append_right (by simp [hlen]; omega_using [hlen, hk'])]
        simp [VG.Proof.Poly1305.X86_64.padded, show ¬ k < VG.Proof.Poly1305.X86_64.kf s₀ by omega_using [hlen, hk'], show k ≠ VG.Proof.Poly1305.X86_64.kf s₀ by omega_using [hlen, hk']]
  rw [show (0 : BitVec 32).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, VG.Proof.Poly1305.X86_64.bytesAt_buf h, hl,
    Poly1305.leNum_append _ (List.replicate _ _), Poly1305.leNum_replicate_zero, Nat.mul_zero, Nat.add_zero]

/-- After the buffered bytes (if any) are absorbed. -/
structure Tail (s₀ : State) (m₁ : Mem) (s₁ : State) (s : State) : Prop where
  keep : ∀ r ∈ [Reg.rdi, .rcx, .rsp, .r8, .r9, .r10], s.gpr r = s₁.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [bfR (st s₀)] m₁ s.mem
  acc : H2 s₀ ≤ 4 → hval s % P = Poly1305.absorbAll (Rn s₀) (A0 s₀) (VG.Proof.Poly1305.X86_64.tail s₀) % P ∧
    (s.gpr .rbp).toNat ≤ 4

theorem tail_nil {s₀ : State} (h : VG.Proof.Poly1305.X86_64.kf s₀ = 0) : VG.Proof.Poly1305.X86_64.tail s₀ = [] := by
  simp [VG.Proof.Poly1305.X86_64.tail, bytesAt, h]

theorem lastBlock_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State}
    (h₁ : VG.Proof.Poly1305.X86_64.F0 s₀ m₁ s₁) (hpos : 0 < VG.Proof.Poly1305.X86_64.kf s₀) : WP isa lastBlock s₁ (VG.Proof.Poly1305.X86_64.Tail s₀ m₁ s₁) := by
  have hk := VG.Proof.Poly1305.X86_64.kf_lt s₀
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.zinit_ok hm h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.zeroLoop_ok hp h₁ h₂) fun s₃ h₃ => ?_)
  refine WP.block_append (WP.mono (VG.Proof.Poly1305.X86_64.pad1_ok hp h₁ h₃) fun s₄ h₄ => ?_)
  have g : ∀ r, r ≠ .rax → r ≠ .r12 → s₄.gpr r = s₁.gpr r := h₄.keep
  have hq : (R1 s₀).toNat % 4 = 0 := r1_mod _
  have hq' : (R1 s₀).toNat < 2 ^ 60 := r1_lt _
  have hrdi : s₄.gpr .rdi = st s₀ := by rw [g _ (by decide) (by decide), h₁.keep .rdi (by simp)]
  have hab := VG.Proof.Poly1305.X86_64.absorbBuf_ok s₄ (pad := 0) (Or.inl rfl) (by rw [h₄.wr, hrdi]; exact hp.st_in)
    (q := (R1 s₀).toNat / 4)
    (by rw [g .r8 (by decide) (by decide), h₁.r8]; exact r0_lt _)
    (by rw [g .r9 (by decide) (by decide), h₁.r9]; omega_using [hq]) (by omega_using [hq, hq'])
    (by rw [g .r10 (by decide) (by decide), h₁.r10])
  refine WP.mono hab fun s₅ ⟨ha, k₅⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [k₅.2.2.1, h₄.rd], by rw [k₅.2.2.2, h₄.wr], by rw [k₅.2.1]; exact h₄.frame,
    fun hH2 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k₅.gpr', g _ (by decide) (by decide)]
  · have hv4 : hval s₄ = A0 s₀ := by
      simp only [hval, g .r11 (by decide) (by decide), g .rbx (by decide) (by decide),
        g .rbp (by decide) (by decide)]
      exact h₁.hv
    have hb4 : (s₄.gpr .rbp).toNat ≤ 4 := by
      rw [g .rbp (by decide) (by decide), h₁.rbp]; exact hH2
    obtain ⟨hv, hb⟩ := ha hb4
    refine ⟨?_, hb⟩
    have hlen : (VG.Proof.Poly1305.X86_64.tail s₀).length = VG.Proof.Poly1305.X86_64.kf s₀ := Poly1305.length_bytesAt _ _ _
    rw [hv, hv4, hrdi, VG.Proof.Poly1305.X86_64.padded_value h₄.buf, g .r8 (by decide) (by decide),
      g .r9 (by decide) (by decide), h₁.r8, h₁.r9,
      Poly1305.absorbAll_block (by omega_using [hpos, hk, hlen]) (by omega_using [hpos, hk, hlen]), Nat.mod_mod, Nat.mul_comm]

/-! ## Epilogue -/

/-- An addition with carry into a second word, as numbers, modulo `2¹²⁸`. -/
theorem add_adc_mod (a b c d : BitVec 64) :
    (a + b).toNat + 2 ^ 64 * (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64).toNat =
      (a.toNat + b.toNat + 2 ^ 64 * (c.toNat + d.toNat)) % 2 ^ 128 := by
  simp only [BitVec.toNat_add]
  rw [carry_toNat]
  have ha := a.isLt; have hb := b.isLt; have hc := c.isLt; have hd := d.isLt
  by_cases h2 : 2 ^ 64 ≤ a.toNat + b.toNat <;>
    simp only [h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false] <;> omega_using [ha, hb, h2]

theorem tagWords_eq : [Instr.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
    .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] ++ restore =
    [.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
    .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx, .mov .rbx (.mem (at_ .rdi 72)),
    .mov .rbp (.mem (at_ .rdi 80)), .mov .r12 (.mem (at_ .rdi 88)), .mov .r13 (.mem (at_ .rdi 96)),
    .mov .r14 (.mem (at_ .rdi 104)), .mov .r15 (.mem (at_ .rdi 112))] := rfl

set_option simprocs false in
/-- Adding `s`, storing the tag and restoring the callee-saved registers. -/
theorem tagWords_ok (s : State) (hin : sR (s.gpr .rdi) ∈ s.wr) (hout : ⟨s.gpr .rcx, 16⟩ ∈ s.wr)
    (hsep : (sR (s.gpr .rdi)).Disjoint ⟨s.gpr .rcx, 16⟩) :
    WP isa (.block (([.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] : List Instr) ++ restore)) s fun s' =>
      (s'.mem.readW (off (s.gpr .rcx) 0) 64).toNat + 2 ^ 64 * (s'.mem.readW (off (s.gpr .rcx) 8) 64).toNat =
        ((s.gpr .r11).toNat + (s.mem.readW (off (s.gpr .rdi) 40) 64).toNat +
          2 ^ 64 * ((s.gpr .rbx).toNat + (s.mem.readW (off (s.gpr .rdi) 48) 64).toNat)) % 2 ^ 128 ∧
      Frame [⟨s.gpr .rcx, 16⟩] s.mem s'.mem ∧
      s'.gpr .rbx = s.mem.readW (off (s.gpr .rdi) 72) 64 ∧ s'.gpr .rbp = s.mem.readW (off (s.gpr .rdi) 80) 64 ∧
      s'.gpr .r12 = s.mem.readW (off (s.gpr .rdi) 88) 64 ∧ s'.gpr .r13 = s.mem.readW (off (s.gpr .rdi) 96) 64 ∧
      s'.gpr .r14 = s.mem.readW (off (s.gpr .rdi) 104) 64 ∧ s'.gpr .r15 = s.mem.readW (off (s.gpr .rdi) 112) 64 ∧
      s'.gpr .rsp = s.gpr .rsp ∧ s'.gpr .rcx = s.gpr .rcx := by
  have i : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (off (s.gpr .rdi) d) 8 :=
    fun d hd => ⟨_, List.mem_append_right _ hin, contains_off hd (by omega_using [hd])⟩
  have o : ∀ d, d + 8 ≤ 16 → InRegions s.wr (off (s.gpr .rcx) d) 8 :=
    fun d hd => ⟨_, hout, contains_off hd (by omega_using [hd])⟩
  have i40 := i 40 (by decide); have i48 := i 48 (by decide)
  have i0 := i 72 (by decide); have i1 := i 80 (by decide); have i2 := i 88 (by decide)
  have i3 := i 96 (by decide); have i4 := i 104 (by decide); have i5 := i 112 (by decide)
  have o0 := o 0 (by decide); have o8 := o 8 (by decide)
  -- The stores to the tag do not change the state.
  have sep : ∀ d, d + 8 ≤ 128 → ∀ e, e + 8 ≤ 16 → ∀ (m : Mem) (v : BitVec 64),
      (m.writeW (off (s.gpr .rcx) e) v).readW (off (s.gpr .rdi) d) 64 = m.readW (off (s.gpr .rdi) d) 64 :=
    fun d hd e he m v => Mem.readW_writeW_sep (hsep.sep (contains_off hd (by omega_using [hd]))
      (contains_off he (by omega_using [he]))) (by decide)
  simp only [off] at i40 i48 i0 i1 i2 i3 i4 i5 o0 o8 sep
  apply WP.of_runBlock
  rw [VG.Proof.Poly1305.X86_64.tagWords_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, execAlu, arithFlags, State.setFlags, State.store64, State.load64, State.setReg, i40, i48,
    i0, i1, i2, i3, i4, i5, o0, o8, ite_true, ite_false, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', sep]
  have e40 : s.gpr .rdi + BitVec.ofInt 64 ↑(40 : Nat) = off (s.gpr .rdi) 40 := rfl
  have e48 : s.gpr .rdi + BitVec.ofInt 64 ↑(48 : Nat) = off (s.gpr .rdi) 48 := rfl
  rw [e40, e48]
  generalize s.gpr .r11 = a, s.mem.readW (off (s.gpr .rdi) 40) 64 = b, s.gpr .rbx = c,
    s.mem.readW (off (s.gpr .rdi) 48) 64 = d
  refine ⟨?_, ?_, trivial⟩
  · have r0 : ((s.mem.writeW (off (s.gpr .rcx) 0) (a + b)).writeW (off (s.gpr .rcx) 8)
        (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64)).readW
          (off (s.gpr .rcx) 0) 64 = a + b := by
      rw [readW_writeW_off _ _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self64]
    have r8 : ((s.mem.writeW (off (s.gpr .rcx) 0) (a + b)).writeW (off (s.gpr .rcx) 8)
        (c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64)).readW
          (off (s.gpr .rcx) 8) 64 = c + d + (BitVec.ofBool (decide (2 ^ 64 ≤ a.toNat + b.toNat))).setWidth 64 :=
      Mem.readW_writeW_self64 _ _ _
    simp only [off] at r0 r8
    rw [r0, r8]
    exact VG.Proof.Poly1305.X86_64.add_adc_mod a b c d
  · exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _ (contains_off (by decide) (by decide))

theorem off_zero (p : Addr) : off p 0 = p := by simp [off]

theorem fepilogue_ok {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) {m₁ : Mem} (hm : Mem₁ s₀ m₁) {s₁ : State}
    (h₁ : VG.Proof.Poly1305.X86_64.F0 s₀ m₁ s₁) {s : State} (ht : VG.Proof.Poly1305.X86_64.Tail s₀ m₁ s₁ s) :
    WP isa (.block (reduce ++ ([.alu .add .r11 (.mem (at_ .rdi 40)), .alu .adc .rbx (.mem (at_ .rdi 48)),
      .store (at_ .rcx 0) .r11, .store (at_ .rcx 8) .rbx] : List Instr) ++ restore)) s fun s' =>
      gprPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86_64.post s₀ s' := by
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (reduce_ok s) fun s₂ ⟨hr, k₂⟩ => ?_)
  have rdi₂ : s₂.gpr .rdi = st s₀ := by
    rw [k₂.gpr' (r := .rdi), ht.keep .rdi (by simp), h₁.keep .rdi (by simp)]
  have rcx₂ : s₂.gpr .rcx = VG.Proof.Poly1305.X86_64.op s₀ := by
    rw [k₂.gpr' (r := .rcx), ht.keep .rcx (by simp), h₁.rcx]
  have wr₂ : s₂.wr = s₀.wr := by rw [k₂.2.2.2, ht.wr]
  refine WP.mono (VG.Proof.Poly1305.X86_64.tagWords_ok s₂ (by rw [wr₂, rdi₂]; exact hp.st_in) (by rw [wr₂, rcx₂]; exact hp.o_in)
    (by rw [rdi₂, rcx₂]; exact hp.st_o)) fun s₃ ⟨hw, hf₃, g1, g2, g3, g4, g5, g6, g7, g8⟩ => ?_
  rw [rdi₂, rcx₂, k₂.2.1] at hw
  rw [rcx₂, k₂.2.1] at hf₃
  rw [rdi₂, k₂.2.1] at g1 g2 g3 g4 g5 g6
  -- The state outside the buffer is as the prologue left it.
  have low : ∀ d, d + 8 ≤ 56 ∨ 72 ≤ d → d + 8 ≤ 128 →
      s.mem.readW (off (st s₀) d) 64 = m₁.readW (off (st s₀) d) 64 := by
    intro d hd hd'
    refine ht.frame.readW (r := ⟨off (st s₀) d, 8⟩) (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_singleton, forall_eq, bfR, off, ofInt_natCast]
    exact Offset.disjoint (st s₀) (by omega_using [hd]) (by omega_using [hd']) (by decide)
  obtain ⟨sv1, sv2, sv3, sv4, sv5, sv6⟩ := hm.saved
  have hf : Frame [wR (st s₀), VG.Proof.Poly1305.X86_64.oR s₀] s₀.mem s₃.mem :=
    (hm.frame_wR.mono (by simp)).trans ((ht.frame.sub fun r hr => ⟨wR (st s₀), by simp, by
      simp only [List.mem_singleton] at hr; subst hr; exact VG.Proof.Poly1305.X86_64.bfR_sub_wR _⟩).trans (hf₃.mono (by simp)))
  refine ⟨⟨fun r hr => ?_, ?_⟩, by rw [g8, rcx₂], fun key msg hbuf hcnt => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [g1, low 72 (by decide) (by decide), sv1]
    · rw [g2, low 80 (by decide) (by decide), sv2]
    · rw [g7, k₂.gpr' (r := .rsp), ht.keep .rsp (by simp), h₁.keep .rsp (by simp)]
    · rw [g3, low 88 (by decide) (by decide), sv3]
    · rw [g4, low 96 (by decide) (by decide), sv4]
    · rw [g5, low 104 (by decide) (by decide), sv5]
    · rw [g6, low 112 (by decide) (by decide), sv6]
  · refine hf.readW (Region.contains_self _ _) ?_ (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.ret_st.sub_right (sub_sR _ (by decide))
    · exact hp.ret_o
  · obtain ⟨W, B, rfl, hrep, hBl, hBb⟩ := Buffered.split hbuf
    have hk : VG.Proof.Poly1305.X86_64.kf s₀ = (W ++ B).length % 16 := hcnt
    have htail : VG.Proof.Poly1305.X86_64.tail s₀ = B := by rw [VG.Proof.Poly1305.X86_64.tail, hk, VG.Proof.Poly1305.X86_64.off_56, hBb]
    rw [← htail]
    obtain ⟨hlen, hkey, hacc⟩ := hrep
    have hH2 := H2_le ⟨hlen, hkey, hacc⟩
    obtain ⟨hv, hb⟩ := ht.acc hH2
    have hR := hr hb
    rw [← off_24] at hkey
    have hkey' : bytesAt s₀.mem (off (st s₀) 24) 32 = key := hkey
    have hA : accumulate (Rn s₀) W = A0 s₀ := by rw [A0, hacc, ← hkey', clamp_key]
    have hlt : A0 s₀ < P := by rw [← hA]; exact Poly1305.accumulate_lt _ _
    have hV := Poly1305.absorbAll_lt (r := Rn s₀) hlt (VG.Proof.Poly1305.X86_64.tail s₀)
    rw [low 40 (by decide) (by decide), low 48 (by decide) (by decide), hm.readW_low (by decide),
      hm.readW_low (by decide)] at hw
    have e₀ := (s₂.gpr .r11).isLt; have e₁ := (s₂.gpr .rbx).isLt
    have hh : hval s₂ = Poly1305.absorbAll (Rn s₀) (A0 s₀) (VG.Proof.Poly1305.X86_64.tail s₀) := by
      rw [hR, hv, Nat.mod_eq_of_lt hV]
    unfold hval at hh
    simp only [mac]
    rw [← hkey', clamp_key, key_drop, leNum_key, off_off, off_off, Poly1305.accumulate_append hlen, hA]
    have w0 := (s₃.mem.readW (off (VG.Proof.Poly1305.X86_64.op s₀) 0) 64).isLt
    have w1 := (s₃.mem.readW (off (VG.Proof.Poly1305.X86_64.op s₀) 8) 64).isLt
    rw [VG.Proof.Poly1305.X86_64.off_zero] at hw w0
    rw [show off (st s₀) (40 + 0) = off (st s₀) 40 from rfl, show off (st s₀) (40 + 8) = off (st s₀) 48 from rfl]
    refine Poly1305.bytesAt_leBytes_16 _ (VG.Proof.Poly1305.X86_64.op s₀) (Poly1305.absorbAll (Rn s₀) (A0 s₀) (VG.Proof.Poly1305.X86_64.tail s₀) +
      ((s₀.mem.readW (off (st s₀) 40) 64).toNat + 2 ^ 64 * (s₀.mem.readW (off (st s₀) 48) 64).toNat)) ?_ ?_
    · omega_using [hw, hh]
    · change (s₃.mem.readW (off (VG.Proof.Poly1305.X86_64.op s₀) 8) 64).toNat = _; omega_using [hw, hh]

/-! ## The whole function -/

theorem finalize_correct {s₀ : State} (hp : VG.Proof.Poly1305.X86_64.FPre s₀) :
    WP isa finalize s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Poly1305.finalizeX86_64.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Poly1305.X86_64.fprologue_ok hp) fun s₁ ⟨m₁, hm, h₁, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Poly1305.X86_64.Tail s₀ m₁ s₁) ?_ fun s₂ h₂ => VG.Proof.Poly1305.X86_64.fepilogue_ok hp hm h₁ h₂)
  refine WP.ite (BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kf s₀) &&& BitVec.ofNat 64 (VG.Proof.Poly1305.X86_64.kf s₀) == 0) (by simp [eval, hzf])
    (fun h => ?_) (fun h => ?_)
  · rw [BitVec.and_self, ofNat_beq_zero (by have := VG.Proof.Poly1305.X86_64.kf_lt s₀; omega_using [this])] at h
    simp only [decide_eq_true_eq] at h
    refine WP.block_nil (M := isa) ⟨fun r _ => rfl, h₁.rd, h₁.wr, by rw [h₁.mem]; exact Frame.refl _ _,
      fun hH2 => ⟨?_, by rw [h₁.rbp]; exact hH2⟩⟩
    rw [VG.Proof.Poly1305.X86_64.tail_nil h, Poly1305.absorbAll_nil, h₁.hv]
  · rw [BitVec.and_self, ofNat_beq_zero (by have := VG.Proof.Poly1305.X86_64.kf_lt s₀; omega_using [this])] at h
    simp only [decide_eq_false_iff_not] at h
    exact VG.Proof.Poly1305.X86_64.lastBlock_ok hp hm h₁ (Nat.pos_of_ne_zero h)

/-- A state satisfying the precondition (with 128 bytes of working space at `rcx`). -/
def finalizeSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x3000 | .rcx => 0x5000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 128⟩, ⟨0x3000, 16⟩, ⟨0x5000, 128⟩]

theorem finalize_ok (s : State) (hs : Proof.Poly1305.finalizeX86_64.pre s) :
    ∃ t s', Exec isa Impl.Poly1305.X86_64.finalize s t s' ∧ abiPreserved s s' ∧
      Proof.Poly1305.finalizeX86_64.post s s' := by
  obtain ⟨t, s', he, h⟩ := VG.Proof.Poly1305.X86_64.finalize_correct (FPre.of s hs)
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩

theorem finalize_ct : ConstantTime isa Proof.Poly1305.finalizeX86_64.pre
    Proof.Poly1305.finalizeX86_64.pub Impl.Poly1305.X86_64.finalize := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, h3⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> with_reducible assumption

theorem finalize_verified :
    Verified X86_64.target Impl.Poly1305.X86_64.finalize (Spec.Poly1305.finalizeScratchContract X86_64.abi)
      :=
  Verified.of_correct VG.Proof.Poly1305.X86_64.finalize_ok VG.Proof.Poly1305.X86_64.finalize_ct
    { pre := by
        sig_implies_pre [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost,
          Proof.Poly1305.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost, X86_64.abi,
            X86_64.argRegs]
        intro key msg hb hc
        exact h.2 key msg hb (VG.Proof.Poly1305.X86_64.count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost,
          Proof.Poly1305.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.finalizeScratchContract, Spec.Poly1305.finalizeScratchSig, Spec.Poly1305.finalizePost, X86_64.abi,
          X86_64.argRegs,
          Proof.Poly1305.X86_64.finalizeSat]
          [Proof.Poly1305.X86_64.finalizeSat] using Proof.Poly1305.X86_64.finalizeSat }

end VG.Proof.Poly1305.X86_64

end
