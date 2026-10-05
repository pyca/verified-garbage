import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Impl.MdStream.X86_64
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.X86_64.Common`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on x86-64: common lemmas

The contracts the generic proofs are written against, what they need of a hash
function's parameters (`Shape`) and of its compression function (`CalleeOk`),
the call of the compression function (`compressAt`), and weakest-precondition
rules for the instructions used.
-/

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)

/-! ## Addresses and regions -/

theorem ofInt_natCast (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := Offset.contains_base base h ho

theorem contains_offset' {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofInt 64 (off : Int)) n := by
  rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.contains_offset h ho

theorem sub_offset {base : Addr} {off len len' : Nat} (h : off + len ≤ len') (_ho : off < 2 ^ 64) :
    Region.Sub ⟨base + BitVec.ofNat 64 off, len⟩ ⟨base, len'⟩ := Offset.sub_base base h

theorem save_sep (p : Addr) {d e : Nat} (hd : d < 2 ^ 32) (he : e < 2 ^ 32)
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    Mem.Sep (p + BitVec.ofInt 64 (d : Int)) 8 (p + BitVec.ofInt 64 (e : Int)) 8 := by
  rw [VG.Proof.MdStream.X86_64.ofInt_natCast, VG.Proof.MdStream.X86_64.ofInt_natCast]
  exact Offset.sep p h (by omega) (by omega)

theorem readW_writeW_save (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 (e : Int)) v).readW (p + BitVec.ofInt 64 (d : Int)) 64 =
    m.readW (p + BitVec.ofInt 64 (d : Int)) 64 :=
  Mem.readW_writeW_sep (VG.Proof.MdStream.X86_64.save_sep p hd he h) (by decide)

/-! Saves at `so + d`, with the conditions on the literal offsets `d`, `e`
alone, which `decide` discharges. -/
theorem readW_writeW_save_so {so : Nat} (hso : so ≤ 2048) (m : Mem) (p : Addr) (v : BitVec 64)
    {d e : Nat} (hd : d ≤ 64) (he : e ≤ 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (p + BitVec.ofInt 64 ((so + e : Nat) : Int)) v).readW
      (p + BitVec.ofInt 64 ((so + d : Nat) : Int)) 64 =
      m.readW (p + BitVec.ofInt 64 ((so + d : Nat) : Int)) 64 :=
  VG.Proof.MdStream.X86_64.readW_writeW_save m p v (by omega) (by omega) (by omega)

theorem readW_writeW_save_so_l {so : Nat} (hso : so ≤ 2048) (m : Mem) (p : Addr) (v : BitVec 64)
    {e : Nat} (he : e ≤ 64) (h : 8 ≤ e) :
    (m.writeW (p + BitVec.ofInt 64 ((so + e : Nat) : Int)) v).readW (p + BitVec.ofInt 64 (so : Int)) 64 =
      m.readW (p + BitVec.ofInt 64 (so : Int)) 64 :=
  VG.Proof.MdStream.X86_64.readW_writeW_save m p v (by omega) (by omega) (by omega)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem add_ofNat (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]

/-! ## Immediates and arithmetic -/

theorem sx_ofNat {n : Nat} (h : n < 2 ^ 31) : (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat]; simp; omega

theorem zx_ofNat {n : Nat} (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = (1 : BitVec 64) := by decide

theorem and_mask {B : Nat} (hB : B = 64 ∨ B = 128) (x : BitVec 64) :
    x &&& (BitVec.ofNat 32 (B - 1)).signExtend 64 = BitVec.ofNat 64 (x.toNat % B) := by
  rw [VG.Proof.MdStream.X86_64.sx_ofNat (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rcases hB with rfl | rfl
  · rw [show (64 - 1 : Nat) % 2 ^ 64 = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega
  · rw [show (128 - 1 : Nat) % 2 ^ 64 = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega

theorem ofNat_succ (k : Nat) : BitVec.ofNat 64 (k + 1) = BitVec.ofNat 64 k + 1 := by
  rw [BitVec.ofNat_add]; rfl

theorem ofNat_pred {k : Nat} (h : 1 ≤ k) : BitVec.ofNat 64 k - 1 = BitVec.ofNat 64 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, VG.Proof.MdStream.X86_64.ofNat_succ, Nat.add_sub_cancel, BitVec.add_sub_cancel]

theorem ofNat_beq_zero {k : Nat} (h : k < 2 ^ 64) : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h] at this
    exact hk this

theorem bytesAt_getD {m : Mem} {p : Addr} {n : Nat} {l : List Byte} (h : bytesAt m p n = l) {k : Nat}
    (hk : k < n) : m (p + BitVec.ofNat 64 k) = l.getD k 0 := by
  subst h; simp [bytesAt, List.getD_eq_getElem?_getD, hk]

theorem sub_ofNat {a b : Nat} (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  rw [show BitVec.ofNat 64 a = BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel h], BitVec.add_sub_cancel]

theorem sub_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b == 0) = decide (a = b) := by
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h'
    apply h
    have := congrArg BitVec.toNat h'
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt hb] at this
    change _ = 0 at this
    omega

/-! ## Sizes -/

/-- The sizes the generic proofs support, checked for each hash function by
`decide`. -/
structure Dims (P : Params) : Prop where
  B : P.B = 64 ∨ P.B = 128
  N : 0 < P.N ∧ P.N ≤ 64
  L : 0 < P.L ∧ P.L ≤ 16
  so : P.so ≤ 2048

theorem Dims.mod {P : Params} (hd : VG.Proof.MdStream.X86_64.Dims P) (n : Nat) : n % 2 ^ 64 % P.B = n % P.B := by
  rcases hd.B with h | h <;> rw [h] <;> omega

theorem Dims.pos {P : Params} (hd : VG.Proof.MdStream.X86_64.Dims P) : 0 < P.B := by rcases hd.B with h | h <;> omega

/-- The shift count of `direct`. -/
theorem Dims.lg {P : Params} (hd : VG.Proof.MdStream.X86_64.Dims P) :
    1 ≤ Nat.log2 P.B ∧ Nat.log2 P.B ≤ 63 ∧ 2 ^ Nat.log2 P.B = P.B := by
  rcases hd.B with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

theorem restore_eq (P : Params) : restore P = [
    .mov .rbx (.mem (at_ .r15 P.so)), .mov .rbp (.mem (at_ .r15 (P.so + 8))),
    .mov .r12 (.mem (at_ .r15 (P.so + 16))), .mov .r13 (.mem (at_ .r15 (P.so + 24))),
    .mov .r14 (.mem (at_ .r15 (P.so + 32))), .mov .r15 (.mem (at_ .r15 (P.so + 40)))] :=
  rfl

theorem save_eq (P : Params) (b : Reg) : save P b = [
    .store (at_ b P.so) .rbx, .store (at_ b (P.so + 8)) .rbp, .store (at_ b (P.so + 16)) .r12,
    .store (at_ b (P.so + 24)) .r13, .store (at_ b (P.so + 32)) .r14, .store (at_ b (P.so + 40)) .r15] :=
  rfl

/-! ## Saving the caller's registers -/

section
variable (P : Params) (s₀ : State) (b : Reg)

/-- The caller's callee-saved registers are saved in the scratch space at `b`. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ saved P, m.readW (s₀.gpr b + BitVec.ofInt 64 (p.2 : Int)) 64 = s₀.gpr p.1

/-- The memory after saving them. -/
def saveMem : Mem :=
  (((((s₀.mem.writeW (s₀.gpr b + BitVec.ofInt 64 ((P.so : Nat) : Int)) (s₀.gpr .rbx)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (s₀.gpr .rbp)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int)) (s₀.gpr .r12)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int)) (s₀.gpr .r13)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int)) (s₀.gpr .r14)).writeW
    (s₀.gpr b + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int)) (s₀.gpr .r15)

end

section
variable {P : Params} {s₀ : State} {b : Reg}

theorem saveMem_saved (hd : VG.Proof.MdStream.X86_64.Dims P) : VG.Proof.MdStream.X86_64.Saved P s₀ b (VG.Proof.MdStream.X86_64.saveMem P s₀ b) := by
  have := hd.so
  intro p hp
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := decide) only [VG.Proof.MdStream.X86_64.saveMem, Mem.readW_writeW_self64, VG.Proof.MdStream.X86_64.readW_writeW_save_so this,
    VG.Proof.MdStream.X86_64.readW_writeW_save_so_l this]

theorem saveMem_frame (hd : VG.Proof.MdStream.X86_64.Dims P) : Frame [⟨s₀.gpr b, P.so + 48⟩] s₀.mem (VG.Proof.MdStream.X86_64.saveMem P s₀ b) := by
  have := hd.so
  have c : ∀ d : Nat, d + 8 ≤ P.so + 48 →
      (⟨s₀.gpr b, P.so + 48⟩ : Region).Contains (s₀.gpr b + BitVec.ofInt 64 (d : Int)) (64 / 8) :=
    fun d hd => VG.Proof.MdStream.X86_64.contains_offset' hd (by omega)
  simp only [VG.Proof.MdStream.X86_64.saveMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega))).writeW (List.mem_singleton_self _) _
    (c _ (by omega))).writeW (List.mem_singleton_self _) _ (c _ (by omega))).writeW
    (List.mem_singleton_self _) _ (c _ (by omega)) |>.writeW (List.mem_singleton_self _) _
    (c _ (by omega))

/-- The saved registers are outside the part of the scratch space the
compression function uses. -/
theorem saved_offset (hd : VG.Proof.MdStream.X86_64.Dims P) {p : Reg × Nat} (hp : p ∈ saved P) : P.so ≤ p.2 ∧ p.2 + 8 ≤ P.so + 48 := by
  have := hd.so
  simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega

end

/-! ## The contracts

The generic proofs are written against these; each hash function's own
contracts are these for its instance. -/

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The contract of the compression function: updates the hash value at
`rdi` with the `rdx` blocks at `rsi`, with scratch space `rcx` (`so`
bytes). -/
def compressK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, P.N⟩
    let blocks : Region := ⟨s.gpr .rsi, P.B * (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, P.so⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch
  post s s' :=
    H.stateAt s'.mem (s.gpr .rdi) =
      H.compressBlocks (H.stateAt s.mem (s.gpr .rdi)) s.mem (s.gpr .rsi) (s.gpr .rdx).toNat
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- The contract of `update`: if the state at `rdi` represents a message of
`rsi` bytes (modulo 2⁶⁴) from any initial hash value, it then represents
that message followed by the `rcx` bytes at `rdx`. -/
def updK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, P.N + P.B⟩
    let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, P.so + 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [data] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .rdi) m → s.gpr .rsi = BitVec.ofNat 64 m.length →
    H.Repr iv s'.mem (s.gpr .rdi) (m ++ bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- The contract of `finalize`: if the state at `rdi` represents a message of
`rsi` bytes, writes its final hash value to `rdx` (`N` bytes). -/
def finK : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, P.N + P.B⟩
    let out : Region := ⟨s.gpr .rdx, P.N⟩
    let scratch : Region := ⟨s.gpr .rcx, P.so + 48⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch
  post s s' := ∀ iv m, H.Repr iv s.mem (s.gpr .rdi) m → H.lenOk m.length →
    s.gpr .rsi = BitVec.ofNat 64 m.length → bytesAt s'.mem (s.gpr .rdx) P.N = H.hash iv m
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

end

/-! ## What each hash function's own code must do -/

/-- The length field and the digest: `P.len` stores the length field for the
byte count in `r12` at `rbx + N + B - L`, and `P.out` writes the digest of the
hash value at `rbx` to `rbp`; each writes only `rax` and the flags. -/
structure Shape {P : Params} (H : Md P.B P.N P.L) : Prop where
  len : ∀ s : State, InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L →
    WP isa (.block P.len) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L)) (H.lenOf (s.gpr .r12))
  out : ∀ s : State, InRegions (s.rd ++ s.wr) (s.gpr .rbx) P.N → InRegions s.wr (s.gpr .rbp) P.N →
    Region.Disjoint ⟨s.gpr .rbx, P.N⟩ ⟨s.gpr .rbp, P.N⟩ →
    WP isa (.block P.out) s fun s' => (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .rbp) (H.digest (H.stateAt s.mem (s.gpr .rbx)))

/-- The initial taint of `update`: the arguments and `rsp` are public, and
`rdi` and `r8` point at the writable regions. -/
def τ₀ (P : Params) : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [P.N + P.B, P.so + 48],
    bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

/-- What the taint analysis proves of the pieces of `update` and `finalize`
between the calls of the compression function, for one hash function's
code: each is `⟨_, by taint_decide⟩`. -/
structure Taints (P : Params) : Prop where
  updStart : ∃ hc, (taint.check (VG.Proof.MdStream.X86_64.τ₀ P) (.block (updateStart P)) hc).isSome = true
  updHead : ∃ hc, ((taint.check (X86_64.Taint.ofRegs [.rbx, .r15, .rsp, .rbp, .r12, .r13]) (updateHead P) hc).map
    fun τ' => (RegSet.ofList [.r12, .r14]).subset τ'.regs) = some true
  updEnd : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.r15]) (.block (restore P)) hc).isSome = true
  finStart : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp]) (finalizeStart P) hc).isSome
    = true
  finPad : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.rbx, .r15, .rbp, .r12, .rsp, .r13, .r14]) (finalizePad P)
    hc).isSome = true
  finEnd : ∃ hc, (taint.check (X86_64.Taint.ofRegs [.rbx, .rbp, .r15]) (.block (P.out ++ restore P)) hc).isSome
    = true

/-! ## The compression function -/

/-- What `compressAt` needs of the compression function it calls: that it is
correct and constant time, does not touch `rsp` or the stack, and keeps
`rdi` and `rcx`. -/
structure CalleeOk {P : Params} (H : Md P.B P.N P.L) (code : Prog isa) : Prop where
  verified : ∀ s, (VG.Proof.MdStream.X86_64.compressK H).pre s →
    ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MdStream.X86_64.compressK H).post s s'
  ct : ConstantTime isa (VG.Proof.MdStream.X86_64.compressK H).pre (VG.Proof.MdStream.X86_64.compressK H).pub code
  nosp : NoSp code
  depth : code.depth = 0
  keeps_rdi : ∀ i ∈ instrs code, Taint.clobbers i .rdi = false
  keeps_rcx : ∀ i ∈ instrs code, Taint.clobbers i .rcx = false

/-- The facts about the instructions of `code`, from one kernel check each. -/
theorem CalleeOk.of_verified {P : Params} {H : Md P.B P.N P.L} {code : Prog isa}
    (hv : ∀ s, (VG.Proof.MdStream.X86_64.compressK H).pre s → ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧ (VG.Proof.MdStream.X86_64.compressK H).post s s')
    (hct : ConstantTime isa (VG.Proof.MdStream.X86_64.compressK H).pre (VG.Proof.MdStream.X86_64.compressK H).pub code)
    (hk : ((instrs code).all fun i => !Taint.clobbers i .rdi && !Taint.clobbers i .rcx &&
      !Taint.clobbers i .rsp) = true)
    (hd : code.depth = 0) : VG.Proof.MdStream.X86_64.CalleeOk H code := by
  have h := fun i hi => List.all_eq_true.mp hk i hi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨hv, hct, fun i hi => (h i hi).2, hd, fun i hi => (h i hi).1.1, fun i hi => (h i hi).1.2⟩

/-- A region disjoint from the return address of a call reads the same on
entry to the callee. -/
theorem callEntry_byte (s : State) {R : Region} (hd : (below (s.gpr .rsp) 8).Disjoint R)
    (hR : R.len ≤ 2 ^ 64) {i : Nat} (hi : i < R.len) :
    s.callEntry.mem (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
  Frame.bytes (rs := [below (s.gpr .rsp) 8])
    (Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (below_call _ (by omega) (by omega)))
    (by simpa using hd.symm) hR hi

/-- What the call of the compression function in `compressWith` needs of the
state `s` before it: the hash value `st` at `rbx`, the scratch space `scr` at
`r15` and the `len` bytes of blocks `src` at `rsi` do not overlap each other
or the return address, and may be accessed. -/
structure CallOkN (P : Params) (s : State) (st scr src : Addr) (len : Nat) : Prop where
  rbx : s.gpr .rbx = st
  r15 : s.gpr .r15 = scr
  rsi : s.gpr .rsi = src
  d₁ : Region.Disjoint ⟨st, P.N⟩ ⟨scr, P.so⟩
  d₂ : Region.Disjoint ⟨src, len⟩ ⟨st, P.N⟩
  d₃ : Region.Disjoint ⟨src, len⟩ ⟨scr, P.so⟩
  d₄ : (below (s.gpr .rsp) 8).Disjoint ⟨st, P.N⟩
  d₅ : (below (s.gpr .rsp) 8).Disjoint ⟨scr, P.so⟩
  d₆ : (below (s.gpr .rsp) 8).Disjoint ⟨src, len⟩
  hc : Covers [⟨src, len⟩, ⟨st, P.N⟩, ⟨scr, P.so⟩] (s.rd ++ s.wr)
  hw : Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr

/-- For one block (`compressAt`). -/
abbrev CallOk (P : Params) (s : State) (st scr src : Addr) : Prop := VG.Proof.MdStream.X86_64.CallOkN P s st scr src P.B

/-- The arguments of the call, set up from `σ`, with `n` blocks. -/
structure Setup (σ s : State) (n : BitVec 64) : Prop where
  rdi : s.gpr .rdi = σ.gpr .rbx
  rdx : s.gpr .rdx = n
  rcx : s.gpr .rcx = σ.gpr .r15
  rsi : s.gpr .rsi = σ.gpr .rsi
  cs : ∀ r ∈ calleeSaved, s.gpr r = σ.gpr r
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  mem : s.mem = σ.mem

/-- The instruction setting the number of blocks, and what it sets. -/
def SetsN (i : Instr) (N : State → BitVec 64) : Prop :=
  ∀ s, WP isa (.block [.mov .rdi (.reg .rbx), i, .mov .rcx (.reg .r15)]) s fun s' => VG.Proof.MdStream.X86_64.Setup s s' (N s)

theorem setsN_one : VG.Proof.MdStream.X86_64.SetsN (.mov32 .rdx (.imm 1)) fun _ => 1 := by
  intro s
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, readSrc32, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp [State.setReg, State.setReg32], by simp [State.setReg, State.setReg32],
    by simp [State.setReg, State.setReg32], by simp [State.setReg, State.setReg32],
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [State.setReg, State.setReg32]

theorem setsN_r14 : VG.Proof.MdStream.X86_64.SetsN (.mov .rdx (.reg .r14)) fun s => s.gpr .r14 := by
  intro s
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp [State.setReg], by simp [State.setReg],
    by simp [State.setReg], by simp [State.setReg],
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [State.setReg]

section
variable {P : Params} (H : Md P.B P.N P.L)

/-- The call's precondition, narrowed to the regions it is given. -/
theorem call_hyps {σ s : State} {st scr src : Addr} {k : Nat} {n : BitVec 64} (hk : n.toNat = k)
    (h : VG.Proof.MdStream.X86_64.CallOkN P σ st scr src (P.B * k)) (hs : VG.Proof.MdStream.X86_64.Setup σ s n) :
    (VG.Proof.MdStream.X86_64.compressK H).pre (s.callEntry.withRegions [⟨src, P.B * k⟩] [⟨st, P.N⟩, ⟨scr, P.so⟩]) ∧
    Covers ([⟨src, P.B * k⟩] ++ [⟨st, P.N⟩, ⟨scr, P.so⟩]) (s.rd ++ s.wr) ∧
    Covers [⟨st, P.N⟩, ⟨scr, P.so⟩] s.wr := by
  have hsp : s.gpr .rsp = σ.gpr .rsp := hs.cs _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s.callEntry.gpr r = s.gpr r := fun r h => State.callEntry_gpr _ h
  refine ⟨?_, ?_, ?_⟩
  · simp only [VG.Proof.MdStream.X86_64.compressK, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, State.callEntry_rsp, hne _ (by decide : Reg.rdi ≠ .rsp),
      hne _ (by decide : Reg.rsi ≠ .rsp), hne _ (by decide : Reg.rdx ≠ .rsp),
      hne _ (by decide : Reg.rcx ≠ .rsp), hs.rdi, hs.rdx, hs.rcx, hs.rsi, h.rbx, h.r15, h.rsi, hsp, hk]
    exact ⟨by simp, by simp, h.d₁, by simpa using h.d₂, by simpa using h.d₃, h.d₄, h.d₅⟩
  · rw [hs.rd, hs.wr]; simpa using h.hc
  · rw [hs.wr]; exact h.hw

/-- Compressing the `k` blocks at `rsi` into the hash value at `rbx`, with
scratch space at `r15`, by calling the compression function, when `i` sets
`rdx` to `k`. -/
theorem compressWith_ok {i : Instr} {N : State → BitVec 64} (hi : VG.Proof.MdStream.X86_64.SetsN i N) {name : String}
    {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s : State} {st scr src : Addr} {k : Nat} (hk : (N s).toNat = k)
    (h : VG.Proof.MdStream.X86_64.CallOkN P s st scr src (P.B * k)) (hB : P.B * k ≤ 2 ^ 64) (hN : P.N ≤ 2 ^ 64)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, P.N⟩, ⟨scr, P.so⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      H.stateAt s'.mem st = H.compressBlocks (H.stateAt s.mem st) s.mem src k →
      s'.gpr .rdi = st → s'.gpr .rcx = scr → Q s') :
    WP isa (compressWith i name code) s Q := by
  unfold compressWith
  refine WP.seq (WP.mono (hi s) fun s₁ hs => ?_)
  have e₁ : s₁.gpr .rdi = st := hs.rdi.trans h.rbx
  have e₂ := hs.rdx
  have e₃ : s₁.gpr .rcx = scr := hs.rcx.trans h.r15
  have e₄ : s₁.gpr .rsi = src := hs.rsi.trans h.rsi
  have e₅ := hs.cs
  have hsp : s₁.gpr .rsp = s.gpr .rsp := e₅ _ (by simp [calleeSaved])
  have hne : ∀ r : Reg, r ≠ .rsp → s₁.callEntry.gpr r = s₁.gpr r := fun r h => State.callEntry_gpr _ h
  obtain ⟨hpre, hc, hw⟩ := VG.Proof.MdStream.X86_64.call_hyps H hk h hs
  refine WP.seq (WP.call (k := VG.Proof.MdStream.X86_64.compressK H) hf.verified hf.nosp (by rw [hf.depth]; decide)
    (rd := [⟨src, P.B * k⟩]) (wr := [⟨st, P.N⟩, ⟨scr, P.so⟩]) hpre hc hw ?_)
  intro s₂ hrd hwr hcs hfr hkeep ⟨s₃, hm₃, _, hpost⟩
  have k₁ := hkeep .rdi hf.keeps_rdi
  have k₃ := hkeep .rcx hf.keeps_rcx
  simp only [VG.Proof.MdStream.X86_64.compressK, State.withRegions_gpr, State.withRegions_mem,
    hne _ (by decide : Reg.rdi ≠ .rsp), hne _ (by decide : Reg.rsi ≠ .rsp),
    hne _ (by decide : Reg.rdx ≠ .rsp), e₁, e₂, e₄, hm₃, hk] at hpost
  have hst : H.stateAt s₁.callEntry.mem st = H.stateAt s.mem st :=
    (H.stateAt_congr fun i hi => VG.Proof.MdStream.X86_64.callEntry_byte s₁ (R := ⟨st, P.N⟩) (by rw [hsp]; exact h.d₄)
      hN hi).trans (by rw [hs.mem])
  have hblk : H.compressBlocks (H.stateAt s.mem st) s₁.callEntry.mem src k =
      H.compressBlocks (H.stateAt s.mem st) s.mem src k := by
    apply H.compressBlocks_congr
    intro j hj
    rw [VG.Proof.MdStream.X86_64.callEntry_byte s₁ (R := ⟨src, P.B * k⟩) (by rw [hsp]; exact h.d₆) hB hj, hs.mem]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    readSrc, isa, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine hQ _ (hrd.trans hs.rd) (hwr.trans hs.wr) (fun r hr => ?_) (by
    rw [hf.depth, hsp, hs.mem] at hfr; simpa [State.setReg] using hfr)
    (by simp only [State.setReg]; rw [hpost, hst, hblk]) (by simp [State.setReg, k₁, e₁])
    (by simp [State.setReg, k₃, e₃])
  have h₂ := hcs r hr
  simp only [State.setReg]
  by_cases h15 : r = .r15
  · subst h15; simp [k₃, e₃, h.r15]
  · by_cases hbx : r = .rbx
    · subst hbx; simp [k₁, e₁, h.rbx]
    · simp [h15, hbx, h₂, e₅ r hr]

/-- Compressing the block at `rsi` into the hash value at `rbx`, with scratch
space at `r15`, by calling the compression function. -/
theorem compressAt_ok {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s : State}
    {st scr src : Addr} (h : VG.Proof.MdStream.X86_64.CallOk P s st scr src) (hB : P.B ≤ 2 ^ 64) (hN : P.N ≤ 2 ^ 64)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨st, P.N⟩, ⟨scr, P.so⟩, below (s.gpr .rsp) 8] s.mem s'.mem →
      H.stateAt s'.mem st = H.compress (H.stateAt s.mem st) (H.blockAt s.mem src) →
      s'.gpr .rdi = st → s'.gpr .rcx = scr → Q s') :
    WP isa (compressAt name code) s Q :=
  VG.Proof.MdStream.X86_64.compressWith_ok H VG.Proof.MdStream.X86_64.setsN_one hf (k := 1) rfl (by rw [Nat.mul_one]; exact h) (by rw [Nat.mul_one]; exact hB) hN
    fun s' h₁ h₂ h₃ h₄ h₅ => hQ s' h₁ h₂ h₃ h₄ (by rw [h₅, Md.compressBlocks_one])

/-- `compressWith` is constant time, in runs that agree on its arguments. -/
theorem compressWith_rel {i : Instr} {N : State → BitVec 64} (hi : VG.Proof.MdStream.X86_64.SetsN i N)
    (hti : ∃ hc, (taint.check (X86_64.Taint.ofRegs []) (.block [.mov .rdi (.reg .rbx), i, .mov .rcx (.reg .r15)])
      hc).isSome = true)
    {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → (∃ a b c k, (N s₁).toNat = k ∧ VG.Proof.MdStream.X86_64.CallOkN P s₁ a b c (P.B * k)) ∧
      (∃ a b c k, (N s₂).toNat = k ∧ VG.Proof.MdStream.X86_64.CallOkN P s₂ a b c (P.B * k)) ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .r15 = s₂.gpr .r15 ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rsp = s₂.gpr .rsp ∧ N s₁ = N s₂) :
    RelCT isa P' (compressWith i name code) fun _ _ => True := by
  unfold compressWith
  obtain ⟨_, hti⟩ := hti
  have su := (RelCT.taint (A := taint) (P := P') (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.mov .rdi (.reg .rbx), i, .mov .rcx (.reg .r15)]) hti).wpDep
      (F := fun σ s => VG.Proof.MdStream.X86_64.Setup σ s (N σ)) fun s₁ s₂ _ => ⟨hi s₁, hi s₂⟩
  have cl := RelCT.callEx (n := name) (k := VG.Proof.MdStream.X86_64.compressK H)
    (P := fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P' σ₁ σ₂ ∧ VG.Proof.MdStream.X86_64.Setup σ₁ s₁ (N σ₁) ∧ VG.Proof.MdStream.X86_64.Setup σ₂ s₂ (N σ₂)) hf.verified hf.ct
    fun s₁ s₂ ⟨_, σ₁, σ₂, hp, h₁, h₂⟩ => by
      obtain ⟨⟨_, _, _, _, hk₁, k₁⟩, ⟨_, _, _, _, hk₂, k₂⟩, ebx, e15, esi, esp, eN⟩ := hP _ _ hp
      obtain ⟨p₁, c₁, w₁⟩ := VG.Proof.MdStream.X86_64.call_hyps H hk₁ k₁ h₁
      obtain ⟨p₂, c₂, w₂⟩ := VG.Proof.MdStream.X86_64.call_hyps H hk₂ k₂ h₂
      refine ⟨_, _, _, _, p₁, p₂, ?_, c₁, w₁, c₂, w₂, ?_⟩
      · simp only [VG.Proof.MdStream.X86_64.compressK, State.withRegions_gpr,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp)]
        exact ⟨by rw [h₁.rdi, h₂.rdi, ebx], by rw [h₁.rsi, h₂.rsi, esi], by rw [h₁.rdx, h₂.rdx, eN],
          by rw [h₁.rcx, h₂.rcx, e15]⟩
      · rw [h₁.cs _ (by simp [calleeSaved]), h₂.cs _ (by simp [calleeSaved]), esp]
  have tl := RelCT.taint (A := taint) (P := fun _ _ => True) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (c := .block [.mov .rbx (.reg .rdi), .mov .r15 (.reg .rcx)])
    (by taint_decide)
  exact su.seq (cl.seq tl)

/-- `compressAt` is constant time, in runs that agree on its arguments. -/
theorem compressAt_rel {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {P' : State → State → Prop}
    (hP : ∀ s₁ s₂, P' s₁ s₂ → (∃ a b c, VG.Proof.MdStream.X86_64.CallOk P s₁ a b c) ∧ (∃ a b c, VG.Proof.MdStream.X86_64.CallOk P s₂ a b c) ∧
      s₁.gpr .rbx = s₂.gpr .rbx ∧ s₁.gpr .r15 = s₂.gpr .r15 ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rsp = s₂.gpr .rsp) :
    RelCT isa P' (compressAt name code) fun _ _ => True :=
  VG.Proof.MdStream.X86_64.compressWith_rel H VG.Proof.MdStream.X86_64.setsN_one ⟨_, by taint_decide⟩ hf fun s₁ s₂ hp =>
    let ⟨⟨a, b, c, h₁⟩, ⟨a', b', c', h₂⟩, e⟩ := hP s₁ s₂ hp
    ⟨⟨a, b, c, 1, rfl, by rw [Nat.mul_one]; exact h₁⟩, ⟨a', b', c', 1, rfl, by rw [Nat.mul_one]; exact h₂⟩,
      e.1, e.2.1, e.2.2.1, e.2.2.2, rfl⟩

end

/-! ## One instruction at a time

Weakest-precondition rules for the instruction forms used here, exposing
only what changes, so that proofs about a block stay small. -/

/-- `s'` is `s` with register `d` set to `v` (flags aside). -/
structure Upd (s s' : State) (d : Reg) (v : BitVec 64) : Prop where
  gpr : s'.gpr d = v
  other : ∀ r, r ≠ d → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Upd.setReg (s : State) (d : Reg) (v : BitVec 64) : VG.Proof.MdStream.X86_64.Upd s (s.setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem Upd.flags (s : State) {w : Nat} (d : Reg) (x : BitVec w) (c o : Bool) (v : BitVec 64) :
    VG.Proof.MdStream.X86_64.Upd s ((arithFlags s x c o).setReg d v) d v :=
  ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h], rfl, rfl, rfl⟩

theorem WP.cons {i : Instr} {is : List Instr} {s s' : State} {Q : State → Prop}
    (h : exec i s = some s') (k : WP isa (.block is) s' Q) : WP isa (.block (i :: is)) s Q :=
  WP.block_cons_iff.mpr ⟨s', h, k⟩

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem wp_mov {d r : Reg} (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr r) → s'.zf = s.zf → s'.cf = s.cf →
    WP isa (.block is) s' Q) : WP isa (.block (.mov d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_mov32i {d : Reg} {v : BitVec 32} (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (v.setWidth 64) → s'.zf = s.zf →
    s'.cf = s.cf → WP isa (.block is) s' Q) : WP isa (.block (.mov32 d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _) rfl rfl)

theorem wp_addi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr d + v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_subi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr d - v.signExtend 64) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_sub {d r : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr d - s.gpr r) → s'.zf = some (s.gpr d - s.gpr r == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .sub d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_add {d r : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr d + s.gpr r) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_mov32m {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 4)
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d ((s.mem.readW a 32).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov32 d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem.readW a 32).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc32, State.load32, State.setReg32, ha, hin]

theorem wp_bswap32 {d : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d ((bswap32 ((s.gpr d).setWidth 32)).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap32 d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

theorem wp_store32 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 32) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store32 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 32) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store32, ha, hout]

theorem wp_movm {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 8)
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.mem.readW a 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem m) :: is)) s Q := by
  refine WP.cons (s' := s.setReg d (s.mem.readW a 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, readSrc, State.load64, ha, hin]

theorem wp_andi {d : Reg} {v : BitVec 32}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr d &&& v.signExtend 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_shr {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 63)
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (s.gpr d >>> n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q := by
  refine WP.cons (s' := (s.setFlags (some ((s.gpr d).getLsbD (n - 1)))
    (if n = 1 then some (s.gpr d).msb else none) (some ((s.gpr d >>> n) == 0))
    (some (s.gpr d >>> n).msb)).setReg d (s.gpr d >>> n)) ?_ (k _ ?_)
  · simp [exec, execShift, hn]
  · exact ⟨by simp [State.setReg], fun r h => by simp [State.setReg, h]; rfl, rfl, rfl, rfl⟩

/-- `cmp d, r`: CF is `d < r` (unsigned). -/
theorem wp_cmp {d r : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (s.gpr r).toNat)) →
      s'.zf = some (s.gpr d - s.gpr r == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.reg r) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_cmpi {d : Reg} {v : BitVec 32}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.cf = some (decide ((s.gpr d).toNat < (v.signExtend 64).toNat)) →
      s'.zf = some (s.gpr d - v.signExtend 64 == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .cmp d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl rfl)

theorem wp_test {d : Reg}
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr →
      s'.zf = some (s.gpr d &&& s.gpr d == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .test d (.reg d) :: is)) s Q :=
  WP.cons rfl (k _ rfl rfl rfl rfl rfl)

theorem wp_movzx8 {d : Reg} {m : MemOp} {a : Addr} (ha : s.ea m = a)
    (hin : InRegions (s.rd ++ s.wr) a 1)
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d ((s.mem a).setWidth 64) → WP isa (.block is) s' Q) :
    WP isa (.block (.movzx8 d m :: is)) s Q := by
  refine WP.cons (s' := s.setReg d ((s.mem a).setWidth 64)) ?_ (k _ (Upd.setReg _ _ _))
  simp [exec, State.load8, ha, hin]

theorem wp_store8 {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 1)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a ((s.gpr r).setWidth 8) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store8 m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a ((s.gpr r).setWidth 8) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store8, ha, hout]

theorem wp_store {m : MemOp} {r : Reg} {a : Addr} (ha : s.ea m = a) (hout : InRegions s.wr a 8)
    (k : ∀ s', s'.gpr = s.gpr → s'.mem = s.mem.writeW a (s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → WP isa (.block is) s' Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine WP.cons (s' := { s with mem := s.mem.writeW a (s.gpr r) }) ?_ (k _ rfl rfl rfl rfl)
  simp [exec, State.store64, ha, hout]

theorem wp_bswap {d : Reg}
    (k : ∀ s', VG.Proof.MdStream.X86_64.Upd s s' d (bswap64 (s.gpr d)) → WP isa (.block is) s' Q) :
    WP isa (.block (.bswap d :: is)) s Q :=
  WP.cons rfl (k _ (Upd.setReg _ _ _))

end

/-- `test r, r`, as a block of its own. -/
theorem test_ok {s : State} (r : Reg) :
    WP isa (.block [.alu .test r (.reg r)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.zf = some (s.gpr r &&& s.gpr r == 0) :=
  VG.Proof.MdStream.X86_64.wp_test fun _ g m rd wr z => WP.block_nil ⟨g, m, rd, wr, z⟩

theorem WP.seq_assoc {M : ISA} {a b c : Prog M} {s : M.State} {Q : M.State → Prop} :
    WP M (.seq (.seq a b) c) s Q ↔ WP M (.seq a (.seq b c)) s Q := by
  simp only [WP.seq_iff]

end VG.Proof.MdStream.X86_64

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.X86_64.FinalizeCT`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `finalize`

The functional correctness of `finalize`, for any hash function (`Md`) whose
code stores the length field and writes the digest as `Shape` says, and any
correct compression function (`CalleeOk`).
-/

namespace VG.Proof.MdStream.X86_64.Finalize

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame writeBytes_append bytesAt_congr)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev cnt : Nat := (s₀.gpr .rsi).toNat
abbrev out : Addr := s₀.gpr .rdx
abbrev scr : Addr := s₀.gpr .rcx
abbrev stR : Region := ⟨VG.Proof.MdStream.X86_64.Finalize.st s₀, P.N + P.B⟩
abbrev outR : Region := ⟨VG.Proof.MdStream.X86_64.Finalize.out s₀, P.N⟩
abbrev scR : Region := ⟨VG.Proof.MdStream.X86_64.Finalize.scr s₀, P.so + 48⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of the compression function stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The buffer. -/
abbrev buf : Addr := VG.Proof.MdStream.X86_64.Finalize.st s₀ + BitVec.ofNat 64 P.N

/-- The end of the zeros in a block: before the length field in the last
block (`k = 0`). -/
def lim (k : Nat) : Nat := if k = 0 then P.B - P.L else P.B

end

section
variable {P : Params} (H : Md P.B P.N P.L) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) m ∧ s₀.gpr .rsi = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the last. -/
def Fin1 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (VG.Proof.MdStream.X86_64.Finalize.st s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) n ++ List.replicate (P.B - n) 0).getD t 0))
    (H.parse fun t => (List.replicate (P.B - P.L) 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block. -/
def Fin0 (mem : Mem) (n : Nat) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (VG.Proof.MdStream.X86_64.Finalize.st s₀))
    (H.parse fun t => (bytesAt mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) n ++ List.replicate (P.B - P.L - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [VG.Proof.MdStream.X86_64.Finalize.stR P s₀, VG.Proof.MdStream.X86_64.Finalize.outR P s₀, VG.Proof.MdStream.X86_64.Finalize.scR P s₀]
  st_out : (VG.Proof.MdStream.X86_64.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.outR P s₀)
  st_scr : (VG.Proof.MdStream.X86_64.Finalize.stR P s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.scR P s₀)
  out_scr : (VG.Proof.MdStream.X86_64.Finalize.outR P s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.scR P s₀)
  ret_st : (VG.Proof.MdStream.X86_64.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.stR P s₀)
  ret_out : (VG.Proof.MdStream.X86_64.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.outR P s₀)
  ret_scr : (VG.Proof.MdStream.X86_64.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.scR P s₀)
  stk_st : (VG.Proof.MdStream.X86_64.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.stR P s₀)
  stk_out : (VG.Proof.MdStream.X86_64.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.outR P s₀)
  stk_scr : (VG.Proof.MdStream.X86_64.Finalize.stkR s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.scR P s₀)

theorem pre_of {P : Params} {H : Md P.B P.N P.L} {s₀ : State} (h : (VG.Proof.MdStream.X86_64.finK H).pre s₀) : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (VG.Proof.MdStream.X86_64.Finalize.retR s₀).Disjoint (VG.Proof.MdStream.X86_64.Finalize.stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (Nat.le_refl _) (by omega)
  rwa [BitVec.sub_add_cancel] at this

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = VG.Proof.MdStream.X86_64.Finalize.st s₀
  r15 : s.gpr .r15 = VG.Proof.MdStream.X86_64.Finalize.scr s₀
  rbp : s.gpr .rbp = VG.Proof.MdStream.X86_64.Finalize.out s₀
  r12 : s.gpr .r12 = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [VG.Proof.MdStream.X86_64.Finalize.stR P s₀, VG.Proof.MdStream.X86_64.Finalize.scR P s₀, VG.Proof.MdStream.X86_64.Finalize.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.X86_64.Saved P s₀ .rcx s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered. -/
structure LInv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k n : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s where
  k_le : k ≤ 1
  n_le : n ≤ VG.Proof.MdStream.X86_64.Finalize.lim P k
  r13 : s.gpr .r13 = BitVec.ofNat 64 n
  r14 : s.gpr .r14 = BitVec.ofNat 64 k
  hash : ∀ iv m, VG.Proof.MdStream.X86_64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then VG.Proof.MdStream.X86_64.Finalize.Fin1 H s₀ s.mem n m else VG.Proof.MdStream.X86_64.Finalize.Fin0 H s₀ s.mem n m)

/-- All blocks are compressed. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s ∧ ∀ iv m, VG.Proof.MdStream.X86_64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀))

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem lim_le (k : Nat) : VG.Proof.MdStream.X86_64.Finalize.lim P k ≤ P.B := by unfold VG.Proof.MdStream.X86_64.Finalize.lim; split <;> omega
theorem lim_ge (k : Nat) : P.B - P.L ≤ VG.Proof.MdStream.X86_64.Finalize.lim P k := by unfold VG.Proof.MdStream.X86_64.Finalize.lim; split <;> omega

theorem buf_add (s₀ : State) (n : Nat) : VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n = VG.Proof.MdStream.X86_64.Finalize.st s₀ + BitVec.ofNat 64 (P.N + n) :=
  VG.Proof.MdStream.X86_64.add_ofNat _ _ _

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s' where
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

/-- Writing buffer bytes `[n, n + |xs|)` keeps `Common`. -/
theorem Common.writeBuf (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {s : State} (h : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ P.B) :
    Frame [VG.Proof.MdStream.X86_64.Finalize.stR P s₀] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Frame [VG.Proof.MdStream.X86_64.Finalize.stR P s₀, VG.Proof.MdStream.X86_64.Finalize.scR P s₀, VG.Proof.MdStream.X86_64.Finalize.stkR s₀] s₀.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      VG.Proof.MdStream.X86_64.Saved P s₀ .rcx (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have := hd.N; have := hd.B; have := hd.so
  have hf : Frame [VG.Proof.MdStream.X86_64.Finalize.stR P s₀] s.mem (VG.WriteBytes.writeBytes s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n) xs) := by
    refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
    rw [VG.Proof.MdStream.X86_64.Finalize.buf_add]
    exact VG.Proof.MdStream.X86_64.contains_offset (by omega) (by omega)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  have hd' := VG.Proof.MdStream.X86_64.saved_offset hd hp'
  refine hf.readW (r := ⟨VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact (hp.st_scr.symm.sub_left (by rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega)))

/-! ## Zeroing the buffer -/

/-- Zeroing buffer bytes `[n, lim)` from state `sI`: `j` of them done. -/
structure Zero (P : Params) (s₀ : State) (sI : State) (n lim j : Nat) (s : State) : Prop where
  j_le : j ≤ lim - n
  keep : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp, .r14], s.gpr r = sI.gpr r
  rd : s.rd = sI.rd
  wr : s.wr = sI.wr
  r9 : s.gpr .r9 = 0
  r13 : s.gpr .r13 = BitVec.ofNat 64 (n + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (lim - n - j)
  mem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ P.B) (hj : j < lim - n) {s : State} (h : VG.Proof.MdStream.X86_64.Finalize.Zero P s₀ sI n lim j s) :
    WP isa (.block [.store8 (bufByte P) .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) s fun s' =>
      VG.Proof.MdStream.X86_64.Finalize.Zero P s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have := hd.N; have := hd.B
  have hrbx : s.gpr .rbx = VG.Proof.MdStream.X86_64.Finalize.st s₀ := by rw [h.keep _ (by simp), hC.rbx]
  have hout : InRegions s.wr (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [VG.Proof.MdStream.X86_64.add_ofNat, VG.Proof.MdStream.X86_64.Finalize.buf_add]
    exact VG.Proof.MdStream.X86_64.contains_offset (by omega) (by omega)
  refine VG.Proof.MdStream.X86_64.wp_store8 (r := .r9) (a := VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_ hout
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  · simp only [State.ea, bufByte, VG.Proof.MdStream.X86_64.Finalize.buf, hrbx, h.r13, BitVec.ofNat_add, BitVec.mul_one, VG.Proof.MdStream.X86_64.ofInt_natCast]
    ac_rfl
  refine VG.Proof.MdStream.X86_64.wp_addi fun s₂ u₂ => VG.Proof.MdStream.X86_64.wp_subi fun s₃ u₃ hz₃ => WP.block_nil ⟨⟨by omega, fun r hr => ?_,
    by rw [u₃.rd, u₂.rd, rd₁, h.rd], by rw [u₃.wr, u₂.wr, wr₁, h.wr], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .rax ∧ r ≠ .r13 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₃.other r this.1, u₂.other r this.2, g₁, h.keep r hr]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.r9]
  · rw [u₃.other _ (by decide), u₂.gpr, g₁, h.r13, VG.Proof.MdStream.X86_64.sx1, ← Nat.add_assoc, VG.Proof.MdStream.X86_64.ofNat_succ]
  · rw [u₃.gpr, u₂.other _ (by decide), g₁, h.rax, VG.Proof.MdStream.X86_64.sx1, VG.Proof.MdStream.X86_64.ofNat_pred (by omega), Nat.sub_sub]
  · rw [u₃.mem, u₂.mem, m₁, h.r9, h.mem, List.replicate_succ',
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega), List.length_replicate]
    rfl
  · rw [hz₃, u₂.other _ (by decide), g₁, h.rax, VG.Proof.MdStream.X86_64.sx1, VG.Proof.MdStream.X86_64.ofNat_pred (by omega), VG.Proof.MdStream.X86_64.ofNat_beq_zero (by omega),
      Nat.sub_sub, Nat.sub_sub]

theorem zero_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {sI : State} (hC : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ P.B) (hn : n ≤ lim) {s : State} (h : VG.Proof.MdStream.X86_64.Finalize.Zero P s₀ sI n lim 0 s)
    (hz : s.zf = some (decide (lim - n = 0))) :
    WP isa (.ite .e (.block []) (zeroLoop P)) s (VG.Proof.MdStream.X86_64.Finalize.Zero P s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (hb ▸ h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ VG.Proof.MdStream.X86_64.Finalize.Zero P s₀ sI n lim j s)
      ?_ (lim - n) s ⟨0, rfl, by omega, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (VG.Proof.MdStream.X86_64.Finalize.zero_step hd hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by simp [eval, hz', hl], ?_⟩
      rwa [show j + 1 = lim - n by omega] at hZ'
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega, j + 1, rfl, by omega, hZ'⟩

/-! ## One block -/

/-- The call of the compression function's requirements. -/
theorem Common.callOk (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {s : State} (hC : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s)
    (hrsi : s.gpr .rsi = VG.Proof.MdStream.X86_64.Finalize.buf P s₀) : VG.Proof.MdStream.X86_64.CallOk P s (VG.Proof.MdStream.X86_64.Finalize.st s₀) (VG.Proof.MdStream.X86_64.Finalize.scr s₀) (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) := by
  have := hd.N; have := hd.B; have := hd.so
  have eN : Region.Sub ⟨VG.Proof.MdStream.X86_64.Finalize.st s₀, P.N⟩ (VG.Proof.MdStream.X86_64.Finalize.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.X86_64.Finalize.scr s₀, P.so⟩ (VG.Proof.MdStream.X86_64.Finalize.scR P s₀) := Region.sub_prefix (by omega)
  have eb : Region.Sub ⟨VG.Proof.MdStream.X86_64.Finalize.buf P s₀, P.B⟩ (VG.Proof.MdStream.X86_64.Finalize.stR P s₀) := VG.Proof.MdStream.X86_64.sub_offset (off := P.N) (by omega) (by omega)
  have hsp := hC.rsp
  refine ⟨hC.rbx, hC.r15, hrsi, (hp.st_scr.sub_left eN).sub_right eso, ?_,
    (hp.st_scr.sub_left eb).sub_right eso, by rw [hsp]; exact hp.stk_st.sub_right eN,
    by rw [hsp]; exact hp.stk_scr.sub_right eso, by rw [hsp]; exact hp.stk_st.sub_right eb, ?_, ?_⟩
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp, P.N, rfl, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.scR P s₀, by simp, 0, by simp, by simp⟩

/-- The compression of the buffer. -/
theorem compress_buf (hd : VG.Proof.MdStream.X86_64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {s : State} (hC : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s) (hrsi : s.gpr .rsi = VG.Proof.MdStream.X86_64.Finalize.buf P s₀) {Q : State → Prop}
    (hQ : ∀ s', VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀)) (H.blockAt s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀)) →
      s'.gpr .rdi = VG.Proof.MdStream.X86_64.Finalize.st s₀ → s'.gpr .rcx = VG.Proof.MdStream.X86_64.Finalize.scr s₀ → Q s') :
    WP isa (compressAt name code) s Q := by
  have := hd.N; have := hd.B; have := hd.so
  have eN : Region.Sub ⟨VG.Proof.MdStream.X86_64.Finalize.st s₀, P.N⟩ (VG.Proof.MdStream.X86_64.Finalize.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.X86_64.Finalize.scr s₀, P.so⟩ (VG.Proof.MdStream.X86_64.Finalize.scR P s₀) := Region.sub_prefix (by omega)
  have hsp := hC.rsp
  refine VG.Proof.MdStream.X86_64.compressAt_ok H hf (hC.callOk hd hp hrsi) (by omega) (by omega)
    fun s' hrd hwr hcs hf hstate hdi hcx => hQ s' ?_ hcs hstate hdi hcx
  have cs : ∀ r, r ∈ calleeSaved → s'.gpr r = s.gpr r := hcs
  refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.rbx,
    by rw [cs _ (by decide)]; exact hC.r15, by rw [cs _ (by decide)]; exact hC.rbp,
    by rw [cs _ (by decide)]; exact hC.r12, by rw [cs _ (by decide)]; exact hC.rsp,
    hC.frame.trans (hf.sub ?_), fun p hp' => ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp, eN⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.scR P s₀, by simp, eso⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Finalize.stkR s₀, by simp, by rw [hsp]; exact fun _ h => h⟩
  · rw [← hC.saved p hp']
    have hd' := VG.Proof.MdStream.X86_64.saved_offset hd hp'
    refine hf.readW (r := ⟨VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_
      (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact (hp.st_scr.symm.sub_left (by rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega))).sub_right eN
    · rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact Offset.disjoint_base _ hd'.1 (by omega)
    · rw [hsp]
      exact hp.stk_scr.symm.sub_left (by rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega))

end

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (k = 0 ∧ eval .e s = some false ∧ VG.Proof.MdStream.X86_64.Finalize.Done H s₀ s ∧ s.gpr .rdi = VG.Proof.MdStream.X86_64.Finalize.st s₀ ∧ s.gpr .rcx = VG.Proof.MdStream.X86_64.Finalize.scr s₀) ∨
    (k = 1 ∧ eval .e s = some true ∧ VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ 0 0 s)

/-- Before the call of the compression function: the block to compress is
ready in the buffer, and compressing it finishes the iteration. -/
def Mid {P : Params} (H : Md P.B P.N P.L) (name : String) (code : Prog isa) (s₀ : State) (k : Nat)
    (s : State) : Prop :=
  VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s ∧ s.gpr .rsi = VG.Proof.MdStream.X86_64.Finalize.buf P s₀ ∧
    WP isa (.seq (compressAt name code) (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)])) s
      (VG.Proof.MdStream.X86_64.Finalize.Step H s₀ k)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pad_ok (hd : VG.Proof.MdStream.X86_64.Dims P) (hs : VG.Proof.MdStream.X86_64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {k n : Nat} {s : State} (h : VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ k n s) :
    WP isa (finalizePad P) s (VG.Proof.MdStream.X86_64.Finalize.Mid H name code s₀ k) := by
  have hk := h.k_le; have hn := h.n_le
  have hC := h.toCommon
  have := hd.N; have := hd.B; have := hd.L
  have hlim := VG.Proof.MdStream.X86_64.Finalize.lim_le (P := P) k; have hlim' := VG.Proof.MdStream.X86_64.Finalize.lim_ge (P := P) k
  unfold finalizePad
  -- `rax := B` or `B - L`: the end of the zeros.
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_mov32i fun s₁ u₁ _ _ => VG.Proof.MdStream.X86_64.wp_test fun s₂ g₂ m₂ rd₂ wr₂ z₂ => WP.block_nil ?_)
  have hz₂ : s₂.zf = some (decide (k = 0)) := by
    rw [z₂, u₁.other _ (by decide), h.r14, BitVec.and_self, VG.Proof.MdStream.X86_64.ofNat_beq_zero (by omega)]
  have hne : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], r ≠ .rax := by decide
  refine WP.seq (WP.mono (Q := fun (s₃ : State) => s₃.gpr .rax = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Finalize.lim P k) ∧
      (∀ r, r ≠ .rax → s₃.gpr r = s.gpr r) ∧ s₃.mem = s.mem ∧ s₃.rd = s.rd ∧ s₃.wr = s.wr) ?_
    fun s₃ ⟨hrax₃, g₃, m₃, rd₃, wr₃⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      refine VG.Proof.MdStream.X86_64.wp_mov32i fun s₃ u₃ _ _ => WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [u₃.gpr, VG.Proof.MdStream.X86_64.zx_ofNat (by omega)]; rfl
      · rw [u₃.other r hr, g₂, u₁.other r hr]
      · rw [u₃.mem, m₂, u₁.mem]
      · rw [u₃.rd, rd₂, u₁.rd]
      · rw [u₃.wr, wr₂, u₁.wr]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
      · rw [g₂, u₁.gpr, VG.Proof.MdStream.X86_64.zx_ofNat (by omega)]; simp [VG.Proof.MdStream.X86_64.Finalize.lim, hb]
      · rw [g₂, u₁.other r hr]
      · rw [m₂, u₁.mem]
      · rw [rd₂, u₁.rd]
      · rw [wr₂, u₁.wr]
  -- Zero the rest of the buffer, up to `lim`.
  have hC₃ : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₃ := hC.of_gpr (fun r hr => g₃ r (hne r hr)) m₃ rd₃ wr₃
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_mov32i fun s₄ u₄ _ _ => VG.Proof.MdStream.X86_64.wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have hrax₅ : s₅.gpr .rax = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Finalize.lim P k - n) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₄.other _ (by decide), hrax₃, g₃ _ (by decide), h.r13,
      VG.Proof.MdStream.X86_64.sub_ofNat (by omega)]
  have hZ : VG.Proof.MdStream.X86_64.Finalize.Zero P s₀ s n (VG.Proof.MdStream.X86_64.Finalize.lim P k) 0 s₅ := by
    refine ⟨Nat.zero_le _, fun r hr => ?_, by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃], ?_, ?_, ?_, ?_⟩
    · have : r ≠ .rax ∧ r ≠ .r9 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [u₅.other r this.1, u₄.other r this.2, g₃ r this.1]
    · rw [u₅.other _ (by decide), u₄.gpr]; rfl
    · rw [u₅.other _ (by decide), u₄.other _ (by decide), g₃ _ (by decide), h.r13, Nat.add_zero]
    · rw [hrax₅, Nat.sub_zero]
    · rw [u₅.mem, u₄.mem, m₃, List.replicate_zero, VG.WriteBytes.writeBytes_nil]
  have hz₅ : s₅.zf = some (decide (VG.Proof.MdStream.X86_64.Finalize.lim P k - n = 0)) := by
    rw [z₅, ← u₅.gpr, hrax₅, VG.Proof.MdStream.X86_64.ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86_64.Finalize.zero_ok hd hp hC hlim hn hZ hz₅) fun s₆ hZ₆ => ?_)
  obtain ⟨hf₆, hfr₆, hsv₆⟩ := hC.writeBuf hd hp (n := n) (xs := List.replicate (VG.Proof.MdStream.X86_64.Finalize.lim P k - n) 0)
    (by simp only [List.length_replicate]; omega)
  have hC₆ : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₆ :=
    ⟨hZ₆.rd.trans hC.rd, hZ₆.wr.trans hC.wr, by rw [hZ₆.keep _ (by simp), hC.rbx],
      by rw [hZ₆.keep _ (by simp), hC.r15], by rw [hZ₆.keep _ (by simp), hC.rbp],
      by rw [hZ₆.keep _ (by simp), hC.r12], by rw [hZ₆.keep _ (by simp), hC.rsp],
      by rw [hZ₆.mem]; exact hfr₆, by rw [hZ₆.mem]; exact hsv₆⟩
  have hst₆ : H.stateAt s₆.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) = H.stateAt s.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) := by
    rw [hZ₆.mem]
    apply H.stateAt_congr
    intro i hi
    rw [VG.Proof.MdStream.X86_64.Finalize.buf_add]
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp only [List.length_replicate]; omega)
  have hby₆ : bytesAt s₆.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) (VG.Proof.MdStream.X86_64.Finalize.lim P k) =
      bytesAt s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) n ++ List.replicate (VG.Proof.MdStream.X86_64.Finalize.lim P k - n) 0 := by
    rw [hZ₆.mem, ← bytesAt_writeBytes _ _ _ _ (by simp only [List.length_replicate]; omega)]
    congr 1; simp only [List.length_replicate]; omega
  have h14₆ : s₆.gpr .r14 = BitVec.ofNat 64 k := by rw [hZ₆.keep _ (by simp), h.r14]
  -- In the last block, the length field.
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_test fun s₇ g₇ m₇ rd₇ wr₇ z₇ => WP.block_nil ?_)
  have hC₇ : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₇ := hC₆.of_gpr (fun r _ => by rw [g₇]) m₇ rd₇ wr₇
  have hz₇ : s₇.zf = some (decide (k = 0)) := by
    rw [z₇, h14₆, BitVec.and_self, VG.Proof.MdStream.X86_64.ofNat_beq_zero (by omega)]
  refine WP.seq (WP.mono (Q := fun (s₈ : State) => VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₈ ∧ s₈.gpr .r14 = BitVec.ofNat 64 k ∧
      H.stateAt s₈.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) = H.stateAt s.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) ∧
      ∀ iv m, VG.Proof.MdStream.X86_64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → bytesAt s₈.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) P.B = bytesAt s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) n ++
        (if k = 1 then List.replicate (P.B - n) 0 else List.replicate (P.B - P.L - n) 0 ++
          H.lenBytes m.length)) ?_
    fun s₈ ⟨hC₈, h14₈, hst₈, hby₈⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₇]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb; subst hb
      have e : VG.Proof.MdStream.X86_64.Finalize.st s₀ + BitVec.ofNat 64 (P.N + P.B - P.L) = VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 (P.B - P.L) := by
        rw [VG.Proof.MdStream.X86_64.Finalize.buf_add, show P.N + (P.B - P.L) = P.N + P.B - P.L by omega]
      have hout : InRegions s₇.wr (s₇.gpr .rbx + BitVec.ofNat 64 (P.N + P.B - P.L)) P.L :=
        ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp [hC₇.wr, hp.wr], by rw [hC₇.rbx]; exact VG.Proof.MdStream.X86_64.contains_offset (by omega) (by omega)⟩
      refine WP.mono (hs.len s₇ hout) fun s₈ ⟨g₈, rd₈, wr₈, m₈⟩ => ?_
      rw [hC₇.rbx, hC₇.r12, e] at m₈
      have hlen := H.lenOf_length (s₀.gpr .rsi)
      obtain ⟨-, hfr, hsv⟩ := hC₆.writeBuf hd hp (n := P.B - P.L) (xs := H.lenOf (s₀.gpr .rsi)) (by omega)
      have hl0 : VG.Proof.MdStream.X86_64.Finalize.lim P 0 = P.B - P.L := rfl
      refine ⟨⟨rd₈.trans hC₇.rd, wr₈.trans hC₇.wr, by rw [g₈ _ (by decide), hC₇.rbx],
        by rw [g₈ _ (by decide), hC₇.r15], by rw [g₈ _ (by decide), hC₇.rbp], by rw [g₈ _ (by decide), hC₇.r12],
        by rw [g₈ _ (by decide), hC₇.rsp], by rw [m₈, m₇]; exact hfr, by rw [m₈, m₇]; exact hsv⟩,
        by rw [g₈ _ (by decide), g₇, h14₆], ?_, fun iv m hm hok => ?_⟩
      · rw [m₈, m₇, ← hst₆]
        apply H.stateAt_congr
        intro i hi
        rw [VG.Proof.MdStream.X86_64.Finalize.buf_add]
        exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by omega)
      · simp only [show ¬ ((0 : Nat) = 1) by decide, ite_false]
        rw [hm.2, H.lenOf_eq _ hok] at m₈
        have e := bytesAt_writeBytes s₆.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) (P.B - P.L) (H.lenBytes m.length)
          (by rw [H.lenBytes_length]; omega)
        rw [H.lenBytes_length, show P.B - P.L + P.L = P.B by omega] at e
        rw [m₈, m₇, e, ← hl0, hby₆, hl0, List.append_assoc]
    · simp only [decide_eq_false_iff_not] at hb
      have hk1 : k = 1 := by omega
      subst hk1
      refine WP.block_nil ⟨hC₇, by rw [g₇, h14₆], by rw [m₇, hst₆], fun iv m _ _ => ?_⟩
      have e1 : VG.Proof.MdStream.X86_64.Finalize.lim P 1 = P.B := rfl
      rw [e1] at hby₆
      rw [m₇, hby₆]; simp
  -- Compress the block.
  refine VG.Proof.MdStream.X86_64.wp_mov fun s₉ u₉ _ _ => VG.Proof.MdStream.X86_64.wp_addi fun s₁₀ u₁₀ => WP.block_nil ?_
  have hC₁₀ : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₁₀ := hC₈.of_gpr (fun r hr => by
      have : r ≠ .rsi := by simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
      rw [u₁₀.other r this, u₉.other r this]) (by rw [u₁₀.mem, u₉.mem]) (by rw [u₁₀.rd, u₉.rd])
    (by rw [u₁₀.wr, u₉.wr])
  have hrsi : s₁₀.gpr .rsi = VG.Proof.MdStream.X86_64.Finalize.buf P s₀ := by
    rw [u₁₀.gpr, u₉.gpr, hC₈.rbx, VG.Proof.MdStream.X86_64.sx_ofNat (by omega)]
  refine ⟨hC₁₀, hrsi, ?_⟩
  refine WP.seq (VG.Proof.MdStream.X86_64.Finalize.compress_buf hd hf hp hC₁₀ hrsi fun s₁₁ hC₁₁ cs₁₁ hst₁₁ hdi₁₁ hcx₁₁ => ?_)
  have h14₁₁ : s₁₁.gpr .r14 = BitVec.ofNat 64 k := by
    rw [cs₁₁ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h14₈]
  have hblk : ∀ iv m, VG.Proof.MdStream.X86_64.Finalize.R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s₁₀.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) = H.parse fun t =>
      (bytesAt s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) n ++ (if k = 1 then List.replicate (P.B - n) 0 else
        List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
    intro iv m hm hok
    apply H.parse_congr
    intro t ht
    rw [u₁₀.mem, u₉.mem]
    exact VG.Proof.MdStream.X86_64.bytesAt_getD (hby₈ iv m hm hok) ht
  -- Next block, if any.
  refine VG.Proof.MdStream.X86_64.wp_mov32i fun s₁₂ u₁₂ _ _ => VG.Proof.MdStream.X86_64.wp_subi fun s₁₃ u₁₃ z₁₃ => WP.block_nil ?_
  have hC₁₃ : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₁₃ := hC₁₁.of_gpr (fun r hr => by
      have : r ≠ .r14 ∧ r ≠ .r13 := by simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
      rw [u₁₃.other r this.1, u₁₂.other r this.2]) (by rw [u₁₃.mem, u₁₂.mem]) (by rw [u₁₃.rd, u₁₂.rd])
    (by rw [u₁₃.wr, u₁₂.wr])
  have hz : s₁₃.zf = some (decide (k = 1)) := by
    rw [z₁₃, u₁₂.other _ (by decide), h14₁₁, VG.Proof.MdStream.X86_64.sx1, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
      VG.Proof.MdStream.X86_64.sub_beq (by omega) (by omega)]
  have hst : ∀ iv m, VG.Proof.MdStream.X86_64.Finalize.R₀ H s₀ iv m → H.lenOk m.length →
      H.stateAt s₁₃.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) = H.compress (H.stateAt s.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀)) (H.parse fun t =>
        (bytesAt s.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) n ++ (if k = 1 then List.replicate (P.B - n) 0 else
          List.replicate (P.B - P.L - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
    intro iv m hm hok
    rw [u₁₃.mem, u₁₂.mem, hst₁₁, u₁₀.mem, u₉.mem, hst₈, ← hblk iv m hm hok, u₁₀.mem, u₉.mem]
  by_cases hk1 : k = 1
  · subst hk1
    refine .inr ⟨rfl, by simp [eval, hz], ⟨hC₁₃, by omega, by rw [VG.Proof.MdStream.X86_64.Finalize.lim]; simp, ?_, ?_, fun iv m hm hok => ?_⟩⟩
    · rw [u₁₃.other _ (by decide), u₁₂.gpr]; rfl
    · rw [u₁₃.gpr, u₁₂.other _ (by decide), h14₁₁, VG.Proof.MdStream.X86_64.sx1]; rfl
    · rw [h.hash iv m hm hok]
      simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.X86_64.Finalize.Fin1, VG.Proof.MdStream.X86_64.Finalize.Fin0, hst iv m hm hok]
      simp [bytesAt]
  · have hk0 : k = 0 := by omega
    subst hk0
    refine .inl ⟨rfl, by simp [eval, hz], ⟨hC₁₃, fun iv m hm hok => ?_⟩,
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), hdi₁₁],
      by rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), hcx₁₁]⟩
    rw [h.hash iv m hm hok, hst iv m hm hok]
    simp only [show ¬ (0 = 1) by decide, ite_false, VG.Proof.MdStream.X86_64.Finalize.Fin0, List.append_assoc]

theorem body_ok (hd : VG.Proof.MdStream.X86_64.Dims P) (hs : VG.Proof.MdStream.X86_64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {k n : Nat} {s : State} (h : VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ k n s) :
    WP isa (finalizeBody P name code) s (VG.Proof.MdStream.X86_64.Finalize.Step H s₀ k) :=
  WP.seq (WP.mono (VG.Proof.MdStream.X86_64.Finalize.pad_ok hd hs hf hp h) fun _ h => h.2.2)

/-! ## Prologue -/

theorem R₀.length (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.X86_64.Finalize.R₀ H s₀ iv m) :
    VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.X86_64.Finalize.cnt, h.2, BitVec.toNat_ofNat, hd.mod]

/-- The number of blocks after the first, `1` if the length field does not
fit in the first. -/
def kOf (P : Params) (s₀ : State) : Nat := if P.B - P.L + 1 ≤ VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1 then 1 else 0

theorem prologue_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) :
    WP isa (finalizeStart P) s₀ (VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ (VG.Proof.MdStream.X86_64.Finalize.kOf P s₀) (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1)) := by
  have := hd.N; have := hd.B; have := hd.L; have := hd.so
  have o : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions s₀.wr (VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨VG.Proof.MdStream.X86_64.Finalize.scR P s₀, by simp [hp.wr], VG.Proof.MdStream.X86_64.contains_offset' hd (by omega)⟩
  have hr : VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B < P.B := Nat.mod_lt _ hd.pos
  have hr' : (s₀.gpr .rsi).toNat % P.B < P.B := hr
  unfold finalizeStart
  rw [VG.Proof.MdStream.X86_64.save_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_store (a := VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 ((P.so : Nat) : Int)) rfl (o _ (by omega))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_)
  refine VG.Proof.MdStream.X86_64.wp_store (a := VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (by simp only [State.ea, at_, g₁])
    (by rw [wr₁]; exact o _ (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine VG.Proof.MdStream.X86_64.wp_store (a := VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int))
    (by simp only [State.ea, at_, g₂, g₁]) (by rw [wr₂, wr₁]; exact o _ (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine VG.Proof.MdStream.X86_64.wp_store (a := VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int))
    (by simp only [State.ea, at_, g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁]; exact o _ (by omega))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine VG.Proof.MdStream.X86_64.wp_store (a := VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int))
    (by simp only [State.ea, at_, g₄, g₃, g₂, g₁])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine VG.Proof.MdStream.X86_64.wp_store (a := VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int))
    (by simp only [State.ea, at_, g₅, g₄, g₃, g₂, g₁])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have hg₆ : s₆.gpr = s₀.gpr := by rw [g₆, g₅, g₄, g₃, g₂, g₁]
  have hm₆ : s₆.mem = VG.Proof.MdStream.X86_64.saveMem P s₀ .rcx := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁]; simp only [VG.Proof.MdStream.X86_64.saveMem, g₅, g₄, g₃, g₂, g₁]
  have hsf := VG.Proof.MdStream.X86_64.saveMem_frame (s₀ := s₀) (b := .rcx) hd
  refine VG.Proof.MdStream.X86_64.wp_mov fun s₇ u₇ _ _ => VG.Proof.MdStream.X86_64.wp_mov fun s₈ u₈ _ _ => VG.Proof.MdStream.X86_64.wp_mov fun s₉ u₉ _ _ => VG.Proof.MdStream.X86_64.wp_mov fun s₁₀ u₁₀ _ _ =>
    VG.Proof.MdStream.X86_64.wp_mov fun s₁₁ u₁₁ _ _ => VG.Proof.MdStream.X86_64.wp_andi fun s₁₂ u₁₂ => ?_
  have hC₁₂ : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₁₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, rd₆, rd₅, rd₄, rd₃, rd₂, rd₁]
    · rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, wr₆, wr₅, wr₄, wr₃, wr₂, wr₁]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.gpr, hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.gpr, u₇.other _ (by decide), hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr,
        u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), hg₆]
    · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
      exact hsf.mono (by simp)
    · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]; exact VG.Proof.MdStream.X86_64.saveMem_saved hd
  have hm₁₂ : s₁₂.mem = VG.Proof.MdStream.X86_64.saveMem P s₀ .rcx := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
  have hr13 : s₁₂.gpr .r13 = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), hg₆]
    exact VG.Proof.MdStream.X86_64.and_mask hd.B _
  -- The `0x80` byte.
  have hout : InRegions s₁₂.wr (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B)) 1 := by
    refine ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp [hC₁₂.wr, hp.wr], ?_⟩
    rw [VG.Proof.MdStream.X86_64.Finalize.buf_add]; exact VG.Proof.MdStream.X86_64.contains_offset (by omega) (by omega)
  refine VG.Proof.MdStream.X86_64.wp_mov32i fun s₁₃ u₁₃ _ _ => VG.Proof.MdStream.X86_64.wp_store8 (a := VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B)) ?_
    (by rw [u₁₃.wr]; exact hout) fun s₁₄ g₁₄ m₁₄ rd₁₄ wr₁₄ => ?_
  · simp only [State.ea, bufByte, u₁₃.other .rbx (by decide), u₁₃.other .r13 (by decide), hC₁₂.rbx, hr13,
      BitVec.mul_one, VG.Proof.MdStream.X86_64.ofInt_natCast, VG.Proof.MdStream.X86_64.Finalize.buf]
    ac_rfl
  obtain ⟨-, hfr, hsv⟩ := hC₁₂.writeBuf hd hp (n := VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B) (xs := [0x80]) (by simp; omega)
  have hm₁₄ : s₁₄.mem = VG.WriteBytes.writeBytes s₁₂.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀ + BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B)) [0x80] := by
    rw [m₁₄, u₁₃.mem, u₁₃.gpr, ← List.nil_append [(0x80 : Byte)], VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp),
      VG.WriteBytes.writeBytes_nil]
    simp
  refine VG.Proof.MdStream.X86_64.wp_addi fun s₁₅ u₁₅ => VG.Proof.MdStream.X86_64.wp_mov32i fun s₁₆ u₁₆ _ _ => VG.Proof.MdStream.X86_64.wp_cmpi fun s₁₇ g₁₇ m₁₇ rd₁₇ wr₁₇ cf₁₇ _ =>
    WP.block_nil ?_
  have keep : ∀ r, r ≠ .r13 → r ≠ .r14 → r ≠ .rax → s₁₇.gpr r = s₁₂.gpr r := fun r h1 h2 h3 => by
    rw [g₁₇, u₁₆.other r h2, u₁₅.other r h1, g₁₄, u₁₃.other r h3]
  have hm₁₇ : s₁₇.mem = s₁₄.mem := by rw [m₁₇, u₁₆.mem, u₁₅.mem]
  have hC₁₇ : VG.Proof.MdStream.X86_64.Finalize.Common P s₀ s₁₇ :=
    ⟨by rw [rd₁₇, u₁₆.rd, u₁₅.rd, rd₁₄, u₁₃.rd, hC₁₂.rd], by rw [wr₁₇, u₁₆.wr, u₁₅.wr, wr₁₄, u₁₃.wr, hC₁₂.wr],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rbx],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.r15],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rbp],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.r12],
      by rw [keep _ (by decide) (by decide) (by decide), hC₁₂.rsp],
      by rw [hm₁₇, hm₁₄]; exact hfr, by rw [hm₁₇, hm₁₄]; exact hsv⟩
  have hr13' : s₁₇.gpr .r13 = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1) := by
    rw [g₁₇, u₁₆.other _ (by decide), u₁₅.gpr, g₁₄, u₁₃.other _ (by decide), hr13, VG.Proof.MdStream.X86_64.sx1, VG.Proof.MdStream.X86_64.ofNat_succ]
  have hcf : s₁₇.cf = some (decide (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1 < P.B - P.L + 1)) := by
    rw [cf₁₇, u₁₆.other _ (by decide), u₁₅.gpr, g₁₄, u₁₃.other _ (by decide), hr13, VG.Proof.MdStream.X86_64.sx1, ← VG.Proof.MdStream.X86_64.ofNat_succ,
      VG.Proof.MdStream.X86_64.sx_ofNat (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1) (by omega), Nat.mod_eq_of_lt (a := P.B - P.L + 1) (by omega)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, VG.Proof.MdStream.X86_64.Finalize.R₀ H s₀ iv m → bytesAt s₁₇.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1) =
      Md.rest P.B m ++ [0x80] := by
    intro iv m hm
    have e := bytesAt_writeBytes s₁₂.mem (VG.Proof.MdStream.X86_64.Finalize.buf P s₀) (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B) [0x80] (by simp; omega)
    simp only [List.length_singleton] at e
    rw [hm₁₇, hm₁₄, e, hm₁₂]
    refine congrArg (· ++ [0x80]) ?_
    rw [hm.length hd]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := Nat.mod_lt m.length hd.pos
    have := hsf.bytes (R := VG.Proof.MdStream.X86_64.Finalize.stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega)
      (i := P.N + i) (by show P.N + i < P.N + P.B; omega)
    rwa [← VG.Proof.MdStream.X86_64.Finalize.buf_add] at this
  have hstate : H.stateAt s₁₇.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) = H.stateAt s₀.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₇, hm₁₄, VG.Proof.MdStream.X86_64.Finalize.buf_add, VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by simp; omega), hm₁₂]
    exact hsf.bytes (R := VG.Proof.MdStream.X86_64.Finalize.stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega)
      (by show i < P.N + P.B; omega)
  refine WP.ite (!decide (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1 < P.B - P.L + 1)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    rw [show VG.Proof.MdStream.X86_64.Finalize.kOf P s₀ = 1 from ite_eq_left_iff.mpr fun h => absurd hb h]
    refine VG.Proof.MdStream.X86_64.wp_mov32i fun s₁₈ u₁₈ _ _ => WP.block_nil ⟨hC₁₇.of_gpr (fun r hr => u₁₈.other r (by
      simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide)) u₁₈.mem u₁₈.rd u₁₈.wr,
      (Nat.le_refl _), by rw [VG.Proof.MdStream.X86_64.Finalize.lim]; simp; omega, by rw [u₁₈.other _ (by decide), hr13'],
      by rw [u₁₈.gpr]; rfl, fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [Md.hash_two H hd.pos (by omega) (by rw [← hm.length hd]; omega), VG.Proof.MdStream.X86_64.Finalize.Fin1, u₁₈.mem, hbytes iv m hm, hstate,
      hm.1.1, ← hm.length hd, show P.B - (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1) = P.B - 1 - VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B by omega]
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    rw [show VG.Proof.MdStream.X86_64.Finalize.kOf P s₀ = 0 from ite_eq_right_iff.mpr fun h => absurd hb (by omega)]
    refine WP.block_nil ⟨hC₁₇, by omega, by rw [VG.Proof.MdStream.X86_64.Finalize.lim]; simp; omega, hr13', ?_, fun iv m hm _ => ?_⟩
    · rw [g₁₇, u₁₆.gpr]; rfl
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [Md.hash_one H hd.pos (by rw [← hm.length hd]; omega), VG.Proof.MdStream.X86_64.Finalize.Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length hd, show P.B - P.L - (VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B + 1) = P.B - P.L - 1 - VG.Proof.MdStream.X86_64.Finalize.cnt s₀ % P.B by omega]

/-! ## Output and epilogue -/

set_option simprocs false in
theorem epilogue_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) {sD : State} (hD : VG.Proof.MdStream.X86_64.Finalize.Done H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r, r ≠ .rax → s.gpr r = sD.gpr r)
    (hm : s.mem = VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.X86_64.Finalize.out s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀))))
    (hdi : s.gpr .rdi = s₀.gpr .rdi) (hcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa (.block (restore P)) s fun s' =>
      gprPreserved s₀ s' ∧ (VG.Proof.MdStream.X86_64.finK H).post s₀ s' ∧ s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx := by
  have := hd.N; have := hd.so
  have hC := hD.1
  have hdl := H.digest_length (H.stateAt sD.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀))
  have hfo : Frame [VG.Proof.MdStream.X86_64.Finalize.outR P s₀] sD.mem (VG.WriteBytes.writeBytes sD.mem (VG.Proof.MdStream.X86_64.Finalize.out s₀) (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀)))) :=
    VG.WriteBytes.writeBytes_frame _ _ _ (by
      rw [show VG.Proof.MdStream.X86_64.Finalize.out s₀ = VG.Proof.MdStream.X86_64.Finalize.out s₀ + BitVec.ofNat 64 0 by simp]
      exact VG.Proof.MdStream.X86_64.contains_offset (by omega) (by omega))
  have i : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨VG.Proof.MdStream.X86_64.Finalize.scR P s₀, by simp [hrd, hwr, hp.wr], VG.Proof.MdStream.X86_64.contains_offset' hd (by omega)⟩
  have sv : ∀ r d, (r, d) ∈ saved P →
      s.mem.readW (VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 ((d : Nat) : Int)) 64 = s₀.gpr r := by
    intro r d hrd
    rw [hm, ← hC.saved _ hrd]
    have hd' := VG.Proof.MdStream.X86_64.saved_offset hd hrd
    refine hfo.readW (r := ⟨VG.Proof.MdStream.X86_64.Finalize.scr s₀ + BitVec.ofInt 64 (d : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact (hp.out_scr.symm.sub_left (by rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega)))
  have i0 := i P.so (by omega); have i1 := i (P.so + 8) (by omega); have i2 := i (P.so + 16) (by omega)
  have i3 := i (P.so + 24) (by omega); have i4 := i (P.so + 32) (by omega); have i5 := i (P.so + 40) (by omega)
  have g0 := sv .rbx P.so (by simp [saved]); have g1 := sv .rbp (P.so + 8) (by simp [saved])
  have g2 := sv .r12 (P.so + 16) (by simp [saved]); have g3 := sv .r13 (P.so + 24) (by simp [saved])
  have g4 := sv .r14 (P.so + 32) (by simp [saved]); have g5 := sv .r15 (P.so + 40) (by simp [saved])
  have hr15 : s.gpr .r15 = VG.Proof.MdStream.X86_64.Finalize.scr s₀ := by rw [hkeep _ (by decide), hC.r15]
  have hrsp : s.gpr .rsp = s₀.gpr .rsp := by rw [hkeep _ (by decide), hC.rsp]
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
    rw [hm, hfo.readW (Region.contains_self _ _) (by simpa using hp.ret_out) (by decide)]
    exact hC.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, VG.Proof.MdStream.X86_64.Finalize.ret_stk s₀⟩)
      (by decide)
  have hout : bytesAt s.mem (s₀.gpr .rdx) P.N = H.digest (H.stateAt sD.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀)) := by
    have e := bytesAt_writeBytes sD.mem (VG.Proof.MdStream.X86_64.Finalize.out s₀) 0 (H.digest (H.stateAt sD.mem (VG.Proof.MdStream.X86_64.Finalize.st s₀))) (by omega)
    rw [hdl, show VG.Proof.MdStream.X86_64.Finalize.out s₀ + BitVec.ofNat 64 0 = VG.Proof.MdStream.X86_64.Finalize.out s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (VG.Proof.MdStream.X86_64.Finalize.out s₀) 0 = [] from rfl, List.nil_append] at e
    rw [hm]; exact e
  apply WP.of_runBlock
  rw [VG.Proof.MdStream.X86_64.restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, VG.Proof.MdStream.X86_64.ea_at, State.load64,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun iv m hm' hok hc => ?_, hdi, hcx⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · rw [hout]; exact (hD.2 iv m ⟨hm', hc⟩ hok).symm

/-- `finalize` is correct, and leaves `rdi` and `rcx` as they were (which code
inlining it relies on). -/
theorem correct (hd : VG.Proof.MdStream.X86_64.Dims P) (hs : VG.Proof.MdStream.X86_64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) :
    WP isa (finalize P name code) s₀ fun s' => gprPreserved s₀ s' ∧ (VG.Proof.MdStream.X86_64.finK H).post s₀ s' ∧
      s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx := by
  have := hd.N; have := hd.B
  unfold finalize
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86_64.Finalize.prologue_ok (H := H) hd hp) fun s₁ hL => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => VG.Proof.MdStream.X86_64.Finalize.Done H s₀ s ∧ s.gpr .rdi = VG.Proof.MdStream.X86_64.Finalize.st s₀ ∧ s.gpr .rcx = VG.Proof.MdStream.X86_64.Finalize.scr s₀) ?_
    fun sD ⟨hD, hdi, hcx⟩ => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n, VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ i n s) ?_ (VG.Proof.MdStream.X86_64.Finalize.kOf P s₀) s₁ ⟨_, hL⟩
    rintro i s ⟨n, hL⟩
    refine WP.mono (VG.Proof.MdStream.X86_64.Finalize.body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨-, he, hD⟩ | ⟨rfl, he, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega, 0, hL'⟩
  · have hC := hD.1
    rw [WP.block_append_iff]
    refine WP.mono (hs.out sD ?_ ?_ ?_) fun s ⟨g, rd, wr, m⟩ =>
      VG.Proof.MdStream.X86_64.Finalize.epilogue_ok hd hp hD (rd.trans hC.rd) (wr.trans hC.wr) g (by rw [m, hC.rbp, hC.rbx])
        (by rw [g _ (by decide), hdi]) (by rw [g _ (by decide), hcx])
    · refine ⟨VG.Proof.MdStream.X86_64.Finalize.stR P s₀, by simp [hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hC.rbx]; simpa using VG.Proof.MdStream.X86_64.contains_offset (base := VG.Proof.MdStream.X86_64.Finalize.st s₀) (off := 0) (n := P.N) (len := P.N + P.B)
        (by omega) (by omega)
    · refine ⟨VG.Proof.MdStream.X86_64.Finalize.outR P s₀, by simp [hC.wr, hp.wr], ?_⟩
      rw [hC.rbp]; simpa using VG.Proof.MdStream.X86_64.contains_offset (base := VG.Proof.MdStream.X86_64.Finalize.out s₀) (off := 0) (n := P.N) (len := P.N)
        (by omega) (by omega)
    · rw [hC.rbx, hC.rbp]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega))

/-- A state satisfying the precondition. -/
def sat (P : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x2000, P.N⟩, ⟨0x3000, P.so + 48⟩]

/-- `finalize` is verified if it is constant time (`FinalizeCT.lean`) and
never loads MXCSR. -/
theorem verified_of (hd : VG.Proof.MdStream.X86_64.Dims P) (hs : VG.Proof.MdStream.X86_64.Shape H) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code)
    (hm : (finalize P name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (VG.Proof.MdStream.X86_64.finK H).pre (VG.Proof.MdStream.X86_64.finK H).pub (finalize P name code)) :
    Verified X86_64.target (finalize P name code) (VG.Proof.MdStream.X86_64.finK H) := by
  have := hd.N; have := hd.B; have := hd.so
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.X86_64.Finalize.correct hd hs hf (VG.Proof.MdStream.X86_64.Finalize.pre_of hs')
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2.1⟩
  · refine ⟨VG.Proof.MdStream.X86_64.Finalize.sat P, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [VG.Proof.MdStream.X86_64.Finalize.sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

end

end VG.Proof.MdStream.X86_64.Finalize

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `finalize` is constant time

This holds for any compression function (`CalleeOk`), so it is proven once
for every implementation, by relating two runs (`RelCT`) as for `update`
(`UpdateCT.lean`): the number of blocks to pad and the bytes buffered depend
only on `count`, so at every iteration correctness determines our registers
from the public arguments alone; between the calls the taint analysis proves
each piece constant time from that (`Taints`), and the calls are constant
time by `compressAt_rel`.
-/

namespace VG.Proof.MdStream.X86_64.Finalize

open VG VG.X86_64 VG.Impl.MdStream.X86_64

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.kOf {P : Params} {s₀ s₀' : State} (hq : VG.Proof.MdStream.X86_64.Finalize.PubEq s₀ s₀') : VG.Proof.MdStream.X86_64.Finalize.kOf P s₀ = VG.Proof.MdStream.X86_64.Finalize.kOf P s₀' := by
  have e : VG.Proof.MdStream.X86_64.Finalize.cnt s₀ = VG.Proof.MdStream.X86_64.Finalize.cnt s₀' := congrArg BitVec.toNat hq.rsi
  simp only [Finalize.kOf, e]

theorem PubEq.cnt {s₀ s₀' : State} (hq : VG.Proof.MdStream.X86_64.Finalize.PubEq s₀ s₀') : VG.Proof.MdStream.X86_64.Finalize.cnt s₀ = VG.Proof.MdStream.X86_64.Finalize.cnt s₀' :=
  congrArg BitVec.toNat hq.rsi

/-- The registers the pieces between the calls use. -/
abbrev regs : List Reg := [.rbx, .r15, .rbp, .r12, .rsp, .r13, .r14]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem LInv.agree {s₀ s₀' : State} (hq : VG.Proof.MdStream.X86_64.Finalize.PubEq s₀ s₀') {k n : Nat} {s s' : State} (h : VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ k n s)
    (h' : VG.Proof.MdStream.X86_64.Finalize.LInv H s₀' k n s') : ∀ r ∈ VG.Proof.MdStream.X86_64.Finalize.regs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [VG.Proof.MdStream.X86_64.Finalize.regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]; exact hq.rdi
  · rw [h.r15, h'.r15]; exact hq.rcx
  · rw [h.rbp, h'.rbp]; exact hq.rdx
  · rw [h.r12, h'.r12]; exact hq.rsi
  · rw [h.rsp, h'.rsp]; exact hq.rsp
  · rw [h.r13, h'.r13]
  · rw [h.r14, h'.r14]

variable (hd : VG.Proof.MdStream.X86_64.Dims P) (hs : VG.Proof.MdStream.X86_64.Shape H) (ht : VG.Proof.MdStream.X86_64.Taints P) {name : String} {code : Prog isa}
  (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s₀ s₀' : State} (hp : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀) (hp' : VG.Proof.MdStream.X86_64.Finalize.Pre P s₀') (hq : VG.Proof.MdStream.X86_64.Finalize.PubEq s₀ s₀')
include hd hs ht hf hp hp' hq

theorem body_rel {k n : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ k n s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.LInv H s₀' k n s₂) (finalizeBody P name code)
      fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.Step H s₀ k s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.Step H s₀' k s₂ := by
  obtain ⟨_, hpad⟩ := ht.finPad
  have pad : RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ k n s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.LInv H s₀' k n s₂) (finalizePad P)
      fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.Mid H name code s₀ k s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.Mid H name code s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs VG.Proof.MdStream.X86_64.Finalize.regs) (P := fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ k n s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.LInv H s₀' k n s₂)
      (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.1 h.2)) (c := finalizePad P) hpad).wp
      fun _ _ h => ⟨VG.Proof.MdStream.X86_64.Finalize.pad_ok hd hs hf hp h.1, VG.Proof.MdStream.X86_64.Finalize.pad_ok hd hs hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cmp : RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.Mid H name code s₀ k s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.Mid H name code s₀' k s₂) (compressAt name code)
      fun s₁ s₂ => WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (VG.Proof.MdStream.X86_64.Finalize.Step H s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (VG.Proof.MdStream.X86_64.Finalize.Step H s₀' k) :=
    ((VG.Proof.MdStream.X86_64.compressAt_rel H hf fun s₁ s₂ ⟨⟨C₁, si₁, _⟩, ⟨C₂, si₂, _⟩⟩ =>
      ⟨⟨_, _, _, C₁.callOk hd hp si₁⟩, ⟨_, _, _, C₂.callOk hd hp' si₂⟩,
        by rw [C₁.rbx, C₂.rbx]; exact hq.rdi, by rw [C₁.r15, C₂.r15]; exact hq.rcx,
        by rw [si₁, si₂]; exact congrArg (· + _) hq.rdi, by rw [C₁.rsp, C₂.rsp]; exact hq.rsp⟩).wp
      fun _ _ h => ⟨WP.seq_iff.mp h.1.2.2, WP.seq_iff.mp h.2.2.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ =>
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (VG.Proof.MdStream.X86_64.Finalize.Step H s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (VG.Proof.MdStream.X86_64.Finalize.Step H s₀' k))
      (.block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)])
      fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.Step H s₀ k s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.Step H s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block [.mov32 .r13 (.imm 0), .alu .sub .r14 (.imm 1)]) (by taint_decide)).wp
      fun _ _ h => h).mono (fun _ _ h => h) fun _ _ h => h.2
  exact pad.seq (cmp.seq fin)

theorem finalize_rel :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalize P name code) fun _ _ => True := by
  obtain ⟨_, hst⟩ := ht.finStart
  obtain ⟨_, hend⟩ := ht.finEnd
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalizeStart P) fun s₁ s₂ =>
      ∃ n, VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ (VG.Proof.MdStream.X86_64.Finalize.kOf P s₀) n s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.LInv H s₀' (VG.Proof.MdStream.X86_64.Finalize.kOf P s₀) n s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .rsp])
      (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (fun _ _ ⟨e, e'⟩ => Taint.agree_ofRegs fun r hr => by
        rw [e, e']
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.rsp) (c := finalizeStart P) hst).wp
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨VG.Proof.MdStream.X86_64.Finalize.prologue_ok (H := H) hd hp, VG.Proof.MdStream.X86_64.Finalize.prologue_ok (H := H) hd hp'⟩).mono
      (fun _ _ h => h) fun _ _ h => ⟨_, h.2.1, by rw [hq.kOf, hq.cnt]; exact h.2.2⟩
  have lp := RelCT.loop (M := isa) (body := finalizeBody P name code) (c := .e)
    (Q := fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.Done H s₀' s₂)
    (fun m s₁ s₂ => ∃ n, VG.Proof.MdStream.X86_64.Finalize.LInv H s₀ m n s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.LInv H s₀' m n s₂) (fun m => RelCT.exists_ fun n =>
      (VG.Proof.MdStream.X86_64.Finalize.body_rel hd hs ht hf hp hp' hq).mono (fun _ _ h => h) fun s₁ s₂ ⟨h₁, h₂⟩ => by
        rcases h₁ with ⟨rfl, z₁, D₁, -⟩ | ⟨rfl, z₁, L₁⟩ <;>
          rcases h₂ with ⟨h0, z₂, D₂, -⟩ | ⟨h1, z₂, L₂⟩
        · exact ⟨z₁.trans z₂.symm, fun _ => ⟨D₁, D₂⟩, fun h => absurd (z₁.symm.trans h) (by simp)⟩
        · cases h1
        · cases h0
        · exact ⟨z₁.trans z₂.symm, fun h => absurd (z₁.symm.trans h) (by simp),
            fun _ => ⟨0, by omega, 0, L₁, L₂⟩⟩) (VG.Proof.MdStream.X86_64.Finalize.kOf P s₀)
  have epi : RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Finalize.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Finalize.Done H s₀' s₂) (.block (P.out ++ restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rbx, .rbp, .r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1.rbx, h.2.1.rbx]; exact hq.rdi
      · rw [h.1.1.rbp, h.2.1.rbp]; exact hq.rdx
      · rw [h.1.1.r15, h.2.1.r15]; exact hq.rcx) hend
  exact pro.seq (lp.seq epi)

end

theorem pubEq_of {P : Params} {H : Md P.B P.N P.L} {s₁ s₂ : State} (h : (VG.Proof.MdStream.X86_64.finK H).pub s₁ s₂) : VG.Proof.MdStream.X86_64.Finalize.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem constantTime {P : Params} {H : Md P.B P.N P.L} (hd : VG.Proof.MdStream.X86_64.Dims P) (hs : VG.Proof.MdStream.X86_64.Shape H) (ht : VG.Proof.MdStream.X86_64.Taints P)
    {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) :
    ConstantTime isa (VG.Proof.MdStream.X86_64.finK H).pre (VG.Proof.MdStream.X86_64.finK H).pub (finalize P name code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (VG.Proof.MdStream.X86_64.Finalize.finalize_rel hd hs ht hf (VG.Proof.MdStream.X86_64.Finalize.pre_of h₁) (VG.Proof.MdStream.X86_64.Finalize.pre_of h₂) (VG.Proof.MdStream.X86_64.Finalize.pubEq_of hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified {P : Params} {H : Md P.B P.N P.L} (hd : VG.Proof.MdStream.X86_64.Dims P) (hs : VG.Proof.MdStream.X86_64.Shape H) (ht : VG.Proof.MdStream.X86_64.Taints P)
    {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code)
    (hm : (finalize P name code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize P name code) (VG.Proof.MdStream.X86_64.finK H) :=
  VG.Proof.MdStream.X86_64.Finalize.verified_of hd hs hf hm (VG.Proof.MdStream.X86_64.Finalize.constantTime hd hs ht hf)

end VG.Proof.MdStream.X86_64.Finalize

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.X86_64.UpdateCT`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `update`

The functional correctness of `update`, for any hash function (`Md`) and any
correct compression function (`CalleeOk`).
-/

namespace VG.Proof.MdStream.X86_64.Update

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Spec.Sha256 (bytesAt)
open VG.Proof.MdStream.Md (add_mod_of_eq add_mod_of_lt)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_snoc writeBytes_before bytesAt_writeBytes
  writeBytes_frame)

/-! ## The precondition -/

section
variable (P : Params) (s₀ : State)

abbrev st : Addr := s₀.gpr .rdi
abbrev cnt : Nat := (s₀.gpr .rsi).toNat
abbrev dp : Addr := s₀.gpr .rdx
abbrev len : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev stR : Region := ⟨VG.Proof.MdStream.X86_64.Update.st s₀, P.N + P.B⟩
abbrev dR : Region := ⟨VG.Proof.MdStream.X86_64.Update.dp s₀, VG.Proof.MdStream.X86_64.Update.len s₀⟩
/-- Where the call of the compression function stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
abbrev scR : Region := ⟨VG.Proof.MdStream.X86_64.Update.scr s₀, P.so + 48⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- The data. -/
abbrev D : List Byte := bytesAt s₀.mem (VG.Proof.MdStream.X86_64.Update.dp s₀) (VG.Proof.MdStream.X86_64.Update.len s₀)

end

/-- The messages the initial state represents, from `iv`. -/
def R₀ {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (VG.Proof.MdStream.X86_64.Update.st s₀) m ∧ s₀.gpr .rsi = BitVec.ofNat 64 m.length

structure Pre (P : Params) (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.MdStream.X86_64.Update.dR s₀]
  wr : s₀.wr = [VG.Proof.MdStream.X86_64.Update.stR P s₀, VG.Proof.MdStream.X86_64.Update.scR P s₀]
  st_scr : (VG.Proof.MdStream.X86_64.Update.stR P s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.scR P s₀)
  d_st : (VG.Proof.MdStream.X86_64.Update.dR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.stR P s₀)
  d_scr : (VG.Proof.MdStream.X86_64.Update.dR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.scR P s₀)
  ret_st : (VG.Proof.MdStream.X86_64.Update.retR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.stR P s₀)
  ret_scr : (VG.Proof.MdStream.X86_64.Update.retR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.scR P s₀)
  stk_st : (VG.Proof.MdStream.X86_64.Update.stkR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.stR P s₀)
  stk_d : (VG.Proof.MdStream.X86_64.Update.stkR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.dR s₀)
  stk_scr : (VG.Proof.MdStream.X86_64.Update.stkR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.scR P s₀)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem pre_of {s₀ : State} (h : (VG.Proof.MdStream.X86_64.updK H).pre s₀) : VG.Proof.MdStream.X86_64.Update.Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (VG.Proof.MdStream.X86_64.Update.retR s₀).Disjoint (VG.Proof.MdStream.X86_64.Update.stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (Nat.le_refl _) (by omega)
  rwa [BitVec.sub_add_cancel] at this

theorem R₀.length (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : VG.Proof.MdStream.X86_64.Update.R₀ H s₀ iv m) :
    VG.Proof.MdStream.X86_64.Update.cnt s₀ % P.B = m.length % P.B := by
  rw [VG.Proof.MdStream.X86_64.Update.cnt, h.2, BitVec.toNat_ofNat, hd.mod]

theorem len_lt (s₀ : State) : VG.Proof.MdStream.X86_64.Update.len s₀ < 2 ^ 64 := (s₀.gpr .rcx).isLt

theorem D_length (s₀ : State) : (VG.Proof.MdStream.X86_64.Update.D s₀).length = VG.Proof.MdStream.X86_64.Update.len s₀ := by simp [bytesAt]

end

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (P : Params) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ VG.Proof.MdStream.X86_64.Update.len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = VG.Proof.MdStream.X86_64.Update.st s₀
  r15 : s.gpr .r15 = VG.Proof.MdStream.X86_64.Update.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 c
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.len s₀ - c)
  frame : Frame [VG.Proof.MdStream.X86_64.Update.stR P s₀, VG.Proof.MdStream.X86_64.Update.scR P s₀, VG.Proof.MdStream.X86_64.Update.stkR s₀] s₀.mem s.mem
  saved : VG.Proof.MdStream.X86_64.Saved P s₀ .r8 s.mem

/-- The loop invariant: the state represents the message followed by the
first `c` bytes of data. -/
structure Inv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.X86_64.Update.Common P s₀ c s where
  r13 : s.gpr .r13 = BitVec.ofNat 64 ((VG.Proof.MdStream.X86_64.Update.cnt s₀ + c) % P.B)
  repr : ∀ iv m, VG.Proof.MdStream.X86_64.Update.R₀ H s₀ iv m → H.Repr iv s.mem (VG.Proof.MdStream.X86_64.Update.st s₀) (m ++ (VG.Proof.MdStream.X86_64.Update.D s₀).take c)

section
variable {P : Params} {H : Md P.B P.N P.L}

/-! ## Prologue and epilogue -/

theorem inv_zero (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {s : State} (hm : s.mem = VG.Proof.MdStream.X86_64.saveMem P s₀ .r8)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hrbx : s.gpr .rbx = VG.Proof.MdStream.X86_64.Update.st s₀) (hr15 : s.gpr .r15 = VG.Proof.MdStream.X86_64.Update.scr s₀)
    (hrsp : s.gpr .rsp = s₀.gpr .rsp) (hrbp : s.gpr .rbp = VG.Proof.MdStream.X86_64.Update.dp s₀) (hr12 : s.gpr .r12 = s₀.gpr .rcx)
    (hr13 : s.gpr .r13 = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.cnt s₀ % P.B)) : VG.Proof.MdStream.X86_64.Update.Inv H s₀ 0 s where
  c_le := Nat.zero_le _
  rd := hrd
  wr := hwr
  rbx := hrbx
  r15 := hr15
  rsp := hrsp
  rbp := by rw [hrbp]; simp
  r12 := by rw [hr12]; simp
  frame := by rw [hm]; exact (VG.Proof.MdStream.X86_64.saveMem_frame hd).mono fun r hr => by simp at hr; simp [hr]
  saved := by rw [hm]; exact VG.Proof.MdStream.X86_64.saveMem_saved hd
  r13 := by rw [hr13, Nat.add_zero]
  repr iv m hm₀ := by
    rw [List.take_zero, List.append_nil, hm]
    exact H.repr_congr hd.pos (fun i hi => (VG.Proof.MdStream.X86_64.saveMem_frame hd).bytes (R := VG.Proof.MdStream.X86_64.Update.stR P s₀)
      (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; have := hd.N; have := hd.B; omega) hi) hm₀.1

set_option simprocs false in
theorem prologue_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) :
    WP isa (.block (updateStart P)) s₀ (VG.Proof.MdStream.X86_64.Update.Inv H s₀ 0) := by
  have := hd.so
  have o : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions s₀.wr (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨VG.Proof.MdStream.X86_64.Update.scR P s₀, by simp [hp.wr], VG.Proof.MdStream.X86_64.contains_offset' hd (by omega)⟩
  have o0 := o P.so (by omega); have o1 := o (P.so + 8) (by omega); have o2 := o (P.so + 16) (by omega)
  have o3 := o (P.so + 24) (by omega); have o4 := o (P.so + 32) (by omega); have o5 := o (P.so + 40) (by omega)
  apply WP.of_runBlock
  rw [updateStart, VG.Proof.MdStream.X86_64.save_eq]
  simp only [List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, execAlu, readSrc, isa, VG.Proof.MdStream.X86_64.ea_at,
    State.store64, o0, o1, o2, o3, o4, o5, ite_true, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine VG.Proof.MdStream.X86_64.Update.inv_zero hd hp rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp (config := {decide := true}) only [RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne,
      RegUpd.gpr_arithFlags, not_false_eq_true, VG.Proof.MdStream.X86_64.and_mask hd.B]

set_option simprocs false in
theorem epilogue_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {s : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s) :
    WP isa (.block (restore P)) s fun s' => gprPreserved s₀ s' ∧ (VG.Proof.MdStream.X86_64.updK H).post s₀ s' := by
  have := hd.so
  have i : ∀ d : Nat, d + 8 ≤ P.so + 48 →
      InRegions (s.rd ++ s.wr) (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨VG.Proof.MdStream.X86_64.Update.scR P s₀, by simp [hI.rd, hI.wr, hp.wr], VG.Proof.MdStream.X86_64.contains_offset' hd (by omega)⟩
  have i0 := i P.so (by omega); have i1 := i (P.so + 8) (by omega); have i2 := i (P.so + 16) (by omega)
  have i3 := i (P.so + 24) (by omega); have i4 := i (P.so + 32) (by omega); have i5 := i (P.so + 40) (by omega)
  have g0 : s.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 ((P.so : Nat) : Int)) 64 = s₀.gpr .rbx :=
    hI.saved (.rbx, P.so) (by simp [saved])
  have g1 : s.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) 64 = s₀.gpr .rbp :=
    hI.saved (.rbp, P.so + 8) (by simp [saved])
  have g2 : s.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int)) 64 = s₀.gpr .r12 :=
    hI.saved (.r12, P.so + 16) (by simp [saved])
  have g3 : s.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int)) 64 = s₀.gpr .r13 :=
    hI.saved (.r13, P.so + 24) (by simp [saved])
  have g4 : s.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int)) 64 = s₀.gpr .r14 :=
    hI.saved (.r14, P.so + 32) (by simp [saved])
  have g5 : s.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int)) 64 = s₀.gpr .r15 :=
    hI.saved (.r15, P.so + 40) (by simp [saved])
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 :=
    hI.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, VG.Proof.MdStream.X86_64.Update.ret_stk s₀⟩)
      (by decide)
  have hrsp := hI.rsp
  have hr15 := hI.r15
  have hrepr := hI.repr
  apply WP.of_runBlock
  rw [VG.Proof.MdStream.X86_64.restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, VG.Proof.MdStream.X86_64.ea_at, State.load64,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun iv m hm hc => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · have := hrepr iv m ⟨hm, hc⟩
    rwa [List.take_of_length_le (Nat.le_of_eq (VG.Proof.MdStream.X86_64.Update.D_length _))] at this

end

/-! ## One iteration -/

/-- `k` whole blocks are ready at `rsi` (in `r14`): the buffer, or blocks of
data, and compressing them absorbs the first `c` bytes of data. -/
structure Pending {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c k : Nat) (s : State) : Prop
    extends VG.Proof.MdStream.X86_64.Update.Common P s₀ c s where
  r13 : s.gpr .r13 = 0
  r14 : s.gpr .r14 = BitVec.ofNat 64 k
  k_pos : 0 < k
  mod : (VG.Proof.MdStream.X86_64.Update.cnt s₀ + c) % P.B = 0
  src : (s.gpr .rsi = VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N ∧ k = 1) ∨
    ∃ c₀, s.gpr .rsi = VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 c₀ ∧ c₀ + P.B * k ≤ VG.Proof.MdStream.X86_64.Update.len s₀
  repr : ∀ iv m, VG.Proof.MdStream.X86_64.Update.R₀ H s₀ iv m → ∀ mem', H.stateAt mem' (VG.Proof.MdStream.X86_64.Update.st s₀) =
      H.compressBlocks (H.stateAt s.mem (VG.Proof.MdStream.X86_64.Update.st s₀)) s.mem (s.gpr .rsi) k →
    H.Repr iv mem' (VG.Proof.MdStream.X86_64.Update.st s₀) (m ++ (VG.Proof.MdStream.X86_64.Update.D s₀).take c)

/-- All the data is absorbed. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s ∧ s.gpr .r14 = 0

/-- The loop's postcondition for one iteration from `c` bytes. -/
def Step {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (c : Nat) (s : State) : Prop :=
  (eval .ne s = some false ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s) ∨
    (eval .ne s = some true ∧ ∃ c', c < c' ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀ c' s)

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Common.congr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.X86_64.Update.Common P s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86_64.Update.Common P s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg]; exact h.rbx
  r15 := by rw [hg]; exact h.r15
  rsp := by rw [hg]; exact h.rsp
  rbp := by rw [hg]; exact h.rbp
  r12 := by rw [hg]; exact h.r12
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.congr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s' :=
  { h.toCommon.congr hg hm hrd hwr with
    r13 := by rw [hg]; exact h.r13
    repr := by rw [hm]; exact h.repr }

/-- The blocks fit in the address space. -/
theorem Pending.k_lt (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} {c k : Nat} {s : State} (h : VG.Proof.MdStream.X86_64.Update.Pending H s₀ c k s) :
    P.B * k ≤ 2 ^ 64 ∧ k < 2 ^ 64 := by
  have := hd.B; have := VG.Proof.MdStream.X86_64.Update.len_lt s₀
  have : k ≤ P.B * k := Nat.le_mul_of_pos_left k hd.pos
  rcases h.src with ⟨_, rfl⟩ | ⟨c₀, _, hc₀⟩ <;> omega

theorem Pending.ne_zero (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} {c k : Nat} {s : State} (h : VG.Proof.MdStream.X86_64.Update.Pending H s₀ c k s) :
    BitVec.ofNat 64 k ≠ 0 := fun e => by
  have e := congrArg BitVec.toNat e
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h.k_lt hd).2] at e
  exact absurd e (Nat.pos_iff_ne_zero.mp h.k_pos)

theorem ofNat_and_ne {k : Nat} (h0 : 0 < k) (h : k < 2 ^ 64) :
    (BitVec.ofNat 64 k &&& BitVec.ofNat 64 k == 0) = false := by
  rw [BitVec.and_self, VG.Proof.MdStream.X86_64.ofNat_beq_zero h]; simp; omega

/-- The call of the compression function's requirements. -/
theorem Pending.callOk (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c k : Nat} {s : State}
    (h : VG.Proof.MdStream.X86_64.Update.Pending H s₀ c k s) : VG.Proof.MdStream.X86_64.CallOkN P s (VG.Proof.MdStream.X86_64.Update.st s₀) (VG.Proof.MdStream.X86_64.Update.scr s₀) (s.gpr .rsi) (P.B * k) := by
  have := hd.N; have := hd.so; have := hd.B; have := VG.Proof.MdStream.X86_64.Update.len_lt s₀
  have eN : Region.Sub ⟨VG.Proof.MdStream.X86_64.Update.st s₀, P.N⟩ (VG.Proof.MdStream.X86_64.Update.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.X86_64.Update.scr s₀, P.so⟩ (VG.Proof.MdStream.X86_64.Update.scR P s₀) := Region.sub_prefix (by omega)
  have eSrc : Region.Sub ⟨s.gpr .rsi, P.B * k⟩ (VG.Proof.MdStream.X86_64.Update.stR P s₀) ∨ Region.Sub ⟨s.gpr .rsi, P.B * k⟩ (VG.Proof.MdStream.X86_64.Update.dR s₀) := by
    rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · exact .inl (h' ▸ VG.Proof.MdStream.X86_64.sub_offset (off := P.N) (by omega) (by omega))
    · exact .inr (h' ▸ VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega))
  have hsp := h.rsp
  refine ⟨h.rbx, h.r15, rfl, (hp.st_scr.sub_left eN).sub_right eso, ?_, ?_,
    by rw [hsp]; exact hp.stk_st.sub_right eN, by rw [hsp]; exact hp.stk_scr.sub_right eso, ?_, ?_, ?_⟩
  · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
    · rw [h']; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega)
    · exact (hp.d_st.sub_left (h' ▸ VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega))).sub_right eN
  · rcases eSrc with e | e
    · exact (hp.st_scr.sub_left e).sub_right eso
    · exact (hp.d_scr.sub_left e).sub_right eso
  · rw [hsp]
    rcases eSrc with e | e
    · exact hp.stk_st.sub_right e
    · exact hp.stk_d.sub_right e
  · rw [h.rd, h.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rcases h.src with ⟨h', rfl⟩ | ⟨c₀, h', hc₀⟩
      · exact ⟨VG.Proof.MdStream.X86_64.Update.stR P s₀, by simp, P.N, h', by simp⟩
      · exact ⟨VG.Proof.MdStream.X86_64.Update.dR s₀, by simp, c₀, h', hc₀⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Update.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Update.scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [h.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨VG.Proof.MdStream.X86_64.Update.stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Update.scR P s₀, by simp, 0, by simp, by simp⟩

theorem Pending.compress_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code)
    {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c k : Nat} {s : State} (h : VG.Proof.MdStream.X86_64.Update.Pending H s₀ c k s) :
    WP isa (compressN name code) s fun s' => VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s' ∧ s'.gpr .r14 = BitVec.ofNat 64 k := by
  have := hd.N; have := hd.so; have := hd.B
  have eN : Region.Sub ⟨VG.Proof.MdStream.X86_64.Update.st s₀, P.N⟩ (VG.Proof.MdStream.X86_64.Update.stR P s₀) := Region.sub_prefix (by omega)
  have eso : Region.Sub ⟨VG.Proof.MdStream.X86_64.Update.scr s₀, P.so⟩ (VG.Proof.MdStream.X86_64.Update.scR P s₀) := Region.sub_prefix (by omega)
  have hsp := h.rsp
  obtain ⟨hk, hk'⟩ := h.k_lt hd
  refine VG.Proof.MdStream.X86_64.compressWith_ok H VG.Proof.MdStream.X86_64.setsN_r14 hf (k := k) (by rw [h.r14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk'])
    (h.callOk hd hp) hk (by omega) ?_
  intro s' hrd hwr hcs hf hstate _ _
  have cs : ∀ r, r ∈ calleeSaved → s'.gpr r = s.gpr r := hcs
  refine ⟨⟨⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [cs _ (by decide)]; exact h.rbx,
    by rw [cs _ (by decide)]; exact h.r15, by rw [cs _ (by decide)]; exact h.rsp,
    by rw [cs _ (by decide)]; exact h.rbp, by rw [cs _ (by decide)]; exact h.r12,
    h.frame.trans (hf.sub ?_), fun p hp' => ?_⟩, ?_, fun iv m hm => h.repr iv m hm _ hstate⟩,
    by rw [cs _ (by decide)]; exact h.r14⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨VG.Proof.MdStream.X86_64.Update.stR P s₀, by simp, eN⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Update.scR P s₀, by simp, eso⟩
    · exact ⟨VG.Proof.MdStream.X86_64.Update.stkR s₀, by simp, by rw [hsp]; exact fun _ h => h⟩
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd' : ∀ d : Nat, P.so ≤ d → d + 8 ≤ P.so + 48 →
        s'.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 (d : Int)) 64 =
          s.mem.readW (VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 (d : Int)) 64 := by
      intro d hd₁ hd₂
      refine hf.readW (r := ⟨VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 (d : Int), 8⟩) (Region.contains_self _ _) ?_
        (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl
      · exact (hp.st_scr.symm.sub_left (by rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega))).sub_right eN
      · rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact Offset.disjoint_base _ (by omega) (by omega)
      · rw [hsp]
        exact hp.stk_scr.symm.sub_left (by rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega))
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rw [hd' _ (by omega) (by omega)]; exact h.saved _ (by simp [saved])
  · rw [cs _ (by decide), h.r13, h.mod]; rfl

theorem Pending.congr {s₀ : State} {c k : Nat} {s s' : State} (h : VG.Proof.MdStream.X86_64.Update.Pending H s₀ c k s) (hg : s'.gpr = s.gpr)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86_64.Update.Pending H s₀ c k s' :=
  { h.toCommon.congr hg hm hrd hwr with
    r13 := by rw [hg]; exact h.r13
    r14 := by rw [hg]; exact h.r14
    k_pos := h.k_pos
    mod := h.mod
    src := by rw [hg]; exact h.src
    repr := by rw [hm, hg]; exact h.repr }

/-- The second half of the loop body: compress if blocks are ready, and loop
back if so. -/
theorem tail_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {s : State} (h : (∃ c' k, c < c' ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀ c' k s) ∨ VG.Proof.MdStream.X86_64.Update.Done H s₀ s) :
    WP isa (updateTail name code) s (VG.Proof.MdStream.X86_64.Update.Step H s₀ c) := by
  unfold updateTail
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86_64.test_ok .r14) fun s₁ ⟨hg, hm, hrd, hwr, hz⟩ => ?_)
  rcases h with ⟨c', k, hc, hP⟩ | ⟨hI, h14⟩
  · have hP₁ := hP.congr hg hm hrd hwr
    have nz := hP.ne_zero hd
    refine WP.seq (WP.ite true (by simp [eval, hz, hP.r14]; exact nz) (fun _ => ?_) (fun h => by cases h))
    refine WP.mono (hP₁.compress_ok hd hf hp) fun s₂ ⟨hI₂, h14⟩ => ?_
    refine WP.mono (VG.Proof.MdStream.X86_64.test_ok .r14) fun s₃ ⟨hg₃, hm₃, hrd₃, hwr₃, hz₃⟩ => ?_
    exact .inr ⟨by simp [eval, hz₃, h14]; exact nz, c', hc, hI₂.congr hg₃ hm₃ hrd₃ hwr₃⟩
  · refine WP.seq (WP.ite false (by simp [eval, hz, h14]) (fun h => by cases h) fun _ => ?_)
    refine WP.block_nil ?_
    refine WP.mono (VG.Proof.MdStream.X86_64.test_ok .r14) fun s₃ ⟨hg₃, hm₃, hrd₃, hwr₃, hz₃⟩ => ?_
    exact .inl ⟨by simp [eval, hz₃, hg, h14], (hI.congr hg hm hrd hwr).congr hg₃ hm₃ hrd₃ hwr₃⟩

/-! ## Consuming data -/

theorem D_getD (s₀ : State) {i : Nat} (hi : i < VG.Proof.MdStream.X86_64.Update.len s₀) :
    (VG.Proof.MdStream.X86_64.Update.D s₀).getD i 0 = s₀.mem (VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {s : State} (h : VG.Proof.MdStream.X86_64.Update.Common P s₀ c s) {i : Nat}
    (hi : i < VG.Proof.MdStream.X86_64.Update.len s₀) : s.mem (VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 i) = (VG.Proof.MdStream.X86_64.Update.D s₀).getD i 0 := by
  rw [VG.Proof.MdStream.X86_64.Update.D_getD s₀ hi]
  exact h.frame.bytes (R := VG.Proof.MdStream.X86_64.Update.dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩) (Nat.le_of_lt (VG.Proof.MdStream.X86_64.Update.len_lt s₀)) hi

theorem length_mid (hd : VG.Proof.MdStream.X86_64.Dims P) (s₀ : State) {iv : H.HV} {m : List Byte} (hm : VG.Proof.MdStream.X86_64.Update.R₀ H s₀ iv m) {c : Nat}
    (hc : c ≤ VG.Proof.MdStream.X86_64.Update.len s₀) : (m ++ (VG.Proof.MdStream.X86_64.Update.D s₀).take c).length % P.B = (VG.Proof.MdStream.X86_64.Update.cnt s₀ + c) % P.B := by
  simp only [List.length_append, List.length_take, VG.Proof.MdStream.X86_64.Update.D_length, Nat.min_eq_left hc]
  rw [Nat.add_mod, ← hm.length hd, ← Nat.add_mod]

theorem take_add_data (s₀ : State) (c t : Nat) (m : List Byte) :
    m ++ (VG.Proof.MdStream.X86_64.Update.D s₀).take c ++ ((VG.Proof.MdStream.X86_64.Update.D s₀).drop c).take t = m ++ (VG.Proof.MdStream.X86_64.Update.D s₀).take (c + t) := by
  rw [List.take_add, List.append_assoc]

/-- A list whose length is a multiple of `B` has nothing past its last block. -/
theorem drop_full {B : Nat} {l : List Byte} (h : l.length % B = 0) : l.drop (B * (l.length / B)) = [] := by
  rw [List.drop_eq_nil_iff]
  have := Nat.div_add_mod l.length B
  omega

theorem shr_ofNat (hd : VG.Proof.MdStream.X86_64.Dims P) {q : Nat} (h : P.B * q < 2 ^ 64) :
    BitVec.ofNat 64 (P.B * q) >>> Nat.log2 P.B = BitVec.ofNat 64 q := by
  obtain ⟨-, -, lgB⟩ := hd.lg
  have : q ≤ P.B * q := Nat.le_mul_of_pos_left q hd.pos
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, lgB, Nat.mul_div_cancel_left _ hd.pos]

/-- Every whole block left, straight from the data. -/
theorem direct_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s)
    (hr : (VG.Proof.MdStream.X86_64.Update.cnt s₀ + c) % P.B = 0) (hl : P.B ≤ VG.Proof.MdStream.X86_64.Update.len s₀ - c) :
    WP isa (.block (direct P)) s fun s' =>
      VG.Proof.MdStream.X86_64.Update.Pending H s₀ (c + P.B * ((VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B)) ((VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B) s' ∧
        s'.gpr .rsi = VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 c := by
  have hrbp := hI.rbp; have hr12 := hI.r12; have hr13 := hI.r13
  have := hd.B; have hlen := VG.Proof.MdStream.X86_64.Update.len_lt s₀; have hc := hI.c_le
  obtain ⟨lg₁, lg₂, -⟩ := hd.lg
  have hdm := Nat.div_add_mod (VG.Proof.MdStream.X86_64.Update.len s₀ - c) P.B
  have hq : 0 < (VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B := Nat.div_pos hl hd.pos
  have hm := Nat.mod_lt (VG.Proof.MdStream.X86_64.Update.len s₀ - c) hd.pos
  have hmod : (VG.Proof.MdStream.X86_64.Update.cnt s₀ + (c + P.B * ((VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B))) % P.B = 0 := by
    rw [← Nat.add_assoc, Nat.add_mul_mod_self_left]; exact hr
  have hsh := VG.Proof.MdStream.X86_64.Update.shr_ofNat hd (q := (VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B) (by omega)
  unfold direct
  refine VG.Proof.MdStream.X86_64.wp_mov fun s₁ u₁ _ _ => VG.Proof.MdStream.X86_64.wp_mov fun s₂ u₂ _ _ => VG.Proof.MdStream.X86_64.wp_andi fun s₃ u₃ => VG.Proof.MdStream.X86_64.wp_mov fun s₄ u₄ _ _ =>
    VG.Proof.MdStream.X86_64.wp_sub fun s₅ u₅ _ => VG.Proof.MdStream.X86_64.wp_add fun s₆ u₆ => VG.Proof.MdStream.X86_64.wp_mov fun s₇ u₇ _ _ => VG.Proof.MdStream.X86_64.wp_shr ⟨lg₁, lg₂⟩ fun s₈ u₈ =>
    WP.block_nil ?_
  have hrax : s₃.gpr .rax = BitVec.ofNat 64 ((VG.Proof.MdStream.X86_64.Update.len s₀ - c) % P.B) := by
    rw [u₃.gpr, u₂.gpr, u₁.other _ (by decide), hr12, VG.Proof.MdStream.X86_64.and_mask hd.B, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := VG.Proof.MdStream.X86_64.Update.len s₀ - c) (b := 2 ^ 64) (by omega)]
  have h14 : s₅.gpr .r14 = BitVec.ofNat 64 (P.B * ((VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B)) := by
    rw [u₅.gpr, u₄.gpr, u₄.other _ (by decide), hrax, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hr12, VG.Proof.MdStream.X86_64.sub_ofNat (Nat.mod_le _ _)]
    exact congrArg _ (by omega)
  generalize (VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B = q at *
  have g : ∀ r, r ≠ .rsi → r ≠ .rax → r ≠ .r14 → r ≠ .rbp → r ≠ .r12 → s₈.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₈.other r h3, u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h3, u₃.other r h2,
        u₂.other r h2, u₁.other r h1]
  have m₈ : s₈.mem = s.mem := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hsi : s₈.gpr .rsi = VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 c := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hrbp]
  refine ⟨⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₈]; exact hI.frame, by rw [m₈]; exact hI.saved⟩,
    ?_, ?_, hq, hmod, .inr ⟨c, hsi, by omega⟩, ?_⟩, hsi⟩
  · rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  · rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rbx
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.r15
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hI.rsp
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), h14,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hrbp,
      BitVec.add_assoc, ← BitVec.ofNat_add]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), hrax]
    exact congrArg _ (by omega)
  · rw [g .r13 (by decide) (by decide) (by decide) (by decide) (by decide), hr13, hr]; rfl
  · rw [u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), h14, hsh]
  · intro iv m hm mem' hs
    have hmod' := VG.Proof.MdStream.X86_64.Update.length_mid hd s₀ hm (c := c) (by omega)
    rw [← VG.Proof.MdStream.X86_64.Update.take_add_data]
    refine H.repr_append_blocks (n := q) hd.pos (hI.repr iv m hm) (by rw [hmod', hr])
      (by rw [List.length_take, List.length_drop, VG.Proof.MdStream.X86_64.Update.D_length]; omega) ?_
    rw [hs, hsi, m₈]
    apply H.compressBlocks_eq
    intro j hj
    rw [VG.Proof.MdStream.X86_64.add_ofNat, hI.data hp (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hj]

/-! ## Buffering data -/

section
variable (P) (s₀ : State) (c : Nat)
/-- Bytes in the buffer before this iteration. -/
abbrev rr : Nat := (VG.Proof.MdStream.X86_64.Update.cnt s₀ + c) % P.B
/-- Bytes copied into the buffer in this iteration. -/
abbrev tt : Nat := min (P.B - VG.Proof.MdStream.X86_64.Update.rr P s₀ c) (VG.Proof.MdStream.X86_64.Update.len s₀ - c)
/-- Where they go. -/
abbrev q : Addr := VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N + BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.rr P s₀ c)
/-- The data copied. -/
abbrev xs : List Byte := ((VG.Proof.MdStream.X86_64.Update.D s₀).drop c).take (VG.Proof.MdStream.X86_64.Update.tt P s₀ c)
end

theorem rr_lt (hd : VG.Proof.MdStream.X86_64.Dims P) (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86_64.Update.rr P s₀ c < P.B := Nat.mod_lt _ hd.pos
theorem rr_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86_64.Update.rr P s₀ c = (VG.Proof.MdStream.X86_64.Update.cnt s₀ + c) % P.B := rfl
theorem tt_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86_64.Update.tt P s₀ c = min (P.B - VG.Proof.MdStream.X86_64.Update.rr P s₀ c) (VG.Proof.MdStream.X86_64.Update.len s₀ - c) := rfl
theorem tt_le (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86_64.Update.tt P s₀ c ≤ VG.Proof.MdStream.X86_64.Update.len s₀ - c := Nat.min_le_right _ _
theorem tt_le' (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86_64.Update.tt P s₀ c ≤ P.B - VG.Proof.MdStream.X86_64.Update.rr P s₀ c := Nat.min_le_left _ _

theorem q_eq (s₀ : State) (c : Nat) : VG.Proof.MdStream.X86_64.Update.q P s₀ c = VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 (P.N + VG.Proof.MdStream.X86_64.Update.rr P s₀ c) := by
  rw [VG.Proof.MdStream.X86_64.Update.q, VG.Proof.MdStream.X86_64.add_ofNat]

/-- The state while copying: `j` bytes copied, into memory `M` otherwise as in `mI`. -/
structure Copy (P : Params) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (s : State) : Prop where
  j_le : j ≤ VG.Proof.MdStream.X86_64.Update.tt P s₀ c
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = VG.Proof.MdStream.X86_64.Update.st s₀
  r15 : s.gpr .r15 = VG.Proof.MdStream.X86_64.Update.scr s₀
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbp : s.gpr .rbp = VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 (c + j)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.len s₀ - c - VG.Proof.MdStream.X86_64.Update.tt P s₀ c)
  r13 : s.gpr .r13 = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.rr P s₀ c + j)
  rax : s.gpr .rax = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.tt P s₀ c - j)
  mem : s.mem = VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.X86_64.Update.q P s₀ c) ((VG.Proof.MdStream.X86_64.Update.xs P s₀ c).take j)

theorem xs_length (s₀ : State) (c : Nat) : (VG.Proof.MdStream.X86_64.Update.xs P s₀ c).length = VG.Proof.MdStream.X86_64.Update.tt P s₀ c := by
  have := VG.Proof.MdStream.X86_64.Update.tt_le (P := P) s₀ c
  simp only [VG.Proof.MdStream.X86_64.Update.xs, List.length_take, List.length_drop, VG.Proof.MdStream.X86_64.Update.D_length]; omega

theorem write_frame (hd : VG.Proof.MdStream.X86_64.Dims P) (s₀ : State) (c : Nat) (mI : Mem) (j : Nat) (hj : j ≤ VG.Proof.MdStream.X86_64.Update.tt P s₀ c) :
    Frame [VG.Proof.MdStream.X86_64.Update.stR P s₀] mI (VG.WriteBytes.writeBytes mI (VG.Proof.MdStream.X86_64.Update.q P s₀ c) ((VG.Proof.MdStream.X86_64.Update.xs P s₀ c).take j)) := by
  have := VG.Proof.MdStream.X86_64.Update.tt_le' (P := P) s₀ c; have := VG.Proof.MdStream.X86_64.Update.rr_lt hd s₀ c; have := hd.N; have := hd.B
  refine VG.WriteBytes.writeBytes_frame _ _ _ ?_
  rw [VG.Proof.MdStream.X86_64.Update.q_eq]
  exact VG.Proof.MdStream.X86_64.contains_offset (by simp only [List.length_take]; omega) (by omega)

set_option simprocs false in
theorem copy_step (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c sI)
    {j : Nat} (hj : j < VG.Proof.MdStream.X86_64.Update.tt P s₀ c) {s : State} (h : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c sI.mem j s) :
    WP isa (.block [.movzx8 .r9 { base := .rbp }, .store8 (bufByte P) .r9, .alu .add .rbp (.imm 1),
      .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) s fun s' =>
      VG.Proof.MdStream.X86_64.Update.Copy P s₀ c sI.mem (j + 1) s' ∧ s'.zf = some (decide (VG.Proof.MdStream.X86_64.Update.tt P s₀ c - (j + 1) = 0)) := by
  have hlen := VG.Proof.MdStream.X86_64.Update.len_lt s₀
  have hc := hI.c_le
  have hr := VG.Proof.MdStream.X86_64.Update.rr_lt hd s₀ c
  have ht := VG.Proof.MdStream.X86_64.Update.tt_le (P := P) s₀ c; have ht' := VG.Proof.MdStream.X86_64.Update.tt_le' (P := P) s₀ c
  have := hd.N; have := hd.B
  -- The byte read.
  have hin : InRegions (s.rd ++ s.wr) (VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) 1 :=
    ⟨VG.Proof.MdStream.X86_64.Update.dR s₀, by simp [h.rd, hp.rd], VG.Proof.MdStream.X86_64.contains_offset (by omega) (by omega)⟩
  have hbyte : s.mem (VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) = (VG.Proof.MdStream.X86_64.Update.D s₀).getD (c + j) 0 := by
    rw [h.mem, ← hI.data hp (by omega)]
    exact (VG.Proof.MdStream.X86_64.Update.write_frame hd s₀ c sI.mem j h.j_le).bytes (R := VG.Proof.MdStream.X86_64.Update.dR s₀) (by simpa using hp.d_st)
      (by show VG.Proof.MdStream.X86_64.Update.len s₀ ≤ 2 ^ 64; omega) (by show c + j < VG.Proof.MdStream.X86_64.Update.len s₀; omega)
  -- The byte written.
  have hout : InRegions s.wr (VG.Proof.MdStream.X86_64.Update.q P s₀ c + BitVec.ofNat 64 j) 1 :=
    ⟨VG.Proof.MdStream.X86_64.Update.stR P s₀, by simp [h.wr, hp.wr], by
      rw [VG.Proof.MdStream.X86_64.Update.q_eq, VG.Proof.MdStream.X86_64.add_ofNat]; exact VG.Proof.MdStream.X86_64.contains_offset (by omega) (by omega)⟩
  have hrbp := h.rbp; have hr13 := h.r13; have hrbx := h.rbx
  have hxs := VG.Proof.MdStream.X86_64.Update.xs_length (P := P) s₀ c
  refine VG.Proof.MdStream.X86_64.wp_movzx8 (d := .r9) (a := VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 (c + j)) (by simp [State.ea, hrbp]) hin
    fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.X86_64.wp_store8 (r := .r9) (a := VG.Proof.MdStream.X86_64.Update.q P s₀ c + BitVec.ofNat 64 j) ?_ (by rw [u₁.wr]; exact hout)
    fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  · simp only [State.ea, bufByte, u₁.other .rbx (by decide), u₁.other .r13 (by decide), hrbx, hr13, VG.Proof.MdStream.X86_64.Update.q,
      BitVec.ofNat_add, BitVec.mul_one, VG.Proof.MdStream.X86_64.ofInt_natCast]
    ac_rfl
  refine VG.Proof.MdStream.X86_64.wp_addi fun s₃ u₃ => VG.Proof.MdStream.X86_64.wp_addi fun s₄ u₄ => VG.Proof.MdStream.X86_64.wp_subi fun s₅ u₅ hz₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rax → r ≠ .r13 → r ≠ .rbp → r ≠ .r9 → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h1, u₄.other r h2, u₃.other r h3, g₂, u₁.other r h4]
  have hrax : s₅.gpr .rax = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.tt P s₀ c - (j + 1)) := by
    rw [u₅.gpr, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax,
      VG.Proof.MdStream.X86_64.sx1, VG.Proof.MdStream.X86_64.ofNat_pred (by omega), Nat.sub_sub]
  refine ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrax, ?_⟩, ?_⟩
  · rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, h.rd]
  · rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, h.wr]
  · rw [g .rbx (by decide) (by decide) (by decide) (by decide), hrbx]
  · rw [g .r15 (by decide) (by decide) (by decide) (by decide), h.r15]
  · rw [g .rsp (by decide) (by decide) (by decide) (by decide), h.rsp]
  · rw [u₅.other .rbp (by decide), u₄.other .rbp (by decide), u₃.gpr, g₂, u₁.other .rbp (by decide), hrbp,
      VG.Proof.MdStream.X86_64.sx1, ← Nat.add_assoc, VG.Proof.MdStream.X86_64.ofNat_succ, BitVec.add_assoc]
  · rw [g .r12 (by decide) (by decide) (by decide) (by decide), h.r12]
  · rw [u₅.other .r13 (by decide), u₄.gpr, u₃.other .r13 (by decide), g₂, u₁.other .r13 (by decide), hr13,
      VG.Proof.MdStream.X86_64.sx1, ← Nat.add_assoc, VG.Proof.MdStream.X86_64.ofNat_succ]
  · have hj' : j < (VG.Proof.MdStream.X86_64.Update.xs P s₀ c).length := by omega
    rw [u₅.mem, u₄.mem, u₃.mem, m₂, u₁.mem, u₁.gpr, hbyte, h.mem, List.take_add_one,
      List.getElem?_eq_getElem hj', Option.toList_some,
      VG.WriteBytes.writeBytes_snoc _ _ _ _ (by simp only [List.length_take]; omega)]
    have hl : (List.take j (VG.Proof.MdStream.X86_64.Update.xs P s₀ c)).length = j := by rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj')]
    rw [hl, BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]
    congr 1
    simp only [VG.Proof.MdStream.X86_64.Update.xs, List.getElem_take, List.getElem_drop, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show c + j < (VG.Proof.MdStream.X86_64.Update.D s₀).length by rw [VG.Proof.MdStream.X86_64.Update.D_length]; omega), Option.getD_some]
  · rw [hz₅, u₄.other .rax (by decide), u₃.other .rax (by decide), g₂, u₁.other .rax (by decide), h.rax, VG.Proof.MdStream.X86_64.sx1,
      VG.Proof.MdStream.X86_64.ofNat_pred (by omega), VG.Proof.MdStream.X86_64.ofNat_beq_zero (by omega), show VG.Proof.MdStream.X86_64.Update.tt P s₀ c - j - 1 = VG.Proof.MdStream.X86_64.Update.tt P s₀ c - (j + 1) by omega]

theorem Inv.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved
  r13 := by rw [hg _ (by simp)]; exact h.r13
  repr := by rw [hm]; exact h.repr

/-- The memory after copying `tt` bytes. -/
theorem copied_facts (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c sI) :
    let mem := VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.X86_64.Update.q P s₀ c) (VG.Proof.MdStream.X86_64.Update.xs P s₀ c)
    Frame [VG.Proof.MdStream.X86_64.Update.stR P s₀, VG.Proof.MdStream.X86_64.Update.scR P s₀, VG.Proof.MdStream.X86_64.Update.stkR s₀] s₀.mem mem ∧ VG.Proof.MdStream.X86_64.Saved P s₀ .r8 mem ∧
      H.stateAt mem (VG.Proof.MdStream.X86_64.Update.st s₀) = H.stateAt sI.mem (VG.Proof.MdStream.X86_64.Update.st s₀) ∧
      bytesAt mem (VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N) (VG.Proof.MdStream.X86_64.Update.rr P s₀ c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c) =
        bytesAt sI.mem (VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N) (VG.Proof.MdStream.X86_64.Update.rr P s₀ c) ++ VG.Proof.MdStream.X86_64.Update.xs P s₀ c := by
  intro mem
  have hr := VG.Proof.MdStream.X86_64.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.X86_64.Update.tt_le' (P := P) s₀ c
  have hxs := VG.Proof.MdStream.X86_64.Update.xs_length (P := P) s₀ c
  have := hd.N; have := hd.B; have := hd.so
  have hf : Frame [VG.Proof.MdStream.X86_64.Update.stR P s₀] sI.mem mem := by
    have := VG.Proof.MdStream.X86_64.Update.write_frame hd s₀ c sI.mem (VG.Proof.MdStream.X86_64.Update.tt P s₀ c) (Nat.le_refl _)
    rwa [List.take_of_length_le (by omega)] at this
  refine ⟨hI.frame.trans (hf.mono (by simp)), fun p hp' => ?_, ?_, ?_⟩
  · rw [← hI.saved p hp']
    simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    have hd' : P.so ≤ p.2 ∧ p.2 + 8 ≤ P.so + 48 := by
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega
    refine hf.readW (r := ⟨VG.Proof.MdStream.X86_64.Update.scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact (hp.st_scr.symm.sub_left (by rw [VG.Proof.MdStream.X86_64.ofInt_natCast]; exact VG.Proof.MdStream.X86_64.sub_offset (by omega) (by omega)))
  · apply H.stateAt_congr
    intro i hi
    simp only [mem, VG.Proof.MdStream.X86_64.Update.q_eq]
    exact VG.WriteBytes.writeBytes_before _ _ _ (by omega) (by omega)
  · rw [← hxs]
    exact bytesAt_writeBytes _ _ _ _ (by omega)

set_option simprocs false in
/-- A full buffer: compress it. -/
theorem fill_pending (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.X86_64.Update.tt P s₀ c) s) (hfull : VG.Proof.MdStream.X86_64.Update.rr P s₀ c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c = P.B) :
    WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 P.N)), .mov32 .r13 (.imm 0),
      .mov32 .r14 (.imm 1)]) s fun s' =>
      VG.Proof.MdStream.X86_64.Update.Pending H s₀ (c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c) 1 s' ∧ s'.gpr .rsi = VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N := by
  have ht := VG.Proof.MdStream.X86_64.Update.tt_le (P := P) s₀ c; have ht' := VG.Proof.MdStream.X86_64.Update.tt_le' (P := P) s₀ c
  have hrr := VG.Proof.MdStream.X86_64.Update.rr_eq (P := P) s₀ c
  have hxs := VG.Proof.MdStream.X86_64.Update.xs_length (P := P) s₀ c
  have hc := hI.c_le
  have := hd.N
  obtain ⟨hfr, hsv, hst, hby⟩ := VG.Proof.MdStream.X86_64.Update.copied_facts hd hp hI
  have hmem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.X86_64.Update.q P s₀ c) (VG.Proof.MdStream.X86_64.Update.xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine VG.Proof.MdStream.X86_64.wp_mov fun s₁ u₁ _ _ => VG.Proof.MdStream.X86_64.wp_addi fun s₂ u₂ => VG.Proof.MdStream.X86_64.wp_mov32i fun s₃ u₃ _ _ =>
    VG.Proof.MdStream.X86_64.wp_mov32i fun s₄ u₄ _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rsi → r ≠ .r13 → r ≠ .r14 → s₄.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₄.other r h3, u₃.other r h2, u₂.other r h1, u₁.other r h1]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have hsi : s₄.gpr .rsi = VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, h.rbx, VG.Proof.MdStream.X86_64.sx_ofNat (by omega)]
  refine ⟨⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [m₄, hmem]; exact hfr, by rw [m₄, hmem]; exact hsv⟩,
    by rw [u₄.other _ (by decide), u₃.gpr]; rfl, by rw [u₄.gpr]; rfl, Nat.one_pos, ?_, .inl ⟨hsi, rfl⟩, ?_⟩,
    hsi⟩
  · rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd]
  · rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr]
  · rw [g .rbx (by decide) (by decide) (by decide), h.rbx]
  · rw [g .r15 (by decide) (by decide) (by decide), h.r15]
  · rw [g .rsp (by decide) (by decide) (by decide), h.rsp]
  · rw [g .rbp (by decide) (by decide) (by decide), h.rbp]
  · rw [g .r12 (by decide) (by decide) (by decide), h.r12, Nat.sub_sub]
  · rw [← Nat.add_assoc, add_mod_of_eq (B := P.B) hfull]
  · intro iv m hm mem' hs
    rw [Md.compressBlocks_one] at hs
    rw [← VG.Proof.MdStream.X86_64.Update.take_add_data]
    have hmod := VG.Proof.MdStream.X86_64.Update.length_mid hd s₀ hm hc
    refine H.repr_append_block hd.pos (hI.repr iv m hm) (by rw [hmod, hxs]; exact hfull) ?_
    rw [hs, m₄, hmem, hst, hsi]
    refine congrArg (H.compress _) (H.parse_congr fun k hk => ?_)
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb, show VG.Proof.MdStream.X86_64.Update.rr P s₀ c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c = P.B from hfull] at hby
    exact VG.Proof.MdStream.X86_64.bytesAt_getD hby hk

set_option simprocs false in
/-- All the data fits in the buffer. -/
theorem fill_done (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.X86_64.Update.tt P s₀ c) s) (h14 : s.gpr .r14 = 0)
    (hnf : VG.Proof.MdStream.X86_64.Update.rr P s₀ c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c ≠ P.B) : VG.Proof.MdStream.X86_64.Update.Done H s₀ s := by
  have hr := VG.Proof.MdStream.X86_64.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.X86_64.Update.tt_le' (P := P) s₀ c
  have hrr := VG.Proof.MdStream.X86_64.Update.rr_eq (P := P) s₀ c
  have htt := VG.Proof.MdStream.X86_64.Update.tt_eq (P := P) s₀ c
  have hxs := VG.Proof.MdStream.X86_64.Update.xs_length (P := P) s₀ c
  have hc := hI.c_le
  have htl : VG.Proof.MdStream.X86_64.Update.tt P s₀ c = VG.Proof.MdStream.X86_64.Update.len s₀ - c := by omega
  obtain ⟨hfr, hsv, hst, hby⟩ := VG.Proof.MdStream.X86_64.Update.copied_facts hd hp hI
  have hmem : s.mem = VG.WriteBytes.writeBytes sI.mem (VG.Proof.MdStream.X86_64.Update.q P s₀ c) (VG.Proof.MdStream.X86_64.Update.xs P s₀ c) := by
    rw [h.mem, List.take_of_length_le (by omega)]
  refine ⟨⟨⟨(Nat.le_refl _), h.rd, h.wr, h.rbx, h.r15, h.rsp, ?_, ?_, by rw [hmem]; exact hfr,
    by rw [hmem]; exact hsv⟩, ?_, fun iv m hm => ?_⟩, h14⟩
  · rw [h.rbp, show c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c = VG.Proof.MdStream.X86_64.Update.len s₀ by omega]
  · rw [h.r12, show VG.Proof.MdStream.X86_64.Update.len s₀ - c - VG.Proof.MdStream.X86_64.Update.tt P s₀ c = VG.Proof.MdStream.X86_64.Update.len s₀ - VG.Proof.MdStream.X86_64.Update.len s₀ by omega]
  · rw [h.r13, show VG.Proof.MdStream.X86_64.Update.cnt s₀ + VG.Proof.MdStream.X86_64.Update.len s₀ = VG.Proof.MdStream.X86_64.Update.cnt s₀ + c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c by omega,
      add_mod_of_lt (B := P.B) (by omega)]
  · have hmod := VG.Proof.MdStream.X86_64.Update.length_mid hd s₀ hm hc
    rw [show VG.Proof.MdStream.X86_64.Update.len s₀ = c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c by omega, ← VG.Proof.MdStream.X86_64.Update.take_add_data]
    refine H.repr_append_buf (hI.repr iv m hm) (by rw [hmod, hxs]; omega) (by rw [hmem, hst]) ?_
    rw [hmod, hxs, hmem, hby]
    have hb := (hI.repr iv m hm).2
    rw [hmod] at hb
    rw [hb]

theorem Copy.of_gpr {s₀ : State} {c : Nat} {mI : Mem} {j : Nat} {s s' : State} (h : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c mI j s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13, .rax], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c mI j s' where
  j_le := h.j_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  rbx := by rw [hg _ (by simp)]; exact h.rbx
  r15 := by rw [hg _ (by simp)]; exact h.r15
  rsp := by rw [hg _ (by simp)]; exact h.rsp
  rbp := by rw [hg _ (by simp)]; exact h.rbp
  r12 := by rw [hg _ (by simp)]; exact h.r12
  r13 := by rw [hg _ (by simp)]; exact h.r13
  rax := by rw [hg _ (by simp)]; exact h.rax
  mem := by rw [hm]; exact h.mem

theorem copy_loop_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {sI : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c sI)
    {s : State} (h : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c sI.mem 0 s) (ht : 0 < VG.Proof.MdStream.X86_64.Update.tt P s₀ c) :
    WP isa (copyLoop P) s (VG.Proof.MdStream.X86_64.Update.Copy P s₀ c sI.mem (VG.Proof.MdStream.X86_64.Update.tt P s₀ c)) := by
  refine WP.loop (M := isa) (fun n s => ∃ j, n = VG.Proof.MdStream.X86_64.Update.tt P s₀ c - j ∧ j < VG.Proof.MdStream.X86_64.Update.tt P s₀ c ∧ VG.Proof.MdStream.X86_64.Update.Copy P s₀ c sI.mem j s)
    ?_ (VG.Proof.MdStream.X86_64.Update.tt P s₀ c) s ⟨0, rfl, ht, h⟩
  rintro n s ⟨j, rfl, hj, hc⟩
  refine WP.mono (VG.Proof.MdStream.X86_64.Update.copy_step hd hp hI hj hc) fun s' ⟨hc', hz⟩ => ?_
  by_cases hl : VG.Proof.MdStream.X86_64.Update.tt P s₀ c - (j + 1) = 0
  · refine .inl ⟨by simp [eval, hz, hl], ?_⟩
    rwa [show j + 1 = VG.Proof.MdStream.X86_64.Update.tt P s₀ c by omega] at hc'
  · exact .inr ⟨by simp [eval, hz, hl], _, by omega, j + 1, rfl, by omega, hc'⟩

theorem fill_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s) :
    WP isa (fill P) s fun s' =>
      (∃ c', c < c' ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀ c' 1 s' ∧ s'.gpr .rsi = VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N) ∨ VG.Proof.MdStream.X86_64.Update.Done H s₀ s' := by
  have hr := VG.Proof.MdStream.X86_64.Update.rr_lt hd s₀ c; have ht' := VG.Proof.MdStream.X86_64.Update.tt_le' (P := P) s₀ c
  have htt := VG.Proof.MdStream.X86_64.Update.tt_eq (P := P) s₀ c
  have hlen := VG.Proof.MdStream.X86_64.Update.len_lt s₀
  have := hd.B
  unfold fill
  -- `rax := B - r13; cmp r12, rax`
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_mov32i fun s₁ u₁ _ _ => VG.Proof.MdStream.X86_64.wp_sub fun s₂ u₂ _ => VG.Proof.MdStream.X86_64.wp_cmp fun s₃ g₃ m₃ rd₃ wr₃ cf₃ _ =>
    WP.block_nil ?_)
  have e₃ : ∀ r, r ≠ .rax → s₃.gpr r = s.gpr r := fun r h => by rw [g₃, u₂.other r h, u₁.other r h]
  have hne : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13], r ≠ .rax := by decide
  have hI₃ : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s₃ := hI.of_gpr (fun r hr => e₃ r (hne r hr)) (by rw [m₃, u₂.mem, u₁.mem])
    (by rw [rd₃, u₂.rd, u₁.rd]) (by rw [wr₃, u₂.wr, u₁.wr])
  have hrax₂ : s₂.gpr .rax = BitVec.ofNat 64 (P.B - VG.Proof.MdStream.X86_64.Update.rr P s₀ c) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hI.r13, ← VG.Proof.MdStream.X86_64.Update.rr_eq, VG.Proof.MdStream.X86_64.zx_ofNat (by omega), VG.Proof.MdStream.X86_64.sub_ofNat (by omega)]
  have hcf : s₃.cf = some (decide (VG.Proof.MdStream.X86_64.Update.len s₀ - c < P.B - VG.Proof.MdStream.X86_64.Update.rr P s₀ c)) := by
    rw [cf₃, hrax₂, u₂.other _ (by decide), u₁.other _ (by decide), hI.r12, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  -- `rax := min(rax, r12)`
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s₄ ∧ s₄.gpr .rax = BitVec.ofNat 64 (VG.Proof.MdStream.X86_64.Update.tt P s₀ c) ∧
    s₄.mem = s.mem) ?_ fun s₄ ⟨hI₄, hrax₄, hm₄⟩ => ?_)
  · refine WP.ite (decide (VG.Proof.MdStream.X86_64.Update.len s₀ - c < P.B - VG.Proof.MdStream.X86_64.Update.rr P s₀ c)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
    · refine VG.Proof.MdStream.X86_64.wp_mov fun s₄ u₄ _ _ => WP.block_nil
        ⟨hI₃.of_gpr (fun r hr => u₄.other r (hne r hr)) u₄.mem u₄.rd u₄.wr, ?_,
          by rw [u₄.mem, m₃, u₂.mem, u₁.mem]⟩
      rw [u₄.gpr, hI₃.r12]; congr 1; simp at hb; omega
    · refine WP.block_nil ⟨hI₃, ?_, by rw [m₃, u₂.mem, u₁.mem]⟩
      rw [g₃, hrax₂]; congr 1; simp at hb; omega
  -- `r12 -= rax; test rax, rax`
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_sub fun s₅ u₅ _ => VG.Proof.MdStream.X86_64.wp_test fun s₆ g₆ m₆ rd₆ wr₆ z₆ => WP.block_nil ?_)
  have hC₀ : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c s.mem 0 s₆ := by
    have e : ∀ r, r ≠ .r12 → s₆.gpr r = s₄.gpr r := fun r h => by rw [g₆, u₅.other r h]
    refine ⟨Nat.zero_le _, by rw [rd₆, u₅.rd, hI₄.rd], by rw [wr₆, u₅.wr, hI₄.wr],
      by rw [e _ (by decide), hI₄.rbx], by rw [e _ (by decide), hI₄.r15], by rw [e _ (by decide), hI₄.rsp],
      by rw [e _ (by decide), hI₄.rbp, Nat.add_zero], ?_, by rw [e _ (by decide), hI₄.r13, Nat.add_zero],
      by rw [e _ (by decide), hrax₄, Nat.sub_zero], ?_⟩
    · rw [g₆, u₅.gpr, hI₄.r12, hrax₄, VG.Proof.MdStream.X86_64.sub_ofNat (by omega), Nat.sub_sub]
    · rw [m₆, u₅.mem, hm₄, List.take_zero, VG.WriteBytes.writeBytes_nil]
  have hz₆ : s₆.zf = some (decide (VG.Proof.MdStream.X86_64.Update.tt P s₀ c = 0)) := by
    rw [z₆, u₅.other _ (by decide), hrax₄, BitVec.and_self, VG.Proof.MdStream.X86_64.ofNat_beq_zero (by omega)]
  -- Copy the bytes.
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.X86_64.Update.Copy P s₀ c s.mem (VG.Proof.MdStream.X86_64.Update.tt P s₀ c)) ?_ fun s₇ hC => ?_)
  · refine WP.ite (decide (VG.Proof.MdStream.X86_64.Update.tt P s₀ c = 0)) (by simp [eval, hz₆]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil (hb ▸ hC₀)
    · simp only [decide_eq_false_iff_not] at hb
      rw [← hm₄]
      exact VG.Proof.MdStream.X86_64.Update.copy_loop_ok hd hp hI₄ (by rw [hm₄]; exact hC₀) (by omega)
  -- Is the buffer full?
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_mov32i fun s₈ u₈ _ _ => VG.Proof.MdStream.X86_64.wp_cmpi fun s₉ g₉ m₉ rd₉ wr₉ _ z₉ => WP.block_nil ?_)
  have hne14 : ∀ r ∈ [Reg.rbx, .r15, .rsp, .rbp, .r12, .r13, .rax], r ≠ .r14 := by decide
  have hC₉ : VG.Proof.MdStream.X86_64.Update.Copy P s₀ c s.mem (VG.Proof.MdStream.X86_64.Update.tt P s₀ c) s₉ :=
    hC.of_gpr (fun r hr => by rw [g₉, u₈.other r (hne14 r hr)]) (by rw [m₉, u₈.mem])
      (by rw [rd₉, u₈.rd]) (by rw [wr₉, u₈.wr])
  have hz₉ : s₉.zf = some (decide (VG.Proof.MdStream.X86_64.Update.rr P s₀ c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c = P.B)) := by
    rw [z₉, u₈.other _ (by decide), hC.r13, VG.Proof.MdStream.X86_64.sx_ofNat (by omega), VG.Proof.MdStream.X86_64.sub_beq (by omega) (by omega)]
  have h14 : s₉.gpr .r14 = 0 := by rw [g₉, u₈.gpr]; rfl
  refine WP.ite (decide (VG.Proof.MdStream.X86_64.Update.rr P s₀ c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c = P.B)) (by simp [eval, hz₉]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.mono (VG.Proof.MdStream.X86_64.Update.fill_pending hd hp hI hC₉ hb) fun s' h => .inl ⟨c + VG.Proof.MdStream.X86_64.Update.tt P s₀ c, by omega, h.1, h.2⟩
  · simp only [decide_eq_false_iff_not] at hb
    exact WP.block_nil (.inr (VG.Proof.MdStream.X86_64.Update.fill_done hd hp hI hC₉ h14 hb))

/-- Where the block compressed after absorbing `c` bytes is: in the data if
the buffer is empty and a whole block remains, otherwise in the buffer. -/
def srcOf (P : Params) (s₀ : State) (c : Nat) : Addr :=
  if VG.Proof.MdStream.X86_64.Update.rr P s₀ c = 0 ∧ P.B ≤ VG.Proof.MdStream.X86_64.Update.len s₀ - c then VG.Proof.MdStream.X86_64.Update.dp s₀ + BitVec.ofNat 64 c else VG.Proof.MdStream.X86_64.Update.st s₀ + BitVec.ofNat 64 P.N

/-- The first half of an iteration. -/
theorem head_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {s₀ : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s) :
    WP isa (updateHead P) s fun s' =>
      (∃ c' k, c < c' ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀ c' k s' ∧ s'.gpr .rsi = VG.Proof.MdStream.X86_64.Update.srcOf P s₀ c) ∨ VG.Proof.MdStream.X86_64.Update.Done H s₀ s' := by
  have hlen := VG.Proof.MdStream.X86_64.Update.len_lt s₀; have hr := VG.Proof.MdStream.X86_64.Update.rr_lt hd s₀ c
  have := hd.B
  have hr' : (VG.Proof.MdStream.X86_64.Update.cnt s₀ + c) % P.B < P.B := Nat.mod_lt _ hd.pos
  unfold updateHead
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_test fun s₁ g₁ m₁ rd₁ wr₁ z₁ => WP.block_nil ?_)
  have hI₁ := hI.of_gpr (fun r _ => by rw [g₁]) m₁ rd₁ wr₁
  refine WP.ite (decide (VG.Proof.MdStream.X86_64.Update.rr P s₀ c = 0))
    (by rw [show isa.eval .e s₁ = s₁.zf from rfl, z₁, hI.r13, BitVec.and_self, VG.Proof.MdStream.X86_64.ofNat_beq_zero (by omega)])
    (fun hb => ?_) (fun hb => WP.mono (VG.Proof.MdStream.X86_64.Update.fill_ok hd hp hI₁) fun _ h => h.imp
      (fun ⟨c', hc', hP, hs⟩ => ⟨c', 1, hc', hP, by
        rw [hs, VG.Proof.MdStream.X86_64.Update.srcOf]; exact (ite_eq_right_iff.mpr fun h => absurd h.1 (by simpa using hb)).symm⟩) id)
  simp only [decide_eq_true_eq] at hb
  refine WP.seq (VG.Proof.MdStream.X86_64.wp_cmpi fun s₂ g₂ m₂ rd₂ wr₂ cf₂ _ => WP.block_nil ?_)
  have hI₂ := hI₁.of_gpr (fun r _ => by rw [g₂]) m₂ rd₂ wr₂
  have hcf : s₂.cf = some (decide (VG.Proof.MdStream.X86_64.Update.len s₀ - c < P.B)) := by
    rw [cf₂, hI₁.r12, VG.Proof.MdStream.X86_64.sx_ofNat (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine WP.ite (!decide (VG.Proof.MdStream.X86_64.Update.len s₀ - c < P.B)) (by simp [eval, hcf]) (fun hb' => ?_) (fun hb' =>
    WP.mono (VG.Proof.MdStream.X86_64.Update.fill_ok hd hp hI₂) fun _ h => h.imp
      (fun ⟨c', hc', hP, hs⟩ => ⟨c', 1, hc', hP, by
        rw [hs, VG.Proof.MdStream.X86_64.Update.srcOf]; exact (ite_eq_right_iff.mpr fun h => absurd h.2 (by simp at hb'; omega)).symm⟩) id)
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb'
  have hq : 0 < (VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B := Nat.div_pos hb' hd.pos
  have : (VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B ≤ P.B * ((VG.Proof.MdStream.X86_64.Update.len s₀ - c) / P.B) := Nat.le_mul_of_pos_left _ hd.pos
  exact WP.mono (VG.Proof.MdStream.X86_64.Update.direct_ok hd hp hI₂ hb hb') fun s' h => .inl ⟨_, _, by omega, h.1, by
    rw [h.2, VG.Proof.MdStream.X86_64.Update.srcOf]; exact (ite_eq_left_iff.mpr fun h => absurd ⟨hb, hb'⟩ h).symm⟩

theorem body_ok (hd : VG.Proof.MdStream.X86_64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) {c : Nat} {s : State} (hI : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s) :
    WP isa (updateBody P name code) s (VG.Proof.MdStream.X86_64.Update.Step H s₀ c) :=
  WP.seq (WP.mono (VG.Proof.MdStream.X86_64.Update.head_ok hd hp hI) fun _ h =>
    VG.Proof.MdStream.X86_64.Update.tail_ok hd hf hp (h.imp (fun ⟨c', k, hc, hP, _⟩ => ⟨c', k, hc, hP⟩) id))

theorem correct (hd : VG.Proof.MdStream.X86_64.Dims P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s₀ : State}
    (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) :
    WP isa (update P name code) s₀ fun s' => gprPreserved s₀ s' ∧ (VG.Proof.MdStream.X86_64.updK H).post s₀ s' := by
  unfold update
  refine WP.seq (WP.mono (VG.Proof.MdStream.X86_64.Update.prologue_ok (H := H) hd hp) fun s₁ hI => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀)) ?_ fun s₂ hI₂ => VG.Proof.MdStream.X86_64.Update.epilogue_ok hd hp hI₂)
  refine WP.loop (M := isa) (fun n s => ∃ c, n = VG.Proof.MdStream.X86_64.Update.len s₀ - c ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s) ?_ (VG.Proof.MdStream.X86_64.Update.len s₀) s₁ ⟨0, rfl, hI⟩
  rintro n s ⟨c, rfl, hI⟩
  refine WP.mono (VG.Proof.MdStream.X86_64.Update.body_ok hd hf hp hI) fun s' h => ?_
  rcases h with ⟨he, hI'⟩ | ⟨he, c', hc, hI'⟩
  · exact .inl ⟨he, hI'⟩
  · exact .inr ⟨he, VG.Proof.MdStream.X86_64.Update.len s₀ - c', by have := hI'.c_le; omega, c', rfl, hI'⟩

end

end VG.Proof.MdStream.X86_64.Update

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `update` is constant time

This holds for any compression function (`CalleeOk`), so it is proven once
for every implementation. The taint analysis cannot prove it without
looking into the compression function, which saves and restores our
registers in memory it also writes secrets to. So we relate two runs
(`RelCT`), as for PBKDF2's iteration (`Proof/Pbkdf2/X86_64/IterateCT.lean`):
at the start of every iteration, both runs have absorbed the same number of
bytes, so correctness determines our registers from the public arguments
alone; between the calls, the taint analysis proves each piece constant time
from that (`Taints`, checked for each hash function's code), and shows that
the pieces agree on how many bytes they absorb; and the calls are constant
time by `compressAt_rel`.
-/

namespace VG.Proof.MdStream.X86_64.Update

open VG VG.X86_64 VG.Impl.MdStream.X86_64

/-- The public arguments are the same. -/
structure PubEq (s₀ s₀' : State) : Prop where
  rdi : s₀.gpr .rdi = s₀'.gpr .rdi
  rsi : s₀.gpr .rsi = s₀'.gpr .rsi
  rdx : s₀.gpr .rdx = s₀'.gpr .rdx
  rcx : s₀.gpr .rcx = s₀'.gpr .rcx
  r8 : s₀.gpr .r8 = s₀'.gpr .r8
  rsp : s₀.gpr .rsp = s₀'.gpr .rsp

theorem PubEq.len {s₀ s₀' : State} (hq : VG.Proof.MdStream.X86_64.Update.PubEq s₀ s₀') : VG.Proof.MdStream.X86_64.Update.len s₀ = VG.Proof.MdStream.X86_64.Update.len s₀' :=
  congrArg BitVec.toNat hq.rcx

theorem PubEq.src {P : Params} {s₀ s₀' : State} (hq : VG.Proof.MdStream.X86_64.Update.PubEq s₀ s₀') {c : Nat} :
    VG.Proof.MdStream.X86_64.Update.srcOf P s₀ c = VG.Proof.MdStream.X86_64.Update.srcOf P s₀' c := by
  have e : VG.Proof.MdStream.X86_64.Update.rr P s₀ c = VG.Proof.MdStream.X86_64.Update.rr P s₀' c := congrArg (fun x : BitVec 64 => (x.toNat + c) % P.B) hq.rsi
  simp only [VG.Proof.MdStream.X86_64.Update.srcOf, e, hq.len]
  rw [show VG.Proof.MdStream.X86_64.Update.dp s₀ = VG.Proof.MdStream.X86_64.Update.dp s₀' from hq.rdx, show VG.Proof.MdStream.X86_64.Update.st s₀ = VG.Proof.MdStream.X86_64.Update.st s₀' from hq.rdi]

/-- The registers the pieces between the calls use. -/
abbrev regs : List Reg := [.rbx, .r15, .rsp, .rbp, .r12, .r13]

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem Inv.agree {s₀ s₀' : State} (hq : VG.Proof.MdStream.X86_64.Update.PubEq s₀ s₀') {c : Nat} {s s' : State} (h : VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s)
    (h' : VG.Proof.MdStream.X86_64.Update.Inv H s₀' c s') : ∀ r ∈ VG.Proof.MdStream.X86_64.Update.regs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [VG.Proof.MdStream.X86_64.Update.regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]; exact hq.rdi
  · rw [h.r15, h'.r15]; exact hq.r8
  · rw [h.rsp, h'.rsp]; exact hq.rsp
  · rw [h.rbp, h'.rbp]; exact congrArg (· + _) hq.rdx
  · rw [h.r12, h'.r12, hq.len]
  · rw [h.r13, h'.r13]; exact congrArg (fun x : BitVec 64 => BitVec.ofNat 64 ((x.toNat + c) % P.B)) hq.rsi

end

theorem test_rel {P : State → State → Prop} :
    RelCT isa P (.block [.alu .test .r14 (.reg .r14)]) fun s₁ s₂ => True ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧
      (s₁.gpr = σ₁.gpr ∧ s₁.mem = σ₁.mem ∧ s₁.rd = σ₁.rd ∧ s₁.wr = σ₁.wr ∧
        s₁.zf = some (σ₁.gpr .r14 &&& σ₁.gpr .r14 == 0)) ∧
      (s₂.gpr = σ₂.gpr ∧ s₂.mem = σ₂.mem ∧ s₂.rd = σ₂.rd ∧ s₂.wr = σ₂.wr ∧
        s₂.zf = some (σ₂.gpr .r14 &&& σ₂.gpr .r14 == 0)) :=
  (RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
    (c := .block [.alu .test .r14 (.reg .r14)]) (by taint_decide)).wpDep
    fun _ _ _ => ⟨VG.Proof.MdStream.X86_64.test_ok .r14, VG.Proof.MdStream.X86_64.test_ok .r14⟩

/-- `k` blocks, as a nonzero `r14`. -/
abbrev nz (k : Nat) : Prop := BitVec.ofNat 64 k ≠ 0
theorem zero_and : ((0 : BitVec 64) &&& 0 == 0) = true := by decide

section
variable {P : Params} {H : Md P.B P.N P.L} (hd : VG.Proof.MdStream.X86_64.Dims P) (ht : VG.Proof.MdStream.X86_64.Taints P) {name : String} {code : Prog isa}
  (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) {s₀ s₀' : State} (hp : VG.Proof.MdStream.X86_64.Update.Pre P s₀) (hp' : VG.Proof.MdStream.X86_64.Update.Pre P s₀') (hq : VG.Proof.MdStream.X86_64.Update.PubEq s₀ s₀')

/-- After the first half of an iteration: the same block is ready in both
runs, or all the data is buffered in both. -/
def Mid (H : Md P.B P.N P.L) (s₀ s₀' : State) (c : Nat) (s₁ s₂ : State) : Prop :=
  (∃ c' k, c < c' ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀ c' k s₁ ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀' c' k s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi) ∨
    (VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂)

include hd ht hp hp' hq in
theorem head_rel {c : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' c s₂) (updateHead P) (VG.Proof.MdStream.X86_64.Update.Mid H s₀ s₀' c) := by
  obtain ⟨_, htc⟩ := ht.updHead
  have t := (RelCT.taintRegs (τ := Taint.ofRegs VG.Proof.MdStream.X86_64.Update.regs) (P := fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' c s₂)
    (fun _ _ h => Taint.agree_ofRegs (Inv.agree hq h.1 h.2)) [.r12, .r14] (c := updateHead P)
    htc).wp fun _ _ h => ⟨VG.Proof.MdStream.X86_64.Update.head_ok hd hp h.1, VG.Proof.MdStream.X86_64.Update.head_ok hd hp' h.2⟩
  refine t.mono (fun _ _ h => h) fun s₁ s₂ ⟨ag, h₁, h₂⟩ => ?_
  have e12 := ag .r12 (by simp)
  have e14 := ag .r14 (by simp)
  rcases h₁ with ⟨c₁, k₁, hc₁, P₁, si₁⟩ | D₁ <;> rcases h₂ with ⟨c₂, k₂, hc₂, P₂, si₂⟩ | D₂
  · have e := congrArg BitVec.toNat (P₁.r12.symm.trans (e12.trans P₂.r12))
    have l₁ := P₁.c_le; have l₂ := P₂.c_le; have hl := VG.Proof.MdStream.X86_64.Update.len_lt s₀; have hl' := hq.len
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at e
    obtain rfl : c₁ = c₂ := by omega
    have ek := congrArg BitVec.toNat (P₁.r14.symm.trans (e14.trans P₂.r14))
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₁.k_lt hd).2,
      Nat.mod_eq_of_lt (P₂.k_lt hd).2] at ek
    subst ek
    exact .inl ⟨c₁, k₁, hc₁, P₁, P₂, by rw [si₁, si₂]; exact hq.src⟩
  · have e := congrArg BitVec.toNat (P₁.r14.symm.trans (e14.trans D₂.2))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₁.k_lt hd).2] at e
    exact absurd e (by have := P₁.k_pos; simp; omega)
  · have e := congrArg BitVec.toNat (D₁.2.symm.trans (e14.trans P₂.r14))
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₂.k_lt hd).2] at e
    exact absurd e (by have := P₂.k_pos; simp; omega)
  · exact .inr ⟨D₁, D₂⟩

include hd hf hp hp' hq in
/-- The second half, when blocks are ready. -/
theorem tail_pending {c' k : Nat} :
    RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Pending H s₀ c' k s₁ ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀' c' k s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi)
      (updateTail name code) fun s₁ s₂ =>
        eval .ne s₁ = some true ∧ eval .ne s₂ = some true ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀ c' s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' c' s₂ := by
  unfold updateTail
  refine (test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨P₁, P₂, esi⟩,
    ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      (⟨P₁.congr g₁ m₁ rd₁ wr₁, P₂.congr g₂ m₂ rd₂ wr₂, by rw [g₁, g₂]; exact esi,
        by rw [z₁, P₁.r14, VG.Proof.MdStream.X86_64.Update.ofNat_and_ne P₁.k_pos (P₁.k_lt hd).2],
        by rw [z₂, P₂.r14, VG.Proof.MdStream.X86_64.Update.ofNat_and_ne P₂.k_pos (P₂.k_lt hd).2]⟩ :
        VG.Proof.MdStream.X86_64.Update.Pending H s₀ c' k s₁ ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀' c' k s₂ ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
          s₁.zf = some false ∧ s₂.zf = some false)).seq ?_
  have cmp : RelCT isa (fun s₁ s₂ => (VG.Proof.MdStream.X86_64.Update.Pending H s₀ c' k s₁ ∧ VG.Proof.MdStream.X86_64.Update.Pending H s₀' c' k s₂ ∧
        s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.zf = some false ∧ s₂.zf = some false) ∧
        eval .ne s₁ = some true) (compressN name code)
      fun s₁ s₂ => (VG.Proof.MdStream.X86_64.Update.Inv H s₀ c' s₁ ∧ s₁.gpr .r14 = BitVec.ofNat 64 k ∧ VG.Proof.MdStream.X86_64.Update.nz k) ∧
        (VG.Proof.MdStream.X86_64.Update.Inv H s₀' c' s₂ ∧ s₂.gpr .r14 = BitVec.ofNat 64 k ∧ VG.Proof.MdStream.X86_64.Update.nz k) :=
    ((VG.Proof.MdStream.X86_64.compressWith_rel H VG.Proof.MdStream.X86_64.setsN_r14 ⟨_, by taint_decide⟩ hf fun s₁ s₂ ⟨⟨P₁, P₂, esi, _⟩, _⟩ =>
      ⟨⟨_, _, _, k, by rw [P₁.r14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₁.k_lt hd).2], P₁.callOk hd hp⟩,
        ⟨_, _, _, k, by rw [P₂.r14, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (P₂.k_lt hd).2], P₂.callOk hd hp'⟩,
        by rw [P₁.rbx, P₂.rbx]; exact hq.rdi, by rw [P₁.r15, P₂.r15]; exact hq.r8, esi,
        by rw [P₁.rsp, P₂.rsp]; exact hq.rsp, by rw [P₁.r14, P₂.r14]⟩).wp
      fun _ _ h => ⟨WP.mono (h.1.1.compress_ok hd hf hp) fun _ r =>
          ⟨r.1, r.2, h.1.1.ne_zero hd⟩,
        WP.mono (h.1.2.1.compress_ok hd hf hp') fun _ r =>
          ⟨r.1, r.2, h.1.2.1.ne_zero hd⟩⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ => (VG.Proof.MdStream.X86_64.Update.Inv H s₀ c' s₁ ∧ s₁.gpr .r14 = BitVec.ofNat 64 k ∧ VG.Proof.MdStream.X86_64.Update.nz k) ∧
        (VG.Proof.MdStream.X86_64.Update.Inv H s₀' c' s₂ ∧ s₂.gpr .r14 = BitVec.ofNat 64 k ∧ VG.Proof.MdStream.X86_64.Update.nz k))
      (.block [.alu .test .r14 (.reg .r14)]) fun s₁ s₂ =>
        eval .ne s₁ = some true ∧ eval .ne s₂ = some true ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀ c' s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' c' s₂ :=
    test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨⟨I₁, r₁, n₁⟩, ⟨I₂, r₂, n₂⟩⟩,
      ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      ⟨by simp [eval, z₁, r₁]; exact n₁, by simp [eval, z₂, r₂]; exact n₂, I₁.congr g₁ m₁ rd₁ wr₁, I₂.congr g₂ m₂ rd₂ wr₂⟩
  refine (RelCT.ite (fun s₁ s₂ h => ?_) cmp (RelCT.of_false fun s₁ s₂ h => ?_)).seq fin
  · simp [eval, h.2.2.2.1, h.2.2.2.2]
  · have := h.2; simp [eval, h.1.2.2.2.1] at this

/-- The second half, when all the data is buffered. -/
theorem tail_done :
    RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂) (updateTail name code) fun s₁ s₂ =>
      eval .ne s₁ = some false ∧ eval .ne s₂ = some false ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂ := by
  unfold updateTail
  refine (test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨D₁, D₂⟩,
    ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      (⟨⟨D₁.1.congr g₁ m₁ rd₁ wr₁, by rw [g₁]; exact D₁.2⟩, ⟨D₂.1.congr g₂ m₂ rd₂ wr₂, by rw [g₂]; exact D₂.2⟩,
        by rw [z₁, D₁.2, VG.Proof.MdStream.X86_64.Update.zero_and], by rw [z₂, D₂.2, VG.Proof.MdStream.X86_64.Update.zero_and]⟩ :
        VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂ ∧ s₁.zf = some true ∧ s₂.zf = some true)).seq ?_
  have skip : RelCT isa (fun s₁ s₂ => (VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂ ∧ s₁.zf = some true ∧
        s₂.zf = some true) ∧ eval .ne s₁ = some false) (.block [])
      fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block []) (by taint_decide)).wp fun _ _ h => ⟨WP.block_nil h.1.1, WP.block_nil h.1.2.1⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂)
      (.block [.alu .test .r14 (.reg .r14)]) fun s₁ s₂ =>
        eval .ne s₁ = some false ∧ eval .ne s₂ = some false ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂ :=
    test_rel.mono (fun _ _ h => h) fun s₁ s₂ ⟨_, σ₁, σ₂, ⟨D₁, D₂⟩,
      ⟨g₁, m₁, rd₁, wr₁, z₁⟩, ⟨g₂, m₂, rd₂, wr₂, z₂⟩⟩ =>
      ⟨by simp [eval, z₁, D₁.2], by simp [eval, z₂, D₂.2],
        ⟨D₁.1.congr g₁ m₁ rd₁ wr₁, by rw [g₁]; exact D₁.2⟩, ⟨D₂.1.congr g₂ m₂ rd₂ wr₂, by rw [g₂]; exact D₂.2⟩⟩
  refine (RelCT.ite (fun s₁ s₂ h => ?_) (RelCT.of_false fun s₁ s₂ h => ?_) skip).seq fin
  · simp [eval, h.2.2.1, h.2.2.2]
  · have := h.2; simp [eval, h.1.2.2.1] at this

/-- The loop invariant of two runs: both absorbed the first `len - n` bytes. -/
def LoopInv (H : Md P.B P.N P.L) (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ c, n = VG.Proof.MdStream.X86_64.Update.len s₀ - c ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' c s₂

include hd ht hf hp hp' hq in
theorem body_rel (n : Nat) :
    RelCT isa (VG.Proof.MdStream.X86_64.Update.LoopInv H s₀ s₀' n) (updateBody P name code) fun s₁ s₂ => eval .ne s₁ = eval .ne s₂ ∧
      (eval .ne s₁ = some false → VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' (VG.Proof.MdStream.X86_64.Update.len s₀) s₂) ∧
      (eval .ne s₁ = some true → ∃ m < n, VG.Proof.MdStream.X86_64.Update.LoopInv H s₀ s₀' m s₁ s₂) := by
  refine RelCT.exists_ fun c => fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨hn, h⟩ e₁ e₂ => ?_
  have tl : RelCT isa (VG.Proof.MdStream.X86_64.Update.Mid H s₀ s₀' c) (updateTail name code) fun s₁ s₂ =>
      (eval .ne s₁ = some true ∧ eval .ne s₂ = some true ∧ ∃ c', c < c' ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀ c' s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' c' s₂) ∨
      (eval .ne s₁ = some false ∧ eval .ne s₂ = some false ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀ s₁ ∧ VG.Proof.MdStream.X86_64.Update.Done H s₀' s₂) :=
    RelCT.or (RelCT.exists_ fun c' => RelCT.exists_ fun _ => fun _ _ _ _ _ _ ⟨hc, h⟩ e₁ e₂ =>
        let ⟨ht, z₁, z₂, I₁, I₂⟩ := VG.Proof.MdStream.X86_64.Update.tail_pending hd hf hp hp' hq _ _ _ _ _ _ h e₁ e₂
        ⟨ht, .inl ⟨z₁, z₂, c', hc, I₁, I₂⟩⟩)
      ((VG.Proof.MdStream.X86_64.Update.tail_done (name := name) (code := code) (s₀ := s₀) (s₀' := s₀')).mono (fun _ _ h => h)
        fun _ _ h => .inr h)
  have main : RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ c s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' c s₂) (updateBody P name code) fun s₁ s₂ =>
      eval .ne s₁ = eval .ne s₂ ∧
      (eval .ne s₁ = some false → VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' (VG.Proof.MdStream.X86_64.Update.len s₀) s₂) ∧
      (eval .ne s₁ = some true → ∃ m < n, VG.Proof.MdStream.X86_64.Update.LoopInv H s₀ s₀' m s₁ s₂) :=
    ((VG.Proof.MdStream.X86_64.Update.head_rel hd ht hp hp' hq).seq tl).mono (fun _ _ h => h) fun s₁ s₂ h => by
      rcases h with ⟨z₁, z₂, c', hc, I₁, I₂⟩ | ⟨z₁, z₂, D₁, D₂⟩
      · have := I₁.c_le
        exact ⟨z₁.trans z₂.symm, ⟨fun h => absurd (z₁.symm.trans h) (by simp),
          fun _ => ⟨VG.Proof.MdStream.X86_64.Update.len s₀ - c', by omega, c', rfl, I₁, I₂⟩⟩⟩
      · exact ⟨z₁.trans z₂.symm, ⟨fun _ => ⟨D₁.1, by rw [hq.len]; exact D₂.1⟩,
          fun h => absurd (z₁.symm.trans h) (by simp)⟩⟩
  exact main _ _ _ _ _ _ h e₁ e₂

end

section
variable {P : Params} {H : Md P.B P.N P.L}

theorem agree₀ (hd : VG.Proof.MdStream.X86_64.Dims P) {s₁ s₂ : State} (h₁ : (VG.Proof.MdStream.X86_64.updK H).pre s₁) (h₂ : (VG.Proof.MdStream.X86_64.updK H).pre s₂) (hpub : (VG.Proof.MdStream.X86_64.updK H).pub s₁ s₂) :
    X86_64.Taint.Agree (VG.Proof.MdStream.X86_64.τ₀ P) s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, (VG.Proof.MdStream.X86_64.updK H).pre s → X86_64.Taint.Wf (VG.Proof.MdStream.X86_64.τ₀ P) s := by
    intro s hs
    obtain ⟨-, hw, hdj, -⟩ := hs
    have := hd.N; have := hd.B; have := hd.so
    refine ⟨fun _ => ⟨by simp [hw, VG.Proof.MdStream.X86_64.τ₀], by simp [hw, hdj], by simp [hw]; omega⟩, fun p hp => ?_⟩
    simp only [VG.Proof.MdStream.X86_64.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [VG.Proof.MdStream.X86_64.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [VG.Proof.MdStream.X86_64.τ₀] at h
  · intro sl h; simp [VG.Proof.MdStream.X86_64.τ₀] at h

theorem pubEq_of {s₁ s₂ : State} (h : (VG.Proof.MdStream.X86_64.updK H).pub s₁ s₂) : VG.Proof.MdStream.X86_64.Update.PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem constantTime (hd : VG.Proof.MdStream.X86_64.Dims P) (ht : VG.Proof.MdStream.X86_64.Taints P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code) :
    ConstantTime isa (VG.Proof.MdStream.X86_64.updK H).pre (VG.Proof.MdStream.X86_64.updK H).pub (update P name code) := by
  intro s₀ s₀' t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  have hp := VG.Proof.MdStream.X86_64.Update.pre_of h₁; have hp' := VG.Proof.MdStream.X86_64.Update.pre_of h₂; have hq := VG.Proof.MdStream.X86_64.Update.pubEq_of hpub
  obtain ⟨_, hs⟩ := ht.updStart
  obtain ⟨_, he⟩ := ht.updEnd
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (.block (updateStart P))
      fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ 0 s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' 0 s₂ :=
    ((RelCT.taint (A := taint) (VG.Proof.MdStream.X86_64.τ₀ P) (fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact VG.Proof.MdStream.X86_64.Update.agree₀ hd h₁ h₂ hpub)
      hs).wp fun _ _ ⟨e, e'⟩ => by
        rw [e, e']; exact ⟨VG.Proof.MdStream.X86_64.Update.prologue_ok hd hp, VG.Proof.MdStream.X86_64.Update.prologue_ok hd hp'⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have lp := RelCT.loop (M := isa) (body := updateBody P name code) (c := .ne)
    (Q := fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' (VG.Proof.MdStream.X86_64.Update.len s₀) s₂) (VG.Proof.MdStream.X86_64.Update.LoopInv H s₀ s₀')
    (VG.Proof.MdStream.X86_64.Update.body_rel hd ht hf hp hp' hq) (VG.Proof.MdStream.X86_64.Update.len s₀)
  have epi : RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' (VG.Proof.MdStream.X86_64.Update.len s₀) s₂) (.block (restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      rw [h.1.r15, h.2.r15]; exact hq.r8) he
  have lp' : RelCT isa (fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ 0 s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' 0 s₂) (.loop (updateBody P name code) .ne)
      fun s₁ s₂ => VG.Proof.MdStream.X86_64.Update.Inv H s₀ (VG.Proof.MdStream.X86_64.Update.len s₀) s₁ ∧ VG.Proof.MdStream.X86_64.Update.Inv H s₀' (VG.Proof.MdStream.X86_64.Update.len s₀) s₂ :=
    lp.mono (fun _ _ h => ⟨0, by omega, h⟩) fun _ _ h => h
  exact (pro.seq (lp'.seq epi) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- A state satisfying the precondition (with no data). -/
def sat (P : Params) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .r8 => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x3000, P.so + 48⟩]

/-- `update` is verified if it never loads MXCSR. -/
theorem verified (hd : VG.Proof.MdStream.X86_64.Dims P) (ht : VG.Proof.MdStream.X86_64.Taints P) {name : String} {code : Prog isa} (hf : VG.Proof.MdStream.X86_64.CalleeOk H code)
    (hm : (update P name code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (update P name code) (VG.Proof.MdStream.X86_64.updK H) := by
  have := hd.N; have := hd.B; have := hd.so
  refine ⟨fun s hs => ?_, VG.Proof.MdStream.X86_64.Update.constantTime hd ht hf, ?_⟩
  · obtain ⟨t, s', he, h⟩ := VG.Proof.MdStream.X86_64.Update.correct hd hf (VG.Proof.MdStream.X86_64.Update.pre_of hs)
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩
  · refine ⟨VG.Proof.MdStream.X86_64.Update.sat P, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [VG.Proof.MdStream.X86_64.Update.sat]
    · exact Offset.disjoint_of_le (by simp <;> omega) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact Offset.disjoint_of_le (by simp) (by simp <;> omega)
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega) (by simp)).symm

end

end VG.Proof.MdStream.X86_64.Update

end

/- Proofs formerly in `VerifiedGarbage.Proof.MdStream.X86_64.Words`. -/
section

/-!
# Streaming Merkle–Damgård hash functions on x86-64: length fields and digests

What the length fields (`len64`) and digests (`out32`, `out64`) of
`Impl/MdStream/X86_64.lean` write, for the hash functions' `Shape`s.
-/

namespace VG.Proof.MdStream.X86_64

open VG VG.X86_64 VG.Impl.MdStream.X86_64
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil write_eq_writeBytes writeBytes_append
  writeBytes_frame)

/-! ## Byte order -/

/-- The bytes of a byte-reversed word, one by one. -/
theorem bswap32_byte_0 (x : BitVec 32) : (bswap32 x).extractLsb' 0 8 = x.extractLsb' 24 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap32_byte_1 (x : BitVec 32) : (bswap32 x).extractLsb' 8 8 = x.extractLsb' 16 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap32_byte_2 (x : BitVec 32) : (bswap32 x).extractLsb' 16 8 = x.extractLsb' 8 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap32_byte_3 (x : BitVec 32) : (bswap32 x).extractLsb' 24 8 = x.extractLsb' 0 8 := by
  unfold bswap32
  rw [BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bswap64_byte_0 (x : BitVec 64) : (bswap64 x).extractLsb' 0 8 = x.extractLsb' 56 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_add_le (v := 56) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_1 (x : BitVec 64) : (bswap64 x).extractLsb' 8 8 = x.extractLsb' 48 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 48) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_2 (x : BitVec 64) : (bswap64 x).extractLsb' 16 8 = x.extractLsb' 40 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 40) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_3 (x : BitVec 64) : (bswap64 x).extractLsb' 24 8 = x.extractLsb' 32 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 32) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_4 (x : BitVec 64) : (bswap64 x).extractLsb' 32 8 = x.extractLsb' 24 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 24) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_5 (x : BitVec 64) : (bswap64 x).extractLsb' 40 8 = x.extractLsb' 16 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 16) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_6 (x : BitVec 64) : (bswap64 x).extractLsb' 48 8 = x.extractLsb' 8 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_add_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self

theorem bswap64_byte_7 (x : BitVec 64) : (bswap64 x).extractLsb' 56 8 = x.extractLsb' 0 8 := by
  unfold bswap64
  rw [BitVec.extractLsb'_append_eq_of_le (v := 56) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 48) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 40) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 32) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 24) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 16) (w := 8) (by decide),
    BitVec.extractLsb'_append_eq_of_le (v := 8) (w := 8) (by decide)]
  exact BitVec.extractLsb'_eq_self


theorem bytes32_store (be : Bool) (x : BitVec 32) :
    (List.range 4).map (fun j => (if be then bswap32 x else x).extractLsb' (8 * j) 8) = bytes32 be x := by
  cases be
  · rfl
  · simp only [bytes32, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, Nat.reduceMul, VG.Proof.MdStream.X86_64.bswap32_byte_0, VG.Proof.MdStream.X86_64.bswap32_byte_1, VG.Proof.MdStream.X86_64.bswap32_byte_2,
      VG.Proof.MdStream.X86_64.bswap32_byte_3]


theorem bytes64_store (be : Bool) (x : BitVec 64) :
    (List.range 8).map (fun j => (if be then bswap64 x else x).extractLsb' (8 * j) 8) = bytes64 be x := by
  cases be
  · rfl
  · simp only [bytes64, ite_true, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, List.cons_append, List.reverse_cons, List.reverse_nil, Nat.reduceMul,
      VG.Proof.MdStream.X86_64.bswap64_byte_0, VG.Proof.MdStream.X86_64.bswap64_byte_1, VG.Proof.MdStream.X86_64.bswap64_byte_2, VG.Proof.MdStream.X86_64.bswap64_byte_3, VG.Proof.MdStream.X86_64.bswap64_byte_4, VG.Proof.MdStream.X86_64.bswap64_byte_5, VG.Proof.MdStream.X86_64.bswap64_byte_6,
      VG.Proof.MdStream.X86_64.bswap64_byte_7]


theorem writeW32 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 32) :
    m.writeW a (if be then bswap32 x else x) = VG.WriteBytes.writeBytes m a (bytes32 be x) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes, ← VG.Proof.MdStream.X86_64.bytes32_store]; rfl

theorem writeW64 (m : Mem) (a : Addr) (be : Bool) (x : BitVec 64) :
    m.writeW a (if be then bswap64 x else x) = VG.WriteBytes.writeBytes m a (bytes64 be x) := by
  rw [Mem.writeW, VG.WriteBytes.write_eq_writeBytes, ← VG.Proof.MdStream.X86_64.bytes64_store]; rfl

/-! ## Regions -/

theorem InRegions.offset {rs : List Region} {a : Addr} {n off m : Nat} (h : InRegions rs a n)
    (hm : off + m ≤ n) (hn : n < 2 ^ 64) : InRegions rs (a + BitVec.ofNat 64 off) m := by
  obtain ⟨R, hR, hc⟩ := h
  refine ⟨R, hR, ?_⟩
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 off - R.base).toNat ≤ (a - R.base).toNat + off := by
    rw [Offset.add_sub_comm,
      BitVec.toNat_add, VG.Proof.MdStream.X86_64.toNat_ofNat_lt (by omega)]
    exact Nat.mod_le _ _
  omega

/-! ## The length field -/

theorem times8 (x : BitVec 64) : x + x + (x + x) + (x + x + (x + x)) = BitVec.ofNat 64 (8 * x.toNat) := by
  bv_omega

/-- `len64 d be` stores `8 · r12` at `rbx + d`. -/
theorem len64_ok {d : Nat} {be : Bool} {s : State} {rest : List Instr} {Q : State → Prop}
    (hout : InRegions s.wr (s.gpr .rbx + BitVec.ofNat 64 d) 8)
    (k : ∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.mem = VG.WriteBytes.writeBytes s.mem (s.gpr .rbx + BitVec.ofNat 64 d)
        (bytes64 be (BitVec.ofNat 64 (8 * (s.gpr .r12).toNat))) → WP isa (.block rest) s' Q) :
    WP isa (.block (len64 d be ++ rest)) s Q := by
  have hdi : BitVec.ofInt 64 (d : Int) = BitVec.ofNat 64 d := VG.Proof.MdStream.X86_64.ofInt_natCast d
  refine VG.Proof.MdStream.X86_64.wp_mov fun s₁ u₁ _ _ => VG.Proof.MdStream.X86_64.wp_add fun s₂ u₂ => VG.Proof.MdStream.X86_64.wp_add fun s₃ u₃ => VG.Proof.MdStream.X86_64.wp_add fun s₄ u₄ => ?_
  have g₄ : ∀ r, r ≠ .rax → s₄.gpr r = s.gpr r := fun r h => by
    rw [u₄.other r h, u₃.other r h, u₂.other r h, u₁.other r h]
  have v₄ : s₄.gpr .rax = BitVec.ofNat 64 (8 * (s.gpr .r12).toNat) := by
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, VG.Proof.MdStream.X86_64.times8]
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have rd₄ : s₄.rd = s.rd := by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have ea : ∀ t : State, t.gpr .rbx = s.gpr .rbx →
      t.ea (at_ .rbx d) = s.gpr .rbx + BitVec.ofNat 64 d := fun t ht => by rw [VG.Proof.MdStream.X86_64.ea_at, ht, hdi]
  cases be
  · simp only [Bool.false_eq_true, ite_false]
    refine VG.Proof.MdStream.X86_64.wp_store (ea s₄ (g₄ _ (by decide))) (by rw [wr₄]; exact hout) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
    refine k s₅ (fun r h => by rw [g₅, g₄ r h]) (rd₅.trans rd₄) (wr₅.trans wr₄) ?_
    rw [m₅, m₄, v₄, ← VG.Proof.MdStream.X86_64.writeW64 _ _ false]; rfl
  · simp only [ite_true]
    refine VG.Proof.MdStream.X86_64.wp_bswap fun s₅ u₅ => VG.Proof.MdStream.X86_64.wp_store (ea s₅ (by rw [u₅.other _ (by decide), g₄ _ (by decide)]))
      (by rw [u₅.wr, wr₄]; exact hout) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
    refine k s₆ (fun r h => by rw [g₆, u₅.other r h, g₄ r h]) (by rw [rd₆, u₅.rd, rd₄]) (by rw [wr₆, u₅.wr, wr₄]) ?_
    rw [m₆, u₅.mem, m₄, u₅.gpr, v₄, ← VG.Proof.MdStream.X86_64.writeW64 _ _ true]; rfl

/-! ## The digest -/

/-- Words `[k, n)` of the hash value at `rbx` are written as `f` says, the first
`k` already written. -/
theorem out_words {w : Nat} (n : Nat) (hn : w * n ≤ 64) (f : BitVec (8 * w) → List Byte)
    (hf : ∀ x, (f x).length = w) (ins : Nat → List Instr) {s₀ : State}
    (hstep : ∀ k < n, ∀ (s : State) (rest : List Instr) (Q : State → Prop),
      s.gpr .rbx = s₀.gpr .rbx → s.gpr .rbp = s₀.gpr .rbp → s.rd = s₀.rd → s.wr = s₀.wr →
      (∀ s', (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
        s'.mem = VG.WriteBytes.writeBytes s.mem (s₀.gpr .rbp + BitVec.ofNat 64 (w * k))
          (f (s.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k)) (8 * w))) → WP isa (.block rest) s' Q) →
      WP isa (.block (ins k ++ rest)) s Q)
    (hd : Region.Disjoint ⟨s₀.gpr .rbx, w * n⟩ ⟨s₀.gpr .rbp, w * n⟩) :
    ∀ j ≤ n, ∀ s, (∀ r, r ≠ .rax → s.gpr r = s₀.gpr r) → s.rd = s₀.rd → s.wr = s₀.wr →
      s.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .rbp)
        ((List.range (n - j)).flatMap fun k => f (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k)) (8 * w))) →
      WP isa (.block (((List.range n).drop (n - j)).flatMap ins)) s fun s' =>
        (∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
        s'.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .rbp)
          ((List.range n).flatMap fun k => f (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k)) (8 * w))) := by
  have hflat : ∀ k, ((List.range k).flatMap fun k => f (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * k))
      (8 * w))).length = w * k := by
    intro k
    rw [List.length_flatMap, List.map_congr_left (fun x _ => hf _), List.map_const', List.sum_replicate_nat,
      List.length_range, Nat.mul_comm]
  intro j
  induction j with
  | zero =>
    intro _ s g rd wr m
    rw [Nat.sub_zero, List.drop_of_length_le (by simp), List.flatMap_nil]
    exact WP.block_nil ⟨g, rd, wr, m⟩
  | succ j ih =>
    intro hj s g rd wr m
    have hk : n - (j + 1) < n := by omega
    rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_range]
    refine hstep _ hk s _ _ (by rw [g _ (by decide)]) (by rw [g _ (by decide)]) rd wr
      fun s' g' rd' wr' m' => ?_
    rw [show n - (j + 1) + 1 = n - j by omega]
    refine ih (by omega) s' (fun r h => by rw [g' r h, g r h]) (rd'.trans rd) (wr'.trans wr) ?_
    -- The word read is not yet overwritten.
    have h1 : w * (n - (j + 1)) + w ≤ w * n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    have e8 : 8 * w / 8 = w := Nat.mul_div_cancel_left w (by decide)
    have hread : s.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * (n - (j + 1)))) (8 * w) =
        s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (w * (n - (j + 1)))) (8 * w) := by
      rw [m]
      refine (VG.WriteBytes.writeBytes_frame _ _ _ (R := ⟨s₀.gpr .rbp, w * n⟩) ?_).readW
        (r := ⟨s₀.gpr .rbx + BitVec.ofNat 64 (w * (n - (j + 1))), w⟩)
        (by rw [e8]; exact Region.contains_self _ _) ?_ (by rw [e8]; omega)
      · rw [hflat]
        simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]
        exact Nat.mul_le_mul_left _ (by omega)
      · intro r' hr'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
        subst hr'
        exact hd.sub_left (VG.Proof.MdStream.X86_64.sub_offset h1 (by omega))
    rw [m', hread, m, show n - j = n - (j + 1) + 1 by omega, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, ← VG.WriteBytes.writeBytes_append _ _ _ _ (by rw [hflat, hf]; omega), hflat]

theorem setWidth32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- `out32 n be` writes the `n` 32-bit words at `rbx` to `rbp`. -/
theorem out32_ok {n : Nat} (be : Bool) (hn : 4 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rbx) (4 * n)) (hout : InRegions s₀.wr (s₀.gpr .rbp) (4 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .rbx, 4 * n⟩ ⟨s₀.gpr .rbp, 4 * n⟩) :
    WP isa (.block (out32 n be)) s₀ fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .rbp)
        ((List.range n).flatMap fun k => bytes32 be (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (4 * k)) 32)) := by
  have h := VG.Proof.MdStream.X86_64.out_words (w := 4) n hn (bytes32 be) (bytes32_length be)
    (fun k => [.mov32 .rax (.mem (at_ .rbx (4 * k)))] ++ (if be then [.bswap32 .rax] else []) ++
      [.store32 (at_ .rbp (4 * k)) .rax]) (s₀ := s₀) ?_ hd n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, VG.WriteBytes.writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx hbp hrd hwr kk
  have hoff : 4 * k + 4 ≤ 4 * n := by omega
  refine VG.Proof.MdStream.X86_64.wp_mov32m (a := s₀.gpr .rbx + BitVec.ofNat 64 (4 * k)) (by rw [VG.Proof.MdStream.X86_64.ea_at, hbx, VG.Proof.MdStream.X86_64.ofInt_natCast])
    (by rw [hrd, hwr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
  have ea₁ : ∀ t : State, t.gpr .rbp = s₀.gpr .rbp →
      t.ea (at_ .rbp (4 * k)) = s₀.gpr .rbp + BitVec.ofNat 64 (4 * k) := fun t ht => by
    rw [VG.Proof.MdStream.X86_64.ea_at, ht, VG.Proof.MdStream.X86_64.ofInt_natCast]
  cases be
  · refine VG.Proof.MdStream.X86_64.wp_store32 (ea₁ s₁ (by rw [u₁.other _ (by decide), hbp]))
      (by rw [u₁.wr, hwr]; exact InRegions.offset hout hoff (by omega)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
    refine kk s₂ (fun r h => by rw [g₂, u₁.other r h]) (by rw [rd₂, u₁.rd]) (by rw [wr₂, u₁.wr]) ?_
    rw [m₂, u₁.mem, u₁.gpr, VG.Proof.MdStream.X86_64.setWidth32, ← VG.Proof.MdStream.X86_64.writeW32 _ _ false]; rfl
  · refine VG.Proof.MdStream.X86_64.wp_bswap32 fun s₂ u₂ => VG.Proof.MdStream.X86_64.wp_store32 (ea₁ s₂ (by rw [u₂.other _ (by decide),
                                                        u₁.other _ (by decide), hbp])) (by rw [u₂.wr, u₁.wr, hwr]; exact InRegions.offset hout hoff (by omega))
      fun s₃ g₃ m₃ rd₃ wr₃ => ?_
    refine kk s₃ (fun r h => by rw [g₃, u₂.other r h, u₁.other r h]) (by rw [rd₃, u₂.rd, u₁.rd])
      (by rw [wr₃, u₂.wr, u₁.wr]) ?_
    rw [m₃, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, VG.Proof.MdStream.X86_64.setWidth32, VG.Proof.MdStream.X86_64.setWidth32, ← VG.Proof.MdStream.X86_64.writeW32 _ _ true]; rfl

/-- `out64 n` writes the `n` 64-bit words at `rbx` to `rbp`, big-endian. -/
theorem out64_ok {n : Nat} (hn : 8 * n ≤ 64) {s₀ : State}
    (hin : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rbx) (8 * n)) (hout : InRegions s₀.wr (s₀.gpr .rbp) (8 * n))
    (hd : Region.Disjoint ⟨s₀.gpr .rbx, 8 * n⟩ ⟨s₀.gpr .rbp, 8 * n⟩) :
    WP isa (.block (out64 n)) s₀ fun s' =>
      (∀ r, r ≠ .rax → s'.gpr r = s₀.gpr r) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      s'.mem = VG.WriteBytes.writeBytes s₀.mem (s₀.gpr .rbp)
        ((List.range n).flatMap fun k => bytes64 true (s₀.mem.readW (s₀.gpr .rbx + BitVec.ofNat 64 (8 * k)) 64)) := by
  have h := VG.Proof.MdStream.X86_64.out_words (w := 8) n hn (bytes64 true) (bytes64_length true)
    (fun k => [.mov .rax (.mem (at_ .rbx (8 * k))), .bswap .rax, .store (at_ .rbp (8 * k)) .rax])
    (s₀ := s₀) ?_ hd n (Nat.le_refl _) s₀ (fun _ _ => rfl) rfl rfl
    (by rw [Nat.sub_self, List.range_zero, List.flatMap_nil, VG.WriteBytes.writeBytes_nil])
  · rw [Nat.sub_self, List.drop_zero] at h
    exact h
  intro k hk s rest Q hbx hbp hrd hwr kk
  have hoff : 8 * k + 8 ≤ 8 * n := by omega
  refine VG.Proof.MdStream.X86_64.wp_movm (a := s₀.gpr .rbx + BitVec.ofNat 64 (8 * k)) (by rw [VG.Proof.MdStream.X86_64.ea_at, hbx, VG.Proof.MdStream.X86_64.ofInt_natCast])
    (by rw [hrd, hwr]; exact InRegions.offset hin hoff (by omega)) fun s₁ u₁ => ?_
  refine VG.Proof.MdStream.X86_64.wp_bswap fun s₂ u₂ => VG.Proof.MdStream.X86_64.wp_store (a := s₀.gpr .rbp + BitVec.ofNat 64 (8 * k))
    (by rw [VG.Proof.MdStream.X86_64.ea_at, u₂.other _ (by decide), u₁.other _ (by decide), hbp, VG.Proof.MdStream.X86_64.ofInt_natCast])
    (by rw [u₂.wr, u₁.wr, hwr]; exact InRegions.offset hout hoff (by omega)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine kk s₃ (fun r h => by rw [g₃, u₂.other r h, u₁.other r h]) (by rw [rd₃, u₂.rd, u₁.rd])
    (by rw [wr₃, u₂.wr, u₁.wr]) ?_
  rw [m₃, u₂.mem, u₁.mem, u₂.gpr, u₁.gpr, ← VG.Proof.MdStream.X86_64.writeW64 _ _ true]; rfl

end VG.Proof.MdStream.X86_64

end
