module

import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Calls
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Init
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Variant
import VerifiedGarbage.Proof.ChaCha20.X86_64.Stream.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# Streaming ChaCha20 on x86-64: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/X86_64/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function, for any implementation `v` of
`vg_chacha20_xor`. The pieces are those that the proof of constant time
(`ApplyCT.lean`) relates in two runs.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open VG.X86_64
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- x86-64 contract for
`vg_chacha20_apply(state = rdi, data = rsi, len = rdx, scratch = rcx) -> eax`,
with 24 bytes of stack below the return address (8 for the return address
of a call, and 16 for the calls of any implementation of `vg_chacha20_xor`). -/
def applyX86_64 : Contract X86_64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 136⟩
    let data : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scratch : Region := ⟨s.gpr .rcx, 512⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 24, 24⟩
    s.rd = [] ∧ s.wr = [state, data, scratch] ∧ state.Disjoint data ∧ state.Disjoint scratch ∧
    data.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch ∧
    (s.gpr .rdi).toNat + 136 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + 512 ≤ 2 ^ 64
  post s s' :=
    keyAt s'.mem (s.gpr .rdi) = keyAt s.mem (s.gpr .rdi) ∧
      if (s.gpr .rdx).toNat ≤ leftAt s.mem (s.gpr .rdi) then
        (s'.gpr .rax).setWidth 32 = 1 ∧
          bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
              ((restAt s.mem (s.gpr .rdi)).take (s.gpr .rdx).toNat) ∧
          restAt s'.mem (s.gpr .rdi) = (restAt s.mem (s.gpr .rdi)).drop (s.gpr .rdx).toNat
      else
        (s'.gpr .rax).setWidth 32 = 0 ∧
          bytesAt s'.mem (s.gpr .rsi) (s.gpr .rdx).toNat = bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat ∧
          restAt s'.mem (s.gpr .rdi) = restAt s.mem (s.gpr .rdi)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
      [leftAt s₁.mem (s₁.gpr .rdi)] = [leftAt s₂.mem (s₂.gpr .rdi)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.X86_64.Stream

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Stream
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Proof.ChaCha20.X86_64 (toNat_ofNat_lt contains_off ea_at ofInt_natCast off_sep)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .rdi
abbrev dp : Addr := s₀.gpr .rsi
abbrev sc : Addr := s₀.gpr .rcx
abbrev L : Nat := (s₀.gpr .rdx).toNat
/-- The number of bytes of keystream left, and those in the buffered block. -/
abbrev N : Nat := leftAt s₀.mem (st s₀)
abbrev O : Nat := N s₀ % 64
/-- The bytes from the buffered block, the whole blocks and the bytes of the
next block that `apply` uses. -/
abbrev H : Nat := headLen s₀.mem (st s₀) (L s₀)
abbrev NB : Nat := blocksOf s₀.mem (st s₀) (L s₀)
abbrev T : Nat := tailLen s₀.mem (st s₀) (L s₀)
abbrev S0 : CState := stateAt s₀.mem (st s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (dp s₀ + BitVec.ofNat 64 k)
abbrev stR : Region := ⟨st s₀, 136⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
abbrev scR : Region := ⟨sc s₀, 512⟩
/-- The part of the scratch that `apply` writes. -/
abbrev scwR : Region := ⟨sc s₀, 424⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := ⟨s₀.gpr .rsp - 24, 24⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀, scR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  st_sc : (stR s₀).Disjoint (scR s₀)
  d_sc : (dR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_d : (retR s₀).Disjoint (dR s₀)
  ret_sc : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  stk_sc : (stkR s₀).Disjoint (scR s₀)
  wrap_st : (st s₀).toNat + 136 ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  wrap_sc : (sc s₀).toNat + 512 ≤ 2 ^ 64

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyX86_64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- Our caller's `rbx, rbp, r12, r13`, and the bytes left after `apply`, in
the scratch. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  rbx : m.readW (off (sc s₀) 384) 64 = s₀.gpr .rbx
  rbp : m.readW (off (sc s₀) 392) 64 = s₀.gpr .rbp
  r12 : m.readW (off (sc s₀) 400) 64 = s₀.gpr .r12
  r13 : m.readW (off (sc s₀) 408) 64 = s₀.gpr .r13
  left : m.readW (off (sc s₀) 416) 64 = BitVec.ofNat 64 (N s₀ - L s₀)

/-! ## Regions -/

theorem scwR_sub (s₀ : State) : Region.Sub (scwR s₀) (scR s₀) := Region.sub_prefix (by decide)

theorem APre.w_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 136) :
    InRegions s₀.wr (off (st s₀) d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., contains_off h (by omega_arith)⟩

theorem APre.r_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 136) :
    InRegions (s₀.rd ++ s₀.wr) (off (st s₀) d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

theorem APre.w_sc {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 512) :
    InRegions s₀.wr (off (sc s₀) d) n :=
  ⟨scR s₀, by rw [hp.wr]; simp, contains_off h (by omega_arith)⟩

theorem APre.r_sc {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 512) :
    InRegions (s₀.rd ++ s₀.wr) (off (sc s₀) d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_sc h

/-! ## The check -/

/-- After the check: `rax` holds the bytes left, and the carry whether they
are fewer than `len`. -/
structure Q0 (s₀ s : State) : Prop where
  rax : s.gpr .rax = BitVec.ofNat 64 (N s₀)
  cf : s.cf = some (decide (N s₀ < L s₀))
  keep : ∀ r, r ≠ .rax → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

set_option simprocs false in
theorem check_ok {s₀ : State} (hp : APre s₀) : WP isa (.block check) s₀ (Q0 s₀) := by
  have i₁ := hp.r_st (d := 128) (n := 8) (by decide)
  simp only [off] at i₁
  apply WP.of_runBlock
  simp only [check, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, arithFlags, State.load64, State.setReg, State.setFlags, i₁, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hn : s₀.mem.readW (st s₀ + BitVec.ofInt 64 ((128 : Nat) : Int)) 64 = BitVec.ofNat 64 (N s₀) := by
    rw [ofInt_natCast]; simp [N, leftAt]
  have hn' : s₀.mem.readW (s₀.gpr .rdi + 128) 64 = BitVec.ofNat 64 (N s₀) := by simp [N, leftAt]
  refine ⟨hn', ?_, fun r hr => by simp [hr], rfl, rfl, rfl⟩
  simp only [hn, toNat_ofNat_lt (N_lt s₀)]
  rfl


/-! ## The bytes left in the buffered block -/

/-- `and` with `-64` rounds down to a multiple of 64. -/
theorem and_mask (x : BitVec 64) :
    x &&& BitVec.signExtend 64 (0xffffffc0 : BitVec 32) = BitVec.ofNat 64 (x.toNat / 64 * 64) := by
  have : BitVec.signExtend 64 (0xffffffc0 : BitVec 32) = BitVec.ofNat 64 ((2 ^ 58 - 1) <<< 6) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hx := x.isLt
  generalize x.toNat = n at *
  rw [Nat.mod_eq_of_lt (by decide), Nat.mod_eq_of_lt (by omega_arith),
    show n / 64 * 64 = (n >>> 6) <<< 6 by rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 6 ≤ i
  · by_cases h2 : i - 6 < 58
    · simp [hi, h2, show 6 + (i - 6) = i by omega_arith]
    · have : n.testBit i = false := Nat.testBit_lt_two_pow (by
        calc n < 2 ^ 64 := hx
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega_arith))
      simp [hi, h2, this, show 6 + (i - 6) = i by omega_arith]
  · simp [hi]

/-- `and` with 63: the remainder modulo 64. -/
theorem and_63 (x : BitVec 64) : x &&& BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 (x.toNat % 64) := by
  have : BitVec.signExtend 64 (63 : BitVec 32) = BitVec.ofNat 64 (2 ^ 6 - 1) := by decide
  rw [this]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 2 ^ 6 - 1 < 2 ^ 64 by decide), Nat.and_two_pow_sub_one_eq_mod]
  omega_arith

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : Saved s₀ m


/-- Where our caller's registers and the bytes left after `apply` are. -/
abbrev savR (s₀ : State) : Region := ⟨off (sc s₀) 384, 40⟩

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' := by
  have c : ∀ d, 384 ≤ d → d + 8 ≤ 424 → (savR s₀).Contains (off (sc s₀) d) (64 / 8) := by
    intro d h₁ h₂
    simp only [savR, off_eq]
    exact Offset.contains _ h₁ (by omega_arith) (by omega_arith)
  exact ⟨by rw [hf.readW (c 384 (by decide) (by decide)) hd (by decide), h.rbx],
    by rw [hf.readW (c 392 (by decide) (by decide)) hd (by decide), h.rbp],
    by rw [hf.readW (c 400 (by decide) (by decide)) hd (by decide), h.r12],
    by rw [hf.readW (c 408 (by decide) (by decide)) hd (by decide), h.r13],
    by rw [hf.readW (c 416 (by decide) (by decide)) hd (by decide), h.left]⟩

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (scR s₀) := by
  simp only [savR, off_eq]; exact Offset.sub_base _ (by omega_arith)

/-- After `start`, with `x` in `rdx`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀)
  r13 : s.gpr .r13 = sc s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 x
  rax : s.gpr .rax = BitVec.ofNat 64 (O s₀)
  keep : ∀ r ∈ [Reg.r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [scwR s₀] s₀.mem s.mem

theorem readW64_off (m : Mem) (p : Addr) (v : BitVec 64) {d e : Nat} (hd : d < 2 ^ 32)
    (he : e < 2 ^ 32) (h : d + 8 ≤ e ∨ e + 8 ≤ d) :
    (m.writeW (off p e) v).readW (off p d) 64 = m.readW (off p d) 64 := readW64_writeW_off m p v hd he h

/-- A byte outside a write of at most 8 bytes is unchanged. -/
theorem byte_writeW_off (m : Mem) (p : Addr) {w : Nat} (v : BitVec w) {i e : Nat} (hw : w / 8 ≤ 8)
    (hi : i < 2 ^ 32) (he : e < 2 ^ 32) (h : i + 1 ≤ e ∨ e + w / 8 ≤ i) :
    (m.writeW (off p e) v) (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) := by
  have hs := off_sep p (d := i) (n := 1) (e := e) (k := w / 8) hi he (by decide) hw h
  rw [← off_eq]
  exact Mem.write_apply (hs _ (by simp))

set_option simprocs false in
theorem start_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block start) s fun s' => R1 s₀ (L s₀) s' ∧ s'.cf = some (decide (O s₀ < L s₀)) := by
  have o384 := hp.w_sc (d := 384) (n := 8) (by decide)
  have o392 := hp.w_sc (d := 392) (n := 8) (by decide)
  have o400 := hp.w_sc (d := 400) (n := 8) (by decide)
  have o408 := hp.w_sc (d := 408) (n := 8) (by decide)
  have o416 := hp.w_sc (d := 416) (n := 8) (by decide)
  rw [← h.wr] at o384 o392 o400 o408 o416
  simp only [off] at o384 o392 o400 o408 o416
  have hrdi := h.keep .rdi (by decide); have hrsi := h.keep .rsi (by decide)
  have hrdx := h.keep .rdx (by decide); have hrcx := h.keep .rcx (by decide)
  have hrbx := h.keep .rbx (by decide); have hrbp := h.keep .rbp (by decide)
  have hr12 := h.keep .r12 (by decide); have hr13 := h.keep .r13 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [start, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, execAlu, arithFlags, State.store64, State.setReg, State.setFlags, hrdi, hrsi, hrdx,
    hrcx, hrbx, hrbp, hr12, hr13, h.rax, o384, o392, o400, o408, o416, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  have hL := L_lt s₀
  have hN := N_lt s₀
  have hsub : BitVec.ofNat 64 (N s₀) - s₀.gpr .rdx = BitVec.ofNat 64 (N s₀ - L s₀) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat_lt hN]; exact hle),
      toNat_ofNat_lt hN, toNat_ofNat_lt (by omega_arith)]
  have hf : Frame [scwR s₀] s₀.mem (((((s₀.mem.writeW (off (sc s₀) 384) (s₀.gpr .rbx)).writeW
      (off (sc s₀) 392) (s₀.gpr .rbp)).writeW (off (sc s₀) 400) (s₀.gpr .r12)).writeW (off (sc s₀) 408)
      (s₀.gpr .r13)).writeW (off (sc s₀) 416) (BitVec.ofNat 64 (N s₀ - L s₀))) := by
    have c : ∀ d, d + 8 ≤ 424 → (scwR s₀).Contains (off (sc s₀) d) (64 / 8) :=
      fun d hd => contains_off hd (by omega_arith)
    exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (c 384 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 392 (by decide))).writeW (List.mem_singleton_self _) _
      (c 400 (by decide))).writeW (List.mem_singleton_self _) _ (c 408 (by decide))).writeW
      (List.mem_singleton_self _) _ (c 416 (by decide))
  rw [hsub, h.mem]
  refine ⟨⟨by simp (config := {decide := true}), by simp (config := {decide := true}),
    by simp (config := {decide := true}) [L], rfl,
    by simp (config := {decide := true}) [L, hrdx], ?_,
    fun r hr => ?_, h.rd, h.wr, ⟨fun i hi => ?_, ?_⟩,
    fun k hk => ?_, hf⟩, ?_⟩
  · simp (config := {decide := true}) only [ite_true, ite_false, and_63, toNat_ofNat_lt hN]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp (config := {decide := true}) <;>
      exact h.keep _ (by decide)
  · exact hf.bytes (R := stR s₀) (by simpa using hp.st_sc.sub_right (scwR_sub s₀)) (show 136 ≤ 2 ^ 64 by decide) hi
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (config := {decide := true}) only [readW64_off, Mem.readW_writeW_self64]
  · dsimp only
    rw [hf.bytes (R := dR s₀) (by simpa using hp.d_sc.sub_right (scwR_sub s₀)) (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega_arith) hk]
    simp
  · simp (config := {decide := true}) only [and_63, toNat_ofNat_lt hN,
      toNat_ofNat_lt (show N s₀ % 64 < 2 ^ 64 by omega_arith)]


theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)

set_option simprocs false in
theorem sel_ok {s₀ : State} {s : State} (h : R1 s₀ (L s₀) s) (hc : s.cf = some (decide (O s₀ < L s₀))) :
    WP isa (.ite .b (.block [.mov .rdx (.reg .rax)]) (.block [])) s (R1 s₀ (H s₀)) := by
  refine WP.ite (decide (O s₀ < L s₀)) (by simp only [eval, hc]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
      Option.some.injEq, exists_eq_left']
    have g : ∀ r, r ≠ .rdx → (s.setReg .rdx (s.gpr .rax)).gpr r = s.gpr r := fun r hr => by
      simp [State.setReg, hr]
    exact ⟨by rw [g _ (by decide), h.rbx], by rw [g _ (by decide), h.rbp], by rw [g _ (by decide), h.r12],
      by rw [g _ (by decide), h.r13],
      by simp [State.setReg, h.rax, H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [g _ (by decide), h.rax],
      fun r hr => by rw [g r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)]; exact h.keep r hr,
      h.rd, h.wr, h.mid, h.done, h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.rbx, h.rbp, h.r12, h.r13, ?_, h.rax, h.keep, h.rd, h.wr, h.mid, h.done,
      h.frame⟩
    rw [h.rdx, H, headLen, bufLeft, Nat.min_eq_right hge]


/-- After `part1`: the bytes from the buffered block XORed, and `rdx` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (L s₀ - H s₀)
  r13 : s.gpr .r13 = sc s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (64 * NB s₀)
  zf : s.zf = some (decide (64 * NB s₀ = 0))
  keep : ∀ r ∈ [Reg.r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ (H s₀) s.mem
  frame : Frame [scwR s₀, dR s₀] s₀.mem s.mem

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega_arith

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

theorem ptr_eq (p : Addr) {o : Nat} (ho : o < 64) :
    p + BitVec.signExtend 64 (128 : BitVec 32) - BitVec.ofNat 64 o = p + BitVec.ofNat 64 (128 - o) := by
  rw [show BitVec.signExtend 64 (128 : BitVec 32) = BitVec.ofNat 64 (128 - o) + BitVec.ofNat 64 o by
      rw [BitVec.ofNat_add_ofNat, show 128 - o + o = 128 by omega_arith]; decide,
    ← BitVec.add_assoc, BitVec.add_sub_cancel]

set_option simprocs false in
theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (sel_ok h₁ hc₁) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block.
  have h₃ : WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 128), .alu .sub .rsi (.reg .rax)]) s₂
      fun s₃ => R1 s₀ (H s₀) s₃ ∧ s₃.gpr .rsi = st s₀ + BitVec.ofNat 64 (128 - O s₀) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false, h₂.rbx, h₂.rax]
    refine ⟨⟨h₂.rbx, h₂.rbp, h₂.r12, h₂.r13, h₂.rdx, h₂.rax, fun r hr => ?_, h₂.rd, h₂.wr, h₂.mid, h₂.done,
      h₂.frame⟩, ptr_eq _ hO⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp (config := {decide := true}) <;>
      exact h₂.keep _ (by simp)
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h₃, hrsi⟩ => ?_)
  have hb : BPre s₃ (dp s₀) (st s₀ + BitVec.ofNat 64 (128 - O s₀)) (H s₀) :=
    ⟨h₃.rbp, hrsi, h₃.rdx, by omega_arith,
      by
        rw [h₃.wr]
        exact ⟨dR s₀, by rw [hp.wr]; simp, by
          simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add]; omega_arith⟩,
      by
        rw [h₃.rd, h₃.wr, hp.rd, hp.wr, List.nil_append]
        exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
      (hp.st_d.symm.sub_left (Region.sub_prefix (by omega_arith))).sub_right (Offset.sub_base _ (by omega_arith))⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hr12 : s₄.gpr .r12 = BitVec.ofNat 64 (L s₀ - H s₀) := by
    rw [h₄.r12, h₃.r12, Offset.ofNat_sub_ofNat hH]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left', ite_true, hr12, and_mask,
    toNat_ofNat_lt (show L s₀ - H s₀ < 2 ^ 64 by omega_arith)]
  have hnb : (L s₀ - H s₀) / 64 * 64 = 64 * NB s₀ := by simp only [NB, blocksOf, H]; omega_arith
  rw [hnb]
  have hrbx : s₄.gpr .rbx = st s₀ := by
    rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h₃.rbx]
  have hr13 : s₄.gpr .r13 = sc s₀ := by
    rw [h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h₃.r13]
  have hk4 : ∀ r ∈ [Reg.r14, .r15, .rsp], s₄.gpr r = s₀.gpr r := fun r hr => by
    have := h₃.keep r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
      (rw [← this]; exact h₄.keep _ (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨by simp (config := {decide := true}) [hrbx],
    by simp (config := {decide := true}) [h₄.rbp], by simp (config := {decide := true}) [hr12],
    hr13, by simp (config := {decide := true}), ?_, fun r hr => ?_, by rw [h₄.rd, h₃.rd],
    by rw [h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩, fun k hk => ?_, ?_⟩
  · rw [← Offset.ofNat_sub_ofNat_beq (x := 64 * NB s₀) (y := 0) (by omega_arith) (by omega_arith)]
    simp
  · have := hk4 r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simpa (config := {decide := true}) using this
  · rw [h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 136) (by omega_arith) (by omega_arith))
        (Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega_arith) _ (by simpa using hc))
  · exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.d_sc.symm.sub_left (savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega_arith) x (by simpa using hx)
  · by_cases hk' : k < H s₀
    · rw [h₄.data k hk', h₃.done k hk, Offset.add_add, h₃.mid.keep _ (by omega_arith)]
      simp [hk', KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in_prefix _ (by omega_arith) (by omega_arith),
        h₃.done k hk]
      simp [hk']
  · exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, prefix_sub _ hH⟩)



/-! ## The whole blocks -/

/-- The memory before the counter is advanced: the state at `p` copied to `q`. -/
def copyMem8 (m : Mem) (p q : Addr) : Mem :=
  (((((((m.writeW (off q 0) (m.readW (off p 0) 64)).writeW (off q 8) (m.readW (off p 8) 64)).writeW
    (off q 16) (m.readW (off p 16) 64)).writeW (off q 24) (m.readW (off p 24) 64)).writeW
    (off q 32) (m.readW (off p 32) 64)).writeW (off q 40) (m.readW (off p 40) 64)).writeW
    (off q 48) (m.readW (off p 48) 64)).writeW (off q 56) (m.readW (off p 56) 64)

/-- The memory after the arguments of `vg_chacha20_xor` are set up: the
state copied to `q`, and its counter advanced by `c`. -/
def copyMem (m : Mem) (p q : Addr) (c : BitVec 32) : Mem :=
  (copyMem8 m p q).writeW (off p 48) ((m.readW (off p 48) 64).setWidth 32 + c)

set_option simprocs false in
theorem args_exec {s : State} {p q : Addr} (hrbx : s.gpr .rbx = p) (hr13 : s.gpr .r13 = q)
    (hw : ∀ d, d + 8 ≤ 136 → InRegions s.wr (off p d) 8)
    (hwq : ∀ d, d + 8 ≤ 512 → InRegions s.wr (off q d) 8) (hrd : s.rd = []) :
    WP isa (.block blocksArgs) s fun s' => s'.mem = copyMem s.mem p q ((s.gpr .rdx >>> 6).setWidth 32) ∧
      s'.gpr .rdi = q ∧ s'.gpr .rsi = s.gpr .rbp ∧ s'.gpr .rcx = q + BitVec.ofNat 64 64 ∧
      s'.gpr .rdx = s.gpr .rdx ∧ s'.gpr .rbp = s.gpr .rbp + s.gpr .rdx ∧
      s'.gpr .r12 = s.gpr .r12 - s.gpr .rdx ∧
      (∀ r ∈ [Reg.rbx, .r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i : ∀ d, d + 8 ≤ 136 → InRegions (s.rd ++ s.wr) (off p d) 8 := fun d hd => by
    rw [hrd, List.nil_append]; exact hw d hd
  have o4 : InRegions s.wr (off p 48) 4 := by
    obtain ⟨r, hr, hc⟩ := hw 48 (by decide); exact ⟨r, hr, by simp only [Region.Contains] at hc ⊢; omega_arith⟩
  have i0 := i 0 (by decide); have i8 := i 8 (by decide); have i16 := i 16 (by decide)
  have i24 := i 24 (by decide); have i32 := i 32 (by decide); have i40 := i 40 (by decide)
  have i48 := i 48 (by decide); have i56 := i 56 (by decide)
  have o0 := hwq 0 (by decide); have o8 := hwq 8 (by decide); have o16 := hwq 16 (by decide)
  have o24 := hwq 24 (by decide); have o32 := hwq 32 (by decide); have o40 := hwq 40 (by decide)
  have o48 := hwq 48 (by decide); have o56 := hwq 56 (by decide)
  simp only [off] at i0 i8 i16 i24 i32 i40 i48 i56 o4 o0 o8 o16 o24 o32 o40 o48 o56
  apply WP.of_runBlock
  simp (config := {decide := true}) only [blocksArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, readSrc32, execAlu, execAlu32, execShift, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.cf_arithFlags,
    RegUpd.zf_arithFlags, State.store64, State.store32,
    State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.xmm_setReg, RegUpd.cf_setReg, RegUpd.zf_setReg, State.setReg32, RegUpd.gpr_setFlags,
    RegUpd.mem_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.xmm_setFlags, hrbx, hr13, i0, i8,
    i16, i24, i32, i40, i48, i56, o4, o0, o8, o16, o24, o32, o40, o48, o56, ite_true, ite_false,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', RegUpd.setWidth_setWidth_32]
  refine ⟨rfl, trivial, trivial, rfl, trivial, trivial, trivial, fun r hr => ?_, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrbx, hr13]

theorem copyMem_eq (m : Mem) (p q : Addr) (c : BitVec 32) :
    copyMem m p q c = (copyMem8 m p q).writeW (off p 48) ((m.readW (off p 48) 64).setWidth 32 + c) := rfl

theorem copyMem8_frame (m : Mem) (p q : Addr) : Frame [⟨q, 64⟩] m (copyMem8 m p q) := by
  have c : ∀ d, d + 8 ≤ 64 → (⟨q, 64⟩ : Region).Contains (off q d) (64 / 8) :=
    fun d hd => by rw [off_eq]; exact contains_off hd (by omega_arith)
  simp only [copyMem8]
  have w : ∀ {m' : Mem} (_ : Frame [⟨q, 64⟩] m m') (d : Nat), d + 8 ≤ 64 →
      ∀ v : BitVec 64, Frame [⟨q, 64⟩] m (m'.writeW (off q d) v) :=
    fun hf d h v => hf.writeW (List.mem_singleton_self _) v (c d h)
  exact w (w (w (w (w (w (w (w (Frame.refl _ _) 0 (by decide) _) 8 (by decide) _) 16 (by decide) _)
    24 (by decide) _) 32 (by decide) _) 40 (by decide) _) 48 (by decide) _) 56 (by decide) _

theorem copyMem_frame (m : Mem) (p q : Addr) (c : BitVec 32) :
    Frame [⟨p, 64⟩, ⟨q, 64⟩] m (copyMem m p q c) := by
  rw [copyMem_eq]
  refine ((copyMem8_frame m p q).mono (by simp)).writeW (List.mem_cons_self ..) _ ?_
  simp only [off_eq]; exact Offset.contains_base _ (by omega_arith) (by omega_arith)

/-- The copy of the state. -/
theorem copyMem_copy (m : Mem) (p q : Addr) (c : BitVec 32) (hd : (⟨q, 64⟩ : Region).Disjoint ⟨p, 64⟩) :
    stateAt (copyMem m p q c) q = stateAt m p := by
  refine stateAt_congr fun i hi => ?_
  have hf : Frame [⟨off p 48, 4⟩] (copyMem8 m p q) (copyMem m p q c) := by
    rw [copyMem_eq]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  rw [hf.bytes (R := ⟨q, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hd.sub_right (by rw [off_eq]; exact Offset.sub_base _ (by omega_arith))) (show 64 ≤ 2 ^ 64 by decide) hi]
  have hw : ∀ k, 0 ≤ k → k < 8 → (copyMem8 m p q).readW (q + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (p + BitVec.ofNat 64 (8 * k)) 64 := by
    intro k _ h₂
    rw [word_off, word_off]
    simp only [copyMem8]
    obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega_arith
    all_goals simp (config := {decide := true}) only [Mem.readW_writeW_self64, readW64_off]
  have hm : ∀ k, 0 ≤ k → k < 8 → m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 :=
    fun _ _ _ => rfl
  rw [byte_of_words64 hw (Nat.zero_le _) (by omega_arith), byte_of_words64 hm (i := i) (Nat.zero_le _) (by omega_arith)]

/-- The state, with its counter advanced. -/
theorem copyMem_state (m : Mem) (p q : Addr) (c : BitVec 32) (hd : (⟨p, 64⟩ : Region).Disjoint ⟨q, 64⟩) :
    stateAt (copyMem m p q c) p = (stateAt m p).set 12 ((stateAt m p)[12] + c) := by
  rw [copyMem_eq, Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter,
    Proof.ChaCha20.X86_64.Xor.stateAt_frame (copyMem8_frame m p q) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd),
    readW64_setWidth]
  simp [stateAt, off_eq]


theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (64 * nb) >>> 6).setWidth 32 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, toNat_ofNat_lt h, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  omega_arith

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  rbp : s.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  r12 : s.gpr .r12 = BitVec.ofNat 64 (T s₀)
  r13 : s.gpr .r13 = sc s₀
  keep : ∀ r ∈ [Reg.r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : Saved s₀ s.mem
  done : Done s₀ (H s₀ + 64 * NB s₀) s.mem
  frame : Frame [stR s₀, dR s₀, scwR s₀, stkR s₀] s₀.mem s.mem

theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by simp only [T, NB, tailLen, blocksOf, H]; omega_arith
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega_arith

theorem Mid.state {s₀ : State} {m : Mem} (h : Mid s₀ m) : stateAt m (st s₀) = S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega_arith)

theorem nb_zero_ok {s₀ : State} {s : State} (h : Q1 s₀ s) (h0 : 64 * NB s₀ = 0) : Q2 s₀ s := by
  have hT := T_eq s₀
  refine ⟨h.rbx, by rw [h.rbp, h0, Nat.add_zero], by rw [h.r12, hT, h0, Nat.sub_zero], h.r13, h.keep, h.rd, h.wr,
    by rw [h.mid.state, show NB s₀ = 0 by omega_arith, ctr_zero], fun i hi => h.mid.keep _ (by omega_arith), h.mid.saved,
    by rw [h0, Nat.add_zero]; exact h.done, h.frame.mono (by simp)⟩

theorem Q1.w {s₀ s : State} (hp : APre s₀) (h : Q1 s₀ s) :
    ∀ d, d + 8 ≤ 136 → InRegions s.wr (off (st s₀) d) 8 := fun d hd => by rw [h.wr]; exact hp.w_st hd

theorem Q1.wq {s₀ s : State} (hp : APre s₀) (h : Q1 s₀ s) :
    ∀ d, d + 8 ≤ 512 → InRegions s.wr (off (sc s₀) d) 8 := fun d hd => by rw [h.wr]; exact hp.w_sc hd

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨sc s₀, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨sc s₀ + BitVec.ofNat 64 64, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (scR s₀) := Region.sub_prefix (by decide)
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (scR s₀) := Offset.sub_base _ (by omega_arith)
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)
theorem stS (s₀ : State) : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := Region.sub_prefix (by decide)

/-- `⟨st, 64⟩` and `⟨sc, 64⟩` are apart. -/
theorem APre.st_cp {s₀ : State} (hp : APre s₀) : (⟨st s₀, 64⟩ : Region).Disjoint (cpR s₀) :=
  (hp.st_sc.sub_left (stS s₀)).sub_right (cpR_sub s₀)


theorem part2_eq (x : Impl.ChaCha20.X86_64.Callee) :
    part2 x = .ite .e (.block []) (.seq (.block blocksArgs) (.call x.name x.code)) := rfl

theorem blocks_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s)
    (hnb : 0 < NB s₀) : WP isa (.seq (.block blocksArgs) (.call v.callee.name v.callee.code)) s (Q2 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hT := T_eq s₀
  refine WP.seq (WP.mono (args_exec h.rbx h.r13 (h.w hp) (h.wq hp) (by rw [h.rd, hp.rd]))
    fun s₁ ⟨m₁, rdi₁, rsi₁, rcx₁, rdx₁, rbp₁, r12₁, k₁, rd₁, wr₁⟩ => ?_)
  rw [h.rdx, shr_eq (by omega_arith)] at m₁
  rw [h.rdx] at rdx₁
  rw [h.rbp] at rsi₁
  have hsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [k₁ .rsp (by simp), h.keep .rsp (by simp)]
  have hstk : below (s₁.gpr .rsp) 24 = stkR s₀ := by rw [hsp₁]; rfl
  have hwr₁ : s₁.wr = [stR s₀, dR s₀, scR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have dSB : (cpR s₀).Disjoint (wkR s₀) := Offset.base_disjoint _ (by omega_arith) (by omega_arith)
  have dSD : (cpR s₀).Disjoint (blR s₀) := (hp.d_sc.symm.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀)
  have dDB : (blR s₀).Disjoint (wkR s₀) := (hp.d_sc.sub_left (blR_sub s₀)).sub_right (wkR_sub s₀)
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀, scR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, hHNB⟩
    · exact ⟨scR s₀, by simp, 64, rfl, by simp⟩
  have hwrap : (dp s₀ + BitVec.ofNat 64 (H s₀)).toNat + 64 * NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega_arith)]
    omega_arith
  refine xor_call v (S := sc s₀) (D := dp s₀ + BitVec.ofNat 64 (H s₀))
    (B := sc s₀ + BitVec.ofNat 64 64) (n := 64 * NB s₀) rdi₁ rsi₁ rdx₁ rcx₁ (by omega_arith) dSD dSB dDB hwrap
    (by rw [hstk]; exact hp.stk_sc.sub_right (cpR_sub s₀)) (by rw [hstk]; exact hp.stk_d.sub_right (blR_sub s₀))
    (by rw [hstk]; exact hp.stk_sc.sub_right (wkR_sub s₀))
    (by rw [hrd₁, hwr₁, List.nil_append, List.nil_append]; exact Covers.of_sub hcov)
    (by rw [hwr₁]; exact Covers.of_sub hcov) ?_
  intro s₂ rd₂ wr₂ cs₂ f₂ x₂
  rw [hstk] at f₂
  have g : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₂.gpr r = s₁.gpr r :=
    fun r hr => cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (cpR s₀) → R.Disjoint (blR s₀) → R.Disjoint (wkR s₀) →
      R.Disjoint (stkR s₀) → ∀ r ∈ [cpR s₀, blR s₀, wkR s₀, stkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ h₄ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  have nc : ∀ R : Region, R.Disjoint ⟨st s₀, 64⟩ → R.Disjoint (cpR s₀) →
      ∀ r ∈ [⟨st s₀, 64⟩, cpR s₀], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  have fc := copyMem_frame s.mem (st s₀) (sc s₀) (BitVec.ofNat 32 (NB s₀))
  rw [← m₁] at fc
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega_arith)
  have svS := savR_sub s₀
  -- The state, the scratch, the data and the stack are apart.
  have ts : ∀ R R', Region.Sub R (stR s₀) → Region.Sub R' (scR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_sc.sub_left h₁).sub_right h₂
  have td : ∀ R R', Region.Sub R (stR s₀) → Region.Sub R' (dR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.sub_left h₁).sub_right h₂
  have cd : ∀ R R', Region.Sub R (scR s₀) → Region.Sub R' (dR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.d_sc.symm.sub_left h₁).sub_right h₂
  have tk : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (stkR s₀) := fun R hR => hp.stk_st.symm.sub_left hR
  have ck : ∀ R, Region.Sub R (scR s₀) → R.Disjoint (stkR s₀) := fun R hR => hp.stk_sc.symm.sub_left hR
  have dk : ∀ R, Region.Sub R (dR s₀) → R.Disjoint (stkR s₀) := fun R hR => hp.stk_d.symm.sub_left hR
  have dS : Region.Sub (dR s₀) (dR s₀) := fun _ h => h
  refine ⟨by rw [g .rbx (by simp), k₁ .rbx (by simp), h.rbx], ?_, ?_,
    by rw [g .r13 (by simp), k₁ .r13 (by simp), h.r13], fun r hr => ?_, by rw [rd₂, rd₁, h.rd],
    by rw [wr₂, wr₁, h.wr], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g .rbp (by simp), rbp₁, h.rbp, h.rdx, Offset.add_add]
  · rw [g .r12 (by simp), r12₁, h.r12, h.rdx, Offset.ofNat_sub_ofNat (by omega_arith), hT, Nat.sub_sub]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [g r (by rcases hr with rfl | rfl | rfl <;> simp), k₁ r (by rcases hr with rfl | rfl | rfl <;> simp)]
    exact h.keep r (by rcases hr with rfl | rfl | rfl <;> simp)
  · rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame f₂ (nd _ hp.st_cp
        (td _ _ (stS s₀) (blR_sub s₀)) (ts _ _ (stS s₀) (wkR_sub s₀)) (tk _ (stS s₀))),
      m₁, copyMem_state _ _ _ _ hp.st_cp, h.mid.state]
    rfl
  · rw [← Offset.add_add, f₂.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (ts _ _ bufS (cpR_sub s₀)) (td _ _ bufS (blR_sub s₀)) (ts _ _ bufS (wkR_sub s₀)) (tk _ bufS))
        (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega_arith) (by omega_arith))
        (ts _ _ bufS (cpR_sub s₀))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega_arith)
  · refine (h.mid.saved.frame fc (nc _ ((ts _ _ (stS s₀) svS).symm) ?_)).frame f₂ (nd _ ?_ (cd _ _ svS (blR_sub s₀))
      ?_ (ck _ svS))
    · simp only [savR, off_eq]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · simp only [savR, off_eq]; exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
    · simp only [savR, off_eq]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
  · have fcd : s₁.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := dR s₀) (nc _ (td _ _ (stS s₀) dS).symm (cd _ _ (cpR_sub s₀) dS).symm)
        (show L s₀ ≤ 2 ^ 64 by omega_arith) hk
    by_cases hk₁ : k < H s₀
    · have hpre : Region.Sub ⟨dp s₀, H s₀⟩ (dR s₀) := prefix_sub _ hH
      rw [f₂.bytes (R := ⟨dp s₀, H s₀⟩) (nd _ (cd _ _ (cpR_sub s₀) hpre).symm
          (Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (cd _ _ (wkR_sub s₀) hpre).symm (dk _ hpre))
          (show H s₀ ≤ 2 ^ 64 by omega_arith) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega_arith)]
    by_cases hk₂ : k < H s₀ + 64 * NB s₀
    · have e := xor_getD (length_keystream _ _) x₂ (j := k - H s₀) (by omega_arith)
      rw [Offset.add_add, show H s₀ + (k - H s₀) = k by omega_arith, fcd, h.done k hk, ite_neg hk₁, m₁,
        copyMem_copy _ _ _ _ hp.st_cp.symm, h.mid.state, keystream_getD _ (by omega_arith)] at e
      rw [e, ite_pos hk₂]
      simp only [KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩ (dR s₀) :=
        Offset.sub_base _ (by omega_arith)
      have := f₂.bytes (R := ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩)
        (nd _ (cd _ _ (cpR_sub s₀) hR).symm (Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith))
          (cd _ _ (wkR_sub s₀) hR).symm (dk _ hR)) (show L s₀ - (H s₀ + 64 * NB s₀) ≤ 2 ^ 64 by omega_arith)
          (i := k - (H s₀ + 64 * NB s₀)) (by simp only; omega_arith)
      rw [Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega_arith] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine ((h.frame.mono (by simp)).trans (fc.sub fun r hr => ?_)).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, stS s₀⟩
      · exact ⟨scwR s₀, by simp, Region.sub_prefix (by decide)⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨scwR s₀, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨dR s₀, by simp, blR_sub s₀⟩
      · exact ⟨scwR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩


theorem part2_ok (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) :
    WP isa (part2 v.callee) s (Q2 s₀) := by
  rw [part2_eq]
  refine WP.ite (decide (64 * NB s₀ = 0)) (by simp [eval, h.zf])
    (fun h0 => WP.block_nil (M := isa) (nb_zero_ok h (by simpa using h0)))
    (fun h0 => blocks_ok v hp h (by simp at h0; omega_arith))

/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  rbx : s.gpr .rbx = st s₀
  r13 : s.gpr .r13 = sc s₀
  keep : ∀ r ∈ [Reg.r14, .r15, .rsp], s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
    if T s₀ = 0 then s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0
  saved : Saved s₀ s.mem
  done : Done s₀ (L s₀) s.mem
  frame : Frame [stR s₀, dR s₀, scwR s₀, stkR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : Q2 s₀ s) (h0 : T s₀ = 0) : Q3 s₀ s := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  refine ⟨h.rbx, h.r13, h.keep, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl,
    h.saved, by rw [show L s₀ = H s₀ + 64 * NB s₀ by omega_arith]; exact h.done, h.frame⟩


/-- Where the block function computes the next block: the scratch after
the copy of the state. -/
abbrev bufR (s₀ : State) : Region := ⟨sc s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (bufR s₀) (scR s₀) := Offset.sub_base _ (by omega_arith)

theorem below8_stk (s₀ : State) : Region.Sub (below (s₀.gpr .rsp) 8) (stkR s₀) :=
  below_sub (by decide) (by decide)

/-- The memory after `k` words of the block at `q + 64` are copied to `p + 64`. -/
def copyBlk (m : Mem) (p q : Addr) : Nat → Mem
  | 0 => m
  | k + 1 => (copyBlk m p q k).writeW (off p (64 + 8 * k)) ((copyBlk m p q k).readW (off q (64 + 8 * k)) 64)

theorem copyBlock_eq : copyBlock =
    [.mov .rax (.mem (at_ .r13 64)), .store (at_ .rbx 64) .rax, .mov .rax (.mem (at_ .r13 72)),
     .store (at_ .rbx 72) .rax, .mov .rax (.mem (at_ .r13 80)), .store (at_ .rbx 80) .rax,
     .mov .rax (.mem (at_ .r13 88)), .store (at_ .rbx 88) .rax, .mov .rax (.mem (at_ .r13 96)),
     .store (at_ .rbx 96) .rax, .mov .rax (.mem (at_ .r13 104)), .store (at_ .rbx 104) .rax,
     .mov .rax (.mem (at_ .r13 112)), .store (at_ .rbx 112) .rax, .mov .rax (.mem (at_ .r13 120)),
     .store (at_ .rbx 120) .rax] := rfl

set_option simprocs false in
theorem copyBlock_exec {s : State} {p q : Addr} (hrbx : s.gpr .rbx = p) (hr13 : s.gpr .r13 = q)
    (hw : ∀ d, d + 8 ≤ 136 → InRegions s.wr (off p d) 8)
    (hr : ∀ d, d + 8 ≤ 512 → InRegions (s.rd ++ s.wr) (off q d) 8) :
    WP isa (.block copyBlock) s fun s' => s'.mem = copyBlk s.mem p q 8 ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have o64 := hw 64 (by decide); have o72 := hw 72 (by decide); have o80 := hw 80 (by decide)
  have o88 := hw 88 (by decide); have o96 := hw 96 (by decide); have o104 := hw 104 (by decide)
  have o112 := hw 112 (by decide); have o120 := hw 120 (by decide)
  have i64 := hr 64 (by decide); have i72 := hr 72 (by decide); have i80 := hr 80 (by decide)
  have i88 := hr 88 (by decide); have i96 := hr 96 (by decide); have i104 := hr 104 (by decide)
  have i112 := hr 112 (by decide); have i120 := hr 120 (by decide)
  simp only [off] at o64 o72 o80 o88 o96 o104 o112 o120 i64 i72 i80 i88 i96 i104 i112 i120
  apply WP.of_runBlock
  simp (config := {decide := true}) only [copyBlock_eq, runBlock_cons, runStep_some, runBlock_nil, exec,
    ea_at, readSrc, State.store64, State.load64, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, hrbx, hr13, ite_true, ite_false, o64, o72, o80, o88, o96, o104, o112, o120, i64, i72,
    i80, i88, i96, i104, i112, i120, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun r h => by simp [h], trivial⟩

theorem copyBlk_frame (m : Mem) (p q : Addr) {k : Nat} (hk : k ≤ 8) :
    Frame [⟨p + BitVec.ofNat 64 64, 64⟩] m (copyBlk m p q k) := by
  induction k with
  | zero => exact Frame.refl _ _
  | succ k ih =>
    exact (ih (by omega_arith)).writeW (List.mem_singleton_self _) _ (by
      rw [off_eq]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))

theorem copyBlk_word (m : Mem) (p q : Addr)
    (hd : (⟨p + BitVec.ofNat 64 64, 64⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 64, 64⟩) {k : Nat} (hk : k ≤ 8) :
    ∀ j < k, (copyBlk m p q k).readW (off p (64 + 8 * j)) 64 = m.readW (off q (64 + 8 * j)) 64 := by
  induction k with
  | zero => intro j hj; omega_arith
  | succ k ih =>
    intro j hj
    simp only [copyBlk]
    by_cases hjk : j = k
    · subst hjk
      rw [Mem.readW_writeW_self64]
      exact (copyBlk_frame m p q (by omega_arith)).readW (r := ⟨q + BitVec.ofNat 64 64, 64⟩)
        (by rw [off_eq]; exact Offset.contains _ (by omega_arith) (by omega_arith) (by omega_arith))
        (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hd.symm) (by decide)
    · rw [readW64_off _ _ _ (by omega_arith) (by omega_arith) (by omega_arith)]
      exact ih (by omega_arith) j (by omega_arith)

theorem copyBlk_bytes (m : Mem) (p q : Addr)
    (hd : (⟨p + BitVec.ofNat 64 64, 64⟩ : Region).Disjoint ⟨q + BitVec.ofNat 64 64, 64⟩) {i : Nat} (hi : i < 64) :
    copyBlk m p q 8 (p + BitVec.ofNat 64 (64 + i)) = m (q + BitVec.ofNat 64 (64 + i)) := by
  have hw : ∀ k, 8 ≤ k → k < 16 → (copyBlk m p q 8).readW (p + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (q + BitVec.ofNat 64 (8 * k)) 64 := by
    intro k h₁ h₂
    have := copyBlk_word m p q hd (k := 8) (by decide) (k - 8) (by omega_arith)
    rwa [off_eq, off_eq, show 64 + 8 * (k - 8) = 8 * k by omega_arith] at this
  have hm : ∀ k, 8 ≤ k → k < 16 → m.readW (q + BitVec.ofNat 64 (8 * k)) 64 =
      m.readW (q + BitVec.ofNat 64 (8 * k)) 64 := fun _ _ _ => rfl
  rw [byte_of_words64 hw (by omega_arith) (by omega_arith),
    byte_of_words64 hm (i := 64 + i) (by omega_arith) (by omega_arith)]

set_option simprocs false in
/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {p : Addr} (hrbx : s.gpr .rbx = p) (hw : InRegions s.wr (off p 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (off p 48) 4) :
    WP isa (.block [.mov32 .rax (.mem (at_ .rbx 48)), .alu32 .add .rax (.imm 1),
      .store32 (at_ .rbx 48) .rax, .mov .rsi (.reg .rbx), .alu .add .rsi (.imm 64),
      .mov .rdx (.reg .r12)]) s fun s' =>
      s'.mem = s.mem.writeW (off p 48) (s.mem.readW (off p 48) 32 + 1) ∧
      s'.gpr .rsi = p + BitVec.ofNat 64 64 ∧ s'.gpr .rdx = s.gpr .r12 ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [off] at hw hr
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_at, readSrc,
    readSrc32, execAlu, execAlu32, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.cf_arithFlags, RegUpd.zf_arithFlags, State.load32,
    State.store32, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.xmm_setReg, RegUpd.cf_setReg, RegUpd.zf_setReg, State.setReg32,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true,
    ite_false, hrbx, hw, hr, RegUpd.setWidth_setWidth_32]
  exact ⟨trivial, rfl, trivial, fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃], trivial⟩

set_option simprocs false in
theorem tail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) (ht : T s₀ ≠ 0) :
    WP isa (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
      (.seq (.block copyBlock) tailXor))) s (Q3 s₀) := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have h₁ : WP isa (.block tailArgs) s fun s₁ => s₁.gpr .rdi = st s₀ ∧
      s₁.gpr .rsi = sc s₀ + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [tailArgs, runBlock_cons, runStep_some, runBlock_nil, exec,
      readSrc, execAlu, arithFlags, State.setReg, State.setFlags, Option.map_some, Option.bind_some,
      Option.some.injEq, exists_eq_left', ite_true, ite_false, h.rbx, h.r13]
    exact ⟨trivial, rfl, fun r h₁ h₂ => by simp [h₁, h₂], trivial⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨rdi₁, rsi₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have hsp₁ : s₁.gpr .rsp = s₀.gpr .rsp := by rw [k₁ _ (by decide) (by decide), h.keep .rsp (by simp)]
  have hwr₁ : s₁.wr = [stR s₀, dR s₀, scR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have hb8 : below (s₁.gpr .rsp) 8 = below (s₀.gpr .rsp) 8 := by rw [hsp₁]
  have b8S := below8_stk s₀
  -- The state, the scratch, the data and the stack are apart.
  have ts : ∀ R R', Region.Sub R (stR s₀) → Region.Sub R' (scR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_sc.sub_left h₁).sub_right h₂
  have dS : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have dC : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (scR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.d_sc.sub_left h₁).sub_right h₂
  refine WP.seq (block_call rdi₁ rsi₁ (ts _ _ (stS s₀) (bufR_sub s₀)).symm
    (by rw [hb8]; exact (hp.stk_sc.sub_left b8S).sub_right (bufR_sub s₀))
    (by rw [hb8]; exact (hp.stk_st.sub_left b8S).sub_right (stS s₀))
    (by
      rw [hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 136 by decide⟩
      · exact ⟨scR s₀, by simp, 64, rfl, show 64 + 256 ≤ 512 by decide⟩)
    (by
      rw [hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scR s₀, by simp, 64, rfl, show 64 + 256 ≤ 512 by decide⟩) fun s₂ rd₂ wr₂ cs₂ f₂ rsi₂ blk₂ => ?_)
  rw [hb8] at f₂
  have g : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₂.gpr r = s.gpr r := fun r hr => by
    rw [cs₂ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact k₁ r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  have hwr₂ : s₂.wr = [stR s₀, dR s₀, scR s₀] := by rw [wr₂, hwr₁]
  have hrd₂ : s₂.rd = [] := by rw [rd₂, hrd₁]
  have hb64 : (⟨st s₀ + BitVec.ofNat 64 64, 64⟩ : Region).Disjoint ⟨sc s₀ + BitVec.ofNat 64 64, 64⟩ :=
    ts _ _ (Offset.sub_base _ (by omega_arith)) (Offset.sub_base _ (by omega_arith))
  refine WP.seq (WP.mono (copyBlock_exec (p := st s₀) (q := sc s₀) (by rw [g .rbx (by simp), h.rbx]) (by rw [g .r13 (by simp), h.r13])
    (fun d hd => by rw [hwr₂]; rw [← hp.wr]; exact hp.w_st hd)
    (fun d hd => by rw [hrd₂, hwr₂, List.nil_append, ← hp.wr]; exact hp.w_sc hd))
    fun s₃ ⟨mc₃, kc₃, rdc₃, wrc₃⟩ => ?_)
  have fc : Frame [⟨st s₀ + BitVec.ofNat 64 64, 64⟩] s₂.mem s₃.mem := by
    rw [mc₃]; exact copyBlk_frame _ _ _ (by decide)
  have g₃ : ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₃.gpr r = s.gpr r := fun r hr => by
    rw [kc₃ r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact g r hr
  have hw48 : InRegions s₃.wr (off (st s₀) 48) 4 := by
    rw [wrc₃, hwr₂]; exact ⟨stR s₀, by simp, contains_off (by omega_arith) (by omega_arith)⟩
  have hr48 : InRegions (s₃.rd ++ s₃.wr) (off (st s₀) 48) 4 := by
    rw [rdc₃, hrd₂, List.nil_append]; exact hw48
  refine WP.seq (WP.mono (ctr_exec (by rw [g₃ .rbx (by simp), h.rbx]) hw48 hr48)
    fun s₄ ⟨m₄, rsi₄, rdx₄, k₄, rd₄, wr₄⟩ => ?_)
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hrbp₄ : s₄.gpr .rbp = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀) := by
    rw [k₄ .rbp (by decide) (by decide) (by decide), g₃ .rbp (by simp), h.rbp]
  have hb : BPre s₄ (dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)) (st s₀ + BitVec.ofNat 64 64) (T s₀) :=
    ⟨hrbp₄, rsi₄, by rw [rdx₄, g₃ .r12 (by simp), h.r12], by omega_arith,
      by
        rw [wr₄, wrc₃, hwr₂]
        exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
      by
        rw [rd₄, wr₄, rdc₃, wrc₃, hrd₂, hwr₂, List.nil_append]
        exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega_arith) (by omega_arith)⟩,
      dS _ _ (Offset.sub_base _ (by omega_arith)) (Offset.sub_base _ (by omega_arith))⟩
  refine WP.mono (xorBytes_ok hb) fun s₅ h₅ => ?_
  have f₄ : Frame [⟨off (st s₀) 48, 4⟩] s₃.mem s₄.mem := by
    rw [m₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩ (dR s₀) := Offset.sub_base _ (by omega_arith)
  have c48 : Region.Sub ⟨off (st s₀) 48, 4⟩ (stR s₀) := by rw [off_eq]; exact Offset.sub_base _ (by omega_arith)
  have b64S : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega_arith)
  have st₃ : stateAt s₃.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame fc (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)),
      Proof.ChaCha20.X86_64.Xor.stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ts _ _ (stS s₀) (bufR_sub s₀)
        · exact (hp.stk_st.sub_left b8S).symm.sub_left (stS s₀)),
      m₁, h.state]
  have bb : ∀ i < 64, s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
      (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0 := by
    intro i hi
    rw [mc₃, copyBlk_bytes _ _ _ hb64 hi, ← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b4 : ∀ i < 64, s₄.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₄]; exact byte_writeW_off _ _ _ (show 32 / 8 ≤ 8 by decide) (by omega_arith) (by omega_arith) (by omega_arith)
  have b5 : ∀ i < 64, s₅.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₄.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₅.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR b64S).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  have k₅ : ∀ r ∈ [Reg.rbx, .r13, .r14, .r15, .rsp], s₅.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [h₅.keep r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
      k₄ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide), g₃ r (by rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)]
  refine ⟨by rw [k₅ .rbx (by simp), h.rbx], by rw [k₅ .r13 (by simp), h.r13], fun r hr => ?_,
    by rw [h₅.rd, rd₄, rdc₃, rd₂, rd₁, h.rd], by rw [h₅.wr, wr₄, wrc₃, wr₂, wr₁, h.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [k₅ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)]
    exact h.keep r hr
  · have e12 : s₃.mem.readW (off (st s₀) 48) 32 = (ctr (S0 s₀) (NB s₀))[12] := by
      rw [← st₃]; simp [stateAt, off_eq]
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame h₅.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR (stS s₀)).symm),
      m₄, Proof.ChaCha20.X86_64.Xor.stateAt_writeW_counter, st₃, e12, ctr_succ, ite_neg ht]
  · rw [b5 i hi, b4 i hi, bb i hi, ite_neg ht]
  · have svS := savR_sub s₀
    rw [m₁] at f₂
    refine (((h.saved.frame f₂ fun r hr => ?_).frame fc fun r hr => ?_).frame f₄ fun r hr => ?_).frame
      h₅.frame fun r hr => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp only [savR, off_eq]; exact Offset.disjoint _ (by omega_arith) (by omega_arith) (by omega_arith)
      · exact (hp.stk_sc.sub_left b8S).symm.sub_left svS
    · simp only [List.mem_singleton] at hr; subst hr
      exact (ts _ _ b64S svS).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (ts _ _ c48 svS).symm
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dC _ _ tR svS).symm
  · have back : s₄.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₄.bytes (R := dR s₀) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact dS _ _ (fun _ h => h) c48)
          (show L s₀ ≤ 2 ^ 64 by omega_arith) hk,
        fc.bytes (R := dR s₀) (fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact dS _ _ (fun _ h => h) b64S)
          (show L s₀ ≤ 2 ^ 64 by omega_arith) hk,
        f₂.bytes (R := dR s₀) (fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact dC _ _ (fun _ h => h) (bufR_sub s₀)
          · exact (hp.stk_d.sub_left b8S).symm) (show L s₀ ≤ 2 ^ 64 by omega_arith) hk, m₁]
    by_cases hk₁ : k < H s₀ + 64 * NB s₀
    · rw [h₅.frame.bytes (R := ⟨dp s₀, H s₀ + 64 * NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)) (show H s₀ + 64 * NB s₀ ≤ 2 ^ 64 by omega_arith) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₅.data (k - (H s₀ + 64 * NB s₀)) (by omega_arith)
      rw [Offset.add_add, Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega_arith,
        back, b4 _ (by omega_arith), bb _ (by omega_arith), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [KS, ite_neg (show ¬ k < H s₀ by omega_arith)]
      rw [show (k - H s₀) / 64 = NB s₀ by omega_arith, show (k - H s₀) % 64 = k - (H s₀ + 64 * NB s₀) by omega_arith]
  · rw [m₁] at f₂
    refine (((h.frame.trans (f₂.sub fun r hr => ?_)).trans (fc.sub fun r hr => ?_)).trans
      (f₄.sub fun r hr => ?_)).trans (h₅.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scwR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stkR s₀, by simp, b8S⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, b64S⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, tR⟩


theorem part3_eq : part3 = .seq (.block [.alu .test .r12 (.reg .r12)])
    (.ite .e (.block []) (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.X86_64.block)
      (.seq (.block copyBlock) tailXor)))) := rfl

set_option simprocs false in
theorem part3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) : WP isa part3 s (Q3 s₀) := by
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have h₁ : WP isa (.block [.alu .test .r12 (.reg .r12)]) s fun s₁ =>
      Q2 s₀ s₁ ∧ s₁.zf = some (decide (T s₀ = 0)) := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq,
      exists_eq_left']
    refine ⟨⟨h.rbx, h.rbp, h.r12, h.r13, h.keep, h.rd, h.wr, h.state, h.buf, h.saved, h.done, h.frame⟩, ?_⟩
    rw [BitVec.and_self, h.r12, ← Offset.ofNat_sub_ofNat_beq (x := T s₀) (y := 0) (by omega_arith) (by omega_arith)]
    simp
  rw [part3_eq]
  refine WP.seq (WP.mono h₁ fun s₁ ⟨h₁, hz⟩ => ?_)
  refine WP.ite (decide (T s₀ = 0)) (by simp [eval, hz])
    (fun h0 => WP.block_nil (M := isa) (t_zero_ok h₁ (by simpa using h0)))
    (fun h0 => tail_ok hp h₁ (by simpa using h0))

/-! ## The end -/

/-- What `apply` guarantees (`applyX86_64`), the registers it keeps, and
the scratch past `scwR` kept. -/
def Final (s₀ s : State) : Prop :=
  gprPreserved s₀ s ∧ Proof.ChaCha20.applyX86_64.post s₀ s ∧
    ∀ i, 424 ≤ i → i < 512 → s.mem (sc s₀ + BitVec.ofNat 64 i) = s₀.mem (sc s₀ + BitVec.ofNat 64 i)

theorem retR_stkR (s₀ : State) : (retR s₀).Disjoint (stkR s₀) :=
  Offset.base_disjoint_below (s₀.gpr .rsp) (n := 24) (k := 8) (by decide)

set_option simprocs false in
theorem finish_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q3 s₀ s) :
    WP isa (.block finish) s (Final s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have o128 : InRegions s.wr (off (st s₀) 128) 8 := by rw [h.wr]; exact hp.w_st (by decide)
  have r : ∀ d, d + 8 ≤ 512 → InRegions (s.rd ++ s.wr) (off (sc s₀) d) 8 := fun d hd => by
    rw [h.rd, h.wr]; exact hp.r_sc hd
  have i416 := r 416 (by decide); have i384 := r 384 (by decide); have i392 := r 392 (by decide)
  have i400 := r 400 (by decide); have i408 := r 408 (by decide)
  simp only [off] at o128 i416 i384 i392 i400 i408
  have hfw : Frame [⟨off (st s₀) 128, 8⟩] s.mem (s.mem.writeW (off (st s₀) 128) (BitVec.ofNat 64 (N s₀ - L s₀))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have c128 : Region.Sub ⟨off (st s₀) 128, 8⟩ (stR s₀) := by rw [off_eq]; exact Offset.sub_base _ (by omega_arith)
  have sv : ∀ d, 384 ≤ d → d + 8 ≤ 424 →
      (s.mem.writeW (off (st s₀) 128) (BitVec.ofNat 64 (N s₀ - L s₀))).readW (off (sc s₀) d) 64 =
        s.mem.readW (off (sc s₀) d) 64 := fun d h₁ h₂ =>
    hfw.readW (r := savR s₀) (by simp only [savR, off_eq]; exact Offset.contains _ h₁ (by omega_arith) (by omega_arith))
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((hp.st_sc.sub_left c128).sub_right (savR_sub s₀)).symm) (by decide)
  have hl : s.mem.readW (off (sc s₀) 416) 64 = BitVec.ofNat 64 (N s₀ - L s₀) := h.saved.left
  simp only [off] at hl sv
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finish, runBlock_cons, runStep_some, runBlock_nil, exec, ea_at,
    readSrc, readSrc32, State.load64, State.store64, State.setReg, State.setReg32, Option.map_some,
    Option.some.injEq, exists_eq_left', ite_true, ite_false, h.rbx, h.r13, o128, i416, i384, i392,
    i400, i408]
  rw [hl]
  have hF : Frame [stR s₀, dR s₀, scwR s₀, stkR s₀] s₀.mem
      (s.mem.writeW (off (st s₀) 128) (BitVec.ofNat 64 (N s₀ - L s₀))) :=
    h.frame.trans (hfw.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c128⟩)
  have hS : stateAt (s.mem.writeW (off (st s₀) 128) (BitVec.ofNat 64 (N s₀ - L s₀))) (st s₀) =
      ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1) := by
    rw [Proof.ChaCha20.X86_64.Xor.stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [off_eq]
      exact Offset.base_disjoint _ (by omega_arith) (by omega_arith)), h.state]
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_, fun i h₁ h₂ => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp (config := {decide := true}) only [ite_true, ite_false]
      rw [sv 384 (by decide) (by decide)]; exact h.saved.rbx
    · simp (config := {decide := true}) only [ite_true, ite_false]
      rw [sv 392 (by decide) (by decide)]; exact h.saved.rbp
    · simp (config := {decide := true}) only [ite_false]; exact h.keep .rsp (by simp)
    · simp (config := {decide := true}) only [ite_true, ite_false]
      rw [sv 400 (by decide) (by decide)]; exact h.saved.r12
    · simp (config := {decide := true}) only [ite_true, ite_false]
      rw [sv 408 (by decide) (by decide)]; exact h.saved.r13
    · simp (config := {decide := true}) only [ite_false]; exact h.keep .r14 (by simp)
    · simp (config := {decide := true}) only [ite_false]; exact h.keep .r15 (by simp)
  · dsimp only
    exact hF.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_d
      · exact hp.ret_sc.sub_right (scwR_sub s₀)
      · exact retR_stkR s₀) (by decide)
  · have hd : ∀ k < L s₀, (s.mem.writeW (off (st s₀) 128) (BitVec.ofNat 64 (N s₀ - L s₀)))
        (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := fun k hk =>
      hfw.bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show L s₀ ≤ 2 ^ 64 by omega_arith) hk
    show keyAt _ _ = _ ∧ _
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by simp (config := {decide := true}), apply_data hle fun k hk => ?_,
      apply_rest hle ?_ hS fun i hi => ?_⟩
    · dsimp only
      rw [hd k hk, h.done k hk, ite_pos hk]
    · dsimp only
      simp only [leftAt]
      rw [show (st s₀ + 128 : Addr) = off (st s₀) 128 by rw [off_eq]; rfl, Mem.readW_writeW_self64,
        toNat_ofNat_lt (by omega_arith)]
    · dsimp only
      rw [byte_writeW_off _ _ _ (show 64 / 8 ≤ 8 by decide) (by omega_arith) (by omega_arith) (by omega_arith), h.buf i hi]
  · dsimp only
    have := hF.bytes (R := ⟨sc s₀ + BitVec.ofNat 64 424, 88⟩) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact hp.st_sc.symm.sub_left (Offset.sub_base _ (by omega_arith))
      · exact hp.d_sc.symm.sub_left (Offset.sub_base _ (by omega_arith))
      · exact Offset.disjoint_base _ (by omega_arith) (by omega_arith)
      · exact hp.stk_sc.symm.sub_left (Offset.sub_base _ (by omega_arith)))
      (show 88 ≤ 2 ^ 64 by decide) (i := i - 424) (show i - 424 < 88 by omega_arith)
    rwa [Offset.add_add, show 424 + (i - 424) = i by omega_arith] at this

set_option simprocs false in
theorem fail_ok {s₀ : State} (hlt : N s₀ < L s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block [.mov32 .rax (.imm 0)]) s (Final s₀) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg, State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, by dsimp only; rw [h.mem]⟩, ?_, fun i _ _ => by dsimp only; rw [h.mem]⟩
  · have : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [this, ite_false]; exact h.keep r this
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ L s₀ ≤ N s₀ by omega_arith)]
    dsimp only
    rw [h.mem]
    exact ⟨rfl, by simp, rfl, rfl⟩

theorem apply_eq (x : Impl.ChaCha20.X86_64.Callee) : apply x = .seq (.block check)
    (.ite .b (.block [.mov32 .rax (.imm 0)]) (.seq part1 (.seq (part2 x) (.seq part3 (.block finish))))) := rfl

theorem apply_correct (v : Proof.ChaCha20.X86_64.XorImpl) {s₀ : State} (hp : APre s₀) :
    WP isa (apply v.callee) s₀ (Final s₀) := by
  rw [apply_eq]
  refine WP.seq (WP.mono (check_ok hp) fun s h => ?_)
  refine WP.ite (decide (N s₀ < L s₀)) (by simp [eval, h.cf]) (fun hlt => fail_ok (by simpa using hlt) h)
    (fun hge => ?_)
  have hle : L s₀ ≤ N s₀ := by simp at hge; omega_arith
  exact WP.seq (WP.mono (part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (part2_ok v hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (part3_ok hp h₂) fun s₃ h₃ => finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.X86_64.Stream
