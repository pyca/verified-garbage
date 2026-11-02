module

public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Calls
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import all Init.Data.Nat.Bitwise.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Block
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.RISCV64.ByteLoad
public import VerifiedGarbage.Proof.Framework.RISCV64.Bytes
public import VerifiedGarbage.Proof.Framework.RISCV64.Align
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Xor
import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Init
public import VerifiedGarbage.Impl.ChaCha20.RISCV64.Stream
public import VerifiedGarbage.Proof.ChaCha20.RISCV64.Stream.Bytes
public import VerifiedGarbage.Proof.ChaCha20.Stream

/-!
# Streaming ChaCha20 on RISC-V: `apply`, correctness

Untrusted: everything here is checked by Lean. The pieces of `apply`
(`Impl/ChaCha20/RISCV64/Stream.lean`), each from what holds before it
(`Q0` … `Q3`), and the whole function, as on PPC64LE
(`Proof/ChaCha20/PPC64LE/Stream/Apply.lean`). The pieces are those that the
proof of constant time (`ApplyCT.lean`) relates in two runs.
-/

@[expose] public section

namespace VG.Proof.ChaCha20

open VG.RISCV64
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt)

/-- RISC-V contract for `vg_chacha20_apply(state = a0, data = a1, len = a2) -> a0`.
The return address is in `ra`, which the code saves in the state, so no
stack is used. -/
def applyRISCV64 : Contract RISCV64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .a0, 768⟩
    let data : Region := ⟨s.gpr .a1, (s.gpr .a2).toNat⟩
    s.rd = [] ∧ s.wr = [state, data] ∧ state.Disjoint data ∧
    (s.gpr .a0).toNat + 768 ≤ 2 ^ 64 ∧ (s.gpr .a1).toNat + (s.gpr .a2).toNat ≤ 2 ^ 64 ∧
    (s.gpr .a0).toNat % 8 = 0
  post s s' :=
    keyAt s'.mem (s.gpr .a0) = keyAt s.mem (s.gpr .a0) ∧
      if (s.gpr .a2).toNat ≤ leftAt s.mem (s.gpr .a0) then
        (s'.gpr .a0).setWidth 32 = 1 ∧
          bytesAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat =
            List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat)
              ((restAt s.mem (s.gpr .a0)).take (s.gpr .a2).toNat) ∧
          restAt s'.mem (s.gpr .a0) = (restAt s.mem (s.gpr .a0)).drop (s.gpr .a2).toNat
      else
        (s'.gpr .a0).setWidth 32 = 0 ∧
          bytesAt s'.mem (s.gpr .a1) (s.gpr .a2).toNat = bytesAt s.mem (s.gpr .a1) (s.gpr .a2).toNat ∧
          restAt s'.mem (s.gpr .a0) = restAt s.mem (s.gpr .a0)
  pub s₁ s₂ :=
    s₁.gpr .a0 = s₂.gpr .a0 ∧ s₁.gpr .a1 = s₂.gpr .a1 ∧ s₁.gpr .a2 = s₂.gpr .a2 ∧
      s₁.sp = s₂.sp ∧ [leftAt s₁.mem (s₁.gpr .a0)] = [leftAt s₂.mem (s₂.gpr .a0)]

end VG.Proof.ChaCha20

namespace VG.Proof.ChaCha20.RISCV64.Stream

open VG VG.RISCV64 VG.RISCV64.Steps VG.RISCV64.Align VG.RISCV64.Bytes VG.RISCV64.ByteLoad
  VG.Impl.ChaCha20.RISCV64.Stream VG.Impl.Words.RISCV64
open VG.Impl.ChaCha20.RISCV64.Xor (mov)
open VG.Spec.ChaCha20 (keyAt restAt leftAt bytesAt stateAt serialize block)
open VG.Proof.ChaCha20.RISCV64.Xor (sub_ofNat add_ofNat stateAt_frame stateAt_writeW_counter
  inc_setWidth)

/-! ## Instructions -/

/-- `sltu`'s result. -/
theorem sltu_eq (a b : BitVec 64) :
    (if a < b then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (decide (a.toNat < b.toNat)).toNat := by
  by_cases h : a.toNat < b.toNat
  · rw [ite_pos (BitVec.lt_def.mpr h)]; simp [h]
  · rw [ite_neg (fun h' => h (BitVec.lt_def.mp h'))]; simp [h]

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

/-- `s'` is `s` but for the registers `ws`. -/
structure Rest (ws : List Reg) (s s' : State) : Prop where
  other : ∀ r, r ∉ ws → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem Rest.trans {ws : List Reg} {s s' s'' : State} (h : Rest ws s s') (h' : Rest ws s' s'') : Rest ws s s'' :=
  ⟨fun r hr => (h'.other r hr).trans (h.other r hr), h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    h'.sp.trans h.sp⟩

theorem Rest.upd {ws : List Reg} {s s' : State} {d : Reg} {v : BitVec 64} (u : Upd s s' d v) (hd : d ∈ ws) :
    Rest ws s s' :=
  ⟨fun r hr => u.other r fun e => hr (e ▸ hd), u.mem, u.rd, u.wr, u.sp⟩

theorem Rest.mono {ws ws' : List Reg} {s s' : State} (h : Rest ws s s') (hs : ∀ r ∈ ws, r ∈ ws') :
    Rest ws' s s' :=
  ⟨fun r hr => h.other r fun h' => hr (hs r h'), h.mem, h.rd, h.wr, h.sp⟩

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev st : Addr := s₀.gpr .a0
abbrev dp : Addr := s₀.gpr .a1
abbrev L : Nat := (s₀.gpr .a2).toNat
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
abbrev stR : Region := ⟨st s₀, 768⟩
abbrev dR : Region := ⟨dp s₀, L s₀⟩
/-- The keystream byte XORed into byte `k` of the data. -/
abbrev KS (k : Nat) : Byte :=
  if k < H s₀ then s₀.mem (st s₀ + BitVec.ofNat 64 (128 - O s₀ + k))
  else (serialize (block (ctr (S0 s₀) ((k - H s₀) / 64)))).getD ((k - H s₀) % 64) 0
/-- The data with its first `j` bytes XORed. -/
abbrev Done (j : Nat) (m : Mem) : Prop :=
  ∀ k < L s₀, m (dp s₀ + BitVec.ofNat 64 k) = if k < j then D0 s₀ k ^^^ KS s₀ k else D0 s₀ k
/-- How far `state + 576` is below a multiple of 8. -/
abbrev q : Nat := pad (st s₀ + BitVec.ofNat 64 576)
/-- Where our caller's registers are saved: `state + 576`, rounded up. -/
abbrev sv : Addr := st s₀ + BitVec.ofNat 64 576 + BitVec.ofNat 64 (q s₀)
abbrev savR : Region := ⟨st s₀ + BitVec.ofNat 64 (576 + q s₀), 40⟩
end

theorem L_lt (s₀ : State) : L s₀ < 2 ^ 64 := (s₀.gpr .a2).isLt
theorem N_lt (s₀ : State) : N s₀ < 2 ^ 64 := (s₀.mem.readW (st s₀ + 128) 64).isLt
theorem H_le (s₀ : State) : H s₀ ≤ L s₀ := Nat.min_le_right _ _
theorem H_le_O (s₀ : State) : H s₀ ≤ O s₀ := Nat.min_le_left _ _
theorem O_lt (s₀ : State) : O s₀ < 64 := Nat.mod_lt _ (by decide)
theorem T_eq (s₀ : State) : T s₀ = L s₀ - H s₀ - 64 * NB s₀ := by
  simp only [T, NB, tailLen, blocksOf, H]; omega
theorem HNB_le (s₀ : State) : H s₀ + 64 * NB s₀ ≤ L s₀ := by
  have := H_le s₀; simp only [NB, blocksOf, H] at *; omega
theorem q_lt (s₀ : State) : q s₀ < 8 := pad_lt _

theorem sv_add (s₀ : State) (d : Nat) :
    sv s₀ + BitVec.ofNat 64 d = st s₀ + BitVec.ofNat 64 (576 + q s₀ + d) := align_add _ _ _

theorem sv_al (s₀ : State) {d : Nat} (hd : d % 8 = 0) : (sv s₀ + BitVec.ofNat 64 d).toNat % 8 = 0 :=
  align_al_add _ hd

structure APre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR s₀, dR s₀]
  st_d : (stR s₀).Disjoint (dR s₀)
  wrap_st : (st s₀).toNat + 768 ≤ 2 ^ 64
  wrap_d : (dp s₀).toNat + L s₀ ≤ 2 ^ 64
  st_al : (st s₀).toNat % 8 = 0

theorem APre.of (s₀ : State) (h : Proof.ChaCha20.applyRISCV64.pre s₀) : APre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The state plus a multiple of 4 is 4-byte aligned. -/
theorem APre.al {s₀ : State} (hp : APre s₀) {d : Nat} (hd : d % 4 = 0) :
    (st s₀ + BitVec.ofNat 64 d).toNat % 4 = 0 := by
  have := hp.st_al
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have := (st s₀).isLt
  omega

theorem APre.w_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 d) n :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., Offset.contains_base _ h (by omega)⟩

theorem APre.r_st {s₀ : State} (hp : APre s₀) {d n : Nat} (h : d + n ≤ 768) :
    InRegions (s₀.rd ++ s₀.wr) (st s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd, List.nil_append]; exact hp.w_st h

theorem sav_in (s₀ : State) {d : Nat} (hd : d + 8 ≤ 40) : (stR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) 8 := by
  have := q_lt s₀
  rw [sv_add]; exact contains_st (st s₀) (by omega)

theorem APre.w_sv {s₀ : State} (hp : APre s₀) {d : Nat} (hd : d + 8 ≤ 40) :
    InRegions s₀.wr (sv s₀ + BitVec.ofNat 64 d) 8 :=
  ⟨stR s₀, by rw [hp.wr]; exact List.mem_cons_self .., sav_in s₀ hd⟩

/-- Our caller's `s5`–`s8` and our return address. -/
structure Saved (s₀ : State) (m : Mem) : Prop where
  ra : m.readW (sv s₀ + BitVec.ofNat 64 0) 64 = s₀.gpr .ra
  s5 : m.readW (sv s₀ + BitVec.ofNat 64 8) 64 = s₀.gpr .s5
  s6 : m.readW (sv s₀ + BitVec.ofNat 64 16) 64 = s₀.gpr .s6
  s7 : m.readW (sv s₀ + BitVec.ofNat 64 24) 64 = s₀.gpr .s7
  s8 : m.readW (sv s₀ + BitVec.ofNat 64 32) 64 = s₀.gpr .s8

theorem savR_sub (s₀ : State) : Region.Sub (savR s₀) (stR s₀) :=
  Offset.sub_base _ (by have := q_lt s₀; omega)

theorem sav_contains (s₀ : State) {d : Nat} (hd : d + 8 ≤ 40) :
    (savR s₀).Contains (sv s₀ + BitVec.ofNat 64 d) (64 / 8) := by
  have := q_lt s₀
  rw [sv_add]; exact Offset.contains _ (by omega) (by omega) (by omega)

theorem Saved.frame {s₀ : State} {rs : List Region} {m m' : Mem} (h : Saved s₀ m) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, (savR s₀).Disjoint r) : Saved s₀ m' :=
  ⟨by rw [hf.readW (sav_contains s₀ (by decide)) hd (by decide), h.ra],
    by rw [hf.readW (sav_contains s₀ (by decide)) hd (by decide), h.s5],
    by rw [hf.readW (sav_contains s₀ (by decide)) hd (by decide), h.s6],
    by rw [hf.readW (sav_contains s₀ (by decide)) hd (by decide), h.s7],
    by rw [hf.readW (sav_contains s₀ (by decide)) hd (by decide), h.s8]⟩

/-- The saved registers are apart from any region of the state below 576. -/
theorem savR_disjoint (s₀ : State) {e k : Nat} (h : e + k ≤ 576) :
    (savR s₀).Disjoint ⟨st s₀ + BitVec.ofNat 64 e, k⟩ :=
  Offset.disjoint _ (by omega) (by have := q_lt s₀; omega) (by omega)

/-! ## The check -/

/-- The registers the check writes. -/
abbrev chk : List Reg := [.t1, .t2, .t3, .t4, .t5]

/-- After the check. -/
structure Q0 (s₀ s : State) : Prop where
  t1 : s.gpr .t1 = BitVec.ofNat 64 (N s₀)
  t3 : s.gpr .t3 = BitVec.ofNat 64 (O s₀)
  t4 : s.gpr .t4 = BitVec.ofNat 64 (decide (N s₀ < L s₀)).toNat
  t5 : s.gpr .t5 = BitVec.ofNat 64 (decide (O s₀ < L s₀)).toNat
  rest : Rest chk s₀ s

theorem check_ok {s₀ : State} (hp : APre s₀) : WP isa (.block check) s₀ (Q0 s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have hO := O_lt s₀
  unfold check
  rw [WP.block_append_iff]
  refine WP.mono (loadLE64_ok (d := .t1) (tmp := .t2) (hi := .t3) (n := .a0) (off := 128) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (hp.r_st (d := 128) (n := 4) (by decide)) (hp.r_st (d := 132) (n := 4) (by decide)))
    fun s₁ ⟨t1₁, g₁, m₁, rd₁, wr₁, sp₁⟩ => ?_
  have n1 : s₁.gpr .t1 = BitVec.ofNat 64 (N s₀) := by
    rw [t1₁]; simp [N, leftAt]
  refine wp_andi63 fun s₂ u₂ => wp_sltu fun s₃ u₃ => wp_sltu fun s₄ u₄ => WP.block_nil ?_
  have l1 : s₁.gpr .a2 = BitVec.ofNat 64 (L s₀) := by
    rw [g₁ _ (by decide) (by decide) (by decide)]; simp [L]
  have o2 : s₂.gpr .t3 = BitVec.ofNat 64 (O s₀) := by rw [u₂.gpr, n1, toNat_ofNat_lt hN]
  refine ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), n1],
    by rw [u₄.other _ (by decide), u₃.other _ (by decide), o2],
    by rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₂.other _ (by decide), n1, l1, sltu_eq,
      toNat_ofNat_lt hN, toNat_ofNat_lt hL],
    by rw [u₄.gpr, u₃.other _ (by decide), u₃.other _ (by decide), o2, u₂.other _ (by decide), l1, sltu_eq,
      toNat_ofNat_lt (by omega), toNat_ofNat_lt hL], ?_⟩
  exact (((⟨fun r hr => by
      simp only [chk, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact g₁ r hr.1 hr.2.1 hr.2.2.1, m₁, rd₁, wr₁, sp₁⟩ : Rest chk s₀ s₁).trans
    (Rest.upd u₂ (by simp))).trans (Rest.upd u₃ (by simp))).trans (Rest.upd u₄ (by simp))

/-- The callee-saved registers our code never writes. -/
def kept : List Reg := [.s0, .s1, .s2, .s3, .s4, .s9, .s10, .s11]

theorem kept_ne {r : Reg} (hr : r ∈ kept) {r' : Reg} (h : r' ∉ kept := by decide) : r ≠ r' :=
  fun e => h (e ▸ hr)

/-- What `apply` guarantees (`applyRISCV64`), and the registers it keeps. -/
def Final (s₀ s : State) : Prop :=
  (∀ r ∈ preserved, s.gpr r = s₀.gpr r) ∧ s.gpr .ra = s₀.gpr .ra ∧ Proof.ChaCha20.applyRISCV64.post s₀ s

theorem fail_ok {s₀ : State} (hlt : N s₀ < L s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block [.li .a0 0]) s (Final s₀) := by
  refine wp_li (imm := 0) (by decide) fun s₁ u₁ => WP.block_nil ?_
  refine ⟨fun r hr => ?_, by rw [u₁.other _ (by decide), h.rest.other _ (by decide)], ?_⟩
  · have : r ≠ .a0 ∧ r ∉ chk := by revert r hr; decide
    rw [u₁.other _ this.1, h.rest.other _ this.2]
  · show keyAt _ _ = _ ∧ _
    rw [ite_neg (show ¬ L s₀ ≤ N s₀ by omega)]
    rw [u₁.mem, h.rest.mem]
    exact ⟨rfl, by rw [u₁.gpr]; decide, rfl, rfl⟩


/-! ## The bytes left in the buffered block -/

/-- The state of memory before the data is touched. -/
structure Mid (s₀ : State) (m : Mem) : Prop where
  keep : ∀ i < 136, m (st s₀ + BitVec.ofNat 64 i) = s₀.mem (st s₀ + BitVec.ofNat 64 i)
  saved : Saved s₀ m

theorem Mid.state {s₀ : State} {m : Mem} (h : Mid s₀ m) : stateAt m (st s₀) = S0 s₀ :=
  stateAt_congr fun i hi => h.keep i (by omega)

/-- After `start`, with `x` in `a2`. -/
structure R1 (s₀ : State) (x : Nat) (s : State) : Prop where
  s5 : s.gpr .s5 = st s₀
  s6 : s.gpr .s6 = dp s₀
  s7 : s.gpr .s7 = BitVec.ofNat 64 (L s₀)
  s8 : s.gpr .s8 = BitVec.ofNat 64 (N s₀ - L s₀)
  a2 : s.gpr .a2 = BitVec.ofNat 64 x
  t3 : s.gpr .t3 = BitVec.ofNat 64 (O s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ 0 s.mem
  frame : Frame [stR s₀] s₀.mem s.mem

theorem kept_chk : ∀ r ∈ kept, r ∉ chk := by decide

/-- The memory after `start`. -/
def startMem (s₀ : State) : Mem :=
  ((((s₀.mem.writeW (sv s₀ + BitVec.ofNat 64 0) (s₀.gpr .ra)).writeW (sv s₀ + BitVec.ofNat 64 8)
    (s₀.gpr .s5)).writeW (sv s₀ + BitVec.ofNat 64 16) (s₀.gpr .s6)).writeW (sv s₀ + BitVec.ofNat 64 24)
    (s₀.gpr .s7)).writeW (sv s₀ + BitVec.ofNat 64 32) (s₀.gpr .s8)

theorem startMem_frame (s₀ : State) : Frame [stR s₀] s₀.mem (startMem s₀) := by
  simp only [startMem]
  exact (((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (sav_in s₀ (d := 0) (by decide))).writeW
    (List.mem_singleton_self _) _ (sav_in s₀ (d := 8) (by decide))).writeW (List.mem_singleton_self _) _
    (sav_in s₀ (d := 16) (by decide))).writeW (List.mem_singleton_self _) _
    (sav_in s₀ (d := 24) (by decide))).writeW (List.mem_singleton_self _) _
    (sav_in s₀ (d := 32) (by decide))

/-- A byte of the state below 576, after a doubleword written at `sv`. -/
theorem byte_writeW_sv (s₀ : State) (m : Mem) (v : BitVec 64) {d i : Nat} (hd : d + 8 ≤ 40) (hi : i < 576) :
    (m.writeW (sv s₀ + BitVec.ofNat 64 d) v) (st s₀ + BitVec.ofNat 64 i) = m (st s₀ + BitVec.ofNat 64 i) := by
  have := q_lt s₀
  rw [sv_add]
  exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)

theorem startMem_mid (s₀ : State) : Mid s₀ (startMem s₀) := by
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [startMem]
    rw [byte_writeW_sv _ _ _ (by decide) (by omega), byte_writeW_sv _ _ _ (by decide) (by omega),
      byte_writeW_sv _ _ _ (by decide) (by omega), byte_writeW_sv _ _ _ (by decide) (by omega),
      byte_writeW_sv _ _ _ (by decide) (by omega)]
  all_goals simp only [startMem, Mem.readW_writeW_self64, readW_writeW_ofNat, Nat.reduceAdd,
    Nat.reduceDiv, Nat.reducePow, Nat.reduceLeDiff, Nat.reduceLT, true_or]

theorem savePtr_ok {s : State} (n : Reg) :
    WP isa (.block (savePtr n)) s (· = s.write .t0
      (s.gpr n + BitVec.ofNat 64 576 + BitVec.ofNat 64 (pad (s.gpr n + BitVec.ofNat 64 576)))) := by
  apply WP.of_runBlock
  simp only [savePtr, runBlock_cons, runStep_some, runBlock_nil, exec_addi (show imm12 583 by decide),
    exec_logicImm (show imm12 (-8) by decide), RegUpd.gpr_write_self, RegUpd.write_write,
    Option.some.injEq, exists_eq_left']
  rw [align_off_eq _ (off := 576) (by decide) (by decide)]

theorem start_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa (.block start) s fun s' => R1 s₀ (L s₀) s' ∧ s'.gpr .t5 = s.gpr .t5 := by
  have hw : ∀ d, d + 8 ≤ 40 → InRegions s.wr (sv s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [h.rest.wr]; exact hp.w_sv hd
  have g : ∀ r, r ∉ chk → s.gpr r = s₀.gpr r := h.rest.other
  have a0 : s.gpr .a0 = st s₀ := g _ (by decide)
  unfold start
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .a0) fun s₁ e₁ => ?_
  have u₁ : Upd s s₁ .t0 (sv s₀) := by
    rw [e₁, show sv s₀ = s.gpr .a0 + BitVec.ofNat 64 576 +
      BitVec.ofNat 64 (pad (s.gpr .a0 + BitVec.ofNat 64 576)) by rw [a0]]
    exact Upd.write _ _ _
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 0) (by decide) (by rw [u₁.gpr]) (sv_al _ (by decide))
    (by rw [u₁.wr]; exact hw 0 (by decide)) fun s₂ g₂ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 8) (by decide) (by rw [g₂.gpr, u₁.gpr]) (sv_al _ (by decide))
    (by rw [g₂.wr, u₁.wr]; exact hw 8 (by decide)) fun s₃ g₃ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 16) (by decide) (by rw [g₃.gpr, g₂.gpr, u₁.gpr])
    (sv_al _ (by decide)) (by rw [g₃.wr, g₂.wr, u₁.wr]; exact hw 16 (by decide)) fun s₄ g₄ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 24) (by decide) (by rw [g₄.gpr, g₃.gpr, g₂.gpr, u₁.gpr])
    (sv_al _ (by decide)) (by rw [g₄.wr, g₃.wr, g₂.wr, u₁.wr]; exact hw 24 (by decide)) fun s₅ g₅ => ?_
  refine wp_sd (a := sv s₀ + BitVec.ofNat 64 32) (by decide)
    (by rw [g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, u₁.gpr]) (sv_al _ (by decide))
    (by rw [g₅.wr, g₄.wr, g₃.wr, g₂.wr, u₁.wr]; exact hw 32 (by decide)) fun s₆ g₆ => ?_
  refine wp_mv fun s₇ u₇ => wp_mv fun s₈ u₈ => wp_mv fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ => WP.block_nil ?_
  -- The registers before the moves are those of `s` but for `t0`.
  have g₆' : ∀ r, r ≠ .t0 → s₆.gpr r = s.gpr r := fun r hr => by
    rw [g₆.gpr, g₅.gpr, g₄.gpr, g₃.gpr, g₂.gpr, u₁.other r hr]
  have g₉ : ∀ r, r ≠ .t0 → r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → s₉.gpr r = s.gpr r :=
    fun r h0 h5 h6 h7 => by rw [u₉.other r h7, u₈.other r h6, u₇.other r h5, g₆' r h0]
  have hL2 : s.gpr .a2 = BitVec.ofNat 64 (L s₀) := by rw [g _ (by decide)]; simp [L]
  have hs : ∀ r, r ∉ chk → r ≠ .t0 → s₁.gpr r = s₀.gpr r := fun r h₁ h₂ => by rw [u₁.other r h₂, g r h₁]
  have hm : s₁₀.mem = startMem s₀ := by
    simp only [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, g₆.mem, g₅.mem, g₄.mem, g₃.mem, g₂.mem, g₅.gpr, g₄.gpr,
      g₃.gpr, g₂.gpr, u₁.mem, hs .ra (by decide) (by decide), hs .s5 (by decide) (by decide),
      hs .s6 (by decide) (by decide), hs .s7 (by decide) (by decide), hs .s8 (by decide) (by decide),
      h.rest.mem]
    rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, by rw [hm]; exact startMem_mid s₀, fun k hk => ?_,
    by rw [hm]; exact startMem_frame s₀⟩, ?_⟩
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, g₆' _ (by decide), a0]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), g₆' _ (by decide),
      g _ (by decide)]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), g₆' _ (by decide), hL2]
  · rw [u₁₀.gpr, g₉ _ (by decide) (by decide) (by decide) (by decide),
      g₉ _ (by decide) (by decide) (by decide) (by decide), h.t1, hL2, sub_ofNat hle]
  · rw [u₁₀.other _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide), hL2]
  · rw [u₁₀.other _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide), h.t3]
  · rw [u₁₀.other r (kept_ne hr), g₉ r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr)]
    exact g r (kept_chk r hr)
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, g₆.rd, g₅.rd, g₄.rd, g₃.rd, g₂.rd, u₁.rd, h.rest.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, g₆.wr, g₅.wr, g₄.wr, g₃.wr, g₂.wr, u₁.wr, h.rest.wr]
  · rw [hm, (startMem_frame s₀).bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_d.symm)
      (show L s₀ ≤ 2 ^ 64 by have := L_lt s₀; omega) hk, ite_neg (Nat.not_lt_zero _)]
  · rw [u₁₀.other _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide)]

theorem sel_ok {s₀ : State} {s : State} (h : R1 s₀ (L s₀) s)
    (hc : s.gpr .t5 = BitVec.ofNat 64 (decide (O s₀ < L s₀)).toNat) :
    WP isa (.ite (.nonzero .t5) (.block [mov .a2 .t3]) (.block [])) s (R1 s₀ (H s₀)) := by
  refine WP.ite (decide (O s₀ < L s₀)) (by
      rw [eval_nonzero_ofNat s .t5 (by cases decide (O s₀ < L s₀) <;> decide) hc]
      by_cases hh : O s₀ < L s₀ <;> simp [hh]) (fun hlt => ?_) (fun hge => ?_)
  · simp only [decide_eq_true_eq] at hlt
    refine wp_mv fun s' u => WP.block_nil ?_
    exact ⟨by rw [u.other _ (by decide), h.s5], by rw [u.other _ (by decide), h.s6],
      by rw [u.other _ (by decide), h.s7], by rw [u.other _ (by decide), h.s8],
      by rw [u.gpr, h.t3, H, headLen, bufLeft, Nat.min_eq_left (Nat.le_of_lt hlt)],
      by rw [u.other _ (by decide), h.t3],
      fun r hr => by rw [u.other r (kept_ne hr)]; exact h.keep r hr,
      by rw [u.rd, h.rd], by rw [u.wr, h.wr], u.mem ▸ h.mid, u.mem ▸ h.done, u.mem ▸ h.frame⟩
  · simp only [decide_eq_false_iff_not, Nat.not_lt] at hge
    refine WP.block_nil (M := isa) ⟨h.s5, h.s6, h.s7, h.s8, ?_, h.t3, h.keep, h.rd, h.wr, h.mid, h.done, h.frame⟩
    rw [h.a2, H, headLen, bufLeft, Nat.min_eq_right hge]


/-- After `part1`: the bytes from the buffered block XORed, and `a2` the
bytes of the whole blocks. -/
structure Q1 (s₀ s : State) : Prop where
  s5 : s.gpr .s5 = st s₀
  s6 : s.gpr .s6 = dp s₀ + BitVec.ofNat 64 (H s₀)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (L s₀ - H s₀)
  s8 : s.gpr .s8 = BitVec.ofNat 64 (N s₀ - L s₀)
  a2 : s.gpr .a2 = BitVec.ofNat 64 (64 * NB s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mid : Mid s₀ s.mem
  done : Done s₀ (H s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem d_ne_st {s₀ : State} (hp : APre s₀) {j k : Nat} (hj : j < L s₀) (hk : k < 768) :
    dp s₀ + BitVec.ofNat 64 j ≠ st s₀ + BitVec.ofNat 64 k := by
  intro he
  have c₁ : (dR s₀).Contains (dp s₀ + BitVec.ofNat 64 j) 1 :=
    Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)
  have c₂ : (stR s₀).Contains (st s₀ + BitVec.ofNat 64 k) 1 := Offset.contains_base _ (by omega) (by omega)
  rw [he] at c₁
  exact hp.st_d _ c₂ c₁

theorem dR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < L s₀) :
    InRegions s₀.wr (dp s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨dR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by have := L_lt s₀; omega)⟩

theorem stR_byte {s₀ : State} (hp : APre s₀) {k : Nat} (hk : k < 768) :
    InRegions s₀.wr (st s₀ + BitVec.ofNat 64 k) 1 :=
  ⟨stR s₀, by rw [hp.wr]; simp, Offset.contains_base _ (by omega) (by omega)⟩

theorem not_in_prefix (p : Addr) {k c : Nat} (hk : c ≤ k) (hk' : k < 2 ^ 64) :
    ¬ (⟨p, c⟩ : Region).Contains (p + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains]
  rw [Mem.sub_ofNat_toNat p hk']
  omega

theorem prefix_sub (p : Addr) {c n : Nat} (h : c ≤ n) : Region.Sub ⟨p, c⟩ ⟨p, n⟩ := Region.sub_prefix h

/-- `(x >>> 6) <<< 6` rounds down to a multiple of 64. -/
theorem round64 {x : Nat} (hx : x < 2 ^ 64) :
    (BitVec.ofNat 64 x >>> 6) <<< 6 = BitVec.ofNat 64 (64 * (x / 64)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hx, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem kept_bw : ∀ r ∈ kept, r ∉ bw := by decide

theorem part1_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q0 s₀ s) :
    WP isa part1 s (Q1 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHO := H_le_O s₀
  have hO := O_lt s₀
  refine WP.seq (WP.mono (start_ok hp hle h) fun s₁ ⟨h₁, hc₁⟩ => ?_)
  refine WP.seq (WP.mono (sel_ok h₁ (by rw [hc₁, h.t5])) fun s₂ h₂ => ?_)
  -- The pointer to the bytes left in the buffered block.
  have h₃ : WP isa (.block [.addi .t2 .s5 128, .sub .t2 .t2 .t3]) s₂
      fun s₃ => R1 s₀ (H s₀) s₃ ∧ s₃.gpr .t2 = st s₀ + BitVec.ofNat 64 (128 - O s₀) := by
    refine wp_addi (by decide) fun s' u => ?_
    refine wp_sub fun s'' u' => WP.block_nil ?_
    have g : ∀ r, r ≠ .t2 → s''.gpr r = s₂.gpr r := fun r hr => by rw [u'.other r hr, u.other r hr]
    refine ⟨⟨by rw [g _ (by decide), h₂.s5], by rw [g _ (by decide), h₂.s6], by rw [g _ (by decide), h₂.s7],
      by rw [g _ (by decide), h₂.s8], by rw [g _ (by decide), h₂.a2], by rw [g _ (by decide), h₂.t3],
      fun r hr => by rw [g r (kept_ne hr)]; exact h₂.keep r hr,
      by rw [u'.rd, u.rd, h₂.rd], by rw [u'.wr, u.wr, h₂.wr], by rw [u'.mem, u.mem]; exact h₂.mid,
      by rw [u'.mem, u.mem]; exact h₂.done, by rw [u'.mem, u.mem]; exact h₂.frame⟩, ?_⟩
    rw [u'.gpr, u.gpr, u.other .t3 (by decide), h₂.s5, h₂.t3,
      show (BitVec.ofNat 64 128 : BitVec 64) = BitVec.ofNat 64 (128 - O s₀) + BitVec.ofNat 64 (O s₀) by
        rw [BitVec.ofNat_add_ofNat, show 128 - O s₀ + O s₀ = 128 by omega],
      ← BitVec.add_assoc, BitVec.add_sub_cancel]
  refine WP.seq (WP.mono h₃ fun s₃ ⟨h₃, ht2⟩ => ?_)
  have hb : BPre s₃ (dp s₀) (st s₀ + BitVec.ofNat 64 (128 - O s₀)) (H s₀) :=
    ⟨h₃.s6, ht2, h₃.a2, by omega, fun k hk => by rw [h₃.wr]; exact dR_byte hp (by omega),
      fun k hk => by
        rw [h₃.wr, Offset.add_add]
        obtain ⟨r, hr, hc⟩ := stR_byte hp (k := 128 - O s₀ + k) (by omega)
        exact ⟨r, List.mem_append_right _ hr, hc⟩,
      fun j hj k hk => by rw [Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.seq (WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_)
  have hr7 : s₄.gpr .s7 = BitVec.ofNat 64 (L s₀ - H s₀) := by
    rw [h₄.s7, h₃.s7, sub_ofNat hH]
  refine wp_srl (by decide) fun s₅ u₅ => wp_sll (by decide) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ≠ .a2 → s₆.gpr r = s₄.gpr r := fun r hr => by rw [u₆.other r hr, u₅.other r hr]
  have hm : s₆.mem = s₄.mem := by rw [u₆.mem, u₅.mem]
  have hnb : 64 * ((L s₀ - H s₀) / 64) = 64 * NB s₀ := by simp only [NB, blocksOf, H]
  refine ⟨by rw [g _ (by decide), h₄.keep _ (by decide), h₃.s5],
    by rw [g _ (by decide), h₄.s6], by rw [g _ (by decide), hr7],
    by rw [g _ (by decide), h₄.keep _ (by decide), h₃.s8],
    by rw [u₆.gpr, u₅.gpr, hr7, round64 (by omega), hnb],
    fun r hr => by
      rw [g r (kept_ne hr), h₄.keep r (kept_bw r hr)]
      exact h₃.keep r hr,
    by rw [u₆.rd, u₅.rd, h₄.rd, h₃.rd], by rw [u₆.wr, u₅.wr, h₄.wr, h₃.wr], ⟨fun i hi => ?_, ?_⟩,
    fun k hk => ?_, ?_⟩
  · rw [hm, h₄.frame _ fun r hr hc => ?_]
    · exact h₃.mid.keep i hi
    · simp only [List.mem_singleton] at hr; subst hr
      exact hp.st_d _ (Offset.contains_base (st s₀) (d := i) (n := 1) (k := 768) (by omega) (by omega))
        (Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) _ (by simpa using hc))
  · rw [hm]
    exact h₃.mid.saved.frame h₄.frame fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.st_d.sub_left (savR_sub s₀)).sub_right fun x hx => by
        simpa using Offset.sub_base (dp s₀) (d := 0) (n := H s₀) (k := L s₀) (by omega) x (by simpa using hx)
  · rw [hm]
    by_cases hk' : k < H s₀
    · rw [h₄.data k hk', h₃.done k hk, Offset.add_add, h₃.mid.keep _ (by omega)]
      simp [hk', KS]
    · rw [h₄.frame _ fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr; exact not_in_prefix _ (by omega) (by omega),
        h₃.done k hk]
      simp [hk']
  · rw [hm]
    exact (h₃.frame.mono (by simp)).trans (h₄.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dR s₀, by simp, prefix_sub _ hH⟩)


/-! ## The whole blocks -/

/-- What `blocksArgs` leaves: the state copied to `p + 192`, its counter
advanced, and the arguments of `vg_chacha20_xor`. -/
structure ArgsPost (p : Addr) (s s' : State) : Prop where
  copy : ∀ i < 64, s'.mem (p + BitVec.ofNat 64 (192 + i)) = s.mem (p + BitVec.ofNat 64 i)
  state : stateAt s'.mem p =
    (stateAt s.mem p).set 12 ((stateAt s.mem p)[12] + (s.gpr .a2 >>> 6).setWidth 32)
  frame : Frame [⟨p, 64⟩, ⟨p + BitVec.ofNat 64 192, 64⟩] s.mem s'.mem
  a0 : s'.gpr .a0 = p + BitVec.ofNat 64 192
  a1 : s'.gpr .a1 = s.gpr .s6
  a2 : s'.gpr .a2 = s.gpr .a2
  a3 : s'.gpr .a3 = p + BitVec.ofNat 64 256
  s5 : s'.gpr .s5 = p
  s6 : s'.gpr .s6 = s.gpr .s6 + s.gpr .a2
  s7 : s'.gpr .s7 = s.gpr .s7 - s.gpr .a2
  s8 : s'.gpr .s8 = s.gpr .s8
  keep : ∀ r ∈ kept, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem args_exec {s : State} {p : Addr} (hs5 : s.gpr .s5 = p)
    (hw : ∀ d n, d + n ≤ 768 → InRegions s.wr (p + BitVec.ofNat 64 d) n) (hrd : s.rd = []) :
    WP isa (.block blocksArgs) s (ArgsPost p s) := by
  have hr : ∀ d n, d + n ≤ 768 → InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 d) n := fun d n h => by
    rw [hrd, List.nil_append]; exact hw d n h
  unfold blocksArgs
  simp only [List.append_assoc, List.singleton_append]
  rw [WP.block_append_iff]
  refine WP.mono (copyBytes_ok (tmp := .t1) (src := .s5) (dst := .s5) (soff := 0) (doff := 192) (n := 64)
    (by decide) (by decide) (by decide) (by decide) (fun i hi => by rw [hs5]; exact hr _ 1 (by omega))
    (fun i hi => by rw [hs5]; exact hw _ 1 (by omega))
    (fun i hi hc => by
      rw [hs5] at hc
      exact Offset.disjoint p (d := 0 + i) (n := 1) (e := 192) (k := 64) (by omega) (by omega) (by omega) _
        (Region.contains_self _ _) hc)) fun s₁ h₁ => ?_
  have c₁ : ∀ j < 64, s₁.mem (p + BitVec.ofNat 64 (192 + j)) = s.mem (p + BitVec.ofNat 64 (0 + j)) := by
    rw [← hs5]; exact h₁.copied
  have f₁ : Frame [⟨p + BitVec.ofNat 64 192, 64⟩] s.mem s₁.mem := by rw [← hs5]; exact h₁.frame
  have p₁ : s₁.gpr .s5 = p := by rw [h₁.gpr _ (by decide), hs5]
  refine wp_srl (by decide) fun s₂ u₂ => ?_
  simp only [List.append_eq]
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (d := .t1) (tmp := .t3) (n := .s5) (off := 48) (by decide) (by decide)
    (by decide) (by decide) (by rw [u₂.other _ (by decide), p₁, u₂.rd, u₂.wr, h₁.rd, h₁.wr]; exact hr 48 4 (by decide)))
    fun s₃ e₃ => ?_
  refine wp_add fun s₄ u₄ => ?_
  have g₃ : ∀ r, r ≠ .t1 → r ≠ .t3 → s₃.gpr r = s₂.gpr r := fun r h₁ h₂ => by
    rw [e₃, RegUpd.gpr_write_of_ne _ _ h₁, RegUpd.gpr_write_of_ne _ _ h₂]
  have p₄ : s₄.gpr .s5 = p := by
    rw [u₄.other _ (by decide), g₃ _ (by decide) (by decide), u₂.other _ (by decide), p₁]
  have m₄ : s₄.mem = s₁.mem := by rw [u₄.mem, e₃]; exact u₂.mem
  have w₄ : s₄.wr = s.wr := by rw [u₄.wr, e₃]; exact u₂.wr.trans h₁.wr
  simp only [List.append_eq]
  rw [WP.block_append_iff]
  refine WP.mono (storeLE32_ok (v := .t1) (tmp := .t3) (n := .s5) (off := 48) (by decide) (by decide)
    (by decide) (by rw [p₄, w₄]; exact hw 48 4 (by decide))) fun s₅ e₅ => ?_
  have hc48 : s₁.mem.readW (p + BitVec.ofNat 64 48) 32 = s.mem.readW (p + BitVec.ofNat 64 48) 32 :=
    f₁.readW (r := ⟨p + BitVec.ofNat 64 48, 4⟩) (Region.contains_self _ _)
      (by simpa using Offset.disjoint p (d := 48) (n := 4) (e := 192) (k := 64) (by omega) (by omega) (by omega))
      (by decide)
  have v₄ : (s₄.gpr .t1).setWidth 32 = s.mem.readW (p + BitVec.ofNat 64 48) 32 + (s.gpr .a2 >>> 6).setWidth 32 := by
    rw [u₄.gpr, lo32_add, e₃, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ (by decide),
      RegUpd.gpr_write_of_ne _ _ (by decide), u₂.gpr, u₂.other _ (by decide), p₁, lo32_ext, h₁.gpr _ (by decide)]
    rw [u₂.mem, hc48]
  have m₅ : s₅.mem = s₁.mem.writeW (p + BitVec.ofNat 64 48)
      (s.mem.readW (p + BitVec.ofNat 64 48) 32 + (s.gpr .a2 >>> 6).setWidth 32) := by
    rw [e₅]; simp only [RegUpd.mem_write]; rw [p₄, v₄, m₄]
  have g₅ : ∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .t4 → s₅.gpr r = s.gpr r := fun r h₁' h₂ h₃ => by
    rw [e₅, RegUpd.gpr_write_of_ne _ _ h₂]
    show s₄.gpr r = _
    rw [u₄.other r h₁', g₃ r h₁' h₂, u₂.other r h₃, h₁.gpr r h₁']
  refine wp_addi (by decide) fun s₆ u₆ => wp_mv fun s₇ u₇ => wp_addi (by decide) fun s₈ u₈ =>
    wp_add fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ => WP.block_nil ?_
  have gm : s₁₀.mem = s₅.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g₉ : ∀ r, r ≠ .a0 → r ≠ .a1 → r ≠ .a3 → r ≠ .s6 → r ≠ .s7 → s₁₀.gpr r = s₅.gpr r :=
    fun r h0 h1 h3 h6 h7 => by rw [u₁₀.other r h7, u₉.other r h6, u₈.other r h3, u₇.other r h1, u₆.other r h0]
  have p₅ : s₅.gpr .s5 = p := by rw [g₅ _ (by decide) (by decide) (by decide), hs5]
  refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [gm, m₅, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), c₁ i hi, Nat.zero_add]
  · rw [gm, m₅, stateAt_writeW_counter,
      stateAt_frame f₁ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega))]
    simp [stateAt]
  · rw [gm, m₅]
    refine (f₁.mono (by simp)).writeW (List.mem_cons_self ..) _ ?_
    exact Offset.contains_base _ (by omega) (by omega)
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.gpr, p₅]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide)]
  · rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide)]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide),
      p₅]
  · rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), p₅]
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ _ (by decide) (by decide) (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide)]
  · rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      g₅ _ (by decide) (by decide) (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide) (by decide) (by decide)]
  · rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), g₅ _ (by decide) (by decide) (by decide)]
  · rw [g₉ r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr),
      g₅ r (kept_ne hr) (kept_ne hr) (kept_ne hr)]
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, e₅, RegUpd.rd_write]
    exact u₄.rd.trans ((by rw [e₃]; exact u₂.rd.trans h₁.rd) : s₃.rd = s.rd)
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, e₅, RegUpd.wr_write]; exact w₄


theorem shr_eq {nb : Nat} (h : 64 * nb < 2 ^ 64) :
    (BitVec.ofNat 64 (64 * nb) >>> 6).setWidth 32 = BitVec.ofNat 32 nb := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  omega

/-- After `part2`: the whole blocks XORed, and the counter advanced past
them. -/
structure Q2 (s₀ s : State) : Prop where
  s5 : s.gpr .s5 = st s₀
  s6 : s.gpr .s6 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)
  s7 : s.gpr .s7 = BitVec.ofNat 64 (T s₀)
  s8 : s.gpr .s8 = BitVec.ofNat 64 (N s₀ - L s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
  saved : Saved s₀ s.mem
  done : Done s₀ (H s₀ + 64 * NB s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem nb_zero_ok {s₀ : State} {s : State} (h : Q1 s₀ s) (h0 : 64 * NB s₀ = 0) : Q2 s₀ s := by
  have hT := T_eq s₀
  refine ⟨h.s5, by rw [h.s6, h0, Nat.add_zero], by rw [h.s7, hT, h0, Nat.sub_zero], h.s8, h.keep, h.rd, h.wr,
    by rw [h.mid.state, show NB s₀ = 0 by omega, ctr_zero], fun i hi => h.mid.keep _ (by omega),
    h.mid.saved, by rw [h0, Nat.add_zero]; exact h.done, h.frame⟩

theorem Q1.w {s₀ s : State} (hp : APre s₀) (h : Q1 s₀ s) :
    ∀ d n, d + n ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) n := fun d n hd => by
  rw [h.wr]; exact hp.w_st hd

/-- The regions of the call of `vg_chacha20_xor`: the copy of the state,
the data and the working space. -/
abbrev cpR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 192, 64⟩
abbrev blR (s₀ : State) : Region := ⟨dp s₀ + BitVec.ofNat 64 (H s₀), 64 * NB s₀⟩
abbrev wkR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 256, 320⟩

theorem cpR_sub (s₀ : State) : Region.Sub (cpR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem wkR_sub (s₀ : State) : Region.Sub (wkR s₀) (stR s₀) := Offset.sub_base _ (by omega)
theorem blR_sub (s₀ : State) : Region.Sub (blR s₀) (dR s₀) := Offset.sub_base _ (HNB_le s₀)

/-- The registers kept are callee-saved. -/
theorem kept_preserved : ∀ r ∈ kept, r ∈ preserved := by decide

theorem blocks_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) (hnb : 0 < NB s₀) :
    WP isa (.seq (.block blocksArgs) (.call "vg_chacha20_xor" Impl.ChaCha20.RISCV64.Xor.xor)) s (Q2 s₀) := by
  have hL := L_lt s₀
  have hH := H_le s₀
  have hHNB := HNB_le s₀
  have hT := T_eq s₀
  refine WP.seq (WP.mono (args_exec h.s5 (h.w hp) (by rw [h.rd, hp.rd])) fun s₁ A => ?_)
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [A.wr, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [A.rd, h.rd, hp.rd]
  have dSB : (cpR s₀).Disjoint (wkR s₀) := Offset.disjoint _ (by omega) (by omega) (by omega)
  have dSD : (cpR s₀).Disjoint (blR s₀) := (hp.st_d.sub_left (cpR_sub s₀)).sub_right (blR_sub s₀)
  have dDB : (blR s₀).Disjoint (wkR s₀) := (hp.st_d.sub_left (wkR_sub s₀)).symm.sub_left (blR_sub s₀)
  have hcov : ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], ∃ r' ∈ [stR s₀, dR s₀], ∃ o,
      r.base = r'.base + BitVec.ofNat 64 o ∧ o + r.len ≤ r'.len := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, 192, rfl, by simp⟩
    · exact ⟨dR s₀, by simp, H s₀, rfl, hHNB⟩
    · exact ⟨stR s₀, by simp, 256, rfl, by simp⟩
  have hwrap : (dp s₀ + BitVec.ofNat 64 (H s₀)).toNat + 64 * NB s₀ ≤ 2 ^ 64 := by
    have := hp.wrap_d
    rw [BitVec.toNat_add, toNat_ofNat_lt (by omega)]
    omega
  refine xor_call (S := st s₀ + BitVec.ofNat 64 192) (D := dp s₀ + BitVec.ofNat 64 (H s₀))
    (B := st s₀ + BitVec.ofNat 64 256) (n := 64 * NB s₀) A.a0 (by rw [A.a1, h.s6]) (by rw [A.a2, h.a2])
    A.a3 (by omega) dSD dSB dDB hwrap (hp.al (by decide)) (hp.al (by decide))
    (by rw [hrd₁, hwr₁, List.nil_append, List.nil_append]; exact Covers.of_sub hcov)
    (by rw [hwr₁]; exact Covers.of_sub hcov) ?_
  intro s₂ k₂ x₂
  have g : ∀ r ∈ preserved, s₂.gpr r = s₁.gpr r := k₂.cs
  -- Regions the call does not write.
  have nd : ∀ R : Region, R.Disjoint (cpR s₀) → R.Disjoint (blR s₀) → R.Disjoint (wkR s₀) →
      ∀ r ∈ [cpR s₀, blR s₀, wkR s₀], R.Disjoint r := by
    intro R h₁ h₂ h₃ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> with_reducible assumption
  have nc : ∀ R : Region, R.Disjoint ⟨st s₀, 64⟩ → R.Disjoint ⟨st s₀ + BitVec.ofNat 64 192, 64⟩ →
      ∀ r ∈ [⟨st s₀, 64⟩, ⟨st s₀ + BitVec.ofNat 64 192, 64⟩], R.Disjoint r := by
    intro R h₁ h₂ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> with_reducible assumption
  have fc := A.frame
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  have bufS : Region.Sub ⟨st s₀ + BitVec.ofNat 64 64, 64⟩ (stR s₀) := Offset.sub_base _ (by omega)
  -- Anything in the state is apart from the data.
  have sd : ∀ R, Region.Sub R (stR s₀) → R.Disjoint (blR s₀) := fun R hR =>
    (hp.st_d.sub_left hR).sub_right (blR_sub s₀)
  have ds : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hcopy : stateAt s₁.mem (st s₀ + BitVec.ofNat 64 192) = S0 s₀ := by
    rw [← h.mid.state]
    exact stateAt_congr fun i hi => by rw [Offset.add_add]; exact A.copy i hi
  refine ⟨by rw [g .s5 (by decide), A.s5], ?_, ?_, by rw [g .s8 (by decide), A.s8, h.s8], fun r hr => ?_,
    by rw [k₂.rd, A.rd, h.rd], by rw [k₂.wr, A.wr, h.wr], ?_, fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [g .s6 (by decide), A.s6, h.s6, h.a2, Offset.add_add]
  · rw [g .s7 (by decide), A.s7, h.s7, h.a2, sub_ofNat (by omega), hT, Nat.sub_sub]
  · rw [g r (kept_preserved r hr), A.keep r hr]
    exact h.keep r hr
  · rw [stateAt_frame k₂.frame (nd _
        (Offset.base_disjoint _ (by omega) (by omega)) (sd _ stS)
        (Offset.base_disjoint _ (by omega) (by omega))),
      A.state, h.a2, shr_eq (by omega), h.mid.state]
    rfl
  · rw [← Offset.add_add, k₂.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nd _
        (Offset.disjoint _ (by omega) (by omega) (by omega)) (sd _ bufS)
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      fc.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (nc _ (Offset.disjoint_base _ (by omega) (by omega))
        (Offset.disjoint _ (by omega) (by omega) (by omega))) (show 64 ≤ 2 ^ 64 by decide) hi,
      Offset.add_add]
    exact h.mid.keep _ (by omega)
  · refine (h.mid.saved.frame fc (nc _ ?_ ?_)).frame k₂.frame (nd _ ?_ (sd _ (savR_sub s₀)) ?_)
    · exact savR_disjoint s₀ (e := 0) (k := 64) (by omega) |> fun h => by simpa using h
    · exact savR_disjoint s₀ (by omega)
    · exact savR_disjoint s₀ (by omega)
    · exact savR_disjoint s₀ (by omega)
  · have fcd : s₁.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fc.bytes (R := dR s₀) (nc _ (ds _ _ (fun _ h => h) stS) (ds _ _ (fun _ h => h) (cpR_sub s₀)))
        (show L s₀ ≤ 2 ^ 64 by omega) hk
    by_cases hk₁ : k < H s₀
    · have hpre : Region.Sub ⟨dp s₀, H s₀⟩ (dR s₀) := prefix_sub _ hH
      rw [k₂.frame.bytes (R := ⟨dp s₀, H s₀⟩) (nd _ (ds _ _ hpre (cpR_sub s₀))
          (Offset.base_disjoint _ (by omega) (by omega)) (ds _ _ hpre (wkR_sub s₀)))
          (show H s₀ ≤ 2 ^ 64 by omega) hk₁]
      rw [fcd, h.done k hk, ite_pos hk₁, ite_pos (by omega)]
    by_cases hk₂ : k < H s₀ + 64 * NB s₀
    · have e := xor_getD (length_keystream _ _) x₂ (j := k - H s₀) (by omega)
      rw [Offset.add_add, show H s₀ + (k - H s₀) = k by omega, fcd, h.done k hk, ite_neg hk₁,
        hcopy, keystream_getD _ (by omega)] at e
      rw [e, ite_pos hk₂]
      simp only [KS, ite_neg hk₁]
    · have hR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩ (dR s₀) :=
        Offset.sub_base _ (by omega)
      have := k₂.frame.bytes (R := ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), L s₀ - (H s₀ + 64 * NB s₀)⟩)
        (nd _ (ds _ _ hR (cpR_sub s₀)) (Offset.disjoint _ (by omega) (by omega) (by omega))
          (ds _ _ hR (wkR_sub s₀))) (show L s₀ - (H s₀ + 64 * NB s₀) ≤ 2 ^ 64 by omega)
          (i := k - (H s₀ + 64 * NB s₀)) (by simp only; omega)
      rw [Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega] at this
      rw [this, fcd, h.done k hk, ite_neg hk₁, ite_neg hk₂]
  · refine (h.frame.trans (fc.sub fun r hr => ?_)).trans (k₂.frame.sub fun r hr => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, stS⟩
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨stR s₀, by simp, cpR_sub s₀⟩
      · exact ⟨dR s₀, by simp, blR_sub s₀⟩
      · exact ⟨stR s₀, by simp, wkR_sub s₀⟩

theorem part2_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q1 s₀ s) : WP isa part2 s (Q2 s₀) := by
  have hL := L_lt s₀
  have hHNB := HNB_le s₀
  refine WP.ite (decide (64 * NB s₀ = 0)) (eval_zero_ofNat _ _ (by omega) h.a2)
    (fun h0 => WP.block_nil (M := isa) (nb_zero_ok h (by simpa using h0)))
    (fun h0 => blocks_ok hp h (by simp only [decide_eq_false_iff_not] at h0; omega))


/-! ## The last bytes -/

/-- After `part3`: all the data XORed; the counter advanced past the block
started, if any, which is buffered. -/
structure Q3 (s₀ s : State) : Prop where
  s5 : s.gpr .s5 = st s₀
  s8 : s.gpr .s8 = BitVec.ofNat 64 (N s₀ - L s₀)
  keep : ∀ r ∈ kept, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  state : stateAt s.mem (st s₀) = ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1)
  buf : ∀ i < 64, s.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
    if T s₀ = 0 then s₀.mem (st s₀ + BitVec.ofNat 64 (64 + i))
    else (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0
  saved : Saved s₀ s.mem
  done : Done s₀ (L s₀) s.mem
  frame : Frame [stR s₀, dR s₀] s₀.mem s.mem

theorem t_zero_ok {s₀ : State} {s : State} (h : Q2 s₀ s) (h0 : T s₀ = 0) : Q3 s₀ s := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  refine ⟨h.s5, h.s8, h.keep, h.rd, h.wr, by rw [h.state, h0]; rfl, fun i hi => by rw [h.buf i hi, h0]; rfl,
    h.saved, by rw [show L s₀ = H s₀ + 64 * NB s₀ by omega]; exact h.done, h.frame⟩

/-- The buffered block, and the bytes the block function may write. -/
abbrev bufR (s₀ : State) : Region := ⟨st s₀ + BitVec.ofNat 64 64, 256⟩

theorem bufR_sub (s₀ : State) : Region.Sub (bufR s₀) (stR s₀) := Offset.sub_base _ (by omega)

/-- The counter advanced, and the arguments of `xorBytes` for the buffered
block. -/
theorem ctr_exec {s : State} {p : Addr} (hs5 : s.gpr .s5 = p) (hw : InRegions s.wr (p + BitVec.ofNat 64 48) 4)
    (hr : InRegions (s.rd ++ s.wr) (p + BitVec.ofNat 64 48) 4) :
    WP isa (.block (incr ++ ([.addi .t2 .s5 64, mov .a2 .s7] : List Instr))) s fun s' =>
      s'.mem = s.mem.writeW (p + BitVec.ofNat 64 48) (s.mem.readW (p + BitVec.ofNat 64 48) 32 + 1) ∧
      s'.gpr .t2 = p + BitVec.ofNat 64 64 ∧ s'.gpr .a2 = s.gpr .s7 ∧
      (∀ r, r ≠ .t1 → r ≠ .t3 → r ≠ .t2 → r ≠ .a2 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold incr
  simp only [List.append_assoc, List.singleton_append]
  rw [WP.block_append_iff]
  refine WP.mono (loadLE32_ok (d := .t1) (tmp := .t3) (n := .s5) (off := 48) (by decide) (by decide)
    (by decide) (by decide) (by rw [hs5]; exact hr)) fun s₁ e₁ => ?_
  have g₁ : ∀ r, r ≠ .t1 → r ≠ .t3 → s₁.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [e₁, RegUpd.gpr_write_of_ne _ _ h₁, RegUpd.gpr_write_of_ne _ _ h₂]
  have t₁ : s₁.gpr .t1 = (s.mem.readW (p + BitVec.ofNat 64 48) 32).setWidth 64 := by
    rw [e₁, RegUpd.gpr_write_self, hs5]
  have m₁ : s₁.mem = s.mem := by rw [e₁]; rfl
  have rd₁ : s₁.rd = s.rd := by rw [e₁]; rfl
  have wr₁ : s₁.wr = s.wr := by rw [e₁]; rfl
  refine wp_addi (by decide) fun s₂ u₂ => ?_
  have p₂ : s₂.gpr .s5 = p := by rw [u₂.other _ (by decide), g₁ _ (by decide) (by decide), hs5]
  simp only [List.append_eq]
  rw [WP.block_append_iff]
  refine WP.mono (storeLE32_ok (v := .t1) (tmp := .t3) (n := .s5) (off := 48) (by decide) (by decide)
    (by decide) (by rw [p₂, u₂.wr, wr₁]; exact hw)) fun s₃ e₃ => ?_
  have m₃ : s₃.mem = s.mem.writeW (p + BitVec.ofNat 64 48) (s.mem.readW (p + BitVec.ofNat 64 48) 32 + 1) := by
    rw [e₃]; simp only [RegUpd.mem_write, p₂, u₂.gpr, t₁, inc_setWidth, u₂.mem, m₁]
  have g₃ : ∀ r, r ≠ .t1 → r ≠ .t3 → s₃.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [e₃, RegUpd.gpr_write_of_ne _ _ h₂]; exact (u₂.other r h₁).trans (g₁ r h₁ h₂)
  have rd₃ : s₃.rd = s.rd := by rw [e₃, RegUpd.rd_write]; exact u₂.rd.trans rd₁
  have wr₃ : s₃.wr = s.wr := by rw [e₃, RegUpd.wr_write]; exact u₂.wr.trans wr₁
  refine wp_addi (by decide) fun s₄ u₄ => wp_mv fun s₅ u₅ => WP.block_nil ?_
  refine ⟨by rw [u₅.mem, u₄.mem, m₃], by rw [u₅.other _ (by decide), u₄.gpr, g₃ _ (by decide) (by decide), hs5],
    by rw [u₅.gpr, u₄.other _ (by decide), g₃ _ (by decide) (by decide)], fun r h₁ h₂ h₃ h₄ => ?_,
    by rw [u₅.rd, u₄.rd, rd₃], by rw [u₅.wr, u₄.wr, wr₃]⟩
  rw [u₅.other r h₄, u₄.other r h₃, g₃ r h₁ h₂]

theorem preserved_ne : ∀ r ∈ preserved, r ≠ .a0 ∧ r ≠ .a1 := by decide

theorem tail_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) (ht : T s₀ ≠ 0) :
    WP isa (.seq (.block tailArgs) (.seq (.call "vg_chacha20_block" Impl.ChaCha20.RISCV64.block) tailXor))
      s (Q3 s₀) := by
  have hT := T_eq s₀
  have hHNB := HNB_le s₀
  have hL := L_lt s₀
  have h₁ : WP isa (.block tailArgs) s fun s₁ => s₁.gpr .a0 = st s₀ ∧
      s₁.gpr .a1 = st s₀ + BitVec.ofNat 64 64 ∧
      (∀ r, r ≠ .a0 → r ≠ .a1 → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine wp_mv fun s' u => wp_addi (by decide) fun s'' u' => WP.block_nil ?_
    exact ⟨by rw [u'.other _ (by decide), u.gpr, h.s5], by rw [u'.gpr, u.other _ (by decide), h.s5],
      fun r h₁ h₂ => by rw [u'.other r h₂, u.other r h₁], by rw [u'.mem, u.mem], by rw [u'.rd, u.rd],
      by rw [u'.wr, u.wr]⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨a0₁, a1₁, k₁, m₁, rd₁, wr₁⟩ => ?_)
  have hwr₁ : s₁.wr = [stR s₀, dR s₀] := by rw [wr₁, h.wr, hp.wr]
  have hrd₁ : s₁.rd = [] := by rw [rd₁, h.rd, hp.rd]
  have stS : Region.Sub ⟨st s₀, 64⟩ (stR s₀) := prefix_sub _ (by omega)
  refine WP.seq (block_call a0₁ a1₁ (Offset.disjoint_base _ (by omega) (by omega))
    (by have := hp.st_al; omega) (hp.al (by decide))
    (by
      rw [hrd₁, hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨stR s₀, by simp, 0, by simp, show 0 + 64 ≤ 768 by decide⟩
      · exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩)
    (by
      rw [hwr₁]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 64, rfl, show 64 + 256 ≤ 768 by decide⟩) fun s₂ k₂ blk₂ => ?_)
  have g : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [k₂.cs r hr, k₁ r (preserved_ne r hr).1 (preserved_ne r hr).2]
  have hw48 : InRegions s₂.wr (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.wr, hwr₁]; exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hr48 : InRegions (s₂.rd ++ s₂.wr) (st s₀ + BitVec.ofNat 64 48) 4 := by
    rw [k₂.rd, hrd₁, List.nil_append]; exact hw48
  refine WP.seq (WP.mono (ctr_exec (by rw [g .s5 (by decide), h.s5]) hw48 hr48)
    fun s₃ ⟨m₃, t2₃, a2₃, k₃, rd₃, wr₃⟩ => ?_)
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  have hs6₃ : s₃.gpr .s6 = dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀) := by
    rw [k₃ .s6 (by decide) (by decide) (by decide) (by decide), g .s6 (by decide), h.s6]
  have dS : ∀ R R', Region.Sub R (dR s₀) → Region.Sub R' (stR s₀) → R.Disjoint R' := fun R R' h₁ h₂ =>
    (hp.st_d.symm.sub_left h₁).sub_right h₂
  have hb : BPre s₃ (dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀)) (st s₀ + BitVec.ofNat 64 64) (T s₀) :=
    ⟨hs6₃, t2₃, by rw [a2₃, g .s7 (by decide), h.s7], by omega,
      fun k hk => by
        rw [wr₃, k₂.wr, hwr₁, Offset.add_add]
        exact ⟨dR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun k hk => by
        rw [rd₃, wr₃, k₂.rd, k₂.wr, hrd₁, hwr₁, List.nil_append, Offset.add_add]
        exact ⟨stR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩,
      fun j hj k hk => by rw [Offset.add_add, Offset.add_add]; exact d_ne_st hp (by omega) (by omega)⟩
  refine WP.mono (xorBytes_ok hb) fun s₄ h₄ => ?_
  have f₂ := k₂.frame
  have f₃ : Frame [⟨st s₀ + BitVec.ofNat 64 48, 4⟩] s₂.mem s₃.mem := by
    rw [m₃]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have tR : Region.Sub ⟨dp s₀ + BitVec.ofNat 64 (H s₀ + 64 * NB s₀), T s₀⟩ (dR s₀) :=
    Offset.sub_base _ (by omega)
  have c48 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have st₂ : stateAt s₂.mem (st s₀) = ctr (S0 s₀) (NB s₀) := by
    rw [stateAt_frame f₂ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega)),
      m₁, h.state]
  have bb : ∀ i < 64, s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) =
      (serialize (block (ctr (S0 s₀) (NB s₀)))).getD i 0 := by
    intro i hi
    rw [← Offset.add_add, ← serialize_stateAt s₂.mem _ hi, blk₂, m₁, h.state]
  have b3 : ∀ i < 64, s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₂.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [m₃]; exact byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega)
  have b4 : ∀ i < 64, s₄.mem (st s₀ + BitVec.ofNat 64 (64 + i)) = s₃.mem (st s₀ + BitVec.ofNat 64 (64 + i)) := by
    intro i hi
    rw [← Offset.add_add]
    exact h₄.frame.bytes (R := ⟨st s₀ + BitVec.ofNat 64 64, 64⟩) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR (Offset.sub_base _ (by omega))).symm) (show 64 ≤ 2 ^ 64 by decide) hi
  refine ⟨?_, ?_, fun r hr => ?_, by rw [h₄.rd, rd₃, k₂.rd, rd₁, h.rd], by rw [h₄.wr, wr₃, k₂.wr, wr₁, h.wr], ?_,
    fun i hi => ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [h₄.keep _ (by decide), k₃ .s5 (by decide) (by decide) (by decide) (by decide), g .s5 (by decide), h.s5]
  · rw [h₄.keep _ (by decide), k₃ .s8 (by decide) (by decide) (by decide) (by decide), g .s8 (by decide), h.s8]
  · rw [h₄.keep r (kept_bw r hr), k₃ r (kept_ne hr) (kept_ne hr) (kept_ne hr) (kept_ne hr),
      g r (kept_preserved r hr)]
    exact h.keep r hr
  · have e12 : s₂.mem.readW (st s₀ + BitVec.ofNat 64 48) 32 = (ctr (S0 s₀) (NB s₀))[12] := by
      rw [← st₂]; simp [stateAt]
    rw [stateAt_frame h₄.frame (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (dS _ _ tR stS).symm),
      m₃, stateAt_writeW_counter, st₂, e12, ctr_succ, ite_neg ht]
  · rw [b4 i hi, b3 i hi, bb i hi, ite_neg ht]
  · have svS := savR_sub s₀
    rw [m₁] at f₂
    refine ((h.saved.frame f₂ fun r hr => ?_).frame f₃ fun r hr => ?_).frame h₄.frame fun r hr => ?_
    · simp only [List.mem_singleton] at hr; subst hr
      exact savR_disjoint s₀ (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact savR_disjoint s₀ (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      exact (dS _ _ tR svS).symm
  · have dS48 : (dR s₀).Disjoint ⟨st s₀ + BitVec.ofNat 64 48, 4⟩ := dS _ _ (fun _ h => h) c48
    have back : s₃.mem (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) := by
      rw [f₃.bytes (R := dR s₀) (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact dS48)
          (show L s₀ ≤ 2 ^ 64 by omega) hk,
        f₂.bytes (R := dR s₀) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact dS _ _ (fun _ h => h) (bufR_sub s₀)) (show L s₀ ≤ 2 ^ 64 by omega) hk, m₁]
    by_cases hk₁ : k < H s₀ + 64 * NB s₀
    · rw [h₄.frame.bytes (R := ⟨dp s₀, H s₀ + 64 * NB s₀⟩) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.base_disjoint _ (by omega) (by omega)) (show H s₀ + 64 * NB s₀ ≤ 2 ^ 64 by omega) hk₁,
        back, h.done k hk, ite_pos hk₁, ite_pos hk]
    · have e := h₄.data (k - (H s₀ + 64 * NB s₀)) (by omega)
      rw [Offset.add_add, Offset.add_add, show H s₀ + 64 * NB s₀ + (k - (H s₀ + 64 * NB s₀)) = k by omega,
        back, b3 _ (by omega), bb _ (by omega), h.done k hk, ite_neg hk₁] at e
      rw [e, ite_pos hk]
      simp only [KS, ite_neg (show ¬ k < H s₀ by omega)]
      rw [show (k - H s₀) / 64 = NB s₀ by omega, show (k - H s₀) % 64 = k - (H s₀ + 64 * NB s₀) by omega]
  · rw [m₁] at f₂
    refine ((h.frame.trans (f₂.sub fun r hr => ?_)).trans (f₃.sub fun r hr => ?_)).trans
      (h₄.frame.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, bufR_sub s₀⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, c48⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨dR s₀, by simp, tR⟩

theorem part3_ok {s₀ : State} (hp : APre s₀) {s : State} (h : Q2 s₀ s) : WP isa part3 s (Q3 s₀) := by
  have hT64 : T s₀ < 64 := Nat.mod_lt _ (by decide)
  refine WP.ite (decide (T s₀ = 0)) (eval_zero_ofNat _ _ (by omega) h.s7)
    (fun h0 => WP.block_nil (M := isa) (t_zero_ok h (by simpa using h0)))
    (fun h0 => tail_ok hp h (by simpa using h0))


/-! ## The end -/

theorem preserved_kept : ∀ r ∈ preserved, r ≠ .s5 → r ≠ .s6 → r ≠ .s7 → r ≠ .s8 → r ∈ kept := by decide

/-- The memory after the bytes left are stored. -/
abbrev leftMem (s₀ : State) (m : Mem) : Mem :=
  (m.writeW (st s₀ + BitVec.ofNat 64 128) ((BitVec.ofNat 64 (N s₀ - L s₀)).setWidth 32)).writeW
    (st s₀ + BitVec.ofNat 64 (128 + 4)) ((BitVec.ofNat 64 (N s₀ - L s₀) >>> 32).setWidth 32)

theorem leftMem_sv (s₀ : State) (m : Mem) {d : Nat} (hd : d + 8 ≤ 40) :
    (leftMem s₀ m).readW (sv s₀ + BitVec.ofNat 64 d) 64 = m.readW (sv s₀ + BitVec.ofNat 64 d) 64 := by
  have := q_lt s₀
  rw [sv_add, leftMem, readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by decide),
    readW_writeW_ofNat _ _ _ (by omega) (by omega) (by omega) (by decide)]

theorem leftMem_frame (s₀ : State) (m : Mem) : Frame [⟨st s₀ + BitVec.ofNat 64 128, 8⟩] m (leftMem s₀ m) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega)
    (by omega))).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))

theorem finish_ok {s₀ : State} (hp : APre s₀) (hle : L s₀ ≤ N s₀) {s : State} (h : Q3 s₀ s) :
    WP isa (.block finish) s (Final s₀) := by
  have hL := L_lt s₀
  have hN := N_lt s₀
  have w : ∀ d n, d + n ≤ 768 → InRegions s.wr (st s₀ + BitVec.ofNat 64 d) n := fun d n hd => by
    rw [h.wr]; exact hp.w_st hd
  unfold finish
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (storeLE64_ok (v := .s8) (tmp := .t1) (hi := .t2) (n := .s5) (off := 128) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by rw [h.s5]; exact w 128 4 (by decide))
    (by rw [h.s5]; exact w 132 4 (by decide))) fun s₁ ⟨m₁, g₁, rd₁, wr₁, _⟩ => ?_
  rw [h.s5, h.s8] at m₁
  have r : ∀ d, d + 8 ≤ 40 → InRegions (s₁.rd ++ s₁.wr) (sv s₀ + BitVec.ofNat 64 d) 8 := fun d hd => by
    rw [rd₁, wr₁, h.rd, h.wr, hp.rd, List.nil_append]; exact hp.w_sv hd
  rw [WP.block_append_iff]
  refine WP.mono (savePtr_ok .s5) fun s₂ e₂ => ?_
  have u₂ : Upd s₁ s₂ .t0 (sv s₀) := by
    rw [e₂, show sv s₀ = s₁.gpr .s5 + BitVec.ofNat 64 576 +
      BitVec.ofNat 64 (pad (s₁.gpr .s5 + BitVec.ofNat 64 576)) by
        rw [g₁ _ (by decide) (by decide), h.s5]]
    exact Upd.write _ _ _
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 0) (by decide) (by rw [u₂.gpr]) (sv_al _ (by decide))
    (by rw [u₂.rd, u₂.wr]; exact r 0 (by decide)) fun s₃ u₃ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 16) (by decide) (by rw [u₃.other _ (by decide), u₂.gpr])
    (sv_al _ (by decide)) (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact r 16 (by decide)) fun s₄ u₄ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 24) (by decide)
    (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]) (sv_al _ (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact r 24 (by decide)) fun s₅ u₅ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 32) (by decide)
    (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr])
    (sv_al _ (by decide)) (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact r 32 (by decide))
    fun s₆ u₆ => ?_
  refine wp_ld (a := sv s₀ + BitVec.ofNat 64 8) (by decide)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr]) (sv_al _ (by decide))
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr]; exact r 8 (by decide))
    fun s₇ u₇ => ?_
  refine wp_li (imm := 1) (by decide) fun s₈ u₈ => WP.block_nil ?_
  have hm : ∀ x : State, x.mem = s₁.mem → x.mem = leftMem s₀ s.mem := fun x e => by rw [e, m₁]
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  have m₃ : s₃.mem = s₁.mem := u₃.mem.trans m₂
  have m₄ : s₄.mem = s₁.mem := u₄.mem.trans m₃
  have m₅ : s₅.mem = s₁.mem := u₅.mem.trans m₄
  have m₆ : s₆.mem = s₁.mem := u₆.mem.trans m₅
  have m₈ : s₈.mem = leftMem s₀ s.mem := hm _ (u₈.mem.trans (u₇.mem.trans m₆))
  have sv' : ∀ d, d + 8 ≤ 40 → s₁.mem.readW (sv s₀ + BitVec.ofNat 64 d) 64 = s.mem.readW (sv s₀ + BitVec.ofNat 64 d) 64 :=
    fun d hd => by rw [m₁, leftMem_sv _ _ hd]
  have g : ∀ r ∈ kept, s₈.gpr r = s.gpr r := fun r hr => by
    rw [u₈.other r (kept_ne hr), u₇.other r (kept_ne hr), u₆.other r (kept_ne hr), u₅.other r (kept_ne hr),
      u₄.other r (kept_ne hr), u₃.other r (kept_ne hr), u₂.other r (kept_ne hr),
      g₁ r (kept_ne hr) (kept_ne hr)]
  have hfw := leftMem_frame s₀ s.mem
  have c128 : Region.Sub ⟨st s₀ + BitVec.ofNat 64 128, 8⟩ (stR s₀) := Offset.sub_base _ (by omega)
  have hS : stateAt (leftMem s₀ s.mem) (st s₀) = ctr (S0 s₀) (NB s₀ + if T s₀ = 0 then 0 else 1) := by
    rw [stateAt_frame hfw (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by omega) (by omega)), h.state]
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · by_cases h5 : r = .s5
    · subst h5
      rw [u₈.other _ (by decide), u₇.gpr, m₆, sv' 8 (by decide)]
      exact h.saved.s5
    by_cases h6 : r = .s6
    · subst h6
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
        u₄.gpr, m₃, sv' 16 (by decide)]
      exact h.saved.s6
    by_cases h7 : r = .s7
    · subst h7
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, m₄,
        sv' 24 (by decide)]
      exact h.saved.s7
    by_cases h8 : r = .s8
    · subst h8
      rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, m₅, sv' 32 (by decide)]
      exact h.saved.s8
    have hk := preserved_kept r hr h5 h6 h7 h8
    rw [g r hk]
    exact h.keep r hk
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, m₂, sv' 0 (by decide)]
    exact h.saved.ra
  · have hd : ∀ k < L s₀, (leftMem s₀ s.mem) (dp s₀ + BitVec.ofNat 64 k) = s.mem (dp s₀ + BitVec.ofNat 64 k) :=
      fun k hk => hfw.bytes (R := dR s₀) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact (hp.st_d.symm.sub_right c128)) (show L s₀ ≤ 2 ^ 64 by omega) hk
    show keyAt _ _ = _ ∧ _
    rw [m₈]
    refine ⟨Proof.ChaCha20.keyAt_of_ctr hS, ?_⟩
    rw [ite_pos hle]
    refine ⟨by rw [u₈.gpr]; decide, apply_data hle fun k hk => ?_, apply_rest hle ?_ hS fun i hi => ?_⟩
    · rw [hd k hk, h.done k hk, ite_pos hk]
    · exact leftAt_store _ _ (by omega)
    · rw [leftMem, byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega),
        byte_writeW_ofNat _ _ _ (by omega) (by omega) (by omega), h.buf i hi]

theorem apply_eq : apply = .seq (.block check)
    (.ite (.nonzero .t4) (.block [.li .a0 0]) (.seq part1 (.seq part2 (.seq part3 (.block finish))))) :=
  rfl

theorem apply_correct {s₀ : State} (hp : APre s₀) : WP isa apply s₀ (Final s₀) := by
  rw [apply_eq]
  refine WP.seq (WP.mono (check_ok hp) fun s h => ?_)
  refine WP.ite (decide (N s₀ < L s₀)) (by
      rw [eval_nonzero_ofNat s .t4 (by cases decide (N s₀ < L s₀) <;> decide) h.t4]
      by_cases hh : N s₀ < L s₀ <;> simp [hh])
    (fun hlt => fail_ok (by simpa using hlt) h) (fun hge => ?_)
  have hle : L s₀ ≤ N s₀ := by simp only [decide_eq_false_iff_not] at hge; omega
  exact WP.seq (WP.mono (part1_ok hp hle h) fun s₁ h₁ => WP.seq (WP.mono (part2_ok hp h₁) fun s₂ h₂ =>
    WP.seq (WP.mono (part3_ok hp h₂) fun s₃ h₃ => finish_ok hp hle h₃)))

end VG.Proof.ChaCha20.RISCV64.Stream
