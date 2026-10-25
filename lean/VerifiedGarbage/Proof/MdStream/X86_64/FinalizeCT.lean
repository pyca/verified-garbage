module

public import VerifiedGarbage.Proof.MdStream.X86_64.PadExec
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Sha256.Stream
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MdStream.X86_64.PadExec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Sha256.Stream
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Streaming Merkle–Damgård hash functions on x86-64: `finalize`

The functional correctness of `finalize`, for any hash function (`Md`) whose
code stores the length field and writes the digest as `Shape` says, and any
correct compression function (`CalleeOk`).
-/

@[expose] public section

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
abbrev stR : Region := ⟨st s₀, P.N + P.B⟩
abbrev outR (D : Nat) : Region := ⟨out s₀, D⟩
abbrev scR : Region := ⟨scr s₀, P.so + 48⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
/-- Where the call of the compression function stores its return address. -/
abbrev stkR : Region := below (s₀.gpr .rsp) 8
/-- The buffer. -/
abbrev buf : Addr := st s₀ + BitVec.ofNat 64 P.N

/-- The end of the zeros in a block: before the length field in the last
block (`k = 0`). -/
def lim (k : Nat) : Nat := if k = 0 then P.B - P.L else P.B

end

section
variable {P : Params} (H : Md P.B P.N P.L) (s₀ : State)

/-- The messages the initial state represents, from `iv`. -/
def R₀ (iv : H.HV) (m : List Byte) : Prop :=
  H.Repr iv s₀.mem (st s₀) m ∧ s₀.gpr .rsi = BitVec.ofNat 64 m.length

/-- The final hash value, if `n` bytes are buffered in a block that is not the
last, followed by `mk`. -/
def Fin1 (mem : Mem) (n : Nat) (mk : Byte) (m : List Byte) : H.HV :=
  H.compress (H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ [mk] ++ List.replicate (P.B - 1 - n) 0).getD t 0))
    (H.parse fun t => (List.replicate (P.B - P.L) 0 ++ H.lenBytes m.length).getD t 0)

/-- The final hash value, if `n` bytes are buffered in the last block, followed
by `mk`. -/
def Fin0 (mem : Mem) (n : Nat) (mk : Byte) (m : List Byte) : H.HV :=
  H.compress (H.stateAt mem (st s₀))
    (H.parse fun t => (bytesAt mem (buf P s₀) n ++ [mk] ++ List.replicate (P.B - P.L - 1 - n) 0 ++
      H.lenBytes m.length).getD t 0)

end

structure PreD (P : Params) (D : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [stR P s₀, outR s₀ D, scR P s₀]
  st_out : (stR P s₀).Disjoint (outR s₀ D)
  st_scr : (stR P s₀).Disjoint (scR P s₀)
  out_scr : (outR s₀ D).Disjoint (scR P s₀)
  ret_st : (retR s₀).Disjoint (stR P s₀)
  ret_out : (retR s₀).Disjoint (outR s₀ D)
  ret_scr : (retR s₀).Disjoint (scR P s₀)
  stk_st : (stkR s₀).Disjoint (stR P s₀)
  stk_out : (stkR s₀).Disjoint (outR s₀ D)
  stk_scr : (stkR s₀).Disjoint (scR P s₀)

/-- The precondition for the whole final hash value (`finK`). -/
abbrev Pre (P : Params) (s₀ : State) : Prop := PreD P P.N s₀

theorem pre_ofD {P : Params} {H : Md P.B P.N P.L} {D : Nat} {s₀ : State} (h : (finKD H D).pre s₀) :
    PreD P D s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem pre_of {P : Params} {H : Md P.B P.N P.L} {s₀ : State} (h : (finK H).pre s₀) : Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- The return address and the 8 bytes below it. -/
theorem ret_stk (s₀ : State) : (retR s₀).Disjoint (stkR s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 8) (d := 8) (n := 8) (k := 8)
    (Nat.le_refl _) (by omega_arith)
  rwa [BitVec.sub_add_cancel] at this

/-! ## Invariants -/

structure Common (P : Params) (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rbx : s.gpr .rbx = st s₀
  r15 : s.gpr .r15 = scr s₀
  rbp : s.gpr .rbp = out s₀
  r12 : s.gpr .r12 = s₀.gpr .rsi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  frame : Frame [stR P s₀, scR P s₀, stkR s₀] s₀.mem s.mem
  saved : Saved P s₀ .rcx s.mem

/-- The loop invariant: `k = 1` while the block being padded is not the last
one, with `n` bytes of it buffered and `mk` (in `r9`) the byte after them:
`0x80` in the first block, `0` in the second. -/
structure LInv {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k n mk : Nat) (s : State) : Prop
    extends Common P s₀ s where
  k_le : k ≤ 1
  n_lt : n < lim P k
  mk_lt : mk < 256
  r13 : s.gpr .r13 = BitVec.ofNat 64 n
  r9 : s.gpr .r9 = BitVec.ofNat 64 mk
  r14 : s.gpr .r14 = BitVec.ofNat 64 k
  hash : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m =
    H.digest (if k = 1 then Fin1 H s₀ s.mem n (BitVec.ofNat 8 mk) m else Fin0 H s₀ s.mem n (BitVec.ofNat 8 mk) m)

/-- All blocks are compressed. -/
def Done {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (s : State) : Prop :=
  Common P s₀ s ∧ ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.hash iv m = H.digest (H.stateAt s.mem (st s₀))

section
variable {P : Params} {H : Md P.B P.N P.L} {D : Nat}

theorem lim_le (k : Nat) : lim P k ≤ P.B := by unfold lim; split <;> omega_arith
theorem lim_ge (k : Nat) : P.B - P.L ≤ lim P k := by unfold lim; split <;> omega_arith

theorem buf_add (s₀ : State) (n : Nat) : buf P s₀ + BitVec.ofNat 64 n = st s₀ + BitVec.ofNat 64 (P.N + n) :=
  add_ofNat _ _ _

theorem Common.of_gpr {s₀ : State} {s s' : State} (h : Common P s₀ s)
    (hg : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common P s₀ s' where
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
theorem Common.writeBuf (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) {s : State} (h : Common P s₀ s) {n : Nat}
    {xs : List Byte} (hn : n + xs.length ≤ P.B) :
    Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Frame [stR P s₀, scR P s₀, stkR s₀] s₀.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) ∧
      Saved P s₀ .rcx (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
  have := hd.N; have := hd.B; have := hd.so
  have hf : Frame [stR P s₀] s.mem (writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) xs) := by
    refine writeBytes_frame _ _ _ ?_
    rw [buf_add]
    exact contains_offset (by omega_arith) (by omega_arith)
  refine ⟨hf, h.frame.trans (hf.mono (by simp)), fun p hp' => ?_⟩
  rw [← h.saved p hp']
  have hd' := saved_offset hd hp'
  refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r' hr'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
  subst hr'
  exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega_arith) (by omega_arith)))

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
  mem : s.mem = writeBytes sI.mem (buf P s₀ + BitVec.ofNat 64 n) (List.replicate j 0)

theorem zero_step (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) {sI : State} (hC : Common P s₀ sI) {n lim j : Nat}
    (hlim : lim ≤ P.B) (hj : j < lim - n) {s : State} (h : Zero P s₀ sI n lim j s) :
    WP isa (.block [.store8 (bufByte P) .r9, .alu .add .r13 (.imm 1), .alu .sub .rax (.imm 1)]) s fun s' =>
      Zero P s₀ sI n lim (j + 1) s' ∧ s'.zf = some (decide (lim - n - (j + 1) = 0)) := by
  have := hd.N; have := hd.B
  have hrbx : s.gpr .rbx = st s₀ := by rw [h.keep _ (by simp), hC.rbx]
  have hout : InRegions s.wr (buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 1 := by
    refine ⟨stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [add_ofNat, buf_add]
    exact contains_offset (by omega_arith) (by omega_arith)
  refine wp_store8 (r := .r9) (a := buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_ hout
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  · simp only [State.ea, bufByte, buf, hrbx, h.r13, BitVec.ofNat_add, BitVec.mul_one, ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ hz₃ => WP.block_nil ⟨⟨by omega_arith, fun r hr => ?_,
    by rw [u₃.rd, u₂.rd, rd₁, h.rd], by rw [u₃.wr, u₂.wr, wr₁, h.wr], ?_, ?_, ?_, ?_⟩, ?_⟩
  · have : r ≠ .rax ∧ r ≠ .r13 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₃.other r this.1, u₂.other r this.2, g₁, h.keep r hr]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.r9]
  · rw [u₃.other _ (by decide), u₂.gpr, g₁, h.r13, sx1, ← Nat.add_assoc, ofNat_succ]
  · rw [u₃.gpr, u₂.other _ (by decide), g₁, h.rax, sx1, ofNat_pred (by omega_arith), Nat.sub_sub]
  · rw [u₃.mem, u₂.mem, m₁, h.r9, h.mem, List.replicate_succ',
      writeBytes_snoc _ _ _ _ (by simp only [List.length_replicate]; omega_arith), List.length_replicate]
    rfl
  · rw [hz₃, u₂.other _ (by decide), g₁, h.rax, sx1, ofNat_pred (by omega_arith), ofNat_beq_zero (by omega_arith),
      Nat.sub_sub, Nat.sub_sub]

theorem zero_ok (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) {sI : State} (hC : Common P s₀ sI) {n lim : Nat}
    (hlim : lim ≤ P.B) {j₀ : Nat} (hj₀ : j₀ ≤ lim - n) {s : State} (h : Zero P s₀ sI n lim j₀ s)
    (hz : s.zf = some (decide (lim - n - j₀ = 0))) :
    WP isa (.ite .e (.block []) (zeroLoop P)) s (Zero P s₀ sI n lim (lim - n)) := by
  refine WP.ite (decide (lim - n - j₀ = 0)) hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rwa [show lim - n = j₀ by omega_arith])
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa) (fun k s => ∃ j, k = lim - n - j ∧ j < lim - n ∧ Zero P s₀ sI n lim j s)
      ?_ (lim - n - j₀) s ⟨j₀, rfl, by omega_arith, h⟩
    rintro k s ⟨j, rfl, hj, hZ⟩
    refine WP.mono (zero_step hd hp hC hlim hj hZ) fun s' ⟨hZ', hz'⟩ => ?_
    by_cases hl : lim - n - (j + 1) = 0
    · refine .inl ⟨by simp [eval, hz', hl], ?_⟩
      rwa [show j + 1 = lim - n by omega_arith] at hZ'
    · exact .inr ⟨by simp [eval, hz', hl], _, by omega_arith, j + 1, rfl, by omega_arith, hZ'⟩

set_option simprocs false in
/-- Eight bytes zeroed. -/
theorem zero_word_step (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) {sI : State} (hC : Common P s₀ sI)
    {n lim j : Nat} (hlim : lim ≤ P.B) (hj : j + 8 ≤ lim - n) {s : State} (h : Zero P s₀ sI n lim j s) :
    WP isa (.block [.store (bufByte P) .r9, .alu .add .r13 (.imm 8), .alu .sub .rax (.imm 8),
      .alu .cmp .rax (.imm 8)]) s fun s' =>
      Zero P s₀ sI n lim (j + 8) s' ∧ s'.cf = some (decide (lim - n - (j + 8) < 8)) := by
  have := hd.N; have := hd.B
  have hrbx : s.gpr .rbx = st s₀ := by rw [h.keep _ (by simp), hC.rbx]
  have hout : InRegions s.wr (buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) 8 := by
    refine ⟨stR P s₀, by simp [h.wr, hC.wr, hp.wr], ?_⟩
    rw [add_ofNat, buf_add]
    exact contains_offset (by omega_arith) (by omega_arith)
  refine wp_store (r := .r9) (a := buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j) ?_ hout
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  · simp only [State.ea, bufByte, buf, hrbx, h.r13, BitVec.ofNat_add, BitVec.mul_one, ofInt_natCast]
    ac_rfl
  refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ _ => wp_cmpi fun s₄ g₄ m₄ rd₄ wr₄ cf₄ _ =>
    WP.block_nil ?_
  have hrax₃ : s₃.gpr .rax = BitVec.ofNat 64 (lim - n - (j + 8)) := by
    rw [u₃.gpr, u₂.other _ (by decide), g₁, h.rax, sx8, sub_ofNat (by omega_arith), Nat.sub_sub]
  refine ⟨⟨by omega_arith, fun r hr => ?_, by rw [rd₄, u₃.rd, u₂.rd, rd₁, h.rd], by rw [wr₄, u₃.wr, u₂.wr, wr₁, h.wr],
    ?_, ?_, by rw [g₄, hrax₃], ?_⟩, ?_⟩
  · have : r ≠ .rax ∧ r ≠ .r13 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [g₄, u₃.other r this.1, u₂.other r this.2, g₁, h.keep r hr]
  · rw [g₄, u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.r9]
  · rw [g₄, u₃.other _ (by decide), u₂.gpr, g₁, h.r13, sx8, ← BitVec.ofNat_add, Nat.add_assoc]
  · have e : (List.range 8).map (fun k => (0 : BitVec 64).extractLsb' (8 * k) 8) = List.replicate 8 0 := by
      decide
    rw [m₄, u₃.mem, u₂.mem, m₁, h.r9, writeW_eq_writeBytes, e, h.mem,
      show buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 j =
        buf P s₀ + BitVec.ofNat 64 n + BitVec.ofNat 64 (List.replicate j (0 : Byte)).length by
        rw [List.length_replicate],
      writeBytes_append _ _ _ _ (by simp only [List.length_replicate]; omega_arith), List.replicate_append_replicate]
  · rw [cf₄, hrax₃, sx8, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]

/-- Eight bytes at a time, while at least eight are left. -/
theorem zero_words_ok (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) {sI : State} (hC : Common P s₀ sI)
    {n lim : Nat} (hlim : lim ≤ P.B) {s : State} (h : Zero P s₀ sI n lim 0 s)
    (hcf : s.cf = some (decide (lim - n < 8))) :
    WP isa (.ite .b (.block []) (zeroWords P)) s (Zero P s₀ sI n lim (8 * ((lim - n) / 8))) := by
  refine WP.ite (decide (lim - n < 8)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    exact WP.block_nil (by rw [show (lim - n) / 8 = 0 by omega_arith]; exact h)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.loop (M := isa)
      (fun k s => ∃ i, k = (lim - n) / 8 - i ∧ i < (lim - n) / 8 ∧ Zero P s₀ sI n lim (8 * i) s)
      ?_ ((lim - n) / 8) s ⟨0, rfl, by omega_arith, h⟩
    rintro k s ⟨i, rfl, hi, hZ⟩
    refine WP.mono (zero_word_step hd hp hC hlim (by omega_arith) hZ) fun s' ⟨hZ', hcf'⟩ => ?_
    rw [show 8 * i + 8 = 8 * (i + 1) by omega_arith] at hZ' hcf'
    by_cases hl : (lim - n) / 8 - (i + 1) = 0
    · refine .inl ⟨by simp [eval, hcf']; omega_arith, ?_⟩
      rwa [show i + 1 = (lim - n) / 8 by omega_arith] at hZ'
    · exact .inr ⟨by simp [eval, hcf']; omega_arith, _, by omega_arith, i + 1, rfl, by omega_arith, hZ'⟩

/-- All `lim - n` bytes: eight at a time, then one at a time. -/
theorem zero_all_ok (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) {sI : State} (hC : Common P s₀ sI)
    {n lim : Nat} (hlim : lim ≤ P.B) (hn : n ≤ lim) {s : State} (h : Zero P s₀ sI n lim 0 s) :
    WP isa (zero P) s (Zero P s₀ sI n lim (lim - n)) := by
  have := hd.B
  unfold zero
  refine WP.seq (wp_cmpi fun s₁ g₁ m₁ rd₁ wr₁ cf₁ _ => WP.block_nil ?_)
  have keep : ∀ {s s' : State} {j : Nat}, Zero P s₀ sI n lim j s → s'.gpr = s.gpr → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → Zero P s₀ sI n lim j s' := fun h g m rd wr =>
    ⟨h.j_le, fun r hr => by rw [g, h.keep r hr], by rw [rd, h.rd], by rw [wr, h.wr], by rw [g, h.r9],
      by rw [g, h.r13], by rw [g, h.rax], by rw [m, h.mem]⟩
  have hcf₁ : s₁.cf = some (decide (lim - n < 8)) := by
    rw [cf₁, h.rax, Nat.sub_zero, sx8, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]
  refine WP.seq (WP.mono (zero_words_ok hd hp hC hlim (keep h g₁ m₁ rd₁ wr₁) hcf₁) fun s₂ hZ₂ => ?_)
  refine WP.seq (wp_test fun s₃ g₃ m₃ rd₃ wr₃ z₃ => WP.block_nil ?_)
  have hz₃ : s₃.zf = some (decide (lim - n - 8 * ((lim - n) / 8) = 0)) := by
    rw [z₃, hZ₂.rax, BitVec.and_self, ofNat_beq_zero (by omega_arith)]
  exact zero_ok hd hp hC hlim (by omega_arith) (keep hZ₂ g₃ m₃ rd₃ wr₃) hz₃

/-! ## One block -/

/-- The call of the compression function's requirements. -/
theorem Common.callOk (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) {s : State} (hC : Common P s₀ s)
    (hrsi : s.gpr .rsi = buf P s₀) : CallOk P s (st s₀) (scr s₀) (buf P s₀) := by
  have := hd.N; have := hd.B; have := hd.so
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega_arith)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega_arith)
  have eb : Region.Sub ⟨buf P s₀, P.B⟩ (stR P s₀) := sub_offset (off := P.N) (by omega_arith) (by omega_arith)
  have hsp := hC.rsp
  refine ⟨hC.rbx, hC.r15, hrsi, (hp.st_scr.sub_left eN).sub_right eso, ?_,
    (hp.st_scr.sub_left eb).sub_right eso, by rw [hsp]; exact hp.stk_st.sub_right eN,
    by rw [hsp]; exact hp.stk_scr.sub_right eso, by rw [hsp]; exact hp.stk_st.sub_right eb, ?_, ?_⟩
  · exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)
  · rw [hC.rd, hC.wr, hp.rd, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR P s₀, by simp, P.N, rfl, by simp⟩
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩
  · rw [hC.wr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR P s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scR P s₀, by simp, 0, by simp, by simp⟩

/-- The compression of the buffer. -/
theorem compress_buf (hd : Dims P) {name : String} {code : Prog isa} (hf : CalleeOk H code) {s₀ : State}
    (hp : PreD P D s₀) {s : State} (hC : Common P s₀ s) (hrsi : s.gpr .rsi = buf P s₀) {Q : State → Prop}
    (hQ : ∀ s', Common P s₀ s' → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      H.stateAt s'.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.blockAt s.mem (buf P s₀)) →
      s'.gpr .rdi = st s₀ → s'.gpr .rcx = scr s₀ → Q s') :
    WP isa (compressAt name code) s Q := by
  have := hd.N; have := hd.B; have := hd.so
  have eN : Region.Sub ⟨st s₀, P.N⟩ (stR P s₀) := Region.sub_prefix (by omega_arith)
  have eso : Region.Sub ⟨scr s₀, P.so⟩ (scR P s₀) := Region.sub_prefix (by omega_arith)
  have hsp := hC.rsp
  refine compressAt_ok H hf (hC.callOk hd hp hrsi) (by omega_arith) (by omega_arith)
    fun s' hrd hwr hcs hf hstate hdi hcx => hQ s' ?_ hcs hstate hdi hcx
  have cs : ∀ r, r ∈ calleeSaved → s'.gpr r = s.gpr r := hcs
  refine ⟨hrd.trans hC.rd, hwr.trans hC.wr, by rw [cs _ (by decide)]; exact hC.rbx,
    by rw [cs _ (by decide)]; exact hC.r15, by rw [cs _ (by decide)]; exact hC.rbp,
    by rw [cs _ (by decide)]; exact hC.r12, by rw [cs _ (by decide)]; exact hC.rsp,
    hC.frame.trans (hf.sub ?_), fun p hp' => ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR P s₀, by simp, eN⟩
    · exact ⟨scR P s₀, by simp, eso⟩
    · exact ⟨stkR s₀, by simp, by rw [hsp]; exact fun _ h => h⟩
  · rw [← hC.saved p hp']
    have hd' := saved_offset hd hp'
    refine hf.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_
      (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega_arith) (by omega_arith))).sub_right eN
    · rw [ofInt_natCast]; exact Offset.disjoint_base _ hd'.1 (by omega_arith)
    · rw [hsp]
      exact hp.stk_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega_arith) (by omega_arith))

end

/-! ## Padding a byte at a time -/

/-- A byte after writing `xs` at `p + a`. -/
theorem wb_at (m : Mem) (p : Addr) (xs : List Byte) {a i : Nat} (ha : a + xs.length < 2 ^ 63)
    (hi : i < 2 ^ 63) :
    writeBytes m (p + BitVec.ofNat 64 a) xs (p + BitVec.ofNat 64 i) =
      if a ≤ i ∧ i < a + xs.length then xs.getD (i - a) 0 else m (p + BitVec.ofNat 64 i) := by
  split
  · rename_i h
    rw [show p + BitVec.ofNat 64 i = p + BitVec.ofNat 64 a + BitVec.ofNat 64 (i - a) by
      rw [add_ofNat, Nat.add_sub_cancel' h.1]]
    simp only [VG.WriteBytes.writeBytes, Offset.add_sub_cancel_left, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i - a < 2 ^ 64 by omega_arith), show i - a < xs.length by omega_arith, ite_true]
  · rename_i h
    simp only [VG.WriteBytes.writeBytes]
    rw [ite_f]
    rw [Offset.sub_toNat' p (by omega_arith) (by omega_arith)]
    split <;> omega_arith

theorem lenPart_high (P : Params) (lv : List Byte) (hlv : lv.length = P.L) (hL : P.L ≤ 16) {j : Nat}
    (hj : 16 - P.L ≤ j) : lenPart P 0 lv j = lv.getD (j - (16 - P.L)) 0 := by
  simp only [lenPart, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_append_right
    (show (List.replicate (16 - P.L) (0 : Byte)).length ≤ j by simp; omega), List.length_replicate]

section
variable {P : Params} {H : Md P.B P.N P.L} {D : Nat}

/-- `bytePad` writes the block to compress: `mk` after the `n` bytes
buffered, zeros, and in the last block (`k = 0`) the length field. -/
theorem byte_exec (hd : Dims P) (hs : ShapeD H D) {s₀ : State} (hp : PreD P D s₀) {k n mk : Nat} {s : State}
    (h : LInv H s₀ k n mk s) {Q : State → Prop}
    (kont : ∀ s', (∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp, .r14], s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → Frame [⟨buf P s₀, P.B⟩] s.mem s'.mem →
      (∀ i < P.B, s'.mem (st s₀ + BitVec.ofNat 64 (P.N + i)) =
        if i < n then s.mem (st s₀ + BitVec.ofNat 64 (P.N + i))
        else if i = n then BitVec.ofNat 8 mk
        else if P.B - 16 ≤ i then lenPart P k (H.lenOf (s.gpr .r12)) (i - (P.B - 16)) else 0) →
      Q s') :
    WP isa (bytePad P) s Q := by
  have hk := h.k_le; have hn := h.n_lt; have hC := h.toCommon
  have := hd.N; have := hd.B; have := hd.L; have := hd.so
  have hlim := lim_le (P := P) k; have hlg := lim_ge (P := P) k
  have hrbx : s.gpr .rbx = st s₀ := hC.rbx
  unfold bytePad
  -- The marker.
  refine WP.seq (wp_store8 (a := buf P s₀ + BitVec.ofNat 64 n) (by rw [ea_bufByte P s h.r13, hrbx, buf_add])
    ⟨stR P s₀, by simp [hC.wr, hp.wr], by rw [buf_add]; exact contains_offset (by omega_arith) (by omega_arith)⟩
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_)
  have em₁ : s₁.mem = writeBytes s.mem (buf P s₀ + BitVec.ofNat 64 n) [BitVec.ofNat 8 mk] := by
    rw [m₁, h.r9, ← List.nil_append [BitVec.ofNat 8 mk], writeBytes_snoc _ _ _ _ (by decide), writeBytes_nil,
      List.length_nil, BitVec.add_zero]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega_arith
  obtain ⟨_, fA₁, sv₁⟩ := Common.writeBuf hd hp hC (n := n) (xs := [BitVec.ofNat 8 mk]) (by simp; omega_arith)
  have hC₁ : Common P s₀ s₁ := ⟨rd₁.trans hC.rd, wr₁.trans hC.wr, by rw [g₁, hC.rbx], by rw [g₁, hC.r15],
    by rw [g₁, hC.rbp], by rw [g₁, hC.r12], by rw [g₁, hC.rsp], by rw [em₁]; exact fA₁, by rw [em₁]; exact sv₁⟩
  refine wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ => wp_test fun s₄ g₄ m₄ rd₄ wr₄ z₄ => WP.block_nil ?_
  have hz₄ : s₄.zf = some (decide (k = 0)) := by
    rw [z₄, u₃.other _ (by decide), u₂.other _ (by decide), g₁, h.r14, BitVec.and_self,
      ofNat_beq_zero (by omega_arith)]
  -- `rax` = the end of the zeros.
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => s₅.gpr .rax = BitVec.ofNat 64 (lim P k) ∧
      (∀ r, r ≠ .rax → s₅.gpr r = s₄.gpr r) ∧ s₅.mem = s₄.mem ∧ s₅.rd = s₄.rd ∧ s₅.wr = s₄.wr) ?_
    fun s₅ ⟨a₅, g₅, m₅, rd₅, wr₅⟩ => ?_)
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₄]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mov32i fun s₅ u₅ _ _ => WP.block_nil ⟨?_, fun r hr => u₅.other r hr, u₅.mem, u₅.rd, u₅.wr⟩
      rw [u₅.gpr, zx_ofNat (by omega_arith), lim, ite_t hb]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
      rw [g₄, u₃.gpr, zx_ofNat (by omega_arith), lim, ite_f hb]
  refine WP.seq (wp_mov32i fun s₆ u₆ _ _ => wp_sub fun s₇ u₇ _ => WP.block_nil ?_)
  have keep₇ : ∀ r, r ≠ .rax → r ≠ .r9 → r ≠ .r13 → s₇.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₇.other r h1, u₆.other r h2, g₅ r h1, g₄, u₃.other r h1, u₂.other r h3, g₁]
  have hm₇ : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, m₅, m₄, u₃.mem, u₂.mem]
  have hC₇ : Common P s₀ s₇ := hC₁.of_gpr (fun r hr => by
      have : r ≠ .rax ∧ r ≠ .r9 ∧ r ≠ .r13 := by
        simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
      rw [keep₇ r this.1 this.2.1 this.2.2, g₁]) hm₇
    (by rw [u₇.rd, u₆.rd, rd₅, rd₄, u₃.rd, u₂.rd]) (by rw [u₇.wr, u₆.wr, wr₅, wr₄, u₃.wr, u₂.wr])
  have hZ₇ : Zero P s₀ s₇ (n + 1) (lim P k) 0 s₇ := by
    refine ⟨by omega_arith, fun _ _ => rfl, rfl, rfl, ?_, ?_, ?_, by rw [List.replicate_zero, writeBytes_nil]⟩
    · rw [u₇.other _ (by decide), u₆.gpr]; rfl
    · rw [u₇.other _ (by decide), u₆.other _ (by decide), g₅ _ (by decide), g₄, u₃.other _ (by decide), u₂.gpr, g₁,
        h.r13, sx1, Nat.add_zero, ofNat_succ]
    · rw [u₇.gpr, u₆.other _ (by decide), u₆.other _ (by decide), a₅, g₅ _ (by decide), g₄, u₃.other _ (by decide),
        u₂.gpr, g₁, h.r13, sx1, ← ofNat_succ, sub_ofNat (by omega_arith), Nat.sub_zero]
  -- The zeros.
  refine WP.seq (WP.mono (zero_all_ok hd hp hC₇ hlim (by omega_arith) hZ₇) fun s₈ hZ₈ => ?_)
  refine WP.seq (wp_test fun s₉ g₉ m₉ rd₉ wr₉ z₉ => WP.block_nil ?_)
  have hrbx₉ : s₉.gpr .rbx = st s₀ := by rw [g₉, hZ₈.keep _ (by simp), keep₇ _ (by decide) (by decide) (by decide), hrbx]
  have hr12₉ : s₉.gpr .r12 = s.gpr .r12 := by
    rw [g₉, hZ₈.keep _ (by simp), keep₇ _ (by decide) (by decide) (by decide)]
  have hz₉ : s₉.zf = some (decide (k = 0)) := by
    rw [z₉, hZ₈.keep _ (by simp), keep₇ _ (by decide) (by decide) (by decide), h.r14, BitVec.and_self,
      ofNat_beq_zero (by omega_arith)]
  have hm₉ : s₉.mem = writeBytes s₁.mem (buf P s₀ + BitVec.ofNat 64 (n + 1)) (List.replicate (lim P k - (n + 1)) 0) := by
    rw [m₉, hZ₈.mem, hm₇]
  -- The length field.
  refine WP.mono (Q := fun (s₁₀ : State) => (∀ r, r ≠ .rax → s₁₀.gpr r = s₉.gpr r) ∧ s₁₀.rd = s₉.rd ∧
      s₁₀.wr = s₉.wr ∧ s₁₀.mem = if k = 0 then writeBytes s₉.mem (st s₀ + BitVec.ofNat 64 (P.N + P.B - P.L))
        (H.lenOf (s.gpr .r12)) else s₉.mem) ?_ fun s₁₀ ⟨g₁₀, rd₁₀, wr₁₀, m₁₀⟩ => ?_
  · refine WP.ite (decide (k = 0)) (by simp [eval, hz₉]) (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine WP.mono (hs.len s₉ ⟨stR P s₀, by simp [wr₉, hZ₈.wr, hC₇.wr, hp.wr], by
        rw [hrbx₉]; exact contains_offset (by omega_arith) (by omega_arith)⟩) fun s₁₀ ⟨g, rd, wr, m⟩ =>
        ⟨g, rd, wr, by rw [m, ite_t hb, hrbx₉, hr12₉]⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, by rw [ite_f hb]⟩
  have hlv := H.lenOf_length (s.gpr .r12)
  -- The bytes before the length field.
  have hM : ∀ i < P.B, s₉.mem (st s₀ + BitVec.ofNat 64 (P.N + i)) =
      if i < n then s.mem (st s₀ + BitVec.ofNat 64 (P.N + i)) else if i = n then BitVec.ofNat 8 mk
      else if i < lim P k then 0 else s.mem (st s₀ + BitVec.ofNat 64 (P.N + i)) := by
    intro i hi
    rw [hm₉, buf_add, wb_at _ _ _ (by simp; omega_arith) (by omega_arith), em₁, buf_add,
      wb_at _ _ _ (by simp; omega_arith) (by omega_arith)]
    simp only [List.length_replicate, List.length_singleton]
    by_cases h1 : i < n
    · rw [ite_f (by omega_arith), ite_f (by omega_arith), ite_t h1]
    · rw [ite_f h1]
      by_cases h2 : i = n
      · subst h2
        rw [ite_f (by omega_arith), ite_t (by omega_arith), ite_t rfl]
        simp
      · rw [ite_f h2]
        by_cases h3 : i < lim P k
        · rw [ite_t (by omega_arith), ite_t h3]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
          split <;> rfl
        · rw [ite_f (by omega_arith), ite_f (by omega_arith), ite_f h3]
  refine kont s₁₀ (fun r hr => ?_) ?_ ?_ ?_ fun i hi => ?_
  · have : r ≠ .rax ∧ r ≠ .r9 ∧ r ≠ .r13 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h | h | h | h | h | h <;> subst h <;> decide
    rw [g₁₀ r this.1, g₉, hZ₈.keep r hr, keep₇ r this.1 this.2.1 this.2.2]
  · rw [rd₁₀, rd₉, hZ₈.rd, u₇.rd, u₆.rd, rd₅, rd₄, u₃.rd, u₂.rd, rd₁]
  · rw [wr₁₀, wr₉, hZ₈.wr, u₇.wr, u₆.wr, wr₅, wr₄, u₃.wr, u₂.wr, wr₁]
  · -- Only the buffer changes.
    have c : ∀ {a l : Nat}, a + l ≤ P.B → (⟨buf P s₀, P.B⟩ : Region).Contains (buf P s₀ + BitVec.ofNat 64 a) l :=
      fun h => contains_offset h (by omega_arith)
    have f₁ : Frame [⟨buf P s₀, P.B⟩] s.mem s₉.mem := by
      rw [hm₉, em₁]
      exact (writeBytes_frame _ _ _ (c (by simp; omega_arith))).trans
        (writeBytes_frame _ _ _ (c (by simp; omega_arith)))
    rw [m₁₀]
    split
    · refine f₁.trans (writeBytes_frame _ _ _ ?_)
      rw [hlv, show st s₀ + BitVec.ofNat 64 (P.N + P.B - P.L) = buf P s₀ + BitVec.ofNat 64 (P.B - P.L) by
        rw [buf_add, show P.N + (P.B - P.L) = P.N + P.B - P.L by omega_arith]]
      exact c (by omega_arith)
    · exact f₁
  · rw [m₁₀]
    by_cases hk0 : k = 0
    · subst hk0
      have hlim0 : lim P 0 = P.B - P.L := by simp [lim]
      rw [ite_t rfl, show P.N + P.B - P.L = P.N + (P.B - P.L) by omega_arith,
        wb_at _ _ _ (by rw [hlv]; omega_arith) (by omega_arith), hlv]
      by_cases hl : P.B - P.L ≤ i
      · rw [ite_t ⟨by omega_arith, by omega_arith⟩, ite_f (by omega_arith), ite_f (by omega_arith), ite_t (by omega_arith),
          lenPart_high P _ hlv hd.L.2 (by omega_arith), show P.N + i - (P.N + (P.B - P.L)) = i - (P.B - 16) - (16 - P.L) by
            omega_arith]
      · rw [ite_f (by omega_arith), hM i hi, hlim0]
        by_cases h1 : i < n
        · rw [ite_t h1, ite_t h1]
        · rw [ite_f h1, ite_f h1]
          by_cases h2 : i = n
          · rw [ite_t h2, ite_t h2]
          · rw [ite_f h2, ite_f h2, ite_t (by omega_arith)]
            split
            · exact (lenPart_low P 0 _ (by omega_arith)).symm
            · rfl
    · rw [ite_f hk0, hM i hi]
      have hlim1 : lim P k = P.B := by simp [lim, hk0]
      rw [hlim1]
      by_cases h1 : i < n
      · rw [ite_t h1, ite_t h1]
      · rw [ite_f h1, ite_f h1]
        by_cases h2 : i = n
        · rw [ite_t h2, ite_t h2]
        · rw [ite_f h2, ite_f h2, ite_t hi]
          split
          · simp [lenPart, hk0]
          · rfl

end

/-- The loop's postcondition for one iteration. -/
def Step {P : Params} (H : Md P.B P.N P.L) (s₀ : State) (k : Nat) (s : State) : Prop :=
  (k = 0 ∧ eval .e s = some false ∧ Done H s₀ s ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rcx = scr s₀) ∨
    (k = 1 ∧ eval .e s = some true ∧ LInv H s₀ 0 0 0 s)

/-- Before the call of the compression function: the block to compress is
ready in the buffer, and compressing it finishes the iteration. -/
def Mid {P : Params} (H : Md P.B P.N P.L) (name : String) (code : Prog isa) (s₀ : State) (k : Nat)
    (s : State) : Prop :=
  Common P s₀ s ∧ s.gpr .rsi = buf P s₀ ∧
    WP isa (.seq (compressAt name code) (.block [.mov32 .r13 (.imm 0), .mov32 .r9 (.imm 0), .alu .sub .r14 (.imm 1)])) s
      (Step H s₀ k)

section
variable {P : Params} {H : Md P.B P.N P.L} {D : Nat}

/-- `and` of an immediate, and the zero flag it sets. -/
theorem wp_andiZ {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d &&& v.signExtend 64) → s'.zf = some (s.gpr d &&& v.signExtend 64 == 0) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d (.imm v) :: is)) s Q :=
  WP.cons rfl (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem pad_ok (hd : Dims P) (hs : ShapeD H D) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : PreD P D s₀) {k n mk : Nat} {s : State} (h : LInv H s₀ k n mk s) :
    WP isa (finalizePad P) s (Mid H name code s₀ k) := by
  have hk := h.k_le; have hn := h.n_lt
  have hC := h.toCommon
  have := hd.N; have := hd.B; have := hd.L; have := hd.so
  have hlim := lim_le (P := P) k
  have hn' : n < if k = 0 then P.B - P.L else P.B := by
    unfold lim at hn; by_cases hk0 : k = 0 <;> simp_all
  have hrbx : s.gpr .rbx = st s₀ := hC.rbx
  -- What both paddings leave, and the block's address.
  have cont : ∀ s', (∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp, .r14], s'.gpr r = s.gpr r) → s'.rd = s.rd →
      s'.wr = s.wr → Frame [⟨buf P s₀, P.B⟩] s.mem s'.mem →
      (∀ i < P.B, s'.mem (st s₀ + BitVec.ofNat 64 (P.N + i)) =
        if i < n then s.mem (st s₀ + BitVec.ofNat 64 (P.N + i))
        else if i = n then BitVec.ofNat 8 mk
        else if P.B - 16 ≤ i then lenPart P k (H.lenOf (s.gpr .r12)) (i - (P.B - 16)) else 0) →
      WP isa (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 P.N))]) s'
        (Mid H name code s₀ k) := by
    intro s'' g'' rd'' wr'' fr' by'
    refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s' u' => WP.block_nil ?_
    have g' : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp, .r14], s'.gpr r = s.gpr r := fun r hr => by
      have : r ≠ .rsi := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h <;> subst h <;> decide
      rw [u'.other r this, u₁.other r this, g'' r hr]
    have rsi' : s'.gpr .rsi = buf P s₀ := by
      rw [u'.gpr, u₁.gpr, g'' _ (by simp), hrbx, sx_ofNat (by omega_arith)]
    have rd' : s'.rd = s.rd := by rw [u'.rd, u₁.rd, rd'']
    have wr' : s'.wr = s.wr := by rw [u'.wr, u₁.wr, wr'']
    have hm' : s'.mem = s''.mem := by rw [u'.mem, u₁.mem]
    rw [← hm'] at fr' by'
    have eb : Region.Sub ⟨buf P s₀, P.B⟩ (stR P s₀) := sub_offset (off := P.N) (by omega_arith) (by omega_arith)
    have hframe : Frame [stR P s₀] s.mem s'.mem :=
      fr'.sub fun r hr => ⟨stR P s₀, by simp, by simp only [List.mem_singleton] at hr; subst hr; exact eb⟩
    have keep : ∀ r ∈ [Reg.rbx, .r15, .rbp, .r12, .rsp], s'.gpr r = s.gpr r := by
      intro r hr
      refine g' r ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h | h <;> simp [h]
    have hC' : Common P s₀ s' := by
      refine ⟨rd'.trans hC.rd, wr'.trans hC.wr, by rw [keep _ (by simp), hC.rbx], by rw [keep _ (by simp), hC.r15],
        by rw [keep _ (by simp), hC.rbp], by rw [keep _ (by simp), hC.r12], by rw [keep _ (by simp), hC.rsp],
        hC.frame.trans (hframe.mono (by simp)), fun p hp' => ?_⟩
      rw [← hC.saved p hp']
      have hd' := saved_offset hd hp'
      refine hframe.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (p.2 : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
      intro r' hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      subst hr'
      exact (hp.st_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega_arith) (by omega_arith)))
    have hst' : H.stateAt s'.mem (st s₀) = H.stateAt s.mem (st s₀) := by
      apply H.stateAt_congr
      intro i hi
      exact fr'.bytes (R := ⟨st s₀, P.N⟩) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (Nat.le_refl _) (by omega_arith)) (by show P.N ≤ 2 ^ 64; omega_arith) hi
    have hby' : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → bytesAt s'.mem (buf P s₀) P.B =
        bytesAt s.mem (buf P s₀) n ++ [BitVec.ofNat 8 mk] ++ (if k = 1 then List.replicate (P.B - 1 - n) 0 else
          List.replicate (P.B - P.L - 1 - n) 0 ++ H.lenBytes m.length) := by
      intro iv m hm hok
      have hl : H.lenOf (s.gpr .r12) = H.lenBytes m.length := by rw [hC.r12, hm.2, H.lenOf_eq _ hok]
      rw [← hl, bytesAt, bytesAt, ← pad_list (H.lenOf_length _) hd.L.2 (by omega_arith) hk hn']
      refine List.map_congr_left fun i hi => ?_
      simp only [List.mem_range] at hi
      rw [buf_add, by' i hi, ← buf_add]
      rfl
    refine ⟨hC', rsi', ?_⟩
    -- Compress the block.
    refine WP.seq (compress_buf hd hf hp hC' rsi' fun s₁₁ hC₁₁ cs₁₁ hst₁₁ hdi₁₁ hcx₁₁ => ?_)
    have h14₁₁ : s₁₁.gpr .r14 = BitVec.ofNat 64 k := by
      rw [cs₁₁ _ (by decide), g' _ (by simp), h.r14]
    have hblk : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length → H.blockAt s'.mem (buf P s₀) = H.parse fun t =>
        (bytesAt s.mem (buf P s₀) n ++ [BitVec.ofNat 8 mk] ++ (if k = 1 then List.replicate (P.B - 1 - n) 0 else
          List.replicate (P.B - P.L - 1 - n) 0 ++ H.lenBytes m.length)).getD t 0 := by
      intro iv m hm hok
      apply H.parse_congr
      intro t ht
      exact bytesAt_getD (hby' iv m hm hok) ht
    -- Next block, if any.
    refine wp_mov32i fun s₁₂ u₁₂ _ _ => wp_mov32i fun s₁₃ u₁₃ _ _ => wp_subi fun s₁₄ u₁₄ z₁₄ => WP.block_nil ?_
    have hC₁₄ : Common P s₀ s₁₄ := hC₁₁.of_gpr (fun r hr => by
        have : r ≠ .r14 ∧ r ≠ .r9 ∧ r ≠ .r13 := by
          simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide
        rw [u₁₄.other r this.1, u₁₃.other r this.2.1, u₁₂.other r this.2.2]) (by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem])
      (by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd]) (by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr])
    have hz : s₁₄.zf = some (decide (k = 1)) := by
      rw [z₁₄, u₁₃.other _ (by decide), u₁₂.other _ (by decide), h14₁₁, sx1,
        show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, sub_beq (by omega_arith) (by omega_arith)]
    have hst : ∀ iv m, R₀ H s₀ iv m → H.lenOk m.length →
        H.stateAt s₁₄.mem (st s₀) = H.compress (H.stateAt s.mem (st s₀)) (H.parse fun t =>
          (bytesAt s.mem (buf P s₀) n ++ [BitVec.ofNat 8 mk] ++ (if k = 1 then List.replicate (P.B - 1 - n) 0 else
            List.replicate (P.B - P.L - 1 - n) 0 ++ H.lenBytes m.length)).getD t 0) := by
      intro iv m hm hok
      rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, hst₁₁, hst', ← hblk iv m hm hok]
    by_cases hk1 : k = 1
    · subst hk1
      refine .inr ⟨rfl, by simp [eval, hz], ⟨hC₁₄, by omega_arith, by rw [lim]; simp; omega_arith, by decide, ?_, ?_, ?_,
        fun iv m hm hok => ?_⟩⟩
      · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.gpr]; rfl
      · rw [u₁₄.other _ (by decide), u₁₃.gpr]; rfl
      · rw [u₁₄.gpr, u₁₃.other _ (by decide), u₁₂.other _ (by decide), h14₁₁, sx1]; rfl
      · rw [h.hash iv m hm hok]
        simp only [ite_true, show ¬ (0 = 1) by decide, ite_false, Fin1, Fin0, hst iv m hm hok]
        have e : bytesAt s₁₄.mem (buf P s₀) 0 ++ [BitVec.ofNat 8 0] ++ List.replicate (P.B - P.L - 1 - 0) 0 =
            List.replicate (P.B - P.L) (0 : Byte) := by
          rw [show P.B - P.L = (P.B - P.L - 1 - 0) + 1 by omega_arith, List.replicate_succ]
          rfl
        rw [e]
    · have hk0 : k = 0 := by omega_arith
      subst hk0
      refine .inl ⟨rfl, by simp [eval, hz], ⟨hC₁₄, fun iv m hm hok => ?_⟩,
        by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), hdi₁₁],
        by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), hcx₁₁]⟩
      rw [h.hash iv m hm hok, hst iv m hm hok]
      simp only [show ¬ (0 = 1) by decide, ite_false, Fin0, List.append_assoc]

  -- Whether the buffered bytes end at a multiple of 16.
  unfold finalizePad
  refine WP.seq (wp_mov fun s₁ u₁ _ _ => wp_andiZ fun s₂ u₂ z₂ => WP.block_nil ?_)
  have hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r hr => by rw [u₂.other r hr, u₁.other r hr]
  have hz₂ : s₂.zf = some (decide (n % 16 = 0)) := by
    rw [z₂, u₁.gpr, h.r13, and15 n (by omega_arith), ofNat_beq_zero (by omega_arith)]
  refine WP.seq (WP.ite (decide (n % 16 = 0)) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_))
  · -- Sixteen bytes at a time.
    simp only [decide_eq_true_eq] at hb
    have hout : ∀ e, e + 16 ≤ P.B → InRegions s₂.wr (s₂.gpr .rbx + BitVec.ofNat 64 (P.N + e)) 16 := fun e he =>
      ⟨stR P s₀, by simp [u₂.wr, u₁.wr, hC.wr, hp.wr], by
        rw [g₂ _ (by decide), hC.rbx]; exact contains_offset (by omega_arith) (by omega_arith)⟩
    refine vec_exec P hd.B hd.N.2 hd.L H.lenOf hs.lenV hk hn' hb h.mk_lt (by rw [g₂ _ (by decide), h.r13])
      (by rw [g₂ _ (by decide), h.r9]) (by rw [g₂ _ (by decide), h.r14]) hout
      fun s' g' rd' wr' fr' by' => cont s' (fun r hr => ?_) (by rw [rd', u₂.rd, u₁.rd]) (by rw [wr', u₂.wr, u₁.wr])
        (by rw [← hm₂]; rw [g₂ _ (by decide), hrbx] at fr'; exact fr') fun i hi => ?_
    · have : r ≠ .rax ∧ r ≠ .r13 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h <;> subst h <;> decide
      rw [g' r this.1 this.2, g₂ r this.1]
    · have b := by' i hi
      rw [g₂ _ (by decide), hrbx, hm₂, g₂ _ (by decide)] at b
      exact b
  · -- A byte at a time.
    simp only [decide_eq_false_iff_not] at hb
    have h₂ : LInv H s₀ k n mk s₂ :=
      { toCommon := hC.of_gpr (fun r hr => g₂ r (by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with h | h | h | h | h <;> subst h <;> decide)) hm₂ (by rw [u₂.rd, u₁.rd])
          (by rw [u₂.wr, u₁.wr])
        k_le := hk, n_lt := hn, mk_lt := h.mk_lt
        r13 := by rw [g₂ _ (by decide), h.r13]
        r9 := by rw [g₂ _ (by decide), h.r9]
        r14 := by rw [g₂ _ (by decide), h.r14]
        hash := by rw [hm₂]; exact h.hash }
    refine byte_exec hd hs hp h₂ fun s' g' rd' wr' fr' by' => cont s' (fun r hr => ?_) (by rw [rd', u₂.rd, u₁.rd])
      (by rw [wr', u₂.wr, u₁.wr]) (by rw [← hm₂]; exact fr') fun i hi => ?_
    · have : r ≠ .rax := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with h | h | h | h | h | h <;> subst h <;> decide
      rw [g' r hr, g₂ r this]
    · have b := by' i hi
      rw [hm₂, g₂ _ (by decide)] at b
      exact b

theorem body_ok (hd : Dims P) (hs : ShapeD H D) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : PreD P D s₀) {k n mk : Nat} {s : State} (h : LInv H s₀ k n mk s) :
    WP isa (finalizeBody P name code) s (Step H s₀ k) :=
  WP.seq (WP.mono (pad_ok hd hs hf hp h) fun _ h => h.2.2)

/-! ## Prologue -/

theorem R₀.length (hd : Dims P) {s₀ : State} {iv : H.HV} {m : List Byte} (h : R₀ H s₀ iv m) :
    cnt s₀ % P.B = m.length % P.B := by
  rw [cnt, h.2, BitVec.toNat_ofNat, hd.mod]

/-- The number of blocks after the first, `1` if the length field does not
fit in the first. -/
def kOf (P : Params) (s₀ : State) : Nat := if P.B - P.L + 1 ≤ cnt s₀ % P.B + 1 then 1 else 0

theorem prologue_ok (hd : Dims P) {s₀ : State} (hp : PreD P D s₀) :
    WP isa (finalizeStart P) s₀ (LInv H s₀ (kOf P s₀) (cnt s₀ % P.B) 0x80) := by
  have := hd.N; have := hd.B; have := hd.L; have := hd.so
  have o : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions s₀.wr (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR P s₀, by simp [hp.wr], contains_offset' hd (by omega_arith)⟩
  have hr : cnt s₀ % P.B < P.B := Nat.mod_lt _ hd.pos
  have hr' : (s₀.gpr .rsi).toNat % P.B < P.B := hr
  unfold finalizeStart
  rw [save_eq]
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so : Nat) : Int)) rfl (o _ (by omega_arith))
    fun s₁ g₁ m₁ rd₁ wr₁ => ?_)
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 8 : Nat) : Int)) (by simp only [State.ea, at_, g₁])
    (by rw [wr₁]; exact o _ (by omega_arith)) fun s₂ g₂ m₂ rd₂ wr₂ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 16 : Nat) : Int))
    (by simp only [State.ea, at_, g₂, g₁]) (by rw [wr₂, wr₁]; exact o _ (by omega_arith)) fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 24 : Nat) : Int))
    (by simp only [State.ea, at_, g₃, g₂, g₁]) (by rw [wr₃, wr₂, wr₁]; exact o _ (by omega_arith))
    fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 32 : Nat) : Int))
    (by simp only [State.ea, at_, g₄, g₃, g₂, g₁])
    (by rw [wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega_arith)) fun s₅ g₅ m₅ rd₅ wr₅ => ?_
  refine wp_store (a := scr s₀ + BitVec.ofInt 64 ((P.so + 40 : Nat) : Int))
    (by simp only [State.ea, at_, g₅, g₄, g₃, g₂, g₁])
    (by rw [wr₅, wr₄, wr₃, wr₂, wr₁]; exact o _ (by omega_arith)) fun s₆ g₆ m₆ rd₆ wr₆ => ?_
  have hg₆ : s₆.gpr = s₀.gpr := by rw [g₆, g₅, g₄, g₃, g₂, g₁]
  have hm₆ : s₆.mem = saveMem P s₀ .rcx := by
    rw [m₆, m₅, m₄, m₃, m₂, m₁]; simp only [saveMem, g₅, g₄, g₃, g₂, g₁]
  have hsf := saveMem_frame (s₀ := s₀) (b := .rcx) hd
  refine wp_mov fun s₇ u₇ _ _ => wp_mov fun s₈ u₈ _ _ => wp_mov fun s₉ u₉ _ _ => wp_mov fun s₁₀ u₁₀ _ _ =>
    wp_mov fun s₁₁ u₁₁ _ _ => wp_andi fun s₁₂ u₁₂ => ?_
  have hC₁₂ : Common P s₀ s₁₂ := by
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
    · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]; exact saveMem_saved hd
  have hm₁₂ : s₁₂.mem = saveMem P s₀ .rcx := by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, hm₆]
  have hr13 : s₁₂.gpr .r13 = BitVec.ofNat 64 (cnt s₀ % P.B) := by
    rw [u₁₂.gpr, u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), hg₆]
    exact and_mask hd.B _
  -- The byte after the buffered ones, and the number of blocks.
  refine wp_mov32i fun s₁₃ u₁₃ _ _ => wp_mov32i fun s₁₄ u₁₄ _ _ => wp_cmpi fun s₁₅ g₁₅ m₁₅ rd₁₅ wr₁₅ cf₁₅ _ =>
    WP.block_nil ?_
  have keep : ∀ r, r ≠ .r9 → r ≠ .r14 → s₁₅.gpr r = s₁₂.gpr r := fun r h1 h2 => by
    rw [g₁₅, u₁₄.other r h2, u₁₃.other r h1]
  have hm₁₅ : s₁₅.mem = s₁₂.mem := by rw [m₁₅, u₁₄.mem, u₁₃.mem]
  have hC₁₅ : Common P s₀ s₁₅ := hC₁₂.of_gpr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      exact keep r (by rcases hr with h | h | h | h | h <;> subst h <;> decide)
        (by rcases hr with h | h | h | h | h <;> subst h <;> decide))
    hm₁₅ (by rw [rd₁₅, u₁₄.rd, u₁₃.rd]) (by rw [wr₁₅, u₁₄.wr, u₁₃.wr])
  have hr13' : s₁₅.gpr .r13 = BitVec.ofNat 64 (cnt s₀ % P.B) := by rw [keep _ (by decide) (by decide), hr13]
  have hr9 : s₁₅.gpr .r9 = BitVec.ofNat 64 0x80 := by rw [g₁₅, u₁₄.other _ (by decide), u₁₃.gpr]; rfl
  have hcf : s₁₅.cf = some (decide (cnt s₀ % P.B < P.B - P.L)) := by
    rw [cf₁₅, u₁₄.other _ (by decide), u₁₃.other _ (by decide), hr13, sx_ofNat (by omega_arith),
      toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]
  -- The facts about the buffer.
  have hbytes : ∀ iv m, R₀ H s₀ iv m → bytesAt s₁₅.mem (buf P s₀) (cnt s₀ % P.B) = Md.rest P.B m := by
    intro iv m hm
    rw [hm₁₅, hm₁₂, hm.length hd]
    refine (bytesAt_congr ?_).trans hm.1.2
    intro i hi
    have := Nat.mod_lt m.length hd.pos
    have := hsf.bytes (R := stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega_arith)
      (i := P.N + i) (by show P.N + i < P.N + P.B; omega_arith)
    rwa [← buf_add] at this
  have hstate : H.stateAt s₁₅.mem (st s₀) = H.stateAt s₀.mem (st s₀) := by
    apply H.stateAt_congr
    intro i hi
    rw [hm₁₅, hm₁₂]
    exact hsf.bytes (R := stR P s₀) (by simpa using hp.st_scr) (by show P.N + P.B ≤ 2 ^ 64; omega_arith)
      (by show i < P.N + P.B; omega_arith)
  refine WP.ite (!decide (cnt s₀ % P.B < P.B - P.L)) (by simp [eval, hcf]) (fun hb => ?_) (fun hb => ?_)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt] at hb
    rw [show kOf P s₀ = 1 from ite_eq_left_iff.mpr fun h =>
      absurd (by omega_arith : P.B - P.L + 1 ≤ cnt s₀ % P.B + 1) h]
    refine wp_mov32i fun s₁₆ u₁₆ _ _ => WP.block_nil ⟨hC₁₅.of_gpr (fun r hr => u₁₆.other r (by
      simp at hr; rcases hr with h | h | h | h | h <;> subst h <;> decide)) u₁₆.mem u₁₆.rd u₁₆.wr,
      (Nat.le_refl _), by rw [lim]; simp; omega_arith, by decide, by rw [u₁₆.other _ (by decide), hr13'],
      by rw [u₁₆.other _ (by decide), hr9], by rw [u₁₆.gpr]; rfl, fun iv m hm _ => ?_⟩
    simp only [↓reduceIte]
    rw [Md.hash_two H hd.pos (by omega_arith) (by rw [← hm.length hd]; omega_arith), Fin1, u₁₆.mem, hbytes iv m hm,
      hstate, hm.1.1, ← hm.length hd]
    rfl
  · simp only [Bool.not_eq_false', decide_eq_true_eq] at hb
    rw [show kOf P s₀ = 0 from ite_eq_right_iff.mpr fun h => absurd h (by omega_arith)]
    refine WP.block_nil ⟨hC₁₅, by omega_arith, by rw [lim]; simp; omega_arith, by decide, hr13', hr9, ?_,
      fun iv m hm _ => ?_⟩
    · rw [g₁₅, u₁₄.gpr]; rfl
    simp only [show ((0 : Nat) = 1) = False by decide, ite_false]
    rw [Md.hash_one H hd.pos (by rw [← hm.length hd]; omega_arith), Fin0, hbytes iv m hm, hstate, hm.1.1,
      ← hm.length hd]
    rfl

/-! ## Output and epilogue -/

set_option simprocs false in
theorem epilogue_ok (hd : Dims P) (hDN : D ≤ P.N) {s₀ : State} (hp : PreD P D s₀) {sD : State}
    (hD : Done H s₀ sD) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hkeep : ∀ r, r ≠ .rax → s.gpr r = sD.gpr r)
    (hm : s.mem = writeBytes sD.mem (out s₀) ((H.digest (H.stateAt sD.mem (st s₀))).take D))
    (hdi : s.gpr .rdi = s₀.gpr .rdi) (hcx : s.gpr .rcx = s₀.gpr .rcx) :
    WP isa (.block (restore P)) s fun s' =>
      gprPreserved s₀ s' ∧ (finKD H D).post s₀ s' ∧ s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx := by
  have := hd.N; have := hd.so
  have hC := hD.1
  have hdl : ((H.digest (H.stateAt sD.mem (st s₀))).take D).length = D := by
    rw [List.length_take, H.digest_length]; exact Nat.min_eq_left hDN
  have hfo : Frame [outR s₀ D] sD.mem
      (writeBytes sD.mem (out s₀) ((H.digest (H.stateAt sD.mem (st s₀))).take D)) :=
    writeBytes_frame _ _ _ (by
      rw [show out s₀ = out s₀ + BitVec.ofNat 64 0 by simp]
      exact contains_offset (by omega_arith) (by omega_arith))
  have i : ∀ d : Nat, d + 8 ≤ P.so + 48 → InRegions (s.rd ++ s.wr) (scr s₀ + BitVec.ofInt 64 (d : Int)) 8 :=
    fun d hd => ⟨scR P s₀, by simp [hrd, hwr, hp.wr], contains_offset' hd (by omega_arith)⟩
  have sv : ∀ r d, (r, d) ∈ saved P →
      s.mem.readW (scr s₀ + BitVec.ofInt 64 ((d : Nat) : Int)) 64 = s₀.gpr r := by
    intro r d hrd
    rw [hm, ← hC.saved _ hrd]
    have hd' := saved_offset hd hrd
    refine hfo.readW (r := ⟨scr s₀ + BitVec.ofInt 64 (d : Int), 8⟩) (Region.contains_self _ _) ?_ (by decide)
    intro r' hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst hr'
    exact (hp.out_scr.symm.sub_left (by rw [ofInt_natCast]; exact sub_offset (by omega_arith) (by omega_arith)))
  have i0 := i P.so (by omega_arith); have i1 := i (P.so + 8) (by omega_arith); have i2 := i (P.so + 16) (by omega_arith)
  have i3 := i (P.so + 24) (by omega_arith); have i4 := i (P.so + 32) (by omega_arith); have i5 := i (P.so + 40) (by omega_arith)
  have g0 := sv .rbx P.so (by simp [saved]); have g1 := sv .rbp (P.so + 8) (by simp [saved])
  have g2 := sv .r12 (P.so + 16) (by simp [saved]); have g3 := sv .r13 (P.so + 24) (by simp [saved])
  have g4 := sv .r14 (P.so + 32) (by simp [saved]); have g5 := sv .r15 (P.so + 40) (by simp [saved])
  have hr15 : s.gpr .r15 = scr s₀ := by rw [hkeep _ (by decide), hC.r15]
  have hrsp : s.gpr .rsp = s₀.gpr .rsp := by rw [hkeep _ (by decide), hC.rsp]
  have hret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64 := by
    rw [hm, hfo.readW (Region.contains_self _ _) (by simpa using hp.ret_out) (by decide)]
    exact hC.frame.readW (Region.contains_self _ _) (by simpa using ⟨hp.ret_st, hp.ret_scr, ret_stk s₀⟩)
      (by decide)
  have hout : bytesAt s.mem (s₀.gpr .rdx) D = (H.digest (H.stateAt sD.mem (st s₀))).take D := by
    have e := bytesAt_writeBytes sD.mem (out s₀) 0 ((H.digest (H.stateAt sD.mem (st s₀))).take D) (by omega_arith)
    rw [hdl, show out s₀ + BitVec.ofNat 64 0 = out s₀ by simp, Nat.zero_add,
      show bytesAt sD.mem (out s₀) 0 = [] from rfl, List.nil_append] at e
    rw [hm]; exact e
  apply WP.of_runBlock
  rw [restore_eq]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, isa, ea_at, State.load64,
    State.setReg, hr15, i0, i1, i2, i3, i4, i5, ite_true, ite_false, g0, g1, g2, g3, g4, g5,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨⟨fun r hr => ?_, hret⟩, fun iv m hm' hok hc => ?_, hdi, hcx⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp (config := {decide := true}) [hrsp]
  · rw [hout, (hD.2 iv m ⟨hm', hc⟩ hok)]

/-- `finalize` writing the first `D` bytes of the final hash value is
correct, and leaves `rdi` and `rcx` as they were (which code inlining it
relies on). -/
theorem correctD (hd : Dims P) (hs : ShapeD H D) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : PreD P D s₀) :
    WP isa (finalize P name code) s₀ fun s' => gprPreserved s₀ s' ∧ (finKD H D).post s₀ s' ∧
      s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx := by
  have := hd.N; have := hd.B
  unfold finalize
  refine WP.seq (WP.mono (prologue_ok (H := H) hd hp) fun s₁ hL => ?_)
  refine WP.seq (WP.mono (Q := fun (s : State) => Done H s₀ s ∧ s.gpr .rdi = st s₀ ∧ s.gpr .rcx = scr s₀) ?_
    fun sD ⟨hD, hdi, hcx⟩ => ?_)
  · refine WP.loop (M := isa) (fun i s => ∃ n mk, LInv H s₀ i n mk s) ?_ (kOf P s₀) s₁ ⟨_, _, hL⟩
    rintro i s ⟨n, mk, hL⟩
    refine WP.mono (body_ok hd hs hf hp hL) fun s' h => ?_
    rcases h with ⟨-, he, hD⟩ | ⟨rfl, he, hL'⟩
    · exact .inl ⟨he, hD⟩
    · exact .inr ⟨he, 0, by omega_arith, 0, 0, hL'⟩
  · have hC := hD.1
    rw [WP.block_append_iff]
    have hDN := hs.le
    refine WP.mono (hs.out sD ?_ ?_ ?_) fun s ⟨g, rd, wr, m⟩ =>
      epilogue_ok hd hDN hp hD (rd.trans hC.rd) (wr.trans hC.wr) g (by rw [m, hC.rbp, hC.rbx])
        (by rw [g _ (by decide), hdi]) (by rw [g _ (by decide), hcx])
    · refine ⟨stR P s₀, by simp [hC.rd, hC.wr, hp.wr, hp.rd], ?_⟩
      rw [hC.rbx]; simpa using contains_offset (base := st s₀) (off := 0) (n := P.N) (len := P.N + P.B)
        (by omega_arith) (by omega_arith)
    · refine ⟨outR s₀ D, by simp [hC.wr, hp.wr], ?_⟩
      rw [hC.rbp]; simpa using contains_offset (base := out s₀) (off := 0) (n := D) (len := D)
        (by omega_arith) (by omega_arith)
    · rw [hC.rbx, hC.rbp]
      exact hp.st_out.sub_left (Region.sub_prefix (by omega_arith))

/-- `finalize` is correct, and leaves `rdi` and `rcx` as they were (which code
inlining it relies on). -/
theorem correct (hd : Dims P) (hs : Shape H) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    {s₀ : State} (hp : Pre P s₀) :
    WP isa (finalize P name code) s₀ fun s' => gprPreserved s₀ s' ∧ (finK H).post s₀ s' ∧
      s'.gpr .rdi = s₀.gpr .rdi ∧ s'.gpr .rcx = s₀.gpr .rcx :=
  (correctD hd hs.toD hf hp).mono fun _ ⟨g, h, di, cx⟩ => ⟨g, fun iv m hr hl hc =>
    (h iv m hr hl hc).trans (List.take_of_length_le (by rw [Md.hash, H.digest_length])), di, cx⟩

/-- A state satisfying the precondition of `finKD H D`. -/
def satD (P : Params) (D : Nat) : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rcx => 0x3000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, P.N + P.B⟩, ⟨0x2000, D⟩, ⟨0x3000, P.so + 48⟩]

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
theorem verified_ofD (hd : Dims P) (hs : ShapeD H D) {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (finalize P name code).allInstrs (fun i => !loadsMxcsr i) = true)
    (hct : ConstantTime isa (finKD H D).pre (finKD H D).pub (finalize P name code)) :
    Verified X86_64.target (finalize P name code) (finKD H D) := by
  have := hd.N; have := hd.B; have := hd.so; have := hs.le
  refine ⟨fun s hs' => ?_, hct, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correctD hd hs hf (pre_ofD hs')
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2.1⟩
  · refine ⟨satD P D, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp only [satD]
    · exact Offset.disjoint_of_le (by simp <;> omega_arith) (by simp <;> omega_arith)
    · exact Offset.disjoint_of_le (by simp <;> omega_arith) (by simp <;> omega_arith)
    · exact Offset.disjoint_of_le (by simp <;> omega_arith) (by simp <;> omega_arith)
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm
    · exact (Offset.disjoint_of_le (by simp <;> omega_arith) (by simp)).symm

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

theorem PubEq.kOf {P : Params} {s₀ s₀' : State} (hq : PubEq s₀ s₀') : kOf P s₀ = kOf P s₀' := by
  have e : cnt s₀ = cnt s₀' := congrArg BitVec.toNat hq.rsi
  simp only [Finalize.kOf, e]

theorem PubEq.cnt {s₀ s₀' : State} (hq : PubEq s₀ s₀') : cnt s₀ = cnt s₀' :=
  congrArg BitVec.toNat hq.rsi

/-- The registers the pieces between the calls use. -/
abbrev regs : List Reg := [.rbx, .r15, .rbp, .r12, .rsp, .r13, .r14, .r9]

section
variable {P : Params} {H : Md P.B P.N P.L} {D : Nat}

theorem LInv.agree {s₀ s₀' : State} (hq : PubEq s₀ s₀') {k n mk : Nat} {s s' : State} (h : LInv H s₀ k n mk s)
    (h' : LInv H s₀' k n mk s') : ∀ r ∈ regs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [regs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx]; exact hq.rdi
  · rw [h.r15, h'.r15]; exact hq.rcx
  · rw [h.rbp, h'.rbp]; exact hq.rdx
  · rw [h.r12, h'.r12]; exact hq.rsi
  · rw [h.rsp, h'.rsp]; exact hq.rsp
  · rw [h.r13, h'.r13]
  · rw [h.r14, h'.r14]
  · rw [h.r9, h'.r9]

variable (hd : Dims P) (hs : ShapeD H D) (ht : Taints P) {name : String} {code : Prog isa}
  (hf : CalleeOk H code) {s₀ s₀' : State} (hp : PreD P D s₀) (hp' : PreD P D s₀') (hq : PubEq s₀ s₀')
include hd hs ht hf hp hp' hq

theorem body_rel {k n mk : Nat} :
    RelCT isa (fun s₁ s₂ => LInv H s₀ k n mk s₁ ∧ LInv H s₀' k n mk s₂) (finalizeBody P name code)
      fun s₁ s₂ => Step H s₀ k s₁ ∧ Step H s₀' k s₂ := by
  obtain ⟨_, hpad⟩ := ht.finPad
  have pad : RelCT isa (fun s₁ s₂ => LInv H s₀ k n mk s₁ ∧ LInv H s₀' k n mk s₂) (finalizePad P)
      fun s₁ s₂ => Mid H name code s₀ k s₁ ∧ Mid H name code s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs regs) (P := fun s₁ s₂ => LInv H s₀ k n mk s₁ ∧ LInv H s₀' k n mk s₂)
      (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.1 h.2)) (c := finalizePad P) hpad).wp
      fun _ _ h => ⟨pad_ok hd hs hf hp h.1, pad_ok hd hs hf hp' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2
  have cmp : RelCT isa (fun s₁ s₂ => Mid H name code s₀ k s₁ ∧ Mid H name code s₀' k s₂) (compressAt name code)
      fun s₁ s₂ => WP isa (.block [.mov32 .r13 (.imm 0), .mov32 .r9 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (Step H s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .mov32 .r9 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (Step H s₀' k) :=
    ((compressAt_rel H hf fun s₁ s₂ ⟨⟨C₁, si₁, _⟩, ⟨C₂, si₂, _⟩⟩ =>
      ⟨⟨_, _, _, C₁.callOk hd hp si₁⟩, ⟨_, _, _, C₂.callOk hd hp' si₂⟩,
        by rw [C₁.rbx, C₂.rbx]; exact hq.rdi, by rw [C₁.r15, C₂.r15]; exact hq.rcx,
        by rw [si₁, si₂]; exact congrArg (· + _) hq.rdi, by rw [C₁.rsp, C₂.rsp]; exact hq.rsp⟩).wp
      fun _ _ h => ⟨WP.seq_iff.mp h.1.2.2, WP.seq_iff.mp h.2.2.2⟩).mono
      (fun _ _ h => h) fun _ _ h => h.2
  have fin : RelCT isa (fun s₁ s₂ =>
        WP isa (.block [.mov32 .r13 (.imm 0), .mov32 .r9 (.imm 0), .alu .sub .r14 (.imm 1)]) s₁ (Step H s₀ k) ∧
        WP isa (.block [.mov32 .r13 (.imm 0), .mov32 .r9 (.imm 0), .alu .sub .r14 (.imm 1)]) s₂ (Step H s₀' k))
      (.block [.mov32 .r13 (.imm 0), .mov32 .r9 (.imm 0), .alu .sub .r14 (.imm 1)])
      fun s₁ s₂ => Step H s₀ k s₁ ∧ Step H s₀' k s₂ :=
    ((RelCT.taint (A := taint) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs (by simp))
      (c := .block [.mov32 .r13 (.imm 0), .mov32 .r9 (.imm 0), .alu .sub .r14 (.imm 1)]) (by taint_decide)).wp
      fun _ _ h => h).mono (fun _ _ h => h) fun _ _ h => h.2
  exact pad.seq (cmp.seq fin)

theorem finalize_rel :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalize P name code) fun _ _ => True := by
  obtain ⟨_, hst⟩ := ht.finStart
  obtain ⟨_, hend⟩ := ht.finEnd
  have pro : RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (finalizeStart P) fun s₁ s₂ =>
      ∃ n mk, LInv H s₀ (kOf P s₀) n mk s₁ ∧ LInv H s₀' (kOf P s₀) n mk s₂ :=
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
      fun _ _ ⟨e, e'⟩ => by rw [e, e']; exact ⟨prologue_ok (H := H) hd hp, prologue_ok (H := H) hd hp'⟩).mono
      (fun _ _ h => h) fun _ _ h => ⟨_, _, h.2.1, by rw [hq.kOf, hq.cnt]; exact h.2.2⟩
  have lp := RelCT.loop (M := isa) (body := finalizeBody P name code) (c := .e)
    (Q := fun s₁ s₂ => Done H s₀ s₁ ∧ Done H s₀' s₂)
    (fun m s₁ s₂ => ∃ n mk, LInv H s₀ m n mk s₁ ∧ LInv H s₀' m n mk s₂) (fun m => RelCT.exists_ fun n =>
      RelCT.exists_ fun mk => (body_rel hd hs ht hf hp hp' hq).mono (fun _ _ h => h) fun s₁ s₂ ⟨h₁, h₂⟩ => by
        rcases h₁ with ⟨rfl, z₁, D₁, -⟩ | ⟨rfl, z₁, L₁⟩ <;>
          rcases h₂ with ⟨h0, z₂, D₂, -⟩ | ⟨h1, z₂, L₂⟩
        · exact ⟨z₁.trans z₂.symm, fun _ => ⟨D₁, D₂⟩, fun h => absurd (z₁.symm.trans h) (by simp)⟩
        · cases h1
        · cases h0
        · exact ⟨z₁.trans z₂.symm, fun h => absurd (z₁.symm.trans h) (by simp),
            fun _ => ⟨0, by omega_arith, 0, 0, L₁, L₂⟩⟩) (kOf P s₀)
  have epi : RelCT isa (fun s₁ s₂ => Done H s₀ s₁ ∧ Done H s₀' s₂) (.block (P.out ++ restore P))
      fun _ _ => True :=
    RelCT.taint (A := taint) (Taint.ofRegs [.rbx, .rbp, .r15]) (fun _ _ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h.1.1.rbx, h.2.1.rbx]; exact hq.rdi
      · rw [h.1.1.rbp, h.2.1.rbp]; exact hq.rdx
      · rw [h.1.1.r15, h.2.1.r15]; exact hq.rcx) hend
  exact pro.seq (lp.seq epi)

end

theorem pubEq_ofD {P : Params} {H : Md P.B P.N P.L} {D : Nat} {s₁ s₂ : State} (h : (finKD H D).pub s₁ s₂) :
    PubEq s₁ s₂ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem constantTimeD {P : Params} {H : Md P.B P.N P.L} {D : Nat} (hd : Dims P) (hs : ShapeD H D)
    (ht : Taints P) {name : String} {code : Prog isa} (hf : CalleeOk H code) :
    ConstantTime isa (finKD H D).pre (finKD H D).pub (finalize P name code) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂
  exact (finalize_rel hd hs ht hf (pre_ofD h₁) (pre_ofD h₂) (pubEq_ofD hpub) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `finalize` writing the first `D` bytes of the final hash value is
verified if it never loads MXCSR. -/
theorem verifiedD {P : Params} {H : Md P.B P.N P.L} {D : Nat} (hd : Dims P) (hs : ShapeD H D) (ht : Taints P)
    {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (finalize P name code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize P name code) (finKD H D) :=
  verified_ofD hd hs hf hm (constantTimeD hd hs ht hf)

/-- `finKD` for the whole final hash value is `finK`. -/
theorem finKD_implies {P : Params} (H : Md P.B P.N P.L) (h : ∃ s, (finK H).pre s) :
    (finKD H P.N).Implies (finK H) :=
  ⟨fun _ h => h, fun _ _ _ h iv m hr hl hc =>
    (h iv m hr hl hc).trans (List.take_of_length_le (by rw [Md.hash, H.digest_length])),
    fun _ _ _ _ h => h, h⟩

theorem constantTime {P : Params} {H : Md P.B P.N P.L} (hd : Dims P) (hs : Shape H) (ht : Taints P)
    {name : String} {code : Prog isa} (hf : CalleeOk H code) :
    ConstantTime isa (finK H).pre (finK H).pub (finalize P name code) :=
  constantTimeD hd hs.toD ht hf

/-- `finalize` is verified if it never loads MXCSR. -/
theorem verified {P : Params} {H : Md P.B P.N P.L} (hd : Dims P) (hs : Shape H) (ht : Taints P)
    {name : String} {code : Prog isa} (hf : CalleeOk H code)
    (hm : (finalize P name code).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (finalize P name code) (finK H) :=
  have h := verifiedD hd hs.toD ht hf hm
  h.of_implies (finKD_implies H h.2.2)

end VG.Proof.MdStream.X86_64.Finalize
