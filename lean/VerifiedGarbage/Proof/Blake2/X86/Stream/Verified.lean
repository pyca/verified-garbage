module

public import VerifiedGarbage.Proof.Blake2.X86.Stream.Common
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.MdStream.X86.Common
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Blake2.Spec

/-! ### `Blake2.X86.Stream.Finalize`, which this module and modules that import it used -/

section

/-!
# Streaming BLAKE2 on x86 (32-bit): `finalize`

`finalize` saves the callee-saved registers (`prologue_ok`), computes the
number of buffered bytes (`bufLen_val`), zeroes the rest of the buffer
(`pad_ok`), compresses it as the last block (`call_ok`), copies the hash value
out (`output_ok`) and restores the registers (`epilogue_ok`), for either word
size and any correct compression function (`CalleeOk`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86.Stream.Finalize

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 finalizeX86 countX86 final_eq stateAt_congr bytesAt_congr bytesAt_add
  bytesAt_state wordBytes_readW bufLen_le compressBlocks_succ compressBlocks_zero)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)
open VG.Proof.MdStream.X86 (contains_addr sub_offset contains_offset)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev op : BitVec 32 := arg s₀ 3
abbrev scr : BitVec 32 := arg s₀ 4
abbrev stA : Addr := (st s₀).setWidth 64
abbrev opA : Addr := (op s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev outR (w : Nat) : Region := ⟨opA s₀, bufOff w⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 20⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- Where the call of the compression function pushes its arguments and
stores the return address. -/
abbrev stkR : Region := below (esp₀ s₀) 32

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [argR s₀]
  wr : s₀.wr = [stR s₀ w, outR s₀ w, scR s₀]
  st_out : (stR s₀ w).Disjoint (outR s₀ w)
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  out_scr : (outR s₀ w).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_out : (argR s₀).Disjoint (outR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  ret_out : (retR s₀).Disjoint (outR s₀ w)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀ w)
  stk_out : (stkR s₀).Disjoint (outR s₀ w)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  out_fit : (op s₀).toNat + bufOff w ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 32 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 24 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (finalizeX86 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := h
  obtain e := stk_eq h18
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    by show (below _ _).Disjoint _; rw [e]; exact h12, by show (below _ _).Disjoint _; rw [e]; exact h13,
    by show (below _ _).Disjoint _; rw [e]; exact h14, h15, h16, h17, h18, h19⟩

namespace Pre
variable {s₀ : State} (hp : Pre w s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega_using []) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 20⟩ : Region).Contains _ _
  rw [addr_eq (by omega_using [this]), addr_eq (by omega_using [hd, this])]
  exact Offset.contains _ hd₁ (by omega_using [hd]) (by omega_using [])

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩

theorem sinr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [Taint.sub_setWidth (by omega_arith)]
  exact Offset.base_disjoint_below _ (by omega_using [])

theorem a_stk : (argR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨addr (esp₀ s₀) 4, 20⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [addr_eq (by omega_arith), Taint.sub_setWidth (by omega_arith)]
  exact Offset.disjoint_below _ (by omega_using [])

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 24) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 20⟩
  rw [addr_eq (by omega_using [hd, this]), addr_eq (by omega_using [this])]
  exact Offset.sub _ hd₁ (by omega_using [hd])

end Pre

/-! ## The prologue -/

/-- After the prologue. -/
structure Start (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  eax : s.gpr .eax = arg s₀ 1
  ecx : s.gpr .ecx = arg s₀ 2
  mem : s.mem = saveMem (scr s₀) s₀

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) : WP isa (.block finalizeStart) s₀ (Start s₀) := by
  obtain rin : ∀ {d}, 4 ≤ d → d + 4 ≤ 24 → InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
    fun h₁ h₂ => hp.rin rfl h₁ h₂
  obtain sin : ∀ {d}, d + 4 ≤ 576 → InRegions s₀.wr (addr (scr s₀) d) 4 := fun h => hp.sin rfl h
  obtain sepA : ∀ d e, 512 ≤ d → d + 4 ≤ 576 → 4 ≤ e → e + 4 ≤ 24 →
      Mem.Sep (addr (esp₀ s₀) e) 4 (addr (scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄
    exact hp.a_scr.sep (hp.arg_in h₃ h₄) (hp.scr_in h₂)
  obtain argSave : ∀ e, 4 ≤ e → e + 4 ≤ 24 →
      (saveMem (scr s₀) s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    exact Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      have := saved_bound p h; sepA _ e this.1 (by omega_using [this]) h₁ h₂
  rw [show finalizeStart = .mov .eax (.mem (at_ .esp 20)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .eax (.mem (at_ .esp 8)),
      .mov .ecx (.mem (at_ .esp 12))] : List Instr)) from rfl]
  refine wp_ldm (B := esp₀ s₀) rfl (rin (d := 20) (by omega_using []) (by omega_using [])) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine Spill.save_ok saved (fun p h => by
    rw [e₁, u₁.wr]; exact sin (by have := saved_bound p h; omega_using [this])) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := u₅.gpr
  obtain m₅ : s₅.mem = saveMem (scr s₀) s₀ := by
    rw [u₅.mem, e₁, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₁.wr]
  obtain sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  refine wp_mov fun s₆ u₆ => ?_
  obtain sp₆ : s₆.gpr .esp = esp₀ s₀ := by rw [u₆.other _ (by decide), sp₅]
  obtain rd' : ∀ d, 4 ≤ d → d + 4 ≤ 24 → InRegions (s₆.rd ++ s₆.wr) (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact rin h₁ h₂
  obtain l : ∀ e, 4 ≤ e → e + 4 ≤ 24 → s₆.mem.readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [u₆.mem, m₅]; exact argSave e h₁ h₂
  refine wp_ldm sp₆ (rd' 4 (by omega_using []) (by omega_using [])) fun s₇ u₇ => ?_
  refine wp_ldm (by rw [u₇.other _ (by decide), sp₆]) (by rw [u₇.rd, u₇.wr]; exact rd' 8 (by omega_using []) (by omega_using []))
    fun s₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 12 (by omega_using []) (by omega_using [])) fun s₉ u₉ => WP.block_nil ?_
  refine ⟨by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅], ?_, ?_, ?_, ?_, ?_,
    by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, l 4 (by omega_using []) (by omega_using [])]; rfl
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, g₅, e₁]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), sp₆]
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.mem, l 8 (by omega_using []) (by omega_using [])]; rfl
  · rw [u₉.gpr, u₈.mem, u₇.mem, l 12 (by omega_using []) (by omega_using [])]; rfl

/-! ## The number of buffered bytes -/

theorem bufLen_val (hP : Ok P) {s : State} {lo hi : BitVec 32} (hax : s.gpr .eax = lo)
    (hcx : s.gpr .ecx = hi) :
    WP isa (Impl.Blake2.X86.Stream.bufLen w) s fun s' =>
      s'.gpr .eax = BitVec.ofNat 32 (Proof.Blake2.bufLen w (hi ++ lo).toNat) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold Impl.Blake2.X86.Stream.bufLen
  refine WP.seq (wp_orZ fun s₁ u₁ z₁ => WP.block_nil ?_)
  obtain hz : isa.eval .e s₁ = some (decide ((hi ++ lo).toNat = 0)) := by
    show s₁.zf = _
    rw [z₁, hcx, hax, or_beq_zero]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movi fun s₂ u₂ => WP.block_nil ⟨?_, fun r h1 h2 => by rw [u₂.other r h1, u₁.other r h2],
      by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
    rw [u₂.gpr, hb]; rfl
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_subi fun s₂ u₂ _ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil
      ⟨?_, fun r h1 h2 => by rw [u₄.other r h1, u₃.other r h1, u₂.other r h1, u₁.other r h2],
        by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem], by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd],
        by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]⟩
    obtain e : lo = BitVec.ofNat 32 (hi ++ lo).toNat := (lo_append hi lo).symm
    rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hax]
    conv => lhs; rw [e]
    rw [mask_ofNat hP hb]
    simp only [Proof.Blake2.bufLen, hb, ite_false]

/-! ## Zeroing the rest of the buffer -/

/-- The zeroing loop's state after `j` of `k` bytes, from `s₀`. -/
structure ZI (s₀ : State) (dA : BitVec 32) (k j : Nat) (s : State) : Prop where
  j_le : j ≤ k
  edx : s.gpr .edx = dA + BitVec.ofNat 32 j
  ecx : s.gpr .ecx = BitVec.ofNat 32 (k - j)
  other : ∀ x, x ≠ .edx → x ≠ .ecx → s.gpr x = s₀.gpr x
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : s.mem = writeBytes s₀.mem (addr dA (bufOff w)) (List.replicate j 0)

/-- The loop zeroing `k ≥ 1` bytes at `dA + N` (at `edx`, `eax = 0`). -/
theorem zeroLoop_ok {s₀ : State} {dA : BitVec 32} {k : Nat} (hk : 1 ≤ k) (hk32 : k < 2 ^ 32)
    (hfd : dA.toNat + bufOff w + k ≤ 2 ^ 32)
    (hdx : s₀.gpr .edx = dA) (hcx : s₀.gpr .ecx = BitVec.ofNat 32 k) (hax : s₀.gpr .eax = 0)
    (hout : ∀ i < k, InRegions s₀.wr (addr dA (bufOff w) + BitVec.ofNat 64 i) 1)
    {Q : State → Prop} (hQ : ∀ s, ZI (w := w) s₀ dA k k s → Q s) :
    WP isa (zeroLoop w) s₀ Q := by
  refine WP.loop (M := isa) (fun n (s : State) => ∃ j, n = k - j ∧ j < k ∧ ZI (w := w) s₀ dA k j s) ?_ k s₀
    ⟨0, by omega_arith, by omega_arith, by omega_arith, by simp [hdx], by rw [hcx, Nat.sub_zero], fun _ _ _ => rfl, rfl, rfl,
      by rw [List.replicate_zero, writeBytes_nil]⟩
  rintro n s ⟨j, rfl, hj, h⟩
  obtain eD : addr (s.gpr .edx) (bufOff w) = addr dA (bufOff w) + BitVec.ofNat 64 j := by
    rw [h.edx, MdStream.X86.addr_add_ofNat (by omega_arith), addr_eq (by omega_arith), BitVec.add_assoc,
      BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 j)]
  obtain hout' : InRegions s.wr (addr dA (bufOff w) + BitVec.ofNat 64 j) 1 := by rw [h.wr]; exact hout j hj
  let m₁ := s.mem.writeW (addr dA (bufOff w) + BitVec.ofNat 64 j) ((s.gpr Reg8.al.reg).setWidth 8)
  try rewrite [show s.mem.writeW (addr dA (bufOff w) + BitVec.ofNat 64 j) ((s.gpr Reg8.al.reg).setWidth 8) = m₁ from rfl] at *
  have hm₁ : m₁ = s.mem.writeW (addr dA (bufOff w) + BitVec.ofNat 64 j) ((s.gpr Reg8.al.reg).setWidth 8) := rfl
  refine cons (s' := { s with mem := m₁ }) ?_ ?_
  · have e : s.ea (at_ .edx (N w)) = addr dA (bufOff w) + BitVec.ofNat 64 j := eD
    simp only [exec, State.store8, e, hout', ite_true, hm₁]
  refine wp_addi fun s₂ u₂ => wp_subi fun s₃ u₃ _ hz₃ => WP.block_nil ?_
  obtain e₁ : ∀ r, ({ s with mem := m₁ } : State).gpr r = s.gpr r := fun _ => rfl
  obtain hcx' : s₃.gpr .ecx = BitVec.ofNat 32 (k - (j + 1)) := by
    rw [u₃.gpr, u₂.other _ (by decide), e₁, h.ecx, ofNat_pred (by omega_arith), Nat.sub_sub]
  obtain hI : ZI (w := w) s₀ dA k (j + 1) s₃ := by
    refine ⟨by omega_arith, ?_, hcx', fun x h1 h2 => ?_, ?_, ?_, ?_⟩
    · rw [u₃.other _ (by decide), u₂.gpr, e₁, h.edx, BitVec.add_assoc, BitVec.ofNat_add]; rfl
    · rw [u₃.other x h2, u₂.other x h1]; exact h.other x h1 h2
    · rw [u₃.rd, u₂.rd]; exact h.rd
    · rw [u₃.wr, u₂.wr]; exact h.wr
    · rw [u₃.mem, u₂.mem]
      show m₁ = _
      rw [hm₁, show Reg8.al.reg = Reg.eax from rfl, h.other .eax (by decide) (by decide), hax, h.mem,
        List.replicate_succ',
        writeBytes_snoc _ _ _ _ (by simp; omega_arith), List.length_replicate]
      rfl
  obtain hzf : s₃.zf = some (decide (k - (j + 1) = 0)) := by
    rw [hz₃, u₂.other _ (by decide), e₁, h.ecx, ofNat_pred (show 1 ≤ k - j by omega_arith), ofNat_beq_zero (by omega_arith),
      show k - j - 1 = k - (j + 1) by omega_arith]
  by_cases hjk : j + 1 = k
  · refine .inl ⟨?_, hQ _ (hjk ▸ hI)⟩
    simp only [eval, hzf, show k - (j + 1) = 0 by omega_arith, decide_true, Option.map_some, Bool.not_true]
  · refine .inr ⟨?_, k - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, hI⟩
    simp only [eval, hzf, show k - (j + 1) ≠ 0 by omega_arith, decide_false, Option.map_some, Bool.not_false]

/-- Zeroing the buffer of the state at `ebx` (`st`) from byte `eax` (`r`) on. -/
theorem pad_ok (hP : Ok P) {s : State} {st : BitVec 32} {r : Nat} (hr : r ≤ blockBytes w)
    (hfit : st.toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32)
    (hbx : s.gpr .ebx = st) (hax : s.gpr .eax = BitVec.ofNat 32 r)
    (hdst : ∀ i < blockBytes w - r, InRegions s.wr (addr st (bufOff w + r) + BitVec.ofNat 64 i) 1) :
    WP isa (pad w) s fun s' =>
      (∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s'.gpr x = s.gpr x) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = writeBytes s.mem (addr st (bufOff w + r)) (List.replicate (blockBytes w - r) 0) := by
  have hl := hP.len
  unfold pad
  refine WP.seq (wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ _ => wp_movi fun s₃ u₃ => wp_sub fun s₄ u₄ z₄ =>
    wp_moviF fun s₅ u₅ _ zf₅ => WP.block_nil ?_)
  obtain g : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₅.gpr x = s.gpr x := fun x h1 h2 h3 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h2, u₂.other x h3, u₁.other x h3]
  obtain hcx : s₅.gpr .ecx = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hax, B_eq, sub_ofNat hr]
  obtain hdx : s₅.gpr .edx = st + BitVec.ofNat 32 r := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr,
      u₁.other _ (by decide), hbx, hax]
  obtain hz : isa.eval .e s₅ = some (decide (blockBytes w - r = 0)) := by
    show s₅.zf = _
    rw [zf₅, z₄, ← u₄.gpr, ← u₅.other .ecx (by decide), hcx, ofNat_beq_zero (by omega_using [hl])]
  obtain hm₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain hwr : s₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  obtain hrd : s₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  refine WP.ite _ hz (fun hb => WP.block_nil ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine ⟨g, hrd, hwr, ?_⟩
    rw [hb, List.replicate_zero, writeBytes_nil, hm₅]
  · simp only [decide_eq_false_iff_not] at hb
    obtain e : addr (st + BitVec.ofNat 32 r) (bufOff w) = addr st (bufOff w + r) := by
      rw [MdStream.X86.addr_add_ofNat (by omega_using [hfit, hb]), addr_eq (by omega_using [hfit, hb]), Nat.add_comm]
    refine zeroLoop_ok (w := w) (dA := st + BitVec.ofNat 32 r) (by omega_using [hb]) (by omega_using [hl])
      (by rw [toNat_add_ofNat (by omega_using [hfit, hb])]; omega_using [hfit, hb]) hdx hcx u₅.gpr
      (fun i hi => by rw [hwr, e]; exact hdst i hi) fun s' h => ?_
    refine ⟨fun x h1 h2 h3 => by rw [h.other x h3 h2, g x h1 h2 h3], by rw [h.rd, hrd], by rw [h.wr, hwr], ?_⟩
    rw [h.mem, hm₅, e]

/-! ## Bytes -/

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  rw [show q + BitVec.ofNat 64 i - q = BitVec.ofNat 64 i by rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : bytesAt (writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The buffer after zeroing it from byte `r` on. -/
theorem pad_bytes {m m' : Mem} {st : Addr} {N r bb : Nat} (hr : r ≤ bb) (hlt : N + bb < 2 ^ 64)
    (hm : m' = writeBytes m (st + BitVec.ofNat 64 (N + r)) (List.replicate (bb - r) 0)) :
    bytesAt m' (st + BitVec.ofNat 64 N) bb =
      bytesAt m (st + BitVec.ofNat 64 N) r ++ List.replicate (bb - r) 0 := by
  conv => lhs; rw [show bb = r + (bb - r) by omega_using [hr]]
  rw [bytesAt_add, Offset.add_ofNat_add_ofNat]
  congr 1
  · refine bytesAt_congr fun i hi => ?_
    rw [hm, Offset.add_ofNat_add_ofNat,
      writeBytes_before m st _ (by omega_using [hi] : N + i < N + r) (by simp; omega_using [hr, hlt])]
  · rw [hm]; exact bytesAt_writeBytes_self _ _ (by simp) (by omega_using [hlt])

/-! ## Copying the hash value out -/

/-- After copying `k` words. -/
def OInv (σ : State) (k : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .ecx → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
    s.mem = writeBytes σ.mem ((σ.gpr .eax).setWidth 64) (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k))

theorem output_ok {σ : State} (hN4 : bufOff w % 4 = 0)
    (hfs : (σ.gpr .ebx).toNat + bufOff w ≤ 2 ^ 32) (hfo : (σ.gpr .eax).toNat + bufOff w ≤ 2 ^ 32)
    (hin : ∀ a n, (⟨(σ.gpr .ebx).setWidth 64, bufOff w⟩ : Region).Contains a n → InRegions (σ.rd ++ σ.wr) a n)
    (hout : ∀ a n, (⟨(σ.gpr .eax).setWidth 64, bufOff w⟩ : Region).Contains a n → InRegions σ.wr a n)
    (hd : Region.Disjoint ⟨(σ.gpr .ebx).setWidth 64, bufOff w⟩ ⟨(σ.gpr .eax).setWidth 64, bufOff w⟩) :
    WP isa (.block (output w)) σ fun s =>
      (∀ r, r ≠ .ecx → s.gpr r = σ.gpr r) ∧ s.rd = σ.rd ∧ s.wr = σ.wr ∧
      s.mem = writeBytes σ.mem ((σ.gpr .eax).setWidth 64)
        (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (bufOff w)) := by
  obtain e : 4 * (Impl.Blake2.X86.Stream.N w / 4) = bufOff w := by rw [N_eq]; omega_using [hN4]
  unfold output
  rw [← e]
  refine wp_range_flatMap (M := isa) (OInv σ) (fun k s hk ⟨hg, hrd, hwr, hm⟩ => ?_) _ (Nat.le_refl _) σ
    ⟨fun _ _ => rfl, rfl, rfl, by rw [Nat.mul_zero]; simp [bytesAt, writeBytes_nil]⟩
  rw [N_eq] at hk
  obtain hk4 : 4 * k + 4 ≤ bufOff w := by omega_using [hk]
  obtain hl : (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k)).length = 4 * k := by simp [bytesAt]
  obtain eS : addr (σ.gpr .ebx) (4 * k) = (σ.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega_using [hfs, hk4])
  obtain eO : addr (σ.gpr .eax) (4 * k) = (σ.gpr .eax).setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq (by omega_using [hfo, hk4])
  refine wp_ldm (B := σ.gpr .ebx) (by rw [hg _ (by decide)])
    (by rw [hrd, hwr, eS]; exact hin _ _ (Offset.contains_base _ hk4 (by omega_using [hfo, hk4]))) fun s₁ u₁ => ?_
  refine wp_stm (B := σ.gpr .eax) (by rw [u₁.other _ (by decide), hg _ (by decide)])
    (by rw [u₁.wr, hwr, eO]; exact hout _ _ (Offset.contains_base _ hk4 (by omega_using [hfo, hk4]))) fun s₂ u₂ =>
      WP.block_nil ⟨fun r hr => by rw [u₂.gpr, u₁.other r hr, hg r hr], by rw [u₂.rd, u₁.rd, hrd],
        by rw [u₂.wr, u₁.wr, hwr], ?_⟩
  obtain hv : s.mem.readW (addr (σ.gpr .ebx) (4 * k)) 32 = σ.mem.readW (addr (σ.gpr .ebx) (4 * k)) 32 := by
    rw [hm, eS]
    exact (writeBytes_frame (R := ⟨(σ.gpr .eax).setWidth 64, bufOff w⟩) _ _ _
      (contains_prefix _ (by omega_using [hk4, hl]))).readW
      (Offset.contains_base (k := bufOff w) _ hk4 (by omega_using [hfo, hk4])) (by simpa using hd) (by decide)
  obtain e' := writeBytes_append σ.mem ((σ.gpr .eax).setWidth 64) (bytesAt σ.mem ((σ.gpr .ebx).setWidth 64) (4 * k))
    (wordBytes (σ.mem.readW ((σ.gpr .ebx).setWidth 64 + BitVec.ofNat 64 (4 * k)) 32))
    (by rw [hl]; simp [wordBytes]; omega_using [hfo, hk4])
  rw [hl] at e'
  rw [u₂.mem, u₁.gpr, u₁.mem, hv, hm, eO, eS, writeW_eq, e', wordBytes_readW _ _ (.inl rfl),
    ← bytesAt_add, Nat.mul_succ]

/-! ## The epilogue -/

theorem restore_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hbp : s.gpr .ebp = scr s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hsv : Saved (scr s₀) s₀ s.mem) :
    WP isa (.block restore) s fun s' =>
      (∀ r ∈ calleeSaved, r ≠ .esp → s'.gpr r = s₀.gpr r) ∧ s'.gpr .esp = s.gpr .esp ∧ s'.mem = s.mem :=
  restore_saved hbp (fun d _ hd => hp.sinr hrd hwr (by omega_using [hd])) hsv

/-! ## The whole function -/

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [show (1 : Nat) = 0 + 1 from rfl, compressBlocks_succ, compressBlocks_zero]; simp

/-- The arguments are kept by writes to the writable buffers and below the
stack. -/
theorem arg_keep {s₀ : State} (hp : Pre w s₀) {m : Mem}
    (hf : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 24) :
    m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hp.a_st.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_out.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_scr.sub_left (hp.arg_sub h₁ h₂)
  · exact hp.a_stk.sub_left (hp.arg_sub h₁ h₂)

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (finalize w name code) s₀ fun s' => abiPreserved s₀ s' ∧ (finalizeX86 P).post s₀ s' := by
  have hl := hP.len
  have hpos := hP.pos
  have hN := hP.N
  obtain fS := hp.st_fit; have fO := hp.out_fit; have fC := hp.scr_fit
  obtain hstN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_using [])
  obtain hsc : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega_using [])
  obtain eB : (st s₀ + BitVec.ofNat 32 (bufOff w)).setWidth 64 = stA s₀ + BitVec.ofNat 64 (bufOff w) :=
    sw_add (by omega_using [hN, fS])
  obtain hbuf : Region.Sub ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩ (stR s₀ w) :=
    Offset.sub_base _ (by omega_using [])
  unfold finalize
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ h₁ => ?_)
  obtain F₁ : Frame [scR s₀] s₀.mem s₁.mem := by rw [h₁.mem]; exact saveMem_frame hp.scr_fit s₀
  refine WP.seq (WP.mono (bufLen_val hP h₁.eax h₁.ecx) fun s₂ ⟨ax₂, g₂, m₂, rd₂, wr₂⟩ => ?_)
  generalize hr : Proof.Blake2.bufLen w (arg s₀ 2 ++ arg s₀ 1).toNat = r at ax₂
  obtain hrB : r ≤ blockBytes w := hr ▸ bufLen_le hpos _
  obtain bx₂ : s₂.gpr .ebx = st s₀ := by rw [g₂ _ (by decide) (by decide), h₁.ebx]
  obtain eP : r < blockBytes w → addr (st s₀) (bufOff w + r) = stA s₀ + BitVec.ofNat 64 (bufOff w + r) :=
    fun h => addr_eq (by omega_using [fS, h])
  refine WP.seq (WP.mono (pad_ok hP hrB fS bx₂ ax₂ fun i hi => ?_) fun s₃ ⟨g₃, rd₃, wr₃, m₃⟩ => ?_)
  · rw [wr₂, h₁.wr, hp.wr, eP (by omega_using [hi]), Offset.add_add]
    exact ⟨stR s₀ w, by simp, contains_offset (by omega_using [hi]) (by omega_using [fS, hi])⟩
  obtain hm₃ : s₃.mem = writeBytes s₁.mem (stA s₀ + BitVec.ofNat 64 (bufOff w + r))
      (List.replicate (blockBytes w - r) 0) := by
    rw [m₃, m₂]
    by_cases h : r < blockBytes w
    · rw [eP h]
    · rw [show blockBytes w - r = 0 by omega_using [h], List.replicate_zero, writeBytes_nil, writeBytes_nil]
  obtain F₃ : Frame [stR s₀ w] s₁.mem s₃.mem := by
    rw [hm₃]; exact writeBytes_frame _ _ _ (contains_offset (by simp; omega_using [hrB]) (by omega_using [fS, hrB]))
  obtain F₀₃ : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₀.mem s₃.mem :=
    (F₁.mono (by simp)).trans (F₃.mono (by simp))
  obtain g₃' : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₃.gpr x = s₁.gpr x := fun x h1 h2 h3 => by
    rw [g₃ x h1 h2 h3, g₂ x h1 h2]
  obtain rd₃' : s₃.rd = s₀.rd := by rw [rd₃, rd₂, h₁.rd]
  obtain wr₃' : s₃.wr = s₀.wr := by rw [wr₃, wr₂, h₁.wr]
  obtain sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [g₃' _ (by decide) (by decide) (by decide), h₁.esp]
  -- The call.
  refine WP.seq ?_
  unfold compressLast
  refine WP.seq (wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => wp_movi fun s₆ u₆ => wp_movi fun s₇ u₇ => ?_)
  obtain g₇ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .eax → s₇.gpr x = s₃.gpr x := fun x h1 h2 h3 => by
    rw [u₇.other x h3, u₆.other x h2, u₅.other x h1, u₄.other x h1]
  obtain m₇ : s₇.mem = s₃.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃']
  obtain sp₇ : s₇.gpr .esp = esp₀ s₀ := by rw [g₇ _ (by decide) (by decide) (by decide), sp₃]
  refine wp_ldm sp₇ (hp.rin rd₇ (d := 8) (by omega_using []) (by omega_using [])) fun s₈ u₈ => ?_
  obtain i12 := hp.rin rd₇ (d := 12) (by omega_using []) (by omega_using [])
  refine wp_ldm (by rw [u₈.other _ (by decide), sp₇]) (by rw [u₈.rd, u₈.wr]; exact i12) fun s₉ u₉ => WP.block_nil ?_
  obtain g₉ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .eax → x ≠ .ecx → x ≠ .edx → s₉.gpr x = s₁.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₉.other x h5, u₈.other x h4, g₇ x h1 h2 h3, g₃' x h3 h4 h5]
  obtain m₉ : s₉.mem = s₃.mem := by rw [u₉.mem, u₈.mem, m₇]
  obtain rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, rd₇]
  obtain wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, wr₇]
  obtain cx₉ : s₉.gpr .ecx = arg s₀ 1 := by
    rw [u₉.other _ (by decide), u₈.gpr, m₇, arg_keep hp F₀₃ (by omega_using []) (by omega_using [])]; rfl
  obtain dx₉ : s₉.gpr .edx = arg s₀ 2 := by
    rw [u₉.gpr, u₈.mem, m₇, arg_keep hp F₀₃ (by omega_using []) (by omega_using [])]; rfl
  obtain esp₉ : s₉.gpr .esp = esp₀ s₀ := by
    rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.esp]
  refine call_ok (P := P) hf (k := 1) esp₉
    (by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebx])
    (by rw [g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.gpr, u₄.gpr, g₃' _ (by decide) (by decide) (by decide), h₁.ebx, N_eq])
    (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; rfl)
    cx₉ dx₉ (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]) hp.sp_lo (by omega_using [fS])
    (by rw [toNat_add_ofNat (by omega_using [hN, fS])]; omega_using [fS]) (by omega_using [fC])
    ((hp.st_scr.sub_left hstN).sub_right hsc) (by rw [eB]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_using [fS]))
    (by rw [eB, Nat.mul_one]; exact (hp.st_scr.sub_left hbuf).sub_right hsc) (hp.stk_st.sub_right hstN)
    (hp.stk_scr.sub_right hsc) (by rw [eB, Nat.mul_one]; exact hp.stk_st.sub_right hbuf) ?_ ?_ fun s₁₀ rd₁₀ wr₁₀ cs₁₀ f₁₀ e₁₀ => ?_
  · rw [rd₉, wr₉, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀ w, by simp, bufOff w, by rw [eB], by simp only; omega_using []⟩
  · rw [wr₉, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp only; omega_using []⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp only; omega_using []⟩
  obtain sp₁₀ : s₁₀.gpr .esp = esp₀ s₀ := by rw [cs₁₀ _ (by decide), esp₉]
  obtain bx₁₀ : s₁₀.gpr .ebx = st s₀ := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebx]
  obtain bp₁₀ : s₁₀.gpr .ebp = scr s₀ := by
    rw [cs₁₀ _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.ebp]
  obtain rd₁₀' : s₁₀.rd = s₀.rd := rd₁₀.trans rd₉
  obtain wr₁₀' : s₁₀.wr = s₀.wr := wr₁₀.trans wr₉
  obtain F₃₁₀ : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₃.mem s₁₀.mem := by
    rw [← m₉]
    refine f₁₀.sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, hstN⟩
    · exact ⟨scR s₀, by simp, hsc⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  obtain F₀₁₀ := F₀₃.trans F₃₁₀
  refine wp_ldm sp₁₀ (hp.rin rd₁₀' (d := 16) (by omega_using []) (by omega_using [])) fun s₁₁ u₁₁ => ?_
  obtain ax₁₁ : s₁₁.gpr .eax = op s₀ := by rw [u₁₁.gpr, arg_keep hp F₀₁₀ (by omega_using []) (by omega_using [])]; rfl
  obtain bx₁₁ : s₁₁.gpr .ebx = st s₀ := by rw [u₁₁.other _ (by decide), bx₁₀]
  rw [show (output w).append restore = output w ++ restore from rfl, WP.block_append_iff]
  obtain hN4 : bufOff w % 4 = 0 := by rcases hP.bb with h | h <;> omega_using [hN, h]
  refine WP.mono (output_ok (σ := s₁₁) hN4 (by rw [bx₁₁]; omega_using [fS]) (by rw [ax₁₁]; omega_using [fO])
    (fun a n h => ?_) (fun a n h => ?_) (by rw [bx₁₁, ax₁₁]; exact hp.st_out.sub_left hstN))
    fun s₁₂ ⟨g₁₂, rd₁₂, wr₁₂, m₁₂⟩ => ?_
  · rw [u₁₁.rd, u₁₁.wr, rd₁₀', wr₁₀', hp.rd, hp.wr]
    rw [bx₁₁] at h
    exact ⟨stR s₀ w, by simp, by simp only [Region.Contains, stA] at h ⊢; omega_using [h]⟩
  · rw [u₁₁.wr, wr₁₀', hp.wr]
    rw [ax₁₁] at h
    exact ⟨outR s₀ w, by simp, h⟩
  obtain F₁₂ : Frame [outR s₀ w] s₁₁.mem s₁₂.mem := by
    rw [m₁₂, ax₁₁]
    exact writeBytes_frame _ _ _ (contains_prefix _ (by simp [bytesAt]))
  -- The saved registers.
  obtain sv₁ : Saved (scr s₀) s₀ s₁.mem := by rw [h₁.mem]; exact saveMem_saved hp.scr_fit s₀
  obtain sv₃ : Saved (scr s₀) s₀ s₃.mem :=
    Saved.keep hp.scr_fit sv₁ (F₃.mono fun r hr => List.mem_cons_of_mem _ hr) (by simpa using hp.st_scr.symm)
  obtain f₁₀' : Frame [⟨scA s₀, 512⟩, ⟨stA s₀, bufOff w⟩, stkR s₀] s₉.mem s₁₀.mem :=
    f₁₀.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
  obtain sv₁₀ : Saved (scr s₀) s₀ s₁₀.mem :=
    Saved.keep hp.scr_fit (by rw [m₉]; exact sv₃) f₁₀' (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨(hp.st_scr.sub_left hstN).symm, hp.stk_scr.symm⟩)
  obtain sv₁₂ : Saved (scr s₀) s₀ s₁₂.mem :=
    Saved.keep hp.scr_fit (by rw [← u₁₁.mem] at sv₁₀; exact sv₁₀) (F₁₂.mono fun r hr => List.mem_cons_of_mem _ hr)
      (by simpa using hp.out_scr.symm)
  obtain bp₁₂ : s₁₂.gpr .ebp = scr s₀ := by rw [g₁₂ _ (by decide), u₁₁.other _ (by decide), bp₁₀]
  refine WP.mono (restore_ok hp bp₁₂ (by rw [rd₁₂, u₁₁.rd, rd₁₀']) (by rw [wr₁₂, u₁₁.wr, wr₁₀']) sv₁₂)
    fun s₁₃ ⟨cs₁₃, sp₁₃, m₁₃⟩ => ?_
  obtain F₀₁₂ : Frame [stR s₀ w, outR s₀ w, scR s₀, stkR s₀] s₀.mem s₁₂.mem :=
    F₀₁₀.trans (by rw [← u₁₁.mem]; exact F₁₂.mono (by simp))
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun h0 d hR hlt hcnt => ?_⟩
  · by_cases h : r = .esp
    · subst h
      rw [sp₁₃, g₁₂ _ (by decide), u₁₁.other _ (by decide), sp₁₀]
    · exact cs₁₃ r hr h
  · rw [m₁₃]
    exact F₀₁₂.readW (Region.contains_self _ _)
      (by simpa using ⟨hp.ret_st, hp.ret_out, hp.ret_scr, hp.ret_stk⟩) (by decide)
  · have hn : (arg s₀ 2 ++ arg s₀ 1).toNat = d.length := by
      show (countX86 s₀).toNat = _
      rw [hcnt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [hn] at hr
    subst hr
    obtain hst : ∀ i < bufOff w + blockBytes w,
        s₁.mem (stA s₀ + BitVec.ofNat 64 i) = s₀.mem (stA s₀ + BitVec.ofNat 64 i) :=
      fun i hi => F₁.bytes (R := stR s₀ w) (by simpa using hp.st_scr) (by simp only; omega_using [fS]) hi
    show bytesAt s₁₃.mem (opA s₀) (bufOff w) = _
    rw [m₁₃, m₁₂, ax₁₁, bx₁₁, bytesAt_writeBytes_self _ _ (by simp [bytesAt]) (by omega_using [fO]), u₁₁.mem,
      bytesAt_state _ _ (by rcases hP.w with h | h <;> simp [h]), e₁₀,
      show ((1 : BitVec 32) != 0) = true from rfl, compressBlocks_one, hn, eB, m₉]
    refine final_eq P hpos hR ?_ ?_
    · exact stateAt_congr fun i hi => by
        rw [hm₃, writeBytes_before s₁.mem _ _ (by omega_using [hi] : i < bufOff w + Proof.Blake2.bufLen w d.length)
          (by simp; omega_using [fS, hrB]), hst i (by omega_using [hi])]
    · rw [pad_bytes hrB (by omega_using [fS]) hm₃]
      congr 1
      exact bytesAt_congr fun i hi => by rw [Offset.add_ofNat_add_ofNat, hst _ (by omega_using [hrB, hi])]

end VG.Proof.Blake2.X86.Stream.Finalize

end

end

/-! ### `Blake2.X86.Stream.Update`, which this module and modules that import it used -/

section

/-!
# Streaming BLAKE2 on x86 (32-bit): `update`

The functional correctness of `update`, for either word size and any correct
compression function (`CalleeOk`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (compressX86 updateX86 countX86 ReprR bufLen_le repr_iff reprR_append reprR_flush
  reprR_blocks repr_of_reprR stateAt_congr bytesAt_congr bytesAt_add compressBlocks_congr compressBlocks_succ
  compressBlocks_zero)
open VG.WriteBytes (writeBytes writeBytes_before writeBytes_frame)
open VG.Proof.MdStream.X86 (contains_addr addr_add_ofNat sub_offset contains_offset)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev cnt : Nat := (countX86 s₀).toNat
abbrev dp : BitVec 32 := arg s₀ 3
abbrev len : Nat := (arg s₀ 4).toNat
abbrev scr : BitVec 32 := arg s₀ 5
abbrev stA : Addr := (st s₀).setWidth 64
abbrev dA : Addr := (dp s₀).setWidth 64
abbrev scA : Addr := (scr s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev dR : Region := ⟨dA s₀, len s₀⟩
abbrev scR : Region := ⟨scA s₀, 576⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 24⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- Where the calls of the compression function push its arguments and store
the return address. -/
abbrev stkR : Region := below (esp₀ s₀) 32
/-- The first `c` bytes of data. -/
abbrev D (c : Nat) : List Byte := bytesAt s₀.mem (dA s₀) c

end

structure Pre (w : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [dR s₀, argR s₀]
  wr : s₀.wr = [stR s₀ w, scR s₀]
  st_scr : (stR s₀ w).Disjoint (scR s₀)
  d_st : (dR s₀).Disjoint (stR s₀ w)
  d_scr : (dR s₀).Disjoint (scR s₀)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  a_scr : (argR s₀).Disjoint (scR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  ret_scr : (retR s₀).Disjoint (scR s₀)
  stk_st : (stkR s₀).Disjoint (stR s₀ w)
  stk_scr : (stkR s₀).Disjoint (scR s₀)
  stk_d : (stkR s₀).Disjoint (dR s₀)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  d_fit : (dp s₀).toNat + len s₀ ≤ 2 ^ 32
  scr_fit : (scr s₀).toNat + 576 ≤ 2 ^ 32
  sp_lo : 32 ≤ (esp₀ s₀).toNat
  sp_fit : (esp₀ s₀).toNat + 28 ≤ 2 ^ 32

theorem pre_of {s₀ : State} (h : (updateX86 P).pre s₀) : Pre w s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  obtain e := stk_eq h16
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, by show (below _ _).Disjoint _; rw [e]; exact h10,
    by show (below _ _).Disjoint _; rw [e]; exact h11, by show (below _ _).Disjoint _; rw [e]; exact h12,
    h13, h14, h15, h16, h17⟩

theorem len_lt (s₀ : State) : len s₀ < 2 ^ 32 := (arg s₀ 4).isLt

theorem D_length (s₀ : State) (c : Nat) : (D s₀ c).length = c := by simp [bytesAt]

namespace Pre
variable {s₀ : State} (hp : Pre w s₀)
include hp

theorem scr_in {d : Nat} (hd : d + 4 ≤ 576) : (scR s₀).Contains (addr (scr s₀) d) 4 :=
  contains_addr hd (by omega_arith) hp.scr_fit

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 28) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 24⟩ : Region).Contains _ _
  rw [addr_eq (by omega_arith), addr_eq (by omega_arith)]
  exact Offset.contains _ hd₁ (by omega_arith) (by omega_arith)

theorem ret_stk : (retR s₀).Disjoint (stkR s₀) := by
  have := hp.sp_fit; have := hp.sp_lo
  show Region.Disjoint ⟨(esp₀ s₀).setWidth 64, 4⟩ ⟨(esp₀ s₀ - BitVec.ofNat 32 32).setWidth 64, 32⟩
  rw [Taint.sub_setWidth (by omega_arith)]
  exact Offset.base_disjoint_below _ (by omega_arith)

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 28) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

theorem sin {s : State} (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions s.wr (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hwr, hp.wr], hp.scr_in hd⟩

theorem sinr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 576) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  ⟨scR s₀, by simp [hrd, hwr, hp.wr], hp.scr_in hd⟩

/-- The scratch space is disjoint from the other regions the code writes. -/
theorem scr_disj : ∀ r ∈ [stR s₀ w, stkR s₀], Region.Disjoint ⟨(scr s₀).setWidth 64, 576⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.st_scr.symm, hp.stk_scr.symm⟩

end Pre

/-- The data the initial state represents, from `h0`. -/
def R₀ (P : Params w) (s₀ : State) (h0 : HashValue w) (d : List Byte) : Prop :=
  Spec.Blake2.Repr P h0 s₀.mem (stA s₀) d ∧ countX86 s₀ = BitVec.ofNat 64 d.length ∧
    d.length + len s₀ < 2 ^ 64

theorem R₀.cnt_eq {s₀ : State} {h0 : HashValue w} {d : List Byte} (h : R₀ P s₀ h0 d) :
    cnt s₀ = d.length := by
  rw [cnt, h.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.2.2; omega_arith)]

/-! ## Invariants -/

/-- What holds throughout, after consuming `c` bytes of data. -/
structure Common (w : Nat) (s₀ : State) (c : Nat) (s : State) : Prop where
  c_le : c ≤ len s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  ebx : s.gpr .ebx = st s₀
  ebp : s.gpr .ebp = scr s₀
  esp : s.gpr .esp = esp₀ s₀
  frame : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s.mem
  saved : Saved (scr s₀) s₀ s.mem

/-- The state represents the data followed by the first `c` bytes of data,
the last `r` of them in the buffer. -/
structure Inv (P : Params w) (s₀ : State) (c r : Nat) (s : State) : Prop extends Common w s₀ c s where
  repr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ c) r

/-- The data pointer and the bytes left. -/
structure Ptr (s₀ : State) (c : Nat) (s : State) : Prop where
  esi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c
  edi : s.gpr .edi = BitVec.ofNat 32 (len s₀ - c)

/-- The byte count. -/
structure Cnt (s₀ : State) (c : Nat) (m : Mem) : Prop where
  lo : m.readW (addr (scr s₀) cloOff) 32 = BitVec.ofNat 32 (cnt s₀ + c)
  hi : m.readW (addr (scr s₀) chiOff) 32 = BitVec.ofNat 32 ((cnt s₀ + c) / 2 ^ 32)

theorem Common.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Common w s₀ c s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Common w s₀ c s' where
  c_le := h.c_le
  rd := hrd.trans h.rd
  wr := hwr.trans h.wr
  ebx := by rw [hg _ (by simp)]; exact h.ebx
  ebp := by rw [hg _ (by simp)]; exact h.ebp
  esp := by rw [hg _ (by simp)]; exact h.esp
  frame := by rw [hm]; exact h.frame
  saved := by rw [hm]; exact h.saved

theorem Inv.of_gpr {s₀ : State} {c r : Nat} {s s' : State} (h : Inv P s₀ c r s)
    (hg : ∀ r ∈ [Reg.ebx, .ebp, .esp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Inv P s₀ c r s' :=
  { h.toCommon.of_gpr hg hm hrd hwr with repr := by rw [hm]; exact h.repr }

theorem Ptr.of_gpr {s₀ : State} {c : Nat} {s s' : State} (h : Ptr s₀ c s)
    (h₁ : s'.gpr .esi = s.gpr .esi) (h₂ : s'.gpr .edi = s.gpr .edi) : Ptr s₀ c s' :=
  ⟨h₁.trans h.esi, h₂.trans h.edi⟩

/-- The data is unchanged. -/
theorem Common.data {s₀ : State} (hp : Pre w s₀) {c : Nat} {s : State} (h : Common w s₀ c s) {i : Nat}
    (hi : i < len s₀) : s.mem (dA s₀ + BitVec.ofNat 64 i) = s₀.mem (dA s₀ + BitVec.ofNat 64 i) :=
  h.frame.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
    (by have := len_lt s₀; simp only; omega_arith) hi

/-- Writes to the scratch space keep the state's bytes. -/
theorem st_keep (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (hf : Frame [scR s₀] m m') :
    ∀ i < bufOff w + blockBytes w, m' (stA s₀ + BitVec.ofNat 64 i) = m (stA s₀ + BitVec.ofNat 64 i) :=
  fun i hi => hf.bytes (R := stR s₀ w) (by simpa using hp.st_scr) (by have := hP.len; simp only; omega_arith) hi

/-! ## Prologue -/

/-- The memory after the prologue. -/
def proMem (s₀ : State) : Mem :=
  ((saveMem (scr s₀) s₀).writeW (addr (scr s₀) cloOff) (arg s₀ 1)).writeW (addr (scr s₀) chiOff) (arg s₀ 2)

theorem proMem_frame {s₀ : State} (hp : Pre w s₀) : Frame [scR s₀] s₀.mem (proMem s₀) :=
  ((saveMem_frame hp.scr_fit s₀).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
    (List.mem_singleton_self _) _ (hp.scr_in (by decide))

theorem cnt_lo (s₀ : State) : BitVec.ofNat 32 (cnt s₀) = arg s₀ 1 := lo_append _ _
theorem cnt_hi (s₀ : State) : BitVec.ofNat 32 (cnt s₀ / 2 ^ 32) = arg s₀ 2 := hi_append _ _

theorem proMem_cnt {s₀ : State} (hp : Pre w s₀) : Cnt s₀ 0 (proMem s₀) := by
  refine ⟨?_, ?_⟩ <;> simp only [proMem, Nat.add_zero]
  · rw [rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, cnt_lo]
  · rw [Mem.readW_writeW_self32, cnt_hi]

theorem proMem_saved {s₀ : State} (hp : Pre w s₀) : Saved (scr s₀) s₀ (proMem s₀) :=
  (saveMem_saved hp.scr_fit s₀).of_readW fun p hp' => by
    have := saved_bound p hp'
    simp only [proMem]
    rw [rw_scr hp.scr_fit _ _ (by omega_arith) (by decide) (by simp only [chiOff]; omega_arith),
      rw_scr hp.scr_fit _ _ (by omega_arith) (by decide) (by simp only [cloOff]; omega_arith)]

theorem prologue_ok {s₀ : State} (hp : Pre w s₀) :
    WP isa (.block updateStart) s₀ fun s =>
      Common w s₀ 0 s ∧ Ptr s₀ 0 s ∧ s.mem = proMem s₀ ∧ s.gpr .eax = arg s₀ 1 ∧ s.gpr .ecx = arg s₀ 2 := by
  obtain rin : ∀ {d}, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₀.rd ++ s₀.wr) (addr (esp₀ s₀) d) 4 :=
    fun h₁ h₂ => hp.rin rfl h₁ h₂
  obtain sin : ∀ {d}, d + 4 ≤ 576 → InRegions s₀.wr (addr (scr s₀) d) 4 := fun h => hp.sin rfl h
  -- The saves only touch the scratch space, so the arguments stay readable.
  obtain sepA : ∀ d e, 512 ≤ d → d + 4 ≤ 576 → 4 ≤ e → e + 4 ≤ 28 →
      Mem.Sep (addr (esp₀ s₀) e) 4 (addr (scr s₀) d) 4 := by
    intro d e h₁ h₂ h₃ h₄
    exact hp.a_scr.sep (hp.arg_in h₃ h₄) (hp.scr_in h₂)
  obtain argSave : ∀ e, 4 ≤ e → e + 4 ≤ 28 →
      (saveMem (scr s₀) s₀).readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 := by
    intro e h₁ h₂
    exact Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      have := saved_bound p h; sepA _ e this.1 (by omega_arith) h₁ h₂
  rw [show updateStart = .mov .eax (.mem (at_ .esp 24)) :: (Spill.saveCode .eax saved ++
    ([.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 16)),
      .mov .edi (.mem (at_ .esp 20)), .mov .eax (.mem (at_ .esp 8)), .store (at_ .ebp cloOff) .eax,
      .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp chiOff) .ecx] : List Instr)) from rfl]
  refine wp_ldm (B := esp₀ s₀) rfl (rin (d := 24) (by omega_arith) (by omega_arith)) fun s₁ u₁ => ?_
  have e₁ : s₁.gpr .eax = scr s₀ := u₁.gpr
  refine Spill.save_ok saved (fun p h => by
    rw [e₁, u₁.wr]; exact sin (by have := saved_bound p h; omega_arith)) fun s₅ u₅ => ?_
  have g₅ : s₅.gpr = s₁.gpr := u₅.gpr
  obtain m₅ : s₅.mem = saveMem (scr s₀) s₀ := by
    rw [u₅.mem, e₁, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₁.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₁.wr]
  obtain sp₅ : s₅.gpr .esp = esp₀ s₀ := by rw [g₅, u₁.other _ (by decide)]
  obtain ld : ∀ e, 4 ≤ e → e + 4 ≤ 28 → s₅.mem.readW (addr (esp₀ s₀) e) 32 = s₀.mem.readW (addr (esp₀ s₀) e) 32 :=
    fun e h₁ h₂ => by rw [m₅]; exact argSave e h₁ h₂
  refine wp_mov fun s₆ u₆ => ?_
  obtain ebp₆ : s₆.gpr .ebp = scr s₀ := by rw [u₆.gpr, g₅, e₁]
  obtain sp₆ : s₆.gpr .esp = esp₀ s₀ := by rw [u₆.other _ (by decide), sp₅]
  obtain rd' : ∀ d, 4 ≤ d → d + 4 ≤ 28 → InRegions (s₆.rd ++ s₆.wr) (addr (esp₀ s₀) d) 4 :=
    fun d h₁ h₂ => by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact rin h₁ h₂
  refine wp_ldm sp₆ (rd' 4 (by omega_arith) (by omega_arith)) fun s₇ u₇ => ?_
  refine wp_ldm (by rw [u₇.other _ (by decide), sp₆]) (by rw [u₇.rd, u₇.wr]; exact rd' 16 (by omega_arith) (by omega_arith))
    fun s₈ u₈ => ?_
  refine wp_ldm (by rw [u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 20 (by omega_arith) (by omega_arith)) fun s₉ u₉ => ?_
  refine wp_ldm (by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), sp₆])
    (by rw [u₉.rd, u₉.wr, u₈.rd, u₈.wr, u₇.rd, u₇.wr]; exact rd' 8 (by omega_arith) (by omega_arith)) fun s₁₀ u₁₀ => ?_
  obtain g₁₀ : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .esi → r ≠ .ebx → s₁₀.gpr r = s₆.gpr r := fun r a b c d => by
    rw [u₁₀.other r a, u₉.other r b, u₈.other r c, u₇.other r d]
  obtain m₁₀ : s₁₀.mem = saveMem (scr s₀) s₀ := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
  obtain rd₁₀ : s₁₀.rd = s₀.rd := by rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  obtain wr₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  refine wp_stm (by rw [g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆])
    (hp.sin wr₁₀ (d := cloOff) (by decide)) fun s₁₁ u₁₁ => ?_
  refine wp_ldm (by rw [u₁₁.gpr, g₁₀ _ (by decide) (by decide) (by decide) (by decide), sp₆])
    (by rw [u₁₁.rd, u₁₁.wr]; exact hp.rin rd₁₀ (d := 12) (by omega_arith) (by omega_arith)) fun s₁₂ u₁₂ => ?_
  refine wp_stm (by rw [u₁₂.other _ (by decide), u₁₁.gpr, g₁₀ _ (by decide) (by decide) (by decide) (by decide),
    ebp₆]) (by rw [u₁₂.wr, u₁₁.wr]; exact hp.sin wr₁₀ (d := chiOff) (by decide)) fun s₁₃ u₁₃ => WP.block_nil ?_
  -- The argument words the loads read.
  obtain a8 : s₁₀.gpr .eax = arg s₀ 1 := by
    rw [u₁₀.gpr, u₉.mem, u₈.mem, u₇.mem, u₆.mem, ld 8 (by omega_arith) (by omega_arith)]; rfl
  obtain a12 : s₁₂.gpr .ecx = arg s₀ 2 := by
    rw [u₁₂.gpr, u₁₁.mem, m₁₀, Mem.readW_writeW_sep (sepA cloOff 12 (by decide) (by decide) (by omega_arith)
      (by omega_arith)) (by decide), argSave 12 (by omega_arith) (by omega_arith)]; rfl
  obtain g₁₃ : ∀ r, r ≠ .ecx → s₁₃.gpr r = s₁₀.gpr r := fun r h => by
    rw [u₁₃.gpr, u₁₂.other r h, u₁₁.gpr]
  obtain m₁₃ : s₁₃.mem = proMem s₀ := by
    rw [u₁₃.mem, a12, u₁₂.mem, u₁₁.mem, a8, m₁₀]; rfl
  obtain rd₁₃ : s₁₃.rd = s₀.rd := by rw [u₁₃.rd, u₁₂.rd, u₁₁.rd, rd₁₀]
  obtain wr₁₃ : s₁₃.wr = s₀.wr := by rw [u₁₃.wr, u₁₂.wr, u₁₁.wr, wr₁₀]
  obtain l4 : s₆.mem.readW (addr (esp₀ s₀) 4) 32 = arg s₀ 0 := by rw [u₆.mem, ld 4 (by omega_arith) (by omega_arith)]; rfl
  obtain l16 : s₆.mem.readW (addr (esp₀ s₀) 16) 32 = arg s₀ 3 := by
    rw [u₆.mem, ld 16 (by omega_arith) (by omega_arith)]; rfl
  obtain l20 : s₆.mem.readW (addr (esp₀ s₀) 20) 32 = arg s₀ 4 := by
    rw [u₆.mem, ld 20 (by omega_arith) (by omega_arith)]; rfl
  refine ⟨⟨Nat.zero_le _, rd₁₃, wr₁₃, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, m₁₃, ?_, ?_⟩
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, l4]
  · rw [g₁₃ _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide), ebp₆]
  · rw [g₁₃ _ (by decide), g₁₀ _ (by decide) (by decide) (by decide) (by decide), sp₆]
  · rw [m₁₃]; exact (proMem_frame hp).mono (by simp)
  · rw [m₁₃]; exact proMem_saved hp
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.mem, l16]; simp
  · rw [g₁₃ _ (by decide), u₁₀.other _ (by decide), u₉.gpr, u₈.mem, u₇.mem, l20]; simp
  · rw [g₁₃ _ (by decide), a8]
  · rw [u₁₃.gpr, a12]

/-! ## The bytes in the buffer -/

theorem bufLen_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {s : State} (hC : Common w s₀ 0 s)
    (hptr : Ptr s₀ 0 s) (hm : s.mem = proMem s₀) (hax : s.gpr .eax = arg s₀ 1) (hcx : s.gpr .ecx = arg s₀ 2) :
    WP isa (Impl.Blake2.X86.Stream.bufLen w) s fun s' =>
      Inv P s₀ 0 (Proof.Blake2.bufLen w (cnt s₀)) s' ∧ Ptr s₀ 0 s' ∧ Cnt s₀ 0 s'.mem ∧
        s'.gpr .eax = BitVec.ofNat 32 (Proof.Blake2.bufLen w (cnt s₀)) := by
  -- The representation.
  obtain hrepr : ∀ h0 d, R₀ P s₀ h0 d →
      ReprR P h0 s.mem (stA s₀) (d ++ D s₀ 0) (Proof.Blake2.bufLen w (cnt s₀)) := by
    intro h0 d hd
    obtain e : D s₀ 0 = [] := by simp [bytesAt]
    rw [e, List.append_nil, hd.cnt_eq, ← repr_iff P hP.pos, hm]
    exact repr_congr hP (st_keep hP hp (proMem_frame hp)) hd.1
  obtain hcnt := proMem_cnt hp
  rw [← hm] at hcnt
  unfold Impl.Blake2.X86.Stream.bufLen
  refine WP.seq (wp_orZ fun s₁ u₁ z₁ => WP.block_nil ?_)
  obtain hz : isa.eval .e s₁ = some (decide (cnt s₀ = 0)) := by
    show s₁.zf = _
    rw [z₁, hcx, hax, or_beq_zero]; rfl
  obtain hC₁ : Common w s₀ 0 s₁ := hC.of_gpr (fun r hr => u₁.other r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
    u₁.mem u₁.rd u₁.wr
  obtain hptr₁ : Ptr s₀ 0 s₁ := hptr.of_gpr (u₁.other _ (by decide)) (u₁.other _ (by decide))
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine wp_movi fun s₂ u₂ => WP.block_nil ?_
    obtain e : Proof.Blake2.bufLen w (cnt s₀) = 0 := by simp [Proof.Blake2.bufLen, hb]
    refine ⟨{ hC₁.of_gpr (fun r hr => u₂.other r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      u₂.mem u₂.rd u₂.wr with repr := ?_ }, hptr₁.of_gpr (u₂.other _ (by decide)) (u₂.other _ (by decide)),
      by rw [u₂.mem, u₁.mem]; exact hcnt, by rw [u₂.gpr, e]; rfl⟩
    rw [u₂.mem, u₁.mem]; exact hrepr
  · simp only [decide_eq_false_iff_not] at hb
    refine wp_subi fun s₂ u₂ _ _ => wp_andi fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_
    obtain g : ∀ r, r ≠ .eax → s₄.gpr r = s₁.gpr r := fun r h => by
      rw [u₄.other r h, u₃.other r h, u₂.other r h]
    obtain hm₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine ⟨{ hC₁.of_gpr (fun r hr => g r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide))
      (by rw [hm₄, u₁.mem]) (by rw [u₄.rd, u₃.rd, u₂.rd]) (by rw [u₄.wr, u₃.wr, u₂.wr]) with repr := ?_ },
      hptr₁.of_gpr (g _ (by decide)) (g _ (by decide)), by rw [hm₄]; exact hcnt, ?_⟩
    · rw [hm₄]; exact hrepr
    · rw [u₄.gpr, u₃.gpr, u₂.gpr, u₁.other _ (by decide), hax, ← cnt_lo, mask_ofNat hP hb]
      simp [Proof.Blake2.bufLen, hb]

/-! ## Copying data into the buffer -/

theorem dp_add {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc : c < len s₀) :
    (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = dA s₀ + BitVec.ofNat 64 c :=
  sw_add (by have := hp.d_fit; omega_arith)

/-- Copying `k` bytes of data, from byte `c` on, into the buffer, from byte
`r` on: only the buffer changes. -/
theorem copy_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r k : Nat} (hk : 1 ≤ k)
    (hrk : r + k ≤ blockBytes w) (hck : c + k ≤ len s₀) {s : State}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hesi : s.gpr .esi = dp s₀ + BitVec.ofNat 32 c)
    (hedx : s.gpr .edx = st s₀ + BitVec.ofNat 32 r) (hecx : s.gpr .ecx = BitVec.ofNat 32 k)
    (hf : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s.mem)
    (hrepr : ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s.mem (stA s₀) (d ++ D s₀ c) r) :
    WP isa (copyLoop w .esi .edx .ecx .al) s fun s' =>
      (∀ x, x ≠ .esi → x ≠ .edx → x ≠ .ecx → x ≠ .eax → s'.gpr x = s.gpr x) ∧
      s'.gpr .esi = dp s₀ + BitVec.ofNat 32 (c + k) ∧ s'.rd = s₀.rd ∧ s'.wr = s₀.wr ∧
      Frame [stR s₀ w] s.mem s'.mem ∧
      ∀ h0 d, R₀ P s₀ h0 d → ReprR P h0 s'.mem (stA s₀) (d ++ D s₀ (c + k)) (r + k) := by
  have hl := hP.len
  obtain hL := len_lt s₀
  have fS := hp.st_fit
  have fD := hp.d_fit
  have hN : bufOff w = blockBytes w / 2 := hP.N
  obtain eD : addr (st s₀ + BitVec.ofNat 32 r) (bufOff w) = stA s₀ + BitVec.ofNat 64 (bufOff w + r) := by
    rw [MdStream.X86.addr_add_ofNat (by omega_arith), Nat.add_comm]
  obtain eS : (dp s₀ + BitVec.ofNat 32 c).setWidth 64 = dA s₀ + BitVec.ofNat 64 c := dp_add hp (by omega_arith)
  obtain hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) ((dp s₀ + BitVec.ofNat 32 c).setWidth 64 + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨dR s₀, by simp [hrd, hp.rd], by
      rw [eS, Offset.add_add]; exact contains_offset (by omega_arith) (by omega_arith)⟩
  obtain hdst : ∀ i < k, InRegions s.wr (addr (st s₀ + BitVec.ofNat 32 r) (bufOff w) + BitVec.ofNat 64 i) 1 :=
    fun i hi => ⟨stR s₀ w, by simp [hwr, hp.wr], by
      rw [eD, Offset.add_add]; exact contains_offset (by omega_arith) (by omega_arith)⟩
  obtain hd : Region.Disjoint ⟨(dp s₀ + BitVec.ofNat 32 c).setWidth 64, k⟩
      ⟨addr (st s₀ + BitVec.ofNat 32 r) (bufOff w), k⟩ := by
    rw [eS, eD]
    exact (hp.d_st.sub_left (sub_offset (by omega_arith) (by omega_arith))).sub_right (sub_offset (by omega_arith) (by omega_arith))
  refine copyLoop_ok (w := w) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hk
    (by omega_arith) (by rw [toNat_add_ofNat (by omega_arith)]; omega_arith) (by rw [toNat_add_ofNat (by omega_arith)]; omega_arith)
    hesi hedx hecx hsrc hdst hd fun s' h => ?_
  -- The bytes copied.
  obtain hx : bytesAt s.mem ((dp s₀ + BitVec.ofNat 32 c).setWidth 64) k =
      bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
    rw [eS]
    refine bytesAt_congr fun i hi => ?_
    rw [Offset.add_add]
    exact hf.bytes (R := dR s₀) (by simpa using ⟨hp.d_st, hp.d_scr, hp.stk_d.symm⟩)
      (by simp only; omega_arith) (show c + i < len s₀ by omega_arith)
  obtain hm : s'.mem = writeBytes s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w + r))
      (bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k) := by
    rw [h.mem, List.take_of_length_le (by rw [bytesAt_length]), hx, eD]
  obtain hfw : Frame [stR s₀ w] s.mem s'.mem := by
    rw [hm]; exact writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact contains_offset (by omega_arith) (by omega_arith))
  refine ⟨fun x a b c d => h.other x a b c d, ?_, h.rd.trans hrd, h.wr.trans hwr, hfw, fun h0 d hd => ?_⟩
  · rw [h.srcV, BitVec.add_assoc, BitVec.ofNat_add]
  obtain e : d ++ D s₀ (c + k) = d ++ D s₀ c ++ bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k := by
    rw [D, bytesAt_add, List.append_assoc]
  rw [e]
  have := reprR_append P (hrepr h0 d hd) (x := bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 c) k)
    (mem' := s'.mem) (by rw [bytesAt_length]; exact hrk) ?_ ?_
  · rwa [bytesAt_length] at this
  · rw [hm]
    exact stateAt_congr fun i hi => VG.WriteBytes.writeBytes_before _ _ _ (by omega_arith)
      (by rw [bytesAt_length]; omega_arith)
  · rw [hm, ← Offset.add_add, bytesAt_writeBytes _ _ _ _ (by rw [bytesAt_length]; omega_arith)]

/-! ## Writes to the scratch space and the buffer -/

theorem Saved.write {s₀ : State} (hp : Pre w s₀) {m : Mem} (h : Saved (scr s₀) s₀ m) {d : Nat} (hd : 528 ≤ d)
    (hd' : d + 4 ≤ 576) (v : BitVec 32) : Saved (scr s₀) s₀ (m.writeW (addr (scr s₀) d) v) :=
  h.of_readW fun p hp' => have := saved_bound p hp'; rw_scr hp.scr_fit _ _ (by omega_arith) hd' (by omega_arith)

theorem Saved.st {s₀ : State} (hp : Pre w s₀) {m m' : Mem} (h : Saved (scr s₀) s₀ m)
    (hf : Frame [stR s₀ w] m m') : Saved (scr s₀) s₀ m' :=
  Saved.keep hp.scr_fit h (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
    (by simpa using hp.st_scr.symm)

theorem frame_scr {s₀ : State} (hp : Pre w s₀) {m : Mem} (hf : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem m)
    {d : Nat} (hd : d + 4 ≤ 576) (v : BitVec 32) :
    Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem (m.writeW (addr (scr s₀) d) v) :=
  hf.writeW (by simp) _ (hp.scr_in hd)

theorem frame_st {s₀ : State} {m m' : Mem} (hf : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem m)
    (hf' : Frame [stR s₀ w] m m') : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem m' :=
  hf.trans (hf'.mono (by simp))

/-- The byte count is kept by writes to the buffer. -/
theorem Cnt.st {s₀ : State} (hp : Pre w s₀) {c : Nat} {m m' : Mem} (h : Cnt s₀ c m)
    (hf : Frame [stR s₀ w] m m') : Cnt s₀ c m' := by
  obtain k := fun d (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) =>
    keep_hi hp.scr_fit (m := m) (m' := m') (rs := [stR s₀ w]) (hf.mono fun r hr => List.mem_cons_of_mem _ hr)
      (by simpa using hp.st_scr.symm) h₁ h₂
  exact ⟨(k cloOff (by decide) (by decide)).trans h.lo, (k chiOff (by decide) (by decide)).trans h.hi⟩

/-! ## `fill` -/

theorem fill_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c r : Nat} (hr : r ≤ blockBytes w) {s : State}
    (hI : Inv P s₀ c r s) (hptr : Ptr s₀ c s) (hcnt : Cnt s₀ c s.mem) (hax : s.gpr .eax = BitVec.ofNat 32 r) :
    WP isa (fill w) s fun s' =>
      Inv P s₀ (c + min (blockBytes w - r) (len s₀ - c)) (r + min (blockBytes w - r) (len s₀ - c)) s' ∧
      Ptr s₀ (c + min (blockBytes w - r) (len s₀ - c)) s' ∧
      Cnt s₀ (c + min (blockBytes w - r) (len s₀ - c)) s'.mem := by
  have hl := hP.len
  obtain hL := len_lt s₀
  have hc := hI.c_le
  obtain ⟨a, ha⟩ : ∃ a, a = min (blockBytes w - r) (len s₀ - c) := ⟨_, rfl⟩
  rw [← ha]
  obtain ha₁ : a ≤ blockBytes w - r := ha ▸ Nat.min_le_left _ _
  obtain ha₂ : a ≤ len s₀ - c := ha ▸ Nat.min_le_right _ _
  unfold fill
  refine WP.seq (wp_movi fun s₁ u₁ => wp_sub fun s₂ u₂ _ => wp_cmp fun s₃ f₃ cf₃ _ => WP.block_nil ?_)
  obtain hcx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (blockBytes w - r) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hax, B_eq, sub_ofNat hr]
  obtain hdi₂ : s₂.gpr .edi = BitVec.ofNat 32 (len s₀ - c) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), hptr.edi]
  obtain g₃ : ∀ x, x ≠ .ecx → s₃.gpr x = s.gpr x := fun x h => by rw [f₃.gpr, u₂.other x h, u₁.other x h]
  -- `ecx` := `a`.
  refine WP.seq (WP.mono (Q := fun (t : State) => t.gpr .ecx = BitVec.ofNat 32 a ∧
      (∀ x, x ≠ .ecx → t.gpr x = s.gpr x) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ fun t ht => ?_)
  · have hm : s₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
    obtain hrd : s₃.rd = s.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
    obtain hwr : s₃.wr = s.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
    obtain hcf : isa.eval .b s₃ = some (decide (len s₀ - c < blockBytes w - r)) := by
      show s₃.cf = _
      rw [cf₃, hdi₂, hcx₂, toNat_ofNat_lt (by omega_arith), toNat_ofNat_lt (by omega_arith)]
    refine WP.ite _ hcf (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      refine wp_mov fun s₄ u₄ => WP.block_nil ⟨?_, fun x h => by rw [u₄.other x h, g₃ x h],
        by rw [u₄.mem, hm], by rw [u₄.rd, hrd], by rw [u₄.wr, hwr]⟩
      rw [u₄.gpr, f₃.gpr, hdi₂, ha, Nat.min_eq_right (by omega_arith)]
    · simp only [decide_eq_false_iff_not] at hb
      refine WP.block_nil ⟨?_, g₃, hm, hrd, hwr⟩
      rw [f₃.gpr, hcx₂, ha, Nat.min_eq_left (by omega_arith)]
  obtain ⟨tcx, tg, tm, trd, twr⟩ := ht
  obtain tbp : t.gpr .ebp = scr s₀ := by rw [tg _ (by decide), hI.ebp]
  obtain trd' : t.rd = s₀.rd := trd.trans hI.rd
  obtain twr' : t.wr = s₀.wr := twr.trans hI.wr
  refine WP.seq (wp_sub fun s₅ u₅ _ => wp_mov fun s₆ u₆ => wp_add fun s₇ u₇ _ => ?_)
  obtain g₇ : ∀ x, x ≠ .edx → x ≠ .edi → s₇.gpr x = t.gpr x := fun x h1 h2 => by
    rw [u₇.other x h1, u₆.other x h1, u₅.other x h2]
  obtain m₇ : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, tm]
  obtain rd₇ : s₇.rd = s₀.rd := by rw [u₇.rd, u₆.rd, u₅.rd, trd']
  obtain wr₇ : s₇.wr = s₀.wr := by rw [u₇.wr, u₆.wr, u₅.wr, twr']
  obtain bp₇ : s₇.gpr .ebp = scr s₀ := by rw [g₇ _ (by decide) (by decide), tbp]
  obtain cx₇ : s₇.gpr .ecx = BitVec.ofNat 32 a := by rw [g₇ _ (by decide) (by decide), tcx]
  -- The byte count.
  refine wp_ldmF bp₇ (hp.sinr rd₇ wr₇ (d := cloOff) (by decide)) fun s₈ u₈ _ _ => ?_
  refine wp_add fun s₉ u₉ cf₉ => ?_
  refine wp_stm (o := cloOff) (by rw [u₉.other _ (by decide), u₈.other _ (by decide), bp₇])
    (by rw [u₉.wr, u₈.wr, wr₇]; exact hp.sin rfl (by decide)) fun s₁₀ u₁₀ => ?_
  obtain bp₁₀ : s₁₀.gpr .ebp = scr s₀ := by rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), bp₇]
  obtain ichi := hp.sinr rd₇ wr₇ (d := chiOff) (by decide)
  refine wp_ldmF bp₁₀ (by rw [u₁₀.rd, u₁₀.wr, u₉.rd, u₉.wr, u₈.rd, u₈.wr]; exact ichi)
    fun s₁₁ u₁₁ cf₁₁ _ => ?_
  refine wp_adc0 (by rw [cf₁₁, u₁₀.cf, cf₉]) fun s₁₂ u₁₂ => ?_
  refine wp_stm (o := chiOff) (by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), bp₁₀])
    (by rw [u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]; exact hp.sin rfl (by decide)) fun s₁₃ u₁₃ => ?_
  refine wp_test fun s₁₄ f₁₄ z₁₄ => WP.block_nil ?_
  -- The state after the block.
  obtain g₁₄ : ∀ x, x ≠ .eax → s₁₄.gpr x = s₇.gpr x := fun x h => by
    rw [f₁₄.gpr, u₁₃.gpr, u₁₂.other x h, u₁₁.other x h, u₁₀.gpr, u₉.other x h, u₈.other x h]
  obtain rd₁₄ : s₁₄.rd = s₀.rd := by rw [f₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, rd₇]
  obtain wr₁₄ : s₁₄.wr = s₀.wr := by rw [f₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, wr₇]
  obtain lo₉ : s₉.gpr .eax = BitVec.ofNat 32 (cnt s₀ + (c + a)) := by
    rw [u₉.gpr, u₈.gpr, u₈.other _ (by decide), cx₇, m₇, hcnt.lo, ← BitVec.ofNat_add, Nat.add_assoc]
  obtain m₁₀ : s₁₀.mem = s.mem.writeW (addr (scr s₀) cloOff) (BitVec.ofNat 32 (cnt s₀ + (c + a))) := by
    rw [u₁₀.mem, lo₉, u₉.mem, u₈.mem, m₇]
  obtain hi₁₂ : s₁₂.gpr .eax = BitVec.ofNat 32 ((cnt s₀ + (c + a)) / 2 ^ 32) := by
    rw [u₁₂.gpr, u₁₁.gpr, m₁₀, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.hi,
      u₈.gpr, u₈.other _ (by decide), cx₇, m₇, hcnt.lo, carry_ofNat _ _ (by omega_arith), Nat.add_assoc]
  obtain m₁₄ : s₁₄.mem = (s.mem.writeW (addr (scr s₀) cloOff) (BitVec.ofNat 32 (cnt s₀ + (c + a)))).writeW
      (addr (scr s₀) chiOff) (BitVec.ofNat 32 ((cnt s₀ + (c + a)) / 2 ^ 32)) := by
    rw [f₁₄.mem, u₁₃.mem, hi₁₂, u₁₂.mem, u₁₁.mem, m₁₀]
  obtain hcnt₁₄ : Cnt s₀ (c + a) s₁₄.mem :=
    ⟨by rw [m₁₄, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32],
      by rw [m₁₄, Mem.readW_writeW_self32]⟩
  obtain hfr₁₄ : Frame [stR s₀ w, scR s₀, stkR s₀] s₀.mem s₁₄.mem := by
    rw [m₁₄]; exact frame_scr hp (frame_scr hp hI.frame (by decide) _) (by decide) _
  obtain hsv₁₄ : Saved (scr s₀) s₀ s₁₄.mem := by
    rw [m₁₄]; exact Saved.write hp (Saved.write hp hI.saved (by decide) (by decide) _) (by decide) (by decide) _
  obtain hst₁₄ : ∀ i < bufOff w + blockBytes w,
      s₁₄.mem (stA s₀ + BitVec.ofNat 64 i) = s.mem (stA s₀ + BitVec.ofNat 64 i) := by
    refine st_keep hP hp ?_
    rw [m₁₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
      (List.mem_singleton_self _) _ (hp.scr_in (by decide))
  obtain di₁₄ : s₁₄.gpr .edi = BitVec.ofNat 32 (len s₀ - (c + a)) := by
    rw [g₁₄ _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, tg _ (by decide), tcx,
      hptr.edi, sub_ofNat (by omega_arith), Nat.sub_sub]
  obtain dx₁₄ : s₁₄.gpr .edx = st s₀ + BitVec.ofNat 32 r := by
    rw [g₁₄ _ (by decide), u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other .ebx (by decide),
      u₅.other .eax (by decide), tg .ebx (by decide), tg .eax (by decide), hI.ebx, hax]
  obtain hz : isa.eval .e s₁₄ = some (decide (a = 0)) := by
    show s₁₄.zf = _
    rw [z₁₄, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), cx₇, BitVec.and_self, ofNat_beq_zero (by omega_arith)]
  obtain hC₁₄ : Common w s₀ c s₁₄ :=
    ⟨hc, rd₁₄, wr₁₄, by rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide), tg _ (by decide), hI.ebx],
      by rw [g₁₄ _ (by decide), bp₇], by rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide),
        tg _ (by decide), hI.esp], hfr₁₄, hsv₁₄⟩
  obtain si₁₄ : s₁₄.gpr .esi = dp s₀ + BitVec.ofNat 32 c := by
    rw [g₁₄ _ (by decide), g₇ _ (by decide) (by decide), tg _ (by decide), hptr.esi]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    refine WP.block_nil ⟨{ hC₁₄ with c_le := by omega_arith, repr := fun h0 d hd => ?_ }, ⟨si₁₄, di₁₄⟩, hcnt₁₄⟩
    exact reprR_congr hP hst₁₄ (hI.repr h0 d hd)
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.mono (copy_ok hP hp (c := c) (r := r) (k := a) (by omega_arith) (by omega_arith) (by omega_arith) rd₁₄ wr₁₄
      si₁₄ dx₁₄ (by rw [f₁₄.gpr, u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr,
        u₉.other _ (by decide), u₈.other _ (by decide), cx₇]) hfr₁₄
      (fun h0 d hd => reprR_congr hP hst₁₄ (hI.repr h0 d hd)))
      fun s₁₅ ⟨g₁₅, si₁₅, rd₁₅, wr₁₅, f₁₅, rp₁₅⟩ => ?_
    refine ⟨⟨⟨by omega_arith, rd₁₅, wr₁₅, ?_, ?_, ?_, frame_st hfr₁₄ f₁₅, Saved.st hp hsv₁₄ f₁₅⟩, rp₁₅⟩,
      ⟨si₁₅, ?_⟩, Cnt.st hp hcnt₁₄ f₁₅⟩
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.ebx
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.ebp
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact hC₁₄.esp
    · rw [g₁₅ _ (by decide) (by decide) (by decide) (by decide)]; exact di₁₄

/-! ## Calling the compression function -/

/-- A call of the compression function on the (full) buffer or on blocks of
data, without the final block flag. -/
theorem call_upd (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} {blk tlo thi : BitVec 32} {k : Nat}
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hesp : s.gpr .esp = esp₀ s₀) (hS : s.gpr .ebx = st s₀)
    (hC : s.gpr .ebp = scr s₀) (hB : s.gpr .esi = blk) (hk : (s.gpr .edi).toNat = k)
    (hlo : s.gpr .ecx = tlo) (hhi : s.gpr .edx = thi) (hl : s.gpr .eax = 0)
    (hsrc : (blk = st s₀ + BitVec.ofNat 32 (bufOff w) ∧ k = 1) ∨
      ∃ c₀, blk = dp s₀ + BitVec.ofNat 32 c₀ ∧ c₀ + blockBytes w * k ≤ len s₀ ∧ 0 < k)
    {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩, stkR s₀] s.mem s'.mem →
      stateAt w s'.mem (stA s₀) =
        compressBlocks P (stateAt w s.mem (stA s₀)) s.mem (blk.setWidth 64) k (thi ++ tlo).toNat false →
      Q s') :
    WP isa (compressCall name code) s Q := by
  have hl' := hP.len
  obtain fS := hp.st_fit; have fD := hp.d_fit; have fC := hp.scr_fit
  have hN := hP.N
  obtain eN : Region.Sub ⟨stA s₀, bufOff w⟩ (stR s₀ w) := Region.sub_prefix (by omega_arith)
  obtain eso : Region.Sub ⟨scA s₀, 512⟩ (scR s₀) := Region.sub_prefix (by omega_arith)
  -- Where the blocks are.
  obtain hblk : blk.toNat + blockBytes w * k ≤ 2 ^ 32 ∧
      (Region.Sub ⟨blk.setWidth 64, blockBytes w * k⟩ (stR s₀ w) ∧
        Region.Disjoint ⟨blk.setWidth 64, blockBytes w * k⟩ ⟨stA s₀, bufOff w⟩ ∨
       Region.Sub ⟨blk.setWidth 64, blockBytes w * k⟩ (dR s₀)) ∧
      ∃ r ∈ s₀.rd ++ s₀.wr, ∃ o, (blk.setWidth 64) = r.base + BitVec.ofNat 64 o ∧
        o + blockBytes w * k ≤ r.len := by
    rcases hsrc with ⟨rfl, rfl⟩ | ⟨c₀, rfl, hc₀, hk0⟩
    · have e := sw_add (x := st s₀) (c := bufOff w) (by omega_arith)
      refine ⟨by rw [toNat_add_ofNat (by omega_arith)]; omega_arith, .inl ⟨by rw [e]; exact sub_offset (by omega_arith) (by omega_arith),
        by rw [e]; exact Offset.disjoint_base _ (Nat.le_refl _) (by omega_arith)⟩, stR s₀ w, by simp [hp.wr],
        bufOff w, e, by simp only; omega_arith⟩
    · have hB1 : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ hk0
      obtain e := sw_add (x := dp s₀) (c := c₀) (by have := hP.pos; omega_arith)
      refine ⟨by rw [toNat_add_ofNat (by have := hP.pos; omega_arith)]; omega_arith,
        .inr (by rw [e]; exact sub_offset (by omega_arith) (by omega_arith)), dR s₀, by simp [hp.rd], c₀, e, hc₀⟩
  obtain ⟨f₁, hsub, r₀, hr₀, o₀, ho₀, hl₀⟩ := hblk
  obtain dS : (stkR s₀).Disjoint ⟨stA s₀, bufOff w⟩ := hp.stk_st.sub_right eN
  obtain dC : (stkR s₀).Disjoint ⟨scA s₀, 512⟩ := hp.stk_scr.sub_right eso
  refine call_ok (P := P) hf hesp hS hC hB hk hlo hhi hl hp.sp_lo (by omega_arith) f₁ (by omega_arith)
    ((hp.st_scr.sub_left eN).sub_right eso) ?_ ?_ dS dC ?_ ?_ ?_
    fun s' rd' wr' cs' f' post => hQ s' rd' wr' cs' f' (by rw [post]; rfl)
  · rcases hsub with ⟨_, h⟩ | h
    · exact h
    · exact (hp.d_st.sub_left h).sub_right eN
  · rcases hsub with ⟨h, _⟩ | h
    · exact (hp.st_scr.sub_left h).sub_right eso
    · exact (hp.d_scr.sub_left h).sub_right eso
  · rcases hsub with ⟨h, _⟩ | h
    · exact hp.stk_st.sub_right h
    · exact hp.stk_d.sub_right h
  · rw [hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨r₀, hr₀, o₀, ho₀, hl₀⟩
  · rw [hwr, hp.wr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stR s₀ w, by simp, 0, by simp, by simp⟩
    · exact ⟨scR s₀, by simp, 0, by simp, by simp⟩

/-- A call keeps what holds throughout. -/
theorem Common.after_call (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} {s s' : State}
    (h : Common w s₀ c s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hcs : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r)
    (hf : Frame [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩, stkR s₀] s.mem s'.mem) :
    Common w s₀ c s' := by
  have hl := hP.len
  obtain hf' : Frame (⟨scA s₀, 512⟩ :: [stR s₀ w, stkR s₀]) s.mem s'.mem := hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega_arith)⟩
    · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  exact ⟨h.c_le, hrd.trans h.rd, hwr.trans h.wr, by rw [hcs _ (by decide)]; exact h.ebx,
    by rw [hcs _ (by decide)]; exact h.ebp, by rw [hcs _ (by decide)]; exact h.esp,
    h.frame.trans (hf'.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨scR s₀, by simp, Region.sub_prefix (by omega_arith)⟩
      · exact ⟨stR s₀ w, by simp, fun _ h => h⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩),
    Saved.keep hp.scr_fit h.saved hf' hp.scr_disj⟩

/-- A word of the scratch space from offset 512 on is kept by a call. -/
theorem keep_call {s₀ : State} (hp : Pre w s₀) {m m' : Mem}
    (hf : Frame [⟨stA s₀, bufOff w⟩, ⟨scA s₀, 512⟩, stkR s₀] m m') {d : Nat} (h₁ : 512 ≤ d) (h₂ : d + 4 ≤ 576) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine keep_hi hp.scr_fit (rs := [stR s₀ w, stkR s₀]) (hf.sub fun r hr => ?_) hp.scr_disj h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨stR s₀ w, by simp, Region.sub_prefix (by have := hp.st_fit; omega_arith)⟩
  · exact ⟨⟨scA s₀, 512⟩, by simp, fun _ h => h⟩
  · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem compressBlocks_one (h : HashValue w) (m : Mem) (p : Addr) (t : Nat) (f : Bool) :
    compressBlocks P h m p 1 t f = F P h (blockAt w m p) t f := by
  rw [compressBlocks_succ, compressBlocks_zero]; simp

/-! ## Compressing the full buffer -/

theorem compressBuf_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {c : Nat} {s : State} (hI : Inv P s₀ c (blockBytes w) s) (hptr : Ptr s₀ c s)
    (hcnt : Cnt s₀ c s.mem) :
    WP isa (compressBuf w name code) s fun s' => Inv P s₀ c 0 s' ∧ Ptr s₀ c s' ∧ Cnt s₀ c s'.mem := by
  have hl := hP.len
  unfold compressBuf
  have bp := hI.ebp
  refine WP.seq (wp_stm (o := dataOff) bp (hp.sin hI.wr (by decide)) fun s₁ u₁ => ?_)
  refine wp_stm (o := lenOff) (by rw [u₁.gpr, bp]) (by rw [u₁.wr]; exact hp.sin hI.wr (by decide))
    fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => wp_movi fun s₅ u₅ => ?_
  obtain g₅ : ∀ x, x ≠ .esi → x ≠ .edi → s₅.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₅.other x h2, u₄.other x h1, u₃.other x h1, u₂.gpr, u₁.gpr]
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  obtain m₂ : s₂.mem = (s.mem.writeW (addr (scr s₀) dataOff) (s.gpr .esi)).writeW (addr (scr s₀) lenOff)
      (s.gpr .edi) := by rw [u₂.mem, u₁.mem, u₁.gpr]
  obtain m₅ : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  obtain bp₅ : s₅.gpr .ebp = scr s₀ := by rw [g₅ _ (by decide) (by decide), bp]
  refine wp_ldm bp₅ (hp.sinr rd₅ wr₅ (d := cloOff) (by decide)) fun s₆ u₆ => ?_
  obtain ichi := hp.sinr rd₅ wr₅ (d := chiOff) (by decide)
  refine wp_ldm (by rw [u₆.other _ (by decide), bp₅]) (by rw [u₆.rd, u₆.wr]; exact ichi) fun s₇ u₇ => ?_
  refine wp_movi fun s₈ u₈ => WP.block_nil ?_
  obtain g₈ : ∀ x, x ≠ .esi → x ≠ .edi → x ≠ .ecx → x ≠ .edx → x ≠ .eax → s₈.gpr x = s.gpr x :=
    fun x h1 h2 h3 h4 h5 => by rw [u₈.other x h5, u₇.other x h4, u₆.other x h3, g₅ x h1 h2]
  obtain m₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, m₅]
  -- The memory before the call: only the two words of the scratch space differ.
  obtain fr₂ : Frame [scR s₀] s.mem s₂.mem := by
    rw [m₂]; exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
      (List.mem_singleton_self _) _ (hp.scr_in (by decide))
  obtain rd₂ : s₂.mem.readW (addr (scr s₀) cloOff) 32 = s.mem.readW (addr (scr s₀) cloOff) 32 := by
    rw [m₂, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide)]
  obtain rd₂' : s₂.mem.readW (addr (scr s₀) chiOff) 32 = s.mem.readW (addr (scr s₀) chiOff) 32 := by
    rw [m₂, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide)]
  refine WP.seq (call_upd hP hf hp (blk := st s₀ + BitVec.ofNat 32 (bufOff w)) (k := 1)
    (tlo := BitVec.ofNat 32 (cnt s₀ + c)) (thi := BitVec.ofNat 32 ((cnt s₀ + c) / 2 ^ 32))
    (by rw [u₈.rd, u₇.rd, u₆.rd, rd₅]) (by rw [u₈.wr, u₇.wr, u₆.wr, wr₅])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx])
    (by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), bp])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hI.ebx, N_eq])
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; rfl)
    (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, m₅, rd₂, hcnt.lo])
    (by rw [u₈.other _ (by decide), u₇.gpr, u₆.mem, m₅, rd₂', hcnt.hi]) u₈.gpr (.inl ⟨rfl, rfl⟩)
    fun s' rd' wr' cs' f' post => ?_)
  obtain sv₂ := Saved.write hp (Saved.write hp hI.saved (d := dataOff) (by decide) (by decide) (s.gpr .esi))
    (d := lenOff) (by decide) (by decide) (s.gpr .edi)
  obtain hC₈ : Common w s₀ c s₈ :=
    ⟨hI.c_le, by rw [u₈.rd, u₇.rd, u₆.rd, rd₅], by rw [u₈.wr, u₇.wr, u₆.wr, wr₅],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), bp],
      by rw [g₈ _ (by decide) (by decide) (by decide) (by decide) (by decide), hI.esp],
      by rw [m₈, m₂]; exact frame_scr hp (frame_scr hp hI.frame (by decide) _) (by decide) _,
      by rw [m₈, m₂]; exact sv₂⟩
  obtain hC' : Common w s₀ c s' := hC₈.after_call hP hp rd' wr' cs' f'
  obtain kc : ∀ d, 512 ≤ d → d + 4 ≤ 576 → s'.mem.readW (addr (scr s₀) d) 32 = s₈.mem.readW (addr (scr s₀) d) 32 :=
    fun _ h₁ h₂ => keep_call hp f' h₁ h₂
  refine wp_ldm (b := .ebp) hC'.ebp (hp.sinr hC'.rd hC'.wr (d := dataOff) (by decide)) fun s₉ u₉ => ?_
  obtain ilen := hp.sinr hC'.rd hC'.wr (d := lenOff) (by decide)
  refine wp_ldm (b := .ebp) (by rw [u₉.other _ (by decide), hC'.ebp]) (by rw [u₉.rd, u₉.wr]; exact ilen)
    fun s₁₀ u₁₀ => WP.block_nil ?_
  obtain g₁₀ : ∀ x, x ≠ .esi → x ≠ .edi → s₁₀.gpr x = s'.gpr x := fun x h1 h2 => by
    rw [u₁₀.other x h2, u₉.other x h1]
  obtain m₁₀ : s₁₀.mem = s'.mem := by rw [u₁₀.mem, u₉.mem]
  obtain hC₁₀ : Common w s₀ c s₁₀ := hC'.of_gpr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₀ _ (by decide) (by decide)) m₁₀
    (by rw [u₁₀.rd, u₉.rd]) (by rw [u₁₀.wr, u₉.wr])
  refine ⟨{ hC₁₀ with repr := fun h0 d hd => ?_ }, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have hcn := hd.cnt_eq
    have hlt := hd.2.2
    have hc := hI.c_le
    rw [m₁₀]
    refine reprR_flush P hP.pos (mem := s₂.mem) (reprR_congr hP (st_keep hP hp fr₂) (hI.repr h0 d hd)) ?_
    rw [post, m₈, compressBlocks_one, sw_add (by have := hp.st_fit; have := hP.pos; omega_arith), append_ofNat (by omega_arith),
      List.length_append, D_length, ← hcn]
  · rw [u₁₀.other _ (by decide), u₉.gpr, kc dataOff (by decide) (by decide), m₈, m₂,
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32, hptr.esi]
  · rw [u₁₀.gpr, u₉.mem, kc lenOff (by decide) (by decide), m₈, m₂, Mem.readW_writeW_self32, hptr.edi]
  · rw [m₁₀, kc cloOff (by decide) (by decide), m₈, rd₂, hcnt.lo]
  · rw [m₁₀, kc chiOff (by decide) (by decide), m₈, rd₂', hcnt.hi]

/-! ## `head`: filling the buffer -/

/-- After `head`: all the data is in, with the buffer not empty, or the
buffer is empty and data is left. -/
def HeadPost (P : Params w) (s₀ : State) (s : State) : Prop :=
  ∃ c r, Inv P s₀ c r s ∧ Ptr s₀ c s ∧ Cnt s₀ c s.mem ∧ ((c = len s₀ ∧ 1 ≤ r) ∨ (c < len s₀ ∧ r = 0))

theorem head_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {r : Nat} (hr : r ≤ blockBytes w) (hl : 0 < len s₀) {s : State} (hI : Inv P s₀ 0 r s)
    (hptr : Ptr s₀ 0 s) (hcnt : Cnt s₀ 0 s.mem) (hax : s.gpr .eax = BitVec.ofNat 32 r) :
    WP isa (head w name code) s (HeadPost P s₀) := by
  obtain hL := len_lt s₀
  have hl' := hP.len
  unfold head
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  obtain hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  obtain hptr₁ := hptr.of_gpr (by rw [f₁.gpr]) (by rw [f₁.gpr])
  obtain hz : isa.eval .e s₁ = some (decide (r = 0)) := by
    show s₁.zf = _
    rw [z₁, hax, BitVec.and_self, ofNat_beq_zero (by omega_arith)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    exact WP.block_nil ⟨0, 0, hI₁, hptr₁, by rw [f₁.mem]; exact hcnt, .inr ⟨hl, rfl⟩⟩
  · simp only [decide_eq_false_iff_not] at hb
    refine WP.seq (WP.mono (fill_ok hP hp hr hI₁ hptr₁ (by rw [f₁.mem]; exact hcnt) (by rw [f₁.gpr]; exact hax))
      fun s₂ ⟨hI₂, hptr₂, hcnt₂⟩ => ?_)
    rw [Nat.zero_add, Nat.sub_zero] at hI₂ hptr₂ hcnt₂
    refine WP.seq (wp_test fun s₃ f₃ z₃ => WP.block_nil ?_)
    obtain hI₃ := hI₂.of_gpr (fun r _ => by rw [f₃.gpr]) f₃.mem f₃.rd f₃.wr
    obtain hptr₃ := hptr₂.of_gpr (by rw [f₃.gpr]) (by rw [f₃.gpr])
    obtain hcnt₃ : Cnt s₀ (min (blockBytes w - r) (len s₀)) s₃.mem := by rw [f₃.mem]; exact hcnt₂
    obtain hz₃ : isa.eval .e s₃ = some (decide (len s₀ - min (blockBytes w - r) (len s₀) = 0)) := by
      show s₃.zf = _
      rw [z₃, hptr₂.edi, BitVec.and_self, ofNat_beq_zero (by omega_arith)]
    refine WP.ite _ hz₃ (fun hb' => ?_) (fun hb' => ?_)
    · simp only [decide_eq_true_eq] at hb'
      exact WP.block_nil ⟨_, _, hI₃, hptr₃, hcnt₃, .inl ⟨by omega_arith, by omega_arith⟩⟩
    · simp only [decide_eq_false_iff_not] at hb'
      obtain e : r + min (blockBytes w - r) (len s₀) = blockBytes w := by omega_arith
      rw [e] at hI₃
      exact WP.mono (compressBuf_ok hP hf hp hI₃ hptr₃ hcnt₃) fun s₄ ⟨hI₄, hptr₄, hcnt₄⟩ =>
        ⟨_, _, hI₄, hptr₄, hcnt₄, .inr ⟨by omega_arith, rfl⟩⟩

/-! ## `rest`: whole blocks straight from the data, and the last block -/

theorem ok_lg (hP : Ok P) : 1 ≤ Nat.log2 (B w) ∧ Nat.log2 (B w) ≤ 31 ∧ 2 ^ Nat.log2 (B w) = blockBytes w := by
  rw [B_eq]
  rcases hP.bb with h | h <;> rw [h]
  · rw [show (64 : Nat) = 2 ^ 6 from rfl, Nat.log2_two_pow]; decide
  · rw [show (128 : Nat) = 2 ^ 7 from rfl, Nat.log2_two_pow]; decide

theorem shr_ofNat (hP : Ok P) {m : Nat} (h : m < 2 ^ 32) :
    BitVec.ofNat 32 m >>> Nat.log2 (B w) = BitVec.ofNat 32 (m / blockBytes w) := by
  obtain ⟨-, -, lgB⟩ := ok_lg hP
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h), Nat.shiftRight_eq_div_pow, lgB]

/-- The blocks of data but the last, straight from the data. -/
theorem direct_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {c : Nat} (hc : c < len s₀) {s : State} (hI : Inv P s₀ c 0 s) (hptr : Ptr s₀ c s)
    (hcnt : Cnt s₀ c s.mem) :
    WP isa (direct w name code) s fun s' =>
      Inv P s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) 0 s' ∧
      Ptr s₀ (c + blockBytes w * ((len s₀ - c - 1) / blockBytes w)) s' := by
  have hl := hP.len
  obtain hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨lg₁, lg₂, -⟩ := ok_lg hP
  obtain ⟨k, hk⟩ : ∃ k, k = (len s₀ - c - 1) / blockBytes w := ⟨_, rfl⟩
  rw [← hk]
  obtain hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
  obtain hmod := Nat.mod_lt (len s₀ - c - 1) hpos
  rw [← hk] at hdm
  obtain hBk : blockBytes w * k ≤ len s₀ - c - 1 := by omega_arith
  obtain hkle : k ≤ len s₀ - c - 1 := hk ▸ Nat.div_le_self _ _
  unfold direct
  refine WP.seq (wp_mov fun s₁ u₁ => wp_subi fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ => wp_andi fun s₄ u₄ =>
    wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  obtain hL1 : s₂.gpr .eax = BitVec.ofNat 32 (len s₀ - c - 1) := by
    rw [u₂.gpr, u₁.gpr, hptr.edi, ofNat_pred (by omega_arith)]
  obtain hcx₄ : s₄.gpr .ecx = BitVec.ofNat 32 ((len s₀ - c - 1) % blockBytes w) := by
    rw [u₄.gpr, u₃.gpr, hL1, and_mask hP, toNat_ofNat_lt (by omega_arith)]
  obtain hax₅ : s₅.gpr .eax = BitVec.ofNat 32 (blockBytes w * k) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), hL1, hcx₄, sub_ofNat (by omega_arith)]
    exact congrArg _ (by omega_arith)
  obtain g₅ : ∀ x, x ≠ .eax → x ≠ .ecx → s₅.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₅.other x h1, u₄.other x h2, u₃.other x h2, u₂.other x h1, u₁.other x h1]
  obtain m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  obtain rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, hI.rd]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, hI.wr]
  obtain hz : isa.eval .e s₅ = some (decide (k = 0)) := by
    show s₅.zf = _
    rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), hL1, hcx₄, sub_ofNat (by omega_arith),
      ofNat_beq_zero (by omega_arith)]
    have : len s₀ - c - 1 - (len s₀ - c - 1) % blockBytes w = blockBytes w * k := by omega_arith
    rw [this]
    simp only [Nat.mul_eq_zero, Nat.ne_of_gt hpos, false_or]
  obtain hcom : ∀ r ∈ [Reg.ebx, .ebp, .esp], s₅.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₅ _ (by decide) (by decide)
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    subst hb
    rw [Nat.mul_zero, Nat.add_zero]
    exact WP.block_nil ⟨hI.of_gpr hcom m₅ (by rw [rd₅, hI.rd]) (by rw [wr₅, hI.wr]),
      hptr.of_gpr (g₅ _ (by decide) (by decide)) (g₅ _ (by decide) (by decide))⟩
  simp only [decide_eq_false_iff_not] at hb
  obtain hk1 : 1 ≤ k := Nat.pos_of_ne_zero hb
  obtain hB1 : blockBytes w ≤ blockBytes w * k := Nat.le_mul_of_pos_right _ hk1
  obtain bp₅ : s₅.gpr .ebp = scr s₀ := by rw [g₅ _ (by decide) (by decide), hI.ebp]
  refine WP.seq (wp_stm (o := lenOff) bp₅ (hp.sin wr₅ (by decide)) fun s₆ u₆ => ?_)
  refine wp_stm (o := bytesOff) (by rw [u₆.gpr, bp₅]) (by rw [u₆.wr]; exact hp.sin wr₅ (by decide))
    fun s₇ u₇ => ?_
  refine wp_mov fun s₈ u₈ => wp_shr ⟨lg₁, lg₂⟩ fun s₉ u₉ _ => ?_
  obtain bp₉ : s₉.gpr .ebp = scr s₀ := by rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr, u₆.gpr, bp₅]
  obtain rd₉ : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, rd₅]
  obtain wr₉ : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, wr₅]
  obtain m₉ : s₉.mem = (s.mem.writeW (addr (scr s₀) lenOff) (s₅.gpr .edi)).writeW (addr (scr s₀) bytesOff)
      (BitVec.ofNat 32 (blockBytes w * k)) := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.gpr, u₆.mem, hax₅, m₅]
  obtain rdlo : s₉.mem.readW (addr (scr s₀) cloOff) 32 = BitVec.ofNat 32 (cnt s₀ + c) := by
    rw [m₉, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.lo]
  obtain rdhi : s₉.mem.readW (addr (scr s₀) chiOff) 32 = BitVec.ofNat 32 ((cnt s₀ + c) / 2 ^ 32) := by
    rw [m₉, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide),
      rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), hcnt.hi]
  refine wp_ldmF bp₉ (hp.sinr rd₉ wr₉ (d := cloOff) (by decide)) fun s₁₀ u₁₀ _ _ => ?_
  refine wp_addiC fun s₁₁ u₁₁ cf₁₁ => ?_
  obtain ichi := hp.sinr rd₉ wr₉ (d := chiOff) (by decide)
  refine wp_ldmF (by rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), bp₉])
    (by rw [u₁₁.rd, u₁₁.wr, u₁₀.rd, u₁₀.wr]; exact ichi) fun s₁₂ u₁₂ cf₁₂ _ => ?_
  refine wp_adc0 (by rw [cf₁₂, cf₁₁]) fun s₁₃ u₁₃ => wp_movi fun s₁₄ u₁₄ => WP.block_nil ?_
  obtain g₁₄ : ∀ x, x ≠ .eax → x ≠ .ecx → x ≠ .edx → x ≠ .edi → s₁₄.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [u₁₄.other x h1, u₁₃.other x h3, u₁₂.other x h3, u₁₁.other x h2, u₁₀.other x h2, u₉.other x h4,
      u₈.other x h4, u₇.gpr, u₆.gpr, g₅ x h1 h2]
  obtain m₁₄ : s₁₄.mem = s₉.mem := by rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem]
  obtain lo₁₁ : s₁₁.gpr .ecx = BitVec.ofNat 32 (cnt s₀ + c + blockBytes w) := by
    rw [u₁₁.gpr, u₁₀.gpr, rdlo, B_eq, ← BitVec.ofNat_add]
  obtain sv₉ := Saved.write hp (Saved.write hp hI.saved (d := lenOff) (by decide) (by decide) (s₅.gpr .edi))
    (d := bytesOff) (by decide) (by decide) (BitVec.ofNat 32 (blockBytes w * k))
  obtain hC₁₄ : Common w s₀ c s₁₄ :=
    ⟨hI.c_le, by rw [u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, rd₉],
      by rw [u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, wr₉],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.ebx],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.ebp],
      by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hI.esp],
      by rw [m₁₄, m₉]; exact frame_scr hp (frame_scr hp hI.frame (by decide) _) (by decide) _,
      by rw [m₁₄, m₉]; exact sv₉⟩
  obtain hdi₁₄ : s₁₄.gpr .edi = BitVec.ofNat 32 k := by
    rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
      u₁₀.other _ (by decide), u₉.gpr, u₈.gpr, u₇.gpr, u₆.gpr, hax₅, shr_ofNat hP (by omega_arith),
      Nat.mul_div_cancel_left _ hpos]
  obtain hdx₁₄ : s₁₄.gpr .edx = BitVec.ofNat 32 ((cnt s₀ + c + blockBytes w) / 2 ^ 32) := by
    rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₁.mem, u₁₀.mem, rdhi, u₁₀.gpr, rdlo, B_eq,
      carry_ofNat _ _ (by omega_arith)]
  refine WP.seq (call_upd hP hf hp (blk := dp s₀ + BitVec.ofNat 32 c) (k := k)
    (tlo := BitVec.ofNat 32 (cnt s₀ + c + blockBytes w))
    (thi := BitVec.ofNat 32 ((cnt s₀ + c + blockBytes w) / 2 ^ 32)) hC₁₄.rd hC₁₄.wr hC₁₄.esp hC₁₄.ebx hC₁₄.ebp
    (by rw [g₁₄ _ (by decide) (by decide) (by decide) (by decide), hptr.esi])
    (by rw [hdi₁₄, toNat_ofNat_lt (by omega_arith)])
    (by rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), lo₁₁]) hdx₁₄
    u₁₄.gpr (.inr ⟨c, rfl, by omega_arith, hk1⟩) fun s' rd' wr' cs' f' post => ?_)
  obtain hC' : Common w s₀ c s' := hC₁₄.after_call hP hp rd' wr' cs' f'
  obtain kc : ∀ d, 512 ≤ d → d + 4 ≤ 576 → s'.mem.readW (addr (scr s₀) d) 32 = s₁₄.mem.readW (addr (scr s₀) d) 32 :=
    fun _ h₁ h₂ => keep_call hp f' h₁ h₂
  refine wp_ldm (b := .ebp) hC'.ebp (hp.sinr hC'.rd hC'.wr (d := bytesOff) (by decide)) fun s₁₅ u₁₅ => ?_
  refine wp_add fun s₁₆ u₁₆ _ => ?_
  obtain ilen := hp.sinr hC'.rd hC'.wr (d := lenOff) (by decide)
  refine wp_ldm (b := .ebp) (by rw [u₁₆.other _ (by decide), u₁₅.other _ (by decide), hC'.ebp])
    (by rw [u₁₆.rd, u₁₆.wr, u₁₅.rd, u₁₅.wr]; exact ilen) fun s₁₇ u₁₇ => ?_
  refine wp_sub fun s₁₈ u₁₈ _ => WP.block_nil ?_
  obtain ax₁₅ : s₁₅.gpr .eax = BitVec.ofNat 32 (blockBytes w * k) := by
    rw [u₁₅.gpr, kc bytesOff (by decide) (by decide), m₁₄, m₉, Mem.readW_writeW_self32]
  obtain g₁₈ : ∀ x, x ≠ .eax → x ≠ .esi → x ≠ .edi → s₁₈.gpr x = s'.gpr x := fun x h1 h2 h3 => by
    rw [u₁₈.other x h3, u₁₇.other x h3, u₁₆.other x h2, u₁₅.other x h1]
  obtain m₁₈ : s₁₈.mem = s'.mem := by rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem]
  obtain hC₁₈ : Common w s₀ c s₁₈ := hC'.of_gpr (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact g₁₈ _ (by decide) (by decide) (by decide)) m₁₈
    (by rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd]) (by rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr])
  refine ⟨⟨{ hC₁₈ with c_le := by omega_arith }, fun h0 d hd => ?_⟩, ⟨?_, ?_⟩⟩
  · have hcn := hd.cnt_eq
    have hlt := hd.2.2
    obtain hst : ∀ i < bufOff w + blockBytes w,
        s₁₄.mem (stA s₀ + BitVec.ofNat 64 i) = s.mem (stA s₀ + BitVec.ofNat 64 i) := by
      refine st_keep hP hp ?_
      rw [m₁₄, m₉]
      exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hp.scr_in (by decide))).writeW
        (List.mem_singleton_self _) _ (hp.scr_in (by decide))
    obtain e : d ++ D s₀ (c + blockBytes w * k) =
        d ++ D s₀ c ++ bytesAt s₁₄.mem (dA s₀ + BitVec.ofNat 64 c) (blockBytes w * k) := by
      rw [D, bytesAt_add, List.append_assoc]
      refine congrArg (fun l => d ++ (bytesAt s₀.mem (dA s₀) c ++ l)) (bytesAt_congr fun i hi => ?_)
      rw [Offset.add_add]
      exact (hC₁₄.data hp (by omega_arith)).symm
    rw [m₁₈, e]
    refine reprR_blocks P hpos (reprR_congr hP hst (hI.repr h0 d hd)) ?_
    rw [post, dp_add hp hc, append_ofNat (by omega_arith), List.length_append, D_length, ← hcn]
  · rw [u₁₈.other _ (by decide), u₁₇.other _ (by decide), u₁₆.gpr, u₁₅.other _ (by decide), ax₁₅,
      cs' _ (by decide), g₁₄ _ (by decide) (by decide) (by decide) (by decide), hptr.esi, BitVec.add_assoc,
      BitVec.ofNat_add]
  · rw [u₁₈.gpr, u₁₇.gpr, u₁₇.other .eax (by decide), u₁₆.other .eax (by decide), ax₁₅, u₁₆.mem, u₁₅.mem,
      kc lenOff (by decide) (by decide),
      m₁₄, m₉, rw_scr hp.scr_fit _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
      g₅ _ (by decide) (by decide), hptr.edi, sub_ofNat (by omega_arith)]
    exact congrArg _ (by omega_arith)

/-- The last `1` to `B` bytes of data, into the empty buffer. -/
theorem tail_ok (hP : Ok P) {s₀ : State} (hp : Pre w s₀) {c : Nat} (hc₁ : c < len s₀)
    (hc₂ : len s₀ - c ≤ blockBytes w) {s : State} (hI : Inv P s₀ c 0 s) (hptr : Ptr s₀ c s) :
    WP isa (tail w) s (Inv P s₀ (len s₀) (len s₀ - c)) := by
  obtain hL := len_lt s₀
  unfold tail
  refine WP.seq (wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => WP.block_nil ?_)
  obtain hg : ∀ x, x ≠ .ecx → x ≠ .edx → s₂.gpr x = s.gpr x := fun x h1 h2 => by
    rw [u₂.other x h2, u₁.other x h1]
  obtain hm₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  refine WP.mono (copy_ok hP hp (c := c) (r := 0) (k := len s₀ - c) (by omega_arith) (by omega_arith) (by omega_arith)
      (by rw [u₂.rd, u₁.rd, hI.rd]) (by rw [u₂.wr, u₁.wr, hI.wr])
      (by rw [hg _ (by decide) (by decide)]; exact hptr.esi)
      (by rw [u₂.gpr, u₁.other _ (by decide), hI.ebx]; simp)
      (by rw [u₂.other _ (by decide), u₁.gpr, hptr.edi])
      (by rw [hm₂]; exact hI.frame) (by rw [hm₂]; exact hI.repr))
    fun s₃ ⟨g₃, _, rd₃, wr₃, f₃, rp₃⟩ => ?_
  obtain e : c + (len s₀ - c) = len s₀ := by omega_arith
  rw [e, Nat.zero_add] at rp₃
  obtain g : ∀ x, x ≠ .esi → x ≠ .edx → x ≠ .ecx → x ≠ .eax → s₃.gpr x = s.gpr x := fun x h1 h2 h3 h4 => by
    rw [g₃ x h1 h2 h3 h4, hg x h3 h2]
  refine ⟨⟨Nat.le_refl _, rd₃, wr₃, ?_, ?_, ?_, ?_, ?_⟩, rp₃⟩
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.ebx
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.ebp
  · rw [g _ (by decide) (by decide) (by decide) (by decide)]; exact hI.esp
  · exact frame_st hI.frame (by rw [← hm₂]; exact f₃)
  · exact Saved.st hp hI.saved (by rw [← hm₂]; exact f₃)

/-- All the data is in, and the buffer is not empty. -/
def Full (P : Params w) (s₀ : State) (s : State) : Prop := ∃ r, Inv P s₀ (len s₀) r s ∧ 1 ≤ r

theorem rest_ok (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) {s : State} (h : HeadPost P s₀ s) : WP isa (rest w name code) s (Full P s₀) := by
  obtain hL := len_lt s₀
  have hpos := hP.pos
  obtain ⟨c, r, hI, hptr, hcnt, hcr⟩ := h
  unfold rest
  refine WP.seq (wp_test fun s₁ f₁ z₁ => WP.block_nil ?_)
  obtain hI₁ := hI.of_gpr (fun r _ => by rw [f₁.gpr]) f₁.mem f₁.rd f₁.wr
  obtain hptr₁ := hptr.of_gpr (by rw [f₁.gpr]) (by rw [f₁.gpr])
  obtain hz : isa.eval .e s₁ = some (decide (len s₀ - c = 0)) := by
    show s₁.zf = _
    rw [z₁, hptr.edi, BitVec.and_self, ofNat_beq_zero (by omega_arith)]
  have hc := hI.c_le
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', _⟩
    · exact WP.block_nil ⟨r, hI₁, hr⟩
    · omega_arith
  · simp only [decide_eq_false_iff_not] at hb
    rcases hcr with ⟨rfl, hr⟩ | ⟨hc', rfl⟩
    · omega_arith
    refine WP.seq (WP.mono (direct_ok hP hf hp hc' hI₁ hptr₁ (by rw [f₁.mem]; exact hcnt))
      fun s₂ ⟨hI₂, hptr₂⟩ => ?_)
    obtain hdm := Nat.div_add_mod (len s₀ - c - 1) (blockBytes w)
    obtain hmod := Nat.mod_lt (len s₀ - c - 1) hpos
    exact WP.mono (tail_ok hP hp (by omega_arith) (by omega_arith) hI₂ hptr₂) fun s₃ hI₃ => ⟨_, hI₃, by omega_arith⟩

/-! ## Epilogue and the whole function -/

/-- All the data is in. -/
def Done (P : Params w) (s₀ : State) (s : State) : Prop :=
  Common w s₀ (len s₀) s ∧
    ∀ h0 d, R₀ P s₀ h0 d → Spec.Blake2.Repr P h0 s.mem (stA s₀) (d ++ D s₀ (len s₀))

theorem Full.done (hP : Ok P) {s₀ : State} {s : State} (h : Full P s₀ s) : Done P s₀ s := by
  obtain ⟨r, hI, hr⟩ := h
  exact ⟨hI.toCommon, fun h0 d hd => repr_of_reprR P hP.pos (hI.repr h0 d hd) hr⟩

theorem epilogue_ok {s₀ : State} (hp : Pre w s₀) {s : State} (hD : Done P s₀ s) :
    WP isa (.block restore) s fun s' => abiPreserved s₀ s' ∧ (updateX86 P).post s₀ s' := by
  obtain ⟨hC, hrepr⟩ := hD
  refine WP.mono (restore_saved hC.ebp (fun d _ hd => hp.sinr hC.rd hC.wr (by omega_arith)) hC.saved)
    fun s₅ ⟨hg, hsp, hm₅⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, fun h0 d hd hc hl => ?_⟩
  · by_cases h : r = .esp
    · subst h; rw [hsp, hC.esp]
    · exact hg r hr h
  · rw [hm₅]
    refine hC.frame.readW (r := retR s₀) (Region.contains_self _ _) ?_ (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hp.ret_st, hp.ret_scr, hp.ret_stk]
  · rw [hm₅]; exact hrepr h0 d ⟨hd, hc, hl⟩

theorem correct (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code) {s₀ : State}
    (hp : Pre w s₀) :
    WP isa (update w name code) s₀ fun s' => abiPreserved s₀ s' ∧ (updateX86 P).post s₀ s' := by
  obtain hL := len_lt s₀
  unfold update
  refine WP.seq (WP.mono (prologue_ok hp) fun s₁ ⟨hC, hptr, hm, hax, hcx⟩ => ?_)
  refine WP.seq (WP.mono (bufLen_ok hP hp hC hptr hm hax hcx) fun s₂ ⟨hI, hptr₂, hcnt₂, hax₂⟩ => ?_)
  refine WP.seq (wp_test fun s₃ f₃ z₃ => WP.block_nil ?_)
  obtain hI₃ := hI.of_gpr (fun r _ => by rw [f₃.gpr]) f₃.mem f₃.rd f₃.wr
  obtain hptr₃ := hptr₂.of_gpr (by rw [f₃.gpr]) (by rw [f₃.gpr])
  refine WP.seq (WP.mono (Q := Done P s₀) ?_ fun s₄ h => epilogue_ok hp h)
  obtain hz : isa.eval .e s₃ = some (decide (len s₀ = 0)) := by
    show s₃.zf = _
    rw [z₃, hptr₂.edi, BitVec.and_self, Nat.sub_zero, ofNat_beq_zero (by omega_arith)]
  refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
  · simp only [decide_eq_true_eq] at hb
    refine WP.block_nil ⟨{ hI₃.toCommon with c_le := by omega_arith }, fun h0 d hd => ?_⟩
    have := hI₃.repr h0 d hd
    obtain e0 : ∀ n, n = 0 → D s₀ n = [] := by rintro _ rfl; simp [bytesAt]
    rw [e0 0 rfl, List.append_nil] at this
    rw [e0 _ hb, List.append_nil, repr_iff P hP.pos, ← hd.cnt_eq]; exact this
  · simp only [decide_eq_false_iff_not] at hb
    obtain hr := bufLen_le (w := w) hP.pos (cnt s₀)
    exact WP.seq (WP.mono (head_ok hP hf hp hr (by omega_arith) hI₃ hptr₃ (by rw [f₃.mem]; exact hcnt₂)
      (by rw [f₃.gpr]; exact hax₂)) fun s₄ h => WP.mono (rest_ok hP hf hp h) fun s₅ h => h.done hP)

end VG.Proof.Blake2.X86.Stream.Update

end

end

/-! ### `Blake2.X86.Stream.Init`, which this module and modules that import it used -/

section

/-!
# Streaming BLAKE2 on x86 (32-bit): `init`

`init` copies the key, if any, into the zeroed buffer (`keyBlock_ok`), keeping
our caller's `ebx` in the first word of the hash value meanwhile, then stores
the initial hash value (`initState_ok`), for either word size.
-/

@[expose] public section

namespace VG.Proof.Blake2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Spec.Blake2
open VG.Impl.Blake2.X86 (at_)
open VG.Impl.Blake2.X86.Stream
open VG.Proof.Blake2 (initX86 repr_keyBlock stateAt_congr bytesAt_congr bytesAt_add)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame writeBytes_append
  writeBytes_before write_eq_writeBytes)
open VG.Proof.MdStream.X86 (contains_addr sub_offset contains_offset)

variable {w : Nat} {P : Params w}

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev nn : Nat := (arg s₀ 1).toNat
abbrev key : BitVec 32 := arg s₀ 2
abbrev kk : Nat := (arg s₀ 3).toNat
abbrev stA : Addr := (st s₀).setWidth 64
abbrev keyA : Addr := (key s₀).setWidth 64
abbrev stR (w : Nat) : Region := ⟨stA s₀, bufOff w + blockBytes w⟩
abbrev keyR : Region := ⟨keyA s₀, kk s₀⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩
/-- The key. -/
abbrev K : List Byte := bytesAt s₀.mem (keyA s₀) (kk s₀)

end

structure Pre (P : Params w) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [stR s₀ w]
  key_st : (keyR s₀).Disjoint (stR s₀ w)
  a_st : (argR s₀).Disjoint (stR s₀ w)
  ret_st : (retR s₀).Disjoint (stR s₀ w)
  st_fit : (st s₀).toNat + (bufOff w + blockBytes w) ≤ 2 ^ 32
  key_fit : (key s₀).toNat + kk s₀ ≤ 2 ^ 32
  sp_fit : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32
  nn_lo : 1 ≤ nn s₀
  nn_hi : nn s₀ ≤ P.maxBytes
  kk_hi : kk s₀ ≤ P.maxBytes

theorem pre_of {s₀ : State} (h : (initX86 P).pre s₀) : Pre P s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

namespace Pre
variable {s₀ : State} (hp : Pre P s₀)
include hp

theorem arg_in {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 20) : (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  have := hp.sp_fit
  show (⟨addr (esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [addr_eq (by omega_using [this]), addr_eq (by omega_using [hd, this])]
  exact Offset.contains _ hd₁ (by omega_using [hd]) (by omega_using [])

theorem arg_sub {d : Nat} (hd₁ : 4 ≤ d) (hd : d + 4 ≤ 20) : Region.Sub ⟨addr (esp₀ s₀) d, 4⟩ (argR s₀) := by
  have := hp.sp_fit
  show Region.Sub _ ⟨addr (esp₀ s₀) 4, 16⟩
  rw [addr_eq (by omega_using [hd, this]), addr_eq (by omega_using [this])]
  exact Offset.sub _ hd₁ (by omega_using [hd])

theorem rin {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_in h₁ h₂⟩

/-- The arguments are kept by writes to the state. -/
theorem arg_keep {m : Mem} (hf : Frame [stR s₀ w] s₀.mem m) {d : Nat} (h₁ : 4 ≤ d) (h₂ : d + 4 ≤ 20) :
    m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 :=
  hf.readW (r := ⟨addr (esp₀ s₀) d, 4⟩) (Region.contains_self _ _)
    (by simpa using hp.a_st.sub_left (hp.arg_sub h₁ h₂)) (by decide)

theorem st_in {s : State} (hwr : s.wr = s₀.wr) {d n : Nat} (hd : d + n ≤ bufOff w + blockBytes w) (hn : 0 < n) :
    InRegions s.wr (addr (st s₀) d) n :=
  ⟨stR s₀ w, by simp [hwr, hp.wr], contains_addr hd hn hp.st_fit⟩

theorem st_inr {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {d n : Nat}
    (hd : d + n ≤ bufOff w + blockBytes w) (hn : 0 < n) : InRegions (s.rd ++ s.wr) (addr (st s₀) d) n :=
  ⟨stR s₀ w, by simp [hrd, hwr, hp.wr], contains_addr hd hn hp.st_fit⟩

end Pre

/-! ## Bytes -/

theorem writeW_eq (m : Mem) (a : Addr) (v : BitVec 32) : m.writeW a v = writeBytes m a (wordBytes v) := by
  rw [Mem.writeW, write_eq_writeBytes]; rfl

theorem wordBytes_zero : wordBytes (0 : BitVec 32) = List.replicate 4 0 := by decide

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) = if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  rw [show q + BitVec.ofNat 64 i - q = BitVec.ofNat 64 i by rw [BitVec.add_comm]; exact BitVec.add_sub_cancel _ _,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- The bytes at `q` after writing `xs` there: `xs`, then what was there. -/
theorem bytesAt_writeBytes_prefix (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (h : xs.length ≤ n)
    (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q xs) q n = xs ++ bytesAt m (q + BitVec.ofNat 64 xs.length) (n - xs.length) := by
  apply List.ext_getElem (by rw [List.length_append]; simp only [bytesAt, List.length_map, List.length_range]; omega_using [h])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega_arith : i < 2 ^ 64)]
  by_cases hi : i < xs.length
  · simp [hi, List.getElem_append_left, List.getD_eq_getElem?_getD]
  · rw [List.getElem_append_right (by omega_using [hi])]
    simp only [hi, ↓reduceIte, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat,
      show xs.length + (i - xs.length) = i by omega_using [hi]]

/-- The bytes of a run of zeros written at `q`. -/
theorem bytesAt_writeBytes_zeros (m : Mem) (q : Addr) {n a : Nat} (ha : a ≤ n) (hn : n < 2 ^ 64) :
    bytesAt (writeBytes m q (List.replicate n 0)) (q + BitVec.ofNat 64 a) (n - a) = List.replicate (n - a) 0 := by
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 _
  simp only [bytesAt, List.length_map, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, Offset.add_ofNat_add_ofNat,
    writeBytes_at m q _ (by omega_arith : a + i < 2 ^ 64), List.length_replicate, show a + i < n by omega_arith,
    ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_replicate, List.getElem_replicate]
  simp

/-! ## The key block -/

/-- During the zero stores. -/
def ZS (s₁ : State) (q : Addr) (j : Nat) (s : State) : Prop :=
  s.gpr = s₁.gpr ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧ s.mem = writeBytes s₁.mem q (List.replicate (4 * j) 0)

theorem zeros_ok {s₀ : State} (hp : Pre P s₀) {s₁ : State} (hax : s₁.gpr .eax = st s₀) (hdx : s₁.gpr .edx = 0)
    (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range (B w / 4)).flatMap fun j => [.store (at_ .eax (N w + 4 * j)) .edx])) s₁
      (ZS s₁ (stA s₀ + BitVec.ofNat 64 (bufOff w)) (B w / 4)) := by
  have fS := hp.st_fit
  refine wp_range_flatMap (M := isa) (ZS s₁ (stA s₀ + BitVec.ofNat 64 (bufOff w)))
    (fun j s hj ⟨hg, hrd, hwr', hm⟩ => ?_) _ (Nat.le_refl _) s₁
    ⟨rfl, rfl, rfl, by rw [Nat.mul_zero, List.replicate_zero, writeBytes_nil]⟩
  rw [B_eq] at hj
  rw [N_eq]
  obtain hj4 : bufOff w + 4 * j + 4 ≤ bufOff w + blockBytes w := by omega_using [hj]
  refine wp_stm (B := st s₀) (by rw [hg, hax]) (by rw [hwr', hwr]; exact hp.st_in rfl hj4 (by omega_using []))
    fun s' u' => WP.block_nil ⟨by rw [u'.gpr, hg], by rw [u'.rd, hrd], by rw [u'.wr, hwr'], ?_⟩
  rw [u'.mem, hm, hg, hdx, addr_eq (by omega_using [fS, hj4]), writeW_eq, wordBytes_zero, ← Offset.add_add]
  obtain e := writeBytes_append s₁.mem (stA s₀ + BitVec.ofNat 64 (bufOff w)) (List.replicate (4 * j) 0)
    (List.replicate 4 0) (by simp; omega_using [fS, hj4])
  rw [List.length_replicate] at e
  rw [e, List.replicate_append_replicate, Nat.mul_succ]

/-- After the key block (or none): our caller's `ebx`, `esi`, `edi`, `ebp`
and `esp` are kept, only the state is written, and the buffer holds the key,
padded with zeros, if there is one. -/
structure KB (P : Params w) (s₀ s : State) : Prop where
  gpr : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [stR s₀ w] s₀.mem s.mem
  buf : kk s₀ ≠ 0 → bytesAt s.mem (stA s₀ + BitVec.ofNat 64 (bufOff w)) (blockBytes w) =
    K s₀ ++ List.replicate (blockBytes w - kk s₀) 0

theorem keyBlock_ok (hP : Ok P) {s₀ : State} (hp : Pre P s₀) (hk : kk s₀ ≠ 0) {s : State}
    (hax : s.gpr .eax = st s₀) (hcx : s.gpr .ecx = arg s₀ 3)
    (hg : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    (hm : s.mem = s₀.mem) :
    WP isa (Impl.Blake2.X86.Stream.keyBlock (w := w)) s (KB P s₀) := by
  have hl := hP.len
  have hN := hP.N
  have hmx := hP.max
  have hkk := hp.kk_hi
  have hpos := hP.pos
  have hbb := hP.bb
  obtain fS := hp.st_fit; have fK := hp.key_fit
  unfold Impl.Blake2.X86.Stream.keyBlock
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine wp_movi fun s₁ u₁ => ?_
  refine WP.mono (zeros_ok hp (by rw [u₁.other _ (by decide), hax]) u₁.gpr (by rw [u₁.wr, hwr]))
    fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ => ?_
  rw [B_eq, show 4 * (blockBytes w / 4) = blockBytes w by rcases hP.bb with h | h <;> omega_using [h]] at m₂
  obtain ax₂ : s₂.gpr .eax = st s₀ := by rw [g₂, u₁.other _ (by decide), hax]
  refine wp_stm (o := 0) ax₂ (by rw [wr₂, u₁.wr, hwr]; exact hp.st_in rfl (by omega_using [hbb]) (by omega_using [])) fun s₃ u₃ => ?_
  obtain sp₃ : s₃.gpr .esp = esp₀ s₀ := by rw [u₃.gpr, g₂, u₁.other _ (by decide), hg _ (by decide)]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, rd₂, u₁.rd, hrd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, wr₂, u₁.wr, hwr]
  obtain m₃ : s₃.mem = (writeBytes s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w))
      (List.replicate (blockBytes w) 0)).writeW (addr (st s₀) 0) (s₀.gpr .ebx) := by
    rw [u₃.mem, m₂, u₁.mem, hm, g₂, u₁.other _ (by decide), hg _ (by decide)]
  obtain F₃ : Frame [stR s₀ w] s₀.mem s₃.mem := by
    rw [m₃]
    exact (writeBytes_frame _ _ _ (contains_offset (by simp only [List.length_replicate]; omega_using []) (by omega_using [fS]))).writeW
      (List.mem_singleton_self _) _ (contains_addr (by omega_using [hbb]) (by omega_using []) fS)
  refine wp_ldm sp₃ (hp.rin rd₃ (d := 12) (by omega_using []) (by omega_using [])) fun s₄ u₄ => WP.block_nil ?_
  obtain dx₄ : s₄.gpr .edx = key s₀ := by rw [u₄.gpr, hp.arg_keep F₃ (by omega_using []) (by omega_using [])]; rfl
  have m₄ : s₄.mem = s₃.mem := u₄.mem
  -- The copy.
  obtain hk32 : kk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  refine WP.seq (copyLoop_ok (w := w) (tmp := .bl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (dA := st s₀) (sA := key s₀) (k := kk s₀) (by omega_using [hk]) hk32 (by omega_using [fK]) (by omega_using [hmx, hkk, fS]) dx₄
    (by rw [u₄.other _ (by decide), u₃.gpr, ax₂])
    (by rw [u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hcx]; simp)
    (fun i hi => ⟨keyR s₀, by simp [u₄.rd, rd₃, hp.rd], contains_offset (by omega_using [hi]) (by omega_using [hk32, hi])⟩)
    (fun i hi => by
      rw [u₄.wr, wr₃, addr_eq (by omega_using [hbb, fS])]
      exact ⟨stR s₀ w, by simp [hp.wr], by rw [Offset.add_add]; exact contains_offset (by omega_using [hmx, hkk, hi]) (by omega_using [fS, hk32, hi])⟩)
    (by rw [addr_eq (by omega_using [hbb, fS])]; exact hp.key_st.sub_right (sub_offset (by omega_using [hmx, hkk]) (by omega_using [fS])))
    fun s₅ h₅ => ?_)
  -- The bytes copied are the key's, and the spill is outside them.
  obtain hK : bytesAt s₄.mem (keyA s₀) (kk s₀) = K s₀ :=
    bytesAt_congr fun i hi => by
      rw [m₄]
      exact F₃.bytes (R := keyR s₀) (by simpa using hp.key_st) (by simp only; omega_using [hk32]) hi
  have hm₅ := h₅.mem
  rw [List.take_of_length_le (by simp [bytesAt]), hK, m₄, addr_eq (by omega_using [hbb, fS])] at hm₅
  obtain rd₅ : s₅.rd = s₀.rd := by rw [h₅.rd, u₄.rd, rd₃]
  obtain wr₅ : s₅.wr = s₀.wr := by rw [h₅.wr, u₄.wr, wr₃]
  refine wp_ldm (b := .esp) (by rw [h₅.other _ (by decide) (by decide) (by decide) (by decide), u₄.other _ (by decide), sp₃])
    (hp.rin rd₅ (d := 4) (by omega_using []) (by omega_using [])) fun s₆ u₆ => ?_
  obtain F₅ : Frame [stR s₀ w] s₀.mem s₅.mem := by
    rw [hm₅]
    exact F₃.trans (writeBytes_frame _ _ _ (by
      simp only [bytesAt, List.length_map, List.length_range]; exact contains_offset (by omega_using [hmx, hkk]) (by omega_using [fS])))
  obtain ax₆ : s₆.gpr .eax = st s₀ := by rw [u₆.gpr, hp.arg_keep F₅ (by omega_using []) (by omega_using [])]; rfl
  refine wp_ldm ax₆ (by rw [u₆.rd, u₆.wr, rd₅, wr₅]; exact hp.st_inr rfl rfl (by omega_using [hbb]) (by omega_using []))
    fun s₇ u₇ => WP.block_nil ?_
  obtain m₇ : s₇.mem = s₅.mem := by rw [u₇.mem, u₆.mem]
  -- The spilled `ebx`, outside the buffer.
  obtain hbx : s₅.mem.readW (addr (st s₀) 0) 32 = s₀.gpr .ebx := by
    rw [hm₅, m₃]
    rw [(writeBytes_frame (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) _ _ _ (by
      simp only [bytesAt, List.length_map, List.length_range]
      exact Offset.contains _ (Nat.le_refl _) (by omega_using [hmx, hkk]) (by omega_using [fS]))).readW
      (r := ⟨addr (st s₀) 0, 4⟩) (Region.contains_self _ _) ?_ (by decide), Mem.readW_writeW_self32]
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega_using [])]
    exact Offset.disjoint (stA s₀) (by omega_using [hN, hbb]) (by omega_using []) (by omega_using [fS])
  refine ⟨fun r hr => ?_, by rw [u₇.rd, u₆.rd, rd₅], by rw [u₇.wr, u₆.wr, wr₅],
    by rw [m₇]; exact F₅, fun _ => ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [u₇.gpr, u₆.mem, hbx]
    all_goals
      rw [u₇.other _ (by decide), u₆.other _ (by decide), h₅.other _ (by decide) (by decide) (by decide) (by decide),
        u₄.other _ (by decide), u₃.gpr, g₂, u₁.other _ (by decide), hg _ (by decide)]
  · have hKl : (K s₀).length = kk s₀ := by simp [bytesAt]
    rw [m₇, hm₅, m₃, bytesAt_writeBytes_prefix _ _ (by rw [hKl]; omega_using [hmx, hkk]) (by omega_using [fS]), hKl]
    refine congrArg (K s₀ ++ ·) ?_
    rw [← bytesAt_writeBytes_zeros s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w)) (a := kk s₀)
      (n := blockBytes w) (by omega_using [hmx, hkk]) (by omega_using [fS])]
    obtain hf : Frame [⟨addr (st s₀) 0, 4⟩] (writeBytes s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w))
        (List.replicate (blockBytes w) 0)) ((writeBytes s₀.mem (stA s₀ + BitVec.ofNat 64 (bufOff w))
        (List.replicate (blockBytes w) 0)).writeW (addr (st s₀) 0) (s₀.gpr .ebx)) :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    refine bytesAt_congr fun i hi => ?_
    refine hf.bytes (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w) + BitVec.ofNat 64 (kk s₀), blockBytes w - kk s₀⟩)
      ?_ (by simp only; omega_using [fS]) hi
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by omega_using []), Offset.add_add]
    exact Offset.disjoint (stA s₀) (by omega_using [hN, hbb]) (by omega_using [fS, hi]) (by omega_using [])

/-! ## The initial hash value -/

theorem wp_xori {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d (.imm v) :: is)) s Q :=
  cons rfl (k _ (Upd.flags _ _ _ _ _ _))

/-- During the stores of the IV. -/
def WS (P : Params w) (st : BitVec 32) (s₁ : State) (j : Nat) (s : State) : Prop :=
  (∀ r, r ≠ .ecx → s.gpr r = s₁.gpr r) ∧ s.rd = s₁.rd ∧ s.wr = s₁.wr ∧
    Frame [⟨st.setWidth 64, bufOff w⟩] s₁.mem s.mem ∧ ∀ i < j, s.mem.readW (addr st (4 * i)) 32 = ivWord P i

theorem words_ok (hP : Ok P) {s₀ : State} (hp : Pre P s₀) {s₁ : State} (hax : s₁.gpr .eax = st s₀)
    (hwr : s₁.wr = s₀.wr) :
    WP isa (.block ((List.range (N w / 4)).flatMap fun k =>
      [.mov .ecx (.imm (ivWord P k)), .store (at_ .eax (4 * k)) .ecx])) s₁ (WS P (st s₀) s₁ (N w / 4)) := by
  have fS := hp.st_fit
  have hl := hP.len
  have hbb := hP.bb
  refine wp_range_flatMap (M := isa) (WS P (st s₀) s₁) (fun k s hk ⟨hg, hrd, hwr', hf, hv⟩ => ?_) _
    (Nat.le_refl _) s₁ ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (by omega_using [])⟩
  rw [N_eq] at hk
  have hN : bufOff w = blockBytes w / 2 := hP.N
  obtain hk4 : 4 * k + 4 ≤ bufOff w := by omega_using [hk]
  refine wp_movi fun s₂ u₂ => wp_stm (B := st s₀) (by rw [u₂.other _ (by decide), hg _ (by decide), hax])
    (by rw [u₂.wr, hwr', hwr]; exact hp.st_in rfl (by omega_using [hk4]) (by omega_using [])) fun s₃ u₃ => WP.block_nil ?_
  refine ⟨fun r hr => by rw [u₃.gpr, u₂.other r hr, hg r hr], by rw [u₃.rd, u₂.rd, hrd],
    by rw [u₃.wr, u₂.wr, hwr'], ?_, fun i hi => ?_⟩
  · rw [u₃.mem, u₂.mem]
    exact hf.writeW (List.mem_singleton_self _) _ (contains_addr (by omega_using [hk4]) (by omega_using []) (by omega_using [fS]))
  · rw [u₃.mem, u₂.gpr, u₂.mem]
    by_cases e : i = k
    · subst e; rw [Mem.readW_writeW_self32]
    · rw [MdStream.X86.readW_writeW_addr _ _ (by omega_using [fS, hk4, hi]) (by omega_using [fS, hk4]) (by omega_using [e])]
      exact hv i (by omega_using [hi, e])

theorem rot24 {kk : Nat} (h : kk < 2 ^ 24) :
    (BitVec.ofNat 32 kk).rotateRight 24 = BitVec.ofNat 32 kk <<< 8 := by
  rw [BitVec.rotateRight_def]
  obtain e : BitVec.ofNat 32 kk >>> (24 % 32) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega_using [h])]
    show kk / 2 ^ (24 % 32) = 0
    exact Nat.div_eq_of_lt (by simpa using h)
  rw [e, BitVec.zero_or]

theorem getElem!_IV (P : Params w) {i : Nat} (hi : i < 8) : P.IV[i]! = P.IV[i] := by
  simp [hi]

theorem ivWord32 (P : Params 32) {i : Nat} (hi : i < 8) : ivWord P i = P.IV[i] := by
  simp only [ivWord, Nat.reduceDiv, Nat.div_one, Nat.mod_one, Nat.mul_zero, getElem!_IV P hi,
    BitVec.extractLsb'_eq_self]

theorem ivWord64_lo (P : Params 64) {i : Nat} (hi : i < 8) :
    ivWord P (2 * i) = Proof.Sha512.Word64.lo P.IV[i] := by
  simp only [ivWord, Nat.reduceDiv, Nat.mul_div_cancel_left _ (by decide : 0 < 2), Nat.mul_mod_right,
    Nat.mul_zero, getElem!_IV P hi, Proof.Sha512.Word64.lo]

theorem ivWord64_hi (P : Params 64) {i : Nat} (hi : i < 8) :
    ivWord P (2 * i + 1) = Proof.Sha512.Word64.hi P.IV[i] := by
  obtain e : (2 * i + 1) / 2 = i := by omega_using []
  obtain e' : (2 * i + 1) % 2 = 1 := by omega_using []
  simp only [ivWord, Nat.reduceDiv, e, e', Nat.mul_one, getElem!_IV P hi, Proof.Sha512.Word64.hi]

theorem lohi (X : BitVec 64) (x : BitVec 32) (h : X.toNat = x.toNat) :
    Proof.Sha512.Word64.lo X = x ∧ Proof.Sha512.Word64.hi X = 0 := by
  have := x.isLt
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
  · rw [Proof.Sha512.Word64.lo_toNat, h, Nat.mod_eq_of_lt this]
  · rw [Proof.Sha512.Word64.hi_toNat, h, Nat.div_eq_of_lt this]; rfl

/-- The initial hash value, from the words stored. -/
theorem stateAt_init (hP : Ok P) {m : Mem} {st : BitVec 32} (hfit : st.toNat + bufOff w ≤ 2 ^ 32)
    {kk nn : Nat} (hkk : kk < 2 ^ 24) (hnn : nn < 2 ^ 32)
    (h0 : m.readW (addr st 0) 32 =
      ((ivWord P 0 ^^^ 0x01010000) ^^^ (BitVec.ofNat 32 kk).rotateRight 24) ^^^ BitVec.ofNat 32 nn)
    (h : ∀ i, 1 ≤ i → i < bufOff w / 4 → m.readW (addr st (4 * i)) 32 = ivWord P i) :
    stateAt w m (st.setWidth 64) = init P nn kk := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, Spec.Blake2.init, Vector.getElem_set]
  rcases hP.w with rfl | rfl
  · -- 64-bit words: two 32-bit words each.
    obtain e₀ : addr st (8 * j) = st.setWidth 64 + BitVec.ofNat 64 (64 / 8 * j) := addr_eq (by simp [bufOff] at hfit; omega_using [hj, hfit])
    obtain e₁ : addr st (8 * j + 4) = st.setWidth 64 + BitVec.ofNat 64 (64 / 8 * j) + 4 := by
      rw [addr_eq (by simp [bufOff] at hfit; omega_using [hj, hfit]), show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Offset.add_ofNat_add_ofNat]
    rw [Proof.Sha512.Word64.readW64, ← e₁, ← e₀, show 8 * j = 4 * (2 * j) by omega_using [],
      show 4 * (2 * j) + 4 = 4 * (2 * j + 1) by omega_using []]
    obtain hhi := h (2 * j + 1) (by omega_using []) (by simp [bufOff]; omega_using [hj])
    rw [hhi, ivWord64_hi P hj]
    by_cases e : j = 0
    · subst e
      simp only [Nat.mul_zero, ↓reduceIte] at h0 ⊢
      obtain l0 := ivWord64_lo P (i := 0) (by decide)
      rw [Nat.mul_zero] at l0
      rw [h0, l0, rot24 hkk]
      obtain hC := lohi (((16842752 : Nat) : BitVec 64)) (0x01010000 : BitVec 32) rfl
      obtain hK := lohi (BitVec.ofNat 64 kk <<< 8) (BitVec.ofNat 32 kk <<< 8) (by
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]; omega_using [hkk])
      obtain hN := lohi (BitVec.ofNat 64 nn) (BitVec.ofNat 32 nn) (by simp only [BitVec.toNat_ofNat]; omega_using [hnn])
      refine Proof.Sha512.Word64.eq_of_lo_hi ?_ ?_
      · rw [Proof.Sha512.Word64.lo_append, Proof.Sha512.Word64.lo_xor, Proof.Sha512.Word64.lo_xor,
          Proof.Sha512.Word64.lo_xor, hC.1, hK.1, hN.1]
      · rw [Proof.Sha512.Word64.hi_append, Proof.Sha512.Word64.hi_xor, Proof.Sha512.Word64.hi_xor,
          Proof.Sha512.Word64.hi_xor, hC.2, hK.2, hN.2]; simp
    · rw [h (2 * j) (by omega_using [e]) (by simp [bufOff]; omega_using [hj]), ivWord64_lo P hj,
        Proof.Sha512.Word64.hi_append_lo]
      simp [Ne.symm e]
  · have e₀ : addr st (4 * j) = st.setWidth 64 + BitVec.ofNat 64 (32 / 8 * j) := addr_eq (by simp [bufOff] at hfit; omega_using [hj, hfit])
    rw [← e₀]
    by_cases e : j = 0
    · subst e
      simp only [Nat.mul_zero, ↓reduceIte]
      rw [h0, ivWord32 P (by decide), rot24 hkk]; rfl
    · rw [h j (by omega_using [e]) (by simp [bufOff]; omega_using [hj]), ivWord32 P hj]
      simp [Ne.symm e]

theorem initState_ok (hP : Ok P) {s₀ : State} (hp : Pre P s₀) {s : State} (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hsp : s.gpr .esp = esp₀ s₀) (hf : Frame [stR s₀ w] s₀.mem s.mem) :
    WP isa (.block (.mov .eax (.mem (at_ .esp 4)) :: initState P)) s fun s' =>
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨stA s₀, bufOff w⟩] s.mem s'.mem ∧ stateAt w s'.mem (stA s₀) = Spec.Blake2.init P (nn s₀) (kk s₀) := by
  have hl := hP.len
  have hbb := hP.bb
  have hN := hP.N
  have fS := hp.st_fit
  have hkk := hp.kk_hi
  have hmx := hP.max
  refine wp_ldm hsp (hp.rin hrd (d := 4) (by omega_using []) (by omega_using [])) fun s₁ u₁ => ?_
  obtain ax₁ : s₁.gpr .eax = st s₀ := by rw [u₁.gpr, hp.arg_keep hf (by omega_using []) (by omega_using [])]; rfl
  unfold initState
  rw [WP.block_append_iff]
  refine WP.mono (words_ok hP hp ax₁ (by rw [u₁.wr, hwr])) fun s₂ ⟨g₂, rd₂, wr₂, f₂, v₂⟩ => ?_
  obtain ax₂ : s₂.gpr .eax = st s₀ := by rw [g₂ _ (by decide), ax₁]
  obtain hN4 : 0 < N w / 4 := by rw [N_eq]; omega_using [hbb, hN]
  obtain f₂' : Frame [stR s₀ w] s₁.mem s₂.mem := f₂.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega_using [])⟩
  obtain F₂ : Frame [stR s₀ w] s₀.mem s₂.mem := hf.trans (u₁.mem ▸ f₂')
  obtain rd₂' : s₂.rd = s₀.rd := by rw [rd₂, u₁.rd, hrd]
  obtain wr₂' : s₂.wr = s₀.wr := by rw [wr₂, u₁.wr, hwr]
  obtain sp₂ : s₂.gpr .esp = esp₀ s₀ := by rw [g₂ _ (by decide), u₁.other _ (by decide), hsp]
  refine wp_ldm ax₂ (hp.st_inr rd₂' wr₂' (by omega_using [hbb]) (by omega_using [])) fun s₃ u₃ => ?_
  refine wp_xori fun s₄ u₄ => ?_
  refine wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), sp₂])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact hp.rin rd₂' (d := 16) (by omega_using []) (by omega_using [])) fun s₅ u₅ => ?_
  refine wp_ror ⟨by decide, by decide⟩ fun s₆ u₆ => wp_xor fun s₇ u₇ => ?_
  obtain i8 := hp.rin rd₂' (d := 8) (by omega_using []) (by omega_using [])
  refine wp_xorm (b := .esp) (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
    u₄.other _ (by decide), u₃.other _ (by decide), sp₂])
    (by rw [u₇.rd, u₇.wr, u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i8) fun s₈ u₈ => ?_
  refine wp_stm (o := 0) (by rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
    u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), ax₂])
    (by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr]; exact hp.st_in wr₂' (by omega_using [hbb]) (by omega_using []))
    fun s₉ u₉ => WP.block_nil ?_
  obtain hm₈ : s₈.mem = s₂.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  obtain a16 : s₅.gpr .edx = arg s₀ 3 := by
    rw [u₅.gpr, u₄.mem, u₃.mem, hp.arg_keep F₂ (by omega_using []) (by omega_using [])]; rfl
  obtain a8 : s₇.mem.readW (addr (esp₀ s₀) 8) 32 = arg s₀ 1 := by
    rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hp.arg_keep F₂ (by omega_using []) (by omega_using [])]; rfl
  obtain v₀ : s₂.mem.readW (addr (st s₀) 0) 32 = ivWord P 0 := v₂ 0 hN4
  obtain hV : s₈.gpr .ecx = ((ivWord P 0 ^^^ 0x01010000) ^^^ (BitVec.ofNat 32 (kk s₀)).rotateRight 24) ^^^
      BitVec.ofNat 32 (nn s₀) := by
    rw [u₈.gpr, a8, u₇.gpr, u₆.gpr, u₆.other _ (by decide), u₅.other _ (by decide), a16, u₄.gpr, u₃.gpr, v₀]
    simp
  obtain hm₉ : s₉.mem = s₂.mem.writeW (addr (st s₀) 0) (s₈.gpr .ecx) := by rw [u₉.mem, hm₈]
  refine ⟨fun r h1 h2 h3 => ?_, by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd],
    by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr], ?_, ?_⟩
  · rw [u₉.gpr, u₈.other r h2, u₇.other r h2, u₆.other r h3, u₅.other r h3, u₄.other r h2, u₃.other r h2,
      g₂ r h2, u₁.other r h1]
  · rw [hm₉, ← u₁.mem]
    exact f₂.writeW (List.mem_singleton_self _) _ (contains_addr (by omega_using [hbb, hN]) (by omega_using []) (by omega_using [fS]))
  · rw [hm₉]
    refine stateAt_init hP (by omega_using [fS]) (by omega_using [hbb, hkk, hmx]) (by have := (arg s₀ 1).isLt; omega_using [this])
      (by rw [Mem.readW_writeW_self32, hV]) fun i h1 h2 => ?_
    rw [MdStream.X86.readW_writeW_addr _ _ (by omega_using [fS, h2]) (by omega_using [fS, h2]) (by omega_using [h1])]
    exact v₂ i (by rw [N_eq]; omega_using [h2])

/-! ## The whole function -/

theorem correct (hP : Ok P) {s₀ : State} (hp : Pre P s₀) :
    WP isa (Impl.Blake2.X86.Stream.init P) s₀ fun s' => abiPreserved s₀ s' ∧ (initX86 P).post s₀ s' := by
  have hl := hP.len
  have hkk := hp.kk_hi
  have hmx := hP.max
  unfold Impl.Blake2.X86.Stream.init
  refine WP.seq (wp_ldm rfl (hp.rin rfl (d := 4) (by omega_using []) (by omega_using [])) fun s₁ u₁ => ?_)
  refine wp_ldm (by rw [u₁.other _ (by decide)]) (by rw [u₁.rd, u₁.wr]; exact hp.rin rfl (d := 16) (by omega_using []) (by omega_using []))
    fun s₂ u₂ => wp_test fun s₃ f₃ z₃ => WP.block_nil ?_
  obtain ax₃ : s₃.gpr .eax = st s₀ := by rw [f₃.gpr, u₂.other _ (by decide), u₁.gpr]; rfl
  obtain cx₃ : s₃.gpr .ecx = arg s₀ 3 := by rw [f₃.gpr, u₂.gpr, u₁.mem]; rfl
  obtain g₃ : ∀ r ∈ calleeSaved, s₃.gpr r = s₀.gpr r := fun r hr => by
    rw [f₃.gpr, u₂.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide),
      u₁.other r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
  obtain rd₃ : s₃.rd = s₀.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
  obtain wr₃ : s₃.wr = s₀.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
  obtain m₃ : s₃.mem = s₀.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  obtain hz : isa.eval .e s₃ = some (decide (kk s₀ = 0)) := by
    show s₃.zf = _
    rw [z₃, u₂.gpr, u₁.mem, BitVec.and_self]
    show some (arg s₀ 3 == 0) = _
    have := ofNat_beq_zero (arg s₀ 3).isLt
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    rw [this]
  refine WP.seq (WP.mono (Q := KB P s₀) ?_ fun s₄ hK => ?_)
  · refine WP.ite _ hz (fun hb => ?_) (fun hb => ?_)
    · simp only [decide_eq_true_eq] at hb
      exact WP.block_nil ⟨g₃, rd₃, wr₃, by rw [m₃]; exact Frame.refl _ _, fun h => absurd hb h⟩
    · simp only [decide_eq_false_iff_not] at hb
      exact keyBlock_ok hP hp hb ax₃ cx₃ g₃ rd₃ wr₃ m₃
  refine WP.mono (initState_ok hP hp hK.rd hK.wr (hK.gpr _ (by decide)) hK.frame)
    fun s₅ ⟨g₅, rd₅, wr₅, f₅, st₅⟩ => ?_
  obtain F : Frame [stR s₀ w] s₀.mem s₅.mem := hK.frame.trans (f₅.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀ w, by simp, Region.sub_prefix (by omega_using [])⟩)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · rw [g₅ r (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)]
    exact hK.gpr r hr
  · exact F.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · show Spec.Blake2.Repr P (Spec.Blake2.init P (nn s₀) (kk s₀)) s₅.mem (stA s₀) (Spec.Blake2.keyBlock w (K s₀))
    obtain hKl : (K s₀).length = kk s₀ := by simp [bytesAt]
    refine repr_keyBlock P hP.pos (by omega_using [hkk, hmx, hKl]) st₅ fun hk => ?_
    rw [hKl] at hk ⊢
    rw [← hK.buf hk]
    refine bytesAt_congr fun i hi => ?_
    refine f₅.bytes (R := ⟨stA s₀ + BitVec.ofNat 64 (bufOff w), blockBytes w⟩) ?_ (by simp only; omega_using [hl]) hi
    simp only [List.mem_singleton, forall_eq]
    exact Offset.disjoint_base _ (Nat.le_refl _) (by have := hp.st_fit; omega_using [this])

end VG.Proof.Blake2.X86.Stream.Init

end

end

/-!
# Streaming BLAKE2 on x86 (32-bit): `Verified`, for any compression function

`init`, `update` and `finalize` meet the per-target contracts of
`Proof/Blake2/X86/Contract.lean`, for either word size, given a correct
compression function (`CalleeOk`) and that the code (with that compression
function) is constant time, which each instance proves by the taint analysis
(`VG.Taint.constantTime`) from the initial taint (`τInit`, `τUpdate`,
`τFinalize`) and the facts that the public inputs give it (`init_agree`,
`update_agree`, `finalize_agree`).
-/

@[expose] public section

namespace VG.Proof.Blake2.X86.Stream

open VG VG.X86 VG.Spec.Blake2
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86)

variable {w : Nat} {P : Params w}

/-! ## The initial taint -/

section
variable (w : Nat)

/-- `init`: the stack arguments are public, and the word holding `state` is
the base address of the writable region. -/
def τInit : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w], argLen := 20,
    argBases := [(4, 0)] }

/-- `update`: the stack arguments are public, the words holding `state` and
`scratch` are the base addresses of the writable regions, and the 32 bytes
below `esp` are outside them. -/
def τUpdate : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w, 576], argLen := 28,
    argBases := [(4, 0), (24, 1)], room := 32 }

/-- `finalize`: as `update`, with the output. -/
def τFinalize : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [bufOff w + blockBytes w, bufOff w, 576], argLen := 24,
    argBases := [(4, 0), (16, 1), (20, 2)], room := 32 }

end

theorem argMem_eq {s₁ s₂ : State} {n : Nat} (f₁ : (s₁.gpr .esp).toNat + n ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + n ≤ 2 ^ 32) (ha : ∀ i, 4 + 4 * i < n → arg s₁ i = arg s₂ i) {k : Nat}
    (h4 : 4 ≤ k) (hk : k < n) :
    s₁.mem (VG.X86.Taint.argByte s₁ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) =
      s₂.mem (VG.X86.Taint.argByte s₂ (VG.X86.Taint.depth ([] : List (Option Nat)) + k)) := by
  rw [show VG.X86.Taint.depth ([] : List (Option Nat)) = 0 from rfl, Nat.zero_add,
    VG.X86.Taint.argByte_eq f₁ h4 hk, VG.X86.Taint.argByte_eq f₂ h4 hk,
    Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by omega_using [])), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by omega_using []))]
  exact congrArg _ (ha _ (by omega_using [h4, hk]))

/-! ## `init` -/

theorem init_wf (hP : Ok P) {s : State} (h : (initX86 P).pre s) : VG.X86.Taint.Wf (τInit w) s := by
  have hp := Init.pre_of h
  have hst := hp.st_fit; have hs := hp.sp_fit; have hl := hP.len
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, τInit], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τInit]; omega, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega_using [hst]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 16) (by omega) hp.ret_st hp.a_st
  · intro p hp'
    simp only [τInit, List.mem_cons, List.not_mem_nil, or_false] at hp'
    subst hp'
    exact ⟨by simp [τInit], by simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]⟩

theorem init_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (initX86 P).pre s₁) (h₂ : (initX86 P).pre s₂)
    (hpub : (initX86 P).pub s₁ s₂) : VG.X86.Taint.Agree (τInit w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Init.pre_of h₁; have hp₂ := Init.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, init_wf hP h₁, init_wf hP h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 20) (by have := hp₁.sp_fit; omega) (by have := hp₂.sp_fit; omega)
      (fun i hi => ha i (by omega_using [hi])) h4 hk⟩
  · simp only [τInit, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Init.stR, Init.stA, Init.st, ha 0 (by omega_using [])]

/-! ## `update` -/

theorem update_wf (hP : Ok P) {s : State} (h : (updateX86 P).pre s) : VG.X86.Taint.Wf (τUpdate w) s := by
  have hp := Update.pre_of h
  have hst := hp.st_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hl := hP.len
  obtain ⟨-, -, -, -, -, -, -, -, -, k1, k2, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τUpdate], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τUpdate]; omega, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    exact ⟨hp.st_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 24) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [τUpdate, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by simp [τUpdate], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    exacts [k1, k2]

theorem update_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (updateX86 P).pre s₁) (h₂ : (updateX86 P).pre s₂)
    (hpub : (updateX86 P).pub s₁ s₂) : VG.X86.Taint.Agree (τUpdate w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Update.pre_of h₁; have hp₂ := Update.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, update_wf hP h₁, update_wf hP h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 28) hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega_using [hi])) h4 hk⟩
  · simp only [τUpdate, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Update.stR, Update.scR, Update.stA, Update.scA, Update.st, Update.scr, ha 0 (by omega_using []),
      ha 5 (by omega_using [])]

/-! ## `finalize` -/

theorem finalize_wf (hP : Ok P) {s : State} (h : (finalizeX86 P).pre s) :
    VG.X86.Taint.Wf (τFinalize w) s := by
  have hp := Finalize.pre_of h
  have hst := hp.st_fit; have hso := hp.out_fit; have hsc := hp.scr_fit; have hs := hp.sp_fit
  have hlo := hp.sp_lo; have hl := hP.len
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, k1, k2, k3, -⟩ := h
  refine VG.X86.Taint.Wf.entryRoom rfl ⟨fun _ => ⟨by simp [hp.wr, τFinalize], ?_, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨by simp only [τFinalize]; omega, ?_⟩, ?_⟩ fun _ => ⟨hlo, ?_⟩
  · simp only [hp.wr, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true]
    exact ⟨⟨hp.st_out, hp.st_scr⟩, hp.out_scr, fun _ h => h.elim⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega_arith
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_st hp.a_st
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_out hp.a_out
    · exact VG.X86.Taint.frame_disjoint (n := 20) (by omega) hp.ret_scr hp.a_scr
  · intro p hp'
    simp only [τFinalize, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl <;> refine ⟨by simp [τFinalize], ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    exacts [k1, k2, k3]

theorem finalize_agree (hP : Ok P) {s₁ s₂ : State} (h₁ : (finalizeX86 P).pre s₁)
    (h₂ : (finalizeX86 P).pre s₂) (hpub : (finalizeX86 P).pub s₁ s₂) :
    VG.X86.Taint.Agree (τFinalize w) s₁ s₂ := by
  obtain ⟨hesp, ha⟩ := hpub
  have hp₁ := Finalize.pre_of h₁; have hp₂ := Finalize.pre_of h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, finalize_wf hP h₁, finalize_wf hP h₂,
    VG.X86.Taint.slotsOk_empty, VG.X86.Taint.slotsAgree_empty, fun _ => hesp,
    fun k h4 hk => argMem_eq (n := 24) hp₁.sp_fit hp₂.sp_fit (fun i hi => ha i (by omega_using [hi])) h4 hk⟩
  · simp only [τFinalize, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]
    simp only [Finalize.stR, Finalize.outR, Finalize.scR, Finalize.stA, Finalize.opA, Finalize.scA,
      Finalize.st, Finalize.op, Finalize.scr, ha 0 (by omega_using []), ha 3 (by omega_using []), ha 4 (by omega_using [])]

/-! ## `Verified` -/

theorem init_verified (hP : Ok P)
    (hct : ConstantTime isa (initX86 P).pre (initX86 P).pub (Impl.Blake2.X86.Stream.init P))
    (hsat : ∃ s, (initX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.init P) (initX86 P) :=
  ⟨fun _ hs => Init.correct hP (Init.pre_of hs), hct, hsat⟩

theorem update_verified (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    (hct : ConstantTime isa (updateX86 P).pre (updateX86 P).pub (Impl.Blake2.X86.Stream.update w name code))
    (hsat : ∃ s, (updateX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.update w name code) (updateX86 P) :=
  ⟨fun _ hs => Update.correct hP hf (Update.pre_of hs), hct, hsat⟩

theorem finalize_verified (hP : Ok P) {name : String} {code : Prog isa} (hf : CalleeOk P code)
    (hct : ConstantTime isa (finalizeX86 P).pre (finalizeX86 P).pub (Impl.Blake2.X86.Stream.finalize w name code))
    (hsat : ∃ s, (finalizeX86 P).pre s) :
    Verified X86.target (Impl.Blake2.X86.Stream.finalize w name code) (finalizeX86 P) :=
  ⟨fun _ hs => Finalize.correct hP hf (Finalize.pre_of hs), hct, hsat⟩

end VG.Proof.Blake2.X86.Stream
