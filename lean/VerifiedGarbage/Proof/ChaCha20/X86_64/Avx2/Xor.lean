module

import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2.RoundsVL
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Xor
public import VerifiedGarbage.Proof.ChaCha20.X86_64.Avx2Tail.Out
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# ChaCha20 keystream XOR on x86-64 with AVX2

The entry state, from the source to the destination (`TPre`, which the
other kernels' proofs use too), and the loop over 512-byte chunks (`Setup`,
`Rounds`, `Finish`); the rest, constant time and the calling convention are
in `Avx2/Verified.lean`.
-/

@[expose] public section

namespace VG.Proof.ChaCha20.X86_64.Avx2

open VG VG.X86_64 VG.Impl.ChaCha20.X86_64.Avx2
open VG.Impl.ChaCha20.X86_64 (at_)
open VG.Spec.ChaCha20 (Word stateAt keystream serialize bytesAt)
open VG.Proof.ChaCha20

/-! ## The entry state -/

section
variable (s₀ : State)
abbrev est : Addr := s₀.gpr .rdi
abbrev edp : Addr := s₀.gpr .rsi
abbrev eL : Nat := (s₀.gpr .rdx).toNat
abbrev ebp : Addr := s₀.gpr .rcx
abbrev edR : Region := ⟨edp s₀, eL s₀⟩
abbrev eret : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev estk : Region := below (s₀.gpr .rsp) 16
/-- The state, the data and the keystream on entry. -/
abbrev S0 : CState := stateAt s₀.mem (est s₀)
abbrev D0 (k : Nat) : Byte := s₀.mem (edp s₀ + BitVec.ofNat 64 k)
abbrev KS : List Byte := keystream (S0 s₀) (eL s₀)
end

theorem eL_lt (s₀ : State) : eL s₀ < 2 ^ 64 := (s₀.gpr .rdx).isLt

/-! ## From a source to a destination -/

section
variable (s₀ : State)
/-- The destination (`r8`) and its region. -/
abbrev edq : Addr := s₀.gpr .r8
abbrev eqR : Region := ⟨edq s₀, eL s₀⟩
/-- The destination's bytes on entry. -/
abbrev Q0 (k : Nat) : Byte := s₀.mem (edq s₀ + BitVec.ofNat 64 k)
/-- The regions the code writes, from a source to a destination. -/
abbrev frT : List Region := [stR (est s₀), eqR s₀, bufR (ebp s₀)]
end

/-- What the proofs use of `xorTo 16`'s precondition, from the source (read)
to the destination (written), which is the source or apart from it: of the
regions, only that the source may be read (so that `vg_chacha20_xor_split`,
which XORs in place what its source and its destination hold, has it too). -/
structure TPre (s₀ : State) : Prop where
  rd : edR s₀ ∈ s₀.rd ++ s₀.wr
  wr : s₀.wr = frT s₀
  st_d : (stR (est s₀)).Disjoint (edR s₀)
  st_q : (stR (est s₀)).Disjoint (eqR s₀)
  st_b : (stR (est s₀)).Disjoint (bufR (ebp s₀))
  d_b : (edR s₀).Disjoint (bufR (ebp s₀))
  q_b : (eqR s₀).Disjoint (bufR (ebp s₀))
  alias : edq s₀ = edp s₀ ∨ (edR s₀).Disjoint (eqR s₀)
  ret_st : (eret s₀).Disjoint (stR (est s₀))
  ret_q : (eret s₀).Disjoint (eqR s₀)
  ret_b : (eret s₀).Disjoint (bufR (ebp s₀))
  stk_st : (estk s₀).Disjoint (stR (est s₀))
  stk_d : (estk s₀).Disjoint (edR s₀)
  stk_q : (estk s₀).Disjoint (eqR s₀)
  stk_b : (estk s₀).Disjoint (bufR (ebp s₀))
  nowrap : (edp s₀).toNat + eL s₀ ≤ 2 ^ 64
  nowrap_q : (edq s₀).toNat + eL s₀ ≤ 2 ^ 64

theorem TPre.of (s₀ : State) (h : (xorTo 16).pre s₀) : TPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  exact ⟨by rw [h1]; simp, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

theorem TPre.w_st {s₀ : State} (hp : TPre s₀) : stR (est s₀) ∈ s₀.wr := by simp [hp.wr]
theorem TPre.w_b {s₀ : State} (hp : TPre s₀) : bufR (ebp s₀) ∈ s₀.wr := by simp [hp.wr]
theorem TPre.w_q {s₀ : State} (hp : TPre s₀) : eqR s₀ ∈ s₀.wr := by simp [hp.wr]

/-- The source or the destination from byte `p` on does not wrap around
either. -/
theorem nowrap_at {a : Addr} {L p : Nat} (h : a.toNat + L ≤ 2 ^ 64) (hp : p ≤ L) (hL : L < 2 ^ 64) :
    (a + BitVec.ofNat 64 p).toNat + (L - p) ≤ 2 ^ 64 := by
  rw [Offset.toNat_add_ofNat, Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega)]
  have := Nat.mod_le (a.toNat + p) (2 ^ 64)
  omega

theorem in_eqR {s₀ : State} {k : Nat} (hk : k < eL s₀) : (eqR s₀).Contains (edq s₀ + BitVec.ofNat 64 k) 1 :=
  Xor.contains_ofNat (by lit_omega) (by have := eL_lt s₀; omega)

/-- The source after the first `p` bytes is intact, when the destination
holds the source from there on (in place) or is apart from it. -/
theorem TPre.src_of {s₀ : State} (hp : TPre s₀) {m : Mem} {p : Nat}
    (hd : ∀ k < eL s₀, m (edq s₀ + BitVec.ofNat 64 k) =
      if k < p then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k)
    (hf : Frame (frT s₀) s₀.mem m) {k : Nat} (hpk : p ≤ k) (hk : k < eL s₀) :
    m (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k := by
  rcases hp.alias with he | hdis
  · have := hd k hk
    rw [ite_eq_right (by omega)] at this
    simp only [D0, Q0, edq, edp] at this he ⊢
    rw [← he]; exact this
  · exact hf.bytes (R := edR s₀) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_d.symm
      · exact hdis
      · exact hp.d_b) (show eL s₀ ≤ 2 ^ 64 by have := eL_lt s₀; omega) hk

/-- What the source and the destination hold from byte `p` on. -/
abbrev pS (s₀ : State) (p : Nat) : Region := ⟨edp s₀ + BitVec.ofNat 64 p, eL s₀ - p⟩
abbrev pQ (s₀ : State) (p : Nat) : Region := ⟨edq s₀ + BitVec.ofNat 64 p, eL s₀ - p⟩

theorem pS_sub {s₀ : State} {p : Nat} (hp : p ≤ eL s₀) : Region.Sub (pS s₀ p) (edR s₀) :=
  Offset.sub_base _ (by have := eL_lt s₀; omega_arith)
theorem pQ_sub {s₀ : State} {p : Nat} (hp : p ≤ eL s₀) : Region.Sub (pQ s₀ p) (eqR s₀) :=
  Offset.sub_base _ (by have := eL_lt s₀; omega_arith)

theorem not_pQ {s₀ : State} {p k : Nat} (hk : k < p) (hp : p ≤ eL s₀) :
    ¬ (pQ s₀ p).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by omega_arith) (by omega_arith)]
  split <;> omega_arith

theorem ret_frT {s₀ : State} (hp : TPre s₀) : ∀ r ∈ frT s₀, (eret s₀).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.ret_st
  · exact hp.ret_q
  · exact hp.ret_b

/-- `XorBuf.delta`: `r11` set to the destination's distance from the source. -/
theorem delta_ok (s : State) :
    WP isa (.block Impl.ChaCha20.X86_64.XorBuf.delta) s fun s' =>
      s'.gpr .r11 = s.gpr .r8 - s.gpr .rsi ∧ (∀ r, r ≠ .r11 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp only [Impl.ChaCha20.X86_64.XorBuf.delta, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execAlu, Option.bind_some, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_setReg_self,
      RegUpd.gpr_setReg_of_ne _ _ (by decide : ¬Reg.rsi = .r11)]
  · simp only [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]

/-- Before chunk `t` (the loop's invariant): the destination done before
it, the source from it on intact (`LInv.src`). -/
structure LInv (s₀ : State) (t : Nat) (s : State) : Prop where
  rdi : s.gpr .rdi = est s₀
  rcx : s.gpr .rcx = ebp s₀
  rsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (512 * t)
  r11 : s.gpr .r11 = edq s₀ - edp s₀
  rdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 512 * t)
  le : 512 * t ≤ eL s₀
  keep : ∀ r ∈ calleeSaved, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cnt : stateAt s.mem (est s₀) = ctr (S0 s₀) (8 * t)
  data : ∀ k < eL s₀, s.mem (edq s₀ + BitVec.ofNat 64 k) =
    if k < 512 * t then D0 s₀ k ^^^ (KS s₀).getD k 0 else Q0 s₀ k
  consts : Consts s.mem (ebp s₀)
  incs : Avx2Tail.Incs s.mem (ebp s₀)
  frame : Frame (frT s₀) s₀.mem s.mem

theorem LInv.src {s₀ : State} (hp : TPre s₀) {t : Nat} {s : State} (h : LInv s₀ t s) {k : Nat}
    (hpk : 512 * t ≤ k) (hk : k < eL s₀) : s.mem (edp s₀ + BitVec.ofNat 64 k) = D0 s₀ k :=
  hp.src_of h.data h.frame hpk hk

/-! ## Counters and keystream -/

theorem ctr_ctr (S : CState) (a b : Nat) : ctr (ctr S a) b = ctr S (a + b) := by
  simp only [ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]

theorem ctr_add (S : CState) (j n : Nat) :
    (ctr S j).set 12 ((ctr S j)[12] + BitVec.ofNat 32 n) = ctr S (j + n) := by
  rw [← ctr_ctr]; rfl

/-- The keystream from block `8 t` on. -/
theorem ks_shift (S : CState) {L t k : Nat} (hk : k < L) (ht : 512 * t ≤ k) :
    (keystream S L).getD k 0 =
      (serialize (Spec.ChaCha20.block (ctr (ctr S (8 * t)) ((k - 512 * t) / 64)))).getD
        ((k - 512 * t) % 64) 0 := by
  rw [keystream_getD _ hk, ctr_ctr, show 8 * t + (k - 512 * t) / 64 = k / 64 by omega,
    show (k - 512 * t) % 64 = k % 64 by omega]

/-! ## The end of a chunk -/

set_option simprocs false in
theorem next_ok {s₀ : State} (hp : TPre s₀) {t : Nat} (hge : 512 ≤ eL s₀ - 512 * t) {s : State}
    (hrdi : s.gpr .rdi = est s₀) (hrsi : s.gpr .rsi = edp s₀ + BitVec.ofNat 64 (512 * t))
    (hrdx : s.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 512 * t)) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) :
    WP isa (.block next) s fun s' =>
      s'.gpr .rsi = edp s₀ + BitVec.ofNat 64 (512 * (t + 1)) ∧
      s'.gpr .rdx = BitVec.ofNat 64 (eL s₀ - 512 * (t + 1)) ∧
      (∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s'.gpr r = s.gpr r) ∧
      stateAt s'.mem (est s₀) = (stateAt s.mem (est s₀)).set 12 ((stateAt s.mem (est s₀))[12]'(by decide) + 8) (by decide) ∧
      Frame [stR (est s₀)] s.mem s'.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.cf = some (decide (eL s₀ - 512 * (t + 1) < 512)) := by
  have hL := eL_lt s₀
  have c₁ : (stR (est s₀)).Contains (Xor.off (est s₀) 48) 4 := contains_off (by lit_omega) (by lit_omega)
  have i₁ : InRegions (s.rd ++ s.wr) (Xor.off (est s₀) 48) 4 :=
    ⟨stR (est s₀), by simp [hrd, hwr, hp.wr], c₁⟩
  have o₁ : InRegions s.wr (Xor.off (est s₀) 48) 4 := ⟨stR (est s₀), by simp [hwr, hp.wr], c₁⟩
  simp only [Xor.off] at i₁ o₁
  apply WP.of_runBlock
  simp (config := {decide := true}) only [next, runBlock_cons, runStep_some, runBlock_nil, exec,
    VG.Proof.ChaCha20.X86_64.ea_at, readSrc, readSrc32, execAlu, execAlu32, arithFlags,
    State.load32, State.store32, State.setReg, State.setReg32, State.setFlags, hrdi, i₁, o₁, ite_true,
    ite_false, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
  have hv : s.mem.readW (est s₀ + BitVec.ofInt 64 ((48 : Nat) : Int)) 32 = (stateAt s.mem (est s₀))[12]'(by decide) := by
    simp [stateAt]
  have hfs : Frame [stR (est s₀)] s.mem (s.mem.writeW (Xor.off (est s₀) 48)
      ((stateAt s.mem (est s₀))[12]'(by decide) + 8)) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c₁
  have hrdx' : (s.gpr .rdx).toNat = eL s₀ - 512 * t := by rw [hrdx, toNat_ofNat_lt (by lit_omega)]
  have se : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  have e' : s.gpr .rdx - 512 = BitVec.ofNat 64 (eL s₀ - 512 * (t + 1)) := by
    rw [hrdx, show (512 : BitVec 64) = BitVec.ofNat 64 512 from rfl, Offset.ofNat_sub_ofNat (by lit_omega),
      show eL s₀ - 512 * t - 512 = eL s₀ - 512 * (t + 1) by omega]
  have e : (s.gpr .rdx - 512).toNat = eL s₀ - 512 * (t + 1) := by
    rw [e', toNat_ofNat_lt (by lit_omega)]
  rw [hv, se]
  refine ⟨by rw [hrsi]; exact (Offset.add_add _ _ 512).trans (by rw [Nat.mul_succ]), by rw [← e', hrdx], fun r h₁ h₂ h₃ => by simp [h₁, h₂, h₃],
    Xor.stateAt_writeW_counter _ _ _, hfs, trivial, trivial, ?_⟩
  rw [e]; rfl

/-! ## The chunk of data -/

section
variable {s₀ : State} {t : Nat}

theorem win_sub (hw : 512 * t + 512 ≤ eL s₀) :
    Region.Sub (dR5 (edp s₀ + BitVec.ofNat 64 (512 * t))) (edR s₀) :=
  Offset.sub_base _ hw

theorem dwin {ws : List Region} (hd : edR s₀ ∈ ws) (hw : 512 * t + 512 ≤ eL s₀) :
    DWin ws (edp s₀ + BitVec.ofNat 64 (512 * t)) := by
  have hL := eL_lt s₀
  intro off n h
  refine ⟨edR s₀, hd, ?_⟩
  rw [Offset.add_add]; exact Offset.contains_base _ (by lit_omega) (by lit_omega)

theorem dwinQ {ws : List Region} (hd : eqR s₀ ∈ ws) (hw : 512 * t + 512 ≤ eL s₀) :
    DWin ws (edq s₀ + BitVec.ofNat 64 (512 * t)) := by
  have hL := eL_lt s₀
  intro off n h
  refine ⟨eqR s₀, hd, ?_⟩
  rw [Offset.add_add]; exact Offset.contains_base _ (by lit_omega) (by lit_omega)

theorem winQ_sub (hw : 512 * t + 512 ≤ eL s₀) :
    Region.Sub (dR5 (edq s₀ + BitVec.ofNat 64 (512 * t))) (eqR s₀) :=
  Offset.sub_base _ hw

theorem out_winQ (hw : 512 * t + 512 ≤ eL s₀) {k : Nat} (hk : k < eL s₀)
    (ho : k < 512 * t ∨ 512 * t + 512 ≤ k) :
    ¬ (dR5 (edq s₀ + BitVec.ofNat 64 (512 * t))).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
  split <;> omega

theorem in_dR {k : Nat} (hk : k < eL s₀) : (edR s₀).Contains (edp s₀ + BitVec.ofNat 64 k) 1 :=
  Xor.contains_ofNat (by lit_omega) (by have := eL_lt s₀; omega)

theorem out_win (hw : 512 * t + 512 ≤ eL s₀) {k : Nat} (hk : k < eL s₀)
    (ho : k < 512 * t ∨ 512 * t + 512 ≤ k) :
    ¬ (dR5 (edp s₀ + BitVec.ofNat 64 (512 * t))).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := by
  have hL := eL_lt s₀
  simp only [Region.Contains]
  rw [Offset.sub_toNat' _ (by lit_omega) (by lit_omega)]
  split <;> omega

end

theorem Consts.frame {m m' : Mem} {buf : Addr} (h : Consts m buf) {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (hiR buf).Disjoint r) : Consts m' buf := by
  have e : ∀ d, 128 ≤ d → d + 32 ≤ 320 →
      m'.readW (buf + BitVec.ofNat 64 d) 256 = m.readW (buf + BitVec.ofNat 64 d) 256 :=
    fun d h₁ h₂ => hf.readW (hiR_contains buf h₁ h₂) hd (by decide)
  refine ⟨?_, ?_, ⟨?_, ?_⟩, incs_frame h.inc hf hd⟩
  · rw [e 128 (by lit_omega) (by lit_omega)]; exact h.lo16
  · rw [e 128 (by lit_omega) (by lit_omega)]; exact h.hi16
  · rw [e 160 (by lit_omega) (by lit_omega)]; exact h.m8.1
  · rw [e 160 (by lit_omega) (by lit_omega)]; exact h.m8.2

theorem plus_block (S : CState) (j : Nat) :
    plus (fun j => Nat.repeat Spec.ChaCha20.innerBlock 10 (ctr S j)) S j =
      Spec.ChaCha20.block (ctr S j) := rfl

/-! ## A chunk -/

theorem body_eq (vl : Bool) :
    body vl = .seq (.block setup) (.seq (roundsFor vl) (.block (finishTo true ++ next))) := rfl

theorem calleeSaved_ne {r : Reg} (hr : r ∈ calleeSaved) : r ≠ .rax ∧ r ≠ .rsi ∧ r ≠ .rdx := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem body_ok (vl : Bool) {s₀ : State} (hp : TPre s₀) {t : Nat} (hge : 512 ≤ eL s₀ - 512 * t) {s : State}
    (h : LInv s₀ t s) :
    WP isa (body vl) s fun s' =>
      LInv s₀ (t + 1) s' ∧ s'.cf = some (decide (eL s₀ - 512 * (t + 1) < 512)) := by
  have hL := eL_lt s₀
  have hw : 512 * t + 512 ≤ eL s₀ := by omega
  have hst : stR (est s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_st
  have hb : bufR (ebp s₀) ∈ s.wr := by rw [h.wr]; exact hp.w_b
  have hq : eqR s₀ ∈ s.wr := by rw [h.wr]; exact hp.w_q
  have hd : edR s₀ ∈ s.rd ++ s.wr := by rw [h.rd, h.wr]; exact hp.rd
  have sw := win_sub hw
  have sq := winQ_sub hw
  have dsd := hp.st_q.sub_right sq
  have dbd := hp.q_b.symm.sub_right sq
  have dba := hp.d_b.symm.sub_right sw
  have dss : (stR (est s₀)).Disjoint (slotsR (ebp s₀)) := hp.st_b.sub_right (slotsR_sub _)
  have hsl : ∀ r ∈ [slotsR (ebp s₀)], (hiR (ebp s₀)).Disjoint r := by
    intro r hr; simp only [List.mem_singleton] at hr; subst hr; exact hiR_slots _
  have al : edq s₀ + BitVec.ofNat 64 (512 * t) = edp s₀ + BitVec.ofNat 64 (512 * t) ∨
      (dR5 (edp s₀ + BitVec.ofNat 64 (512 * t))).Disjoint (dR5 (edq s₀ + BitVec.ofNat 64 (512 * t))) := by
    rcases hp.alias with he | hdis
    · exact .inl (by simp only [edq, edp] at he ⊢; rw [he])
    · exact .inr ((hdis.sub_left sw).sub_right sq)
  rw [body_eq vl]
  refine WP.seq (WP.mono (setup_ok h.rdi h.rcx hst hb h.consts)
    fun s₁ ⟨hh, h15, g₁, rd₁, wr₁, y₁, y₂, m₁⟩ => ?_)
  have c₁ : Consts s₁.mem (ebp s₀) := by rw [m₁]; exact h.consts.w2 (by decide) y₁ y₂
  have F₁ : Frame [slotsR (ebp s₀)] s.mem s₁.mem := by
    rw [m₁]; exact W2_frame _ (by decide) y₁ y₂ (Frame.refl _ _)
  refine WP.seq (WP.mono (roundsFor_ok vl hh h15 (by rw [g₁]; exact h.rcx) (by rw [wr₁]; exact hb) c₁.m8
    ⟨c₁.lo16, c₁.hi16⟩)
    fun s₂ hr => ?_)
  have F₂ := F₁.trans hr.frame
  have g₂ : s₂.gpr = s.gpr := hr.gpr.trans g₁
  have rd₂ : s₂.rd = s.rd := hr.rd.trans rd₁
  have wr₂ : s₂.wr = s.wr := hr.wr.trans wr₁
  refine WP.block_append (WP.mono (finishTo_ok (to := true) hr.holds (st := est s₀) (by rw [g₂]; exact h.rdi)
    (by rw [g₂]; exact h.rcx) (by rw [g₂]; exact h.rsi)
    (XorBuf.DstAt.add (to := true) (g := s₂.gpr) (a := edp s₀) (b := edq s₀)
      ⟨fun _ => by rw [g₂]; exact h.r11, fun e => nomatch e⟩ (BitVec.ofNat 64 (512 * t)))
    (by rw [wr₂]; exact hst) (by rw [wr₂]; exact hb) (dwin (by rw [rd₂, wr₂]; exact hd) hw)
    (dwinQ (by rw [wr₂]; exact hq) hw) al (incs_frame c₁.inc hr.frame hsl) dsd hp.st_b dbd dba)
    fun s₃ ⟨d₃, f₃, g₃, rd₃, wr₃⟩ => ?_)
  have g₃' : s₃.gpr = s.gpr := g₃.trans g₂
  have F₃ : Frame [slotsR (ebp s₀), dR5 (edq s₀ + BitVec.ofNat 64 (512 * t))] s.mem s₃.mem :=
    (F₂.mono (by simp)).trans f₃
  have hS₂ : stateAt s₂.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame F₂ (by simpa using dss)
  have hS₃ : stateAt s₃.mem (est s₀) = stateAt s.mem (est s₀) :=
    Xor.stateAt_frame F₃ (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact dss
      · exact dsd)
  refine WP.mono (next_ok hp hge (by rw [g₃']; exact h.rdi) (by rw [g₃']; exact h.rsi)
    (by rw [g₃']; exact h.rdx) (by rw [rd₃, hr.rd, rd₁, h.rd]) (by rw [wr₃, wr₂, h.wr]))
    fun s₄ ⟨e₁, e₂, e₃, e₄, f₄, rd₄, wr₄, cf₄⟩ => ⟨?_, cf₄⟩
  have FA : Frame [slotsR (ebp s₀), dR5 (edq s₀ + BitVec.ofNat 64 (512 * t)), stR (est s₀)]
      s.mem s₄.mem := (F₃.mono (by simp)).trans (f₄.mono (by simp))
  have gk : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s₄.gpr r = s.gpr r := fun r a b c => by
    rw [e₃ r a b c, g₃']
  refine ⟨by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rdi,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.rcx, e₁,
    by rw [gk _ (by decide) (by decide) (by decide)]; exact h.r11, e₂, by omega,
    fun r hr => ?_, by rw [rd₄, rd₃, hr.rd, rd₁, h.rd], by rw [wr₄, wr₃, wr₂, h.wr], ?_,
    fun k hk => ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, b, c⟩ := calleeSaved_ne hr
    rw [gk r a b c]; exact h.keep r hr
  · rw [e₄, hS₃, h.cnt, show 8 * (t + 1) = 8 * t + 8 by omega]
    exact ctr_add _ _ 8
  · have n_st : ¬ (stR (est s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.st_q _ hc (in_eqR hk)
    have n_sl : ¬ (slotsR (ebp s₀)).Contains (edq s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
      hp.q_b _ (in_eqR hk) (slotsR_sub _ _ hc)
    by_cases hin : 512 * t ≤ k ∧ k < 512 * t + 512
    · have ea : edq s₀ + BitVec.ofNat 64 k =
          edq s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' hin.1]
      have ea' : edp s₀ + BitVec.ofNat 64 k =
          edp s₀ + BitVec.ofNat 64 (512 * t) + BitVec.ofNat 64 (k - 512 * t) := by
        rw [add_ofNat, Nat.add_sub_cancel' hin.1]
      have x₃ := d₃ (k - 512 * t) (by lit_omega)
      rw [← ea, ← ea'] at x₃
      have n_sl' : ¬ (slotsR (ebp s₀)).Contains (edp s₀ + BitVec.ofNat 64 k) 1 := fun hc =>
        hp.d_b _ (in_dR hk) (slotsR_sub _ _ hc)
      rw [f₄ _ (by simpa using n_st), x₃, F₂ _ (by simpa using n_sl'), h.src hp hin.1 hk,
        ite_eq_left (by omega : k < 512 * (t + 1)), hS₂, plus_block, h.cnt, ks_shift _ hk hin.1]
    · have n_w := out_winQ hw hk (by lit_omega)
      rw [FA _ (by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact n_sl
          · exact n_w
          · exact n_st), h.data k hk]
      by_cases hlt : k < 512 * t
      · rw [ite_eq_left hlt, ite_eq_left (by omega : k < 512 * (t + 1))]
      · rw [ite_eq_right hlt, ite_eq_right (by omega : ¬ k < 512 * (t + 1))]
  · refine c₁.frame (rs := [slotsR (ebp s₀), dR5 (edq s₀ + BitVec.ofNat 64 (512 * t)), stR (est s₀)])
      (((hr.frame.mono (by simp)).trans (f₃.mono (by simp))).trans (f₄.mono (by simp))) ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hiR_slots _
    · exact dbd.sub_left (hiR_sub _)
    · exact (hp.st_b.sub_right (hiR_sub _)).symm
  · refine Avx2Tail.incs_frame h.incs FA ?_
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hiR_slots _
    · exact dbd.sub_left (hiR_sub _)
    · exact (hp.st_b.sub_right (hiR_sub _)).symm
  · refine h.frame.trans (FA.sub fun r hr' => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact ⟨bufR (ebp s₀), by simp, slotsR_sub _⟩
    · exact ⟨eqR s₀, by simp, sq⟩
    · exact ⟨stR (est s₀), by simp, fun _ h => h⟩

/-! ## The prologue -/

set_option simprocs false in
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .rdx (.imm 512)]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.cf = some (decide ((s.gpr .rdx).toNat < 512)) := by
  have se : BitVec.signExtend 64 (512 : BitVec 32) = 512 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, arithFlags,
    State.setFlags, Option.bind_some, Option.some.injEq, exists_eq_left', se]
  exact ⟨trivial, trivial, trivial, trivial, rfl⟩

theorem constPairs_le : ∀ p ∈ constPairs, p.1 + 8 ≤ 320 := by decide

/-- The offsets in `buf` and values of the quadwords of the lane increments of
the last bytes (`Impl.ChaCha20.X86_64.Avx2Tail.consts`). -/
def tPairs : List (Nat × BitVec 64) :=
  [(224, 0), (232, 0), (240, 1), (248, 0), (256, 2), (264, 0), (272, 3), (280, 0)]

theorem tconsts_eq : Impl.ChaCha20.X86_64.Avx2Tail.consts = pairsCode tPairs := rfl

theorem tPairs_le : ∀ p ∈ tPairs, p.1 + 8 ≤ 320 := by decide

theorem tincs_mem (m : Mem) (buf : Addr) :
    Avx2Tail.Incs (storeAll buf constPairs (storeAll buf tPairs m)) buf := by
  have H : ∀ k < 2, ∀ j < 8, readsTo tPairs constPairs (56 + 8 * k + j)
      (if j % 4 = 0 then BitVec.ofNat 32 (2 * k + j / 4) else 0) = true := by decide +kernel
  intro k hk j hj
  exact storeAll_readW32 (H k hk j hj) m

theorem prologue_ok {s₀ : State} (hp : TPre s₀) :
    WP isa (.block (Impl.ChaCha20.X86_64.Avx2Tail.consts ++ consts ++ Impl.ChaCha20.X86_64.XorBuf.delta ++
      ([.alu .cmp .rdx (.imm 512)] : List Instr))) s₀ fun s =>
      LInv s₀ 0 s ∧ s.cf = some (decide (eL s₀ < 512)) := by
  have hL := eL_lt s₀
  rw [tconsts_eq, consts_eq]
  refine WP.block_append (WP.block_append (WP.block_append (WP.mono (pairs_ok tPairs tPairs_le (s := s₀) rfl hp.w_b)
    fun s₀' ⟨m₀, g₀, rd₀, wr₀⟩ => WP.mono (pairs_ok (buf := ebp s₀) constPairs constPairs_le (s := s₀')
      (by rw [g₀ _ (by decide)]) (by rw [wr₀]; exact hp.w_b))
    fun s₁ ⟨m₁, g₁, rd₁, wr₁⟩ => WP.mono (delta_ok s₁) fun s₁' ⟨d₁, gd, md, rdd, wrd, _⟩ =>
      WP.mono (cmp_ok s₁') fun s₂ ⟨g₂, m₂, rd₂, wr₂, cf₂⟩ => ?_)))
  have F : Frame [bufR (ebp s₀)] s₀.mem s₂.mem := by
    rw [m₂, md, m₁, m₀]
    exact (storeAll_frame (List.mem_singleton_self _) _ tPairs_le _).trans
      (storeAll_frame (List.mem_singleton_self _) _ constPairs_le _)
  have gk : ∀ r, r ≠ .rax → r ≠ .r11 → s₂.gpr r = s₀.gpr r := fun r hr h11 => by
    rw [g₂, gd r h11, g₁ r hr, g₀ r hr]
  refine ⟨⟨gk _ (by decide) (by decide), gk _ (by decide) (by decide),
    by rw [gk _ (by decide) (by decide)]; simp,
    by rw [g₂, d₁, g₁ _ (by decide), g₁ _ (by decide), g₀ _ (by decide), g₀ _ (by decide)],
    by rw [gk _ (by decide) (by decide)]; simp, by omega,
    fun r hr => gk r (calleeSaved_ne hr).1 (by intro h; subst h; simp [calleeSaved] at hr),
    by rw [rd₂, rdd, rd₁, rd₀], by rw [wr₂, wrd, wr₁, wr₀], ?_, fun k hk => ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Xor.stateAt_frame F (by simpa using hp.st_b), Nat.mul_zero, ctr_zero]
  · rw [F _ (by simpa using fun hc => hp.q_b _ (in_eqR hk) hc)]
    simp
  · rw [m₂, md, m₁, m₀]; exact consts_mem _ _
  · rw [m₂, md, m₁, m₀]; exact tincs_mem _ _
  · exact F.mono (by simp)
  · rw [cf₂, gd _ (by decide), g₁ _ (by decide), g₀ _ (by decide)]

/-! ## Helpers -/

theorem xor_keeps : ((instrs Impl.ChaCha20.X86_64.Xor.xor).all fun i => !Taint.clobbers i .rsp) = true := by
  rw [← Code.allInstrs_eq]; lit_decide

/-- `vg_chacha20_xor` does not write `rsp` (for its variant, `Variant.scalar`). -/
theorem xor_nosp : NoSp Impl.ChaCha20.X86_64.Xor.xor := by
  intro i hi
  simpa using List.all_eq_true.mp xor_keeps i hi

theorem xor_depth : Impl.ChaCha20.X86_64.Xor.xor.depth = 1 := by lit_decide

/-- Byte `k` of data XORed with `ks`. -/
theorem bytes_of_bytesAt_to {m m' : Mem} {p q : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' q n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (q + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 := by
  have e := congrArg (fun l => l[k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    List.getElem?_zipWith, List.getElem?_eq_getElem (show k < ks.length by omega)] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < ks.length by omega),
    Option.getD_some]
  simpa using e

theorem bytes_of_bytesAt {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks) {k : Nat} (hk : k < n) :
    m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0 :=
  bytes_of_bytesAt_to hks h hk

theorem stk_ret (s₀ : State) : Region.Sub ⟨s₀.gpr .rsp - 8, 8⟩ (estk s₀) :=
  Offset.sub_below _ (a := 8) (b := 16) (by decide) (by decide)

theorem stk_stk (s₀ : State) : Region.Sub ⟨s₀.gpr .rsp - 8 - 8, 8⟩ (estk s₀) := by
  rw [BitVec.sub_sub]; exact Offset.sub_below _ (a := 16) (b := 16) (by decide) (by decide)

theorem ret_stk (s₀ : State) : (eret s₀).Disjoint (estk s₀) := by
  have := Offset.disjoint_base (s₀.gpr .rsp - BitVec.ofNat 64 16) (d := 16) (n := 8) (k := 16) (by decide) (by decide)
  rwa [BitVec.sub_add_cancel] at this

theorem vz_ok (s : State) :
    WP isa (.block [.vop .vzeroupper]) s fun s' =>
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Option.some.injEq, exists_eq_left',
    VOp.exec_gpr, VOp.exec_mem, VOp.exec_rd, VOp.exec_wr]
  exact ⟨trivial, trivial, trivial, trivial⟩

end VG.Proof.ChaCha20.X86_64.Avx2
