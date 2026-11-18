module

public import VerifiedGarbage.Proof.Framework.TacticTemplate
public meta import VerifiedGarbage.Proof.Framework.TacticTemplate
public import VerifiedGarbage.Proof.Aes.X86.VariantProof
public import VerifiedGarbage.Proof.AesGcm.X86.Callee
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.AesCcm.X86
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.AesGcm.X86.Env
public import VerifiedGarbage.Proof.AesGcm.X86.Common
import VerifiedGarbage.Proof.Aes.X86.AesNi.Lit
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `AesCcm.X86.Env`, which the modules that import this one used -/

section

/-!
# AES-CCM on x86: where everything is

Untrusted: everything here is checked by Lean. The key schedule (240 bytes
at `K`), the working space (2560 bytes at `W`) and the 60 bytes of stack
below `SP` that the calls use (`Lay`); what a state may access (`Perm`); the
registers holding `W` and the stack pointer (`Env`); and the public values
the entry keeps in `W` (`Slots`). The pieces write the parts of `W` in
`mutR` (and the data, and the stack below `SP`), so the slots and our
caller's registers saved in `W` stay as the entry left them.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Proof.AesGcm.X86 (w64 toNat_ofNat32 toNat_add32 w64_add covers_off in_off in_left covers_left
  covers_cons covers_nil slotv)

/-! ## Covering -/

theorem covers_of_mem {r : Region} {ts : List Region} (h : r ∈ ts) : Covers [r] ts := by
  intro a n ⟨x, hx, hc⟩
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨x, h, hc⟩

/-! ## The regions -/

/-- The key schedule, `W` and the stack below `SP` used by the calls. -/
structure Lay (K W SP : BitVec 32) : Prop where
  fk : K.toNat + 240 ≤ 2 ^ 32
  fw : W.toNat + 2560 ≤ 2 ^ 32
  sp : 60 ≤ SP.toNat
  k_w : (⟨w64 K, 240⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  stk_k : (below SP 60).Disjoint ⟨w64 K, 240⟩
  stk_w : (below SP 60).Disjoint ⟨w64 W, 2560⟩

/-- What a state may access. -/
structure Perm (K W : BitVec 32) (s : State) : Prop where
  k : Covers [⟨w64 K, 240⟩] (s.rd ++ s.wr)
  w : Covers [⟨w64 W, 2560⟩] s.wr

/-- The registers holding `W` and the stack pointer, and what the state may
access. -/
structure Env (K W SP : BitVec 32) (s : State) : Prop where
  ebp : s.gpr .ebp = W
  esp : s.gpr .esp = SP
  perm : Perm K W s

theorem Perm.of_eq {K W : BitVec 32} {s s' : State} (h : Perm K W s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) :
    Perm K W s' := ⟨by rw [hrd, hwr]; exact h.k, by rw [hwr]; exact h.w⟩

/-- An environment, after code that keeps `ebp`, `esp` and the permissions. -/
theorem Env.keep {K W SP : BitVec 32} {s s' : State} (h : Env K W SP s) (hbp : s'.gpr .ebp = s.gpr .ebp)
    (hsp : s'.gpr .esp = s.gpr .esp) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Env K W SP s' :=
  ⟨by rw [hbp, h.ebp], by rw [hsp, h.esp], h.perm.of_eq hrd hwr⟩

namespace Lay

theorem kSub {K : Addr} {d n : Nat} (h : d + n ≤ 240) : Region.Sub ⟨K + BitVec.ofNat 64 d, n⟩ ⟨K, 240⟩ :=
  Offset.sub_base _ h

theorem wSub {W : Addr} {d n : Nat} (h : d + n ≤ 2560) : Region.Sub ⟨W + BitVec.ofNat 64 d, n⟩ ⟨W, 2560⟩ :=
  Offset.sub_base _ h

/-- Parts of `W` are disjoint. -/
theorem w_w {W : BitVec 32} {a n d k : Nat} (h : a + n ≤ d ∨ d + k ≤ a) (ha : a + n ≤ 2560) (hd : d + k ≤ 2560) :
    (⟨w64 W + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  Offset.disjoint _ h (by omega_using [ha]) (by omega_using [hd])

variable {K W SP : BitVec 32} (L : Lay K W SP)
include L

theorem k_w' {a n d k : Nat} (ha : a + n ≤ 240) (hd : d + k ≤ 2560) :
    (⟨w64 K + BitVec.ofNat 64 a, n⟩ : Region).Disjoint ⟨w64 W + BitVec.ofNat 64 d, k⟩ :=
  (L.k_w.sub_left (kSub ha)).sub_right (wSub hd)

theorem stk_w' {a n : Nat} (ha : a + n ≤ 2560) : (below SP 60).Disjoint ⟨w64 W + BitVec.ofNat 64 a, n⟩ :=
  L.stk_w.sub_right (wSub ha)

theorem aW {o : Nat} (ho : o < 2560) : w64 (W + BitVec.ofNat 32 o) = w64 W + BitVec.ofNat 64 o :=
  w64_add (by have := L.fw; omega_using [ho, this])

theorem nW {o : Nat} (ho : o < 2560) : (W + BitVec.ofNat 32 o).toNat = W.toNat + o :=
  toNat_add32 (by have := L.fw; omega_using [ho, this])

end Lay

namespace Perm

variable {K W : BitVec 32} {s : State} (P : Perm K W s)
include P

theorem wW {d n : Nat} (h : d + n ≤ 2560) : InRegions s.wr (w64 W + BitVec.ofNat 64 d) n :=
  in_off P.w h (by decide)

theorem wR {d n : Nat} (h : d + n ≤ 2560) : InRegions (s.rd ++ s.wr) (w64 W + BitVec.ofNat 64 d) n :=
  in_left (P.wW h)

theorem wC {d n : Nat} (h : d + n ≤ 2560) : Covers [⟨w64 W + BitVec.ofNat 64 d, n⟩] s.wr :=
  covers_off P.w h (by decide)

end Perm

/-! ## Buffers -/

/-- A buffer of `n` bytes at `D` that the code may read, apart from `W`, the
key schedule and the stack below `SP`. -/
structure Buf (W SP : BitVec 32) (s : State) (D : BitVec 32) (n : Nat) : Prop where
  rd : Covers [⟨w64 D, n⟩] (s.rd ++ s.wr)
  wrap : D.toNat + n ≤ 2 ^ 32
  w : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩
  stk : (below SP 60).Disjoint ⟨w64 D, n⟩

namespace Buf

variable {W SP : BitVec 32} {s : State} {D : BitVec 32} {n : Nat} (h : Buf W SP s D n)
include h

theorem of_eq {s' : State} (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Buf W SP s' D n :=
  { h with rd := by rw [hrd, hwr]; exact h.rd }

theorem lt : n < 2 ^ 64 := by have := h.wrap; omega_using [this]

omit h in
/-- The address of byte `k`. -/
theorem ptr {k : Nat} (hk : D.toNat + k < 2 ^ 32) : w64 (D + BitVec.ofNat 32 k) = w64 D + BitVec.ofNat 64 k :=
  w64_add hk

/-- The bytes from `k` on. -/
theorem drop {k : Nat} (hk : k ≤ n) (hw : D.toNat + k < 2 ^ 32) : Buf W SP s (D + BitVec.ofNat 32 k) (n - k) where
  rd := by rw [ptr hw]; exact covers_off h.rd (by omega_using [hk]) h.lt
  wrap := by rw [toNat_add32 hw]; have := h.wrap; omega_using [hk, this]
  w := by rw [ptr hw]; exact h.w.sub_left (Offset.sub_base _ (by omega_using [hk]))
  stk := by rw [ptr hw]; exact h.stk.sub_right (Offset.sub_base _ (by omega_using [hk]))

/-- The first `k` bytes. -/
theorem take {k : Nat} (hk : k ≤ n) : Buf W SP s D k where
  rd := fun a m ⟨r, hr, hc⟩ => by
    simp only [List.mem_singleton] at hr; subst hr
    exact h.rd a m ⟨_, List.mem_singleton_self _, by simp only [Region.Contains] at hc ⊢; omega_using [hk, hc]⟩
  wrap := by have := h.wrap; omega_using [hk, this]
  w := h.w.sub_left (Region.sub_prefix hk)
  stk := h.stk.sub_right (Region.sub_prefix hk)

end Buf

/-! ## The slots -/

/-- The public values the entry keeps in `W`: the key schedule, the rounds,
the nonce and its length, the associated data and its length, the data and
its length, the tag and its length. -/
structure Slots (W K : BitVec 32) (R : Nat) (N A D T : BitVec 32) (nl al n tl : Nat) (m : Mem) : Prop where
  ctx : slotv m W Impl.AesCcm.X86.ctxO = K
  rounds : slotv m W Impl.AesCcm.X86.roundsO = BitVec.ofNat 32 R
  nonce : slotv m W Impl.AesCcm.X86.nonceO = N
  nlen : slotv m W Impl.AesCcm.X86.nlenO = BitVec.ofNat 32 nl
  aad : slotv m W Impl.AesCcm.X86.aadO = A
  alen : slotv m W Impl.AesCcm.X86.alenO = BitVec.ofNat 32 al
  data : slotv m W Impl.AesCcm.X86.dataO = D
  len : slotv m W Impl.AesCcm.X86.lenO = BitVec.ofNat 32 n
  tl : slotv m W Impl.AesGcm.X86.tglO = BitVec.ofNat 32 tl
  tp : slotv m W Impl.AesGcm.X86.tpO = T

/-- The parts of `W` the pieces write: the blocks at `[0, 112)`, the result of
the comparison at `[176, 180)`, the padded received tag at `[196, 212)`, and
`[240, 2560)` (the padded computed tag, the arguments of the piece running
and the working space of the functions called). -/
abbrev wA (W : BitVec 32) : Region := ⟨w64 W, 112⟩
abbrev wO (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 176, 4⟩
abbrev wT (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 196, 16⟩
abbrev wC (W : BitVec 32) : Region := ⟨w64 W + BitVec.ofNat 64 240, 2320⟩

/-- What the pieces may change: those parts of `W`, the stack below `SP`
and the data. -/
abbrev mutR (W SP D : BitVec 32) (n : Nat) : List Region :=
  [wA W, wO W, wT W, wC W, below SP 60, ⟨w64 D, n⟩]

/-- The part of `W` at `[d, d + k)`, when it misses the parts the pieces write. -/
theorem kept_mut {K W SP D : BitVec 32} {n : Nat} (L : Lay K W SP)
    (hD : (⟨w64 D, n⟩ : Region).Disjoint ⟨w64 W, 2560⟩) {d k : Nat}
    (hd : 112 ≤ d ∧ d + k ≤ 176 ∨ 180 ≤ d ∧ d + k ≤ 196 ∨ 212 ≤ d ∧ d + k ≤ 240) :
    ∀ r ∈ mutR W SP D n, (⟨w64 W + BitVec.ofNat 64 d, k⟩ : Region).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa using Lay.w_w (W := W) (a := d) (n := k) (d := 0) (k := 112) (.inr (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (by omega_using [hd]) (by omega_using [hd]) (by decide)
  · exact Lay.w_w (.inl (by omega_using [hd])) (by omega_using [hd]) (by decide)
  · exact (L.stk_w' (by omega_using [hd])).symm
  · exact (hD.sub_right (Lay.wSub (by omega_using [hd]))).symm

/-- The slots, after code that changes only `mutR`. -/
theorem slots_mut {K W SP D' : BitVec 32} {n' : Nat} (L : Lay K W SP)
    (hD : (⟨w64 D', n'⟩ : Region).Disjoint ⟨w64 W, 2560⟩) {m m' : Mem} (hf : Frame (mutR W SP D' n') m m')
    {R : Nat} {N A D T : BitVec 32} {nl al n tl : Nat} (S : Slots W K R N A D T nl al n tl m) :
    Slots W K R N A D T nl al n tl m' := by
  have k : ∀ o, (112 ≤ o ∧ o + 4 ≤ 176 ∨ 180 ≤ o ∧ o + 4 ≤ 196 ∨ 212 ≤ o ∧ o + 4 ≤ 240) →
      slotv m' W o = slotv m W o := fun o ho =>
    hf.readW (r := ⟨w64 W + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (kept_mut L hD ho) (by decide)
  exact ⟨by rw [k _ (by decide)]; exact S.ctx, by rw [k _ (by decide)]; exact S.rounds,
    by rw [k _ (by decide)]; exact S.nonce, by rw [k _ (by decide)]; exact S.nlen,
    by rw [k _ (by decide)]; exact S.aad, by rw [k _ (by decide)]; exact S.alen,
    by rw [k _ (by decide)]; exact S.data, by rw [k _ (by decide)]; exact S.len,
    by rw [k _ (by decide)]; exact S.tl, by rw [k _ (by decide)]; exact S.tp⟩

end VG.Proof.AesCcm.X86

end

end

/-!
# AES-CCM on x86: running straight-line blocks

Untrusted: everything here is checked by Lean. `crun [facts]` runs a block
symbolically (`runBlock_cons`, `runStep_some`, the semantics of the
instructions the code uses, and reads through the writes with `RegUpd`,
keeping the registers folded), as AES-GCM's `xrun` does, with the offsets
of the AES-CCM code.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace VG.Proof.AesCcm.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.AesCcm.X86
open VG.Impl.AesGcm.X86 (at_ imm slot argOp tglO rO vO tpO dO nO bO)
open VG.Proof.AesGcm.X86 (store32_eq store8_eq gpr_setMem mem_setMem rd_setMem wr_setMem cf_setMem zf_setMem
  readW_writeW_off CT)

/-- A word at `p + a`, after a byte written at `p + b` elsewhere. -/
theorem readW_writeB_off (m : Mem) (p : Addr) (v : BitVec 8) {a b : Nat} (h : a + 4 ≤ b ∨ b + 1 ≤ a)
    (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    (m.writeW (p + BitVec.ofNat 64 b) v).readW (p + BitVec.ofNat 64 a) 32 = m.readW (p + BitVec.ofNat 64 a) 32 :=
  Mem.readW_writeW_sep (Offset.sep _ h (by omega_using [ha]) (by omega_using [hb])) (by decide)

theorem add_ofNat_assoc (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Runs a block of the instructions the AES-CCM code uses. The facts given
rewrite the addresses and discharge the permissions. -/
tactic_template "crun" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := first | decide | omega) only [runBlock_cons, runStep_some,
                     runBlock_nil, exec, readSrc, execAlu, execShift, State.load32, store32_eq, State.load8, store8_eq,
                     State.ea, at_, imm, slot, argOp, blkO, c0O, c1O, ksO, uO, ctxO, roundsO, nonceO, nlenO, aadO, alenO, dataO,
                     lenO, okO, scrO, tglO, rO, vO, tpO, dO, nO, bO, List.cons_append, List.nil_append, List.append_assoc,
                     Option.bind_some, Option.map_some, readW_writeW_off, readW_writeB_off, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, mem_setReg,
                     mem_arithFlags, mem_setFlags, rd_setReg, rd_arithFlags, rd_setFlags, wr_setReg, wr_arithFlags,
                     wr_setFlags, cf_setReg, cf_arithFlags, zf_setReg, zf_arithFlags, gpr_setMem, mem_setMem, rd_setMem,
                     wr_setMem, cf_setMem, zf_setMem, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd, ↓reduceIte, Nat.reduceLT,
                     Nat.reduceLeDiff, Nat.reduceSub, Nat.reduceEqDiff, Nat.reduceMul, and_self, and_true, true_and,
                     eq_self_iff_true, Reg8.reg, $ts,*]) <;>
                   try rfl)

/-- Reads registers through the writes of a block. -/
tactic_template "cregs" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := first | decide | with_reducible assumption) only [gpr_setMem, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags,
                     $ts,*]))

/-- Reads the memory, flags and permissions through the writes of a block. -/
tactic_template "cmems" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
                   simp (disch := first | decide | omega) only [mem_setMem, mem_setReg, mem_arithFlags, mem_setFlags,
                     rd_setMem, rd_setReg, rd_arithFlags, rd_setFlags, wr_setMem, wr_setReg, wr_arithFlags, wr_setFlags,
                     zf_setMem, zf_setReg, zf_arithFlags, cf_setMem, cf_setReg, cf_arithFlags, gpr_setMem, gpr_setReg_self,
                     gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, Mem.readW_writeW_self32, readW_writeW_off, readW_writeB_off, blkO, c0O, c1O,
                     ksO, uO, ctxO, roundsO, nonceO, nlenO, aadO, alenO, dataO, lenO, okO, scrO, tglO, rO, vO, tpO, dO, nO, bO,
                     Nat.reduceAdd, Reg8.reg, eq_self_iff_true, and_self, $ts,*]))

theorem eval_e {s : State} {b : Bool} (h : s.zf = some b) : isa.eval .e s = some b := h

theorem eval_b {s : State} {b : Bool} (h : s.cf = some b) : isa.eval .b s = some b := h

theorem seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq (.seq a b) c) s Q) :
    WP isa (.seq a (.seq b c)) s Q :=
  WP.seq (WP.mono (WP.seq_iff.mp (WP.seq_iff.mp h)) fun _ h => WP.seq h)

/-- A block, then code: the block constant time by the taint analysis from
the registers `rs`, which `I` pins, and the code from what the block leaves
(`F`, from the state it started in). -/
theorem CT.block_seq {I : State → Prop} {is : List Instr} {c : Prog isa} {F : State → State → Prop}
    (rs : List Reg) (hr : ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) {hc : Taint.Hint VG.X86.taint.T}
    (h : (VG.X86.taint.check (τr rs) (.block is) hc).isSome = true)
    (blk : ∀ s, I s → ∃ s', runBlock isa is s = some s' ∧ F s s') (h₂ : CT (fun s' => ∃ s, I s ∧ F s s') c) :
    CT I (.seq (.block is) c) :=
  CT.seq (CT.taint rs hr h) (fun s hs => let ⟨s', r, f⟩ := blk s hs; WP.of_runBlock ⟨s', r, s, hs, f⟩) h₂

/-- `a; (b; (c; d))` from `(a; (b; c)); d`. -/
theorem CT.assoc3 {I : State → Prop} {a b c d : Prog isa}
    (h : Proof.AesGcm.X86.CT I (.seq (.seq a (.seq b c)) d)) : Proof.AesGcm.X86.CT I (.seq a (.seq b (.seq c d))) := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ e₁ =>
    cases e₁ with
    | seq b₁ e₁ =>
      cases e₁ with
      | seq c₁ d₁ =>
        cases e₂ with
        | seq a₂ e₂ =>
          cases e₂ with
          | seq b₂ e₂ =>
            cases e₂ with
            | seq c₂ d₂ =>
              obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp (.seq (.seq a₁ (.seq b₁ c₁)) d₁) (.seq (.seq a₂ (.seq b₂ c₂)) d₂)
              simp only [List.append_assoc] at ht
              exact ⟨ht, hq⟩

/-- A register pinned. -/
theorem pin1 {I : State → Prop} {a : Reg} {x : BitVec 32} (h : ∀ s, I s → s.gpr a = x) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- `ebp` pinned. -/
theorem pin_ebp {I : State → Prop} {W : BitVec 32} (h : ∀ s, I s → s.gpr .ebp = W) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [Reg.ebp], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h _ h₁, h _ h₂]

/-- Two registers pinned. -/
theorem pin2 {I : State → Prop} {a b : Reg} {x y : BitVec 32} (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2, (h _ h₂).2]

/-- Three registers pinned. -/
theorem pin3 {I : State → Prop} {a b c : Reg} {x y z : BitVec 32}
    (h : ∀ s, I s → s.gpr a = x ∧ s.gpr b = y ∧ s.gpr c = z) :
    ∀ s₁ s₂, I s₁ → I s₂ → ∀ r ∈ [a, b, c], s₁.gpr r = s₂.gpr r := fun s₁ s₂ h₁ h₂ r hr => by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [(h _ h₁).1, (h _ h₂).1]
  · rw [(h _ h₁).2.1, (h _ h₂).2.1]
  · rw [(h _ h₁).2.2, (h _ h₂).2.2]

end VG.Proof.AesCcm.X86
